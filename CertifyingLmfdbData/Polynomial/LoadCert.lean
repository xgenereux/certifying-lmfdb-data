import Mathlib

/-!
# Loading root certificates from a file

At high precision the numeric literals in a root certificate — the approximation `v` (a
`Fin 2 → ℝ` vector) and the inverse-Jacobian `M` (a `2 × 2` real matrix) — are decimal numbers
of tens of thousands of digits. Written inline in a `.lean` source these are re-tokenized and
re-parsed by the Lean frontend on every elaboration, which dominates the `unique_root_near`
profile once the actual proof work is cheap.

This module provides two term elaborators that read those numbers from a plain-text file at
elaboration time and build the corresponding `Expr` directly, bypassing the frontend:

* `load_vec "path"`  ⟶  `![v₀, v₁, …] : Fin n → ℝ`
* `load_mat "path"`  ⟶  `!![…] : Matrix (Fin r) (Fin c) ℝ`

Each decimal token is turned straight into an `OfScientific.ofScientific` application whose
mantissa is stored as a raw `Nat` literal (`Expr.lit (.natVal …)`), so no decimal string is ever
serialized back out. The `Nat` itself is assembled from the digit string by a divide-and-conquer
combine (`digitsToNat`) so the base-10 → binary conversion stays subquadratic (GMP fast
multiplication) rather than the naive `n²` `foldl (·*10 + ·)`.

## File format

Whitespace within a number is ignored. Entries are separated by `,`; matrix rows additionally by
`;` or a newline. So a vector file is e.g. `1.41421356, 0` and a matrix file
`0.3536, 0; 0, 0.3536`. Each token is a decimal, optionally signed, optionally with an `e`/`E`
exponent (`-0.032`, `1e-7`, `423423.4111`).

The produced `Expr`s match the shapes the `unique_root_near` meta-level parsers expect
(`Matrix.vecCons`/`vecEmpty` for vectors, `⇑Matrix.of ![…]` for matrices), so they drop in as the
goal's `v` and the tactic's `M` argument without any further conversion.
-/

namespace LoadCert

open Lean Elab Term Meta

/-- The `Nat` denoted by the decimal digit characters `arr[lo:hi]`, by divide-and-conquer:
recursively convert the two halves and combine as `high * 10 ^ (hi - mid) + low`. This routes the
big-integer growth through GMP's subquadratic multiplication, whereas the naive left fold
`n ↦ n * 10 + d` is `Θ(D²)` in the digit count `D`. -/
partial def digitsToNat (arr : Array Char) (lo hi : Nat) : Nat :=
  if hi - lo ≤ 18 then Id.run do
    let mut n : Nat := 0
    for i in [lo:hi] do
      n := n * 10 + (arr[i]!.toNat - 48)
    return n
  else
    let mid := (lo + hi) / 2
    digitsToNat arr lo mid * 10 ^ (hi - mid) + digitsToNat arr mid hi

/-- The `Nat` denoted by a short run of digit characters (used only for exponents). -/
def natFromChars (t : List Char) : Nat := t.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- The (possibly signed) `Int` denoted by a short run of digit characters (a decimal exponent). -/
def intFromChars : List Char → Int
  | '-' :: t => -(natFromChars t : Int)
  | '+' :: t => (natFromChars t : Int)
  | t        => (natFromChars t : Int)

/-- Parse one decimal token (given as its list of non-space characters) into an `Expr` of type
`ty`, as `OfScientific.ofScientific mant b e` (wrapped in `Neg.neg` when negative). The mantissa
is a raw `Nat` literal, so no decimal string is materialized. Handles an optional sign, an
optional fractional part, and an optional `e`/`E` exponent. -/
def parseDecimal (tok : List Char) (ty : Expr) : MetaM Expr := do
  let (neg, l1) := match tok with
    | '-' :: t => (true, t)
    | '+' :: t => (false, t)
    | t        => (false, t)
  -- split mantissa from the `e`/`E` exponent, then the integer part from the fractional part
  let (mantChars, expChars) := match l1.span (fun c => c != 'e' && c != 'E') with
    | (m, [])     => (m, [])
    | (m, _ :: e) => (m, e)
  let (intChars, fracChars) := match mantChars.span (· != '.') with
    | (a, [])     => (a, [])
    | (a, _ :: b) => (a, b)
  let digits := (intChars ++ fracChars).toArray
  -- value = mant * 10 ^ (expo - fracLen); express as `ofScientific mant b e`
  let net : Int := intFromChars expChars - fracChars.length
  let sci ← mkAppOptM ``OfScientific.ofScientific
    #[some ty, none, mkRawNatLit (digitsToNat digits 0 digits.size),
      mkConst (if net ≤ 0 then ``Bool.true else ``Bool.false), mkRawNatLit net.natAbs]
  if neg then mkAppM ``Neg.neg #[sci] else pure sci

/-- Split file contents into rows (separated by `;` or newlines) of decimal tokens (separated by
`,`), each token as its list of non-whitespace characters. Empty tokens/rows are dropped. -/
def tokenize (s : String) : Array (Array (List Char)) := Id.run do
  let mut rows : Array (Array (List Char)) := #[]
  for rowStr in s.splitOn ";" |>.flatMap (·.splitOn "\n") do
    let toks := (rowStr.splitOn ",").filterMap fun t =>
      let cs := t.toList.filter (fun c => !c.isWhitespace)
      if cs.isEmpty then none else some cs
    if !toks.isEmpty then rows := rows.push toks.toArray
  return rows

/-- Assemble a `![e₀, e₁, …] : Fin n → ty` vector `Expr` from its entries. -/
def mkVec (elems : Array Expr) (ty : Expr) : MetaM Expr := do
  let mut acc ← mkAppOptM ``Matrix.vecEmpty #[some ty]
  for e in elems.reverse do acc ← mkAppM ``Matrix.vecCons #[e, acc]
  return acc

/-- Assemble a `!![…] : Matrix (Fin r) (Fin c) ty` matrix `Expr` from its rows, in the
`⇑Matrix.of ![![…], …]` shape produced by the `!![…]` notation. -/
def mkMat (rows : Array (Array Expr)) (ty : Expr) : MetaM Expr := do
  let rowVecs ← rows.mapM (mkVec · ty)
  let inner ← mkVec rowVecs (← inferType rowVecs[0]!)
  let nrows := mkApp (mkConst ``Fin) (mkNatLit rows.size)
  let ncols := mkApp (mkConst ``Fin) (mkNatLit rows[0]!.size)
  let ofEquiv ← mkAppOptM ``Matrix.of #[some nrows, some ncols, some ty]
  mkAppM ``DFunLike.coe #[ofEquiv, inner]

/-- `load_vec "path"` : read a `![…] : Fin n → ℝ` vector from the file at `path`. -/
syntax (name := loadVec) "load_vec " str : term
/-- `load_mat "path"` : read a `!![…] : Matrix (Fin r) (Fin c) ℝ` matrix from the file at `path`. -/
syntax (name := loadMat) "load_mat " str : term

@[term_elab loadVec] def elabLoadVec : TermElab := fun stx _ => do
  let `(load_vec $s:str) := stx | throwUnsupportedSyntax
  let toks := (tokenize (← IO.FS.readFile s.getString)).flatMap id
  let ty := Lean.mkConst ``Real
  mkVec (← toks.mapM (parseDecimal · ty)) ty

@[term_elab loadMat] def elabLoadMat : TermElab := fun stx _ => do
  let `(load_mat $s:str) := stx | throwUnsupportedSyntax
  let ty := Lean.mkConst ``Real
  mkMat (← (tokenize (← IO.FS.readFile s.getString)).mapM (·.mapM (parseDecimal · ty))) ty

end LoadCert
