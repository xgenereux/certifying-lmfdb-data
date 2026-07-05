import CertifyingLmfdbData.Polynomial.UniqueRootNear

/-!
# The `unique_root_near` tactic

`unique_root_near M` closes a goal of the form

```
UniqueRootNear (aeval · p) (toComplex v) r
```

given an approximate inverse-Jacobian matrix `M`. All other certificate data is derived
automatically, by exact rational arithmetic **at the meta level**:

* `y := r / 10`, `z₁ := 1/2` and `R := max r 10⁻⁶` (overridable with `(y := …)`, `(z₁ := …)`,
  `(R := …)`),
* the derivative polynomial `pd`, its degree bound `d`, the row-sum bound `a` on `M`, and the
  norm bound `B` on `v` are computed from the goal and the certificate,
* the Lipschitz certificate `z₂` is estimated as `3a` times the binomial-weighted coefficient
  sum appearing in the `hnum` hypothesis (with `R` tiny, the `k ≥ 1` tail is negligible,
  so this is essentially sharp); override with `(z₂ := …)` if needed.

The approximate-inverse bound is *not* certified at `v` itself: `p'` is evaluated at a proxy
point `w` — `v` truncated to an adaptively chosen number of decimal places,
`~max 6 (log₁₀(500·z₂/z₁))` — and the row-sum bound `z₁'` obtained there is transported to
`v` through the Lipschitz certificate, `‖1 - M·p'(v)‖ ≤ z₁' + z₂·ε ≤ z₁` with `ε ≥ |v - w|`
the truncation error. Since `z₁ = 1/2` is loose (the Newton–Kantorovich inequalities
`hyr`/`hzr` admit `z₁ ≈ 0.9`), a few digits of `p'(w)` suffice, so this check costs O(1) in
the precision of `v` instead of dominating the runtime at high precision; ill-conditioned
inputs (large `z₂`, i.e. clustered roots) buy `w` exactly the extra digits they require.

The tactic applies `UniqueRootNear.of_certificates'` and dispatches every side goal to a fixed
finisher; a failing numeric check is reported by hypothesis name so that a bad certificate
(`M` too inaccurate, `z₂` too small, `r` too tight) can be told apart from a tactic bug.

The meta-level rational evaluators (`parseRat`, `parsePoly`, `parseVec`, `parseMatrix`) are the
groundwork for computing the remaining certificates (`M`, `z₂`, `R`) at elaboration time, so
that eventually the goal statement itself is the entire input.
-/

noncomputable section

open Polynomial NNReal Finset in
/-- Assembly lemma for the `unique_root_near` tactic: `UniqueRootNear.of_certificates` with
two extra degrees of freedom that let a tactic apply it without rewriting the goal first:

* the radius `r` is a real number, linked to the `ℝ≥0` certificate radius `r'` by `hr`;
* the derivative of `p` is given explicitly as `pd` (with proof `hpd`), so that every
  remaining hypothesis mentions only the explicit polynomial `pd` and is closed by uniform
  `simp`/`norm_num` calls;
* the approximate-inverse bound `hz1w` is stated at a low-precision proxy `w` for `v` (with
  truncation error `hw0`/`hw1` at most `ε ≤ R`) and transported to `v` through the Lipschitz
  certificate by `hz1 : z₁' + z₂ * ε ≤ z₁`, keeping its arithmetic O(1) in the precision. -/
noncomputable def UniqueRootNear.of_certificates' (p pd : ℚ[X])
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) {r : ℝ} (r' y z₁ z₁' z₂ ε R : ℝ≥0)
    (d : ℕ) (a B : ℝ)
    (hr : r = r')
    (hpd : derivative p = pd)
    (hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (hy1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y)
    (hz1w : ∀ i, ∑ j, |(1 - M *
        !![(aeval (toComplex w) pd).re, -(aeval (toComplex w) pd).im;
           (aeval (toComplex w) pd).im, (aeval (toComplex w) pd).re]) i j| ≤ z₁')
    (hw0 : |v 0 - w 0| ≤ ε)
    (hw1 : |v 1 - w 1| ≤ ε)
    (hεR : ε ≤ R)
    (hz1 : z₁' + z₂ * ε ≤ z₁)
    (hdeg : pd.natDegree ≤ d)
    (ha : ∀ i, ∑ j, |M i j| ≤ a)
    (hB : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) (hB0 : 0 ≤ B)
    (hnum : 3 * a *
        (∑ k ∈ Finset.range d,
          (∑ n ∈ Finset.range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((pd.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (3 / 2 * R) ^ k) ≤ z₂)
    (hrR : r' ≤ R)
    (hyr : y + z₁ * r' + z₂ * r' ^ 2 / 2 ≤ r')
    (hzr : z₁ + z₂ * r' < 1) :
    UniqueRootNear p (toComplex v) r := by
  subst hr hpd
  exact .of_certificates_approx p M v w hy0 hy1 hz1w hw0 hw1 hεR hz1 hdeg ha hB hB0 hnum
    hrR hyr hzr

end

namespace UniqueRootNearTactic

open Lean Elab Meta Tactic

/-! ### Meta-level rational evaluation

Small evaluators turning the numeric literal expressions occurring in root-certification
goals (decimal approximations, vector/matrix literals, explicit polynomials) into exact
rational data. Constants (`myPoly`, `rroot1`, …) are delta-unfolded on the fly. -/

/-- Evaluate an expression built from numeric literals, casts and field operations to a
rational number. -/
partial def parseRat (e : Expr) : MetaM ℚ := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return (n : ℚ)
  let err {α} : MetaM α :=
    throwError "unique_root_near: cannot evaluate{indentExpr e}\nas a rational number"
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``OfNat.ofNat, #[_, n, _] => parseRat n
  | some ``OfScientific.ofScientific, #[_, _, m, sign, ex] => do
    let mq ← parseRat m
    let k := (← parseRat ex).num.toNat
    match sign.consumeMData with
    | .const ``Bool.true _ => return mq / (10 : ℚ) ^ k
    | .const ``Bool.false _ => return mq * (10 : ℚ) ^ k
    | _ => err
  | some ``Neg.neg, #[_, _, x] => return -(← parseRat x)
  | some ``HAdd.hAdd, #[_, _, _, _, x, y] => return (← parseRat x) + (← parseRat y)
  | some ``HSub.hSub, #[_, _, _, _, x, y] => return (← parseRat x) - (← parseRat y)
  | some ``HMul.hMul, #[_, _, _, _, x, y] => return (← parseRat x) * (← parseRat y)
  | some ``HDiv.hDiv, #[_, _, _, _, x, y] => do
    let yq ← parseRat y
    if yq = 0 then err else return (← parseRat x) / yq
  | some ``HPow.hPow, #[_, _, _, _, x, n] => do
    let nq ← parseRat n
    if nq.den = 1 && 0 ≤ nq.num then return (← parseRat x) ^ nq.num.toNat else err
  | some ``Nat.cast, #[_, _, x] => parseRat x
  | some ``Int.cast, #[_, _, x] => parseRat x
  | some ``Rat.cast, #[_, _, x] => parseRat x
  | some ``NatCast.natCast, #[_, _, x] => parseRat x
  | some ``IntCast.intCast, #[_, _, x] => parseRat x
  | some ``RatCast.ratCast, #[_, _, x] => parseRat x
  | some ``Int.ofNat, #[x] => parseRat x
  | _, _ =>
    match ← unfoldDefinition? e with
    | some e' => parseRat e'
    | none => err

/-- Evaluate an expression to a natural number literal. -/
def parseNat (e : Expr) : MetaM ℕ := do
  let q ← parseRat e
  unless q.den = 1 && 0 ≤ q.num do
    throwError "unique_root_near: expected a natural number literal, got{indentExpr e}"
  return q.num.toNat

/-- Parse a `![a, b, …]` vector literal (delta-unfolding constants) with entries read by
`elem`. -/
partial def parseVec {α} [Inhabited α] (elem : Expr → MetaM α) (e : Expr) :
    MetaM (Array α) := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Matrix.vecCons, #[_, _, a, s] => return #[← elem a] ++ (← parseVec elem s)
  | some ``Matrix.vecEmpty, _ => return #[]
  | _, _ =>
    match ← unfoldDefinition? e with
    | some e' => parseVec elem e'
    | none => throwError "unique_root_near: cannot parse{indentExpr e}\nas a vector literal"

/-- Parse a `!![a, b; c, d]` matrix literal (delta-unfolding constants) into its rational
entries. -/
partial def parseMatrix (e : Expr) : MetaM (Array (Array ℚ)) := do
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``DFunLike.coe, #[_, _, _, _, f, x] =>
    if f.getAppFn.isConstOf ``Matrix.of then
      parseVec (parseVec parseRat) x
    else
      throwError "unique_root_near: cannot parse{indentExpr e}\nas a matrix literal"
  | _, _ =>
    match ← unfoldDefinition? e with
    | some e' => parseMatrix e'
    | none => throwError "unique_root_near: cannot parse{indentExpr e}\nas a matrix literal"

/-! ### Dense polynomial arithmetic on coefficient arrays -/

/-- Pointwise sum of dense coefficient arrays. -/
def polyAdd (a b : Array ℚ) : Array ℚ :=
  .ofFn (n := max a.size b.size) fun i => a.getD i 0 + b.getD i 0

/-- Negation of a dense coefficient array. -/
def polyNeg (a : Array ℚ) : Array ℚ := a.map (-·)

/-- Difference of dense coefficient arrays. -/
def polySub (a b : Array ℚ) : Array ℚ := polyAdd a (polyNeg b)

/-- Product of dense coefficient arrays. -/
def polyMul (a b : Array ℚ) : Array ℚ := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut res := Array.replicate (a.size + b.size - 1) (0 : ℚ)
  for i in [0:a.size] do
    for j in [0:b.size] do
      res := res.set! (i + j) (res[i + j]! + a[i]! * b[j]!)
  return res

/-- Power of a dense coefficient array. -/
def polyPow (a : Array ℚ) : ℕ → Array ℚ
  | 0 => #[1]
  | n + 1 => polyMul a (polyPow a n)

/-- Drop trailing zero coefficients. -/
def polyTrim (a : Array ℚ) : Array ℚ := Id.run do
  let mut a := a
  while !a.isEmpty && a.back! = 0 do a := a.pop
  return a

/-- Coefficients of the derivative. -/
def polyDeriv (a : Array ℚ) : Array ℚ :=
  .ofFn (n := a.size - 1) fun i => ((i.1 : ℚ) + 1) * a[i.1 + 1]!

/-- Evaluate a dense `ℚ` coefficient array at the Gaussian rational `vr + vi·i` by Horner's
scheme, returning the real and imaginary parts of the result (both exact rationals). -/
def evalGaussian (coeffs : Array ℚ) (vr vi : ℚ) : ℚ × ℚ := Id.run do
  let mut re : ℚ := 0
  let mut im : ℚ := 0
  for k in [0:coeffs.size] do
    let c := coeffs[coeffs.size - 1 - k]!
    -- (re + im·i)·(vr + vi·i) + c
    let nre := re * vr - im * vi + c
    let nim := re * vi + im * vr
    re := nre
    im := nim
  return (re, im)

/-- Evaluate a `ℚ[X]` expression (delta-unfolding constants) into its dense coefficient
array. -/
partial def parsePoly (e : Expr) : MetaM (Array ℚ) := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return #[(n : ℚ)]
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``HAdd.hAdd, #[_, _, _, _, x, y] => return polyAdd (← parsePoly x) (← parsePoly y)
  | some ``HSub.hSub, #[_, _, _, _, x, y] => return polySub (← parsePoly x) (← parsePoly y)
  | some ``HMul.hMul, #[_, _, _, _, x, y] => return polyMul (← parsePoly x) (← parsePoly y)
  | some ``HPow.hPow, #[_, _, _, _, x, n] => return polyPow (← parsePoly x) (← parseNat n)
  | some ``Neg.neg, #[_, _, x] => return polyNeg (← parsePoly x)
  | some ``Polynomial.X, _ => return #[0, 1]
  | some ``OfNat.ofNat, #[_, n, _] => return #[← parseRat n]
  | some ``OfScientific.ofScientific, _ => return #[← parseRat e]
  | some ``Nat.cast, #[_, _, x] => return #[← parseRat x]
  | some ``Int.cast, #[_, _, x] => return #[← parseRat x]
  | some ``Rat.cast, #[_, _, x] => return #[← parseRat x]
  | some ``DFunLike.coe, #[_, _, _, _, f, x] =>
    if f.getAppFn.isConstOf ``Polynomial.C then
      return #[← parseRat x]
    else if f.getAppFn.isConstOf ``Polynomial.monomial then
      let n ← parseNat f.getAppArgs[2]!
      return (Array.replicate n (0 : ℚ)).push (← parseRat x)
    else
      throwError "unique_root_near: cannot parse{indentExpr e}\nas a polynomial"
  | _, _ =>
    match ← unfoldDefinition? e with
    | some e' => parsePoly e'
    | none => throwError "unique_root_near: cannot parse{indentExpr e}\nas a polynomial"

/-! ### Rational rounding helpers -/

/-- Ceiling of a rational number, as an integer. -/
def ratCeil (q : ℚ) : ℤ := -((-q.num).fdiv q.den)

/-- A rational `B` on the grid `ℤ / 10^prec` with `B^2 > S` (an upper bound for `√S`). -/
def sqrtUpper (S : ℚ) (prec : ℕ) : ℚ :=
  if S ≤ 0 then 0
  else
    let scale : ℚ := (10 : ℚ) ^ prec
    let N := ratCeil (S * scale * scale)
    ((N.toNat.sqrt + 1 : ℕ) : ℚ) / scale

/-- An upper bound for `⌈log₁₀ q⌉`: a `k` with `q ≤ 10 ^ k` (0 for `q ≤ 1`). Computed from the
numerator's bit length — `q ≤ q.num < 2 ^ (log₂ num + 1) ≤ 10 ^ (0.31 (log₂ num + 1) + 1)` —
so it is a single GMP lookup even for enormous values, at the price of overshooting by a digit
or two (harmless where this is used: sizing the truncation width of `w`). -/
def log10Upper (q : ℚ) : ℕ :=
  if q ≤ 1 then 0 else (q.num.natAbs.log2 + 1) * 31 / 100 + 1

/-- Truncate `q` toward `-∞` to `k` decimal places: `⌊q * 10^k⌋ / 10^k`, so
`0 ≤ q - truncDecimals q k < 10^(-k)`. -/
def truncDecimals (q : ℚ) (k : ℕ) : ℚ :=
  let scale : ℤ := 10 ^ k
  (((q.num * scale).fdiv q.den : ℤ) : ℚ) / (scale : ℚ)

/-- Round `s` up to about `sig` significant decimal digits (never rounding below `s`). -/
def roundUpSig (s : ℚ) (sig : ℕ) : ℚ := Id.run do
  if s ≤ 0 then return 0
  let target : ℚ := (10 : ℚ) ^ sig
  let mut k := 0
  let mut scaled := s
  while scaled < target && k < 500 do
    scaled := scaled * 10
    k := k + 1
  return (ratCeil scaled : ℚ) / (10 : ℚ) ^ k

/-! ### `Expr` builders and `MetaM` tactic primitives

Everything the tactic feeds to its side goals is built as an `Expr` and dispatched through
`MetaM`/`TacticM` internals — no tactic `Syntax` is constructed. In particular numerals are built
with `mkNumeral`, which stores the (possibly enormous) integer directly in `Expr.lit (.natVal …)`
rather than serializing it to a decimal string; the O(N²) base-10 conversion that string route
incurred was the tactic's dominant cost on high-precision inputs. -/

/-- `Expr` numeral of value `q` at type `ty` (ℝ, ℚ, or `ℝ≥0`). The bignum is stored directly in
`Expr.lit (.natVal …)` via `mkNumeral`; unlike a `Syntax`-built numeral this never serializes the
integer to a decimal string. -/
def ratToExpr (q : ℚ) (ty : Expr) : MetaM Expr := do
  let numE ← Lean.Meta.mkNumeral ty q.num.natAbs
  let baseE ← if q.den = 1 then pure numE
              else mkAppM ``HDiv.hDiv #[numE, ← Lean.Meta.mkNumeral ty q.den]
  if q.num < 0 then
    if ty.isConstOf ``NNReal then
      throwError "unique_root_near: internal error: negative value {q} at ℝ≥0"
    mkAppM ``Neg.neg #[baseE]
  else pure baseE

/-- `ℚ[X]` `Expr` for a dense coefficient array, in the shape
`cₙ * X^n ± … ± c₀ * X^0` (using `Polynomial.C` for non-integer coefficients), matching the shape
the `hpd`/`hnum` coefficient `simp` lemmas expect. -/
def polyToExpr (coeffs : Array ℚ) : MetaM Expr := do
  let Xexpr ← mkAppOptM ``Polynomial.X #[some (mkConst ``Rat), none]
  let qXTy ← inferType Xexpr
  let Chom ← mkAppOptM ``Polynomial.C #[some (mkConst ``Rat), none]
  let mkTerm (c : ℚ) (k : ℕ) : MetaM Expr := do
    let cabs := if c < 0 then -c else c
    let coeffExpr ←
      if cabs.den = 1 then Lean.Meta.mkNumeral qXTy cabs.num.natAbs
      else mkAppM ``DFunLike.coe #[Chom, ← ratToExpr cabs (mkConst ``Rat)]
    mkAppM ``HMul.hMul #[coeffExpr, ← mkAppM ``HPow.hPow #[Xexpr, mkNatLit k]]
  let mut acc : Option Expr := none
  for k' in [0:coeffs.size] do
    let k := coeffs.size - 1 - k'
    let c := coeffs[k]!
    if c = 0 then continue
    let t ← mkTerm c k
    acc := some (← match acc with
      | none => if c < 0 then mkAppM ``Neg.neg #[t] else pure t
      | some s => if c < 0 then mkAppM ``HSub.hSub #[s, t] else mkAppM ``HAdd.hAdd #[s, t])
  match acc with
  | some t => return t
  | none => Lean.Meta.mkNumeral qXTy 0

/-- The `Expr` `(Polynomial.aeval x) p = ↑re + ↑im * I` (with `re`, `im : ℝ`, `x`, `p` over the
`ℚ`-algebra ℂ). -/
def mkAevalEq (x pE reE imE : Expr) : MetaM Expr := do
  let hom ← mkAppOptM ``Polynomial.aeval
    #[some (mkConst ``Rat), some (mkConst ``Complex), none, none, none, some x]
  let lhs ← mkAppM ``DFunLike.coe #[hom, pE]
  let rhs ← mkAppM ``HAdd.hAdd
    #[← mkAppM ``Complex.ofReal #[reE],
      ← mkAppM ``HMul.hMul #[← mkAppM ``Complex.ofReal #[imE], mkConst ``Complex.I]]
  mkEq lhs rhs

/-- Rewrite the target of `g` by the equation/iff `heq` (a global lemma `mkConst n` or a local
hypothesis `mkFVar h`); `symm` uses it right-to-left. Returns the rewritten goal. -/
def rwGoal (g : MVarId) (heq : Expr) (symm : Bool := false) : MetaM MVarId := do
  let r ← g.rewrite (← g.getType) heq symm
  g.replaceTargetEq r.eNew r.eqProof

/-- Run `norm_num` on `g` from `MetaM` (no `Syntax`): the default `simp` set plus the norm_num
extension, augmented with `consts` (each `(lemma, inv)`, `inv := true` for a `←` rewrite),
`unfolds` (definitions to unfold, e.g. a named polynomial or matrix), and `fvars` (local
hypotheses used as rewrites). With `pushCast`, the `push_cast` `simp` set is also added (for the
`ℝ≥0` coercion goals). Returns `none` when the goal is closed, else the simplified residual. -/
def normNumGoal (g : MVarId) (consts : Array (Name × Bool) := #[])
    (unfolds : Array Name := #[]) (fvars : Array FVarId := #[])
    (pushCast : Bool := false) : MetaM (Option MVarId) := g.withContext do
  let mut thms ← getSimpTheorems
  for (n, inv) in consts do thms ← thms.addConst n (inv := inv)
  for n in unfolds do thms ← thms.addDeclToUnfold n
  for h in fvars do thms ← thms.add (.fvar h) #[] (mkFVar h)
  let mut arr : Array SimpTheorems := #[thms]
  if pushCast then arr := arr.push (← Lean.Meta.NormCast.pushCastExt.getTheorems)
  let ctx ← Simp.mkContext (← Simp.Context.mkDefault).config (simpTheorems := arr)
              (congrTheorems := ← getSimpCongrTheorems)
  let tgt ← instantiateMVars (← g.getType)
  let r ← Mathlib.Meta.NormNum.deriveSimp ctx true tgt
  match ← r.ofTrue with
  | some prf => g.assign prf; return none
  | none => return some (← applySimpResultToTarget g tgt r)

/-- Close an equality goal with the `ring1` engine, from `MetaM`. -/
def ringGoal (g : MVarId) : MetaM Unit :=
  Mathlib.Tactic.AtomM.run .instances (Mathlib.Tactic.Ring.proveEq g)

/-- Prove proposition `type` by running `close` on a fresh metavariable (in the current local
context) — `close` must fully solve it — returning the resulting proof term. -/
def proveExpr (type : Expr) (close : MVarId → MetaM Unit) : TacticM Expr := do
  let m ← mkFreshExprMVar type
  close m.mvarId!
  instantiateMVars m

/-- Add `name : type := proof` to the main goal's local context, returning the new hypothesis. -/
def assertHyp (name : Name) (type proof : Expr) : TacticM FVarId := do
  let (fv, g) ← (← (← getMainGoal).assert name type proof).intro1P
  replaceMainGoal [g]
  return fv

/-! ### The tactic -/

/-- Upper bound on the number of decimal places of `q` (the least `e` with `q * 10 ^ e ∈ ℤ`,
i.e. `max (v₂ q.den) (v₅ q.den)`, when `q` denotes a decimal literal): since `2 ^ v₂(den) ≤ den`
and `5 ^ v₅(den) ≤ den`, the bit length `den.log2 + 1` bounds both valuations. A bound suffices
here — this only feeds `exponentiation.threshold`, where overshooting (by ≤ log₂ 10 ≈ 3.3×) is
harmless — and `Nat.log2` is a single GMP bit-length lookup, whereas computing the valuations
exactly by repeated division is O(D²) in the digit count `D` (it dominated the whole tactic at
high precision: ~21 s of a 61 s run at 100 000 digits). -/
def decimalPlaces (q : ℚ) : ℕ := q.den.log2 + 1

/-- Certify a unique root of a rational polynomial near a decimal approximation, via the
Newton–Kantorovich theorem. Usage, on a goal `UniqueRootNear (aeval · p) (toComplex v) r`:

```
unique_root_near M
```

where `M` is a rational approximation of the inverse Jacobian of the zero finder of `p` at
`v` (a `!![…]` literal or a definition unfolding to one). All remaining certificates are
computed from the goal and `M`; the named arguments `(y := …)` (default `r / 10`),
`(z₁ := …)` (default `1/2`), `(R := …)` (default `max r 10⁻⁶`), `(z₂ := …)` (default: an
exact rational estimate of the Lipschitz constant), `(d := …)`, `(a := …)` and `(B := …)`
override the computed values. `z₁`, `R` and `z₂` overrides must be numeric literals (they
size the truncation below).

The approximate-inverse check evaluates `p'` at `w`, the truncation of `v` to
`max 6 (⌈log₁₀(500·z₂/z₁)⌉) (⌈log₁₀(1/R)⌉)` decimal places (truncation error `ε`), and
transports the bound to `v` through the Lipschitz certificate: `z₁' + z₂ * ε ≤ z₁`, where
`z₁'` bounds `‖1 - M·p'(w)‖`. By construction `z₂ · ε` consumes ≤ ~0.2% of the `z₁` budget,
however ill-conditioned the input — a large `z₂` (clustered roots) simply buys `w` the digits
it genuinely needs, and since `hzr` forces `z₂ · r < 1` this never exceeds the digits of `r`
by more than ~3 — so the check's cost is independent of the precision of `v`, and a
certificate can only fail here if `M` is inaccurate at the ~`z₁` level. -/
syntax (name := uniqueRootNearStx) "unique_root_near" ppSpace term:max
  (" (" ident " := " term ")")* : tactic

elab_rules : tactic
  | `(tactic| unique_root_near $Mstx:term $[($ids:ident := $vals:term)]*) =>
    withMainContext do
    -- named arguments
    let mut named : Array (Name × Term) := #[]
    for id in ids, val in vals do
      let key := id.getId
      unless [`y, `z₁, `z₂, `R, `a, `B, `d].contains key do
        throwErrorAt id
          "unique_root_near: unknown parameter '{key}' (expected y, z₁, z₂, R, a, B or d)"
      named := named.push (key, val)
    let arg? (key : Name) : Option Term :=
      named.findSome? fun (n, t) => if n = key then some t else none

    -- dissect the goal
    let goalTy := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    unless goalTy.isAppOfArity ``UniqueRootNear 3 do
      throwError "unique_root_near: goal is not of the form\
        {indentD "UniqueRootNear (aeval · p) (toComplex v) r"}\ngot{indentExpr goalTy}"
    let args := goalTy.getAppArgs
    let p ← match args[0]!.consumeMData with
      | pe =>
        if pe.hasLooseBVars then
          throwError "unique_root_near: cannot extract the polynomial from{indentExpr args[0]!}"
        pure pe
    unless args[1]!.consumeMData.isApp do
      throwError "unique_root_near: expected `toComplex v`, got{indentExpr args[1]!}"
    let v := args[1]!.consumeMData.appArg!
    let rExpr := args[2]!

    -- meta-level certificate computation (exact rational arithmetic)
    let rq ← parseRat rExpr
    unless 0 < rq do
      throwError "unique_root_near: the radius must be a positive numeral, got{indentExpr rExpr}"
    let vq ← parseVec parseRat v
    unless vq.size = 2 do
      throwError "unique_root_near: expected a 2-dimensional approximation, got{indentExpr v}"
    -- The `hv0`/`hv1` and `hr` finishers rewrite the source decimal literals (radius, coordinates)
    -- to `↑m / 10 ^ e` and then evaluate `10 ^ e`. `norm_num`/`simp` refuse to compute `n ^ e`
    -- once `e` exceeds `exponentiation.threshold` (default 256), so an approximation with more than
    -- ~256 significant digits would otherwise be left unreduced. Raise the threshold — only where
    -- these finishers run — to cover the certificate's actual precision.
    let expThreshold : Nat :=
      max 256 (8 + vq.foldl (fun acc q => max acc (decimalPlaces q)) (decimalPlaces rq))
    let pq := polyTrim (← parsePoly p)
    let pdq := polyTrim (polyDeriv pq)
    if pdq.isEmpty then
      throwError "unique_root_near: the derivative of the polynomial is zero"
    let dVal := pdq.size - 1

    -- Names to unfold in the finishers when `p`, `v` or `M` are named constants (not literals).
    let constName? (e : Expr) : Option Name := if let .const n _ := e then some n else none
    let pName? := (constName? p).toArray
    let vName? := (constName? v).toArray

    -- Elaborate the inverse-Jacobian matrix once (feeds the row-sum bound `a` and the assembly
    -- lemma).
    let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
    let Mty ← mkAppM ``Matrix #[fin2, fin2, mkConst ``Real]
    let MExpr ← instantiateMVars (← Tactic.elabTermEnsuringType Mstx Mty)
    let Mq ← parseMatrix MExpr
    unless Mq.size = 2 && Mq.all (·.size = 2) do
      throwError "unique_root_near: expected a 2×2 matrix, got{indentExpr MExpr}"
    let MName? := (constName? MExpr).toArray

    -- Certificate `Expr`s (user overrides take precedence). For `z₁`, `R` and `z₂` we also
    -- keep the exact rational value, which sizes the truncated evaluation point `w`; for `a`
    -- and `B` the rational value feeds the `z₂` estimate (so it is only needed while `z₂` is
    -- not given).
    let realTy := mkConst ``Real
    let nnTy := mkConst ``NNReal
    let z₂Given := (arg? `z₂).isSome
    let overrideExpr (t : Term) (ty : Expr) : TacticM Expr := do
      instantiateMVars (← Tactic.elabTermEnsuringType t ty)
    -- an override elaborated to an `Expr`, with its exact rational value; `why` names the
    -- automatic computation that needs the value (skipped entirely with `needed := false`)
    let overrideRatE (t : Term) (ty : Expr) (what why : String) (needed : Bool := true) :
        TacticM (ℚ × Expr) := do
      let e ← overrideExpr t ty
      let q ← if !needed then pure 0 else
        try parseRat e
        catch _ => throwErrorAt t
          "unique_root_near: to {why}, ({what} := …) must be a numeric literal"
      pure (q, e)
    let estWhy := "estimate z₂ automatically (otherwise supply (z₂ := …) explicitly)"
    let truncWhy := "size the truncated derivative evaluation point automatically"

    let pdExpr ← polyToExpr pdq
    let r'E ← ratToExpr rq nnTy
    let yE ← match arg? `y with | some t => overrideExpr t nnTy | none => ratToExpr (rq / 10) nnTy
    let (z₁q, z₁E) ← match arg? `z₁ with
      | some t => overrideRatE t nnTy "z₁" truncWhy
      | none => pure (1 / 2, ← ratToExpr (1 / 2 : ℚ) nnTy)
    let dE ← match arg? `d with
      | some t => overrideExpr t (mkConst ``Nat)
      | none => pure (mkNatLit dVal)
    let (Bq, BE) ← match arg? `B with
      | some t => overrideRatE t realTy "B" estWhy (needed := !z₂Given)
      | none => do
        let q := sqrtUpper (vq[0]! ^ 2 + vq[1]! ^ 2) 4
        pure (q, ← ratToExpr q realTy)
    let (aq, aE) ← match arg? `a with
      | some t => overrideRatE t realTy "a" estWhy (needed := !z₂Given)
      | none => do
        -- row-sum bound on |M|, from the elaborated matrix
        let rowSum (i : ℕ) : ℚ := |(Mq[i]!)[0]!| + |(Mq[i]!)[1]!|
        let q := roundUpSig (max (rowSum 0) (rowSum 1)) 6
        pure (q, ← ratToExpr q realTy)
    -- The Lipschitz ball must contain both the certified root (radius `r`) and the truncated
    -- point `w` (distance ≤ ε from `v`); the `10⁻⁶` floor guarantees `ε ≤ R` for the adaptive
    -- `ε` below at no cost (`R` enters `z₂` only through the negligible `(3/2·R)^k` tail).
    let (Rq, RE) ← match arg? `R with
      | some t => overrideRatE t nnTy "R" truncWhy
      | none => do
        let q := max rq (1 / 1000000)
        pure (q, ← ratToExpr q nnTy)
    let (z₂q, z₂E) ← match arg? `z₂ with
      | some t => overrideRatE t nnTy "z₂" truncWhy
      | none => do
        -- exact rational evaluation of the sum bounded in `hnum`, rounded up
        let mut S : ℚ := 0
        for k in [0:dVal] do
          let mut inner : ℚ := 0
          for n in [0:dVal - k] do
            inner := inner + ((n + k + 1).choose (k + 1) : ℚ) * |pdq[n + k + 1]!| * Bq ^ n
          S := S + inner * ((3 / 2 : ℚ) * Rq) ^ k
        let q := roundUpSig (3 * aq * S) 3
        pure (q, ← ratToExpr q nnTy)

    -- The proxy point `w` for the approximate-inverse check: `v` truncated to `wDigits`
    -- decimal places, sized so the transported truncation error `z₂ · ε` consumes at most
    -- ~0.2% of the `z₁` budget (`10^wDigits ≥ 500·z₂/z₁`) and so `w` lies in the Lipschitz
    -- ball (`ε ≤ R`). This adapts to ill-conditioned inputs — `z₂` scales like the inverse
    -- root-separation, so clustered roots simply buy `w` the digits they genuinely require —
    -- while staying independent of the precision of `v`: since `hzr` forces `z₂ · r < 1`,
    -- `w` never carries more than ~3 digits beyond what the radius `r` itself demands.
    let wDigits : ℕ :=
      max 6 (max (log10Upper (500 * z₂q / z₁q)) (log10Upper (1 / Rq)))
    let εq : ℚ := 1 / 10 ^ wDigits
    let wq := vq.map (truncDecimals · wDigits)
    let εE ← ratToExpr εq nnTy

    -- `p'` at the truncated point `toComplex w` (exact Gaussian rational, bounded size), and
    -- the rounded-up row-sum bound `z₁'` on `|1 - M · p'(w)|` (as a 2×2 real matrix).
    let (pdwReQ, pdwImQ) := evalGaussian pdq wq[0]! wq[1]!
    let z₁'q := Id.run do
      let mut rows : Array ℚ := #[]
      for i in [0:2] do
        let mi0 := (Mq[i]!)[0]!
        let mi1 := (Mq[i]!)[1]!
        let c0 := (if i = 0 then (1 : ℚ) else 0) - (mi0 * pdwReQ + mi1 * pdwImQ)
        let c1 := (if i = 1 then (1 : ℚ) else 0) - (mi0 * (-pdwImQ) + mi1 * pdwReQ)
        rows := rows.push (|c0| + |c1|)
      return roundUpSig (max rows[0]! rows[1]!) 3
    let z₁'E ← ratToExpr z₁'q nnTy

    -- Shared evaluation: `p` at `toComplex v` and `p'` at `toComplex w` are exact Gaussian
    -- rationals, computed at the meta level so the residual (`hy0`/`hy1`) and inverse-bound
    -- (`hz1w`) finishers rewrite to a concrete value and do only rational arithmetic, instead
    -- of each re-expanding the (typeclass-heavy) `aeval`. (`p'` is never evaluated at `v`
    -- itself: at high precision that exact value — and its verification — dominated the
    -- runtime, and the certificate only needs it at the truncated `w`.)
    let (pvReQ, pvImQ) := evalGaussian pq vq[0]! vq[1]!
    let pvReE ← ratToExpr pvReQ realTy
    let pvImE ← ratToExpr pvImQ realTy
    let pdwReE ← ratToExpr pdwReQ realTy
    let pdwImE ← ratToExpr pdwImQ realTy
    let v0E ← ratToExpr vq[0]! realTy
    let v1E ← ratToExpr vq[1]! realTy
    let tcV := args[1]!
    -- `w` as a `![w0, w1]` vector literal, and `toComplex w` (reusing the head symbol of the
    -- goal's `toComplex v`)
    let wE ← do
      let empty ← mkAppOptM ``Matrix.vecEmpty #[some realTy]
      let tail ← mkAppM ``Matrix.vecCons #[← ratToExpr wq[1]! realTy, empty]
      mkAppM ``Matrix.vecCons #[← ratToExpr wq[0]! realTy, tail]
    let tcW := mkApp tcV.consumeMData.appFn! wE
    let expOpts : Options → Options := (exponentiation.threshold.set · expThreshold)

    -- Assert `hv0`/`hv1 : (v : Fin 2 → ℝ) i = <rational>`, rewriting each decimal coordinate to
    -- the exact rational it denotes. This is where the (possibly thousands of digits long) decimal
    -- literals are consumed: `LawfulOfScientific.ofScientific_def` turns `OfScientific … e` into
    -- `↑m / 10 ^ e`, and `norm_num` folds `10 ^ e` into a numeral (with the raised exponentiation
    -- threshold — its scientific plugin otherwise caps the exponent at 256). Downstream finishers
    -- then see only ordinary `num / den` numerals.
    let assertDecimal (nm : Name) (i : ℕ) (vE : Expr) : TacticM FVarId := do
      (← getMainGoal).withContext do
        let ty ← mkEq (mkApp v (← Lean.Meta.mkNumeral fin2 i)) vE
        let pf ← proveExpr ty fun g => do
          unless (← withOptions expOpts <| normNumGoal g
              #[(``Lean.Grind.LawfulOfScientific.ofScientific_def, false)] vName?).isNone do
            throwError "unique_root_near: failed to convert the decimal coordinate '{nm}'"
        assertHyp nm ty pf
    let hv0 ← assertDecimal `hv0 0 v0E
    let hv1 ← assertDecimal `hv1 1 v1E

    -- Assert `hpv : (aeval (toComplex v)) p = ↑re + ↑im · I` and
    -- `hpdw : (aeval (toComplex w)) pd = ↑re + ↑im · I`, a single `aeval` expansion each.
    -- `Complex.ext_iff` splits into `re`/`im` after the expansion, and `v 0`/`v 1` are
    -- rewritten via `hv0`/`hv1` so no oversized decimal reaches `norm_num` (which then only
    -- expands the small complex/polynomial powers `(a + b·I) ^ k`); the components of the
    -- `![…]` literal `w` reduce by the default `Matrix.cons_val` simp lemmas.
    let expandClose (unfolds : Array Name) (g : MVarId) : MetaM Unit := do
      let g ← rwGoal g (← mkConstWithFreshMVarLevels ``Polynomial.aeval_def)
      let g ← rwGoal g (← mkConstWithFreshMVarLevels ``Polynomial.eval₂_eq_eval_map)
      unless (← normNumGoal g #[(``toComplex_apply, false), (``pow_succ, false),
          (``pow_zero, false), (``Complex.ext_iff, false)] unfolds #[hv0, hv1]).isNone do
        throwError "unique_root_near: could not evaluate p or p' at the approximation"
    let assertAeval (nm : Name) (x pE reE imE : Expr) (unfolds : Array Name) :
        TacticM FVarId := do
      (← getMainGoal).withContext do
        let ty ← mkAevalEq x pE reE imE
        assertHyp nm ty (← proveExpr ty (expandClose unfolds))
    let hpv ← assertAeval `hpv tcV p pvReE pvImE pName?
    let hpdw ← assertAeval `hpdw tcW pdExpr pdwReE pdwImE #[]

    -- Apply the assembly lemma; `apply` unifies its conclusion with the goal (solving `p`, `v`,
    -- `r`) and returns the 17 hypothesis goals in declaration order.
    let e ← mkAppOptM ``UniqueRootNear.of_certificates'
      #[p, pdExpr, MExpr, v, wE, some rExpr, r'E, yE, z₁E, z₁'E, z₂E, εE, RE, dE, aE, BE]
    let goals ←
      try (← getMainGoal).apply e
      catch err => throwError "unique_root_near: failed to apply \
        UniqueRootNear.of_certificates':{indentD err.toMessageData}"
    setGoals goals

    -- Finishers, each run directly on its side goal via `MetaM` (no `Syntax`). Every
    -- `norm_num`-style check goes through `normNumGoal`; `fin_cases` is replaced by rewriting
    -- `Fin.forall_fin_two`. `hdeg` alone keeps a constant `compute_degree!` script (no `MetaM`
    -- entry point).
    let close (g : MVarId) (consts : Array (Name × Bool) := #[]) (unfolds : Array Name := #[])
        (fvars : Array FVarId := #[]) (pushCast := false) : MetaM Unit := do
      match ← withOptions expOpts <| normNumGoal g consts unfolds fvars pushCast with
      | none => pure ()
      | some g' => throwError "goal not closed by norm_num; remaining:{indentD (← g'.getType)}"
    let coeArith : Array (Name × Bool) := #[(``NNReal.coe_add, false), (``NNReal.coe_mul, false),
      (``NNReal.coe_div, false), (``NNReal.coe_pow, false), (``NNReal.coe_one, false),
      (``NNReal.coe_ofNat, false)]
    let hnumConsts : Array (Name × Bool) :=
      #[(``Finset.sum_range_succ, false), (``Finset.sum_range_zero, false),
        (``Polynomial.C_ofNat, true), (``Polynomial.coeff_add, false),
        (``Polynomial.coeff_sub, false), (``Polynomial.coeff_neg, false),
        (``Polynomial.coeff_C_mul, false), (``Polynomial.coeff_X_pow, false),
        (``Polynomial.coeff_C, false), (``Polynomial.coeff_X, false)]
    let checks : Array (String × String × (MVarId → TacticM Unit)) := #[
      ("hr", "the radius coercion ℝ = ℝ≥0", fun g => do
        close g (coeArith.push (``NNReal.coe_ofNat, false)) (pushCast := true)),
      ("hpd", "computing the derivative polynomial", fun g => do
        match ← normNumGoal g #[(``Polynomial.C_ofNat, false)] pName? with
        | none => pure ()
        | some g' => ringGoal g'),
      ("hy0", "the residual bound |(M·p(v))₀| ≤ y", fun g => do
        close (← rwGoal g (mkFVar hpv)) (unfolds := MName?)),
      ("hy1", "the residual bound |(M·p(v))₁| ≤ y", fun g => do
        close (← rwGoal g (mkFVar hpv)) (unfolds := MName?)),
      ("hz1w", "the approximate-inverse bound ‖1 - M·p'(w)‖ ≤ z₁' at the truncated point",
        fun g => do
        let g ← rwGoal g (← mkConstWithFreshMVarLevels ``Fin.forall_fin_two)
        let g ← rwGoal g (mkFVar hpdw)
        close g #[(``Matrix.one_apply, false), (``Fin.sum_univ_two, false)] MName?),
      ("hw0", "the truncation error |v 0 - w 0| ≤ ε", fun g => do
        close g (fvars := #[hv0])),
      ("hw1", "the truncation error |v 1 - w 1| ≤ ε", fun g => do
        close g (fvars := #[hv1])),
      ("hεR", "ε ≤ R", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``NNReal.coe_le_coe) (symm := true))
          coeArith (pushCast := true)),
      ("hz1", "the combined approximate-inverse bound z₁' + z₂·ε ≤ z₁", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``NNReal.coe_le_coe) (symm := true))
          coeArith (pushCast := true)),
      ("hdeg", "the degree bound on the derivative", fun g => do
        setGoals [g]
        evalTactic (← `(tactic| compute_degree!))
        unless (← getUnsolvedGoals).isEmpty do
          throwError "compute_degree! left unsolved goals"),
      ("ha", "the row-sum bound ‖M‖ ≤ a", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``Fin.forall_fin_two))
          #[(``Fin.sum_univ_two, false)] MName?),
      ("hB", "the norm bound ‖v‖ ≤ B", fun g => do close g (fvars := #[hv0, hv1])),
      ("hB0", "0 ≤ B", fun g => do close g),
      ("hnum", "the Lipschitz certificate: coefficient sum ≤ z₂", fun g => do
        close g hnumConsts #[``Nat.choose]),
      ("hrR", "r ≤ R", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``NNReal.coe_le_coe) (symm := true))
          coeArith (pushCast := true)),
      ("hyr", "the Newton–Kantorovich inequality y + z₁·r + z₂·r²/2 ≤ r", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``NNReal.coe_le_coe) (symm := true))
          coeArith (pushCast := true)),
      ("hzr", "the contraction inequality z₁ + z₂·r < 1", fun g => do
        close (← rwGoal g (← mkConstWithFreshMVarLevels ``NNReal.coe_lt_coe) (symm := true))
          coeArith (pushCast := true))]

    let gs := (← getGoals).toArray
    unless gs.size = checks.size do
      throwError "unique_root_near: internal error: expected {checks.size} side goals, \
        found {gs.size}"
    for i in [0:checks.size] do
      let (tag, what, check) := checks[i]!
      try check gs[i]!
      catch err => throwError
        "unique_root_near: certificate check '{tag}' ({what}) failed:{indentD err.toMessageData}"
    setGoals []

end UniqueRootNearTactic
