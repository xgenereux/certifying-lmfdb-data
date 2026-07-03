import CertifyingLmfdbData.Polynomial.UniqueRootNear

/-!
# The `unique_root_near` tactic

`unique_root_near M` closes a goal of the form

```
UniqueRootNear (aeval · p) (toComplex v) r
```

given an approximate inverse-Jacobian matrix `M`. All other certificate data is derived
automatically, by exact rational arithmetic **at the meta level**:

* `y := r / 10`, `z₁ := r` and `R := r` (overridable with `(y := …)`, `(z₁ := …)`,
  `(R := …)`),
* the derivative polynomial `pd`, its degree bound `d`, the row-sum bound `a` on `M`, and the
  norm bound `B` on `v` are computed from the goal and the certificate,
* the Lipschitz certificate `z₂` is estimated as `3a` times the binomial-weighted coefficient
  sum appearing in the `hnum` hypothesis (with `R = r` tiny, the `k ≥ 1` tail is negligible,
  so this is essentially sharp); override with `(z₂ := …)` if needed.

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
  `simp`/`norm_num` calls. -/
noncomputable def UniqueRootNear.of_certificates' (p pd : ℚ[X])
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) {r : ℝ} (r' y z₁ z₂ R : ℝ≥0)
    (d : ℕ) (a B : ℝ)
    (hr : r = r')
    (hpd : derivative p = pd)
    (hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (hy1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y)
    (hz1 : ∀ i, ∑ j, |(1 - M *
        !![(aeval (toComplex v) pd).re, -(aeval (toComplex v) pd).im;
           (aeval (toComplex v) pd).im, (aeval (toComplex v) pd).re]) i j| ≤ z₁)
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
  exact .of_certificates p M v hy0 hy1 hz1 hdeg ha hB hB0 hnum hrR hyr hzr

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

/-! ### Syntax builders -/

/-- Term syntax for a rational literal (`n`, `-n`, `n / d` or `-(n / d)`). -/
def ratToTerm (q : ℚ) : TacticM Term := do
  let num : Term := Syntax.mkNumLit (toString q.num.natAbs)
  let base : Term ← if q.den = 1 then pure num else do
    let den : Term := Syntax.mkNumLit (toString q.den)
    `($num / $den)
  if q.num < 0 then `(-$base) else pure base

/-- Term syntax for the polynomial with the given coefficients, in the shape
`c_n * Polynomial.X ^ n ± … ± c_0 * Polynomial.X ^ 0` (using `Polynomial.C` for non-integer
coefficients). -/
def polyToTerm (coeffs : Array ℚ) : TacticM Term := do
  let mut acc : Option Term := none
  for k' in [0:coeffs.size] do
    let k := coeffs.size - 1 - k'
    let c := coeffs[k]!
    if c = 0 then continue
    let cabs ← ratToTerm (if c < 0 then -c else c)
    let kLit : Term := Syntax.mkNumLit (toString k)
    let t : Term ←
      if c.den = 1 then `($cabs * Polynomial.X ^ $kLit)
      else `(Polynomial.C ($cabs : ℚ) * Polynomial.X ^ $kLit)
    acc := some (← match acc with
      | none => if c < 0 then `(-$t) else pure t
      | some s => if c < 0 then `($s - $t) else `($s + $t))
  match acc with
  | some t => return t
  | none => `((0 : Polynomial ℚ))

/-- Term syntax referring to the constant `n`. -/
def cid (n : Name) : Term := ⟨(mkCIdent n).raw⟩

/-- Build `simp [l₁, …, lₙ]` (or `simp only […]`) from a list of lemma/definition terms. -/
def mkSimp (lemmas : Array Term) (only : Bool := false) :
    TacticM (TSyntax `tactic) := do
  let args ← lemmas.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  if only then `(tactic| simp only [$args,*]) else `(tactic| simp [$args,*])

/-- Build `norm_num [l₁, …, lₙ]`; the flag in each pair requests a reversed (`←`) rewrite. -/
def mkNormNum (lemmas : Array (Term × Bool)) :
    TacticM (TSyntax `tactic) := do
  if lemmas.isEmpty then `(tactic| norm_num) else do
    let args ← lemmas.mapM fun (t, rev) =>
      if rev then `(Lean.Parser.Tactic.simpLemma| ← $t) else
        `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| norm_num [$args,*])

/-! ### The tactic -/

/-- Certify a unique root of a rational polynomial near a decimal approximation, via the
Newton–Kantorovich theorem. Usage, on a goal `UniqueRootNear (aeval · p) (toComplex v) r`:

```
unique_root_near M
```

where `M` is a rational approximation of the inverse Jacobian of the zero finder of `p` at
`v` (a `!![…]` literal or a definition unfolding to one). All remaining certificates are
computed from the goal and `M`; the named arguments `(y := …)` (default `r / 10`),
`(z₁ := …)` (default `r`), `(R := …)` (default `r`), `(z₂ := …)` (default: an exact
rational estimate of the Lipschitz constant), `(d := …)`, `(a := …)` and `(B := …)`
override the computed values. -/
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
      -- | _ => throwError "unique_root_near: cannot extract the polynomial from{indentExpr args[0]!}"
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
    let pq := polyTrim (← parsePoly p)
    let pdq := polyTrim (polyDeriv pq)
    if pdq.isEmpty then
      throwError "unique_root_near: the derivative of the polynomial is zero"
    let dVal := pdq.size - 1

    -- syntax for the certificate arguments (user overrides take precedence); for `a`, `B`
    -- and `R` we also track the exact rational value, which feeds the `z₂` estimate
    let pdStx ← polyToTerm pdq
    let r'Stx ← ratToTerm rq
    let yStx ← match arg? `y with | some t => pure t | none => ratToTerm (rq / 10)
    let z₁Stx ← match arg? `z₁ with | some t => pure t | none => ratToTerm rq
    let dStx ← match arg? `d with
      | some t => pure t
      | none => pure (Syntax.mkNumLit (toString dVal) : Term)
    let z₂Given := (arg? `z₂).isSome
    -- exact rational value of an override, needed only when `z₂` is estimated automatically
    let overrideRat (t : Term) (ty : Expr) (what : String) : TacticM ℚ := do
      if z₂Given then return 0  -- unused
      let e ← Tactic.elabTermEnsuringType t ty
      try parseRat (← instantiateMVars e)
      catch _ => throwErrorAt t
        "unique_root_near: to estimate z₂ automatically, ({what} := …) must be a numeric \
        literal; otherwise supply (z₂ := …) explicitly"
    let (Bq, BStx) ← match arg? `B with
      | some t => do pure (← overrideRat t (mkConst ``Real) "B", t)
      | none => do
        let q := sqrtUpper (vq[0]! ^ 2 + vq[1]! ^ 2) 4
        pure (q, ← ratToTerm q)
    let (aq, aStx) ← match arg? `a with
      | some t => do pure (← overrideRat t (mkConst ``Real) "a", t)
      | none => do
        -- row-sum bound on |M|, computed from the elaborated matrix
        let fin2 := mkApp (mkConst ``Fin) (mkNatLit 2)
        let Mty ← mkAppM ``Matrix #[fin2, fin2, mkConst ``Real]
        let MExpr ← Tactic.elabTermEnsuringType Mstx Mty
        let Mq ← parseMatrix (← instantiateMVars MExpr)
        unless Mq.size = 2 && Mq.all (·.size = 2) do
          throwError "unique_root_near: expected a 2×2 matrix, got{indentExpr MExpr}"
        let rowSum (i : ℕ) : ℚ :=
          |(Mq[i]!)[0]!| + |(Mq[i]!)[1]!|
        let q := roundUpSig (max (rowSum 0) (rowSum 1)) 6
        pure (q, ← ratToTerm q)
    let (Rq, RStx) ← match arg? `R with
      | some t => do pure (← overrideRat t (mkConst ``NNReal) "R", t)
      | none => pure (rq, ← ratToTerm rq)
    let z₂Stx ← match arg? `z₂ with
      | some t => pure t
      | none => do
        -- exact rational evaluation of the sum bounded in `hnum`, rounded up
        let mut S : ℚ := 0
        for k in [0:dVal] do
          let mut inner : ℚ := 0
          for n in [0:dVal - k] do
            inner := inner + ((n + k + 1).choose (k + 1) : ℚ) * |pdq[n + k + 1]!| * Bq ^ n
          S := S + inner * ((3 / 2 : ℚ) * Rq) ^ k
        ratToTerm (roundUpSig (3 * aq * S) 3)

    -- unfolding hints for the finishers: p, v and M when they are named constants
    let constTerm? (e : Expr) : Option Term :=
      if let .const n _ := e then some (cid n) else none
    let pU := (constTerm? p).toArray
    let vU := (constTerm? v).toArray
    let MU : Array Term := if Mstx.raw.isIdent then #[Mstx] else #[]

    -- Shared evaluation: the values of `p` and its derivative at `toComplex v` are exact
    -- Gaussian rationals (rational polynomial, rational `v`). We evaluate them at the meta
    -- level so the residual (`hy0`, `hy1`) and inverse-bound (`hz1`) finishers can rewrite to
    -- a concrete value and do only rational arithmetic, instead of each re-expanding `aeval`
    -- through the (typeclass-heavy) `ℚ`-algebra homomorphism machinery.
    let (pvReQ, pvImQ) := evalGaussian pq vq[0]! vq[1]!
    let (pdReQ, pdImQ) := evalGaussian pdq vq[0]! vq[1]!
    let tcVStx ← Term.exprToSyntax args[1]!
    let pStx' ← Term.exprToSyntax p
    let (pvReStx, pvImStx, pdReStx, pdImStx) ← (·,·,·,·) <$> ratToTerm pvReQ <*>
      ratToTerm pvImQ <*> ratToTerm pdReQ <*> ratToTerm pdImQ
    -- Prove `aeval (toComplex v) p = A + B·I` and the same for the derivative, in one `aeval`
    -- expansion each: `Complex.ext_iff` splits into `re`/`im` *after* the expansion, so the
    -- typeclass-heavy homomorphism work is done once per polynomial instead of once per side
    -- goal (`p` feeds `hy0` and `hy1`; `pd` feeds both `fin_cases` branches of `hz1`).
    -- Rewrite `aeval (toComplex v) p` (a `ℚ`-algebra `AlgHom`) to `eval (toComplex v)`
    -- on the polynomial mapped into `ℂ[X]` *before* expanding: `Polynomial.eval`/`Polynomial.map`
    -- use `ℂ`'s own ring structure via direct simp lemmas, so the expansion no longer triggers
    -- the (expensive, ~60 ms/goal) `AlgHom` hom-class / `Module ℚ ℂ` instance search that
    -- `map_add`/`map_mul`/`map_pow` on the bundled `aeval` would.
    let expandTac ← do
      let s ← mkSimp (pU ++ vU ++ #[cid ``toComplex_apply, cid ``pow_succ, cid ``pow_zero,
        cid ``Complex.ext_iff])
      `(tactic| rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] <;>
        $s:tactic <;> norm_num)
    let cval (reS imS : Term) : TacticM Term :=
      `(((($reS : ℝ) : ℂ) + (($imS : ℝ) : ℂ) * Complex.I))
    let shares : Array (Ident × Term) := #[
      (mkIdent `hpv, ← `((Polynomial.aeval $tcVStx) $pStx' = $(← cval pvReStx pvImStx))),
      (mkIdent `hpdv, ← `((Polynomial.aeval $tcVStx) ($pdStx : Polynomial ℚ)
        = $(← cval pdReStx pdImStx)))]
    for (nm, ty) in shares do
      let t ← `(tactic| have $nm:ident : $ty := by $expandTac:tactic)
      try evalTactic t
      catch e => throwError
        "unique_root_near: failed to evaluate p or p' at the approximation \
        ('{nm.getId}'):{indentD e.toMessageData}"
    let hpv := shares[0]!.1
    let hpdv := shares[1]!.1

    -- apply the assembly lemma
    let refTac ← `(tactic| refine UniqueRootNear.of_certificates' _ $pdStx $Mstx _
      $r'Stx $yStx $z₁Stx $z₂Stx $RStx $dStx $aStx $BStx
      ?hr ?hpd ?hy0 ?hy1 ?hz1 ?hdeg ?ha ?hB ?hB0 ?hnum ?hrR ?hyr ?hzr)
    try evalTactic refTac
    catch e => throwError
      "unique_root_near: failed to apply UniqueRootNear.of_certificates':\
      {indentD e.toMessageData}"

    -- finishers
    let hrTac ← `(tactic| first
      | (push_cast <;> norm_num <;> done)
      | norm_num [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat])
    let hpdTac ← do
      let nn ← mkNormNum ((pU.map (·, false)).push (cid ``Polynomial.C_ofNat, false))
      `(tactic| $nn:tactic <;> ring1)
    let hyTac ← do
      -- rewrite `aeval (toComplex v) p` to its precomputed complex value (removing `aeval`),
      -- then finish with `re`/`im`/matrix unfolding + rational arithmetic
      let s ← mkSimp MU
      `(tactic| rw [$hpv:ident] <;> $s:tactic <;> norm_num)
    let hz1Tac ← do
      let s ← mkSimp (MU ++ #[cid ``Matrix.one_apply, cid ``Fin.sum_univ_two])
      `(tactic| intro i <;> fin_cases i <;> rw [$hpdv:ident] <;> $s:tactic <;> norm_num)
    let hdegTac ← `(tactic| compute_degree!)
    let haTac ← do
      let s ← mkSimp (MU ++ #[cid ``Fin.sum_univ_two])
      `(tactic| intro i <;> fin_cases i <;> $s:tactic <;> norm_num)
    let hBTac ← do
      let s ← mkSimp vU
      `(tactic| $s:tactic <;> norm_num)
    let hB0Tac ← `(tactic| norm_num)
    let hnumTac ← do
      let s ← mkSimp #[cid ``Finset.sum_range_succ, cid ``Finset.sum_range_zero] (only := true)
      let nn ← mkNormNum #[(cid ``Polynomial.C_ofNat, true),
        (cid ``Polynomial.coeff_add, false), (cid ``Polynomial.coeff_sub, false),
        (cid ``Polynomial.coeff_neg, false), (cid ``Polynomial.coeff_C_mul, false),
        (cid ``Polynomial.coeff_X_pow, false), (cid ``Polynomial.coeff_C, false),
        (cid ``Polynomial.coeff_X, false), (cid ``Nat.choose, false)]
      `(tactic| $s:tactic <;> $nn:tactic)
    let hrRTac ← `(tactic| first
      | (norm_num <;> done)
      | (rw [← NNReal.coe_le_coe] <;> push_cast <;> norm_num))
    let hyrTac ← `(tactic| first
      | (norm_num <;> done)
      | (apply le_of_lt <;> norm_num <;> done)
      | (rw [← NNReal.coe_le_coe] <;> push_cast <;> norm_num))
    let hzrTac ← `(tactic| first
      | (norm_num <;> done)
      | (rw [← NNReal.coe_lt_coe] <;> push_cast <;> norm_num))

    let checks : Array (String × String × TSyntax `tactic) := #[
      ("hr", "the radius coercion ℝ = ℝ≥0", hrTac),
      ("hpd", "computing the derivative polynomial", hpdTac),
      ("hy0", "the residual bound |(M·p(v))₀| ≤ y", hyTac),
      ("hy1", "the residual bound |(M·p(v))₁| ≤ y", hyTac),
      ("hz1", "the approximate-inverse bound ‖1 - M·p'(v)‖ ≤ z₁", hz1Tac),
      ("hdeg", "the degree bound on the derivative", hdegTac),
      ("ha", "the row-sum bound ‖M‖ ≤ a", haTac),
      ("hB", "the norm bound ‖v‖ ≤ B", hBTac),
      ("hB0", "0 ≤ B", hB0Tac),
      ("hnum", "the Lipschitz certificate: coefficient sum ≤ z₂", hnumTac),
      ("hrR", "r ≤ R", hrRTac),
      ("hyr", "the Newton–Kantorovich inequality y + z₁·r + z₂·r²/2 ≤ r", hyrTac),
      ("hzr", "the contraction inequality z₁ + z₂·r < 1", hzrTac)]

    let gs := (← getGoals).toArray
    unless gs.size = checks.size do
      throwError "unique_root_near: internal error: expected {checks.size} side goals, \
        found {gs.size}"
    for i in [0:checks.size] do
      let (tag, what, tac) := checks[i]!
      setGoals [gs[i]!]
      try evalTactic tac
      catch e => throwError
        "unique_root_near: certificate check '{tag}' ({what}) failed:{indentD e.toMessageData}"
      let rem ← getUnsolvedGoals
      unless rem.isEmpty do throwError
        "unique_root_near: certificate check '{tag}' ({what}) was not fully solved; \
        the certificate may be inadequate. Remaining:\n{goalsToMessageData rem}"
    setGoals []

end UniqueRootNearTactic
