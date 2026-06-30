-- import Matlib.ForMathlib.SumFin
-- import Matlib.Banach
-- import Matlib.PowerSeries
-- import Matlib.Tactic
import CertifyingLmfdbData.Polynomial.NewtonKantorovich
import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Complex
universe u z

open Qq in
simproc_decl Complex.I_pow_eq_pow_mod' (Complex.I ^ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(ℂ), ~q(Complex.I ^ $n) => do
    let some n' := Lean.Expr.nat? n | return .continue
    if n' < 4 then return .continue
    return .visit <| .mk q(I ^ ($n % 4)) <| .some q(Complex.I_pow_eq_pow_mod $n)

@[simp] theorem Polynomial.aeval_ofNat {R : Type u} {A : Type z}
    [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ) [n.AtLeastTwo] :
    (aeval x) (ofNat(n) : R[X]) = ofNat(n) :=
  Polynomial.aeval_natCast (R := R) x n

noncomputable def toComplex : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow _ _).trans Complex.equivRealProdCLM.symm

set_option autoImplicit true

@[simp] lemma toComplex_apply : toComplex h = h 0 + h 1 * I := by
  simp [toComplex, Complex.equivRealProdCLM_symm_apply]

@[simp] lemma toComplex_symm_apply : toComplex.symm z = ![z.re, z.im] := by
  simp [toComplex]

lemma hasFDerivAt_toComplex : HasFDerivAt (𝕜 := ℝ) toComplex toComplex x :=
  toComplex.hasFDerivAt

lemma hasFDerivAt_toComplex_symm : HasFDerivAt (𝕜 := ℝ) toComplex.symm toComplex.symm x :=
  toComplex.symm.hasFDerivAt

noncomputable def polyToZeroFinder (p : Polynomial ℚ) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  toComplex.symm ∘ (p.aeval ·) ∘ toComplex

noncomputable def polyToZeroFinderDeriv (p : Polynomial ℚ) (v : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
    ((ContinuousLinearMap.mul ℝ ℂ (p.derivative.aeval (toComplex v))).comp
      (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ))

lemma polyToZeroFinderDeriv_sub {p v₁ v₂} :
    polyToZeroFinderDeriv p v₁ - polyToZeroFinderDeriv p v₂ =
      (toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.mul ℝ ℂ
          (p.derivative.aeval (toComplex v₁) - p.derivative.aeval (toComplex v₂))).comp
          (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ)) := by
  simp [polyToZeroFinderDeriv]

lemma continuous_polyToZeroFinderDeriv : Continuous (polyToZeroFinderDeriv p) := by
  delta polyToZeroFinderDeriv
  fun_prop

lemma hasFDerivAt_polyToZeroFinder :
    HasFDerivAt (𝕜 := ℝ) (polyToZeroFinder p) (polyToZeroFinderDeriv p x) x := by
  refine HasFDerivAt.comp (𝕜 := ℝ) (g := toComplex.symm) _ hasFDerivAt_toComplex_symm
    (HasFDerivAt.comp (𝕜 := ℝ) _ ?_ hasFDerivAt_toComplex)
  convert (p.hasFDerivAt_aeval (toComplex x)).restrictScalars ℝ
  ext y
  simp [mul_comm]

lemma opNorm_mul {x : ℂ} :
    ‖ContinuousLinearMap.mul ℝ ℂ x‖ = ‖x‖ := by
  simp only [ContinuousLinearMap.opNorm_mul_apply]

-- lemma lipschitzOnWith_derivZeroFinder {x₀ : Fin 2 → ℝ} {R : NNReal} {p} :
--     LipschitzOnWith K (polyToZeroFinderDeriv p) (Metric.closedBall x₀ R) := by
--   rw [lipschitzOnWith_iff_norm_sub_le]
--   intro x hx y hy
--   simp only [polyToZeroFinderDeriv_sub]
--   grw [ContinuousLinearMap.opNorm_comp_le]
--   grw [ContinuousLinearMap.opNorm_comp_le]
--   simp only [ContinuousLinearMap.opNorm_mul_apply]
--   sorry

@[simp] lemma polyToZeroFinderDeriv_apply_one_zero :
    polyToZeroFinderDeriv p v ![1, 0] =
      ![((aeval (v 0 + v 1 * I)) (derivative p)).re,
        ((aeval (v 0 + v 1 * I)) (derivative p)).im] := by
  simp [polyToZeroFinderDeriv]

@[simp] lemma polyToZeroFinderDeriv_apply_zero_one :
    polyToZeroFinderDeriv p v ![0, 1] =
      ![-((aeval (v 0 + v 1 * I)) (derivative p)).im,
        ((aeval (v 0 + v 1 * I)) (derivative p)).re] := by
  simp [polyToZeroFinderDeriv]

macro "reducePoly" : tactic =>
  `(tactic| {
    simp only [polyToZeroFinder, pow_succ, pow_zero, one_mul, map_add, map_sub, map_neg, map_mul,
      aeval_X, map_one,
      Function.comp_apply, toComplex_apply, Fin.isValue, toComplex_symm_apply, Nat.succ_eq_add_one,
      Nat.reduceAdd, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, one_re, one_im, aeval_ofNat,
      and_true, Fin.isValue, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons,
      Matrix.cons_sub_cons, Matrix.empty_sub_empty,
      zero_add, Matrix.empty_add_empty, Matrix.vecCons_inj, add_left_inj]
    constructor <;> ring
    })

noncomputable def myPoly : Polynomial ℚ := X ^ 5 - X - 1

noncomputable def myPolyDeriv : Polynomial ℚ := 5 * X ^ 4 - 1

def zeroFinder : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x ↦
  ![x 0 ^ 5 - 10 * x 0 ^ 3 * x 1 ^ 2 + 5 * x 0 * x 1 ^ 4 - x 0 - 1,
    5 * x 0 ^ 4 * x 1 - 10 * x 0 ^ 2 * x 1 ^ 3 + x 1 ^ 5 - x 1]

lemma polyToZeroFinder_myPoly : polyToZeroFinder myPoly = zeroFinder := by
  ext x : 1
  simp only [myPoly, zeroFinder]
  reducePoly

lemma myPoly_derivative : myPoly.derivative = myPolyDeriv := by
  norm_num [myPoly, myPolyDeriv, C_ofNat]

noncomputable def derivZeroFinder (v : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    polyToZeroFinderDeriv myPoly v

def v : Fin 2 → ℝ := ![0.18123244446987538, -1.0839541013177107]

def A_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0.11124510611637174,  0.10508700867158703;
     -0.10508700867158703,  0.11124510611637174]

noncomputable def A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin A_mat

lemma y : ‖A (polyToZeroFinder myPoly v)‖₊ ≤ 1e-16 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty]
  simp only [polyToZeroFinder_myPoly]
  simp only [A, A_mat, zeroFinder, v]
  norm_num

-- TODO: does `Module.Basis.opNorm_le` really require CompleteSpace?
theorem opNorm_le_of_basisFun {ι 𝕜 F : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜]
    {u : (ι → 𝕜) →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (Pi.basisFun 𝕜 ι i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • M := by
  convert (Module.Basis.opNorm_le (Pi.basisFun 𝕜 ι) (u := u) hM hu).trans ?_
  suffices (Pi.basisFun 𝕜 ι).equivFunL = ContinuousLinearMap.id 𝕜 (ι → 𝕜) by
    grw [this, ContinuousLinearMap.norm_id_le]
    simp
  ext v i
  simp

@[simp] lemma Pi.single_fin_two_zero {x : ℝ} : Pi.single 0 x = ![x, 0] := funext <| by simp
@[simp] lemma Pi.single_fin_two_one {x : ℝ} : Pi.single 1 x = ![0, x] := funext <| by simp
example {x : ℝ} : Pi.single 0 x = ![x, 0, 0] := funext <| by simp [Fin.forall_fin_succ]
example {x : ℝ} : Pi.single 1 x = ![0, x, 0] := funext <| by simp [Fin.forall_fin_succ]
example {x : ℝ} : Pi.single 2 x = ![0, 0, x] := funext <| by simp [Fin.forall_fin_succ]

lemma z₁ : ‖1 - A.comp (derivZeroFinder v)‖₊ ≤ 1e-11 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 5e-12) (by norm_num) ?h1).trans (by norm_num)
  simp [myPoly_derivative, myPolyDeriv, pow_succ, v, A, A_mat, pi_norm_le_iff_of_nonempty]
  norm_num

open NNReal

open Finset in
/-- Coefficient Lipschitz bound for a complex polynomial on a ball of radius `R`:
`Q(v+w) - Q(v)` is controlled by `‖w‖` times the absolute Taylor coefficients at `v`. -/
lemma norm_eval_add_sub_eval_le
    (Q : ℂ[X]) (v w : ℂ) {R : ℝ} (hw : ‖w‖ ≤ R) :
    ‖Q.eval (v + w) - Q.eval v‖
      ≤ (∑ k ∈ range Q.natDegree, ‖(taylor v Q).coeff (k + 1)‖ * R ^ k) * ‖w‖ := by
  have key : Q.eval (v + w) - Q.eval v
      = ∑ k ∈ range Q.natDegree, (taylor v Q).coeff (k + 1) * w ^ (k + 1) := by
    have e1 : Q.eval (v + w) = (taylor v Q).eval w := by
      rw [taylor_apply, eval_comp, eval_add, eval_X, eval_C, add_comm v w]
    have e2 : Q.eval v = (taylor v Q).coeff 0 := (taylor_coeff_zero v Q).symm
    rw [e1, e2, eval_eq_sum_range, natDegree_taylor, sum_range_succ']
    simp
  rw [key, sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow, mul_assoc, pow_succ]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg w) hw k) (norm_nonneg w))
    (norm_nonneg _)

/-- Conjugating complex multiplication by `c` through `toComplex` gives an operator on `ℝ²`
whose (sup-norm) operator norm is at most `2 * ‖c‖`. -/
lemma opNorm_toComplex_mul_le (c : ℂ) :
    ‖(toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.mul ℝ ℂ c).comp (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ))‖
      ≤ 2 * ‖c‖ := by
  rw [show (2 : ℝ) * ‖c‖ = Fintype.card (Fin 2) • ‖c‖ by simp [nsmul_eq_mul]]
  apply opNorm_le_of_basisFun (norm_nonneg c)
  intro i
  rw [pi_norm_le_iff_of_nonempty]
  fin_cases i <;>
  · intro j
    fin_cases j <;>
      simp [mul_comm, abs_re_le_norm, abs_im_le_norm]

/-- `toComplex` distorts the norm by at most `√2`. -/
lemma norm_toComplex_le (u : Fin 2 → ℝ) : ‖toComplex u‖ ≤ Real.sqrt 2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (toComplex u)),
    show Real.sqrt 2 * ‖u‖ = Real.sqrt (2 * ‖u‖ ^ 2) from by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg u)]]
  apply Real.sqrt_le_sqrt
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, toComplex_apply]
  have h0 : |u 0| ≤ ‖u‖ := norm_le_pi_norm u 0
  have h1 : |u 1| ≤ ‖u‖ := norm_le_pi_norm u 1
  simp only [add_re, add_im, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, zero_add, mul_im]
  nlinarith [abs_nonneg (u 0), abs_nonneg (u 1), sq_abs (u 0), sq_abs (u 1), norm_nonneg u]

/-- `‖A‖ ≤ C` whenever every absolute row sum of the matrix is `≤ C` (sup norm).
The true value is the max absolute row sum. -/
lemma opNorm_mulVecLin_le {n : Type*} [Fintype n] (M : Matrix n n ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hrow : ∀ i, ∑ j, |M i j| ≤ C) :
    ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  rw [LinearMap.coe_toContinuousLinearMap', pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVecLin_apply]
  have hsum : M.mulVec x i = ∑ j, M i j * x j := by simp [Matrix.mulVec, dotProduct]
  calc |M.mulVec x i| = |∑ j, M i j * x j| := by rw [hsum]
    _ ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        gcongr
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm x j
    _ = (∑ j, |M i j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ C * ‖x‖ := by gcongr; exact hrow i

open Finset in
/-- Assembled Lipschitz bound: `A ∘ (DF x - DF v)` is Lipschitz in `x - v`, with constant
built from the absolute, `(√2·Rb)`-weighted Taylor coefficients at `v` of `(p')_ℂ`. -/
lemma polyToZeroFinderDeriv_lipschitz_bound
    (p : ℚ[X]) (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (v : Fin 2 → ℝ) {Rb : ℝ}
    {x : Fin 2 → ℝ} (hx : ‖x - v‖ ≤ Rb) :
    ‖A.comp (polyToZeroFinderDeriv p x - polyToZeroFinderDeriv p v)‖
      ≤ 2 * Real.sqrt 2 * ‖A‖ *
          (∑ k ∈ range (p.derivative.map (algebraMap ℚ ℂ)).natDegree,
            ‖(taylor (toComplex v) (p.derivative.map (algebraMap ℚ ℂ))).coeff (k + 1)‖
              * (Real.sqrt 2 * Rb) ^ k)
          * ‖x - v‖ := by
  set Q := p.derivative.map (algebraMap ℚ ℂ) with hQ
  set L := ∑ k ∈ range Q.natDegree,
      ‖(taylor (toComplex v) Q).coeff (k + 1)‖ * (Real.sqrt 2 * Rb) ^ k with hL
  have hRb : 0 ≤ Rb := (norm_nonneg _).trans hx
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun k _ =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hRb) k)
  have ha : ∀ z, p.derivative.aeval z = Q.eval z := fun z => by rw [hQ, eval_map, aeval_def]
  have hwle : ‖toComplex (x - v)‖ ≤ Real.sqrt 2 * Rb :=
    (norm_toComplex_le _).trans (by gcongr)
  set c := p.derivative.aeval (toComplex x) - p.derivative.aeval (toComplex v) with hc
  have hcbound : ‖c‖ ≤ L * ‖toComplex (x - v)‖ := by
    have hxv : toComplex x = toComplex v + toComplex (x - v) := by rw [map_sub]; ring
    rw [hc, ha, ha, hxv]
    exact norm_eval_add_sub_eval_le Q (toComplex v) (toComplex (x - v)) hwle
  calc ‖A.comp (polyToZeroFinderDeriv p x - polyToZeroFinderDeriv p v)‖
      = ‖A.comp ((toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
            ((ContinuousLinearMap.mul ℝ ℂ c).comp (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ)))‖ := by
        rw [polyToZeroFinderDeriv_sub]
    _ ≤ ‖A‖ * (2 * ‖c‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by gcongr; exact opNorm_toComplex_mul_le c)
    _ ≤ ‖A‖ * (2 * (L * (Real.sqrt 2 * ‖x - v‖))) := by
        gcongr
        exact hcbound.trans (by gcongr; exact norm_toComplex_le _)
    _ = 2 * Real.sqrt 2 * ‖A‖ * L * ‖x - v‖ := by ring

open Finset in
/-- `hz₂` for `newton_kantorovich_fd`: a single numeric inequality `hz` yields the
`NNReal`/`closedEBall` Lipschitz statement. -/
lemma polyToZeroFinderDeriv_lipschitzOn
    (p : ℚ[X]) (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (v : Fin 2 → ℝ) (R z : NNReal)
    (hz : 2 * Real.sqrt 2 * ‖A‖ *
        (∑ k ∈ range (p.derivative.map (algebraMap ℚ ℂ)).natDegree,
          ‖(taylor (toComplex v) (p.derivative.map (algebraMap ℚ ℂ))).coeff (k + 1)‖
            * (Real.sqrt 2 * R) ^ k) ≤ z) :
    ∀ x ∈ Metric.closedEBall v (R : ENNReal),
      ‖A.comp (polyToZeroFinderDeriv p x - polyToZeroFinderDeriv p v)‖₊ ≤ z * ‖x - v‖₊ := by
  intro x hx
  rw [Metric.mem_closedEBall, edist_nndist, nndist_eq_nnnorm] at hx
  replace hx : ‖x - v‖ ≤ (R : ℝ) := by exact_mod_cast hx
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  refine (polyToZeroFinderDeriv_lipschitz_bound p A v hx).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
-- the `simp`/`norm_num` over the expanded coefficient sum and `√2`/‖v‖ bounds is heavy
lemma z₂ (x) (hx : x ∈ Metric.closedEBall v 2) :
    ‖A.comp (derivZeroFinder x - derivZeroFinder v)‖₊ ≤ 400 * ‖x - v‖₊ := by
  simp only [derivZeroFinder]
  refine polyToZeroFinderDeriv_lipschitzOn myPoly A v 2 400 ?_ x ?_
  · -- the single numeric obligation `hz`
    have hQ : myPoly.derivative.map (algebraMap ℚ ℂ) = 5 * X ^ 4 - 1 := by
      simp [myPoly_derivative, myPolyDeriv]
    rw [hQ, show (5 * X ^ 4 - 1 : ℂ[X]).natDegree = 4 from by compute_degree!]
    set c := toComplex v with hcdef
    have htay : taylor c (5 * X ^ 4 - 1 : ℂ[X])
        = monomial 0 (5 * c ^ 4 - 1) + monomial 1 (20 * c ^ 3) + monomial 2 (30 * c ^ 2)
          + monomial 3 (20 * c) + monomial 4 5 := by
      rw [taylor_apply]
      simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp,
        Polynomial.X_comp, Polynomial.one_comp, Polynomial.ofNat_comp,
        ← C_mul_X_pow_eq_monomial, map_ofNat, map_sub, map_mul, map_pow, C_1]
      ring
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [htay, coeff_add, coeff_monomial, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
      add_zero, zero_add, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
      NNReal.coe_ofNat, pow_zero, pow_one, mul_one, Complex.norm_mul, norm_ofNat, norm_pow,
      ge_iff_le]
    have hc : ‖c‖ ≤ 1.1 := by
      have hsq : ‖c‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [hcdef, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, toComplex_apply]
        simp only [add_re, add_im, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, zero_add, mul_im]
        ring
      have : ‖c‖ ^ 2 ≤ 1.1 ^ 2 := by rw [hsq, v]; norm_num
      nlinarith [norm_nonneg c, this]
    have hA : ‖A‖ ≤ 0.21634 := by
      rw [A]; apply opNorm_mulVecLin_le _ (by norm_num)
      intro i; fin_cases i <;> simp [A_mat, Fin.sum_univ_two] <;> norm_num
    have hs : Real.sqrt 2 ≤ 1.4143 := by
      rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    grw [hc, hA, hs, hs]
    norm_num
  · simpa using hx

lemma test :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - v‖₊ ≤ 1e-15 := by
  have := newton_kantorovich_fd
    (F := polyToZeroFinder myPoly)
    (DF := derivZeroFinder)
    (by simp)
    (fun x ↦ hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (x₀ := v)
    (A := A)
    (z₂ := 400)
    (R := 2)
    (r := 1e-15)
    y z₁ z₂ (by apply le_of_lt; norm_cast; norm_num) (by apply le_of_lt; norm_num) (by norm_num)
  -- have : (1 : ℝ) * 2⁻¹ ≤ 3 := by? norm_num
  exact this

#print axioms test

-- #check newton_kantorovich hasFDerivAt_zeroFinder (by fun_prop)
