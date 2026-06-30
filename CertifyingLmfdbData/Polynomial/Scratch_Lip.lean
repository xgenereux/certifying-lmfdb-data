import Mathlib
import CertifyingLmfdbData.Polynomial.NewtonKantorovich

open Polynomial Finset Complex ContinuousLinearMap

open Polynomial Finset in
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

noncomputable def toComplex : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow _ _).trans Complex.equivRealProdCLM.symm

@[simp] lemma toComplex_apply (h) : toComplex h = h 0 + h 1 * I := by
  simp [toComplex, Complex.equivRealProdCLM_symm_apply]

@[simp] lemma toComplex_symm_apply (z) : toComplex.symm z = ![z.re, z.im] := by
  simp [toComplex]

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

/-- **Bridge.** Conjugating complex multiplication by `c` through `toComplex` gives an
operator on `ℝ²` whose (sup-norm) operator norm is at most `2 * ‖c‖`. -/
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

/-- **Radius bridge.** `toComplex` distorts the norm by at most `√2`. -/
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

/-- **Assembled bound for `z₂`.** For any polynomial `p`, preconditioner `A`, base point `v`
and radius `Rb` bounding `‖x - v‖`, the operator `A ∘ (DF x - DF v)` is Lipschitz in `x - v`,
with an explicit constant built from the absolute, `(√2·Rb)`-weighted Taylor coefficients at
`v` of the *complex* derivative `Q = (p')_ℂ`. -/
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
    _ ≤ ‖A‖ * (2 * ‖c‖) := (opNorm_comp_le _ _).trans
          (by gcongr; exact opNorm_toComplex_mul_le c)
    _ ≤ ‖A‖ * (2 * (L * (Real.sqrt 2 * ‖x - v‖))) := by
        gcongr
        exact hcbound.trans (by gcongr; exact norm_toComplex_le _)
    _ = 2 * Real.sqrt 2 * ‖A‖ * L * ‖x - v‖ := by ring

/-- **`hz₂` for `newton_kantorovich_fd`.** Packages the bound into the exact shape required by
the Newton–Kantorovich hypothesis: a single numeric inequality `hz` (constant `≤ z₂`) yields the
`NNReal`/`closedEBall` Lipschitz statement. -/
lemma polyToZeroFinderDeriv_lipschitzOn
    (p : ℚ[X]) (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (v : Fin 2 → ℝ) (R z₂ : NNReal)
    (hz : 2 * Real.sqrt 2 * ‖A‖ *
        (∑ k ∈ range (p.derivative.map (algebraMap ℚ ℂ)).natDegree,
          ‖(taylor (toComplex v) (p.derivative.map (algebraMap ℚ ℂ))).coeff (k + 1)‖
            * (Real.sqrt 2 * R) ^ k) ≤ z₂) :
    ∀ x ∈ Metric.closedEBall v (R : ENNReal),
      ‖A.comp (polyToZeroFinderDeriv p x - polyToZeroFinderDeriv p v)‖₊ ≤ z₂ * ‖x - v‖₊ := by
  intro x hx
  rw [Metric.mem_closedEBall, edist_nndist, nndist_eq_nnnorm] at hx
  replace hx : ‖x - v‖ ≤ (R : ℝ) := by exact_mod_cast hx
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  refine (polyToZeroFinderDeriv_lipschitz_bound p A v hx).trans ?_
  gcongr

/-- **Operator norm of a matrix in the sup norm.** `‖A‖ ≤ C` whenever every absolute row sum of
the matrix is `≤ C`. (The true value is the max absolute row sum; this is the `≤` you need.) -/
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

-- demonstration: the concrete `A_mat` from `Example.lean`
def A_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-0.11915000248755223,  -0.045813378411717155;
      0.045813378411717155, -0.11915000248755223]

example : ‖LinearMap.toContinuousLinearMap (Matrix.mulVecLin A_mat)‖ ≤ 0.16497 := by
  apply opNorm_mulVecLin_le _ (by norm_num)
  intro i
  fin_cases i <;> simp [A_mat, Fin.sum_univ_two] <;> norm_num

/-! ### End-to-end: `z₂` for `myPoly = X⁵ + X + 1` -/

noncomputable def myPoly : Polynomial ℚ := X ^ 5 + X + 1

def vv : Fin 2 → ℝ := ![0.877438833123346, -0.744861766619744]

noncomputable def AA : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A_mat)

set_option maxHeartbeats 1000000 in
-- the `simp`/`norm_num` over the expanded coefficient sum and `√2`/‖v‖ bounds is heavy
lemma example_z₂ (x) (hx : x ∈ Metric.closedEBall vv ((2 : NNReal) : ENNReal)) :
    ‖AA.comp (polyToZeroFinderDeriv myPoly x - polyToZeroFinderDeriv myPoly vv)‖₊
      ≤ 400 * ‖x - vv‖₊ := by
  refine polyToZeroFinderDeriv_lipschitzOn myPoly AA vv 2 400 ?_ x hx
  -- discharge the single numeric obligation `hz`
  have hQ : myPoly.derivative.map (algebraMap ℚ ℂ) = 5 * X ^ 4 + 1 := by
    have h : myPoly.derivative = 5 * X ^ 4 + 1 := by norm_num [myPoly, C_ofNat]
    rw [h]; simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat]
  rw [hQ, show (5 * X ^ 4 + 1 : ℂ[X]).natDegree = 4 from by compute_degree!]
  set c := toComplex vv with hcdef
  have htay : taylor c (5 * X ^ 4 + 1 : ℂ[X])
      = monomial 0 (5 * c ^ 4 + 1) + monomial 1 (20 * c ^ 3) + monomial 2 (30 * c ^ 2)
        + monomial 3 (20 * c) + monomial 4 5 := by
    rw [taylor_apply]
    simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.one_comp, Polynomial.ofNat_comp,
      ← C_mul_X_pow_eq_monomial, map_ofNat, map_add, map_mul, map_pow, C_1]
    ring
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [htay, coeff_add, coeff_monomial, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
    add_zero, zero_add, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
    NNReal.coe_ofNat, pow_zero, pow_one, mul_one]
  -- norms of the (complex) coefficients
  rw [show ‖(20 : ℂ) * c ^ 3‖ = 20 * ‖c‖ ^ 3 by rw [norm_mul, norm_pow]; norm_num,
    show ‖(30 : ℂ) * c ^ 2‖ = 30 * ‖c‖ ^ 2 by rw [norm_mul, norm_pow]; norm_num,
    show ‖(20 : ℂ) * c‖ = 20 * ‖c‖ by rw [norm_mul]; norm_num,
    show ‖(5 : ℂ)‖ = 5 by norm_num]
  -- numeric bounds for ‖c‖, ‖AA‖, √2
  have hc : ‖c‖ ≤ 1.151 := by
    have hsq : ‖c‖ ^ 2 = vv 0 ^ 2 + vv 1 ^ 2 := by
      rw [hcdef, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, toComplex_apply]
      simp only [add_re, add_im, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, zero_add, mul_im]
      ring
    have : ‖c‖ ^ 2 ≤ 1.151 ^ 2 := by rw [hsq, vv]; norm_num
    nlinarith [norm_nonneg c, this]
  have hA : ‖AA‖ ≤ 0.16497 := by
    rw [AA]; apply opNorm_mulVecLin_le _ (by norm_num)
    intro i; fin_cases i <;> simp [A_mat, Fin.sum_univ_two] <;> norm_num
  have hs : Real.sqrt 2 ≤ 1.4143 := by
    rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  calc 2 * Real.sqrt 2 * ‖AA‖ *
        (20 * ‖c‖ ^ 3 + 30 * ‖c‖ ^ 2 * (Real.sqrt 2 * 2) + 20 * ‖c‖ * (Real.sqrt 2 * 2) ^ 2
          + 5 * (Real.sqrt 2 * 2) ^ 3)
      ≤ 2 * 1.4143 * 0.16497 *
          (20 * 1.151 ^ 3 + 30 * 1.151 ^ 2 * (1.4143 * 2) + 20 * 1.151 * (1.4143 * 2) ^ 2
            + 5 * (1.4143 * 2) ^ 3) := by gcongr
    _ ≤ 400 := by norm_num
