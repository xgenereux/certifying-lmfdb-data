import CertifyingLmfdbData.Polynomial.Example

noncomputable section

namespace DegSix

open Polynomial

def myPoly : Polynomial ℚ := X^6 - 5*X^4 - 50 * X^2 + 125
def myPolyDeriv : Polynomial ℚ := 6 * X ^ 5 - 20 * X ^ 3 - 100 * X

def zeroFinder : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x ↦ ![
  x 0 ^ 6 - 15 * x 0 ^ 4 * x 1 ^ 2 + 15 * x 0 ^ 2 * x 1 ^ 4 - x 1 ^ 6 - 5 * x 0 ^ 4 +
  30 * x 0 ^ 2 * x 1 ^ 2 - 5 * x 1 ^ 4 - 50 * x 0 ^ 2 + 50 * x 1 ^ 2 + 125,
  6 * x 0 ^ 5 * x 1 - 20 * x 0 ^ 3 * x 1 ^ 3 + 6 * x 0 * x 1 ^ 5 - 20 * x 0 ^ 3 * x 1 +
  20 * x 0 * x 1 ^ 3 - 100 * x 0 * x 1]

def rroot1 : Fin 2 → ℝ := ![-3.0016143454854741319417131953855135509439233234822720487499, 0]
def rA1_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ -0.0016105823418225894202625671015800570118581107319413733500872, 0;
      0, -0.0016105823418225894202625671015800570118581107319413733500872 ]

def rroot2 : Fin 2 → ℝ := ![-1.4917135581481935578368807432879800495511374280152413050117, 0]
def rA2_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0.0058397219432993508175108135283434777310184356523066979515940, 0;
      0, 0.0058397219432993508175108135283434777310184356523066979515940 ]

def rroot3 : Fin 2 → ℝ := ![1.4917135581481935578368807432879800495511374280152413050117, 0]
def rA3_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ -0.0058397219432993508175108135283434777310184356523066979515940, 0;
      0, -0.0058397219432993508175108135283434777310184356523066979515940 ]

def rroot4 : Fin 2 → ℝ := ![3.0016143454854741319417131953855135509439233234822720487499, 0]
def rA4_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0.0016105823418225894202625671015800570118581107319413733500872, 0;
      0, 0.0016105823418225894202625671015800570118581107319413733500872 ]

def croot1 : Fin 2 → ℝ := ![0, 2.4969777769510355226216439250267029033550572578622404151129]
def cA1_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0, -0.0016105823418225894202625671015800570118581107319413733500872;
      -0.0016105823418225894202625671015800570118581107319413733500872, 0 ]

open Complex NNReal

/-! ### Real root `rroot1` -/

noncomputable def rA1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin rA1_mat

lemma polyToZeroFinder_myPoly : polyToZeroFinder myPoly = zeroFinder := by
  ext x : 1
  simp only [myPoly, zeroFinder]
  -- like `reducePoly`, but the coefficients `5, 50, 125` need `re`/`im` of numerals reduced
  simp only [polyToZeroFinder, pow_succ, pow_zero, one_mul, map_add, map_sub, map_mul,
    aeval_X,
    Function.comp_apply, toComplex_apply, Fin.isValue, toComplex_symm_apply, Nat.succ_eq_add_one,
    Nat.reduceAdd, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, aeval_ofNat, Complex.re_ofNat,
    Complex.im_ofNat,
    and_true, Fin.isValue, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons,
    Matrix.cons_sub_cons, Matrix.empty_sub_empty,
    zero_add, Matrix.empty_add_empty, Matrix.vecCons_inj, add_left_inj]
  constructor <;> ring

lemma myPoly_derivative : myPoly.derivative = myPolyDeriv := by
  norm_num [myPoly, myPolyDeriv, C_ofNat]
  ring

noncomputable def derivZeroFinder (v : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  polyToZeroFinderDeriv myPoly v

lemma ry1 : ‖rA1 (polyToZeroFinder myPoly rroot1)‖₊ ≤ 1e-58 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty]
  simp only [polyToZeroFinder_myPoly]
  simp only [rA1, rA1_mat, zeroFinder, rroot1]
  norm_num

lemma rz1_1 : ‖1 - rA1.comp (derivZeroFinder rroot1)‖₊ ≤ 1e-57 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 5e-58) (by norm_num) ?h1).trans (by norm_num)
  simp [myPoly_derivative, myPolyDeriv, pow_succ, rroot1, rA1, rA1_mat,
    pi_norm_le_iff_of_nonempty]
  norm_num

-- the `simp`/`grw` over the expanded coefficient sum and `√2`/‖c‖ bounds is heavy
lemma rz2_1 (x) (hx : x ∈ Metric.closedEBall rroot1 1) :
    ‖rA1.comp (derivZeroFinder x - derivZeroFinder rroot1)‖₊ ≤ 40 * ‖x - rroot1‖₊ := by
  simp only [derivZeroFinder]
  refine polyToZeroFinderDeriv_lipschitzOn myPoly rA1 rroot1 1 40 ?_ x ?_
  · have hQ : myPoly.derivative.map (algebraMap ℚ ℂ) = myPolyDeriv.map (algebraMap ℚ ℂ) := by
      simp [myPoly_derivative]
    simp only [myPolyDeriv, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      Polynomial.map_pow, map_X] at hQ
    have hdeg : ((myPoly.derivative).map (algebraMap ℚ ℂ)).natDegree = 5 := by
      rw [hQ]
      compute_degree!
    rw [hdeg]
    set c := toComplex rroot1 with hcdef
    have htay : taylor c (myPoly.derivative.map (algebraMap ℚ ℂ)) = ?poly := by
      simp only [hQ, taylor_apply, sub_comp, mul_comp, ofNat_comp, Nat.cast_ofNat, pow_comp,
        X_comp]
      polynomial_nf
      rfl
    simp only [← monomial_zero_left, map_add, add_mul, monomial_mul_X, zero_add,
      monomial_mul_X_pow] at htay
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [htay, coeff_add, coeff_monomial, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte,
      add_zero, zero_add, OfNat.zero_ne_ofNat, OfNat.ofNat_ne_one, OfNat.one_ne_ofNat,
      NNReal.coe_ofNat, pow_zero, pow_one, mul_one, Complex.norm_mul, norm_ofNat,
      ge_iff_le]
    have hc : ‖c‖ ≤ 3.002 := by
      have hsq := norm_toComplex_sq rroot1
      have : ‖c‖ ^ 2 ≤ 3.002 ^ 2 := by rw [hcdef, hsq, rroot1]; norm_num
      nlinarith only [norm_nonneg c, this]
    have hA : ‖rA1‖ ≤ 0.00161059 := by
      rw [rA1]; apply opNorm_mulVecLin_le _ (by norm_num)
      intro i; fin_cases i <;> simp [rA1_mat, Fin.sum_univ_two] <;> norm_num
    have hs : Real.sqrt 2 ≤ 1.4143 := by
      rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    repeat grw [norm_add_le]
    grw [norm_sub_le]
    simp only [norm_neg, norm_ofNat, Complex.norm_mul, norm_pow, NNReal.coe_one, mul_one,
      Nat.ofNat_nonneg, Real.sq_sqrt]
    grw [hc, hA, hs, hs]
    norm_num
  · simpa using hx

lemma rtest1 :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - rroot1‖₊ ≤ 1e-57 := by
  have := newton_kantorovich_fd
    (F := polyToZeroFinder myPoly)
    (DF := derivZeroFinder)
    (by simp)
    (fun x ↦ hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (x₀ := rroot1)
    (A := rA1)
    (z₂ := 40)
    (R := 1)
    (r := 1e-57)
    ry1 rz1_1 rz2_1 (by apply le_of_lt; norm_cast; norm_num) (by apply le_of_lt; norm_num)
    (by norm_num)
  exact this

/-- Conjugation commutes with evaluation of a polynomial with rational coefficients. -/
lemma aeval_conj (z : ℂ) (p : Polynomial ℚ) :
    aeval (starRingEnd ℂ z) p = starRingEnd ℂ (aeval z p) := by
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := by ext q; simp
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, hcomp]

/-- If a root of `p` is uniquely determined by being close to an approximation `v` with zero
imaginary part, then that root is genuinely real: the complex conjugate of any root close to `v`
is again a root the same distance from `v`, so by uniqueness the root equals its own conjugate. -/
lemma im_zero_of_unique {p : Polynomial ℚ} {v : Fin 2 → ℝ} {r : ℝ≥0} (hv : v 1 = 0)
    (huniq : ∃! x, polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r)
    {x : Fin 2 → ℝ} (hx : polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r) : x 1 = 0 := by
  obtain ⟨y, -, huniq⟩ := huniq
  set x' : Fin 2 → ℝ := ![x 0, -(x 1)] with hx'
  have hconj : toComplex x' = starRingEnd ℂ (toComplex x) := by
    simp [hx']
  -- `toComplex x` is a genuine root of `p`
  have hroot : aeval (toComplex x) p = 0 := by
    have h := hx.1
    simp only [polyToZeroFinder, Function.comp_apply] at h
    have := congrArg toComplex h
    simpa using this
  -- the conjugate `x'` also satisfies the defining property
  have hx'P : polyToZeroFinder p x' = 0 ∧ ‖x' - v‖₊ ≤ r := by
    refine ⟨?_, ?_⟩
    · simp only [polyToZeroFinder, Function.comp_apply, hconj, aeval_conj, hroot, map_zero]
    · simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty] at hx ⊢
      intro i
      fin_cases i
      · simpa [hx', Pi.sub_apply] using hx.2 0
      · simpa [hx', Pi.sub_apply, hv, abs_neg] using hx.2 1
  -- uniqueness forces `x = x'`, hence `x 1 = -(x 1)`
  have hxx' : x = x' := (huniq x hx).trans (huniq x' hx'P).symm
  have := congrFun hxx' 1
  simp only [hx', Matrix.cons_val_one, Matrix.cons_val_zero] at this
  linarith

/-- The root approximated by `rroot1` is genuinely real. -/
lemma rroot1_im_zero {x : Fin 2 → ℝ}
    (hx : polyToZeroFinder myPoly x = 0 ∧ ‖x - rroot1‖₊ ≤ 1e-57) : x 1 = 0 :=
  im_zero_of_unique (by simp [rroot1]) rtest1 hx

end DegSix
