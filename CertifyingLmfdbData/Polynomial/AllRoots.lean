import CertifyingLmfdbData.Polynomial.Example

noncomputable section

section Lemmas

open Polynomial NNReal

/-- Conjugation commutes with evaluation of a polynomial with rational coefficients. -/
lemma aeval_conj (z : ℂ) (p : Polynomial ℚ) :
    aeval (starRingEnd ℂ z) p = starRingEnd ℂ (aeval z p) := by
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := by ext q; simp
  rw [aeval_def, aeval_def, Polynomial.hom_eval₂, hcomp]

/-- `UniqueRootNear f v r` certifies a unique root of `f` near `v`: it stores the root itself,
together with proofs that it is a root, that it lies within `r` of `v`, and that it is the only
such root. Here distance is measured in the sup norm (viewing `ℂ` as `ℝ²`), not in the usual
absolute value on `ℂ`: the certified region is a square of side `2 * r` centred at `v`, not a
disc. -/
structure UniqueRootNear (f : ℂ → ℂ) (v : ℂ) (r : ℝ) where
  /-- The root of `f` certified to be unique near `v`. -/
  root : ℂ
  isRoot : f root = 0
  near : max |(root - v).re| |(root - v).im| ≤ r
  unique : ∀ ⦃z : ℂ⦄, f z = 0 → max |(z - v).re| |(z - v).im| ≤ r → z = root

namespace UniqueRootNear

variable {f : ℂ → ℂ} {v : ℂ} {r : ℝ}

lemma re_near (h : UniqueRootNear f v r) : |(h.root - v).re| ≤ r :=
  (le_max_left _ _).trans h.near

lemma im_near (h : UniqueRootNear f v r) : |(h.root - v).im| ≤ r :=
  (le_max_right _ _).trans h.near

lemma existsUnique (h : UniqueRootNear f v r) :
    ∃! z : ℂ, f z = 0 ∧ max |(z - v).re| |(z - v).im| ≤ r :=
  ⟨h.root, ⟨h.isRoot, h.near⟩, fun _ hz ↦ h.unique hz.1 hz.2⟩

/-- Conjugating a certified unique root: since conjugation commutes with evaluation of a
rational polynomial and preserves sup-norm distances, a unique root near `v` gives a unique
root near `conj v`, namely the conjugate of the original root. -/
noncomputable def conj {p : Polynomial ℚ} (h : UniqueRootNear (aeval · p) v r) :
    UniqueRootNear (aeval · p) (starRingEnd ℂ v) r where
  root := starRingEnd ℂ h.root
  isRoot := by
    have hroot : aeval h.root p = 0 := h.isRoot
    change aeval (starRingEnd ℂ h.root) p = 0
    rw [_root_.aeval_conj, hroot, map_zero]
  near := by
    rw [← map_sub]
    simpa only [Complex.conj_re, Complex.conj_im, abs_neg] using h.near
  unique z hz hd := by
    have hz0 : aeval z p = 0 := hz
    have hz' : aeval (starRingEnd ℂ z) p = 0 := by rw [_root_.aeval_conj, hz0, map_zero]
    have hd' : max |(starRingEnd ℂ z - v).re| |(starRingEnd ℂ z - v).im| ≤ r := by
      rw [show starRingEnd ℂ z - v = starRingEnd ℂ (z - starRingEnd ℂ v) by
        rw [map_sub, Complex.conj_conj]]
      simpa only [Complex.conj_re, Complex.conj_im, abs_neg] using hd
    rw [← Complex.conj_conj z, h.unique hz' hd']

@[simp] lemma conj_root {p : Polynomial ℚ} (h : UniqueRootNear (aeval · p) v r) :
    h.conj.root = starRingEnd ℂ h.root := rfl

/-- The unique root near a point `v` with zero imaginary part is genuinely real: its complex
conjugate is again a root the same distance from `v`, so by uniqueness the root equals its own
conjugate. -/
lemma im_eq_zero {p : Polynomial ℚ} (h : UniqueRootNear (aeval · p) v r) (hv : v.im = 0) :
    h.root.im = 0 := by
  have hroot : aeval h.root p = 0 := h.isRoot
  have hd' : max |(starRingEnd ℂ h.root - v).re| |(starRingEnd ℂ h.root - v).im| ≤ r := by
    simpa [Complex.sub_re, Complex.sub_im, hv, abs_neg] using h.near
  have hconj : starRingEnd ℂ h.root = h.root :=
    h.unique (show aeval (starRingEnd ℂ h.root) p = 0 by rw [aeval_conj, hroot, map_zero]) hd'
  exact Complex.conj_eq_iff_im.mp hconj

end UniqueRootNear

/-- Translation between the defining property of the induced zero finder on `ℝ²` (with its sup
norm) and the corresponding property of the polynomial itself. -/
lemma polyToZeroFinder_root_near_iff {p : Polynomial ℚ} {v : Fin 2 → ℝ} {r : ℝ≥0}
    {x : Fin 2 → ℝ} :
    (polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r) ↔
      aeval (toComplex x) p = 0 ∧
        max |(toComplex x - toComplex v).re| |(toComplex x - toComplex v).im| ≤ r := by
  refine and_congr ?_ ?_
  · simp [polyToZeroFinder, Complex.ext_iff]
  · rw [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonneg r.coe_nonneg]
    simp [Fin.forall_fin_two]

/-- Package a Newton–Kantorovich uniqueness result for the zero finder on `ℝ²` into a
`UniqueRootNear` certificate for the polynomial itself. -/
noncomputable def UniqueRootNear.ofZeroFinder {p : Polynomial ℚ} {v : Fin 2 → ℝ} {r : ℝ≥0}
    (h : ∃! x, polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r) :
    UniqueRootNear (aeval · p) (toComplex v) r where
  root := toComplex h.choose
  isRoot := (polyToZeroFinder_root_near_iff.mp h.choose_spec.1).1
  near := (polyToZeroFinder_root_near_iff.mp h.choose_spec.1).2
  unique z hz hd := by
    have hx : polyToZeroFinder p (toComplex.symm z) = 0 ∧ ‖toComplex.symm z - v‖₊ ≤ r := by
      rw [polyToZeroFinder_root_near_iff]
      exact ⟨by simpa using hz, by simpa using hd⟩
    calc z = toComplex (toComplex.symm z) := by simp
      _ = toComplex h.choose := by rw [h.choose_spec.2 _ hx]

/-- If `p` is even (its evaluation is invariant under negating the point), then `polyToZeroFinder`
is invariant under negating the input, since `toComplex` is linear. -/
lemma polyToZeroFinder_neg {p : Polynomial ℚ} (heven : ∀ z : ℂ, aeval (-z) p = aeval z p)
    (x : Fin 2 → ℝ) : polyToZeroFinder p (-x) = polyToZeroFinder p x := by
  simp only [polyToZeroFinder, Function.comp_apply, map_neg, heven]

/-- For an even polynomial, negation is a distance-preserving bijection on the roots, so a root
uniquely determined near `v` transports to a root uniquely determined near `-v`. -/
lemma existsUnique_root_neg {p : Polynomial ℚ} {v : Fin 2 → ℝ} {r : ℝ≥0}
    (heven : ∀ z : ℂ, aeval (-z) p = aeval z p)
    (h : ∃! x, polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r) :
    ∃! x, polyToZeroFinder p x = 0 ∧ ‖x - (-v)‖₊ ≤ r := by
  obtain ⟨x₀, ⟨hroot, hdist⟩, huniq⟩ := h
  refine ⟨-x₀, ⟨?_, ?_⟩, ?_⟩
  · rw [polyToZeroFinder_neg heven]; exact hroot
  · rw [show -x₀ - -v = -(x₀ - v) by ring, nnnorm_neg]; exact hdist
  · rintro y ⟨hy1, hy2⟩
    have hneg : polyToZeroFinder p (-y) = 0 ∧ ‖-y - v‖₊ ≤ r := by
      refine ⟨?_, ?_⟩
      · rw [polyToZeroFinder_neg heven]; exact hy1
      · rw [show -y - v = -(y - -v) by ring, nnnorm_neg]; exact hy2
    exact neg_eq_iff_eq_neg.mp (huniq (-y) hneg)

lemma Real.sqrt_two_lt_d10 : √2 < 1.4142135624 := by
  rw [Real.sqrt_lt] <;> norm_num

lemma Real.sqrt_two_lt_d2 : √2 < 1.42 := by
  rw [Real.sqrt_lt] <;> norm_num

end Lemmas


namespace DegSix

open Polynomial Complex NNReal

def myPoly : Polynomial ℚ := X^6 - 5*X^4 - 50 * X^2 + 125
def myPolyDeriv : Polynomial ℚ := 6 * X ^ 5 - 20 * X ^ 3 - 100 * X

def zeroFinder : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x ↦ ![
  x 0 ^ 6 - 15 * x 0 ^ 4 * x 1 ^ 2 + 15 * x 0 ^ 2 * x 1 ^ 4 - x 1 ^ 6 - 5 * x 0 ^ 4 +
  30 * x 0 ^ 2 * x 1 ^ 2 - 5 * x 1 ^ 4 - 50 * x 0 ^ 2 + 50 * x 1 ^ 2 + 125,
  6 * x 0 ^ 5 * x 1 - 20 * x 0 ^ 3 * x 1 ^ 3 + 6 * x 0 * x 1 ^ 5 - 20 * x 0 ^ 3 * x 1 +
  20 * x 0 * x 1 ^ 3 - 100 * x 0 * x 1]

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
  !![ 0, 0.0015526150743595132569328994275272689662500775889625889026909;
      -0.0015526150743595132569328994275272689662500775889625889026909, 0 ]

def croot1' : Fin 2 → ℝ := ![0, -2.4969777769510355226216439250267029033550572578622404151129]

/-! ### Real root `rroot1` -/

noncomputable def rA1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin rA1_mat


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
    repeat grw [norm_add_le]
    grw [norm_sub_le]
    simp only [norm_neg, norm_ofNat, Complex.norm_mul, norm_pow, NNReal.coe_one, mul_one,
      Nat.ofNat_nonneg, Real.sq_sqrt]
    grw [hc, hA, Real.sqrt_two_lt_d2, Real.sqrt_two_lt_d2]
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

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot1`. -/
noncomputable def uniqueRootNear_rroot1 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot1) 1e-57 := by
  rw [show (1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ) by norm_num [← NNReal.coe_ofScientific]]
  exact .ofZeroFinder rtest1

/-- The root approximated by `rroot1` is real. -/
lemma rroot1_im_zero : uniqueRootNear_rroot1.root.im = 0 :=
  uniqueRootNear_rroot1.im_eq_zero (by simp [rroot1])


/-! ### Real root `rroot2` -/

noncomputable def rA2 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin rA2_mat

lemma ry2 : ‖rA2 (polyToZeroFinder myPoly rroot2)‖₊ ≤ 1e-58 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty]
  simp only [polyToZeroFinder_myPoly]
  simp only [rA2, rA2_mat, zeroFinder, rroot2]
  norm_num

lemma rz1_2 : ‖1 - rA2.comp (derivZeroFinder rroot2)‖₊ ≤ 1e-57 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 5e-58) (by norm_num) ?h1).trans (by norm_num)
  simp [myPoly_derivative, myPolyDeriv, pow_succ, rroot2, rA2, rA2_mat,
    pi_norm_le_iff_of_nonempty]
  norm_num

-- the `simp`/`grw` over the expanded coefficient sum and `√2`/‖c‖ bounds is heavy
lemma rz2_2 (x) (hx : x ∈ Metric.closedEBall rroot2 1) :
    ‖rA2.comp (derivZeroFinder x - derivZeroFinder rroot2)‖₊ ≤ 400 * ‖x - rroot2‖₊ := by
  simp only [derivZeroFinder]
  refine polyToZeroFinderDeriv_lipschitzOn myPoly rA2 rroot2 1 400 ?_ x ?_
  · have hQ : myPoly.derivative.map (algebraMap ℚ ℂ) = myPolyDeriv.map (algebraMap ℚ ℂ) := by
      simp [myPoly_derivative]
    simp only [myPolyDeriv, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      Polynomial.map_pow, map_X] at hQ
    have hdeg : ((myPoly.derivative).map (algebraMap ℚ ℂ)).natDegree = 5 := by
      rw [hQ]
      compute_degree!
    rw [hdeg]
    set c := toComplex rroot2 with hcdef
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
      have hsq := norm_toComplex_sq rroot2
      have : ‖c‖ ^ 2 ≤ 3.002 ^ 2 := by rw [hcdef, hsq, rroot2]; norm_num
      nlinarith only [norm_nonneg c, this]
    have hA : ‖rA2‖ ≤ 0.01 := by
      rw [rA2]; apply opNorm_mulVecLin_le _ (by norm_num)
      intro i; fin_cases i <;> simp [rA2_mat, Fin.sum_univ_two] <;> norm_num
    repeat grw [norm_add_le]
    grw [norm_sub_le]
    simp only [norm_neg, norm_ofNat, Complex.norm_mul, norm_pow, NNReal.coe_one, mul_one,
      Nat.ofNat_nonneg, Real.sq_sqrt]
    grw [hc, hA, Real.sqrt_two_lt_d2, Real.sqrt_two_lt_d2]
    norm_num
  · simpa using hx

lemma rtest2 :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - rroot2‖₊ ≤ 1e-57 := by
  have := newton_kantorovich_fd
    (F := polyToZeroFinder myPoly)
    (DF := derivZeroFinder)
    (by simp)
    (fun x ↦ hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (x₀ := rroot2)
    (A := rA2)
    (z₂ := 400)
    (R := 1)
    (r := 1e-57)
    ry2 rz1_2 rz2_2 (by apply le_of_lt; norm_cast; norm_num) (by apply le_of_lt; norm_num)
    (by norm_num)
  exact this

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot2`. -/
noncomputable def uniqueRootNear_rroot2 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot2) 1e-57 := by
  rw [show (1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ) by norm_num [← NNReal.coe_ofScientific]]
  exact .ofZeroFinder rtest2

/-- The root approximated by `rroot2` is real. -/
lemma rroot2_im_zero : uniqueRootNear_rroot2.root.im = 0 :=
  uniqueRootNear_rroot2.im_eq_zero (by simp [rroot2])


/-! ### Real roots `rroot3`, `rroot4` by evenness

`myPoly` is even, so its roots come in `± pairs`. `rroot3 = -rroot2` and `rroot4 = -rroot1`, so we
obtain them from `rtest2`/`rtest1` without redoing the Newton–Kantorovich estimates. -/

lemma myPoly_even (z : ℂ) : aeval (-z) myPoly = aeval z myPoly := by
  simp only [myPoly, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_ofNat]
  ring

lemma rtest3 :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - rroot3‖₊ ≤ 1e-57 := by
  have hrr : (rroot3 : Fin 2 → ℝ) = -rroot2 := by
    funext i; fin_cases i <;> simp [rroot3, rroot2, Pi.neg_apply]
  rw [hrr]
  exact existsUnique_root_neg myPoly_even rtest2

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot3`. -/
noncomputable def uniqueRootNear_rroot3 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot3) 1e-57 := by
  rw [show (1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ) by norm_num [← NNReal.coe_ofScientific]]
  exact .ofZeroFinder rtest3

/-- The root approximated by `rroot3` is real. -/
lemma rroot3_im_zero : uniqueRootNear_rroot3.root.im = 0 :=
  uniqueRootNear_rroot3.im_eq_zero (by simp [rroot3])

lemma rtest4 :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - rroot4‖₊ ≤ 1e-57 := by
  have hrr : (rroot4 : Fin 2 → ℝ) = -rroot1 := by
    funext i; fin_cases i <;> simp [rroot4, rroot1, Pi.neg_apply]
  rw [hrr]
  exact existsUnique_root_neg myPoly_even rtest1

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot4`. -/
noncomputable def uniqueRootNear_rroot4 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot4) 1e-57 := by
  rw [show (1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ) by norm_num [← NNReal.coe_ofScientific]]
  exact .ofZeroFinder rtest4

/-- The root approximated by `rroot4` is real. -/
lemma rroot4_im_zero : uniqueRootNear_rroot4.root.im = 0 :=
  uniqueRootNear_rroot4.im_eq_zero (by simp [rroot4])

/-! ### Complex `croot1` -/

noncomputable def cA1 : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin cA1_mat


lemma cy1 : ‖cA1 (polyToZeroFinder myPoly croot1)‖₊ ≤ 1e-58 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty]
  simp only [polyToZeroFinder_myPoly]
  simp only [cA1, cA1_mat, zeroFinder, croot1]
  norm_num

lemma cz1_1 : ‖1 - cA1.comp (derivZeroFinder croot1)‖₊ ≤ 1e-57 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 5e-58) (by norm_num) ?h1).trans (by norm_num)
  simp [myPoly_derivative, myPolyDeriv, pow_succ, croot1, cA1, cA1_mat,
    pi_norm_le_iff_of_nonempty]
  norm_num

-- the `simp`/`grw` over the expanded coefficient sum and `√2`/‖c‖ bounds is heavy
lemma cz2_1 (x) (hx : x ∈ Metric.closedEBall croot1 1) :
    ‖cA1.comp (derivZeroFinder x - derivZeroFinder croot1)‖₊ ≤ 40 * ‖x - croot1‖₊ := by
  simp only [derivZeroFinder]
  refine polyToZeroFinderDeriv_lipschitzOn myPoly cA1 croot1 1 40 ?_ x ?_
  · have hQ : myPoly.derivative.map (algebraMap ℚ ℂ) = myPolyDeriv.map (algebraMap ℚ ℂ) := by
      simp [myPoly_derivative]
    simp only [myPolyDeriv, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat,
      Polynomial.map_pow, map_X] at hQ
    have hdeg : ((myPoly.derivative).map (algebraMap ℚ ℂ)).natDegree = 5 := by
      rw [hQ]
      compute_degree!
    rw [hdeg]
    set c := toComplex croot1 with hcdef
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
    have hc : ‖c‖ ≤ 3 := by
      have hsq := norm_toComplex_sq croot1
      have : ‖c‖ ^ 2 ≤ 3 ^ 2 := by rw [hcdef, hsq, croot1]; norm_num
      nlinarith only [norm_nonneg c, this]
    have hA : ‖cA1‖ ≤ 0.002 := by
      rw [cA1]; apply opNorm_mulVecLin_le _ (by norm_num)
      intro i; fin_cases i <;> simp [cA1_mat, Fin.sum_univ_two] <;> norm_num
    repeat grw [norm_add_le]
    grw [norm_sub_le]
    simp only [norm_neg, norm_ofNat, Complex.norm_mul, norm_pow, NNReal.coe_one, mul_one,
      Nat.ofNat_nonneg, Real.sq_sqrt]
    grw [hc, hA, Real.sqrt_two_lt_d2, Real.sqrt_two_lt_d2]
    norm_num
  · simpa using hx

lemma ctest1 :
    ∃! x, polyToZeroFinder myPoly x = 0 ∧ ‖x - croot1‖₊ ≤ 1e-57 := by
  have := newton_kantorovich_fd
    (F := polyToZeroFinder myPoly)
    (DF := derivZeroFinder)
    (by simp)
    (fun x ↦ hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (x₀ := croot1)
    (A := cA1)
    (z₂ := 40)
    (R := 1)
    (r := 1e-57)
    cy1 cz1_1 cz2_1 (by apply le_of_lt; norm_cast; norm_num) (by apply le_of_lt; norm_num)
    (by norm_num)
  exact this

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1`. -/
noncomputable def uniqueRootNear_croot1 :
    UniqueRootNear (aeval · myPoly) (toComplex croot1) 1e-57 := by
  rw [show (1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ) by norm_num [← NNReal.coe_ofScientific]]
  exact .ofZeroFinder ctest1

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1'`, the conjugate
of `croot1`. -/
noncomputable def uniqueRootNear_croot1' :
    UniqueRootNear (aeval · myPoly) (toComplex croot1') 1e-57 :=
  uniqueRootNear_croot1.conj

end DegSix
