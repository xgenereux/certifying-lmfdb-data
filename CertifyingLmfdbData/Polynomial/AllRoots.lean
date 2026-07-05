import CertifyingLmfdbData.Polynomial.Tactic

/-!
# All roots of `X⁶ - 5X⁴ - 50X² + 125`, certified

Each of the six roots is certified by `unique_root_near` from just a decimal approximation of
the root and a decimal approximation of the inverse Jacobian of the zero finder there; the
complex conjugate root comes for free via `UniqueRootNear.conj`.
-/

noncomputable section

section Lemmas

open Polynomial NNReal

/-! ### Root ball → embedding-value ball, uniformly in the root

Unlike `embedding_value_ball` (Taylor coefficients at each approximation `v`), the bound here
only depends on the polynomial `U` and one radius `ρ` covering *all* roots, so a single numeric
evaluation per unit serves every embedding. -/

open Finset in
/-- `‖x^n - y^n‖ ≤ n·ρ^(n-1)·‖x - y‖` on the ball of radius `ρ`, via the factorization
`x^n - y^n = (∑ xⁱy^(n-1-i))·(x - y)`. -/
lemma norm_pow_sub_pow_le (x y : ℂ) {ρ : ℝ} (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * ρ ^ (n - 1) * ‖x - y‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range n, ‖x ^ i * y ^ (n - 1 - i)‖
      ≤ ∑ i ∈ range n, ρ ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hρ0 : 0 ≤ ρ := (norm_nonneg x).trans hx
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i)
            ≤ ρ ^ i * ρ ^ (n - 1 - i) :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hx i)
                (pow_le_pow_left₀ (norm_nonneg y) hy _) (by positivity) (pow_nonneg hρ0 i)
          _ = ρ ^ (n - 1) := by
              rw [← pow_add]
              congr 1
              have := Finset.mem_range.mp hi
              omega
    _ = n * ρ ^ (n - 1) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]

open Finset in
/-- Coefficient-wise Lipschitz constant for `U : ℚ[X]` on the closed ball of radius `ρ` in `ℂ`:
a computable finite sum, independent of the base point. -/
noncomputable def polyLipBound (U : Polynomial ℚ) (ρ : ℝ) : ℝ :=
  ∑ k ∈ range (U.natDegree + 1), |(U.coeff k : ℝ)| * k * ρ ^ (k - 1)

lemma polyLipBound_nonneg (U : Polynomial ℚ) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ polyLipBound U ρ :=
  Finset.sum_nonneg fun k _ => by positivity

open Finset in
/-- `U` is `polyLipBound U ρ`-Lipschitz on the ball of radius `ρ`. -/
lemma norm_aeval_sub_aeval_le_polyLipBound (U : Polynomial ℚ) {α v : ℂ} {ρ : ℝ}
    (hα : ‖α‖ ≤ ρ) (hv : ‖v‖ ≤ ρ) :
    ‖aeval α U - aeval v U‖ ≤ polyLipBound U ρ * ‖α - v‖ := by
  set Q := U.map (algebraMap ℚ ℂ) with hQ
  have ha : ∀ z : ℂ, aeval z U = Q.eval z := fun z => by rw [hQ, eval_map, aeval_def]
  have hdeg : Q.natDegree < U.natDegree + 1 := Nat.lt_succ_of_le (natDegree_map_le)
  rw [ha, ha, eval_eq_sum_range' hdeg, eval_eq_sum_range' hdeg, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  rw [polyLipBound, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, hQ, coeff_map]
  have hcoeff : ‖(algebraMap ℚ ℂ) (U.coeff k)‖ = |(U.coeff k : ℝ)| := by
    rw [show (algebraMap ℚ ℂ) (U.coeff k) = ((U.coeff k : ℝ) : ℂ) from by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  calc ‖(algebraMap ℚ ℂ) (U.coeff k)‖ * ‖α ^ k - v ^ k‖
      ≤ |(U.coeff k : ℝ)| * (k * ρ ^ (k - 1) * ‖α - v‖) := by
        rw [hcoeff]
        exact mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le α v hα hv k) (abs_nonneg _)
    _ = |(U.coeff k : ℝ)| * k * ρ ^ (k - 1) * ‖α - v‖ := by ring

/-- Push a `UniqueRootNear` certificate through a polynomial `U`: the value of `U` at the
certified root lies within `polyLipBound U ρ · √2·r` of the computable center `aeval v U`,
whenever the ball of radius `ρ` swallows the certified box. The `√2` converts the sup-norm
box of `near` into a disc. -/
lemma UniqueRootNear.aeval_near {f : Polynomial ℚ} {v : ℂ} {r ρ : ℝ} (h : UniqueRootNear f v r)
    (hρ : ‖v‖ + Real.sqrt 2 * r ≤ ρ) (U : Polynomial ℚ) :
    ‖aeval h.root U - aeval v U‖ ≤ polyLipBound U ρ * (Real.sqrt 2 * r) := by
  have hr0 : 0 ≤ r := le_trans (abs_nonneg _) ((le_max_left _ _).trans h.near)
  have hsr0 : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hr0
  have hρ0 : 0 ≤ ρ := le_trans (add_nonneg (norm_nonneg _) hsr0) hρ
  have hαv : ‖h.root - v‖ ≤ Real.sqrt 2 * r :=
    (Complex.norm_le_sqrt_two_mul_max _).trans (by gcongr; exact h.near)
  have hv' : ‖v‖ ≤ ρ := le_trans (le_add_of_nonneg_right hsr0) hρ
  have hα : ‖h.root‖ ≤ ρ := by
    calc ‖h.root‖ = ‖v + (h.root - v)‖ := by ring_nf
      _ ≤ ‖v‖ + ‖h.root - v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + Real.sqrt 2 * r := by gcongr
      _ ≤ ρ := hρ
  refine (norm_aeval_sub_aeval_le_polyLipBound U hα hv').trans ?_
  exact mul_le_mul_of_nonneg_left hαv (polyLipBound_nonneg U hρ0)

end Lemmas

namespace DegSix

open Polynomial Complex NNReal

def myPoly : Polynomial ℚ := (X^6 - 5*X^4 - 50 * X^2 + 125 : Polynomial ℤ).map (algebraMap ℤ ℚ)

theorem myPoly_eq : myPoly = X^6 - 5*X^4 - 50 * X^2 + 125 := by
  simp [myPoly]

/-! ### Approximate roots and inverse Jacobians -/

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

/-! ### The four real roots -/

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot1`. -/
noncomputable def uniqueRootNear_rroot1 :
    UniqueRootNear myPoly (toComplex rroot1) 1e-57 := by
  rw [myPoly_eq]
  unique_root_near rA1_mat

/-- The root approximated by `rroot1` is real. -/
lemma rroot1_im_zero : uniqueRootNear_rroot1.root.im = 0 :=
  uniqueRootNear_rroot1.im_eq_zero (by simp [rroot1])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot2`. -/
noncomputable def uniqueRootNear_rroot2 :
    UniqueRootNear myPoly (toComplex rroot2) 1e-57 := by
  rw [myPoly_eq]
  unique_root_near rA2_mat

/-- The root approximated by `rroot2` is real. -/
lemma rroot2_im_zero : uniqueRootNear_rroot2.root.im = 0 :=
  uniqueRootNear_rroot2.im_eq_zero (by simp [rroot2])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot3`. -/
noncomputable def uniqueRootNear_rroot3 :
    UniqueRootNear myPoly (toComplex rroot3) 1e-57 := by
  rw [myPoly_eq]
  unique_root_near rA3_mat

/-- The root approximated by `rroot3` is real. -/
lemma rroot3_im_zero : uniqueRootNear_rroot3.root.im = 0 :=
  uniqueRootNear_rroot3.im_eq_zero (by simp [rroot3])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot4`. -/
noncomputable def uniqueRootNear_rroot4 :
    UniqueRootNear myPoly (toComplex rroot4) 1e-57 := by
  rw [myPoly_eq]
  unique_root_near rA4_mat

/-- The root approximated by `rroot4` is real. -/
lemma rroot4_im_zero : uniqueRootNear_rroot4.root.im = 0 :=
  uniqueRootNear_rroot4.im_eq_zero (by simp [rroot4])

/-! ### The complex conjugate pair -/

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1`. -/
noncomputable def uniqueRootNear_croot1 :
    UniqueRootNear myPoly (toComplex croot1) 1e-57 := by
  rw [myPoly_eq]
  unique_root_near cA1_mat

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1'`, the conjugate
of `croot1`. -/
noncomputable def uniqueRootNear_croot1' :
    UniqueRootNear myPoly (toComplex croot1') 1e-57 :=
  uniqueRootNear_croot1.conj

lemma zero_lt_croot4_im : 0 < uniqueRootNear_croot1.root.im := by
  have := le_of_max_le_right uniqueRootNear_croot1.near
  simp [croot1, abs_le] at this
  linarith

open Polynomial

def myPoly' : Polynomial ℚ := X^6 + 7 * X^5 + X^4 - 1

def A_mat : Matrix (Fin 2) (Fin 2) ℝ := !![ 0.130923022789476, 0; 0, 0.130923022789476 ]

example : UniqueRootNear myPoly' (toComplex ![0.641564061943673, 0]) 1e-10 := by
  unique_root_near A_mat

example : UniqueRootNear (X^6 - 1 : Polynomial ℚ) (toComplex ![1, 0]) 1e-30 := by
  unique_root_near !![1/6, 0; 0, 1/6]

/-- An ill-conditioned certificate: `(X - 1)(X - (1 + 10⁻³⁰))` has two roots `10⁻³⁰` apart, so
the inverse Jacobian at the root `1` is `≈ -10³⁰` and the Lipschitz certificate is
`z₂ ≈ 6·10³⁰`. The truncated derivative point `w` must then carry ~35 decimal places for the
transported error `z₂·ε` to fit in the `z₁ = 1/2` budget — this exercises the adaptive
truncation width (a fixed 20-digit `w` fails here with `z₂·ε ≈ 6·10¹⁰`). -/
example : UniqueRootNear
    (X^2 - C (2000000000000000000000000000001 / 1000000000000000000000000000000) * X
      + C (1000000000000000000000000000001 / 1000000000000000000000000000000) : Polynomial ℚ)
    (toComplex ![1, 0]) 1e-40 := by
  unique_root_near !![-1e30, 0; 0, -1e30]

/-! ### Fundamental units (LMFDB 6.4.19208000.1)

The unit group has rank 4 (signature `(4,1)`); the fundamental units from LMFDB are
`u₁ = a⁴/25 - 2`, `u₂ = a⁴/25 - 1`, `u₃ = a⁵/25 - 2a⁴/25 - 2a + 3`,
`u₄ = a⁵/25 - a²/5 - 2a - 2`. -/

def fundU1 : Polynomial ℚ := C (1/25) * X^4 - C 2
def fundU2 : Polynomial ℚ := C (1/25) * X^4 - C 1
def fundU3 : Polynomial ℚ := C (1/25) * X^5 - C (2/25) * X^4 - C 2 * X + C 3
def fundU4 : Polynomial ℚ := C (1/25) * X^5 - C (1/5) * X^2 - C 2 * X - C 2

def fundUnits : Fin 4 → Polynomial ℚ := ![fundU1, fundU2, fundU3, fundU4]

/-! All six roots of `myPoly` have modulus `< 3.01`, so the ball of radius `ρ = 3.1` swallows
every certified root ball; one Lipschitz constant per unit then serves all embeddings. -/

lemma polyLipBound_fundU1 : polyLipBound fundU1 3.1 ≤ 4.77 := by
  have hdeg : fundU1.natDegree = 4 := by unfold fundU1; compute_degree!
  rw [polyLipBound, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fundU1, coeff_sub, coeff_C_mul,
    coeff_X_pow, coeff_C]
  norm_num

lemma polyLipBound_fundU2 : polyLipBound fundU2 3.1 ≤ 4.77 := by
  have hdeg : fundU2.natDegree = 4 := by unfold fundU2; compute_degree!
  rw [polyLipBound, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fundU2, coeff_sub, coeff_C_mul,
    coeff_X_pow, coeff_C]
  norm_num

lemma polyLipBound_fundU3 : polyLipBound fundU3 3.1 ≤ 30.01 := by
  have hdeg : fundU3.natDegree = 5 := by unfold fundU3; compute_degree!
  rw [polyLipBound, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fundU3, coeff_add, coeff_sub,
    coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

lemma polyLipBound_fundU4 : polyLipBound fundU4 3.1 ≤ 21.72 := by
  have hdeg : fundU4.natDegree = 5 := by unfold fundU4; compute_degree!
  rw [polyLipBound, hdeg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, fundU4, coeff_sub, coeff_C_mul,
    coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-! ### Certified balls for every embedding value `σᵢ(uⱼ)`

One approximation per embedding (the fifth is the complex place; its conjugate carries the same
data), and one radius `δⱼ = polyLipBound uⱼ 3.1 · √2 · 1e-57` per unit — the same `δⱼ` works at
every embedding, and `c = 1e-55` works everywhere. -/

def approxRoots : Fin 5 → (Fin 2 → ℝ) := ![rroot1, rroot2, rroot3, rroot4, croot1]

/-- Per-unit radii `δⱼ` for the embedding-value balls. -/
def unitDelta : Fin 4 → ℝ := ![7e-57, 7e-57, 4.3e-56, 3.1e-56]

lemma norm_toComplex_approxRoots (i : Fin 5) : ‖toComplex (approxRoots i)‖ ≤ 3.01 := by
  have h : ‖toComplex (approxRoots i)‖ ^ 2 ≤ 3.01 ^ 2 := by
    rw [norm_toComplex_sq]
    fin_cases i <;>
      simp [approxRoots, rroot1, rroot2, rroot3, rroot4, croot1] <;> norm_num
  nlinarith [norm_nonneg (toComplex (approxRoots i)), h]

lemma polyLipBound_mul_le (j : Fin 4) :
    polyLipBound (fundUnits j) 3.1 * (Real.sqrt 2 * 1e-57) ≤ unitDelta j := by
  fin_cases j
  · change polyLipBound fundU1 3.1 * (Real.sqrt 2 * 1e-57) ≤ (7e-57 : ℝ)
    grw [polyLipBound_fundU1, Real.sqrt_two_lt_d2]; norm_num
  · change polyLipBound fundU2 3.1 * (Real.sqrt 2 * 1e-57) ≤ (7e-57 : ℝ)
    grw [polyLipBound_fundU2, Real.sqrt_two_lt_d2]; norm_num
  · change polyLipBound fundU3 3.1 * (Real.sqrt 2 * 1e-57) ≤ (4.3e-56 : ℝ)
    grw [polyLipBound_fundU3, Real.sqrt_two_lt_d2]; norm_num
  · change polyLipBound fundU4 3.1 * (Real.sqrt 2 * 1e-57) ≤ (3.1e-56 : ℝ)
    grw [polyLipBound_fundU4, Real.sqrt_two_lt_d2]; norm_num

/-- The five `UniqueRootNear` certificates, uniformly indexed by embedding. -/
noncomputable def uniqueRoots :
    (i : Fin 5) → UniqueRootNear myPoly (toComplex (approxRoots i)) 1e-57
  | 0 => uniqueRootNear_rroot1
  | 1 => uniqueRootNear_rroot2
  | 2 => uniqueRootNear_rroot3
  | 3 => uniqueRootNear_rroot4
  | 4 => uniqueRootNear_croot1

/-- **Certified embedding values.** For each embedding `i` and fundamental unit `uⱼ`, the
embedding value `σᵢ(uⱼ) = aeval (uniqueRoots i).root uⱼ` lies within `unitDelta j` of the
computable center `aeval (toComplex (approxRoots i)) uⱼ`. -/
theorem sigma_bounds (i : Fin 5) (j : Fin 4) :
    ‖aeval (uniqueRoots i).root (fundUnits j)
      - aeval (toComplex (approxRoots i)) (fundUnits j)‖ ≤ unitDelta j := by
  have hρ : ‖toComplex (approxRoots i)‖ + Real.sqrt 2 * 1e-57 ≤ 3.1 := by
    grw [norm_toComplex_approxRoots i, Real.sqrt_two_lt_d2]; norm_num
  exact ((uniqueRoots i).aeval_near hρ _).trans (polyLipBound_mul_le j)

lemma unitDelta_le (j : Fin 4) : unitDelta j ≤ 1e-55 := by
  fin_cases j <;> norm_num [unitDelta]

/-- Uniform version: a single radius `c = 1e-55` certifies every `σᵢ(uⱼ)` simultaneously. -/
theorem sigma_bounds_uniform (i : Fin 5) (j : Fin 4) :
    ‖aeval (uniqueRoots i).root (fundUnits j)
      - aeval (toComplex (approxRoots i)) (fundUnits j)‖ ≤ 1e-55 :=
  (sigma_bounds i j).trans (unitDelta_le j)

end DegSix

end
