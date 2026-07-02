import CertifyingLmfdbData.Polynomial.Example

/-!
# General lemmas for certifying roots numerically

This file reduces each hypothesis of `newton_kantorovich_fd` (as applied to
`polyToZeroFinder p`) to rational-arithmetic inequalities that `norm_num` can close, given a
numerical certificate `(v, M, y, z₁, z₂, R, r)`:

* `hy` (residual bound): `nnnorm_mulVecCLM_polyToZeroFinder_le` — two absolute-value
  inequalities on the components of `M * p(v)`.
* `hz₁` (approximate-inverse bound): `nnnorm_one_sub_mulVecCLM_comp_polyToZeroFinderDeriv_le`
  — row-sum bounds on the explicit 2×2 matrix `1 - M * derivMatrix p v`.
* `hz₂` (Lipschitz bound): `polyToZeroFinderDeriv_lipschitzOn_of_bounds` — a single inequality
  whose left-hand side is a binomial-weighted sum of the absolute coefficients of
  `p.derivative`, replacing the per-root `taylor`/`polynomial_nf` computations.
-/

noncomputable section

open Polynomial Complex NNReal Finset

/-! ### Continuous linear maps from matrices, and sup-norm bounds -/

/-- The continuous linear map on `n → ℝ` (with the sup norm) given by a matrix. -/
def mulVecCLM {n : Type*} [Fintype n] (M : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap M.mulVecLin

@[simp] lemma mulVecCLM_apply {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    mulVecCLM M x = M.mulVec x := rfl

lemma mulVecCLM_comp {n : Type*} [Fintype n] (M N : Matrix n n ℝ) :
    (mulVecCLM M).comp (mulVecCLM N) = mulVecCLM (M * N) := by
  ext x : 1
  simp [Matrix.mulVec_mulVec]

lemma one_sub_mulVecCLM {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    1 - mulVecCLM M = mulVecCLM (1 - M) := by
  ext x : 1
  simp [Matrix.sub_mulVec]

/-- Row-sum bound for the (sup-norm) operator norm of a matrix, in `ℝ≥0` form. -/
lemma nnnorm_mulVecCLM_le {n : Type*} [Fintype n] (M : Matrix n n ℝ) {C : ℝ≥0}
    (hrow : ∀ i, ∑ j, |M i j| ≤ C) : ‖mulVecCLM M‖₊ ≤ C := by
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact opNorm_mulVecLin_le M C.coe_nonneg hrow

/-- Bound the sup-norm of a vector in `ℝ²` by bounding both components. -/
lemma nnnorm_fin_two_le {x : Fin 2 → ℝ} {C : ℝ≥0} (h0 : |x 0| ≤ C) (h1 : |x 1| ≤ C) :
    ‖x‖₊ ≤ C := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonneg C.coe_nonneg]
  intro i
  fin_cases i <;> assumption

/-- Bound `‖toComplex v‖` via the rational quantity `v 0 ^ 2 + v 1 ^ 2`. -/
lemma norm_toComplex_le_of_sq {v : Fin 2 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) : ‖toComplex v‖ ≤ B := by
  have hsq := norm_toComplex_sq v
  nlinarith [norm_nonneg (toComplex v)]

/-! ### The residual bound `hy` -/

/-- Reduce `hy` of `newton_kantorovich_fd` to two absolute-value inequalities on the
components of `M * p(v)`, which are rational once `aeval` is evaluated. -/
lemma nnnorm_mulVecCLM_polyToZeroFinder_le (p : ℚ[X]) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → ℝ) {y : ℝ≥0}
    (h0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (h1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y) :
    ‖mulVecCLM M (polyToZeroFinder p v)‖₊ ≤ y := by
  refine nnnorm_fin_two_le ?_ ?_
  · simpa [polyToZeroFinder, Matrix.mulVec, dotProduct, Fin.sum_univ_two, -toComplex_apply]
      using h0
  · simpa [polyToZeroFinder, Matrix.mulVec, dotProduct, Fin.sum_univ_two, -toComplex_apply]
      using h1

/-! ### The approximate-inverse bound `hz₁` -/

/-- The derivative of the zero finder at `v`, as an explicit 2×2 matrix: multiplication by
`p'(v)` on `ℂ ≃ ℝ²`. -/
def derivMatrix (p : ℚ[X]) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(aeval (toComplex v) p.derivative).re, -(aeval (toComplex v) p.derivative).im;
     (aeval (toComplex v) p.derivative).im,  (aeval (toComplex v) p.derivative).re]

lemma polyToZeroFinderDeriv_eq_mulVecCLM (p : ℚ[X]) (v : Fin 2 → ℝ) :
    polyToZeroFinderDeriv p v = mulVecCLM (derivMatrix p v) := by
  ext x : 1
  funext i
  fin_cases i <;>
    simp [polyToZeroFinderDeriv, derivMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      toComplex_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

/-- Reduce `hz₁` of `newton_kantorovich_fd` to row-sum bounds on the explicit matrix
`1 - M * derivMatrix p v`, which are rational once `aeval` is evaluated. -/
lemma nnnorm_one_sub_mulVecCLM_comp_polyToZeroFinderDeriv_le (p : ℚ[X])
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) {z₁ : ℝ≥0}
    (h : ∀ i, ∑ j, |(1 - M * derivMatrix p v) i j| ≤ z₁) :
    ‖1 - (mulVecCLM M).comp (polyToZeroFinderDeriv p v)‖₊ ≤ z₁ := by
  rw [polyToZeroFinderDeriv_eq_mulVecCLM, mulVecCLM_comp, one_sub_mulVecCLM]
  exact nnnorm_mulVecCLM_le _ h

/-! ### The Lipschitz bound `hz₂` -/

/-- Bound the norms of Taylor coefficients of a complex polynomial by binomial-weighted sums
of the norms of its coefficients: `(taylor c Q).coeff k = Q^(k)(c)/k!`, and expanding the
Hasse derivative gives `∑ n, (n+k).choose k * Q.coeff (n+k) * c^n`. -/
lemma norm_taylor_coeff_le (Q : ℂ[X]) (c : ℂ) {B : ℝ} (hc : ‖c‖ ≤ B) {d k : ℕ}
    (hd : Q.natDegree ≤ d) (hk : k ≤ d) :
    ‖(taylor c Q).coeff k‖ ≤
      ∑ n ∈ range (d + 1 - k), ((n + k).choose k : ℝ) * ‖Q.coeff (n + k)‖ * B ^ n := by
  have hB : 0 ≤ B := (norm_nonneg c).trans hc
  rw [taylor_coeff, eval_eq_sum_range' (n := d + 1 - k)
    (((natDegree_hasseDeriv_le Q k).trans (Nat.sub_le_sub_right hd k)).trans_lt
      (by omega))]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow, norm_natCast]
  gcongr

/-- Reduce `hz₂` of `newton_kantorovich_fd` to a single inequality between rational data: row
sums of `M`, a bound `B` on `‖v‖` (via `v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2`), a rational upper bound
`s` for `√2`, and a binomial-weighted sum of absolute coefficients of `p.derivative`. -/
lemma polyToZeroFinderDeriv_lipschitzOn_of_bounds (p : ℚ[X]) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → ℝ) (R z : ℝ≥0) {d : ℕ} {a B s : ℝ}
    (hdeg : p.derivative.natDegree ≤ d)
    (ha : ∀ i, ∑ j, |M i j| ≤ a)
    (hB : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) (hB0 : 0 ≤ B)
    (hs : Real.sqrt 2 ≤ s)
    (hnum : 2 * s * a *
        (∑ k ∈ range d,
          (∑ n ∈ range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (s * R) ^ k) ≤ z) :
    ∀ x ∈ Metric.closedEBall v (R : ENNReal),
      ‖(mulVecCLM M).comp (polyToZeroFinderDeriv p x - polyToZeroFinderDeriv p v)‖₊ ≤
        z * ‖x - v‖₊ := by
  set Q := p.derivative.map (algebraMap ℚ ℂ) with hQdef
  have hs0 : 0 ≤ s := (Real.sqrt_nonneg 2).trans hs
  have ha0 : 0 ≤ a := (Finset.sum_nonneg fun j _ => abs_nonneg _).trans (ha 0)
  have hAnorm : ‖mulVecCLM M‖ ≤ a := opNorm_mulVecLin_le M ha0 ha
  have hcB : ‖toComplex v‖ ≤ B := norm_toComplex_le_of_sq hB0 hB
  have hQdeg : Q.natDegree ≤ d := (natDegree_map_le).trans hdeg
  have hQcoeff : ∀ j, ‖Q.coeff j‖ = |((p.derivative.coeff j : ℚ) : ℝ)| := fun j => by
    rw [hQdef, coeff_map, eq_ratCast, Complex.norm_ratCast]
  have hsum : ∑ k ∈ range Q.natDegree,
      ‖(taylor (toComplex v) Q).coeff (k + 1)‖ * (Real.sqrt 2 * R) ^ k ≤
        ∑ k ∈ range d,
          (∑ n ∈ range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (s * R) ^ k := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hQdeg) fun k _ _ => by positivity).trans
      (Finset.sum_le_sum fun k hk => ?_)
    have hk' : k + 1 ≤ d := Finset.mem_range.mp hk
    have htay := norm_taylor_coeff_le Q (toComplex v) hcB hQdeg hk'
    simp only [hQcoeff] at htay
    rw [show d + 1 - (k + 1) = d - k from by omega] at htay
    have hb0 : 0 ≤ ∑ n ∈ range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
        |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n :=
      Finset.sum_nonneg fun n _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) (pow_nonneg hB0 n)
    have hpow : (Real.sqrt 2 * (R : ℝ)) ^ k ≤ (s * R) ^ k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hs R.coe_nonneg) k
    exact mul_le_mul htay hpow (by positivity) hb0
  have h1 : 2 * Real.sqrt 2 * ‖mulVecCLM M‖ ≤ 2 * s * a :=
    mul_le_mul (by linarith) hAnorm (norm_nonneg _) (by linarith)
  refine polyToZeroFinderDeriv_lipschitzOn p (mulVecCLM M) v R z ?_
  rw [← hQdef]
  refine le_trans (mul_le_mul h1 hsum ?_ ?_) hnum
  · exact Finset.sum_nonneg fun k _ => by positivity
  · exact mul_nonneg (by linarith) ha0

/-! ### Assembling the Newton–Kantorovich conclusion -/

/-- Package a full numerical certificate `(v, M, y, z₁, z₂, R, r)` into the unique-root
conclusion of `newton_kantorovich_fd` for `polyToZeroFinder p`. All hypotheses are
rational-arithmetic inequalities (after evaluating `aeval` at `toComplex v` and expanding the
finite sums), so each can be closed by `norm_num` with a suitable simp set. The result is
turned into a `UniqueRootNear` by `UniqueRootNear.ofZeroFinder`. -/
lemma existsUnique_root_of_certificates (p : ℚ[X]) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → ℝ) {y z₁ z₂ R r : ℝ≥0} {d : ℕ} {a B s : ℝ}
    (hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (hy1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y)
    (hz1 : ∀ i, ∑ j, |(1 - M * derivMatrix p v) i j| ≤ z₁)
    (hdeg : p.derivative.natDegree ≤ d)
    (ha : ∀ i, ∑ j, |M i j| ≤ a)
    (hB : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) (hB0 : 0 ≤ B)
    (hs : Real.sqrt 2 ≤ s)
    (hnum : 2 * s * a *
        (∑ k ∈ range d,
          (∑ n ∈ range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (s * R) ^ k) ≤ z₂)
    (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    ∃! x, polyToZeroFinder p x = 0 ∧ ‖x - v‖₊ ≤ r :=
  newton_kantorovich_fd
    (by simp)
    (fun x => hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (A := mulVecCLM M)
    (R := (R : ENNReal))
    (nnnorm_mulVecCLM_polyToZeroFinder_le p M v hy0 hy1)
    (nnnorm_one_sub_mulVecCLM_comp_polyToZeroFinderDeriv_le p M v hz1)
    (polyToZeroFinderDeriv_lipschitzOn_of_bounds p M v R z₂ hdeg ha hB hB0 hs hnum)
    (by exact_mod_cast hrR)
    hyr hzr

end
