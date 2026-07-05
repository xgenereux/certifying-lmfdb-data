import CertifyingLmfdbData.Polynomial.Example
import CertifyingLmfdbData.Polynomial.Certify

/-!
# Certified unique roots of rational polynomials

`UniqueRootNear f v r` packages a root of `f` together with proofs that it is the unique root
within (sup-norm) distance `r` of the approximation `v`. This file provides the interface for
producing such certificates from Newton–Kantorovich data:

* `UniqueRootNear.ofZeroFinder` translates the `∃!` conclusion of `newton_kantorovich_fd`
  applied to the zero finder of `p` on `ℝ²` into a `UniqueRootNear` witness;
* `UniqueRootNear.of_certificates` combines this with `existsUnique_root_of_certificates`, so
  that all remaining hypotheses are rational-arithmetic inequalities;
* `UniqueRootNear.conj` and `UniqueRootNear.im_eq_zero` transport certificates along complex
  conjugation.
-/

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
structure UniqueRootNear (f : Polynomial ℚ) (v : ℂ) (r : ℝ) where
  /-- The root of `f` certified to be unique near `v`. -/
  root : ℂ
  isRoot : f.aeval root = 0
  near : max |(root - v).re| |(root - v).im| ≤ r
  unique : ∀ ⦃z : ℂ⦄, f.aeval z = 0 → max |(z - v).re| |(z - v).im| ≤ r → z = root

namespace UniqueRootNear

variable {f : Polynomial ℚ} {v v' : ℂ} {r r' : ℝ}

lemma re_near (h : UniqueRootNear f v r) : |(h.root - v).re| ≤ r :=
  (le_max_left _ _).trans h.near

lemma im_near (h : UniqueRootNear f v r) : |(h.root - v).im| ≤ r :=
  (le_max_right _ _).trans h.near

lemma existsUnique (h : UniqueRootNear f v r) :
    ∃! z : ℂ, f.aeval z = 0 ∧ max |(z - v).re| |(z - v).im| ≤ r :=
  ⟨h.root, ⟨h.isRoot, h.near⟩, fun _ hz ↦ h.unique hz.1 hz.2⟩

lemma distinct (h₁ : UniqueRootNear f v r) (h₂ : UniqueRootNear f v' r')
    (h : r + r' < max |v.re - v'.re| |v.im - v'.im|) : h₁.root ≠ h₂.root := by
  have := h₁.near
  have := h₂.near
  grind [Complex.sub_re, Complex.sub_im]

/-- Conjugating a certified unique root: since conjugation commutes with evaluation of a
rational polynomial and preserves sup-norm distances, a unique root near `v` gives a unique
root near `conj v`, namely the conjugate of the original root. -/
noncomputable def conj {p : Polynomial ℚ} (h : UniqueRootNear p v r) :
    UniqueRootNear p (starRingEnd ℂ v) r where
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

@[simp] lemma conj_root {p : Polynomial ℚ} (h : UniqueRootNear p v r) :
    h.conj.root = starRingEnd ℂ h.root := rfl

/-- The unique root near a point `v` with zero imaginary part is genuinely real: its complex
conjugate is again a root the same distance from `v`, so by uniqueness the root equals its own
conjugate. -/
lemma im_eq_zero {p : Polynomial ℚ} (h : UniqueRootNear p v r) (hv : v.im = 0) :
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
    UniqueRootNear p (toComplex v) r where
  root := toComplex h.choose
  isRoot := (polyToZeroFinder_root_near_iff.mp h.choose_spec.1).1
  near := (polyToZeroFinder_root_near_iff.mp h.choose_spec.1).2
  unique z hz hd := by
    have hx : polyToZeroFinder p (toComplex.symm z) = 0 ∧ ‖toComplex.symm z - v‖₊ ≤ r := by
      rw [polyToZeroFinder_root_near_iff]
      exact ⟨by simpa using hz, by simpa using hd⟩
    calc z = toComplex (toComplex.symm z) := by simp
      _ = toComplex h.choose := by rw [h.choose_spec.2 _ hx]

lemma Real.sqrt_two_lt_d10 : √2 < 1.4142135624 := by
  rw [Real.sqrt_lt] <;> norm_num

lemma Real.sqrt_two_lt_d2 : √2 < 1.42 := by
  rw [Real.sqrt_lt] <;> norm_num

/-- Package a full numerical certificate `(v, M, y, z₁, z₂, R, r)` into a `UniqueRootNear`
witness, via `existsUnique_root_of_certificates`. All hypotheses are rational-arithmetic
inequalities (after evaluating `aeval` at `toComplex v` and expanding the finite sums), so
each can be closed by `norm_num` with a suitable simp set. -/
noncomputable def UniqueRootNear.of_certificates (p : Polynomial ℚ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) {y z₁ z₂ R r : ℝ≥0} {d : ℕ} {a B : ℝ}
    (hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (hy1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y)
    (hz1 : ∀ i, ∑ j, |(1 - M * derivMatrix p v) i j| ≤ z₁)
    (hdeg : p.derivative.natDegree ≤ d)
    (ha : ∀ i, ∑ j, |M i j| ≤ a)
    (hB : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) (hB0 : 0 ≤ B)
    (hnum : 3 * a *
        (∑ k ∈ Finset.range d,
          (∑ n ∈ Finset.range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (3 / 2 * R) ^ k) ≤ z₂)
    (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    UniqueRootNear p (toComplex v) r := by
  refine .ofZeroFinder <| existsUnique_root_of_certificates p M v hy0 hy1 hz1 hdeg ha hB hB0
    (show √2 ≤ 1.5 from Real.sqrt_two_lt_d2.le.trans (by norm_num)) ?_ hrR hyr hzr
  norm_num
  exact hnum

/-- Variant of `UniqueRootNear.of_certificates` whose approximate-inverse bound is certified at
a low-precision proxy `w` for `v` (with `|v i - w i| ≤ ε ≤ R`): the row-sum bound `z₁'` at `w`
and the Lipschitz certificate `z₂` combine into `z₁' + z₂ * ε ≤ z₁`. This keeps the number of
digits needed for the `hz1w` check bounded, however precise the approximation `v` is. -/
noncomputable def UniqueRootNear.of_certificates_approx (p : Polynomial ℚ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (v w : Fin 2 → ℝ) {y z₁ z₁' z₂ ε R r : ℝ≥0} {d : ℕ}
    {a B : ℝ}
    (hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y)
    (hy1 : |M 1 0 * (aeval (toComplex v) p).re + M 1 1 * (aeval (toComplex v) p).im| ≤ y)
    (hz1w : ∀ i, ∑ j, |(1 - M * derivMatrix p w) i j| ≤ z₁')
    (hw0 : |v 0 - w 0| ≤ ε) (hw1 : |v 1 - w 1| ≤ ε) (hεR : ε ≤ R)
    (hz1 : z₁' + z₂ * ε ≤ z₁)
    (hdeg : p.derivative.natDegree ≤ d)
    (ha : ∀ i, ∑ j, |M i j| ≤ a)
    (hB : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2) (hB0 : 0 ≤ B)
    (hnum : 3 * a *
        (∑ k ∈ Finset.range d,
          (∑ n ∈ Finset.range (d - k), ((n + k + 1).choose (k + 1) : ℝ) *
            |((p.derivative.coeff (n + k + 1) : ℚ) : ℝ)| * B ^ n) * (3 / 2 * R) ^ k) ≤ z₂)
    (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    UniqueRootNear p (toComplex v) r := by
  refine .ofZeroFinder <| existsUnique_root_of_certificates_approx p M v w hy0 hy1 hz1w
    hw0 hw1 hεR hz1 hdeg ha hB hB0
    (show √2 ≤ 1.5 from Real.sqrt_two_lt_d2.le.trans (by norm_num)) ?_ hrR hyr hzr
  norm_num
  exact hnum

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

end Lemmas

end
