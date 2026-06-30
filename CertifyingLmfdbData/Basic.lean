import Mathlib

open Real NumberField InfinitePlace Units

theorem foo {a : ℕ} {b : ℝ} {c : ℕ} (ha : a ≠ 0) (hb : 1 ≤ b) (hc : c ≠ 0)
    (h : a * b * c < 2) : a = 1 ∧ b ∈ Set.Ico 1 2 ∧ c = 1 := by
  sorry

example (K : Type*) [Field K] [NumberField K]
    (r₁ : ℕ) (hr₁ : nrRealPlaces K = r₁)
    (r₂ : ℕ) (hr₂ : nrComplexPlaces K = r₂)
    (D : ℤ) (hD : discr K = D)
    (w : ℕ) (hw : w ∣ torsionOrder K)
    (R : ℝ) (hR : regulator K ≤ R)
    (h : ℕ) (hh : classNumber K ∣ h) (hh0 : h ≠ 0)
    (z : ℝ) (hz : z ≤ dedekindZeta_residue K)
    (key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h < 2 * z * w * √|D|) :
    torsionOrder K = w ∧ regulator K ∈ Set.Ioc (R / 2) R ∧ classNumber K = h := by
  have : 0 < w := Nat.pos_of_dvd_of_pos hw (torsionOrder_pos K)
  have : 0 < regulator K := regulator_pos K
  have : 0 < classNumber K := classNumber_pos K
  have : 0 < torsionOrder K := torsionOrder_pos K
  have : 0 < √|(D : ℝ)| := by simpa [hD] using NumberField.discr_ne_zero K
  replace key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h * torsionOrder K <
      2 * 2 ^ r₁ * (2 * π) ^ r₂ * w * regulator K * classNumber K := by
    apply lt_of_lt_of_le (mul_lt_mul_of_pos_right key (by positivity))
    grw [hz]
    simp [dedekindZeta_residue_def, hr₁, hr₂, hD, field]
  replace key : 2 ^ r₁ * (2 * π) ^ r₂ * (torsionOrder K * R * h) <
      2 ^ r₁ * (2 * π) ^ r₂ * (2 * (↑w * regulator K * classNumber K)) := by
    grind
  replace key : torsionOrder K * R * h < 2 * (↑w * regulator K * classNumber K) := by
    rwa [mul_lt_mul_iff_right₀ (by positivity)] at key
  replace key : (torsionOrder K / w) * (R / regulator K) * (h / classNumber K) < 2 := by
    rwa [div_mul_div_comm, div_mul_div_comm, div_lt_iff₀ (by positivity)]
  norm_cast at key
  refine .imp ?_ (.imp ?_ ?_) (foo ?_ ?_ ?_ key)
  · intro H
    simpa using Nat.eq_mul_of_div_eq_left hw H
  · simp [field]
    grind
  · intro H
    simpa using (Nat.eq_mul_of_div_eq_left hh H).symm
  · intro h
    grind [Nat.eq_mul_of_div_eq_left hw h]
  · simpa [field]
  · intro H
    grind [Nat.eq_mul_of_div_eq_left hh H]
