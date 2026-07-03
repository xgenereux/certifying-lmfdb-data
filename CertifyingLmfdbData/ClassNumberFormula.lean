import Mathlib

namespace NumberField

open Real NumberField InfinitePlace Units

theorem prod_lt_gap (K : Type*) [Field K] [NumberField K]
    (r₁ : ℕ) (hr₁ : nrRealPlaces K = r₁)
    (r₂ : ℕ) (hr₂ : nrComplexPlaces K = r₂)
    (D : ℤ) (hD : discr K = D)
    (w : ℕ) (hw : w ∣ torsionOrder K)
    (R : ℝ)
    (h : ℕ) (hh : classNumber K ∣ h)
    (z : ℝ) (hz : z ≤ dedekindZeta_residue K)
    (gap : ℝ) (hgap0 : 0 < gap) -- e.g., 1.99
    (key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h < gap * z * w * √|D|) :
    (torsionOrder K / w : ℕ) * (R / regulator K) * (h / classNumber K : ℕ) < gap := by
  have : 0 < w := Nat.pos_of_dvd_of_pos hw (torsionOrder_pos K)
  have : 0 < regulator K := regulator_pos K
  have : 0 < classNumber K := classNumber_pos K
  have : 0 < torsionOrder K := torsionOrder_pos K
  have : 0 < √|(D : ℝ)| := by simpa [hD] using NumberField.discr_ne_zero K
  replace key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h * torsionOrder K <
      gap * 2 ^ r₁ * (2 * π) ^ r₂ * w * regulator K * classNumber K := by
    apply lt_of_lt_of_le (mul_lt_mul_of_pos_right key (by positivity))
    grw [hz]
    simp [dedekindZeta_residue_def, hr₁, hr₂, hD, field]
  replace key : 2 ^ r₁ * (2 * π) ^ r₂ * (torsionOrder K * R * h) <
      2 ^ r₁ * (2 * π) ^ r₂ * (gap * (↑w * regulator K * classNumber K)) := by
    grind
  replace key : torsionOrder K * R * h < gap * (↑w * regulator K * classNumber K) := by
    rwa [mul_lt_mul_iff_right₀ (by positivity)] at key
  replace key : (torsionOrder K / w) * (R / regulator K) * (h / classNumber K) < gap := by
    rwa [div_mul_div_comm, div_mul_div_comm, div_lt_iff₀ (by positivity)]
  norm_cast at key

theorem classNumberFormulaPrototype {a : ℕ} {b : ℝ} {c : ℕ} {α : ℝ} {β : ℝ}
    (ha : a ≠ 0) (hb : 0 ≤ b) (hc : c ≠ 0)
    (h : a * b * c < 2 * α) (h' : ∃ m : ℕ, 1 ≤ m ∧ b ∈ Set.Icc (m • α) (m • β)) :
    a = 1 ∧ b ∈ Set.Icc α β ∧ c = 1 := by
  have hα : 0 < α := by
    grw [← hb, mul_zero, zero_mul] at h
    grind
  have hαβ : α ≤ b := by
    obtain ⟨m, hm, ⟨hb, -⟩⟩ := h'
    grw [← hb, ← hm, one_smul]
  replace ha : 1 ≤ a := ha.pos
  replace hc : 1 ≤ c := hc.pos
  replace ha : a = 1 := by
    contrapose! h
    replace ha : 2 ≤ a := lt_of_le_of_ne' ha h
    grw [hαβ, ← ha, ← hc, Nat.cast_one, Nat.cast_ofNat, mul_one]
  rw [ha, Nat.cast_one, one_mul] at h
  replace hc : c = 1 := by
    contrapose! h
    replace hc : 2 ≤ c := lt_of_le_of_ne' hc h
    grw [hαβ, ← hc, Nat.cast_ofNat, mul_comm]
  rw [hc, Nat.cast_one, mul_one] at h
  refine ⟨ha, ?_, hc⟩
  obtain ⟨m, hm, hm'⟩ := h'
  replace hm : m = 1 ∨ 2 ≤ m := by grind
  rcases hm with hm | hm
  · simpa [hm] using hm'
  · replace hm' := hm'.1
    grw [← hm] at hm'
    grind

theorem classNumberFormulaAux (K : Type*) [Field K] [NumberField K]
    (r₁ : ℕ) (hr₁ : nrRealPlaces K = r₁)
    (r₂ : ℕ) (hr₂ : nrComplexPlaces K = r₂)
    (D : ℤ) (hD : discr K = D)
    (w : ℕ) (hw : w ∣ torsionOrder K)
    (α : ℝ) (β : ℝ) (hα : 0 < α)
    (R : ℝ) (hR : ∃ m : ℕ, 1 ≤ m ∧ R ∈ Set.Icc (α * m • regulator K) (β * m • regulator K))
    (h : ℕ) (hh : classNumber K ∣ h) (hh0 : h ≠ 0)
    (z : ℝ) (hz : z ≤ dedekindZeta_residue K)
    (key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h < 2 * α * z * w * √|D|) :
    torsionOrder K = w ∧ regulator K ∈ Set.Icc (R / β) (R / α) ∧ classNumber K = h := by
  have : 0 < regulator K := regulator_pos K
  have : 0 < torsionOrder K := torsionOrder_pos K
  have h1 : torsionOrder K / w ≠ 0 := fun H ↦ by grind [Nat.eq_mul_of_div_eq_left hw H]
  have h2 : 0 ≤ R / regulator K := by
    obtain ⟨m, hm, ⟨hR, -⟩⟩ := hR
    grw [← hm, one_smul, ← hα, ← regulator_pos] at hR
    positivity
  have h3 : h / classNumber K ≠ 0 := fun H ↦ by grind [Nat.eq_mul_of_div_eq_left hh H]
  have key1 : α ≤ R / regulator K := by
    obtain ⟨m, hm, ⟨hR, -⟩⟩ := hR
    grw [← hR, ← hm]
    simp [field]
  replace hR : ∃ m : ℕ, 1 ≤ m ∧ R / regulator K ∈ Set.Icc (m • α) (m • β) := by
    obtain ⟨m, hm, hR⟩ := hR
    refine ⟨m, hm, ?_⟩
    apply hR.imp <;> simp [field] <;> grind
  have h4 := prod_lt_gap K r₁ hr₁ r₂ hr₂ D hD w hw R h hh z hz (2 * α) (by positivity) key
  have := classNumberFormulaPrototype h1 h2 h3 h4 hR
  obtain ⟨x, y, z⟩ := this
  refine ⟨(Nat.eq_of_dvd_of_div_eq_one hw x).symm, ?_, Nat.eq_of_dvd_of_div_eq_one hh z⟩
  apply y.symm.imp
  · intro h
    have : 0 ≤ β := by
      grw [← h]
      positivity
    simp only [field] at h
    grw [h]
    simpa [field] using div_self_le_one β
  · simp [field, mul_comm]

theorem classNumberFormula (K : Type*) [Field K] [NumberField K]
    (r₁ : ℕ) (hr₁ : nrRealPlaces K = r₁)
    (r₂ : ℕ) (hr₂ : nrComplexPlaces K = r₂)
    (D : ℤ) (hD : discr K = D)
    (w : ℕ) (hw : w ∣ torsionOrder K)
    (α : ℝ) (β : ℝ) (hα : 0 < α)
    (R : ℝ) (hR : ∃ m : ℕ, 1 ≤ m ∧ R ∈ Set.Icc (α * m • regulator K) (β * m • regulator K))
    (h : ℕ) (hh : classNumber K ∣ h) (hh0 : h ≠ 0)
    (z₀ : ℝ) (hz₀ : z₀ ≤ dedekindZeta_residue K)
    (key : 2 ^ r₁ * (2 * π) ^ r₂ * R * h < 2 * α * z₀ * w * √|D|)
    (ε_reg : ℝ) (hε_reg₁ : R / α - R < ε_reg) (hε_reg₂ : R - R / β < ε_reg)
    (z : ℝ) (ε_res : ℝ) (hε_res₁ : z - 2 ^ r₁ * (2 * π) ^ r₂ * (R / β) * h / (w * √|D|) < ε_res)
    (hε_res₂ : 2 ^ r₁ * (2 * π) ^ r₂ * (R / α) * h / (w * √|D|) - z < ε_res) :
    torsionOrder K = w ∧ (|regulator K - R| < ε_reg) ∧
      classNumber K = h ∧ (|dedekindZeta_residue K - z| < ε_res) := by
  obtain ⟨h₁, ⟨_, _⟩, h₃⟩ :=
    classNumberFormulaAux K r₁ hr₁ r₂ hr₂ D hD w hw α β hα R hR h hh hh0 z₀ hz₀ key
  have h₄ : dedekindZeta_residue K ∈ Set.Icc (2 ^ r₁ * (2 * π) ^ r₂ * (R / β) * h / (w * √|D|))
      (2 ^ r₁ * (2 * π) ^ r₂ * (R / α) * h / (w * √|D|)) := by
    rw [dedekindZeta_residue_def, hr₁, hr₂, h₃, h₁, hD]
    constructor <;> gcongr
  grind

end NumberField
