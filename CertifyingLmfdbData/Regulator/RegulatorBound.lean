import Mathlib.NumberTheory.NumberField.Units.Regulator

variable {K : Type*} [Field K] [NumberField K]

open NumberField NumberField.Units

open Classical in
lemma regulator_le_regOfFamily
    (u : Fin (rank K) → (RingOfIntegers K)ˣ) (hu : regOfFamily u ≠ 0) :
    regulator K ≤ regOfFamily u := by
  have := regulator_pos K
  have := NumberField.Units.regOfFamily_div_regulator u
  field_simp at this
  rw [this]
  have hindex_one :
      (1 : ℝ) ≤ ((Subgroup.closure (Set.range u) ⊔ torsion K).index : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun _ ↦ by simp_all))
  nlinarith
