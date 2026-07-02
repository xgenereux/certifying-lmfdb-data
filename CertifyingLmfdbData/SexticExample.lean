import CertifyingLmfdbData.ClassNumberFormula
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal

noncomputable section

open Polynomial Module NumberField InfinitePlace Units

def f : Polynomial ℚ := X^6 - 5*X^4 - 50 * X^2 + 125

instance : Fact (Irreducible f) := by
  sorry

noncomputable def K : Type := AdjoinRoot f
deriving Field, NumberField

theorem finrank_eq : finrank ℚ K = 6 := by
  sorry

theorem nrRealPlaces_eq : nrRealPlaces K = 4 := by
  sorry

theorem nrComplexPlaces_eq : nrComplexPlaces K = 1 := by
  sorry

theorem discr_eq : discr K = 19208000 := by
  sorry

theorem torsionOrder_aux : 2 ∣ torsionOrder K := by
  sorry

theorem classNumber_aux : classNumber K ∣ 2 := by
  sorry

-- todo: tighten these bounds
abbrev α : ℝ := 1.9
abbrev β : ℝ := 1.1
abbrev reg : ℝ := 15.9596951835
abbrev res : ℝ := 0.366086210051

theorem regulator_aux : ∃ m : ℕ, 1 ≤ m ∧
    reg ∈ Set.Icc (α * m • regulator K) (β * m • regulator K) := by
  sorry

-- todo: add some flex here
theorem dedekindResidue_ge : res ≤ dedekindZeta_residue K := by
  sorry

theorem classNumberFormulaAux' :
    torsionOrder K = 2 ∧ regulator K ∈ Set.Icc (reg / β) (reg / α) ∧ classNumber K = 2 := by
  apply classNumberFormula K
    4 nrRealPlaces_eq
    1 nrComplexPlaces_eq
    19208000 discr_eq
    2 torsionOrder_aux
    α β (by positivity)
    reg regulator_aux
    2 classNumber_aux (by positivity)
    res dedekindResidue_ge
  rw [α, res, reg]
  simp
  dyadic_interval [approx := 4]

end
