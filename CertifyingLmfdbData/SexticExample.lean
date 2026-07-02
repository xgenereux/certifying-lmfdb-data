import CertifyingLmfdbData.ClassNumberFormula
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal

namespace SexticExample

noncomputable section

open Polynomial Module NumberField InfinitePlace Units

-- Let `f = X^6 - 5*X^4 - 50 * X^2 + 125`
def f : Polynomial ℚ := X^6 - 5*X^4 - 50 * X^2 + 125

-- The polynomial `f` is irreducible
instance : Fact (Irreducible f) := by
  sorry

-- Let `K = ℚ[x]/f(x)` be the number field given by adjoining on root of `f`
noncomputable def K : Type := AdjoinRoot f
deriving Field, NumberField

-- The number field `K` has degree `6`
theorem finrank_eq : finrank ℚ K = 6 := by
  sorry

-- The number field `K` has `4` real places
theorem nrRealPlaces_eq : nrRealPlaces K = 4 := by
  sorry

-- The number field `K` has `1` complex place
theorem nrComplexPlaces_eq : nrComplexPlaces K = 1 := by
  sorry

-- The number field `K` has discriminant `19208000`
theorem discr_eq : discr K = 19208000 := by
  sorry

-- We only need a lower bound on the number of roots of unity
theorem torsionOrder_aux : 2 ∣ torsionOrder K := by
  sorry

-- We only need an upper bound on the class number
theorem classNumber_aux : classNumber K ∣ 2 := by
  sorry

-- We will certify that the regulator of `K` is roughly `15.9596951835...`
abbrev reg : ℝ := 15.9596951835

-- The error on our computation of the regulator of `K`
abbrev α : ℝ := 0.9
abbrev β : ℝ := 1.1

-- We only need an upper bound on the regulator
theorem regulator_aux : ∃ m : ℕ, 1 ≤ m ∧
    reg ∈ Set.Icc (α * m • regulator K) (β * m • regulator K) := by
  sorry

-- We will certify that the residue of `K` is roughly `0.366086210051`
abbrev res : ℝ := 0.366086210051

-- But we only need a weak lower bound on the residue
abbrev res_bound : ℝ := 0.3
theorem dedekindResidue_ge : res_bound ≤ dedekindZeta_residue K := by
  sorry

-- The class number formula certifies the torsion order, the regulator, and the class number
theorem classNumberFormula :
    torsionOrder K = 2 ∧ regulator K ∈ Set.Icc (reg / β) (reg / α) ∧ classNumber K = 2 := by
  apply NumberField.classNumberFormula K
    4 nrRealPlaces_eq
    1 nrComplexPlaces_eq
    19208000 discr_eq
    2 torsionOrder_aux
    α β (by positivity)
    reg regulator_aux
    2 classNumber_aux (by positivity)
    res_bound dedekindResidue_ge
  norm_cast
  push_cast
  dyadic_interval [approx := 10]

-- The number field `K` has exactly two roots of unity
theorem torsionOrder_eq : torsionOrder K = 2 := by
  exact classNumberFormula.1

-- The number field `K` has class number `2`
theorem classNumber_eq : classNumber K = 2 := by
  exact classNumberFormula.2.2

-- todo: write this as `|regulator K - reg| < x`
theorem regulator_mem : regulator K ∈ Set.Icc (reg / β) (reg / α) := by
  exact classNumberFormula.2.1

end

end SexticExample
