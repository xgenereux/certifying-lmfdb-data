import CertifyingLmfdbData.ClassNumberFormula
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal
import CertifyingLmfdbData.Regulator.RegulatorBound

namespace SexticExample

noncomputable section

open Polynomial Module NumberField InfinitePlace Units

-- Let `f = X^6 - 5*X^4 - 50 * X^2 + 125`
def f₀ : Polynomial ℤ := X^6 - 5*X^4 - 50 * X^2 + 125
def f : Polynomial ℚ := f₀.map (algebraMap ℤ ℚ)

-- The polynomial `f` is irreducible
instance : Fact (Irreducible f) := by
  sorry

-- Let `K = ℚ[x]/f(x)` be the number field given by adjoining the root of `f`
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
abbrev α : ℝ := 1 - 1e-12
abbrev β : ℝ := 1 + 1e-12

-- We only need an upper bound on the regulator
theorem regulator_aux : ∃ m : ℕ, 1 ≤ m ∧
    reg ∈ Set.Icc (α * m • regulator K) (β * m • regulator K) := by
  sorry

-- We will certify that the residue of `K` is roughly `0.366086210051...`
abbrev res : ℝ := 0.366086210051

-- But we only need a weak lower bound on the residue
theorem dedekindResidue_ge : 0.197 ≤ dedekindZeta_residue K := by
  sorry

-- The final errors on the regulator and residue
abbrev ε_reg : ℝ := 1e-10
abbrev ε_res : ℝ := 1e-10

-- The class number formula certifies the torsion order, the regulator, and the class number
theorem classNumberFormula :
    torsionOrder K = 2 ∧ |regulator K - reg| < ε_reg ∧
      classNumber K = 2 ∧ |dedekindZeta_residue K - res| < ε_res := by
  refine NumberField.classNumberFormula K
    4 nrRealPlaces_eq
    1 nrComplexPlaces_eq
    19208000 discr_eq
    2 torsionOrder_aux
    α β (by positivity)
    reg regulator_aux
    2 classNumber_aux (by positivity)
    0.197 dedekindResidue_ge ?_
    ε_reg (by dyadic_interval [approx := 40]) (by dyadic_interval [approx := 40])
    res ε_res ?_ ?_ <;> norm_cast <;> push_cast <;> dyadic_interval [approx := 40]

-- The number field `K` has exactly two roots of unity
theorem torsionOrder_eq : torsionOrder K = 2 := by
  exact classNumberFormula.1

-- The number field `K` has class number `2`
theorem classNumber_eq : classNumber K = 2 := by
  exact classNumberFormula.2.2.1

-- The regulator of `K` is within `10^-10` of `15.9596951835`
theorem regulator_mem : |regulator K - 15.9596951835| < 1e-10 := by
  exact classNumberFormula.2.1

-- The residue of `K` is within `10^-10` of `0.366086210051`
theorem residue_mem : |dedekindZeta_residue K - 0.366086210051| < 1e-10 := by
  exact classNumberFormula.2.2.2

end

end SexticExample
