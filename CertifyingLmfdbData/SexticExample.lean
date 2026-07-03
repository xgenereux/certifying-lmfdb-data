import CertifyingLmfdbData.ClassNumberFormula
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal
import CertifyingLmfdbData.Regulator_All
import CertifyingLmfdbData.ResidueLowerBoundDegSix
import CertifyingLmfdbData.Torsion_All

namespace SexticExample

noncomputable section

open Polynomial Module NumberField InfinitePlace Units

-- We only need a lower bound on the number of roots of unity
theorem torsionOrder_aux : 2 ∣ torsionOrder K := by
  exact two_dvd_torsion

-- We will certify that the regulator of `K` is roughly `15.959695183485...`
abbrev reg : ℝ := 15.959695183485

-- The error on our computation of the regulator of `K`
abbrev α : ℝ := 1 - 1e-12
abbrev β : ℝ := 1 + 1e-12

-- We only need an upper bound on the regulator
theorem regulator_aux : ∃ m : ℕ, 1 ≤ m ∧
    reg ∈ Set.Icc (α * m • regulator K) (β * m • regulator K) := by
  exact _root_.regulator_aux

-- We will certify that the residue of `K` is roughly `0.366086210051...`
abbrev res : ℝ := 0.366086210051

-- But we only need a weak lower bound on the residue
theorem dedekindResidue_ge
    (grh : GeneralizedRiemannHypothesis DegSix.K₆)
    (rh : RiemannHypothesis) : 0.197 ≤ dedekindZeta_residue K := by
  suffices 198 / 1000 ≤ dedekindZeta_residue K by
    grind
  apply DegSix.residue_lower_bound_degSix <;> assumption

-- The final errors on the regulator and residue
abbrev ε_reg : ℝ := 5*1e-11
abbrev ε_res : ℝ := 1e-10

-- The class number formula certifies the torsion order, the regulator, and the class number
theorem classNumberFormula (grh : GeneralizedRiemannHypothesis DegSix.K₆) (rh : RiemannHypothesis) :
    torsionOrder K = 2 ∧ |regulator K - reg| < ε_reg ∧
      classNumber K = 2 ∧ |dedekindZeta_residue K - res| < ε_res := by
  refine NumberField.classNumberFormula K
    4 nrRealPlaces_eq
    1 nrComplexPlaces_eq
    (-19208000) discr_eq
    2 torsionOrder_aux
    α β (by positivity)
    reg regulator_aux
    2 classNumber_aux (by positivity)
    0.197 (dedekindResidue_ge grh rh) ?_
    ε_reg (by dyadic_interval [approx := 40]) (by dyadic_interval [approx := 40])
    res ε_res ?_ ?_ <;> norm_cast <;> push_cast <;>
    simp only [abs_neg, Nat.abs_ofNat] <;> dyadic_interval [approx := 40]

-- The number field `K` has exactly two roots of unity
theorem torsionOrder_eq
    (grh : GeneralizedRiemannHypothesis DegSix.K₆)
    (rh : RiemannHypothesis) :
    torsionOrder K = 2 := by
  exact (classNumberFormula grh rh).1

-- The number field `K` has class number `2`
theorem classNumber_eq
    (grh : GeneralizedRiemannHypothesis DegSix.K₆)
    (rh : RiemannHypothesis) :
    classNumber K = 2 := by
  exact (classNumberFormula grh rh).2.2.1

-- The regulator of `K` is within `10^-10` of `15.9596951835`
theorem regulator_mem
    (grh : GeneralizedRiemannHypothesis DegSix.K₆)
    (rh : RiemannHypothesis) :
    |regulator K - 15.9596951835| < 1e-10 := by
  grind [(classNumberFormula grh rh).2.1]

-- The residue of `K` is within `10^-10` of `0.366086210051`
theorem residue_mem
    (grh : GeneralizedRiemannHypothesis DegSix.K₆)
    (rh : RiemannHypothesis) :
    |dedekindZeta_residue K - 0.366086210051| < 1e-10 := by
  exact (classNumberFormula grh rh).2.2.2

#printaxioms regulator_mem
#printaxioms residue_mem

#check belabas_friedman_thm1
#check DegSix.nfPrimes1000_spec

end

end SexticExample
