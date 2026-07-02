import Mathlib
/-!

# Importing the Residue Approximation

The work can be found in
- https://github.com/CBirkbeck/AINTLIB/blob/dev/dedekind-residue/projects/DedekindResidue/DedekindResidue/MainTheorem.lean

-/


open NumberField

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real FourierTransform

noncomputable def gammaFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

noncomputable def completedZetaPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|discr K| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s

def IsCompletedDedekindZeta (K : Type*) [Field K] [NumberField K] (Λ : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → Λ s = completedZetaPrefactor K s * dedekindZeta K s)
    ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H
        ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 → H s = s * (s - 1) * Λ s

def GeneralizedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ →
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Λ s ≠ 0

noncomputable def bSum (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  ∑ᶠ (p : {p : Ideal (RingOfIntegers K) // p.IsPrime ∧ p ≠ ⊥}) (m : ℕ),
    if 0 < m ∧ (Ideal.absNorm p.1 : ℝ) ^ m < X then
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2)) *
        (Real.sqrt X * Real.log X /
            ((Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2) *
              Real.log ((Ideal.absNorm p.1 : ℝ) ^ m)) - 1)
    else 0

noncomputable def bSumRel (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  bSum K X - bSum ℚ X

noncomputable def fK (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  3 * (bSumRel K X - bSumRel K (X / 9)) / (2 * Real.sqrt X * Real.log (3 * X))

theorem belabas_friedman_thm1 {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) *
              (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                (Real.sqrt X * Real.log (|discr K| : ℝ))) := by
  sorry
