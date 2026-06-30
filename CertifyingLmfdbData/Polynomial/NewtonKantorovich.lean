/-
Copyright (c) 2026 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Heather Macbeth
-/

import Mathlib

open ENNReal NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/- There is a proof of this theorem in a private repository - talk to b-mehta. -/
theorem newton_kantorovich_fd [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (hXY : Module.finrank ℝ X = Module.finrank ℝ Y)
    {F : X → Y} {DF : X → X →L[ℝ] Y} (hF : ∀ x, HasFDerivAt F (DF x) x) (hDF : Continuous DF)
    {A : Y →L[ℝ] X} {R : ℝ≥0∞} {x₀ : X} {y z₁ z₂ : ℝ≥0}
    (hy : ‖A (F x₀)‖₊ ≤ y)
    (hz₁ : ‖1 - A.comp (DF x₀)‖₊ ≤ z₁)
    (hz₂ : ∀ x ∈ Metric.closedEBall x₀ R, ‖A.comp (DF x - DF x₀)‖₊ ≤ z₂ * ‖x - x₀‖₊)
    {r : ℝ≥0} (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    ∃! x, F x = 0 ∧ ‖x - x₀‖₊ ≤ r := by
  sorry
