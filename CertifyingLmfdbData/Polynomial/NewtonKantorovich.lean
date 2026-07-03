/-
Copyright (c) 2026 Bhavik Mehta All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Heather Macbeth
-/

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Positivity

import Mathlib.Topology.MetricSpace.Contracting

open NNReal Function Set

variable {α : Type*} [MetricSpace α] [CompleteSpace α] {K : ℝ≥0} {f : α → α}

namespace ContractingWith

omit [CompleteSpace α] in
theorem eq_of_fixedPoints {s : Set α} (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s)
    {x y : α} (hxs : x ∈ s) (hys : y ∈ s) (hx : IsFixedPt f x) (hy : IsFixedPt f y) :
    x = y := by
  have hx' : IsFixedPt (hsf.restrict f s s) ⟨x, hxs⟩ := Subtype.ext hx
  have hy' : IsFixedPt (hsf.restrict f s s) ⟨y, hys⟩ := Subtype.ext hy
  simpa using (hf.eq_or_edist_eq_top_of_fixedPoints hx' hy').resolve_right (edist_ne_top _ _)

variable (f) in
-- avoid `fixedPoint _` in pretty printer
/-- Let `s` be a complete, nonempty, forward-invariant set of a self-map `f`. If `f` contracts on
`s`, then `efixedPoint` is the unique fixed point of the restriction of `f` to `s. -/
noncomputable def fixedPoint' {s : Set α} (hsc : IsClosed s) (hs' : s.Nonempty)
    (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) :
    α :=
  Classical.choose <|
    hf.exists_fixedPoint' hsc.isComplete hsf (Exists.choose_spec hs')
      (edist_ne_top (Exists.choose hs') _)

theorem fixedPoint'_mem {s : Set α} (hsc : IsClosed s) (hs' : s.Nonempty) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) :
    fixedPoint' f hsc hs' hsf hf ∈ s :=
  (Classical.choose_spec <|
    hf.exists_fixedPoint' hsc.isComplete hsf (Exists.choose_spec hs')
      (edist_ne_top (Exists.choose hs') _)).1

theorem fixedPoint'_isFixedPt {s : Set α} (hsc : IsClosed s) (hs' : s.Nonempty)
    (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s s) :
    IsFixedPt f (fixedPoint' f hsc hs' hsf hf) :=
  (Classical.choose_spec <|
    hf.exists_fixedPoint' hsc.isComplete hsf (Exists.choose_spec hs')
      (edist_ne_top (Exists.choose hs') _)).2.1

theorem fixedPoint'_unique {s : Set α} (hsc : IsClosed s) (hs' : s.Nonempty)
    (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s s)
    {x : α} (hxs : x ∈ s) (hx : IsFixedPt f x) :
    x = fixedPoint' f hsc hs' hsf hf :=
  hf.eq_of_fixedPoints hsf hxs (hf.fixedPoint'_mem hsc hs' hsf) hx
    (hf.fixedPoint'_isFixedPt hsc hs' hsf)

end ContractingWith


section banach

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

open NNReal ENNReal

-- for `import Mathlib.Analysis.Normed.Group.Basic`
theorem mem_closedBall_iff_nnnorm {E : Type*} [SeminormedAddCommGroup E] {a b : E} {r : ℝ≥0} :
    b ∈ Metric.closedBall a r ↔ ‖b - a‖₊ ≤ r :=
  mem_closedBall_iff_norm

-- for `Mathlib.Analysis.Normed.Operator.Basic`
theorem ContinuousLinearMap.le_opNorm_nnnorm {𝕜 : Type*} {𝕜₂ : Type*} {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [RingHomIsometric σ₁₂] (f : E →SL[σ₁₂] F) (x : E) :
    ‖f x‖₊ ≤ ‖f‖₊ * ‖x‖₊ := by
  change (_ : ℝ) ≤ _
  dsimp
  apply ContinuousLinearMap.le_opNorm

open Metric in
omit [CompleteSpace X] in
/-- Derivative criterion for `ContractingWith`. -/
theorem contractingWith_of_nnnorm_fderiv_le
    {T : X → X} {DT : X → X →L[ℝ] X} (hT : ∀ (x : X), HasFDerivAt T (DT x) x)
    {x₀ : X} {r : ℝ≥0} (hTx₀ : (closedBall x₀ r).MapsTo T (closedBall x₀ r))
    {K : ℝ≥0} (hzK : K < 1)
    (hDT : ∀ {x : X}, x ∈ closedBall x₀ r → ‖DT x‖₊ ≤ K) :
    ContractingWith K (hTx₀.restrict T (closedBall x₀ r) (closedBall x₀ r)) := by
  refine ⟨hzK, ?_⟩
  intro a b
  refine (convex_closedBall x₀ r).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ?_ ?_ a.prop b.prop
  · intro x hx
    exact (hT x).differentiableAt
  · intro x hx
    rw [(hT x).fderiv]
    exact hDT hx

open Metric in
theorem contraction_mapping
    {T : X → X} {DT : X → X →L[ℝ] X} (hT : ∀ x, HasFDerivAt T (DT x) x) (hDT : Continuous DT)
    {R : ℝ≥0} {x₀ : X} {y z₁ z₂ : ℝ≥0}
    (hy : ‖T x₀ - x₀‖₊ ≤ y)
    (hz₁ : ‖DT x₀‖₊ ≤ z₁)
    (hz₂ : ∀ x ∈ closedBall x₀ R, ‖DT x - DT x₀‖₊ ≤ z₂ * ‖x - x₀‖₊)
    {r : ℝ≥0} (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    ∃! x, T x = x ∧ ‖x - x₀‖₊ ≤ r := by
  have H1 {x : X} (hx : x ∈ closedBall x₀ r) :=
  calc
    T x - x₀
      = T x₀ - x₀ + ∫ t in 0..1, DT (x₀ + t • (x - x₀)) (x - x₀) := by
        have key (t) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
            HasDerivAt (fun s ↦ T (x₀ + s • (x - x₀))) ((DT (x₀ + t • (x - x₀))) (x - x₀)) t := by
          simpa using!
            (hT _).comp_hasDerivAt _ (((hasDerivAt_id t).smul_const (f := x - x₀)).const_add x₀)
        have H := intervalIntegral.integral_eq_sub_of_hasDerivAt key ?_
        · simp only [one_smul, add_sub_cancel, zero_smul, add_zero] at H
          linear_combination (norm := abel) -H
        apply Continuous.intervalIntegrable
        fun_prop
    _ = T x₀ - x₀ + DT x₀ (x - x₀)
        + ∫ t in 0..1, (DT (x₀ + t • (x - x₀)) - DT x₀) (x - x₀) := by
        conv_rhs => simp only [sub_apply]
        rw [intervalIntegral.integral_sub, intervalIntegral.integral_const]
        · simp
        · apply Continuous.intervalIntegrable
          fun_prop
        · apply Continuous.intervalIntegrable
          fun_prop
  have H2 {x : X} (hx : x ∈ closedBall x₀ r) :
      ‖T x - x₀‖₊ ≤ y + z₁ * r + z₂ * r ^ 2 / 2 := by
    rw [H1 hx]
    rw [mem_closedBall_iff_nnnorm] at hx
    grw [nnnorm_add_le, nnnorm_add_le, hy, ContinuousLinearMap.le_opNorm_nnnorm, hz₁, hx]
    gcongr
    refine (intervalIntegral.norm_integral_le_integral_norm (by simp)).trans ?_
    dsimp
    calc _ ≤ ∫ t in 0..1, (z₂ * r ^ 2) * t := ?_
      _ = _ := by
          rw [intervalIntegral.integral_const_mul, integral_id]
          ring
    apply intervalIntegral.integral_mono_on (by simp)
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
    intro t ht
    lift t to ℝ≥0 using ht.1
    change (‖(_ : X)‖₊ : ℝ) ≤ _
    norm_cast
    have H :=
      calc ‖x₀ + (t:ℝ) • (x - x₀) - x₀‖₊ = ‖(t:ℝ) • (x - x₀)‖₊ := by abel_nf
        _ = t * ‖x - x₀‖₊ := by simp [nnnorm_smul]
    grw [ContinuousLinearMap.le_opNorm_nnnorm, hz₂]
    · rw [H]
      ring_nf
      grw [hx]
    replace ht : t ≤ 1 := by simpa using ht
    grw [mem_closedBall_iff_nnnorm, H, hx, hrR, ht]
    simp
  have H3 : IsClosed (closedBall x₀ r) := isClosed_closedBall
  have H4 : (closedBall x₀ r).Nonempty := nonempty_closedBall.mpr NNReal.zero_le_coe
  have H5 : (closedBall x₀ r).MapsTo T (closedBall x₀ r) := by
    intro x hx
    rw [mem_closedBall_iff_nnnorm]
    grw [H2 hx, hyr]
  have H6 : ContractingWith (z₁ + z₂ * r) (H5.restrict T (closedBall x₀ r) (closedBall x₀ r)) := by
    apply contractingWith_of_nnnorm_fderiv_le hT _ hzr
    intro x hx
    calc ‖DT x‖₊ = ‖DT x₀ + (DT x - DT x₀)‖₊ := by simp
      _ ≤ z₁ + z₂ * r := by
          grw [← hrR] at hz₂
          specialize hz₂ x hx
          rw [mem_closedBall_iff_nnnorm] at hx
          grw [nnnorm_add_le, hz₁, hz₂, hx]
  simp_rw [← mem_closedBall_iff_nnnorm]
  refine ⟨H6.fixedPoint' T H3 H4 H5, ⟨H6.fixedPoint'_isFixedPt H3 H4 H5,
    H6.fixedPoint'_mem H3 H4 H5⟩, ?_⟩
  rintro x ⟨hTx, hx⟩
  exact H6.fixedPoint'_unique H3 H4 H5 hx hTx

theorem newton_kantorovich
    {F : X → Y} {DF : X → X →L[ℝ] Y} (hF : ∀ x, HasFDerivAt F (DF x) x) (hDF : Continuous DF)
    {A : Y →L[ℝ] X} (hA : Function.Injective A)
    {R : ℝ≥0∞} {x₀ : X} {y z₁ z₂ : ℝ≥0}
    (hy : ‖A (F x₀)‖₊ ≤ y)
    (hz₁ : ‖1 - A.comp (DF x₀)‖₊ ≤ z₁)
    (hz₂ : ∀ x ∈ Metric.closedEBall x₀ R, ‖A.comp (DF x - DF x₀)‖₊ ≤ z₂ * ‖x - x₀‖₊)
    {r : ℝ≥0} (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r)
    (hzr : z₁ + z₂ * r < 1) :
    ∃! x, F x = 0 ∧ ‖x - x₀‖₊ ≤ r := by
  let T (x : X) : X := x - A (F x)
  let DT (x : X) : X →L[ℝ] X := 1 - A.comp (DF x)
  have hT (x : X) : HasFDerivAt T (DT x) x := (hasFDerivAt_id x).sub (A.hasFDerivAt.comp _ (hF x))
  have hDT : Continuous DT := by fun_prop
  have hy : ‖T x₀ - x₀‖₊ ≤ y := by simpa [T]
  have hz₁ : ‖DT x₀‖₊ ≤ z₁ := by simpa [DT]
  have (x : X) : T x = x ↔ F x = 0 := by simp [T, map_eq_zero_iff A hA]
  have hz₂ : ∀ x ∈ Metric.closedBall x₀ r, ‖DT x - DT x₀‖₊ ≤ z₂ * ‖x - x₀‖₊ := by
    intro x hx
    rw [← nnnorm_neg]
    grw [← Metric.closedEBall_coe, hrR] at hx
    simpa [DT] using hz₂ x hx
  simpa [this] using contraction_mapping hT hDT hy hz₁ hz₂ (le_refl _) hyr hzr

theorem surjective_of_nk_assumptions
    {DF : X →L[ℝ] Y} {A : Y →L[ℝ] X} {z₁ : ℝ≥0}
    (hz₁ : ‖1 - A.comp DF‖₊ ≤ z₁) {r : ℝ≥0} (hzr : z₁ + r < 1) :
    Function.Surjective A := by
  obtain _ | _ := subsingleton_or_nontrivial X
  · exact (A : Y → X).surjective_to_subsingleton
  let ADF : X ≃L[ℝ] X := ContinuousLinearEquiv.unitsEquiv _ _ <|
    Units.ofNearby 1 (A ∘L DF) <| by
      simp only [Units.val_one, inv_one, norm_one]
      calc
        ‖A.comp (DF) - 1‖ = ‖1 - A.comp (DF)‖₊ := by simp [norm_sub_rev]
        _ ≤ z₁ := by gcongr
        _ < _ := by simp only [coe_lt_one]; apply lt_of_add_lt_of_nonneg_left hzr (by simp)
  exact .of_comp ADF.surjective

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
  apply newton_kantorovich hF hDF ?_ hy hz₁ hz₂ hrR hyr hzr
  apply (A.injective_iff_surjective_of_finrank_eq_finrank hXY.symm).2
  exact surjective_of_nk_assumptions hz₁ hzr

end banach

