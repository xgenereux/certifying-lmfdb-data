import CertifyingLmfdbData.Polynomial.AllRoots
import CertifyingLmfdbData.Regulator.RegulatorBound
import CertifyingLmfdbData.Regulator.MatrixPerturbation
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal

noncomputable section

open DegSix

abbrev n : ℕ := 6
abbrev m : ℕ := 4
abbrev f := DegSix.myPoly
abbrev u := fundUnits
abbrev α : Fin 4 → ℂ := ![uniqueRootNear_rroot1.root,
                       uniqueRootNear_rroot2.root,
                       uniqueRootNear_rroot3.root,
                       uniqueRootNear_croot1.root]
abbrev t : Fin 4 → ℕ := ![1, 1, 1, 2]
abbrev bound_matrix_exact := Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖
abbrev bound := |bound_matrix_exact.det|

abbrev α_approx : Fin 4 → ℂ := ![toComplex (approxRoots 0),
                                 toComplex (approxRoots 1),
                                 toComplex (approxRoots 2),
                                 toComplex (approxRoots 4)]
abbrev bound_matrix_approx := Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α_approx j)‖
abbrev bound_approx := |bound_matrix_approx.det|

instance : Fact (Irreducible f) := by sorry

theorem bound_regulator : ∃ k : ℕ, k ≠ 0 ∧ bound = k * NumberField.Units.regulator (AdjoinRoot f) := by
  refine regulator_le_regOfFamily_comp
    (m := m) (f := f) (u := u) (α := α) (t := t) (bound := bound)
    ?_ (fun i ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) ?_ ?_
  · sorry
  · fin_cases i <;>
      simp [uniqueRootNear_rroot1.isRoot,
            uniqueRootNear_rroot2.isRoot,
            uniqueRootNear_rroot3.isRoot,
            uniqueRootNear_croot1.isRoot]
  · fin_cases i <;>
      simp [rroot1_im_zero, rroot2_im_zero, rroot3_im_zero, zero_lt_croot4_im.le]
  · fin_cases i <;>
      fin_cases j <;>
        intros hij <;>
        apply UniqueRootNear.distinct <;>
        simp_all [rroot1, rroot2, rroot3, croot1] <;>
        norm_num
  · fin_cases i <;>
      simp [rroot1_im_zero, rroot2_im_zero, rroot3_im_zero, zero_lt_croot4_im.ne.symm]
  · sorry
  · sorry
  · rfl

-- AI generated, not reviewed
theorem log_bound_norm (x y : ℂ) (ε : ℝ) (hεx : ε < ‖x‖) (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ Real.log (‖x‖ / (‖x‖ - ε)) := by
  have hε_nonneg : 0 ≤ ε := (norm_nonneg (x - y)).trans hxy
  have hx_pos : 0 < ‖x‖ := lt_of_le_of_lt hε_nonneg hεx
  have hx_sub_pos : 0 < ‖x‖ - ε := sub_pos.mpr hεx
  have hy_lower : ‖x‖ - ε ≤ ‖y‖ := by
    have : ‖x‖ - ‖y‖ ≤ ε := (norm_sub_norm_le x y).trans hxy
    linarith
  have hy_pos : 0 < ‖y‖ := hx_sub_pos.trans_le hy_lower
  have hy_upper : ‖y‖ ≤ ‖x‖ + ε := by
    have : ‖y‖ - ‖x‖ ≤ ε := by
      calc
        ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
        _ = ‖x - y‖ := by rw [norm_sub_rev]
        _ ≤ ε := hxy
    linarith
  have hx_add_pos : 0 < ‖x‖ + ε := by positivity
  have hright :
      Real.log (‖x‖ / (‖x‖ - ε)) = Real.log ‖x‖ - Real.log (‖x‖ - ε) := by
    rw [Real.log_div hx_pos.ne' hx_sub_pos.ne']
  have hupper :
      Real.log ‖x‖ - Real.log ‖y‖ ≤ Real.log (‖x‖ / (‖x‖ - ε)) := by
    rw [hright]
    exact sub_le_sub_left (Real.log_le_log hx_sub_pos hy_lower) _
  have hlower :
      Real.log ‖y‖ - Real.log ‖x‖ ≤ Real.log (‖x‖ / (‖x‖ - ε)) := by
    have hleft :
        Real.log (‖x‖ + ε) - Real.log ‖x‖ = Real.log ((‖x‖ + ε) / ‖x‖) := by
      rw [Real.log_div hx_add_pos.ne' hx_pos.ne']
    have hratio : (‖x‖ + ε) / ‖x‖ ≤ ‖x‖ / (‖x‖ - ε) := by
      rw [div_le_div_iff₀ hx_pos hx_sub_pos]
      nlinarith [sq_nonneg ε]
    calc
      Real.log ‖y‖ - Real.log ‖x‖ ≤ Real.log (‖x‖ + ε) - Real.log ‖x‖ :=
        sub_le_sub_right (Real.log_le_log hy_pos hy_upper) _
      _ = Real.log ((‖x‖ + ε) / ‖x‖) := hleft
      _ ≤ Real.log (‖x‖ / (‖x‖ - ε)) :=
        Real.log_le_log (div_pos hx_add_pos hx_pos) hratio
  exact abs_le.mpr ⟨by linarith, hupper⟩

theorem log_bound (x y : ℂ) (ε M : ℝ) (hεM : ε < M) (hMx : M ≤ ‖x‖)
    (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ Real.log (M / (M - ε)) := by
  have hε_nonneg : 0 ≤ ε := (norm_nonneg (x - y)).trans hxy
  have hεx : ε < ‖x‖ := hεM.trans_le hMx
  have hx_pos : 0 < ‖x‖ := lt_of_le_of_lt hε_nonneg hεx
  have hx_sub_pos : 0 < ‖x‖ - ε := sub_pos.mpr hεx
  have hM_pos : 0 < M := lt_of_le_of_lt hε_nonneg hεM
  have hM_sub_pos : 0 < M - ε := sub_pos.mpr hεM
  refine (log_bound_norm x y ε hεx hxy).trans ?_
  apply Real.log_le_log (div_pos hx_pos hx_sub_pos)
  rw [div_le_div_iff₀ hx_sub_pos hM_sub_pos]
  nlinarith [mul_le_mul_of_nonneg_left hMx hε_nonneg]

theorem matrix_entry_uniform_bound :
    ∀ i j, 0.05 ≤ ‖Polynomial.aeval (α_approx j) (u i)‖ := fun i j ↦ by
  rw [Complex.norm_eq_sqrt_sq_add_sq, α_approx]
  fin_cases j <;> fin_cases i <;>
    simp [approxRoots, rroot1, rroot2, rroot3, croot1,
          fundUnits, fundU1, fundU2, fundU3, fundU4] <;>
    ring_nf-- <;> simp [Complex.I_pow_eq_pow_mod']



/-
theorem matrix_entry_diffs :
    ∀ i j, |bound_matrix_exact i j - bound_matrix_approx i j| ≤
              2 * 1e-50 := fun i j ↦ by
  rw [bound_matrix_exact, bound_matrix_approx]
  calc
    _ = |(t j : ℝ)| * |Real.log ‖(u i).aeval (α j)‖ -
          Real.log ‖(u i).aeval (α_approx j)‖| := by
      rw [← abs_mul, mul_sub]
      simp
    _ ≤ 2 * |Real.log ‖(u i).aeval (α j)‖ -
          Real.log ‖(u i).aeval (α_approx j)‖| := by
      gcongr
      fin_cases j <;> simp
    _ ≤ 2 * 1e-50 := by
      gcongr
      have : ‖(u i).aeval (α j) - (u i).aeval (α_approx j)‖ ≤ 1e-55 := by
        fin_cases j
        · convert sigma_bounds_uniform 0 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 1 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 2 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 4 i <;> simp [uniqueRoots]
      -- TODO : do this non-uniformly
      have : 0.05 ≤ ‖Polynomial.aeval (α_approx j) (u i)‖ := by
        rw [Complex.norm_eq_sqrt_sq_add_sq, α_approx]
        fin_cases j <;> fin_cases i <;>
          simp [approxRoots, rroot1, rroot2, rroot3, croot1,
                fundUnits, fundU1, fundU2, fundU3, fundU4]
          --norm_num
      sorry
-/

end
