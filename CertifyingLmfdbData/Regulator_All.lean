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
abbrev bound_matrix := Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖
abbrev bound := |bound_matrix.det|

abbrev α_approx : Fin 4 → ℂ := ![toComplex (approxRoots 0),
                                 toComplex (approxRoots 1),
                                 toComplex (approxRoots 2),
                                 toComplex (approxRoots 4)]
abbrev bound_matrix_approx := Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α_approx j)‖
abbrev bound_approx := |bound_matrix_approx.det|

instance : Fact (Irreducible f) := by sorry

-- AI generated
theorem det_fin_four_scratch (A : Matrix (Fin 4) (Fin 4) ℝ) :
    A.det =
      A 0 0 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det
      - A 0 1 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 1)).det
      + A 0 2 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 2)).det
      - A 0 3 * (A.submatrix (Fin.succAbove 0) (Fin.succAbove 3)).det := by
  rw [Matrix.det_succ_row A 0]
  simp [Fin.sum_univ_four]
  ring

-- AI generated, not reviewed
theorem log_bound_norm {x y : ℂ} {ε : ℝ}
    (hεx : ε < ‖y‖) (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
  have hε_nonneg : 0 ≤ ε := (norm_nonneg (x - y)).trans hxy
  have hy_pos : 0 < ‖y‖ := lt_of_le_of_lt hε_nonneg hεx
  have hy_sub_pos : 0 < ‖y‖ - ε := sub_pos.mpr hεx
  have hx_lower : ‖y‖ - ε ≤ ‖x‖ := by
    have : ‖y‖ - ‖x‖ ≤ ε := by
      calc
        ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
        _ = ‖x - y‖ := by rw [norm_sub_rev]
        _ ≤ ε := hxy
    linarith
  have hx_pos : 0 < ‖x‖ := hy_sub_pos.trans_le hx_lower
  have hx_upper : ‖x‖ ≤ ‖y‖ + ε := by
    have : ‖x‖ - ‖y‖ ≤ ε := (norm_sub_norm_le x y).trans hxy
    linarith
  have hy_add_pos : 0 < ‖y‖ + ε := by positivity
  have hright :
      Real.log (‖y‖ / (‖y‖ - ε)) = Real.log ‖y‖ - Real.log (‖y‖ - ε) := by
    rw [Real.log_div hy_pos.ne' hy_sub_pos.ne']
  have hupper :
      Real.log ‖x‖ - Real.log ‖y‖ ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
    have hleft :
        Real.log (‖y‖ + ε) - Real.log ‖y‖ = Real.log ((‖y‖ + ε) / ‖y‖) := by
      rw [Real.log_div hy_add_pos.ne' hy_pos.ne']
    have hratio : (‖y‖ + ε) / ‖y‖ ≤ ‖y‖ / (‖y‖ - ε) := by
      rw [div_le_div_iff₀ hy_pos hy_sub_pos]
      nlinarith [sq_nonneg ε]
    calc
      Real.log ‖x‖ - Real.log ‖y‖ ≤ Real.log (‖y‖ + ε) - Real.log ‖y‖ :=
        sub_le_sub_right (Real.log_le_log hx_pos hx_upper) _
      _ = Real.log ((‖y‖ + ε) / ‖y‖) := hleft
      _ ≤ Real.log (‖y‖ / (‖y‖ - ε)) :=
        Real.log_le_log (div_pos hy_add_pos hy_pos) hratio
  have hlower :
      Real.log ‖y‖ - Real.log ‖x‖ ≤ Real.log (‖y‖ / (‖y‖ - ε)) := by
    rw [hright]
    exact sub_le_sub_left (Real.log_le_log hy_sub_pos hx_lower) _
  exact abs_le.mpr ⟨by linarith, hupper⟩

-- AI generated, not reviewed
theorem log_bound {x y : ℂ} {ε M : ℝ} (hεM : ε < M) (hMy : M ≤ ‖y‖)
    (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ Real.log (M / (M - ε)) := by
  have hε_nonneg : 0 ≤ ε := (norm_nonneg (x - y)).trans hxy
  have hεy : ε < ‖y‖ := hεM.trans_le hMy
  have hy_pos : 0 < ‖y‖ := lt_of_le_of_lt hε_nonneg hεy
  have hy_sub_pos : 0 < ‖y‖ - ε := sub_pos.mpr hεy
  have hM_pos : 0 < M := lt_of_le_of_lt hε_nonneg hεM
  have hM_sub_pos : 0 < M - ε := sub_pos.mpr hεM
  refine (log_bound_norm hεy hxy).trans ?_
  apply Real.log_le_log (div_pos hy_pos hy_sub_pos)
  rw [div_le_div_iff₀ hy_sub_pos hM_sub_pos]
  nlinarith [mul_le_mul_of_nonneg_left hMy hε_nonneg]

-- TODO : do this non-uniformly
theorem matrix_entry_uniform_bound :
    ∀ i j, 0.05 ≤ ‖Polynomial.aeval (α_approx j) (u i)‖ := fun i j ↦ by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  fin_cases j <;>
  simp [fundUnits, fundU1, fundU2, fundU3, fundU4] <;>
    fin_cases i <;>
      simp [approxRoots, rroot1, rroot2, rroot3, croot1] <;>
      ring_nf <;>
      simp [Complex.I_pow_eq_pow_mod'] <;> ring_nf <;>
      dyadic_interval [approx := 10]

theorem matrix_entry_diffs :
    ∀ i j, |bound_matrix i j - bound_matrix_approx i j| ≤
              2 * 1e-53 := fun i j ↦ by
  calc
    _ = |(t j : ℝ)| * |Real.log ‖(u i).aeval (α j)‖ -
          Real.log ‖(u i).aeval (α_approx j)‖| := by
      rw [← abs_mul, mul_sub]
      simp
    _ ≤ 2 * |Real.log ‖(u i).aeval (α j)‖ -
          Real.log ‖(u i).aeval (α_approx j)‖| := by
      gcongr
      fin_cases j <;> simp
    _ ≤ 2 * 1e-53 := by
      gcongr
      have ineq_1 : ‖(u i).aeval (α j) - (u i).aeval (α_approx j)‖ ≤ 1e-55 := by
        fin_cases j
        · convert sigma_bounds_uniform 0 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 1 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 2 i <;> simp [uniqueRoots]
        · convert sigma_bounds_uniform 4 i <;> simp [uniqueRoots]
      grw [log_bound (by norm_num) (matrix_entry_uniform_bound i j) ineq_1]
      dyadic_interval [approx := 1000]

theorem bound_diff : |bound - bound_approx| ≤ 1e-20 := by
  have := absolute_bound_frob' bound_matrix_approx bound_matrix
    (Matrix.of fun i j ↦ 2 * 1e-53) (by simpa using matrix_entry_diffs)
  grw [abs_abs_sub_abs_le, ← Real.norm_eq_abs, this]
  simp [Complex.norm_eq_sqrt_sq_add_sq,
        Fin.sum_univ_castSucc, approxRoots, rroot1, rroot2, rroot3, croot1,
        fundUnits, fundU1, fundU2, fundU3, fundU4]
  ring_nf
  simp [Complex.I_pow_eq_pow_mod']
  ring_nf
  dyadic_interval [approx := 100]

theorem bound_regulator : ∃ k : ℕ, 1 ≤ k ∧ bound = k * NumberField.Units.regulator (AdjoinRoot f) := by
  refine regulator_le_regOfFamily_comp
    (m := m) (f := f) (u := u) (α := α) (t := t) (bound := bound)
    ?_ (fun i ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun hc ↦ ?_) ?_
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
  · have := bound_diff
    rw [hc] at this
    apply this.not_gt
    simp
    sorry
  · rfl

set_option maxHeartbeats 2000000 in
lemma test_2 : 1e-20 < |bound_matrix_approx.det| := by
  simp_rw [det_fin_four_scratch, Matrix.det_fin_three]
  simp [Complex.norm_eq_sqrt_sq_add_sq,
        Fin.sum_univ_castSucc, approxRoots, rroot1, rroot2, rroot3, croot1,
        fundUnits, fundU1, fundU2, fundU3, fundU4]
  ring_nf
  simp [Complex.I_pow_eq_pow_mod']
  ring_nf
  dyadic_interval [approx := 100]

end
