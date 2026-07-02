import CertifyingLmfdbData.Polynomial.AllRoots
import CertifyingLmfdbData.Regulator.RegulatorBound
import CertifyingLmfdbData.Regulator.MatrixPerturbation

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

def log_bound_fun : ℝ → ℝ := sorry
theorem log_bound (x y : ℂ) (ε : ℝ) (hxy : ‖x - y‖ ≤ ε) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ log_bound_fun ε := sorry

theorem matrix_entry_diffs :
    ∀ i j, |bound_matrix_exact i j - bound_matrix_approx i j| ≤ 2 * log_bound_fun 1e-55 := fun i j ↦ by
  rw [bound_matrix_exact, bound_matrix_approx]
  calc
    _ = |(t j : ℝ)| * |Real.log ‖(Polynomial.aeval (α j)) (u i)‖ - Real.log ‖(Polynomial.aeval (α_approx j)) (u i)‖| := by
      rw [← abs_mul, mul_sub]
      simp
    _ ≤ 2 * |Real.log ‖(Polynomial.aeval (α j)) (u i)‖ - Real.log ‖(Polynomial.aeval (α_approx j)) (u i)‖| := by
      gcongr
      fin_cases j <;> simp
    _ ≤ 2 * log_bound_fun 1e-55 := by
      gcongr
      apply log_bound
      have := sigma_bounds_uniform
      simp_rw [α, α_approx]
      sorry

end
