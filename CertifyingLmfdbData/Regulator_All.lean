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
abbrev bound := |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖).det|

abbrev α_approx : Fin 4 → ℂ := ![toComplex (approxRoots 0),
                                 toComplex (approxRoots 1),
                                 toComplex (approxRoots 2),
                                 toComplex (approxRoots 4)]
abbrev approx_bound := |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α_approx j)‖).det|

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


end
