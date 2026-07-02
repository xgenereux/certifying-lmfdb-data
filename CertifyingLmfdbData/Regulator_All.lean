import CertifyingLmfdbData.Polynomial.AllRoots
import CertifyingLmfdbData.Regulator.RegulatorBound
import CertifyingLmfdbData.Regulator.MatrixPerturbation

noncomputable section

open DegSix

def n : ℕ := 6
def m : ℕ := 4
def f := DegSix.myPoly
def u := fundUnits
def α : Fin 4 → ℂ := ![uniqueRootNear_rroot1.root,
                       uniqueRootNear_rroot2.root,
                       uniqueRootNear_rroot3.root,
                       uniqueRootNear_croot1.root]
def t : Fin 4 → ℕ := ![1, 1, 1, 2]
def bound := |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖).det|

instance : Fact (Irreducible f) := by sorry

theorem bound_regulator : ∃ k : ℕ, k ≠ 0 ∧ bound = k * NumberField.Units.regulator (AdjoinRoot f) := by
  refine regulator_le_regOfFamily_comp
    (m := m) (f := f) (u := u) (α := α) (t := t) (bound := bound)
    ?_ (fun i ↦ ?_) (fun i ↦ ?_) ?_ ?_ ?_ ?_ ?_
  · sorry
  · fin_cases i <;>
      simp [f, α, m, uniqueRootNear_rroot1.isRoot,
                     uniqueRootNear_rroot2.isRoot,
                     uniqueRootNear_rroot3.isRoot,
                     uniqueRootNear_croot1.isRoot]
  · fin_cases i <;>
      simp [α, m]
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry


end
