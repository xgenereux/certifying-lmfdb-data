import CertifyingLmfdbData.Polynomial.Tactic
import CertifyingLmfdbData.Polynomial.LoadCert

/-! PROFILING: the 1000005-digit certificate of `Test1M.lean`, but with `v` and `M` read from
files by the `LoadCert` elaborators instead of inline decimal literals. -/
open Polynomial
namespace Test1MFile

noncomputable def p : Polynomial ℚ := X^6 - 2*X - 2

noncomputable def v : Fin 2 → ℝ :=
  load_vec "CertifyingLmfdbData/Polynomial/Tests/cert1M_v.txt"

noncomputable def M : Matrix (Fin 2) (Fin 2) ℝ :=
  load_mat "CertifyingLmfdbData/Polynomial/Tests/cert1M_m.txt"

noncomputable def prof : UniqueRootNear p (toComplex v) 1e-1000002 := by
  unique_root_near M

end Test1MFile
