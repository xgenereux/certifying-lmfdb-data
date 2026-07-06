import CertifyingLmfdbData.Polynomial.Tactic
import CertifyingLmfdbData.Polynomial.LoadCert

/-! PROFILING: the 100000-digit certificate of `Test100000.lean`, but with `v` and `M` read from
files by the `LoadCert` elaborators instead of inline decimal literals. -/
open Polynomial
namespace Test100000File

noncomputable def p : Polynomial ℚ := X^6 - 2*X - 2

noncomputable def v : Fin 2 → ℝ :=
  load_vec "CertifyingLmfdbData/Polynomial/Tests/cert100000_v.txt"

noncomputable def M : Matrix (Fin 2) (Fin 2) ℝ :=
  load_mat "CertifyingLmfdbData/Polynomial/Tests/cert100000_m.txt"

set_option profiler true in
set_option maxHeartbeats 4000000 in
noncomputable def prof : UniqueRootNear p (toComplex v) 1e-99997 := by
  unique_root_near M

end Test100000File
