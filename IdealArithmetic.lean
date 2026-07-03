-- This module serves as the root of the `IdealArithmetic` library.
-- Import modules here that should be built as part of the library.
import IdealArithmetic.ClassGroupProject
import IdealArithmetic.DedekindProject
import IdealArithmetic.IdealArithmetic
-- Galois-group certification showcase (all `IdealArithmetic.Galois.*` build via this sink).
import IdealArithmetic.Galois.Examples.DegSixA4C2
-- NOTE: the LMFDB number-field certificates under `IdealArithmetic/Examples/NF*` are
-- vendored (present in the tree) but intentionally not imported here yet — so, as in
-- upstream's own default build, they are not part of the build target. Their v4.30-era
-- computational certificate proofs are being ported to this toolchain separately.
