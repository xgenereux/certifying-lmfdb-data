-- This module serves as the root of the `IdealArithmetic` library.
-- Import modules here that should be built as part of the library.
import IdealArithmetic.ClassGroupProject
import IdealArithmetic.DedekindProject
import IdealArithmetic.IdealArithmetic
-- Galois-group certification showcase (all `IdealArithmetic.Galois.*` build via this sink).
import IdealArithmetic.Galois.Examples.DegSixA4C2
-- NOTE: the LMFDB number-field certificates under `IdealArithmetic/Examples/NF*` are ported to
-- this toolchain and build green, but are deliberately NOT imported here. Each is a standalone
-- certificate that reuses root-namespace names (`C`, `T`, …), so co-importing several into one
-- environment collides (e.g. `C._proof_6`). As in upstream's default build they are left out of
-- this build root and compiled on demand, e.g.
--   lake build IdealArithmetic.Examples.NF5_1_3790297_2.Results5_1_3790297_2
