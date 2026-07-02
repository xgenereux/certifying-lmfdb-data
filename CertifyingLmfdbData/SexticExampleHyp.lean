import Mathlib
import CertifyingLmfdbData.Polynomial.AllRoots

/-!
# Externally-certified hypotheses for LMFDB field 6.4.19208000.1

The `sorry`ed facts about `K = ℚ[x]/(x⁶ - 5x⁴ - 50x² + 125)` that the rest of the
project consumes, collected in one place so that each fact is stated (and `sorry`ed)
exactly once.  They are to be discharged by the certification machinery elsewhere in
this project.

This file also bridges the two spellings of the defining polynomial used in the
project: `f = f₀.map (algebraMap ℤ ℚ)` here and `DegSix.myPoly` in
`Polynomial/AllRoots.lean` are *proved* equal, and the irreducibility instance is
transported, so downstream files need no separate irreducibility `sorry` for
`DegSix.myPoly`.
-/

namespace SexticExample

noncomputable section

open Polynomial Module NumberField InfinitePlace Units

-- Let `f = X^6 - 5*X^4 - 50 * X^2 + 125`
def f₀ : Polynomial ℤ := X^6 - 5*X^4 - 50 * X^2 + 125
def f : Polynomial ℚ := f₀.map (algebraMap ℤ ℚ)

-- The polynomial `f` is irreducible
instance : Fact (Irreducible f) := by
  sorry

-- Let `K = ℚ[x]/f(x)` be the number field given by adjoining the root of `f`
noncomputable def K : Type := AdjoinRoot f
deriving Field, NumberField

-- The number field `K` has degree `6`
theorem finrank_eq : finrank ℚ K = 6 := by
  sorry

-- The number field `K` has `4` real places
theorem nrRealPlaces_eq : nrRealPlaces K = 4 := by
  sorry

-- The number field `K` has `1` complex place
theorem nrComplexPlaces_eq : nrComplexPlaces K = 1 := by
  sorry

-- The number field `K` has discriminant `-19208000` (the signature is `(4, 1)`, so the
-- discriminant has sign `(-1)^1`; the LMFDB label records `|discr| = 19208000`)
theorem discr_eq : discr K = -19208000 := by
  sorry

-- We only need a lower bound on the number of roots of unity
theorem torsionOrder_aux : 2 ∣ torsionOrder K := by
  sorry

-- We only need an upper bound on the class number
theorem classNumber_aux : classNumber K ∣ 2 := by
  sorry

/-! ### Bridge to `DegSix.myPoly`

`Polynomial/AllRoots.lean` (and the files building on it) spell the same polynomial
directly over `ℚ`.  The two are equal, so the irreducibility hypothesis transports and
no second `sorry` is needed. -/

theorem f_eq_myPoly : f = DegSix.myPoly := by
  simp [f, f₀, DegSix.myPoly, Polynomial.map_ofNat]

instance : Fact (Irreducible DegSix.myPoly) := ⟨f_eq_myPoly ▸ (Fact.out : Irreducible f)⟩

end

end SexticExample
