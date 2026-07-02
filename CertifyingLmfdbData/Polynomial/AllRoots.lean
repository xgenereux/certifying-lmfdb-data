import CertifyingLmfdbData.Polynomial.Tactic

/-!
# All roots of `X⁶ - 5X⁴ - 50X² + 125`, certified

Each of the six roots is certified by `unique_root_near` from just a decimal approximation of
the root and a decimal approximation of the inverse Jacobian of the zero finder there; the
complex conjugate root comes for free via `UniqueRootNear.conj`.
-/

noncomputable section

namespace DegSix

open Polynomial Complex NNReal

def myPoly : Polynomial ℚ := X^6 - 5*X^4 - 50 * X^2 + 125

/-! ### Approximate roots and inverse Jacobians -/

def rroot1 : Fin 2 → ℝ := ![-3.0016143454854741319417131953855135509439233234822720487499, 0]
def rA1_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ -0.0016105823418225894202625671015800570118581107319413733500872, 0;
      0, -0.0016105823418225894202625671015800570118581107319413733500872 ]

def rroot2 : Fin 2 → ℝ := ![-1.4917135581481935578368807432879800495511374280152413050117, 0]
def rA2_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0.0058397219432993508175108135283434777310184356523066979515940, 0;
      0, 0.0058397219432993508175108135283434777310184356523066979515940 ]

def rroot3 : Fin 2 → ℝ := ![1.4917135581481935578368807432879800495511374280152413050117, 0]
def rA3_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ -0.0058397219432993508175108135283434777310184356523066979515940, 0;
      0, -0.0058397219432993508175108135283434777310184356523066979515940 ]

def rroot4 : Fin 2 → ℝ := ![3.0016143454854741319417131953855135509439233234822720487499, 0]
def rA4_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0.0016105823418225894202625671015800570118581107319413733500872, 0;
      0, 0.0016105823418225894202625671015800570118581107319413733500872 ]

def croot1 : Fin 2 → ℝ := ![0, 2.4969777769510355226216439250267029033550572578622404151129]
def cA1_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ 0, 0.0015526150743595132569328994275272689662500775889625889026909;
      -0.0015526150743595132569328994275272689662500775889625889026909, 0 ]

def croot1' : Fin 2 → ℝ := ![0, -2.4969777769510355226216439250267029033550572578622404151129]

/-! ### The four real roots -/

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot1`. -/
noncomputable def uniqueRootNear_rroot1 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot1) 1e-57 := by
  unique_root_near rA1_mat

/-- The root approximated by `rroot1` is real. -/
lemma rroot1_im_zero : uniqueRootNear_rroot1.root.im = 0 :=
  uniqueRootNear_rroot1.im_eq_zero (by simp [rroot1])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot2`. -/
noncomputable def uniqueRootNear_rroot2 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot2) 1e-57 := by
  unique_root_near rA2_mat

/-- The root approximated by `rroot2` is real. -/
lemma rroot2_im_zero : uniqueRootNear_rroot2.root.im = 0 :=
  uniqueRootNear_rroot2.im_eq_zero (by simp [rroot2])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot3`. -/
noncomputable def uniqueRootNear_rroot3 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot3) 1e-57 := by
  unique_root_near rA3_mat

/-- The root approximated by `rroot3` is real. -/
lemma rroot3_im_zero : uniqueRootNear_rroot3.root.im = 0 :=
  uniqueRootNear_rroot3.im_eq_zero (by simp [rroot3])

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `rroot4`. -/
noncomputable def uniqueRootNear_rroot4 :
    UniqueRootNear (aeval · myPoly) (toComplex rroot4) 1e-57 := by
  unique_root_near rA4_mat

/-- The root approximated by `rroot4` is real. -/
lemma rroot4_im_zero : uniqueRootNear_rroot4.root.im = 0 :=
  uniqueRootNear_rroot4.im_eq_zero (by simp [rroot4])

/-! ### The complex conjugate pair -/

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1`. -/
noncomputable def uniqueRootNear_croot1 :
    UniqueRootNear (aeval · myPoly) (toComplex croot1) 1e-57 := by
  unique_root_near cA1_mat

/-- `myPoly` has a unique root within (sup-norm) distance `1e-57` of `croot1'`, the conjugate
of `croot1`. -/
noncomputable def uniqueRootNear_croot1' :
    UniqueRootNear (aeval · myPoly) (toComplex croot1') 1e-57 :=
  uniqueRootNear_croot1.conj

open Polynomial

def myPoly' : Polynomial ℚ := X^6 + 7 * X^5 + X^4 - 1

def A_mat : Matrix (Fin 2) (Fin 2) ℝ := !![ 0.130923022789476, 0; 0, 0.130923022789476 ]

example : UniqueRootNear (aeval · myPoly') (toComplex ![0.641564061943673, 0]) 1e-10 := by
  unique_root_near A_mat

example : UniqueRootNear (aeval · (X^6 - 1 : Polynomial ℚ)) (toComplex ![1, 0]) 1e-30 := by
  unique_root_near !![1/6, 0; 0, 1/6]

end DegSix

end
