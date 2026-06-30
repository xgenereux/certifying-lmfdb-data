-- import Matlib.ForMathlib.SumFin
-- import Matlib.Banach
-- import Matlib.PowerSeries
-- import Matlib.Tactic
import CertifyingLmfdbData.Polynomial.NewtonKantorovich
import Mathlib
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Complex
universe u z

open Qq in
simproc_decl Complex.I_pow_eq_pow_mod' (Complex.I ^ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(ℂ), ~q(Complex.I ^ $n) => do
    let some n' := Lean.Expr.nat? n | return .continue
    if n' < 4 then return .continue
    return .visit <| .mk q(I ^ ($n % 4)) <| .some q(Complex.I_pow_eq_pow_mod $n)

@[simp] theorem Polynomial.aeval_ofNat {R : Type u} {A : Type z}
    [CommSemiring R] [Semiring A] [Algebra R A] (x : A) (n : ℕ) [n.AtLeastTwo] :
    (aeval x) (ofNat(n) : R[X]) = ofNat(n) :=
  Polynomial.aeval_natCast (R := R) x n

noncomputable def toComplex : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow _ _).trans Complex.equivRealProdCLM.symm

set_option autoImplicit true

@[simp] lemma toComplex_apply : toComplex h = h 0 + h 1 * I := by
  simp [toComplex, Complex.equivRealProdCLM_symm_apply]

@[simp] lemma toComplex_symm_apply : toComplex.symm z = ![z.re, z.im] := by
  simp [toComplex]

lemma hasFDerivAt_toComplex : HasFDerivAt (𝕜 := ℝ) toComplex toComplex x :=
  toComplex.hasFDerivAt

lemma hasFDerivAt_toComplex_symm : HasFDerivAt (𝕜 := ℝ) toComplex.symm toComplex.symm x :=
  toComplex.symm.hasFDerivAt

noncomputable def polyToZeroFinder (p : Polynomial ℚ) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  toComplex.symm ∘ (p.aeval ·) ∘ toComplex

noncomputable def polyToZeroFinderDeriv (p : Polynomial ℚ) (v : Fin 2 → ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
    ((ContinuousLinearMap.mul ℝ ℂ (p.derivative.aeval (toComplex v))).comp
      (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ))

lemma polyToZeroFinderDeriv_sub {p v₁ v₂} :
    polyToZeroFinderDeriv p v₁ - polyToZeroFinderDeriv p v₂ =
      (toComplex.symm : ℂ →L[ℝ] (Fin 2 → ℝ)).comp
        ((ContinuousLinearMap.mul ℝ ℂ
          (p.derivative.aeval (toComplex v₁) - p.derivative.aeval (toComplex v₂))).comp
          (toComplex : (Fin 2 → ℝ) →L[ℝ] ℂ)) := by
  simp [polyToZeroFinderDeriv]

lemma continuous_polyToZeroFinderDeriv : Continuous (polyToZeroFinderDeriv p) := by
  delta polyToZeroFinderDeriv
  fun_prop

lemma hasFDerivAt_polyToZeroFinder :
    HasFDerivAt (𝕜 := ℝ) (polyToZeroFinder p) (polyToZeroFinderDeriv p x) x := by
  refine HasFDerivAt.comp (𝕜 := ℝ) (g := toComplex.symm) _ hasFDerivAt_toComplex_symm
    (HasFDerivAt.comp (𝕜 := ℝ) _ ?_ hasFDerivAt_toComplex)
  convert (p.hasFDerivAt_aeval (toComplex x)).restrictScalars ℝ
  ext y
  simp [mul_comm]

lemma opNorm_mul {x : ℂ} :
    ‖ContinuousLinearMap.mul ℝ ℂ x‖ = ‖x‖ := by
  simp only [ContinuousLinearMap.opNorm_mul_apply]

lemma lipschitzOnWith_derivZeroFinder {x₀ : Fin 2 → ℝ} {R : NNReal} {p} :
    LipschitzOnWith K (polyToZeroFinderDeriv p) (Metric.closedBall x₀ R) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x hx y hy
  simp only [polyToZeroFinderDeriv_sub]
  grw [ContinuousLinearMap.opNorm_comp_le]
  grw [ContinuousLinearMap.opNorm_comp_le]
  simp only [ContinuousLinearMap.opNorm_mul_apply]
  sorry

@[simp] lemma polyToZeroFinderDeriv_apply_one_zero :
    polyToZeroFinderDeriv p v ![1, 0] =
      ![((aeval (v 0 + v 1 * I)) (derivative p)).re,
        ((aeval (v 0 + v 1 * I)) (derivative p)).im] := by
  simp [polyToZeroFinderDeriv]

@[simp] lemma polyToZeroFinderDeriv_apply_zero_one :
    polyToZeroFinderDeriv p v ![0, 1] =
      ![-((aeval (v 0 + v 1 * I)) (derivative p)).im,
        ((aeval (v 0 + v 1 * I)) (derivative p)).re] := by
  simp [polyToZeroFinderDeriv]

macro "reducePoly" : tactic =>
  `(tactic| {
    simp only [polyToZeroFinder, pow_succ, pow_zero, one_mul, map_add, map_mul, aeval_X, map_one,
      Function.comp_apply, toComplex_apply, Fin.isValue, toComplex_symm_apply, Nat.succ_eq_add_one,
      Nat.reduceAdd, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, one_re, one_im, aeval_ofNat,
      and_true, Fin.isValue, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons,
      zero_add, Matrix.empty_add_empty, Matrix.vecCons_inj, add_left_inj]
    ring_nf
    constructor <;> trivial
    })

noncomputable def myPoly : Polynomial ℚ := X ^ 5 + X + 1

noncomputable def myPolyDeriv : Polynomial ℚ := 5 * X ^ 4 + 1

def zeroFinder : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x ↦
  ![x 0 ^ 5 - 10 * x 0 ^ 3 * x 1 ^ 2 + 5 * x 0 * x 1 ^ 4 + x 0 + 1,
    5 * x 0 ^ 4 * x 1 - 10 * x 0 ^ 2 * x 1 ^ 3 + x 1 ^ 5 + x 1]

lemma polyToZeroFinder_myPoly : polyToZeroFinder myPoly = zeroFinder := by
  ext x : 1
  simp only [myPoly, zeroFinder]
  reducePoly

lemma myPoly_derivative : myPoly.derivative = myPolyDeriv := by
  norm_num [myPoly, myPolyDeriv, C_ofNat]

noncomputable def derivZeroFinder (v : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    polyToZeroFinderDeriv myPoly v


-- #exit

def v : Fin 2 → ℝ := ![0.877438833123346, -0.744861766619744]

def A_mat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-0.11915000248755223,  -0.045813378411717155;
      0.045813378411717155, -0.11915000248755223]

noncomputable def A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap <| Matrix.mulVecLin A_mat

lemma y : ‖A (polyToZeroFinder myPoly v)‖₊ ≤ 1e-15 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, pi_norm_le_iff_of_nonempty]
  simp only [polyToZeroFinder_myPoly]
  simp only [A, A_mat, zeroFinder, v]
  norm_num

-- TODO: does `Module.Basis.opNorm_le` really require CompleteSpace?
theorem opNorm_le_of_basisFun {ι 𝕜 F : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace 𝕜]
    {u : (ι → 𝕜) →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (Pi.basisFun 𝕜 ι i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • M := by
  convert (Module.Basis.opNorm_le (Pi.basisFun 𝕜 ι) (u := u) hM hu).trans ?_
  suffices (Pi.basisFun 𝕜 ι).equivFunL = ContinuousLinearMap.id 𝕜 (ι → 𝕜) by
    grw [this, ContinuousLinearMap.norm_id_le]
    simp
  ext v i
  simp

@[simp] lemma Pi.single_fin_two_zero {x : ℝ} : Pi.single 0 x = ![x, 0] := funext <| by simp
@[simp] lemma Pi.single_fin_two_one {x : ℝ} : Pi.single 1 x = ![0, x] := funext <| by simp
example {x : ℝ} : Pi.single 0 x = ![x, 0, 0] := funext <| by simp [Fin.forall_fin_succ]
example {x : ℝ} : Pi.single 1 x = ![0, x, 0] := funext <| by simp [Fin.forall_fin_succ]
example {x : ℝ} : Pi.single 2 x = ![0, 0, x] := funext <| by simp [Fin.forall_fin_succ]

lemma z₁ : ‖1 - A.comp (derivZeroFinder v)‖₊ ≤ 1e-11 := by
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 5e-12) (by norm_num) ?h1).trans (by norm_num)
  simp [myPoly_derivative, myPolyDeriv, pow_succ, v, A, A_mat, pi_norm_le_iff_of_nonempty]
  norm_num

open NNReal

lemma temp (x v u : Fin 2 → ℝ) (hu : u = x - v) (h : x ∈ Metric.closedEBall v 2) :
    -2 ≤ u 0 ∧ u 0 ≤ 2 ∧
    -2 ≤ u 1 ∧ u 1 ≤ 2 := by
  have : ∀ i, x i = u i + v i := by
    simp [hu]
  have : edist x v = max (edist (x 0) (v 0)) (edist (x 1) (v 1)) := by
    simp [edist, Finset.univ_fin2]
  simp [this, edist_dist, Real.dist_eq, abs_le] at h
  grind


/-
A * (F' x - F' v)
-/

#check opNorm_le_of_basisFun

set_option maxHeartbeats 10000000000000 in
lemma z₂ (x) (hx : x ∈ Metric.closedEBall v 2) :
    ‖A.comp (derivZeroFinder x - derivZeroFinder v)‖₊ ≤ 400 * ‖x - v‖₊ := by
  stop
  simp only [← NNReal.coe_le_coe, coe_nnnorm, derivZeroFinder]
  apply (opNorm_le_of_basisFun (M := 200 * ‖x - v‖₊) (by positivity) ?h1).trans
    (by simp; linarith [norm_nonneg (x - v)])
  set! u := x - v with hu
  simp [← hu]
  have : ∀ i, x i = u i + v i := by
    simp [hu]
  simp [this]
  simp [myPoly_derivative, myPolyDeriv, pow_succ, v, A, A_mat, pi_norm_le_iff_of_nonempty, Matrix.vecHead, Matrix.vecTail]
  -- norm_num
  ring_nf
  repeat grw [abs_add_le]
  simp only [Fin.isValue, abs_mul, abs_pow, -sq_abs]
  have hu0 : |u 0| ≤ 2 := sorry
  have hu1 : |u 1| ≤ 2 := sorry
  norm_num
  grw [hu0, hu1]
  sorry

  -- simp  only [abs_le]
  -- have hnormu : ‖u‖ ≤ 2 := sorry
  -- have : 0 ≤ ‖u‖  := by grind
  -- obtain ⟨hu0l, hu0r, hu1l, hu1r⟩ := temp _ _ _ hu hx
  -- -- grewrite (config := {newGoals := .nonDependentOnly}) [← hu0l]
  -- have : -‖u‖ ≤ u 0 := sorry
  -- have : u 0 ≤ ‖u‖ := sorry
  -- have : -‖u‖ ≤ u 1 := sorry
  -- have : u 1 ≤ ‖u‖ := sorry
  -- have h1 : 0 ≤ u 0 ^ 2 := by nlinarith
  -- have h2 : -2*‖u‖ ≤ u 0 * u 1 := by nlinarith
  -- have h3 : 0 ≤ u 1 ^ 2 := by nlinarith
  -- have h4 : u 0 ^ 2 ≤ 2 * ‖u‖ := by nlinarith
  -- have : u 0 * u 1 ≤ 2*‖u‖ := by nlinarith
  -- have : u 1 ^ 2 ≤ 2*‖u‖ := by nlinarith
  -- have : -4 * ‖u‖ ≤ u 0 ^ 3 := by nlinarith
  -- have : -4 * ‖u‖ ≤ u 0 ^ 2 * u 1 := by nlinarith
  -- have : -4 * ‖u‖ ≤ u 0 * u 1 ^ 2 := by nlinarith
  -- have : -4 * ‖u‖ ≤ u 1 ^ 3 := by nlinarith
  -- have :  u 0 ^ 3 ≤ 4 * ‖u‖ := by nlinarith
  -- have :  u 0 ^ 2 * u 1 ≤ 4 * ‖u‖ := by nlinarith
  -- have :  u 0 * u 1 ^ 2 ≤ 4 * ‖u‖ := by nlinarith
  -- have :  u 1 ^ 3 ≤ 4 * ‖u‖ := by nlinarith
  -- have : 0 ≤ u 0 ^ 4 := by nlinarith
  -- have : -8 * ‖u‖ ≤ u 0 ^ 3 * u 1 := by nlinarith
  -- have : 0 ≤ u 0 ^ 2 * u 1 ^ 2 := by nlinarith
  -- have : -8 * ‖u‖ ≤ u 0 * u 1 ^ 3 := by nlinarith
  -- have h19 : 0 ≤ u 1 ^ 4 := by nlinarith
  -- have h20 : u 0 ^ 4 ≤ 8 * ‖u‖ := by nlinarith
  -- have h21 : u 0 ^ 3 * u 1 ≤ 8 * ‖u‖ := by nlinarith
  -- have h22 : u 0 ^ 2 * u 1 ^ 2 ≤ 8 * ‖u‖ := by nlinarith
  -- have h23 : u 0 * u 1 ^ 3 ≤ 8 * ‖u‖ := by nlinarith
  -- have h24 : u 1 ^ 4 ≤ 8 * ‖u‖ := by nlinarith
  -- refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  -- · linarith
  -- · linarith
  -- · linarith
  -- · linarith
  -- · linarith
  -- · linarith
  -- · linarith
  -- · linarith

lemma test : False := by
  have := newton_kantorovich_fd
    (F := polyToZeroFinder myPoly)
    (DF := derivZeroFinder)
    (by simp)
    (fun x ↦ hasFDerivAt_polyToZeroFinder)
    continuous_polyToZeroFinderDeriv
    (x₀ := v)
    (A := A)
    (z₂ := 100)
    (R := 2)
    (r := 0.0001)
    y z₁ sorry (by sorry) (by apply le_of_lt; norm_num) (by norm_num)
  -- have : (1 : ℝ) * 2⁻¹ ≤ 3 := by? norm_num
  sorry


-- #check newton_kantorovich hasFDerivAt_zeroFinder (by fun_prop)
