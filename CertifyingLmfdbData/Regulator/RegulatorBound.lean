import Mathlib

variable {K : Type*} [Field K] [NumberField K]

open NumberField Algebra IntermediateField Polynomial

open Classical in
lemma NumberField.Units.regulator_le_regOfFamily
    (u : Fin (rank K) → (𝓞 K)ˣ) (hu : regOfFamily u ≠ 0) :
    regulator K ≤ regOfFamily u := by
  have := regulator_pos K
  have := regOfFamily_div_regulator u
  field_simp at this
  rw [this]
  have hindex_one :
      (1 : ℝ) ≤ ((Subgroup.closure (Set.range u) ⊔ torsion K).index : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun _ ↦ by simp_all))
  nlinarith

variable {n m : ℕ} {f : ℚ[X]} [hf : Fact (Irreducible f)]
         (hn : n = Module.finrank (AdjoinRoot f)) (hm : m = NumberField.Units.rank (AdjoinRoot f))
         {α : Fin m → ℂ} {type : Fin m → ℕ}
         (hα : ∀ i, f.aeval (α i) = 0)
         (hα₂ : ∀ i, 0 ≤ (α i).im)
         (hα₃ : ∀ i j, i ≠ j → α i ≠ α j)
         (h_type : ∀ i, ((α i).im = 0 → type i = 1) ∧ ((α i).im ≠ 0 → type i = 2))
         {u : Fin m → 𝓞 (AdjoinRoot f)}
         {u_inv : Fin m → 𝓞 (AdjoinRoot f)}
         (hu_inv : ∀ i, u i * u_inv i = 1)

variable (type u) in
noncomputable def fake_regulator :=
  |(Matrix.of fun i j ↦
    type i * Real.log ‖(AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (u j))‖).det|

noncomputable def u_to_numberfield :
    Fin (NumberField.Units.rank (AdjoinRoot f)) → (𝓞 (AdjoinRoot f))ˣ :=
  (fun i ↦ ⟨u (finCongr hm.symm i), u_inv (finCongr hm.symm i), hu_inv (finCongr hm.symm i),
              by rw [mul_comm]; exact hu_inv (finCongr hm.symm i)⟩)

-- AI generated and not edited
include hα₂ hα₃ h_type in
theorem fake_regulator_eq_regOfFamily :
    fake_regulator type hα u = NumberField.Units.regOfFamily (u_to_numberfield hm hu_inv) := by
  classical
  let placeOfRoot : Fin m → InfinitePlace (AdjoinRoot f) := fun i ↦
    InfinitePlace.mk (AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i))
  have hroot (i : Fin m) :
      AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (AdjoinRoot.root f) = α i := by
    rw [AdjoinRoot.lift_root]
  have hreal_iff (i : Fin m) :
      ComplexEmbedding.IsReal (AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i)) ↔
        (α i).im = 0 := by
    constructor
    · intro hreal
      rw [← Complex.conj_eq_iff_im]
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hroot i] using
        RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hreal) (AdjoinRoot.root f)
    · intro him
      rw [ComplexEmbedding.isReal_iff]
      apply RingHom.ext
      intro x
      exact AdjoinRoot.induction_on (f := f) x fun p ↦ by
        have hstar : (starRingEnd ℂ) (α i) = α i := by
          simpa [Complex.star_def] using Complex.conj_eq_iff_im.mpr him
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq, AdjoinRoot.lift_mk,
          Polynomial.hom_eval₂]
        have hcomp : (starRingEnd ℂ).comp (algebraMap ℚ ℂ) = algebraMap ℚ ℂ := by
          ext q
          simp
        rw [hcomp, hstar]
  have hplace_inj : Function.Injective placeOfRoot := by
    intro i j hij
    by_contra hne
    have hsame : α i = α j := by
      rcases InfinitePlace.mk_eq_iff.mp hij with heq | hconj
      · simpa [hroot i, hroot j] using
          RingHom.congr_fun heq (AdjoinRoot.root f)
      · have hc : (starRingEnd ℂ) (α i) = α j := by
          simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hroot i, hroot j] using
            RingHom.congr_fun hconj (AdjoinRoot.root f)
        have him : (α i).im = 0 := by
          have him' : -(α i).im = (α j).im := by
            simpa [Complex.star_def, Complex.conj_im] using congrArg Complex.im hc
          linarith [hα₂ i, hα₂ j]
        have hstar : (starRingEnd ℂ) (α i) = α i := by
          simpa [Complex.star_def] using Complex.conj_eq_iff_im.mpr him
        exact hstar.symm.trans hc
    exact hα₃ i j hne hsame
  let placeEmbedding : Fin m ↪ InfinitePlace (AdjoinRoot f) :=
    ⟨placeOfRoot, hplace_inj⟩
  have hcard_places : Fintype.card (InfinitePlace (AdjoinRoot f)) = m + 1 := by
    have hpos : 0 < Fintype.card (InfinitePlace (AdjoinRoot f)) :=
      Fintype.card_pos_iff.mpr inferInstance
    rw [hm, NumberField.Units.rank]
    omega
  have hcard_compl :
      Fintype.card {w : InfinitePlace (AdjoinRoot f) // w ∉ Set.range placeEmbedding} = 1 := by
    change Fintype.card (↑(Set.range placeEmbedding)ᶜ : Sort _) = 1
    rw [Fintype.card_compl_set, Fintype.card_range, Fintype.card_fin, hcard_places]
    omega
  obtain ⟨wCompl, hwCompl⟩ := Fintype.card_eq_one_iff.mp hcard_compl
  let w' : InfinitePlace (AdjoinRoot f) := wCompl
  have hw'_not_mem : w' ∉ Set.range placeEmbedding := wCompl.2
  have hrange_eq : Set.range placeEmbedding = ({w'}ᶜ : Set (InfinitePlace (AdjoinRoot f))) := by
    ext w
    constructor
    · intro hw
      exact fun hw_eq ↦ hw'_not_mem (hw_eq ▸ hw)
    · intro hw
      by_contra hnot
      have hsub : (⟨w, hnot⟩ : {w : InfinitePlace (AdjoinRoot f) //
          w ∉ Set.range placeEmbedding}) = wCompl := hwCompl _
      exact hw (Subtype.ext_iff.mp hsub)
  let placeEquiv : Fin m ≃ {w : InfinitePlace (AdjoinRoot f) // w ≠ w'} :=
    placeEmbedding.toEquivRange.trans (Equiv.setCongr hrange_eq)
  have h_place : ∀ i, placeOfRoot i = (placeEquiv i).1 := by
    intro i
    change placeOfRoot i =
      ((Equiv.setCongr hrange_eq) ⟨placeEmbedding i, Set.mem_range_self i⟩).1
    rfl
  have h_type' : ∀ i, type i = (placeEquiv i).1.mult := by
    intro i
    rw [← h_place i]
    unfold placeOfRoot
    rw [InfinitePlace.mult]
    by_cases hi : (α i).im = 0
    · rw [if_pos]
      · exact (h_type i).1 hi
      · rw [InfinitePlace.isReal_mk_iff]
        exact (hreal_iff i).mpr hi
    · rw [if_neg]
      · exact (h_type i).2 hi
      · rw [InfinitePlace.isReal_mk_iff]
        exact mt (hreal_iff i).mp hi
  let eRank : {w : InfinitePlace (AdjoinRoot f) // w ≠ w'} ≃
      Fin (NumberField.Units.rank (AdjoinRoot f)) :=
    placeEquiv.symm.trans (finCongr hm)
  let M : Matrix {w : InfinitePlace (AdjoinRoot f) // w ≠ w'}
      {w : InfinitePlace (AdjoinRoot f) // w ≠ w'} ℝ :=
    Matrix.of fun i w ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((u_to_numberfield hm hu_inv (eRank i) :
        (𝓞 (AdjoinRoot f))ˣ) : AdjoinRoot f))
  have hnorm (i j : Fin m) :
      (placeEquiv i).1 (u j : AdjoinRoot f) =
        ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (u j)‖ := by
    simpa [placeOfRoot, InfinitePlace.apply] using congrArg
      (fun w : InfinitePlace (AdjoinRoot f) ↦ w (u j : AdjoinRoot f)) (h_place i).symm
  have hM :
      M.reindex placeEquiv.symm placeEquiv.symm =
        Matrix.of (fun i j : Fin m ↦
          type j * Real.log ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α j) (hα j) (u i)‖) := by
    ext i j
    simp [M, eRank, u_to_numberfield, h_type' j, hnorm j i]
  have hdetM : |M.det| = fake_regulator type hα u := by
    rw [← Matrix.det_reindex_self placeEquiv.symm M, hM]
    change |(Matrix.transpose (Matrix.of fun i j : Fin m ↦
      type i * Real.log ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (u j)‖)).det| =
        fake_regulator type hα u
    rw [Matrix.det_transpose]
    rfl
  simpa [NumberField.Units.regOfFamily_eq_det (u_to_numberfield hm hu_inv) w' eRank] using
    hdetM.symm

include hm hu_inv hα₂ hα₃ h_type in
theorem regulator_le_fake_regulator
    (h_nonzero : fake_regulator type hα u ≠ 0) :
    NumberField.Units.regulator (AdjoinRoot f) ≤ fake_regulator type hα u := by
  rw [fake_regulator_eq_regOfFamily (hm := hm) (hα := hα) (hα₂ := hα₂)
    (hα₃ := hα₃) (h_type := h_type) (hu_inv := hu_inv)] at *
  exact NumberField.Units.regulator_le_regOfFamily _ h_nonzero

noncomputable def vec_to_poly (u : Fin n → ℚ) : ℚ[X] :=
  { toFinsupp := Finsupp.mapDomain Fin.val u }

variable {n m : ℕ} {f : ℚ[X]} [hf : Fact (Irreducible f)]
         (hn : n = Module.finrank (AdjoinRoot f))
         (hm : m = NumberField.Units.rank (AdjoinRoot f))
         {α : Fin m → ℂ} {type : Fin m → ℕ}
         (hα : ∀ i, f.aeval (α i) = 0)
         (hα₂ : ∀ i, 0 ≤ (α i).im)
         (hα₃ : ∀ i j, i ≠ j → α i ≠ α j)
         (h_type : ∀ i, ((α i).im = 0 → type i = 1) ∧ ((α i).im ≠ 0 → type i = 2))
         {u : Fin m → (Fin n → ℚ)}
         (hu : ∀ i, ∃ h : IsIntegral ℤ (vec_to_poly (u i)).aeval (AdjoinRoot.root f),
            IsUnit (⟨_, h⟩ : 𝓞 (AdjoinRoot f)))

variable (type u) in
noncomputable def fake_regulator' :=
  |(Matrix.of fun i j ↦
    type i * Real.log ‖(vec_to_poly (u j)).aeval α‖).det|
