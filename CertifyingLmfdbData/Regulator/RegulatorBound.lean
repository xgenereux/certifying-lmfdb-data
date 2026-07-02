import Mathlib

open NumberField Algebra IntermediateField Polynomial

section

variable {K : Type*} [Field K] [NumberField K]

open Classical in
lemma NumberField.Units.exists_regOfFamily_eq_mul
    {u : Fin (rank K) → (𝓞 K)ˣ} (hu : regOfFamily u ≠ 0) :
    ∃ m : ℕ, m ≠ 0 ∧ regOfFamily u = m * regulator K := by
  have := regulator_pos K
  have key : regOfFamily u = ↑(Subgroup.closure (Set.range u) ⊔ torsion K).index * regulator K := by
    have := regOfFamily_div_regulator u
    field_simp at ⊢ this
    exact this
  exact ⟨(Subgroup.closure (Set.range u) ⊔ torsion K).index, fun _ ↦ by simp_all, key⟩

theorem exists_torsion_eq_mul {n : ℕ} (hn : n ≠ 0)
    {ζ : 𝓞 K} (hζ : ζ ^ n = 1) (hζ₂ : ∀ m, m ∣ n → m ≠ n → ζ ^ m ≠ 1) :
    n ∣ NumberField.Units.torsionOrder K := by
  have : NeZero n := ⟨hn⟩
  have horder : orderOf ζ = n := by
    by_contra hne
    exact hζ₂ (orderOf ζ) (orderOf_dvd_of_pow_eq_one hζ) hne (pow_orderOf_eq_one ζ)
  have hprim : IsPrimitiveRoot ζ n := by
    simpa [horder] using (IsPrimitiveRoot.orderOf ζ)
  exact NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot
    (hprim.map_of_injective RingOfIntegers.coe_injective)

end

section

variable {n m : ℕ} {f : ℚ[X]} [hf : Fact (Irreducible f)]
         (hn : n = Module.finrank (AdjoinRoot f))
         (hm : m = NumberField.Units.rank (AdjoinRoot f))
         {α : Fin m → ℂ} {t : Fin m → ℕ}
         (hα : ∀ i, f.aeval (α i) = 0)
         (hα₂ : ∀ i, 0 ≤ (α i).im)
         (hα₃ : ∀ i j, i ≠ j → α i ≠ α j)
         (h_t : ∀ i, ((α i).im = 0 → t i = 1) ∧ ((α i).im ≠ 0 → t i = 2))
         {u : Fin m → ℚ[X]}
         (hu : ∀ i, ∃ h : IsIntegral ℤ ((u i).aeval (AdjoinRoot.root f)),
            IsUnit (⟨_, h⟩ : 𝓞 (AdjoinRoot f)))

-- AI generated, not thought about
include hα hα₂ hα₃ h_t in
theorem regOfFamily_comp_eq_regOfFamily :
    |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖).det| =
    NumberField.Units.regOfFamily (fun i ↦ (hu (finCongr hm.symm i)).2.unit) := by
  classical
  let v : Fin m → (𝓞 (AdjoinRoot f))ˣ := fun i ↦ (hu i).2.unit
  have hv (j : Fin m) :
      (v j : AdjoinRoot f) =
        (u j).aeval (AdjoinRoot.root f) := by
    exact congrArg (fun x : 𝓞 (AdjoinRoot f) ↦ (x : AdjoinRoot f)) (hu j).2.unit_spec
  have hroot (i : Fin m) :
      AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (AdjoinRoot.root f) = α i := by
    rw [AdjoinRoot.lift_root]
  have hlift_aeval (i j : Fin m) :
      AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i)
          ((u j).aeval (AdjoinRoot.root f)) =
        (u j).aeval (α i) := by
    simpa [AdjoinRoot.coe_liftAlgHom] using
      (Polynomial.aeval_algHom_apply
        (AdjoinRoot.liftAlgHom f (Algebra.ofId ℚ ℂ) (α i) (hα i))
        (AdjoinRoot.root f) (u j)).symm
  have hfake :
      |(Matrix.of fun i j ↦ t i * Real.log ‖(u j).aeval (α i)‖).det| =
        |(Matrix.of fun i j ↦
          t i * Real.log ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (v j)‖).det| := by
    congr
    ext i j
    simp [hv j, hlift_aeval i j]
  let placeOfRoot : Fin m → InfinitePlace (AdjoinRoot f) := fun i ↦
    InfinitePlace.mk (AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i))
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
  have h_t' : ∀ i, t i = (placeEquiv i).1.mult := by
    intro i
    rw [← h_place i]
    unfold placeOfRoot
    rw [InfinitePlace.mult]
    by_cases hi : (α i).im = 0
    · rw [if_pos]
      · exact (h_t i).1 hi
      · rw [InfinitePlace.isReal_mk_iff]
        exact (hreal_iff i).mpr hi
    · rw [if_neg]
      · exact (h_t i).2 hi
      · rw [InfinitePlace.isReal_mk_iff]
        exact mt (hreal_iff i).mp hi
  let eRank : {w : InfinitePlace (AdjoinRoot f) // w ≠ w'} ≃
      Fin (NumberField.Units.rank (AdjoinRoot f)) :=
    placeEquiv.symm.trans (finCongr hm)
  let M : Matrix {w : InfinitePlace (AdjoinRoot f) // w ≠ w'}
      {w : InfinitePlace (AdjoinRoot f) // w ≠ w'} ℝ :=
    Matrix.of fun i w ↦
      (w.1.mult : ℝ) * Real.log (w.1 ((v (finCongr hm.symm (eRank i)) :
        (𝓞 (AdjoinRoot f))ˣ) : AdjoinRoot f))
  have hnorm (i j : Fin m) :
      (placeEquiv i).1 (v j : AdjoinRoot f) =
        ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α i) (hα i) (v j)‖ := by
    simpa [placeOfRoot, InfinitePlace.apply] using congrArg
      (fun w : InfinitePlace (AdjoinRoot f) ↦ w (v j : AdjoinRoot f)) (h_place i).symm
  have hM :
      M.reindex placeEquiv.symm placeEquiv.symm =
        Matrix.of (fun i j : Fin m ↦
          t j * Real.log ‖AdjoinRoot.lift (algebraMap ℚ ℂ) (α j) (hα j) (v i)‖) := by
    ext i j
    simp [M, eRank, h_t' j, hnorm j i]
  have hdetM : |M.det| =
      |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖).det| := by
    rw [← Matrix.det_reindex_self placeEquiv.symm M, hM]
    simp [hv, hlift_aeval]
  rw [← hdetM]
  simpa [M, v] using
    (NumberField.Units.regOfFamily_eq_det (fun i ↦ v (finCongr hm.symm i)) w' eRank).symm

include hm hα hα₂ hα₃ h_t hu in
theorem regulator_le_regOfFamily_comp (bound : ℝ) (bound_nonz : bound ≠ 0)
    (h_bound : bound =
        |(Matrix.of fun i j ↦ t j * Real.log ‖(u i).aeval (α j)‖).det|) :
    ∃ m : ℕ, m ≠ 0 ∧ bound = m * NumberField.Units.regulator (AdjoinRoot f) := by
  subst h_bound
  rw [regOfFamily_comp_eq_regOfFamily hm hα hα₂ hα₃ h_t hu] at *
  exact NumberField.Units.exists_regOfFamily_eq_mul bound_nonz

end
