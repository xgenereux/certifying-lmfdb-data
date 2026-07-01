module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] [NumberField K]

/-- This result is lifted from a more recent version of Mathlib. If the
version of Mathlib of this repo is updated, we should delete this lemma
and use the version in Mathlib. -/
lemma not_dvd_discr_iff_isUnramifiedIn {𝒪 : Type*} [CommRing 𝒪] [Algebra 𝒪 K]
    [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    ¬ p ∣ discr K ↔ Algebra.IsUnramifiedIn 𝒪 (Ideal.span {p}) := by
  have := (IsIntegralClosure.algebraMap_injective 𝒪 ℤ K).isDomain
  have := IsIntegralClosure.isDedekindDomain ℤ ℚ K 𝒪
  have := CharZero.of_module (R := 𝒪) K
  rw [not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  exact (Algebra.isUnramifiedIn_iff_forall_of_isDedekindDomain'
    (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)).symm

open IntermediateField in
/--
If the prime ideal `P` is unramified over `ℤ` and the norm of the prime of `ℤ` lying under `P` is
greater than `2`, then the map `Ideal.torsionMapQuot` is injective.
-/
theorem Ideal.torsionMapQuot_injective' {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : 2 < absNorm (under ℤ P)) :
    Function.Injective P.torsionMapQuot := by
  have : NeZero P := ⟨fun h ↦ by simp [h] at hP₂⟩
  rw [injective_iff_map_eq_one]
  by_contra!
  obtain ⟨⟨ζ, hζ₀⟩, hζ₁, hζ₂⟩ := this
  obtain ⟨n, hn, hζ₃⟩ : ∃ n, 2 ≤ n ∧ IsPrimitiveRoot (ζ : K) n := by
    refine ⟨orderOf ζ, ?_, IsPrimitiveRoot.coe_coe_iff.mpr (IsPrimitiveRoot.orderOf ζ)⟩
    rw [Nat.two_le_iff, orderOf_ne_zero_iff]
    exact ⟨hζ₀, by simpa using hζ₂⟩
  have h_cpr := hζ₃.not_coprime_norm_of_mk_eq_one
    (absNorm_eq_one_iff.not.mpr <| IsPrime.ne_top hP) hn
    (by rwa [Units.ext_iff, torsionMapQuot_apply, val_one] at hζ₁)
  let p := (Ideal.under ℤ P).absNorm
  have hp := Nat.absNorm_under_prime P
  have : Fact p.Prime := ⟨hp⟩
  rw [P.absNorm_eq_pow_inertiaDeg' hp, Nat.coprime_pow_left_iff (Ideal.inertiaDeg_pos _ _),
    ← Nat.Prime.dvd_iff_not_coprime hp] at h_cpr
  obtain ⟨c, hc⟩ := h_cpr
  have hζ_pow := IsPrimitiveRoot.pow (by grind) hζ₃ (by rwa [mul_comm])
  let F := ℚ⟮(ζ : K) ^ c⟯
  have : IsCyclotomicExtension {p} ℚ F :=
    hζ_pow.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices 1 < P.ramificationIdx' ℤ by
    rwa [P.ramificationIdx'_eq_one ℤ, lt_self_iff_false] at this
  rw [Ideal.ramificationIdx'_tower (P.under (𝓞 F)) P,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F]
  exact one_lt_mul_of_lt_of_le (by rwa [Nat.lt_sub_iff_add_lt']) <| P.ramificationIdx'_pos (𝓞 F)

/--
Assume that the prime `p` is odd and does not divide the discriminant of `K` then,
for any prime ideal `P` of `K` above `p`, `torsionOrder K` divides `N P - 1`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one' {p : ℕ} (hp₀ : p.Prime)
    (hp₁ : Odd p) (hp₂ : ¬ p ∣ (discr K).natAbs) {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    [hPp : P.LiesOver (span {(p : ℤ)})] :
    torsionOrder K ∣ absNorm P - 1 := by
  have hP₀ : P ≠ ⊥ :=
    ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)}) (by simpa using hp₀.ne_zero) P
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP
  let _ := Ideal.Quotient.field P
  have hP₁ :  Algebra.IsUnramifiedAt ℤ P := by
    rw [← Int.natCast_dvd, not_dvd_discr_iff_isUnramifiedIn (𝒪 := 𝓞 K)
      (Nat.prime_iff_prime_int.mp hp₀)] at hp₂
    exact hp₂ P hP hPp
  have hP₂ : 2 < absNorm (under ℤ P) := by
    rw [← (liesOver_iff _ _).mp hPp, absNorm_span_singleton, Algebra.norm_self,
      MonoidHom.id_apply, Int.natAbs_natCast]
    rw [hp₀.odd_iff] at hp₁
    linarith
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective' hP₁ hP₂)
  rwa [Nat.card_eq_fintype_card, Nat.card_units] at h
