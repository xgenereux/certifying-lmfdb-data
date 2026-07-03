import CertifyingLmfdbData.Polynomial.AllRoots
import CertifyingLmfdbData.SexticExampleHyp

noncomputable section

open NumberField Algebra IntermediateField Polynomial

open DegSix

theorem exists_torsion_eq_mul {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0)
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

theorem two_dvd_torsion : 2 ∣ NumberField.Units.torsionOrder (AdjoinRoot DegSix.myPoly) :=
    exists_torsion_eq_mul (n := 2) (by lia) (ζ := -1) (by simp) <| fun m hm hm₂ ↦ by
  have := Nat.le_of_dvd (show 0 < 2 by lia) hm
  interval_cases m <;> simp_all [Ring.neg_one_ne_one_of_char_ne_two]

end
