import IdealArithmetic.Examples.NF6_4_19208000_1.Results6_4_19208000_1
import CertifyingLmfdbData.Polynomial.AllRoots

open Polynomial

open DegSix NumberField

noncomputable section

noncomputable def f := map (algebraMap ℤ ℚ) T

lemma B_apply' (i : Fin 6) : (B i : K) =
  (Adj.map) (Polynomial.C 25⁻¹ * map (Int.castRingHom ℚ)
    (ofList (List.ofFn (![![25, 0, 0, 0, 0, 0], ![0, 25, 0, 0, 0, 0],
    ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]] i)))) := by
  erw [basisOfBuilderLists_apply]
  unfold BQ
  rfl

def unit1 := B.equivFun.symm ![-2, 0, 0, 0, 1, 0]

def unit2 := B.equivFun.symm ![-1, 0, 0, 0, 1, 0]

def unit3 := B.equivFun.symm ![3, -2, 0, 0, -2, 1]

def unit4 := B.equivFun.symm ![-2, -2, -1, 0, 0, 1]

lemma isUnit_unit1 : IsUnit unit1 := by
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1, 0, 1, 0, 0, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_unit2 : IsUnit unit2 := by
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1, 0, -1, 0, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_unit3 : IsUnit unit3 := by
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6, -4, -1, -1, 3, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_unit4 : IsUnit unit4 := by
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3, -1, -1, -1, -3, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma unit1_poly : (unit1 : K) = Adj.map (C (1/25) * X^4 - C 2) := by
  unfold unit1
  erw [basisOfBuilderLists_apply_Fn]
  unfold BQ
  congr
  simp [Fin.sum_univ_castSucc]
  ring_nf
  have aux1 : (2 : ℚ) = 50 * (1 / 25) := by norm_num
  have aux2 : Polynomial.C (50 : ℚ) = 50 := rfl
  rw [aux1]
  simp only [one_div, map_mul]
  rw [aux2]
  ring

lemma unit2_poly : (unit2 : K) = Adj.map (C (1/25) * X^4 - C 1) := by
  unfold unit2
  erw [basisOfBuilderLists_apply_Fn]
  unfold BQ
  congr
  simp [Fin.sum_univ_castSucc]
  ring_nf
  have aux1 : (1 : ℚ) = 25 * (1 / 25) := by norm_num
  have aux2 : Polynomial.C (25 : ℚ) = 25 := rfl
  rw [ aux1]
  simp only [one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, add_left_inj,
    neg_inj]
  rw [← aux2, ← map_mul]
  simp

lemma unit3_poly : (unit3 : K) = Adj.map  (C (1/25) * X^5 - C (2/25) * X^4 - C 2 * X + C 3) := by
  unfold unit3
  erw [basisOfBuilderLists_apply_Fn]
  unfold BQ
  congr
  simp [Fin.sum_univ_castSucc]
  ring_nf
  have hC1 : Polynomial.C (1/25 : ℚ) * 75 = Polynomial.C (3 : ℚ) := by
    rw [show (75 : ℚ[X]) = Polynomial.C 75 from (map_ofNat Polynomial.C 75).symm, ← map_mul]
    norm_num
  have hC2 : Polynomial.C (1/25 : ℚ) * 50 = Polynomial.C (2 : ℚ) := by
    rw [show (50 : ℚ[X]) = Polynomial.C 50 from (map_ofNat Polynomial.C 50).symm, ← map_mul]
    norm_num
  have hC3 : Polynomial.C (1/25 : ℚ) * 2 = Polynomial.C (2/25 : ℚ) := by
    rw [show (2 : ℚ[X]) = Polynomial.C 2 from (map_ofNat Polynomial.C 2).symm, ← map_mul]
    norm_num
  linear_combination hC1 - X * hC2 - X ^ 4 * hC3

lemma unit4_poly : (unit4 : K) = Adj.map  (C (1/25) * X^5 - C (1/5) * X^2 - C 2 * X - C 2) := by
  unfold unit4
  erw [basisOfBuilderLists_apply_Fn]
  unfold BQ
  congr
  simp [Fin.sum_univ_castSucc]
  ring_nf
  have aux1 : (1 / 25 : ℚ) * 75  =  3 := by norm_num
  have aux2 : (1 / 25 : ℚ) * 50  =  2 := by norm_num
  have : Polynomial.C (1 / 25 : ℚ) * 75 = C 3 := by
    rw [← aux1, map_mul]
    rfl
  rw [← aux2]
  simp only [map_mul, map_ofNat]
  ring_nf
  have hC5 : Polynomial.C (1/25 : ℚ) * 5 = Polynomial.C (1/5 : ℚ) := by
    rw [show (5 : ℚ[X]) = Polynomial.C 5 from (map_ofNat Polynomial.C 5).symm, ← map_mul]
    norm_num
  linear_combination (-X^2) * hC5


def unit1' : (𝓞 K)ˣ :=
  IsUnit.unit (IsUnit.map (Subalgebra.equivOfEq _ _ O_integral_closure) isUnit_unit1)

def unit2' : (𝓞 K)ˣ :=
  IsUnit.unit (IsUnit.map (Subalgebra.equivOfEq _ _ O_integral_closure) isUnit_unit2)

def unit3' : (𝓞 K)ˣ :=
  IsUnit.unit (IsUnit.map (Subalgebra.equivOfEq _ _ O_integral_closure) isUnit_unit3)

def unit4' : (𝓞 K)ˣ :=
  IsUnit.unit (IsUnit.map (Subalgebra.equivOfEq _ _ O_integral_closure) isUnit_unit4)

lemma unit1_poly' : (unit1' : K) = (AdjoinRoot.mk f) fundU1 := by
  change (↑unit1 : K) = (AdjoinRoot.mk f) fundU1
  rw [unit1_poly]
  rfl

lemma unit3_poly' : (unit3' : K) = (AdjoinRoot.mk f) fundU3 := by
  change (↑unit3 : K) = (AdjoinRoot.mk f) fundU3
  rw [unit3_poly]
  rfl

lemma unit2_poly' : (unit2' : K) = (AdjoinRoot.mk f) fundU2 := by
  change (↑unit2 : K) = (AdjoinRoot.mk f) fundU2
  rw [unit2_poly]
  rfl

lemma unit4_poly' : (unit4' : K) = (AdjoinRoot.mk f) fundU4 := by
  change (↑unit4 : K) = (AdjoinRoot.mk f) fundU4
  rw [unit4_poly]
  rfl

lemma unit1_isIntegral : IsIntegral ℤ ((AdjoinRoot.mk f) fundU1) := by
  rw [← unit1_poly']
  exact NumberField.RingOfIntegers.isIntegral_coe (unit1' : 𝓞 K)

lemma unit2_isIntegral : IsIntegral ℤ ((AdjoinRoot.mk f) fundU2) := by
  rw [← unit2_poly']
  exact NumberField.RingOfIntegers.isIntegral_coe (unit2' :𝓞 K)

lemma unit3_isIntegral : IsIntegral ℤ ((AdjoinRoot.mk f) fundU3) := by
  rw [← unit3_poly']
  exact NumberField.RingOfIntegers.isIntegral_coe (unit3' : 𝓞 K)

lemma unit4_isIntegral : IsIntegral ℤ ((AdjoinRoot.mk f) fundU4) := by
  rw [← unit4_poly']
  exact NumberField.RingOfIntegers.isIntegral_coe (unit4' : 𝓞 K)
