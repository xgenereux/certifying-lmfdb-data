import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F1

noncomputable section

def PB42 : PrimesBelowBoundCertificate' O 42 := by
  refine primesBelowBoundCertificate_of_Interval' O ![1, 29, 41] 41 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB42I0
    exact PB42I1
