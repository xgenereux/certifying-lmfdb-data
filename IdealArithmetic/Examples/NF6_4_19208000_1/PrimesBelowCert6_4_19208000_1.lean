import IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F0
import IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F1
import IdealArithmetic.Examples.NF6_4_19208000_1.PrimesBelow6_4_19208000_1F2

noncomputable section
def PB87 : PrimesBelowBoundCertificate' O 87 := by
  refine primesBelowBoundCertificate_of_Interval' O ![1, 23, 61, 86] 86 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB87I0
    exact PB87I1
    exact PB87I2
