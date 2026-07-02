import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F0
import IdealArithmetic.Examples.NF3_1_24843_1.PrimesBelow3_1_24843_1F1

noncomputable section

def PB45 : PrimesBelowBoundCertificate' O 45 := by
  refine primesBelowBoundCertificate_of_Interval' O ![1, 31, 44] 44 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB45I0
    exact PB45I1
