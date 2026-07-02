import IdealArithmetic.Examples.NF2_0_231_1.PrimesBelow2_0_231_1F0

noncomputable section

def PB10 : PrimesBelowBoundCertificate' O 10 := by
  refine primesBelowBoundCertificate_of_Interval' O ![1, 9] 9 rfl rfl ?_ ?_
  · decide
  · rintro ⟨i,hi⟩
    interval_cases i 
    exact PB10I0
