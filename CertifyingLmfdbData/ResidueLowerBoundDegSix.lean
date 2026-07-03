import Mathlib
import CertifyingLmfdbData.ResidueApprox
import CertifyingLmfdbData.SexticExampleHyp
import CertifyingLmfdbData.IntervalArithmetic.Interval
import CertifyingLmfdbData.IntervalArithmetic.DyadicReal

/-!
# A certified residue lower bound for LMFDB field 6.4.19208000.1

Instantiation of `residue_lower_bound` for `K₆ = ℚ[x]/(x⁶ - 5x⁴ - 50x² + 125)`
(https://www.lmfdb.org/NumberField/6.4.19208000.1) at `X = 1000`, `M = 9`:
assuming GRH for `K₆` and RH, the residue of `ζ_{K₆}` at `s = 1` is at least `0.198`
(the true value is `≈ 0.3661`; the Belabas–Friedman error bound at `X = 1000` costs a
factor `≈ e^{-0.63}`).

All numeric facts are *proved*, via `dyadic_interval`, and the rational prime list is
*proved* complete and correct (`ratPrimes1000_spec`).  The field invariants
(irreducibility, degree, discriminant) come from `CertifyingLmfdbData.SexticExampleHyp`;
the only `sorry` of this file is the completeness of the list of prime ideals of `K₆`
of norm `< 1000` together with the correctness of their norms (`nfPrimes1000_spec`).

The data lists and the rational constants are generated and margin-checked by
`sage_code/generate_residue_data.sage`.
-/

open NumberField Polynomial

namespace DegSix

noncomputable section

/-- The number field `ℚ[x]/(x⁶ - 5x⁴ - 50x² + 125)`, LMFDB label 6.4.19208000.1, from
`CertifyingLmfdbData.SexticExampleHyp` (as are its degree and discriminant below). -/
abbrev K₆ := SexticExample.K

theorem finrank_degSix : Module.finrank ℚ K₆ = 6 := SexticExample.finrank_eq

theorem discr_degSix : discr K₆ = -19208000 := SexticExample.discr_eq

/-! ## The prime data below `X = 1000` -/

/-- The 168 rational primes `< 1000`. -/
def ratPrimes1000 : Fin 168 → ℕ :=
  ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
    83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
    173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
    269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
    373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587,
    593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683,
    691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811,
    821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

/-- The norms of the 169 prime ideals of `K₆` of norm `< 1000`, with multiplicity (a
norm appears once per prime ideal).  For `p ≠ 5` these come from factoring the defining
polynomial mod `p` (the index `[O_K : ℤ[a]] = 5⁶` is a power of 5, so Dedekind's
criterion applies); `5` factors as `𝔭²` with residue degree 3, contributing norm 125. -/
def nfPrimesNorms1000 : Fin 169 → ℕ :=
  ![7, 7, 8, 13, 13, 13, 13, 27, 27, 29, 29, 41, 41, 43, 43, 71, 71, 71, 71, 83, 83, 97,
    97, 97, 97, 113, 113, 113, 113, 125, 127, 127, 139, 139, 139, 139, 167, 167, 167,
    167, 167, 167, 169, 181, 181, 181, 181, 181, 181, 197, 197, 197, 197, 211, 211, 211,
    211, 223, 223, 281, 281, 307, 307, 337, 337, 337, 337, 349, 349, 419, 419, 419, 419,
    421, 421, 433, 433, 433, 433, 449, 449, 461, 461, 463, 463, 503, 503, 547, 547, 547,
    547, 547, 547, 587, 587, 601, 601, 617, 617, 617, 617, 631, 631, 631, 631, 643, 643,
    659, 659, 659, 659, 673, 673, 673, 673, 701, 701, 701, 701, 701, 701, 727, 727, 743,
    743, 757, 757, 757, 757, 769, 769, 797, 797, 797, 797, 811, 811, 811, 811, 827, 827,
    839, 839, 839, 839, 841, 841, 853, 853, 853, 853, 881, 881, 881, 881, 881, 881, 883,
    883, 911, 911, 911, 911, 953, 953, 953, 953, 967, 967]

/-! ### The rational prime list is complete and correct

`ratPrimes1000_spec` is *proved*: the prime ideals of `𝓞 ℚ` are classified by transfer
along `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ` and `Ideal.isPrime_int_iff`, primality of
each list entry is checked by `norm_num`, and completeness below `1000` by a kernel
`decide` trial-division sweep (`ratPrimes1000_sweep`): every `q < 1000` not in the list
has a proper divisor among the primes `≤ 31`, so no prime is missing. -/

/-- Every entry of `ratPrimes1000` is a prime number. -/
lemma ratPrimes1000_prime (i : Fin 168) : (ratPrimes1000 i).Prime := by
  fin_cases i <;> norm_num [ratPrimes1000]

set_option maxRecDepth 10000 in
/-- `ratPrimes1000` is strictly increasing (hence injective). -/
lemma ratPrimes1000_strictMono : StrictMono ratPrimes1000 :=
  Fin.strictMono_iff_lt_succ.mpr (by decide)

/-- The same 168 primes as a plain list literal (for cheap kernel computations: `List`
membership is a linear scan, while indexing into `![...]` is quadratic). -/
def ratPrimesList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
   83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
   173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263,
   269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
   373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
   467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587,
   593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683,
   691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811,
   821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
   937, 941, 947, 953, 967, 971, 977, 983, 991, 997]

set_option maxRecDepth 10000 in
lemma ofFn_ratPrimes1000 : List.ofFn ratPrimes1000 = ratPrimesList := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- Trial-division sweep: every `q < 1000` is in the list, is `< 2`, or has a nontrivial
divisor among the primes `≤ 31` (enough, since a composite `< 1000` has a factor
`≤ √999 < 32`).  Only cheap kernel arithmetic is involved — in particular no primality
instance, whose kernel evaluation is prohibitively slow. -/
lemma ratPrimes1000_sweep : ∀ q < 1000, q ∈ ratPrimesList ∨ q < 2 ∨
    ∃ d ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31], d ≠ q ∧ d ∣ q := by
  decide +kernel

/-- `ratPrimes1000` contains every prime `< 1000`: a prime is not `< 2` and has no
nontrivial divisor, so the sweep forces it into the list. -/
lemma ratPrimes1000_complete : ∀ q < 1000, q.Prime → ∃ i, ratPrimes1000 i = q := by
  intro q hq hp
  rcases ratPrimes1000_sweep q hq with hmem | h2 | ⟨d, hd, hne, hdvd⟩
  · exact List.mem_ofFn.mp (ofFn_ratPrimes1000 ▸ hmem)
  · exact absurd hp.two_le (by omega)
  · rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
    · exact absurd h1 (by fin_cases hd <;> norm_num)
    · exact absurd hself hne

/-- A prime natural number is prime in `𝓞 ℚ` (transfer along `𝓞 ℚ ≃+* ℤ`). -/
lemma prime_natCast_ratOI {n : ℕ} (hn : n.Prime) : Prime (n : RingOfIntegers ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hn

open Ideal in
/-- The norm of the ideal of `𝓞 ℚ` generated by `n : ℕ` is `n`. -/
lemma absNorm_span_natCast (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : RingOfIntegers ℚ)}) = n := by
  rw [show ((n : RingOfIntegers ℚ)) = algebraMap ℤ (RingOfIntegers ℚ) (n : ℤ) by
      push_cast; rfl,
    Ideal.absNorm_span_singleton, Algebra.norm_algebraMap, RingOfIntegers.rank,
    Module.finrank_self, pow_one, Int.natAbs_natCast]

/-- Every nonzero prime ideal of `𝓞 ℚ` is generated by a prime natural number
(transfer of `Ideal.isPrime_int_iff` along `𝓞 ℚ ≃+* ℤ`). -/
lemma exists_span_natCast_of_isPrime {p : Ideal (RingOfIntegers ℚ)} (hp : p.IsPrime)
    (hbot : p ≠ ⊥) : ∃ q : ℕ, q.Prime ∧ p = Ideal.span {(q : RingOfIntegers ℚ)} := by
  haveI := hp
  have hmapPrime : (p.map Rat.ringOfIntegersEquiv).IsPrime := inferInstance
  have hmapBot : p.map Rat.ringOfIntegersEquiv ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective Rat.ringOfIntegersEquiv.injective).not.mpr hbot
  obtain ⟨q, hq, heq⟩ := (Ideal.isPrime_int_iff.mp hmapPrime).resolve_left hmapBot
  refine ⟨q, hq, ?_⟩
  have := congrArg
    (Ideal.comap (Rat.ringOfIntegersEquiv : RingOfIntegers ℚ ≃+* ℤ)) heq
  rw [Ideal.comap_map_of_bijective _ Rat.ringOfIntegersEquiv.bijective,
    ← Ideal.map_symm, Ideal.map_span, Set.image_singleton, map_natCast] at this
  exact this

open Ideal in
/-- The nonzero prime ideals of `ℤ = 𝓞 ℚ` of norm `< 1000` are enumerated (injectively
and completely) by a tuple whose norms are exactly `ratPrimes1000`. -/
theorem ratPrimes1000_spec :
    ∃ Q : Fin 168 → Ideal (RingOfIntegers ℚ),
      (∀ i, (Q i).IsPrime) ∧ (∀ i, Q i ≠ ⊥) ∧ Function.Injective Q ∧
      (∀ p : Ideal (RingOfIntegers ℚ), p.IsPrime → p ≠ ⊥ →
        (Ideal.absNorm p : ℝ) < 1000 → ∃ i, Q i = p) ∧
      (∀ i, Ideal.absNorm (Q i) = ratPrimes1000 i) := by
  refine ⟨fun i => span {(ratPrimes1000 i : RingOfIntegers ℚ)},
    fun i => ?_, fun i => ?_, ?_, ?_, fun i => ?_⟩
  · exact (span_singleton_prime
      (Nat.cast_ne_zero.mpr (ratPrimes1000_prime i).ne_zero)).mpr
      (prime_natCast_ratOI (ratPrimes1000_prime i))
  · rw [Ne, span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (ratPrimes1000_prime i).ne_zero
  · intro i j h
    have h' := congrArg absNorm h
    rw [absNorm_span_natCast, absNorm_span_natCast] at h'
    exact ratPrimes1000_strictMono.injective h'
  · intro p hp hbot hnorm
    obtain ⟨q, hq, rfl⟩ := exists_span_natCast_of_isPrime hp hbot
    rw [absNorm_span_natCast] at hnorm
    obtain ⟨i, rfl⟩ := ratPrimes1000_complete q (by exact_mod_cast hnorm) hq
    exact ⟨i, rfl⟩
  · exact absNorm_span_natCast _

/-- The nonzero prime ideals of `𝓞 K₆` of norm `< 1000` are enumerated (injectively
and completely) by a tuple whose norms are exactly `nfPrimesNorms1000`; certified
externally. -/
axiom nfPrimes1000_spec :
    ∃ P : Fin 169 → Ideal (RingOfIntegers K₆),
      (∀ i, (P i).IsPrime) ∧ (∀ i, P i ≠ ⊥) ∧ Function.Injective P ∧
      (∀ p : Ideal (RingOfIntegers K₆), p.IsPrime → p ≠ ⊥ →
        (Ideal.absNorm p : ℝ) < 1000 → ∃ i, P i = p) ∧
      (∀ i, Ideal.absNorm (P i) = nfPrimesNorms1000 i)

/-! ## The numeric bounds

One-sided bounds on the four `bSumFin` sums appearing in `fK_eq_bSumFin_thousand` and
on its denominator.  Reference values (`generate_residue_data.sage`):
`A ≈ 272.64764672`, `B ≈ 487.69424137`, `C ≈ 39.40248448`, `D ≈ 87.21154881`,
`2·√1000·log 3000 ≈ 506.36714597`. -/

/-- The inner exponent sum of `bSumFin` at `M = 9`, pre-expanded.  Rewriting with this
(one cheap `simp only` rewrite per prime) is far faster than having `norm_num` match
`Finset.sum_Icc_succ_top` against numeral bounds inside the ~170-term outer sum. -/
private lemma sum_Icc_one_nine (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 9, f m =
      f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  norm_num [Finset.sum_Icc_succ_top]

-- the `simp only` unfold of a sum with ~170 `![...]`-entries recurses deeply
set_option maxRecDepth 10000 in
lemma bSumFin_nf_1000_lower :
    (2726476467 / 10 ^ 7 : ℝ) ≤ bSumFin 1000 nfPrimesNorms1000 9 := by
  simp only [bSumFin, sum_Icc_one_nine, Fin.sum_univ_succ, Fin.sum_univ_zero,
    nfPrimesNorms1000, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  norm_num [bTerm]
  dyadic_interval [approx := 39]

set_option maxHeartbeats 800000 in
-- the `simp only` unfold of a sum with ~170 `![...]`-entries recurses deeply; the 168
-- distinct primes give `norm_num` ~1500 distinct cutoff conditions to decide
set_option maxRecDepth 10000 in
lemma bSumFin_rat_1000_upper :
    bSumFin 1000 ratPrimes1000 9 ≤ (4876942414 / 10 ^ 7 : ℝ) := by
  simp only [bSumFin, sum_Icc_one_nine, Fin.sum_univ_succ, Fin.sum_univ_zero,
    ratPrimes1000, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  norm_num [bTerm]
  dyadic_interval [approx := 40]

-- the `simp only` unfold of a sum with ~170 `![...]`-entries recurses deeply
set_option maxRecDepth 10000 in
lemma bSumFin_nf_ninth_upper :
    bSumFin (1000 / 9) nfPrimesNorms1000 9 ≤ (394024845 / 10 ^ 7 : ℝ) := by
  simp only [bSumFin, sum_Icc_one_nine, Fin.sum_univ_succ, Fin.sum_univ_zero,
    nfPrimesNorms1000, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  norm_num [bTerm]
  dyadic_interval [approx := 37]

set_option maxHeartbeats 800000 in
-- the `simp only` unfold of a sum with ~170 `![...]`-entries recurses deeply; the 168
-- distinct primes give `norm_num` ~1500 distinct cutoff conditions to decide
set_option maxRecDepth 10000 in
lemma bSumFin_rat_ninth_lower :
    (872115488 / 10 ^ 7 : ℝ) ≤ bSumFin (1000 / 9) ratPrimes1000 9 := by
  simp only [bSumFin, sum_Icc_one_nine, Fin.sum_univ_succ, Fin.sum_univ_zero,
    ratPrimes1000, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  norm_num [bTerm]
  dyadic_interval [approx := 38]

lemma denom_lower : (5063671459 / 10 ^ 7 : ℝ) ≤ 2 * Real.sqrt 1000 * Real.log 3000 := by
  dyadic_interval [approx := 37]

/-! ## `hc`, `hb`, `hz` and the final bound -/

/-- The precise `hc` for `X = 1000`: `-0.9909 ≤ fK K₆ 1000` (true value `≈ -0.9908079`). -/
theorem fK_lower : (-9909 / 10000 : ℝ) ≤ fK K₆ 1000 := by
  obtain ⟨P, hPprime, hPbot, hPinj, hPcover, hPnorm⟩ := nfPrimes1000_spec
  obtain ⟨Q, hQprime, hQbot, hQinj, hQcover, hQnorm⟩ := ratPrimes1000_spec
  have hPfun : (fun i => Ideal.absNorm (P i)) = nfPrimesNorms1000 := funext hPnorm
  have hQfun : (fun i => Ideal.absNorm (Q i)) = ratPrimes1000 := funext hQnorm
  rw [fK_eq_bSumFin_thousand K₆ P Q hPprime hPbot hPinj hPcover hQprime hQbot hQinj
    hQcover, hPfun, hQfun]
  have hd : (0 : ℝ) < 2 * Real.sqrt 1000 * Real.log 3000 :=
    lt_of_lt_of_le (by norm_num) denom_lower
  rw [le_div_iff₀ hd]
  linarith [bSumFin_nf_1000_lower, bSumFin_rat_1000_upper, bSumFin_nf_ninth_upper,
    bSumFin_rat_ninth_lower, denom_lower]

/-- The precise `hb` for `X = 1000`: the Belabas–Friedman error bound is at most
`0.6281` (true value `≈ 0.6280958`). -/
theorem errBound_upper :
    2.324 * Real.log (|discr K₆| : ℝ) / (Real.sqrt 1000 * Real.log (3 * 1000)) *
        ((1 + 3.88 / Real.log (1000 / 9)) *
            (1 + 2 / Real.sqrt (Real.log (|discr K₆| : ℝ))) ^ 2
          + 4.26 * ((Module.finrank ℚ K₆ : ℝ) - 1) /
              (Real.sqrt 1000 * Real.log (|discr K₆| : ℝ)))
      ≤ (6281 / 10000 : ℝ) := by
  rw [discr_degSix, finrank_degSix]
  norm_num
  dyadic_interval [approx := 24]

/-- The final constant: `0.198 ≤ exp (c - b)` (true value `≈ 0.1980988`). -/
theorem z_le : (198 / 1000 : ℝ) ≤ Real.exp (-9909 / 10000 - 6281 / 10000) := by
  dyadic_interval [approx := 18]

/-- **The residue lower bound for LMFDB field 6.4.19208000.1**: under GRH for `K₆`
and RH, the residue of the Dedekind zeta function of `K₆` at `s = 1` is at least
`0.198`. -/
theorem residue_lower_bound_degSix
    (hGRH : GeneralizedRiemannHypothesis K₆) (hRH : RiemannHypothesis) :
    (198 / 1000 : ℝ) ≤ dedekindZeta_residue K₆ :=
  residue_lower_bound (by rw [finrank_degSix]; norm_num) hGRH hRH
    (by norm_num : (69 : ℝ) ≤ 1000) fK_lower errBound_upper z_le

end

end DegSix
