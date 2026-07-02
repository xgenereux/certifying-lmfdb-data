import Mathlib
/-!

# Importing the Residue Approximation

The work can be found in
- https://github.com/CBirkbeck/AINTLIB/blob/dev/dedekind-residue/projects/DedekindResidue/DedekindResidue/MainTheorem.lean

-/


open NumberField

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real FourierTransform

noncomputable def gammaFactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K

noncomputable def completedZetaPrefactor (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ((|discr K| : ℝ) : ℂ) ^ (s / 2) * gammaFactor K s

def IsCompletedDedekindZeta (K : Type*) [Field K] [NumberField K] (Λ : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, 1 < s.re → Λ s = completedZetaPrefactor K s * dedekindZeta K s)
    ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H
        ∧ ∀ s : ℂ, s ≠ 0 → s ≠ 1 → H s = s * (s - 1) * Λ s

def GeneralizedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Λ : ℂ → ℂ, IsCompletedDedekindZeta K Λ →
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Λ s ≠ 0

noncomputable def bSum (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  ∑ᶠ (p : {p : Ideal (RingOfIntegers K) // p.IsPrime ∧ p ≠ ⊥}) (m : ℕ),
    if 0 < m ∧ (Ideal.absNorm p.1 : ℝ) ^ m < X then
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2)) *
        (Real.sqrt X * Real.log X /
            ((Ideal.absNorm p.1 : ℝ) ^ ((m : ℝ) / 2) *
              Real.log ((Ideal.absNorm p.1 : ℝ) ^ m)) - 1)
    else 0

noncomputable def bSumRel (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  bSum K X - bSum ℚ X

noncomputable def fK (K : Type*) [Field K] [NumberField K] (X : ℝ) : ℝ :=
  3 * (bSumRel K X - bSumRel K (X / 9)) / (2 * Real.sqrt X * Real.log (3 * X))

/-!
## A computable form of `bSum`

The summand of `bSum` only depends on the norm `q = N 𝔭` of the prime ideal and on `m`,
and it simplifies: since `log (q ^ m) = m * log q` the leading `log q` cancels, leaving
`√X * log X / (m * q ^ m) - log q / √q ^ m`.  So the quantity we actually evaluate is a
sum over a tuple of *norms* (natural numbers); the enumeration of prime ideals only
enters through the bridge lemma `bSum_eq_bSumFin`.
-/

/-- One term of the Belabas–Friedman sum for a prime ideal of norm `q`, with the cutoff
`q ^ m < X` built in (so a single norm tuple serves both `X` and `X / 9` in `fK`).
Only meaningful for `2 ≤ q` and `0 < m`. -/
noncomputable def bTerm (X : ℝ) (q m : ℕ) : ℝ :=
  if (q : ℝ) ^ m < X then
    Real.sqrt X * Real.log X / (m * (q : ℝ) ^ m) - Real.log q / Real.sqrt q ^ m
  else 0

/-- The finite Belabas–Friedman sum over a tuple of prime-ideal norms `q`, with exponents
`1 ≤ m ≤ M`.  Any uniform `M` with `X ≤ 2 ^ (M + 1)` is large enough. -/
noncomputable def bSumFin (X : ℝ) {N : ℕ} (q : Fin N → ℕ) (M : ℕ) : ℝ :=
  ∑ i, ∑ m ∈ Finset.Icc 1 M, bTerm X (q i) m

/-- The vector containing the first 10 prime numbers. -/
def firstTenPrimes : Fin 10 → ℕ :=
  ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

/-- Your definition instantiated with the first 10 primes. -/
noncomputable def bSumFinTenPrimes : ℝ :=
  bSumFin 10 firstTenPrimes 3

open Classical in
example : bSumFinTenPrimes ≤ 10 := by
  unfold bSumFinTenPrimes bSumFin firstTenPrimes bTerm
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  repeat rw [Finset.sum_Icc_succ_top (by decide)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  have h_log10_upper : Real.log 10 ≤ 2303 / 1000 := by norm_num
  have h_log10_upper : Real.log 10 ≤ 2303 / 1000 := by norm_num




/-- The summand of `bSum`, rewritten so that it only involves `log q`, `√q` and `q ^ m`
(no `rpow` and no `log (q ^ m)`), as in `bTerm`. -/
theorem bSum_term_eq (X : ℝ) {q m : ℕ} (hq : 2 ≤ q) (hm : 0 < m) :
    Real.log q / (q : ℝ) ^ ((m : ℝ) / 2) *
      (Real.sqrt X * Real.log X / ((q : ℝ) ^ ((m : ℝ) / 2) * Real.log ((q : ℝ) ^ m)) - 1)
      = Real.sqrt X * Real.log X / (m * (q : ℝ) ^ m) - Real.log q / Real.sqrt q ^ m := by
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.trans_lt' one_lt_two
  have hsqrt : Real.sqrt q ^ m = (q : ℝ) ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((q : ℝ) ^ (1 / 2 : ℝ)) m,
      ← Real.rpow_mul hq0]
    congr 1
    ring
  have hsq : Real.sqrt q ^ m * Real.sqrt q ^ m = (q : ℝ) ^ m := by
    rw [← mul_pow, Real.mul_self_sqrt hq0]
  have hS : Real.sqrt q ^ m ≠ 0 :=
    pow_ne_zero _ (Real.sqrt_ne_zero'.mpr (lt_trans one_pos hq1))
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [Real.log_pow, ← hsqrt, ← hsq]
  field_simp

/-- Bridge between `bSum` and its computable form: if `P` injectively enumerates (at least)
all the nonzero prime ideals of norm `< X`, then `bSum K X` is the finite sum `bSumFin`
over the norms of the `P i`.  Extra primes of norm `≥ X` in the tuple are harmless (their
terms vanish), so a tuple certified for the bound `X` also serves for `X / 9`. -/
theorem bSum_eq_bSumFin (K : Type*) [Field K] [NumberField K] {X : ℝ} {N M : ℕ}
    (P : Fin N → Ideal (RingOfIntegers K))
    (hM : X ≤ 2 ^ (M + 1))
    (hprime : ∀ i, (P i).IsPrime) (hbot : ∀ i, P i ≠ ⊥)
    (hinj : Function.Injective P)
    (hcover : ∀ p : Ideal (RingOfIntegers K), p.IsPrime → p ≠ ⊥ →
      (Ideal.absNorm p : ℝ) < X → ∃ i, P i = p) :
    bSum K X = bSumFin X (fun i => Ideal.absNorm (P i)) M := by
  -- Proof plan:
  -- 1. A nonzero term forces `(N p : ℝ) ≤ (N p : ℝ) ^ m < X`, so the support of the outer
  --    `finsum` is contained in the image of `i ↦ ⟨P i, hprime i, hbot i⟩` (by `hcover`);
  --    apply `finsum_eq_sum_of_support_subset`, then `Finset.sum_image` (via `hinj`).
  -- 2. The inner `finsum` over `m` has support in `Finset.Icc 1 M`: from `2 ≤ N p` and
  --    `hM`, `(N p : ℝ) ^ m ≥ 2 ^ m ≥ X` whenever `m > M`.
  -- 3. Identify the summands via `bSum_term_eq` (with `2 ≤ Ideal.absNorm (P i)` coming
  --    from `hprime`/`hbot`) and the definition of `bTerm`.
  sorry

/-- `fK` in terms of the finite sums, given injective enumerations `P` of the nonzero
prime ideals of `K` of norm `< X` and `Q` of those of `ℚ` (whose norms are just the
rational primes `< X`).  The same tuples and the same `M` serve all four sums. -/
theorem fK_eq_bSumFin (K : Type*) [Field K] [NumberField K] {X : ℝ} (hX : 0 ≤ X)
    {N N' M : ℕ}
    (P : Fin N → Ideal (RingOfIntegers K)) (Q : Fin N' → Ideal (RingOfIntegers ℚ))
    (hM : X ≤ 2 ^ (M + 1))
    (hPprime : ∀ i, (P i).IsPrime) (hPbot : ∀ i, P i ≠ ⊥) (hPinj : Function.Injective P)
    (hPcover : ∀ p : Ideal (RingOfIntegers K), p.IsPrime → p ≠ ⊥ →
      (Ideal.absNorm p : ℝ) < X → ∃ i, P i = p)
    (hQprime : ∀ i, (Q i).IsPrime) (hQbot : ∀ i, Q i ≠ ⊥) (hQinj : Function.Injective Q)
    (hQcover : ∀ p : Ideal (RingOfIntegers ℚ), p.IsPrime → p ≠ ⊥ →
      (Ideal.absNorm p : ℝ) < X → ∃ i, Q i = p) :
    fK K X =
      3 * ((bSumFin X (fun i => Ideal.absNorm (P i)) M
              - bSumFin X (fun i => Ideal.absNorm (Q i)) M)
          - (bSumFin (X / 9) (fun i => Ideal.absNorm (P i)) M
              - bSumFin (X / 9) (fun i => Ideal.absNorm (Q i)) M))
        / (2 * Real.sqrt X * Real.log (3 * X)) := by
  have h9 : X / 9 ≤ X := by linarith
  have hM9 : X / 9 ≤ 2 ^ (M + 1) := h9.trans hM
  unfold fK bSumRel
  rw [bSum_eq_bSumFin K P hM hPprime hPbot hPinj hPcover,
    bSum_eq_bSumFin ℚ Q hM hQprime hQbot hQinj hQcover,
    bSum_eq_bSumFin K P hM9 hPprime hPbot hPinj
      (fun p hp h0 hn => hPcover p hp h0 (hn.trans_le h9)),
    bSum_eq_bSumFin ℚ Q hM9 hQprime hQbot hQinj
      (fun p hp h0 hn => hQcover p hp h0 (hn.trans_le h9))]

/-- The instance used for LMFDB field 6.4.19208000.1: `X = 1000`, so `M = 9` works
(`2 ^ 10 = 1024 ≥ 1000`) and the tuples must cover the nonzero primes of norm `< 1000`. -/
theorem fK_eq_bSumFin_thousand (K : Type*) [Field K] [NumberField K] {N N' : ℕ}
    (P : Fin N → Ideal (RingOfIntegers K)) (Q : Fin N' → Ideal (RingOfIntegers ℚ))
    (hPprime : ∀ i, (P i).IsPrime) (hPbot : ∀ i, P i ≠ ⊥) (hPinj : Function.Injective P)
    (hPcover : ∀ p : Ideal (RingOfIntegers K), p.IsPrime → p ≠ ⊥ →
      (Ideal.absNorm p : ℝ) < 1000 → ∃ i, P i = p)
    (hQprime : ∀ i, (Q i).IsPrime) (hQbot : ∀ i, Q i ≠ ⊥) (hQinj : Function.Injective Q)
    (hQcover : ∀ p : Ideal (RingOfIntegers ℚ), p.IsPrime → p ≠ ⊥ →
      (Ideal.absNorm p : ℝ) < 1000 → ∃ i, Q i = p) :
    fK K 1000 =
      3 * ((bSumFin 1000 (fun i => Ideal.absNorm (P i)) 9
              - bSumFin 1000 (fun i => Ideal.absNorm (Q i)) 9)
          - (bSumFin (1000 / 9) (fun i => Ideal.absNorm (P i)) 9
              - bSumFin (1000 / 9) (fun i => Ideal.absNorm (Q i)) 9))
        / (2 * Real.sqrt 1000 * Real.log 3000) := by
  have := fK_eq_bSumFin K (by norm_num) P Q (by norm_num : (1000 : ℝ) ≤ 2 ^ (9 + 1))
    hPprime hPbot hPinj hPcover hQprime hQbot hQinj hQcover
  norm_num at this ⊢
  convert this using 3

theorem belabas_friedman_thm1 {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) :
    |Real.log (dedekindZeta_residue K) - fK K X|
      ≤ 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
          ((1 + 3.88 / Real.log (X / 9)) *
              (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
            + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                (Real.sqrt X * Real.log (|discr K| : ℝ))) := by
  sorry


theorem residue_lower_bound {K : Type*} [Field K] [NumberField K]
    (hn : 1 < Module.finrank ℚ K)
    (hGRH : GeneralizedRiemannHypothesis K) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 69 ≤ X) {c b z : ℝ}
    (hc : c ≤ fK K X)
    (hb : 2.324 * Real.log (|discr K| : ℝ) / (Real.sqrt X * Real.log (3 * X)) *
            ((1 + 3.88 / Real.log (X / 9)) *
                (1 + 2 / Real.sqrt (Real.log (|discr K| : ℝ))) ^ 2
              + 4.26 * ((Module.finrank ℚ K : ℝ) - 1) /
                  (Real.sqrt X * Real.log (|discr K| : ℝ))) ≤ b)
    (hz : z ≤ Real.exp (c - b)) :
    z ≤ dedekindZeta_residue K := by
  have key := abs_le.mp (belabas_friedman_thm1 hn hGRH hRH hX)
  have hlog : c - b ≤ Real.log (dedekindZeta_residue K) := by linarith [key.1]
  calc z ≤ Real.exp (c - b) := hz
    _ ≤ Real.exp (Real.log (dedekindZeta_residue K)) := Real.exp_le_exp.mpr hlog
    _ = dedekindZeta_residue K := Real.exp_log (dedekindZeta_residue_pos K)

/-

Look at ResidueApprox.lean. In this file, the goal is to use `belabas_friedman_thm1`
to get a lower bound on the residue of the Dedekind zeta function. (see residue_lower_bound)
but for the field `https://www.lmfdb.org/NumberField/6.4.19208000.1`. We want to prove the bound
up to a couple of sorries. These sorries, together with the actual proof of `belabas_friedman_thm1`
are described here:

There are some things that we sorry for now because it is coming from other projects.

- We can approximate `log`
- We can approximate `sqrt`
- We can approximate `exp`
- We can certify that a list of candidate prime ideals is complete up to a certain bound.
- We can certify that a list of candidate rational prime is complete up to a certain bound.
- We can certify that a list of candidate prime ideals has a list of corresponding norms that is correct
- We can certify the given discriminant as well as the rank of the field is correct.

We now want to instanciate `residue_lower_bound` as much as possible for the given field -
defering the sorries of what I just discribed. What I want is a precise `hc` and `hb` for `X = 1000`.
For `hb` this should be pretty staightforward by adding lemmas of the sort `log 1000 ∈ Icc ....`

For `hc` we need a bit more setup. I think it would make sense to define
`ratPrimes1000 := ![....]`
`nfPrimes1000 := ![....]`
`nfPrimesNorms1000 := ![....]`
`primeRatios1000 := ![....]` (approximates Real.log q / Real.sqrt q)

and any other list you might need. I believe with such a set up  and the appriate sorries claiming
that these lists are complete and correct, we should be able to get a precise `hc` and `hb` for `X = 1000`.



-/
