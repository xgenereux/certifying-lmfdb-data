# Profiling the rewritten `unique_root_near` at high precision

A re-run of the [`HighPrecisionProfile.md`](HighPrecisionProfile.md) scaling study against the
**syntax-free rewrite** of the tactic (commit `8e2370c`: build `Expr`s directly, drive
everything from `MetaM`; numerals via `mkNumeral`, i.e. `Expr.lit (.natVal …)`, instead of
decimal-string `Syntax`). The old document is kept unchanged as the baseline; all "old" numbers
below are quoted from it.

All numbers in the main body are for the rewrite as of `8e2370c`; the `decimalPlaces` fix
identified below has since been implemented and re-measured — see the
[follow-up section](#follow-up-the-od²-decimalplaces-fix-implemented) at the end.

**Headline.** At 30 000 digits the tactic dropped from **117.5 s to 13.9 s** (8.5×). The old
dominant cost — `ratToTerm` serializing `p(v)`/`p'(v)` to decimal numerals, 45.7 s — is now
**7 ms**. A 100 000-digit certificate (not reachable before; extrapolating the old ~D¹·⁹
serialization gives ≳15 min) now takes **61 s** of tactic time. The trade-off: below ~1000
digits the rewrite is ~40% *slower* (floor 2.2 s → 3.0 s), almost entirely a regression in the
`hnum` finisher.

## Method

Identical to the old study, plus a 100 000-digit point:

- **Workload.** `p = X⁶ − 2X − 2`, certifying a mixed complex root (both `Re`, `Im` nonzero —
  worst case for the `Complex.mul_re`/`mul_im` cross-terms). Degree 6.
- **Per-step wall clock.** Each phase of the `elab_rules` body and each of the 13 finishers was
  temporarily bracketed with `IO.monoNanosNow` (a `profMark` helper logging μs deltas). True
  additive wall clock. Instrumentation reverted after measurement (file restored byte-for-byte).
- **Precisions.** 100 – 30 000 decimal digits via `scratchpad_gen_profile.sage <digits> <out.lean>`
  (repo root; sage at `~/miniforge3/envs/sage/bin/sage`), compiled with `lake env lean`. The
  100 000-digit point is the checked-in `Test100000.lean` (same generator, same `p`).
- Times exclude the ~5 s fixed Mathlib import overhead of a single-file `lake env lean` run
  (wall = total + ~5.2 s throughout). Measured on `leanprover/lean4` v4.32.0-rc1, same machine
  as the old study.

## Results — per-step wall clock vs. precision (ms)

"scaling" is the fitted exponent per decade on the 10k → 100k increment over the 100-digit floor.

| Step | 100 | 300 | 1 000 | 3 000 | 10 000 | 30 000 | 100 000 | scaling |
|------|----:|----:|------:|------:|-------:|-------:|--------:|---------|
| **meta-setup** (total)                  | 27 | 29 | 39 | 79 | 408 | 2 594 | **23 696** | **~D¹·⁹** |
| &nbsp;&nbsp;↳ `decimalPlaces` (in parse)| –  | –  | –  | –  | –   | –     | **20 937** | ~D¹·⁹ |
| &nbsp;&nbsp;↳ parse `v`,`r`,`M` (rest of parse) | 1.7 | 3.0 | 7.7 | 33 | 266 | 2 009 | 108 | – |
| &nbsp;&nbsp;↳ `evalGaussian` (Horner)   | 0.5 | 1.3 | 4.8 | 20 | 110 | 527 | 2 635 | ~D¹·⁴ |
| &nbsp;&nbsp;↳ `ratToExpr` (all numerals)| 5.6 | 5.4 | 5.5 | 5.6 | 6.0 | 7.1 | **11** | **flat** |
| &nbsp;&nbsp;↳ certificate `Expr`s       | 19 | 19 | 21 | 20 | 26 | 51 | 205 | small |
| `hv0`+`hv1` (decimal→rational hyps)     | 43 | 43 | 45 | 45 | 48 | 67 | 155 | ~D¹·⁴ |
| **expand `hpv`** (`aeval p = A+Bi`)     | 397 | 401 | 419 | 469 | 792 | 2 566 | **9 112** | ~D¹·³ |
| **expand `hpdv`** (`aeval p' = C+Di`)   | 343 | 353 | 372 | 417 | 672 | 1 847 | **7 790** | ~D¹·⁴ |
| apply assembly lemma                    | 0.4 | 0.7 | 0.4 | 0.4 | 0.4 | 0.4 | 0.4 | flat |
| finisher `hy0`+`hy1`                    | 269 | 274 | 283 | 346 | 605 | 2 589 | **7 723** | ~D¹·³ |
| finisher `hz1`                          | 325 | 339 | 342 | 418 | 778 | 2 402 | **10 159** | ~D¹·³ |
| finisher `hnum`                         | 1 297 | 1 296 | 1 320 | 1 304 | 1 315 | 1 368 | 1 696 | ~flat |
| finisher `ha`                           | 86 | 88 | 86 | 90 | 96 | 133 | 313 | ~D¹·³ |
| finisher `hB`                           | 32 | 33 | 32 | 35 | 42 | 80 | 278 | ~D¹·⁴ |
| other finishers¹                        | ~202 | ~201 | ~199 | ~203 | ~203 | ~217 | ~284 | ~flat |
| **TOTAL (tactic)**                      | 3 024 | 3 059 | 3 138 | 3 407 | 4 962 | **13 865** | **61 206** | ~D¹·⁵ |
| wall (incl. ~5 s import overhead)       | 8.2 s | 8.3 s | 8.4 s | 8.7 s | 10.4 s | 20.1 s | 72.3 s | |

¹ `hr`, `hpd`, `hdeg`, `hB0`, `hrR`, `hyr`, `hzr` (`hyr` alone grows: 40 → 112 ms, since
`y`, `z₁`, `z₂`, `r` are D-digit numerals).

## Old vs. new, at 30 000 digits (ms)

| Step | old (syntax) | new (Expr) | change |
|------|-------------:|-----------:|--------|
| meta-setup — of which serialization | 50 000 — 45 672 | 2 594 — **7** | **19× — 6500×** |
| expand `hpv`                | 34 789 | 2 566 | 14× |
| expand `hpdv`               | 27 942 | 1 847 | 15× |
| refine/apply assembly       | 1 250  | 0.4   | 3000× |
| conv/assert `hv0`+`hv1`     | 1 256  | 67    | 19× |
| finisher `hz1`              | 953    | 2 402 | **0.4× (regressed)** |
| finisher `hy0`+`hy1`        | 441    | 2 589 | **0.17× (regressed)** |
| finisher `hnum`             | 489    | 1 368 | **0.36× (regressed)** |
| other finishers             | ~360   | ~730  | 0.5× |
| **TOTAL**                   | **117 484** | **13 865** | **8.5×** |

### What the rewrite fixed

Exactly what it targeted. The O(N²) base-10 serialization of the ~150 000-digit exact fractions
(`ratToTerm`, the old #1 cost) is gone: `mkNumeral` stores the bignum directly in the `Expr`,
so producing *all* numerals now costs 11 ms even at 100k digits. Downstream, `simp`/`norm_num`
receive `natVal` literals instead of re-parsing decimal strings, which is where the 14–15× on
the two `aeval` expansions comes from. The `apply`-based assembly and `assertHyp`-based decimal
conversion replaced their syntax-elaboration equivalents at negligible cost.

### What regressed: the flat floor (2.2 s → 3.0 s) and the value-consuming finishers

- **`hnum` tripled (0.4 s → 1.3 s flat)** and is now **43% of the entire tactic below
  ~3000 digits**. The old finisher was staged: `simp only [Finset.sum_range_succ,
  sum_range_zero]` (a two-lemma simp set) to unroll the sum, *then* `norm_num [coeff lemmas,
  Nat.choose]`. The rewritten finisher makes a single `normNumGoal` pass whose context is the
  **full default simp set** plus those lemmas (with `Nat.choose` as an unfold), so the sum
  unrolling happens inside a full-simp-set traversal.
- **`hy0`/`hy1`/`hz1` grew ~D¹·³ where they used to be near-flat** (together 5.9 s at 30k vs
  1.4 s old; 17.9 s at 100k). Same suspect: each is one `normNumGoal` call carrying the full
  default simp set, and each unfolds `M` — whose entries are D-digit *decimal* literals that
  get re-normalized (`OfScientific → ↑m/10^e → division`) per finisher, unlike `v`, which is
  converted once into the `hv0`/`hv1` hypotheses. `ha`, which touches *only* `M`, isolates that
  per-finisher cost: 86 → 313 ms, ~D¹·³.

## The new bottleneck: `decimalPlaces` is O(D²) — and unnecessary

The single largest cost at 100k digits (20.9 s, **34% of the total**) is not proof work at all.
The parse-phase sub-timers show `parse` = 21.0 s, of which `decimalPlaces` (computing the
exponentiation threshold) = 20.94 s; actually parsing `v`, `r` and elaborating `M` is 26 ms.
`decimalPlaces` calls `padicVal 2/5` on the denominator: ~D repeated divisions of a
~10^D-magnitude bignum, each O(D) — a textbook O(D²) loop, and it is run on all three of
`v 0`, `v 1`, `r`.

The information it computes is already available for free: `parseRat` visits the
`OfScientific _ _ m sign e` node and reads the exponent literal `e` — which *is* the number of
decimal places (up to cancellation, which only lowers it; the threshold only needs an upper
bound). Returning/accumulating the max exponent seen during parsing (or computing the
denominator's decimal length via `Nat.log 10`-style bit-length arithmetic) makes this O(1)-ish
and removes a third of the 100k runtime for a few lines of code.

## Where the time would go next (100k digits, 61.2 s)

| cost | time | % | lever |
|------|-----:|--:|-------|
| `decimalPlaces`        | 20.9 s | 34% | O(1) exponent from `OfScientific` (trivial) |
| `hz1` + expand `hpdv`  | 18.0 s | 29% | loosen `z₁` to ~0.5 (old doc, lever 1) — `p'(v)` then needs ~1 digit |
| expand `hpv` + `hy0`/`hy1` | 16.8 s | 27% | dyadic/fixed-precision enclosures (old doc, lever 2) — ~D digits instead of 6·D |
| `evalGaussian`         | 2.6 s  | 4%  | shrinks automatically with enclosures |
| `hnum`                 | 1.7 s  | 3%  | restore the staged `simp only` pre-pass (also fixes the low-precision floor) |
| everything else        | ~1.2 s | 2%  | — |

Both recommendations of the old analysis (loosen `z₁`; dyadic enclosures for `p(v)`) survive
unchanged — the rewrite removed the serialization layer *around* the exact-rational pipeline,
but the pipeline still computes and verifies 6·D-digit exact fractions, and that arithmetic
(now ~D¹·³, i.e. GMP/kernel bignum work) is 60% of the remaining time. New, cheaper items
first, though:

1. **Fix `decimalPlaces`** (O(1) instead of O(D²)): −34% at 100k, a few lines.
   *Implemented — see the follow-up section below; the prediction held exactly.*
2. **Restore the staged `hnum` finisher** (`simp only` unroll, then `norm_num`): −~1 s at every
   precision; brings the ≤1000-digit floor back to ~2 s, where the rewrite currently *loses*
   to the old tactic.
3. **Convert `M`'s entries once** into `hM00 … hM11` hypotheses (as is already done for `v` via
   `hv0`/`hv1`), so `ha`/`hy0`/`hy1`/`hz1` stop re-normalizing D-digit decimals per finisher.
4. **Loosen `z₁` and introduce dyadic enclosures** — the two structural levers from
   [`HighPrecisionProfile.md`](HighPrecisionProfile.md), unchanged, now jointly ~56% of the
   remaining time.

## Follow-up: the O(D²) `decimalPlaces` fix (implemented)

Recommendation 1 was implemented and the whole study re-run (same instrumentation, same test
files, same machine). `decimalPlaces` now returns the upper bound `q.den.log2 + 1` instead of
`max (padicVal 2 q.den) (padicVal 5 q.den)`:

- the value only feeds `exponentiation.threshold`, which needs an *upper bound*, and
  `max (v₂ den) (v₅ den) ≤ ⌊log₂ den⌋` always (each of `2^v₂`, `5^v₅` divides, hence is at
  most, `den`); the ≤ log₂ 10 ≈ 3.3× overshoot is harmless since the only large powers the
  finishers actually evaluate are the true `10 ^ e` terms;
- `Nat.log2` is `@[extern "lean_nat_log2"]`, a GMP bit-length lookup. Micro-benchmark on a
  denominator of the 100k-certificate's shape (`2^99998·5^100000`): 6.2–7.9 **s** per call
  before, ≤ 7 **μs** after. `padicVal` was deleted (this was its only caller).

### Results after the fix — per-step wall clock (ms)

| Step | 100 | 300 | 1 000 | 3 000 | 10 000 | 30 000 | 100 000 |
|------|----:|----:|------:|------:|-------:|-------:|--------:|
| **meta-setup** (total)                  | 26 | 27 | 31 | 47 | 147 | 602 | **2 931** |
| &nbsp;&nbsp;↳ parse `v`,`r`,`M` (incl. `decimalPlaces`) | 1.3 | 1.3 | 1.6 | 2.0 | 4.2 | 15 | **72** |
| &nbsp;&nbsp;↳ `evalGaussian` (Horner)   | 0.5 | 1.2 | 4.7 | 20 | 110 | 528 | 2 665 |
| &nbsp;&nbsp;↳ `ratToExpr` (all numerals)| 5.3 | 5.4 | 5.5 | 5.9 | 5.9 | 7.4 | 12 |
| &nbsp;&nbsp;↳ certificate `Expr`s       | 19 | 19 | 19 | 20 | 27 | 52 | 182 |
| `hv0`+`hv1`                             | 44 | 48 | 43 | 45 | 50 | 68 | 156 |
| expand `hpv`                            | 399 | 406 | 411 | 468 | 791 | 2 559 | 9 128 |
| expand `hpdv`                           | 363 | 350 | 356 | 406 | 681 | 1 851 | 7 835 |
| finisher `hy0`+`hy1`                    | 274 | 275 | 279 | 331 | 613 | 2 599 | 7 773 |
| finisher `hz1`                          | 333 | 328 | 343 | 407 | 786 | 2 387 | 10 225 |
| finisher `hnum`                         | 1 298 | 1 326 | 1 289 | 1 306 | 1 321 | 1 366 | 1 700 |
| finisher `ha`                           | 89 | 88 | 89 | 90 | 97 | 133 | 314 |
| finisher `hB`                           | 33 | 32 | 32 | 35 | 42 | 80 | 280 |
| other finishers + apply                 | ~210 | ~202 | ~199 | ~204 | ~210 | ~220 | ~283 |
| **TOTAL (tactic)**                      | 3 071 | 3 082 | 3 072 | 3 339 | 4 739 | **11 864** | **40 624** |
| wall (incl. ~5 s import overhead)       | 8.3 s | 8.3 s | 8.3 s | 8.6 s | 10.2 s | 18.0 s | 51.6 s |

Exactly as predicted: the parse phase collapsed from 20.8 s to **72 ms** at 100k (290×) and
from 2.0 s to 15 ms at 30k, taking the totals from 61.2 s → **40.6 s** (−34%) and
13.9 s → **11.9 s** (−14%). All other steps are unchanged within noise, and every precision
still certifies successfully. Versus the pre-rewrite tactic, 30 000 digits is now **9.9×**
faster (117.5 s → 11.9 s).

### Remaining cost structure (100k digits, 40.6 s)

With the incidental costs gone, the profile is now almost entirely the exact-rational
6·D-digit pipeline, i.e. the two structural levers of
[`HighPrecisionProfile.md`](HighPrecisionProfile.md):

| cost | time | % | lever |
|------|-----:|--:|-------|
| `hz1` + expand `hpdv`                    | 18.1 s | 44% | loosen `z₁` to ~0.5 → `p'(v)` needs ~1 digit |
| expand `hpv` + `hy0`/`hy1` + `evalGaussian` | 19.6 s | 48% | dyadic enclosures: ~D digits instead of 6·D |
| `hnum`                                   | 1.7 s  | 4%  | staged `simp only` pre-pass (also the low-precision floor) |
| everything else                          | ~1.2 s | 3%  | — |

## Follow-up 2: the `z₁` lever (implemented)

The first structural lever — loosen `z₁` and stop evaluating `p'` at the full-precision `v` —
was implemented. Rather than a bare default change, the derivative check now runs at a
**truncated proxy point**: `w := v` truncated to an adaptively chosen number of decimal
places (`truncDecimals`), `wDigits := max 6 (⌈log₁₀ (500·z₂/z₁)⌉) (⌈log₁₀ (1/R)⌉)` with
truncation error `ε := 10^(-wDigits)`, so that the transported error `z₂·ε` consumes at most
~0.2 % of the `z₁` budget however ill-conditioned the input. `z₂` scales like the inverse
root-separation, so clustered roots buy `w` exactly the digits they genuinely need (never
more than ~3 beyond the digits of `r` itself, since `hzr` forces `z₂·r < 1`), while for the
benign workload here `wDigits = 7`. The ceilings are computed from GMP bit lengths
(`log10Upper`), not by O(D²) division loops.

- New lemma `nnnorm_one_sub_comp_polyToZeroFinderDeriv_le_of_approx` (`Certify.lean`):
  `‖1 − M·J(v)‖ ≤ ‖1 − M·J(w)‖ + ‖M·(J(w) − J(v))‖ ≤ z₁' + z₂·ε` for `‖v − w‖ ≤ ε ≤ R`,
  **reusing the already-certified Lipschitz bound `z₂`** — no new sum to verify. Threaded
  through `existsUnique_root_of_certificates_approx` / `UniqueRootNear.of_certificates_approx`
  into the tactic's assembly lemma.
- Tactic changes: default `z₁ := 1/2` (the NK inequalities `hyr`/`hzr` admit `z₁ ≈ 0.9`, so
  nothing tightens), default `R := max r 10⁻⁶` (the floor guarantees `ε ≤ R`); `p'` is
  evaluated (meta-level and in the `hpdw` expansion) only at `w`, never at `v`; new
  O(1)-or-O(D)-cheap side checks `hw0`/`hw1` (`|v i − w i| ≤ ε`, one D-digit subtraction
  each), `hεR` (`ε ≤ R`) and `hz1 : z₁' + z₂·ε ≤ z₁` (small numerals), with `z₁'` the exact
  row-sum bound on `|1 − M·p'(w)|` rounded up to 3 significant digits. The `z₁`/`R`/`z₂`
  overrides must now be numeric literals, since they size `wDigits`.
- Regression test (`AllRoots.lean`): `(X − 1)(X − (1 + 10⁻³⁰))` certified at the root `1`
  with `r = 10⁻⁴⁰` — there `M ≈ −10³⁰`, `z₂ ≈ 6·10³⁰`, and the adaptive width picks
  `wDigits ≈ 35`; any *fixed* truncation width ≤ 31 digits would fail its `hz1` check.

Wall-clock (same machine, `lake env lean`, incl. ~5 s import overhead), all certificates
still succeeding:

| digits | before | after | Δ |
|-------:|-------:|------:|---|
| 1 000  | 8.3 s  | 8.6 s | floor unchanged (new checks ≈ the old `hpdv`/`hz1` floor cost) |
| 30 000 | 18.0 s | 14.7 s | −3.3 s ≈ the old `hz1` (2.4 s) + `hpdv` (1.9 s) |
| 100 000 | 51.6 s | 33.9 s | **−17.7 s**, matching the predicted ~18.1 s for this lever |

The remaining super-linear cost is now almost exclusively the residual path
(`hpv` expansion + `hy0`/`hy1` + `evalGaussian` on `p(v)`), i.e. lever 2 (dyadic enclosures);
the derivative path no longer grows with precision.
