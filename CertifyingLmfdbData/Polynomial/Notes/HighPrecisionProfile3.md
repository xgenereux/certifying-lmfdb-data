# Profiling `unique_root_near` after the interval-arithmetic residual (lever 2)

A third re-run of the [`HighPrecisionProfile.md`](HighPrecisionProfile.md) /
[`HighPrecisionProfile2.md`](HighPrecisionProfile2.md) scaling study, against the current
tactic (`CertifyingLmfdbData/Polynomial/Tactic.lean`). Since Profile 2's last follow-up the
tactic gained the **second structural lever** the earlier documents kept recommending: the
residual `p(v)` is no longer formed as an exact `6·D`-digit Gaussian rational. Instead

* `p(x₀ + x₁·i)` is expanded **symbolically** into two bivariate `ℚ`-coefficient polynomials in
  the atoms `v 0`, `v 1` (`gaussianSymbolic` → `hpvRe`/`hpvIm`, cost `O(deg²)`, precision-free),
  and
* the residual bound `|(M·p(v))ᵢ| ≤ y` is discharged by **dyadic interval arithmetic**
  (`IntervalArithmetic/DyadicReal.lean`) at ~`D`-bit working precision — one kernel `decide`
  per bound instead of a `norm_num` pass over `~6·D`-digit exact rationals.

Together with the `z₁`-truncation lever already in place (derivative checked at a low-precision
proxy `w`), this removes the last super-linear *exact-rational* computation from the hot path.

**Headline.** At 100 000 digits the tactic body is now **5.6 s** (Profile 2's post-`z₁` tail was
~34 s wall). The residual path that dominated Profile 2 — `hpv` expansion + `hy0`/`hy1` +
`evalGaussian` on `p(v)`, ~19.6 s at 100k — is now **~1.1 s**. What remains below ~3 000 digits
is a **precision-independent floor of ~3.45 s**, of which the `hnum` Lipschitz-coefficient
finisher alone is **42 %**. Above ~10k the total grows a clean **~`D¹·³`**, and a
**1 000 000-digit** certificate now completes in **44.8 s** of tactic time (67.7 s wall, via the
file-loading `Test1MFile.lean`). At that scale the growth is *no longer any exact-rational
arithmetic* — it is a handful of finishers **re-normalizing `M`'s `D`-digit decimal entries**,
led by `hz1w` at 34 % of the total.

## Method

Identical to the two earlier studies:

- **Workload.** `p = X⁶ − 2X − 2`, certifying a mixed complex root (both `Re`, `Im` nonzero —
  worst case for the `Complex.mul_re`/`mul_im` cross-terms). Degree 6.
- **Per-step wall clock.** Each phase of the `elab_rules` body and each of the 18 side-goal
  finishers was temporarily bracketed with `IO.monoNanosNow` (a `timeIt`/`PROF` helper logging
  μs deltas). True additive wall clock. Instrumentation reverted after measurement.
- **Precisions.** 100 – 100 000 decimal digits via
  `scratchpad_gen_profile.sage <digits> <out.lean>` (repo root; sage at
  `~/miniforge3/envs/sage/bin/sage`), compiled with `lake env lean`. The 1 000 000-digit point
  is the checked-in `Test1MFile.lean` — same `p`, with `v`/`M` read from `cert1M_*.txt` by the
  `LoadCert` elaborators rather than as inline literals (the inline million-digit literal is
  parsed and kernel-checked far too slowly in a plain `def`).
- Times below are **tactic-internal** (the sum of the `PROF` phases); they exclude the ~5 s
  Mathlib import and, at high precision, the separate non-tactic cost of elaborating and
  kernel-checking the `v`/`M` `def`s and the final proof term (see the wall-clock row).
  Measured on `leanprover/lean4` v4.32.0-rc1, same machine as the earlier studies.

## Results — per-step wall clock vs. precision (ms)

"scaling" is the exponent fitted on the **100k → 1M** increment measured *over the 100-digit
floor* (so a precision-independent step reads ~`D⁰`).

| Step | 100 | 300 | 1 000 | 3 000 | 10 000 | 30 000 | 100 000 | 1 000 000 | scaling |
|------|----:|----:|------:|------:|-------:|-------:|--------:|----------:|---------|
| meta-setup ↳ `parse v,r,M`            | 1.2 | 1.4 | 1.6 | 1.8 | 4.0 | 15.9 | 73 | 1 547 | ~D¹·³ |
| meta-setup ↳ `cert-compute`           | 34 | 39 | 38 | 36 | 52 | 62 | 172 | 2 837 | ~D¹·³ |
| `hv0`+`hv1` (decimal→rational)         | 46 | 48 | 47 | 48 | 51 | 71 | 164 | 2 396 | ~D¹·³ |
| expand `hpdw` (`p'(w)=C+Di` at proxy)  | 382 | 364 | 376 | 376 | 370 | 368 | 374 | 363 | **flat** |
| **`hpv`-symbolic** (`p(v)` bivariate)  | 483 | 498 | 500 | 490 | 494 | 475 | 492 | 470 | **flat** |
| apply assembly lemma                   | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 | 0.3 | flat |
| finisher `hy0`+`hy1` (interval)        | 170 | 181 | 172 | 178 | 196 | 265 | 579 | 7 283 | ~D¹·² |
| finisher `hz1w` (`‖1−M·p'(w)‖≤z₁'`)    | 351 | 357 | 350 | 372 | 385 | 500 | 1 090 | **15 265** | ~D¹·³ |
| finisher `ha` (row-sum `‖M‖≤a`)        | 95 | 95 | 97 | 98 | 110 | 145 | 340 | 4 914 | ~D¹·³ |
| finisher `hB` (`‖v‖≤B`)                | 35 | 35 | 37 | 37 | 46 | 87 | 297 | 4 975 | ~D¹·³ |
| finisher `hnum` (Lipschitz coeff-sum)  | 1 447 | 1 414 | 1 411 | 1 403 | 1 440 | 1 407 | 1 451 | 1 377 | **flat** |
| `hw0`+`hw1` (truncation error)         | 94 | 93 | 94 | 96 | 99 | 114 | 201 | 2 149 | ~D¹·³ |
| `hpd` (derivative polynomial)          | 65 | 64 | 65 | 64 | 67 | 65 | 67 | 64 | flat |
| finisher `hyr` (Newton–Kantorovich)    | 47 | 46 | 45 | 45 | 47 | 55 | 96 | 905 | ~D¹·³ |
| other finishers¹                       | ~216 | ~213 | ~211 | ~210 | ~211 | ~215 | ~223 | ~279 | ~flat |
| **TOTAL (tactic)**                     | 3 466 | 3 449 | 3 446 | 3 459 | 3 573 | 3 845 | **5 619** | **44 823** | **~D¹·³** |
| wall (incl. import + `def` elaboration)| 9.3 s | 9.2 s | 9.3 s | 9.3 s | 9.5 s | 10.3 s | 16.1 s | 67.7 s | |

¹ `hr`, `hεR`, `hz1`, `hdeg`, `hB0`, `hrR`, `hzr` — all small numerals, all flat (`hzr` rises
only 45 → 79 ms).

## Two regimes

- **A precision-independent floor of ~3.45 s**, essentially flat from 100 to 3 000 digits and
  still 61 % of the runtime at 100k. Composition (100-digit column):

  | step | ms | % of floor |
  |------|---:|-----------:|
  | `hnum`         | 1 447 | 42 % |
  | `hpv`-symbolic |   483 | 14 % |
  | `hpdw` expand  |   382 | 11 % |
  | `hz1w`         |   351 | 10 % |
  | `hy0`+`hy1`    |   170 |  5 % |
  | everything else|   633 | 18 % |

  None of these touch the `D`-digit value of `v`: `hnum` works on the tiny coefficients and the
  4-digit `B`; the two `aeval`-shaped expansions (`hpv`-symbolic, `hpdw`) are `O(deg²)` and
  evaluate `p'` only at the ~7-digit proxy `w`; `hz1w` reads the same `hpdw` value.

- **A clean ~`D¹·³` tail** above ~10k, *entirely* from steps that still touch the `D`-digit
  literals of `v` or `M`. Every growing row sits in the band `D¹·²–D¹·³` — polynomial bignum
  work, not the old quadratic base-10 serialization (Profile 1) nor exact `6·D`-digit rationals
  (Profile 2).

At the extremes the leaderboard has completely inverted from Profile 2:

| step | 100k | % | 1M | % | why it grows |
|------|-----:|--:|-----:|--:|--------------|
| `hz1w`         | 1 090 | 19 % | **15 265** | **34 %** | re-normalizes `M`'s `D`-digit decimal entries |
| `hB`           |   297 |  5 % | 4 975 | 11 % | `‖v‖≤B`: touches `v`'s `D`-digit coords |
| `ha`           |   340 |  6 % | 4 914 | 11 % | row-sum touches `M`'s `D`-digit entries |
| `hy0`+`hy1`    |   579 | 10 % | 7 283 | 16 % | interval residual at ~`D` bits |
| `cert-compute` |   172 |  3 % | 2 837 |  6 % | rational cert arithmetic on `D`-digit `v` |
| `hv0`+`hv1`    |   164 |  3 % | 2 396 |  5 % | decimal→rational of `v` coords |
| `parse`        |    73 |  1 % | 1 547 |  3 % | reading the `D`-digit literals |
| `hnum`         | 1 451 | 26 % | 1 377 |  3 % | **flat** — the low-precision floor |
| `hpv`-sym+`hpdw`|  866 | 15 % |   833 |  2 % | **flat** — `O(deg²)` |

## What lever 2 bought (vs. Profile 2's post-`z₁` tail)

Profile 2 ended with the residual path as the only remaining super-linear cost:
`hpv` expansion (9.1 s) + `hy0`/`hy1` (7.8 s) + `evalGaussian` on `p(v)` (2.7 s) ≈ **19.6 s** at
100k, from forming and kernel-checking the `~6·D`-digit exact Gaussian rational `p(v)`. The
current tactic never forms that value:

- **`evalGaussian` on `v` is gone** — the exact `p(v)` is never computed; `evalGaussian` now runs
  only on the bounded 7-digit proxy `w` (inside `cert-compute`).
- **`hpv` expansion → `hpv`-symbolic**, `O(deg²)` in the coefficient atoms, independent of `D`:
  9.1 s → **0.49 s**, and *flat*.
- **`hy0`/`hy1` → dyadic interval `decide`** at ~`D` bits: 7.8 s → **0.58 s** at 100k, growing a
  benign `D¹·²` instead of tracking a `6·D`-digit rational.

Net: the ~19.6 s residual tail collapses to **~1.1 s** at 100k, exactly the ~18× the earlier
documents predicted for "carry ~`D` digits, not `6·D`."

## Where the levers point now

Both structural levers of Profiles 1–2 are done; the profile splits cleanly into a *flat floor*
(fix at low precision) and a *`D¹·³` tail* (fix at high precision), each with one clear target.

1. **`hnum` (1.45 s, flat) — the whole low-precision story.** It is the single largest cost at
   every precision below ~30k (42 % of the floor). This is the recommendation left unimplemented
   in **both** prior documents: the finisher runs one `normNumGoal` carrying the **full default
   simp set** plus the coefficient lemmas, so the `Finset.sum_range_succ` unrolling happens
   inside a full-simp traversal. Restoring a staged `simp only [sum_range_succ, sum_range_zero]`
   pre-pass before `norm_num` (Profile 2, rec. 2), or a dedicated coefficient evaluator
   (Profile 1, priority 4), removes ~1 s at **every** precision.

2. **`M`'s `D`-digit decimal entries — the whole high-precision story.** Above ~30k the tail is
   dominated by finishers that re-normalize `M`'s entries: `hz1w` (34 % at 1M), `ha`, and — for
   `v` — `hB`. `hz1w` checks `‖1 − M·p'(w)‖ ≤ z₁'` where `p'(w)` is a bounded 7-digit value, yet
   its cost tracks `M`'s full precision. Two independent fixes:
   - **Convert `M`'s entries once** into `hM00 … hM11` hypotheses (as is already done for `v` via
     `hv0`/`hv1`) — Profile 2, rec. 3, still not done — so `hz1w`/`ha`/`hy0`/`hy1` stop
     re-parsing the `OfScientific` decimals per finisher.
   - **Truncate `M` like `v`.** `M` is only an *approximate* inverse; the loose `z₁ = 1/2` check
     and the row-sum bound `a` need it to ~a few digits, not `D`. The certificate generator emits
     `M` at full `D`-digit precision unnecessarily; a `w`-style truncation of `M` for `hz1w`/`ha`
     would make them `O(1)` in `D`, exactly as the `z₁` lever did for `p'`. (The residual
     `hy0`/`hy1` genuinely use `M` against the tiny `p(v)`, so they keep ~`D` bits — but that is
     the interval path, already the benign `D¹·²` term.)

3. **The `aeval`-shaped expansions (`hpv`-symbolic 0.49 s, `hpdw` 0.37 s, both flat)** are the
   ~0.9 s fixed residue of the old `AlgHom`/`eval` floor. They do not grow with precision, so they
   are addressable only by a cheaper one-shot expansion, not by any precision lever.

The interval-arithmetic residual and the `z₁`-truncated derivative check have done their job:
neither `p(v)` nor `p'(v)` is ever evaluated exactly at the full-precision `v`, the tactic is
**flat to ~3 000 digits**, and even at **one million digits** its 44.8 s is spent almost
entirely on `M`/`v` decimal handling in a few finishers — pure `D¹·³` bignum work with **no
exact `6·D`-digit arithmetic anywhere**.
