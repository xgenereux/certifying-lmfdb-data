# Profiling `unique_root_near` at high precision

A scaling study of the `unique_root_near` tactic
(`CertifyingLmfdbData/Polynomial/Tactic.lean`) as the decimal precision of the input
approximation grows from 100 to 30 000 digits, plus an analysis of how much precision the
tactic *actually* needs on the values `p(v)` and `p'(v)`.

This is the high-precision companion to [`TacticProfile.md`](TacticProfile.md), which profiled a
single ~57-digit invocation. The conclusions there (dominant costs: `hnum`, the `aeval`
expansions, `hz1`) describe the *low*-precision regime; at high precision the picture changes
qualitatively, and the "priority 3" suggestion there (dyadic interval arithmetic) becomes *the*
lever.

## Method

- **Workload.** `p = X⁶ − 2X − 2`, certifying a **mixed complex root** — both `Re` and `Im`
  non-zero. This is the worst case: the `Complex.mul_re`/`mul_im` cross-terms do not cancel,
  unlike the pure-real / pure-imaginary roots of the LMFDB polynomial `X⁶−5X⁴−50X²+125`, which
  *understate* the cost of `hz1` and the expansions. Degree 6, matching the real workload.
- **Per-step wall clock.** Each `evalTactic` inside the tactic (the two shared `have`s, the
  `refine`, and all 13 finishers) was temporarily wrapped with `IO.monoNanosNow` timers, plus
  sub-timers splitting the meta-level phase. True additive wall clock. Instrumentation reverted
  after measurement.
- **Precisions.** 100, 300, 1000, 3000, 10 000, 30 000 decimal digits. The approximation `v`
  and the inverse-Jacobian `M` are each printed with `D` decimal places (so the literals carry
  ~`D` significant digits — the scaling axis). The radius `r ≈ 10^{-(D-2)}` is chosen so the
  certificate is valid with margin.
- **Reproduction.** `scratchpad_gen_profile.sage <digits> <out.lean>` (repo root) emits a
  standalone test file; compile with `lake env lean <out.lean>`. Times below exclude the ~5 s
  fixed Mathlib import/elaboration overhead of a single-file `lake env lean` invocation (in
  `Test.lean` that overhead is amortized across many invocations).
- Measured on `leanprover/lean4` v4.32.0-rc1.

## Results — per-step wall clock vs. precision (ms)

| Step | 100 | 300 | 1 000 | 3 000 | 10 000 | 30 000 | scaling |
|------|----:|----:|------:|------:|-------:|-------:|---------|
| **meta-setup** (total)        | 6   | 15  | 91  | 602  | 5 904  | **50 000** | **~D¹·⁹** |
| &nbsp;&nbsp;↳ `ratToTerm p(v),p'(v)` | – | – | 71 | ~530 | 5 311 | **45 672** | ~D¹·⁹ |
| &nbsp;&nbsp;↳ `evalGaussian` (Horner) | – | – | 5 | ~9 | 111 | 530 | ~D¹·⁶ |
| &nbsp;&nbsp;↳ parse `v`+`p`, cert-args | – | – | 15 | ~63 | 388 | 2 967 | ~D¹·⁸ |
| **expand `hpv`** (`aeval p = A+Bi`)   | 401 | 400 | 474 | 877 | 4 660 | **34 789** | **~D¹·⁶** |
| **expand `hpdv`** (`aeval p' = C+Di`) | 334 | 334 | 388 | 705 | 3 716 | **27 942** | **~D¹·⁶** |
| refine assembly                       | 63  | 63  | 69  | 86  | 231   | 1 250  | ~D¹·⁶ |
| conv `hv0`+`hv1` (decimal→num/den)    | 85  | 84  | 92  | 110 | 260   | 1 256  | ~D¹·⁴ |
| finisher `hz1`                        | 478 | 451 | 457 | 483 | 572   | 953    | ~flat |
| finisher `hnum`                       | 405 | 400 | 408 | 414 | 426   | 489    | **flat** |
| finisher `hy0`+`hy1`                  | 149 | 143 | 148 | 162 | 202   | 441    | ~flat |
| other finishers¹                      | ~270| ~265| ~265| ~275| ~290  | ~360   | **flat** |
| **TOTAL (tactic)**                    | 2 208 | 2 171 | 2 403 | 3 727 | 16 258 | **117 484** | ~D¹·⁵ |
| wall (incl. ~5 s import overhead)     | 7.3 s | 7.3 s | 7.5 s | 8.9 s | 21.5 s | 123 s |  |

¹ `hpd`, `ha`, `hB`, `hr`, `hdeg`, `hrR`, `hyr`, `hzr`, `hB0`.

## Two regimes

Every cost falls cleanly into one of two classes:

- **A precision-independent floor (~1.3 s).** All the certificate finishers work on *small*
  numbers — `B` is rounded to 4 digits by `sqrtUpper … 4`, the coefficients are tiny — so
  `hnum`, `hpd`, `ha`, `hB`, and the degree/coercion checks barely move across the whole range.
  Below ~1000 digits this floor *is* the entire cost (total ≈ 2.2 s, flat).
- **Super-linear bignum costs.** Everything that *touches the D-digit value* grows steeply:
  the meta-level serialization of `p(v)`/`p'(v)` and the two `aeval` expansions that verify
  them. Past ~3000 digits these dominate and the total tracks them.

At 30 000 digits, **three steps are 96% of the runtime** — and all three are the same
underlying work:

| step | 30k time | % of total |
|------|---------:|-----------:|
| meta-setup (`ratToTerm`)      | 50.0 s | 43% |
| expand `hpv`                  | 34.8 s | 30% |
| expand `hpdv`                 | 27.9 s | 24% |
| — everything else —           | ~4.8 s | ~4% |

## The root cause: exact rationals with 6·D-digit denominators

`v = a / 10^D` (an integer `a` of ~`D` digits). For the degree-6 `p`,

```
p(v) = (a⁶ − 2a·10^{5D} − 2·10^{6D}) / 10^{6D}
```

The **value** is ≈ 10⁻ᴰ (it is the residual — `v` is near a root), but the exact reduced
fraction has a **~5·D-digit numerator over a 6·D-digit denominator**. At D = 30 000 that is a
~150 000-digit numerator. The tactic:

1. computes this exact value cheaply (`evalGaussian`, a Horner scheme over `ℚ×ℚ` — only 0.5 s
   even at 30k), then
2. **serializes it into numeral syntax** (`ratToTerm` → `toString` on the bignums + `Syntax`
   building) — **45.7 s**, i.e. 91% of the meta phase, and
3. proves `aeval (toComplex v) p = ↑A + ↑B·I` for those numerals via `simp`/`norm_num`, whose
   bignum arithmetic is the 35 s + 28 s of the two expansions.

**The meta bottleneck is serialization, not evaluation.** Base-10 conversion of an `N`-digit
integer is classically O(N²), matching the measured ~D¹·⁹ slope; Lean's kernel arithmetic (the
expansions) is better, ~D¹·⁶. Every one of these digits past ~`D` is meaningless, because `v`
itself is only known to `D` places.

## How much precision does the method really need?

Only **three** finishers consume `p(v)`/`p'(v)` (via `rw [hpv]` / `rw [hpdv]`): `hy0`, `hy1`
(use `p(v)`) and `hz1` (uses `p'(v)`). Everything else is arithmetic on the certificates
`(y, z₁, z₂, R, r, a, B)` and the coefficients — which is exactly why the floor is flat. So the
question reduces to how much precision those three need.

### `p(v)` (residual, → `hy0`/`hy1`): irreducibly ~D digits — but not 6·D

`hy0` proves `|M·p(v)| ≤ y = r/10`. The value `p(v)` *is* the residual, ≈ 10⁻ᴰ, compared against
a threshold ≈ 10⁻ᴰ. Certifying a root to radius `r` inherently requires resolving the residual to
precision ~`r`, so **~D significant digits is fundamental here.**

But the exact fraction carries it to *infinite* precision (all 6·D digits of the denominator).
A **D-digit dyadic enclosure** `p(v) ∈ [c − ε, c + ε]` with `ε ~ 10⁻ᴰ` is sufficient:
`|M·p(v)| ≤ |M·c| + ‖M‖·ε ≤ y`. That is ~6× smaller numerals, and since serialization and
verification are ~quadratic, **~36× cheaper** on the `ratToTerm`+`hpv` path.

### `p'(v)` (→ `hz1`): NOT irreducible — the precision is a free knob set far too tight

`hz1` proves `‖1 − M·p'(v)‖ ≤ z₁`, default `z₁ = r ≈ 10⁻ᴰ`. *That default* is what forces
`p'(v)` to ~D digits. But `z₁` is constrained **only** through `hyr` and `hzr` (verified against
`existsUnique_root_of_certificates` in `Certify.lean` — there is no standalone `z₁ < 1`):

- `hyr : y + z₁·r + z₂·r²/2 ≤ r`  ⟹  `z₁ ≤ (r − y − z₂r²/2)/r ≈ 0.9`  (with `y = r/10`)
- `hzr : z₁ + z₂·r < 1`           ⟹  `z₁ < 1 − z₂r ≈ 1`

So **`z₁` may be ~0.5 instead of 10⁻ᴰ** — about `D` orders of magnitude looser. At `z₁ = 0.5`,
`hz1` only needs `M·p'(v)` within `0.5` of `1`, i.e. `p'(v)` to **~1 significant digit**. `hpdv`
(28 s, 24% of the 30k run) then becomes essentially free — one would skip the exact expansion
entirely and discharge `hz1` from a 1-digit enclosure. This is valid because a merely *rough*
inverse `M` still satisfies the NK inequalities; the tight `z₁ = r` default buys nothing.

### Which subgoals rely on cancellation

Exactly `hy0`, `hy1`, `hz1`:

- **`hy0`/`hy1`** rely on `p(v)` being genuinely tiny — cancellation of `p` at the near-root.
  Inputs are O(1) (|root| ≈ 1.2), the result is 10⁻ᴰ, so ~`D` digits are lost to cancellation
  and ~D-digit *working* precision is needed to get the answer. **Irreducible.**
- **`hz1`** relies on `1 − M·p'(v)` being small — cancellation between `1` and `M·p'(v)`. But
  the *tolerance* is `z₁`, which is yours to set. Loosen it and the cancellation you must
  resolve shrinks from 10⁻ᴰ to ~0.5. **Not irreducible.**

`B` is safely trimmed to 4 digits for the same structural reason `z₁` could be: it enters
`hnum → z₂ → hyr/hzr` multiplied by `r²` (astronomical slack), so its precision is irrelevant.
`p(v)` and `p'(v)` sit against the *tight* thresholds `y = r/10` and `z₁ = r`, so with the
current defaults they cannot be trimmed — but one of those thresholds (`z₁`) is needlessly tight.

## Recommendations — two independent levers

1. **Loosen `z₁` to a fixed ~0.5** (cheap first move). Makes `p'(v)`/`hpdv` (28 s, ~24% of the
   30k-digit time) collapse to near-nothing on its own. Requires only a different default plus a
   low-precision `hz1` path — no interval machinery. Mathematically sound: `z₁` has no constraint
   beyond `hyr`/`hzr`, which admit `z₁ ≈ 0.9`.
2. **Dyadic / fixed-precision enclosures instead of exact `ℚ`** for `p(v)` (structural fix).
   Carry ~D digits, not 6·D. Attacks the residual path (`ratToTerm` + `hpv`) — the
   irreducible-but-currently-6×-oversized cost — for ~36× on those steps. This is the
   `TacticProfile.md` "priority 3" idea, now shown to be *the* dominant lever at high precision
   rather than a minor slice.

The `hnum` / `AlgHom` concerns from the 57-digit profile are **not** the high-precision story:
they are < 1% of the runtime at 30 000 digits and should be left alone.
