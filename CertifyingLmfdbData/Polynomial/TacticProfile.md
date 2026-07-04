# Profiling `unique_root_near`

Profile of the `unique_root_near` tactic (`CertifyingLmfdbData/Polynomial/Tactic.lean`),
aimed at finding where elaboration time is spent and whether exact rational arithmetic on
approximate (decimal) numbers is the bottleneck.

## Method

- **Per-side-goal wall clock.** Temporarily wrapped the shared-`have` loop and the finisher
  loop (`Tactic.lean`, the `for … in shares` and `for i in [0:checks.size]` dispatches) with
  `IO.monoNanosNow` timing around each `evalTactic`, logging the elapsed time per step. This is
  true wall clock and the numbers below are additive.
- **Tactic-category breakdown.** Ran the same invocation under `set_option profiler true` and
  read Lean's `cumulative profiling times` block. These per-category counters **overlap** (e.g.
  `typeclass inference` is nested inside `simp`), so they are *not* additive and not comparable
  to the wall-clock table — they only show relative category weight.
- **Workload.** All 7 real invocations in `AllRoots.lean`. Results were highly consistent;
  numbers below are for `uniqueRootNear_rroot1` (`myPoly`, degree 6, ~57-digit decimal
  approximation), representative of the rest. All instrumentation was reverted afterwards.
- **State measured.** Current tactic, i.e. *with* both optimizations below (shared evaluation +
  `eval`-based expansion). See the "Implemented" sections for the before/after of each.

## Results — per side goal (≈1.68 s total: ~0.38 s shared + ~1.31 s finishers)

| Step             | Time    | What it certifies / does                              |
|------------------|---------|-------------------------------------------------------|
| **hnum**         | ~477 ms | Lipschitz coeff-sum `≤ z₂` (untouched — now the largest single cost) |
| **hz1**          | ~291 ms | `‖1 − M·p'(v)‖ ≤ z₁`: `rw [hpdv]`, then `fin_cases`×2 + matrix + rational arith |
| *hpdv* (shared)  | ~212 ms | one `eval`-expansion of `p'` at `toComplex v` → `↑C + ↑D·I` |
| *hpv* (shared)   | ~165 ms | one `eval`-expansion of `p` at `toComplex v` → `↑A + ↑B·I` |
| **hpd**          | ~156 ms | derivative polynomial `= pd` (`norm_num […] <;> ring1`) |
| ha               | ~93 ms  | row-sum bound `‖M‖ ≤ a`                               |
| hy0              | ~64 ms  | residual `|(M·p(v))₀| ≤ y`: `rw [hpv]` + rational arith |
| hB               | ~63 ms  | `‖v‖ ≤ B`                                             |
| hy1              | ~59 ms  | residual `|(M·p(v))₁| ≤ y`: `rw [hpv]` + rational arith |
| hyr              | ~54 ms  | Newton–Kantorovich inequality                         |
| hr, hdeg, hrR, hzr, hB0 | ≤18 ms each | degree / coercions / contraction              |

`hnum` alone is now **~28%** of the total, and the two shared expansions plus `hz1` another
**~40%**. The residual goals `hy0`/`hy1` — formerly ~260 ms each when they re-expanded `aeval`
themselves — are now ~60 ms, doing only rational arithmetic against the shared `hpv`.

## Results — by tactic category (Lean `cumulative profiling times`, same invocation)

Overlapping counters (not additive); shown to indicate where the work concentrates.

| Category              | Cumulative | Note                                                     |
|-----------------------|-----------:|----------------------------------------------------------|
| `simp`                |   ~533 ms  | still the heaviest — bignum numeral normalization        |
| `typeclass inference` |   ~604 ms  | now almost entirely small aggregate lookups (`AddMonoidWithOne`, `CharZero`, `OfNat`, …); the `AlgHom` hom-class floor is gone |
| `norm_num`            |   ~265 ms  | exact rational inequality checking                       |
| type checking         |   ~238 ms  | checking the large numeric proof terms                   |

## Interpretation

The original hypothesis — *effort wasted running `norm_num` with precise calculations on
approximate numbers* — is correct in substance, but the target is broader than `norm_num`
alone:

- **The dominant cost is `simp`, not `norm_num`** (~533 ms vs ~265 ms). In `hz1` and the two
  shared expansions, `simp` expands the degree-6 polynomial at a complex point whose components
  are exact rationals with denominators `10^57`. Raising those to powers up to 6 produces
  numerators/denominators of hundreds of digits, and `simp` normalizes every numeral along the
  way. `norm_num` then re-does exact bignum rational arithmetic to verify the final `|…| ≤ y`.
- So **roughly 1 s of the ~1.68 s** (simp + norm_num + type-checking of their bignum output) is
  exact rational computation on numbers only meaningful to ~57 digits. This is exactly the waste
  dyadic interval arithmetic would eliminate: carry `hz1`/`hy0`/`hy1`/`ha`/`hB` (and the shared
  values) as fixed-precision dyadic enclosures and discharge the inequality by an interval
  comparison, instead of exact `ℚ` with 300-digit numerators.
- **`hnum` (~477 ms) is a different animal.** There the numbers are small (`B` is rounded to
  4 digits by `sqrtUpper … 4`); the cost is `norm_num` rewriting polynomial-coefficient lemmas
  (`coeff_add`, `coeff_C_mul`, `coeff_X_pow`, `Nat.choose`, …) to extract `pd.coeff`. Interval
  arithmetic will *not* help this goal; it wants a dedicated coefficient evaluator or
  precomputed coefficient hypotheses.
- **`hpd` (~156 ms)** is `norm_num <;> ring1` proving `derivative p = pd` — polynomial
  normalization, not a numeric-precision issue.
- **The `AlgHom` typeclass floor is now essentially gone** (see the two "Implemented" sections):
  the ~100 ms/expansion hom-class search that used to dominate `hy0`/`hy1`/`hz1` is no longer
  paid, and what remains is genuine bignum arithmetic.

## Why the `simp`s were slow (the diagnosis that motivated the two fixes below)

Isolating the `hy0`/`hz1` goals (see `ScratchProfile.lean`) and profiling variant finishers
under `profiler true` split the cost into two very different pieces. Piece 1 has since been
eliminated by the `eval`-based expansion; piece 2 was reduced.

### 1. A fixed ~100 ms/goal typeclass-inference floor from `aeval` — *now removed*

The goal contains `(aeval (toComplex v) p).re` with `p : ℚ[X]`. To push `aeval` inward, `simp`
(and `norm_num`) apply `map_add`/`map_mul`/`map_pow`, each of which must synthesize the
homomorphism-class instance for `aeval (toComplex v) : ℚ[X] →ₐ[ℚ] ℂ`. Those instance searches
dominate and are **identical no matter which finisher strategy is used**:

| instance search        | time    |
|------------------------|---------|
| `AddHomClass`          | ~34 ms  |
| `Module`               | ~31 ms  |
| `CoeFun` (`DFunLike`)  | ~16 ms  |
| `NPow`                 | ~20 ms  |
| **floor per goal**     | **~100 ms** |

This was the real bottleneck, and it is *not* the numeral arithmetic — it is the `ℚ`-algebra
`AlgHom` machinery around `aeval`. Because `hy0`, `hy1` and `hz1` each re-expanded the *same*
`aeval (toComplex v) p` (and `hz1` the derivative), the floor was paid ~3× per invocation. The
shared evaluation collapses that to 2× (once per polynomial), and the `eval`-based expansion
then removes the floor itself — measured `107 ms → 13 ms` of `Module`/`AddHomClass` search on
the real `rroot1` invocation (see "Implemented: `eval`-based expansion").

### 2. A variable simp/norm_num cost, worst for mixed roots

On top of the floor, the choice of tactic matters. Timings of `simp + norm_num` (ms), measured
on a real root, a pure-imaginary root, and a **mixed** root `-½ + (√3/2)i` of `(X²+X+1)³`
(the current polynomial `X⁶−5X⁴−50X²+125` is exceptional — all its roots are pure real or
pure imaginary, so the `Complex.mul_re/mul_im` cross-terms cancel and *understate* the cost):

| root type      | current `simp […] <;> norm_num` | `simp only [closed set] <;> norm_num` |
|----------------|--------------------------------:|--------------------------------------:|
| real           | 106 ms                          | 72 ms                                 |
| pure imaginary | 99 ms                           | 69 ms                                 |
| **mixed**      | **164 ms**                      | **116 ms**                            |

Two points:

- The unrestricted default `simp` set is wasteful; a closed `simp only` lemma list
  (the `aeval` push lemmas + the `Complex.re/im` lemmas + matrix accessors, verified to close
  real, imaginary **and** mixed goals) cuts the variable cost ~1.4–1.8×.
- A **mixed root is ~55 % more expensive** than the collapsing real/imaginary roots of the
  current polynomial (164 ms vs ~100 ms for the current tactic). Any general-purpose version of
  this tactic must be tuned against a mixed root, not the current special case.

## Suggested priorities

1. **Share the `aeval` evaluation across goals.** — *IMPLEMENTED, see below.*
   The companion *avoid the `ℚ`-algebra `AlgHom`* (evaluate via `Polynomial.eval` on `ℂ[X]`,
   using `ℂ`'s own ring structure to skip the `Module`/`AddHomClass` search) — *ALSO IMPLEMENTED,
   see "Implemented: `eval`-based expansion" below.* It attacks the ~100 ms floor itself.
2. **Replace `simp` with `simp only [closed set]`** in `hy0`/`hy1`/`hz1`/`ha`/`hB`. Verified to
   close real, imaginary and mixed goals; ~1.4–1.8× on the variable cost. Low-risk, immediate.
3. **Then** consider dyadic interval arithmetic for the final `|…| ≤ y` comparison (the original
   idea): once `aeval` is evaluated once to a concrete `⟨A, B⟩`, bounding `|M·⟨A,B⟩| ≤ y` by
   fixed-precision enclosures avoids the exact bignum rationals — but note this is now a smaller
   slice than the `aeval`-expansion floor.
4. Separately, give **hnum** a coefficient-extraction fast path (not intervals). This is now the
   single largest finisher (~470 ms) and is untouched.

## Implemented: shared `aeval` evaluation (priority 1)

`p` and its derivative are evaluated at `toComplex v` **once** each, at the meta level, as exact
Gaussian rationals (`evalGaussian`, a Horner scheme over `ℚ×ℚ` — valid because the coefficients
and `v` are rational). The tactic then proves, once, in the context shared by all side goals:

```
have hpv  : aeval (toComplex v) p        = ↑A + ↑B·I
have hpdv : aeval (toComplex v) (D p)    = ↑C + ↑D·I
```

Each is one `aeval` expansion: stating the value as a *complex number* and adding
`Complex.ext_iff` to the simp set makes the `re`/`im` split happen **after** the (typeclass-heavy)
homomorphism expansion, so the ~100 ms floor is paid once per polynomial rather than once per
goal. The finishers then `rw [hpv]` / `rw [hpdv]` and do pure rational arithmetic. Validated on
all 7 invocations *and* on a genuinely mixed value `p(0.3+0.9i)` (both parts nonzero).

**Measured (rroot1, representative):** the three `aeval` goals `hy0+hy1+hz1` drop from
**995 ms → 414 ms**; the shared step adds **~490 ms**; net **~90 ms/invocation (~5 %)** off a
~2.0 s total.

Why only ~5 %, not more: the win is exactly the *removed duplicate expansions* (`hy1`'s copy of
`p`, `hz1`'s second `fin_cases` copy of `pd`). Proving the shared value still costs one full
expansion **plus** the `norm_num` arithmetic on the ~57-digit rationals — and that arithmetic is
then partly repeated in the finishers. To go further you must attack the two untouched
heavyweights — `hnum` (~470 ms) and the per-expansion ~100 ms typeclass floor (priorities 4 and
1-`eval`) — not the residual goals, which are now cheap (~60 ms each).

## Implemented: `eval`-based expansion (priority 1-`eval`)

The two shared expansions above (`hpv`, `hpdv`) each proved `aeval (toComplex v) p = ↑A + ↑B·I`
by pushing the **bundled `ℚ`-algebra homomorphism** `aeval (toComplex v) : ℚ[X] →ₐ[ℚ] ℂ` inward
with `map_add`/`map_mul`/`map_pow` — every one of which forces a `FunLike`/hom-class instance
search (`AddHomClass (ℚ[X] →ₐ[ℚ] ℂ) …`, `Module ℚ ℂ`, …). That search wanders the whole exotic
morphism-class hierarchy and is the ~100 ms/expansion floor.

The fix rewrites, *before* expanding,

```
rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
--   aeval (toComplex v) p  ⟶  eval (toComplex v) (p.map (algebraMap ℚ ℂ))
```

so the expansion is now over `Polynomial.eval`/`Polynomial.map`, whose `eval_add`/`eval_mul`/
`map_add`/… simp lemmas are **direct** (no bundled hom, no hom-class search): they use `ℂ`'s own
ring structure. Rational coefficients survive as `eval_C`/`map_C` → `algebraMap ℚ ℂ q`, which
`norm_num` reduces. One line added to `expandTac`; the rest of the finisher machinery is unchanged.

**Measured, deterministic (`#count_heartbeats`, real `rroot1`, 57-digit approximation):**
**20 208 → 18 920 heartbeats, ~6.4 %** off the whole invocation. Per-category (profiler, same
declaration): the `Module`+`AddHomClass`+… *floor* drops **107 ms → 13 ms** (≈ −94 ms); total
`typeclass inference` **731 ms → 628 ms**; `simp`/`norm_num`/`type checking` essentially flat
(the bignum arithmetic is unchanged — it is the real remaining cost). Validated on all 7
invocations plus integer- and rational-coefficient (`C q`) polynomials and a mixed value.

Combined with the sharing, the `AlgHom` floor — flagged as *the* bottleneck in "Why the `simp`s
are slow" — is now paid essentially **zero** times per invocation instead of ~3×. What is left is
genuine exact rational arithmetic on ~57-digit numbers (`simp`+`norm_num`, ~1 s) and `hnum`
(~470 ms) — i.e. priorities 3 (dyadic intervals) and 4 (coefficient fast path) are now the only
remaining levers.

## Reproducing

The head-to-head finisher timings came from a throwaway `ScratchProfile.lean` (not committed —
it carries `set_option profiler` and would pollute every project build) containing, for each of
a real / pure-imaginary / mixed root, the `hy0`-shaped goal
`|M₀₀·(aeval (toComplex v) p).re + M₀₁·(aeval (toComplex v) p).im| ≤ y` proved by the current
finisher vs. a closed `simp only` set, under `set_option profiler true` /
`profiler.threshold 1`. The closed `simp only` set that closes all three root types is:

```
simp only [toComplex_apply, map_ofNat, map_pow, map_mul, map_sub, map_add, aeval_X,
  pow_succ, pow_zero,
  Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
  Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
  Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
  Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
  Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.zero_re,
  Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat,
  mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, neg_zero, sub_zero]
  <;> norm_num
```
