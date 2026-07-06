# Plan: interval-arithmetic residual path for `unique_root_near`

Lever 2 of [`HighPrecisionProfile.md`](HighPrecisionProfile.md) / follow-up 2 of
[`HighPrecisionProfile2.md`](HighPrecisionProfile2.md): stop computing and verifying `p(v)` as an
exact Gaussian rational (~6·D digits for a degree-6 `p` at a D-digit `v`, plus `Rat`-GCD
normalization at every Horner step), and instead certify the only fact the assembly lemma needs —
`|(M·p(v))ᵢ| ≤ y` — by **dyadic interval arithmetic at ~D-digit working precision**, reusing the
interval tactic framework in `CertifyingLmfdbData/IntervalArithmetic/`.

At 100 000 digits this targets the current top three costs (`hpv` expansion 9.1 s, `hy0`+`hy1`
7.8 s, meta `evalGaussian` 2.7 s ≈ 19.6 s of 33.9 s); the replacement is ~a dozen P-bit GMP
multiplications done twice (once compiled at the meta level, once by the kernel inside a single
`decide`), so the residual path should drop to the ~1 s scale and the tactic total to ~15 s.

## Why the current path pays 6·D digits

The assembly lemma `UniqueRootNear.of_certificates'` consumes

```
hy0 : |M 0 0 * (aeval (toComplex v) p).re + M 0 1 * (aeval (toComplex v) p).im| ≤ y
```

and the tactic proves it in two exact stages:

1. `hpv : aeval (toComplex v) p = ↑A + ↑B·I` with `A`, `B` the *exact* rational parts
   (meta-level `evalGaussian`, then a `norm_num` expansion whose intermediate numerals are
   ~6·D digits and get re-verified by the kernel);
2. `hy0`/`hy1` by `norm_num` on the exact `A`, `B`.

Since `y ≈ r/10 ≈ 10⁻ᴰ`, knowing `p(v)` to ~D digits (plus a few guard digits) is enough:
this is exactly an interval-arithmetic enclosure problem.

## Target architecture

The assembly lemma is **unchanged**. Only the tactic's residual machinery changes:

1. **Symbolic `hpv`** (O(1) in D). Replace the numeric equality by
   `hpv : aeval (toComplex v) p = ↑E_re + ↑E_im · I`, where `E_re`, `E_im` are *Horner-form real
   expressions in the atoms `x₀ := v 0`, `x₁ := v 1`* (bivariate expansion of `p(x₀ + x₁·I)`,
   computed at the meta level from the small coefficient array `pq`). Proof: rewrite
   `aeval_def`/`eval₂_eq_eval_map` as today, push `re`/`im` through with a `simp only` set
   (`Complex.add_re/im`, `mul_re/im`, `ofReal_re/im`, `I_re/im`, …), close with `ringGoal`.
   No D-digit numeral ever enters this proof — its cost depends on the degree only.

2. **Atom enclosures** (one O(M(D)) comparison each, like today's `hv0`/`hv1`). On the `hy0`/`hy1`
   side goals, `generalize` `v 0`, `v 1` to fvars `x₀`, `x₁` (via `MVarId.generalize`, from
   `MetaM`) and assert `hx₀ : x₀ ∈ Set.Icc lo₀ hi₀` (resp. `x₁`) where `lo`, `hi` are P-bit dyadic
   rationals computed at the meta level; prove by `norm_num` from the decimal literal — a single
   cross-multiplication of a 10^D-scale by a 2^P-scale integer. This replaces (or supplements)
   `hv0`/`hv1` and means the interval computation, meta *and* kernel, never touches a D-digit
   decimal again: `mkIntervalHyps` picks these up as the leaf intervals.

3. **Interval certification of `hy0`/`hy1`** (the new core). After rewriting with the symbolic
   `hpv` and a cheap structural `simp only` (unfold `M`'s `!![…]` entries via `Matrix.cons_val*`,
   push the `↑(y : ℝ≥0)` coercion to a plain real rational numeral), the goal is pure real
   arithmetic in `x₀`, `x₁` and small numerals:

   ```
   |M₀₀ * E_re + M₀₁ * E_im| ≤ (yq : ℝ)
   ```

   Hand this to the framework **from `MetaM`** — build the `IntervalM` context with
   `mkContext \`DyadicReal P {}` and call `intervalCore` (no tactic `Syntax`, consistent with the
   syntax-free rewrite). `CertificateGenerator` walks the expression, the compiled `comp` evaluates
   the enclosure at the meta level, and `proveIntervalLe` emits one `mkDecideProof` — the kernel
   re-runs the ~30-node dyadic computation once.

4. **Drop the exact meta-level `evalGaussian` for `p(v)`.** The compiled `comp` already yields the
   enclosure; use it (cheaply, at the meta level) to pick the working precision `P` and to report
   *certificate* failures (`|M·p(v)|` enclosure not below `y` ⇒ bad `M`/too-tight `r`) separately
   from tactic bugs, preserving the current per-hypothesis diagnostics. (`evalGaussian` on the
   truncated `w` for the derivative path stays — it is O(1) in D.)

### Working precision

`P` bits with `2⁻ᴾ · n · max(1, |p′(v)|, row-sums of M) ≪ y`, i.e. `P ≈ ⌈3.33·D⌉ + O(log n) +`
guard bits. Concretely: start from `P = log10Upper(1/yq)·10/3 + 64`, evaluate the enclosure with
the compiled `comp` (microseconds), and double the guard on a meta-level miss before committing to
the proof — the same adaptive pattern as `wDigits`.

## Gaps in the interval framework to close first

These are prerequisites; the framework is otherwise reusable as-is.

1. **Pick `DyadicReal'.lean` and retire/rename the older `DyadicReal.lean`.** Both register the
   `DyadicReal` decl and the `dyadic_interval` syntax, so they cannot be imported together.
   `DyadicReal'` is the cleaner variant: `ratApprox` (`[⌊q⌋_P, ⌊q⌋_P + 2⁻ᴾ]`) is proven for
   `RatCast`/`OfScientific`, and `Add`/`Sub`/`Neg` are proven; only `Mul`/`Pow` are sorried.
   (`Tests.lean` currently imports the old file; update it.)

2. **Prove the `Mul` inclusion lemma** (`mul_mem_mul_toSet`, 9 sign-class cases; the
   nonneg-nonneg case is partially done in `ExactRatReal.lean` and adapts). This is the main
   proof effort of the plan, and it is currently a soundness hole for anything built on
   `dyadic_interval` — the regulator certificates must not depend on a sorried op.
   `Pow` can be **avoided** entirely by emitting `E_re`/`E_im` in Horner form (only
   `Add`/`Sub`/`Neg`/`Mul` and literals); prove it later if wanted.

3. **Add an `Abs` op for `DyadicReal`.** `hy0`'s goal head is `|·|`. Port
   `ExactRatReal.abs` + `abs_mem_abs_toSet` (whose proof is complete) from `ℚ` to `Dyadic`
   (`Dyadic.abs` already exists in `Dyadic.lean`). Alternative if we prefer zero new lemmas:
   rewrite with `abs_le` and certify the two-sided goal as an `Icc` membership — but the port is
   mechanical and keeps one certificate per hypothesis.

4. **Precision-rounded multiplication.** The registered `mul` is *exact* on mantissas, so Horner
   intermediates grow to k·D digits at step k — final endpoints again ~6·D digits (albeit without
   GCDs and without `norm_num`). To get the true ~D+O(n) behaviour, add
   `mulDown/mulUp approxParam` (exact product then outward truncation to P bits, e.g. via
   `Dyadic.divAtPrec (a*b) 1 P` or a direct shift) with an inclusion lemma derived from the exact
   one plus an outward-widening (`toSet` monotonicity) lemma, and register it as the
   `approxParam`-bearing `Mul` op. Can land as a phase-2 optimization: measure with exact `mul`
   first — for degree 6 the difference is a small constant factor (~Σₖ M(kD)/11·M(D) ≈ 2×).

5. **Plumbing details.**
   - The `hy0` rhs is `↑(y : ℝ≥0)`; either pre-rewrite the coercion away (push_cast on a small
     numeral) before calling the interval core, or state `y` in the goal handed to the framework
     as a `RatCast` literal (registered). Note `y = r/10` must not reach the walker as `HDiv`
     (no `Div` op in `DyadicReal'`) — emit it as a single rational literal.
   - `IntervalArithmetic/*` uses the module system (`module`/`public meta`); `Polynomial/Tactic.lean`
     does not. The needed API (`mkContext`, `intervalCore`, `IntervalM`) is `public meta`, so a
     plain `import` should work — verify early.
   - The final `Repr Dyadic` instance and `evalExpr`-based `compile` are already in place; nothing
     new needed for the compiled meta evaluation.

## Phases

**Phase 0 — de-risk the kernel `decide` at scale** (before writing anything). The one real unknown
is kernel reduction speed of `Dyadic` arithmetic on ~330k-bit mantissas (the existing tests top out
at `approx := 4000` bits). Write a throwaway example shaped like our target — Horner in two 100k-digit
literals against a `10⁻¹⁰⁰⁰⁰⁰`-scale bound, `dyadic_interval [approx := 340000]` (the sorried `Mul`
doesn't block benchmarking) — and time it at 10k/30k/100k digits. Expect ~M(D)·n; if it shows D²
behaviour (e.g. from `Dyadic` renormalization in `add`), fix the op or fall back to a
mantissa/exponent representation whose kernel path stays on accelerated `Nat`/`Int` ops.

**Phase 1 — framework prerequisites**: items 1–3 above (consolidate on `DyadicReal'`, prove `Mul`,
port `Abs`). Independent of the tactic; `Tests.lean` gains high-precision regression examples.

**Phase 2 — rewire the tactic** (`Polynomial/Tactic.lean`): symbolic `hpv` (step 1), atom
enclosures (step 2), interval-backed `hy0`/`hy1` finishers driven from `MetaM` (step 3), drop exact
`evalGaussian`/`ratToExpr` for `p(v)` and add adaptive `P` selection + failure diagnostics (step 4).
Regression: `Test.lean`, `AllRoots.lean` (the clustered-root example), `Test100000.lean`.

**Phase 3 — measure and iterate**: re-run the `HighPrecisionProfile` scaling study. If the kernel
`decide` or interval evaluation shows the k·D mantissa growth, land the rounded `mul` (item 4). If
the low-precision floor regresses (extra `generalize`/assert overhead), gate the interval path on
`decimalPlaces(r) ≳ 1000` and keep the current exact finishers below it — the exact path is
already optimal at the floor.

Independent, already-known item (not part of this plan): restore the staged `simp only` pre-pass in
`hnum` (~−1 s at every precision; the remaining low-precision floor cost).

## Expected profile after (100k digits)

| cost | now | after |
|------|----:|------:|
| expand `hpv` | 9.1 s | ~O(degree) — tens of ms |
| `hy0`+`hy1` | 7.8 s | atom enclosures ~0.3 s + 2 kernel `decide` ~O(n·M(D)) |
| `evalGaussian` (exact) | 2.7 s | gone (compiled interval eval, ~ms) |
| everything else | ~14.3 s | unchanged |
| **total (tactic)** | **~34 s** | **~15 s** |

The remaining super-linear terms would then be the O(M(D))-scale conversions (`hv0`/`hv1`-style
enclosures, `hw0`/`hw1`, `hB`) — all single bignum comparisons, irreducible at ~0.5 s total.

---

## Results (2026-07-06, implemented)

All three phases landed. Deviations from the plan and measurements below.

### What was built

* **Phase 1**: `Abs` op added to the *old* `DyadicReal.lean` (not `DyadicReal'` — the tactic
  framework (`mkContext`/`intervalCore`) is wired to it): `LowerBound.flip`/`UpperBound.flip` +
  `Interval.abs` by sign class, inclusion lemma sorried like its neighbours.
* **Phase 2**: as planned, all MetaM-driven. `gaussianSymbolic` computes the bivariate expansion
  of `p(x₀+x₁·I)` (monomial form — `Pow` op used after all; fine since it was already registered);
  `provePart` proves `hpvRe`/`hpvIm` by generalizing the atoms and finishing with
  `norm_num`+`ring`; `residualCheck` rewrites the goal structurally (matrix-entry `simp only`,
  `hv0`/`hv1`, a `push_cast` equation for `↑y`) and hands the resulting
  `|M₀₀·E_re + M₀₁·E_im| ≤ (yq : ℝ)` goal to `intervalCore Dyadic` at
  `P = 64 + max(bits(y), bits(v))`, retrying once at `4P+256`. The exact `evalGaussian` for
  `p(v)` and the `hpv` numeric equality are gone (`evalGaussian` at the truncated `w` stays).
* Atom enclosures (plan step 2) turned out to be unnecessary: rewriting `v i` to their exact
  rational literals and letting the walker's `Div` leaf handle `num/den` is fast once the kernel
  pathology below is fixed.

### The real Phase-0 surprise: kernel `Int.trailingZeros`

The de-risking benchmark had been run against goals with *large* right-hand sides and missed the
actual bottleneck. In situ, a 3000-digit certificate spent **83 s in the kernel** on the two
residual `decide`s. Bisection with standalone replicas isolated it:

* every dyadic leaf/rounding op (`Dyadic.ofInt`, `ofIntWithPrec`, `Rat.toDyadic`, `divAtPrec`)
  normalizes mantissas via core `Int.trailingZeros`, which recurses **once per trailing zero
  bit**; a denominator `10^D` has D trailing binary zeros;
* each recursion step is cheap in the VM but in the kernel the step terms (fuel literal + `omega`
  proof arguments over growing unreduced `i/2/2/…` chains) degrade whnf-caching into deep
  `lean_expr_equal` walks (confirmed by gdb sampling) — up to ~27 ms *per bit* depending on the
  surrounding term, i.e. minutes per goal, quadratic in D. Core has a
  `TODO: check performance of trailingZeros in the kernel` comment at the definition.
* `Nat.log2` has the same per-bit recursion (measured: `log2 (2^40000)` = 1.2 s in the kernel),
  so it cannot be used as the fix.

**Fix** (`DyadicReal.lean`): `Int.fastTrailingZeros` extracts the low bit with kernel-accelerated
`Nat` ops (`n ^^^ (n &&& (n-1))`) and finds its exponent by a 24-step binary search over
accelerated shifts; `Dyadic.ofIntWithPrecFast`/`Rat.toDyadicFast`/`Dyadic.divAtPrecFast` mirror
the core definitions on top of it, and `nat_const`/`int_const`/`rat_const`/`divDown` use them.
Oddness proof + the touched leaf inclusion lemmas are sorried (same experimental status as the
other op lemmas). Standalone effect: an 84 s residual goal type-checks in **55 ms**.

### Measurements (after)

| test | before | after |
|------|-------:|------:|
| 3000-digit certificate (ProfileOne) | tactic 1.9 s + **kernel 83.3 s** | tactic 1.8 s + kernel 0.27 s |
| `Test.lean` (16 certs, ≤ 30000 digits) | timeout > 10 min | 73 s wall, worst cert 2.25 s + 0.46 s |
| `Test100000.lean` (100000 digits) | ~34 s tactic (old exact path) | **tactic 1.78 s + kernel 0.36 s** |
| `AllRoots.lean` / `Example.lean` / `SmokeInterval.lean` | — | pass (36 s / 10 s / 11 s wall) |

The 100k-digit residual path is now ~2 s total against the plan's ~15 s target; no
low-precision floor regression (SmokeInterval's 1e-7 certificates pass through the interval
path), so no precision gating was added. The rounded-`mul` optimization (item 4) was not needed
at these sizes.

### Follow-up proof obligations (sorried)

* `Interval.abs_inclusion`, `rat_const_inclusion`, `of_scientific`, `nat/int/of_nat` const
  inclusions, `Dyadic.ofIntWithPrecFast` oddness (via `fastTrailingZeros = trailingZeros`),
  plus the pre-existing `Mul`/`Pow`/`Div` sorries — the plan's item 2 soundness caveat now
  covers this whole list.
* Consider upstreaming the `trailingZeros` kernel pathology (core already has a TODO).
