# Plan: a `unique_root_near` tactic

**Goal:** a tactic that closes `UniqueRootNear (aeval · p) (toComplex v) r` given roughly
`(v, A_mat, z₂, R)` as certificates. The main work is *not* the metaprogramming — it is
refactoring the four proof obligations of `newton_kantorovich_fd` into reusable lemmas whose
remaining side goals are pure rational-arithmetic inequalities that `norm_num` can close
uniformly. Once that's done, the tactic itself is a thin `apply` + goal-dispatch wrapper.

## What the tactic must do

Looking at the per-root proofs in `DegSix` (`AllRoots.lean`), each `uniqueRootNear_*` currently
requires:

1. **Setup, per polynomial:** an explicit derivative (`myPoly_derivative`) and an explicit real
   form of the zero finder (`polyToZeroFinder_myPoly`).
2. **`hy`** — `‖A (polyToZeroFinder p v)‖₊ ≤ y`: rational arithmetic.
3. **`hz₁`** — `‖1 - A ∘ DF(v)‖₊ ≤ z₁`: op-norm bound on an explicit 2×2 rational matrix.
4. **`hz₂`** — the Lipschitz bound: currently ~40 lines of `taylor`/`polynomial_nf`/`grw` per
   root, the heavy part.
5. **Side conditions** `r ≤ R`, `y + z₁r + z₂r²/2 ≤ r`, `z₁ + z₂r < 1`, plus the
   `(1e-57 : ℝ) = ((1e-57 : ℝ≥0) : ℝ)` coercion dance and packaging through `ofZeroFinder`.

The certificate data is exactly `(v, A_mat, y, z₁, z₂, R, r)`; everything else should be
derivable by uniform automation.

## Step 1 — One assembly lemma (easy, do first)

Prove `UniqueRootNear.of_certificates` combining `newton_kantorovich_fd` + `ofZeroFinder` + the
`ℝ≥0` coercion rewrite, with `hasFDerivAt_polyToZeroFinder`, `continuous_polyToZeroFinderDeriv`,
and the finrank check baked in. Statement shape:

```lean
lemma UniqueRootNear.of_certificates (p : ℚ[X]) (v : Fin 2 → ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) {y z₁ z₂ R r : ℝ≥0}
    (hy : …) (hz₁ : …) (hz₂ : …) (hrR : r ≤ R)
    (hyr : y + z₁ * r + z₂ * r ^ 2 / 2 ≤ r) (hzr : z₁ + z₂ * r < 1) :
    UniqueRootNear (aeval · p) (toComplex v) r
```

This alone collapses `rtest1` + `uniqueRootNear_rroot1` into one application.

## Step 2 — Make each hypothesis a rational-arithmetic goal

This is the core refactoring. The pattern for all three: push the analysis into a general lemma
once, so the per-root residue is `norm_num`-closable.

- **`hy`:** the two components of `A.mulVec (polyToZeroFinder p v)` are explicit rationals once
  `p` is evaluated at `v 0 + v 1 * I`. Generalize `reducePoly` from proving function equality
  (`polyToZeroFinder p = zeroFinder`) to evaluation-at-a-point, so the tactic never needs a
  named `zeroFinder`. A simp set (`polyToZeroFinder`, `toComplex_apply`/`toComplex_symm_apply`,
  the `re`/`im` arithmetic lemmas, `Complex.I_pow_eq_pow_mod'`) + `ring_nf` + `norm_num` should
  do it; wrap as `reducePolyEval`.

- **`hz₁`:** prove once that
  `polyToZeroFinderDeriv p v = mulVecLin !![d.re, -d.im; d.im, d.re]` where
  `d = aeval (toComplex v) p.derivative` (this is what `polyToZeroFinderDeriv_apply_one_zero` /
  `..._zero_one` say, packaged as a matrix). Then `1 - A ∘ DF(v)` is an explicit 2×2 matrix and
  `opNorm_mulVecLin_le` (row sums) reduces `hz₁` to two rational inequalities — cleaner and
  cheaper than the current `opNorm_le_of_basisFun` + big `simp`.

- **`hz₂` (the big win):** replace the per-root `taylor`/`polynomial_nf` block with a
  once-and-for-all lemma bounding the Taylor coefficient sum in
  `polyToZeroFinderDeriv_lipschitzOn` directly from the coefficients of `p.derivative`. Using
  `(taylor c Q).coeff (k+1) = Q⁽ᵏ⁺¹⁾(c) / (k+1)!`, one gets

  ```
  ‖(taylor c Q).coeff (k+1)‖ ≤ ∑ⱼ (j.choose (k+1)) * |aⱼ| * B^(j-k-1)   for any B ≥ ‖c‖.
  ```

  Combined with:
  - `‖toComplex v‖ ≤ B` from `norm_toComplex_sq` + `nlinarith` (generalize the current `hc`
    blocks into a lemma `norm_toComplex_le_of_sq : v 0 ^ 2 + v 1 ^ 2 ≤ B ^ 2 → ‖toComplex v‖ ≤ B`),
  - `‖A‖ ≤ a` from row sums (`opNorm_mulVecLin_le`),
  - the existing `Real.sqrt_two_lt_d2` lemma,

  the final `hz₂` statement takes only rational hypotheses: the coefficient list of
  `p.derivative`, `B`, `a`, `R`, and asks `2 * 1.42 * a * (rational sum) ≤ z₂`. Per-root, the
  tactic proves the two inputs by `norm_num` and applies it. The derivative's coefficients can
  be extracted at elaboration time (or via `derivative` simp + `compute_degree!`), so no
  per-polynomial `myPolyDeriv` def is needed either.

## Step 3 — The tactic itself

- **Interface:** goal-directed. The user writes

  ```lean
  def uniqueRootNear_rroot1 : UniqueRootNear (aeval · myPoly) (toComplex ![…, …]) 1e-57 := by
    unique_root_near !![…, …; …, …] (z₂ := 40) (R := 1)
  ```

  The tactic parses `p`, `v`, `r` from the goal; `A_mat`, `z₂`, `R` come from the certificate;
  `y` and `z₁` can be defaulted (e.g. `y := r/10`, `z₁ := r` matches all current examples) with
  optional overrides.

- **Mechanics:** unfold `p` if it's a local def (accept a `simp only [myPoly]`-style unfolding
  first, or take the defining equation as an argument), `apply UniqueRootNear.of_certificates`,
  then dispatch each side goal to its designated finisher (`reducePolyEval`-style simp +
  `norm_num`). No search — every goal has a known closer.

- **Error reporting:** when a numeric check fails, name the failing hypothesis (`hyr`, `hzr`,
  `hy`, …) so the user knows whether the certificate is bad (`A` too inaccurate, `z₂` too
  small, `r` too tight) vs. a tactic bug.

## Step 4 — Certificate generation + validation

- Extend `sage_code` to emit, per root of `p`: the decimal approximation `v`, the rounded
  inverse-Jacobian `A_mat`, and validated `z₂, R` (and `y, z₁` if not defaulted) as
  ready-to-paste Lean.
- Port all of `DegSix` (4 real + 1 complex root) to the tactic as the test suite; keep `conj`
  for the conjugate root (it's free) but the evenness shortcuts (`existsUnique_root_neg`) can
  probably be dropped once per-root certification is cheap.
- Profile: degree-6 evaluation at 60-digit decimals means ~350-digit rationals in `norm_num`.
  The existing proofs already survive this, but if it's a bottleneck, options are (a) truncate
  root approximations to the minimum precision the NK inequalities need, or (b) a small
  `norm_num` extension that does the sup-norm/row-sum checks in kernel `Nat` arithmetic.

## Step 5 (optional, later) — Shrink the certificate to just the root

Since `DF(v)` is an explicit rational 2×2 matrix, the tactic could compute `A_mat` itself in
meta code (exact rational inverse, rounded), and likewise derive tight `y, z₁, z₂` by
evaluating the same rational expressions it's about to prove. Then the entire certificate is
just the decimal approximation of the root — which fits the regulator-pipeline goal of keeping
statements tactic-generatable. Defer this until the explicit-certificate version works, since
it adds meta-level numerics without changing the proof skeleton.

## Suggested order of attack

Step 2's `hz₂` lemma first (it's the riskiest and the biggest deduplication — it deletes the
three near-identical 40-line blocks), then Step 1's assembly lemma, then verify by rewriting
one root of `DegSix` manually with the new lemmas before writing any metaprogram. If the manual
version of `uniqueRootNear_rroot1` fits in ~10 lines of `apply` + `norm_num`, the tactic is
guaranteed to be straightforward.
