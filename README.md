# Certifying tight bounds on regulators

This is the repository for a project on certifying tight bounds on regulators, part of the [Bridging Lean and the LMFDB](https://multramate.github.io/lean-lmfdb/) workshop taking place in Norwich from Monday, 29 June 2026 to Friday, 3 July 2026.

The main result obtained during the week can be found in `CertifyingLmfdbData.SexticExample`
for the specific number field `K` associated to `x^6 - 5*x^4 - 50*x^2 + 125` ([LMFDB page](https://www.lmfdb.org/NumberField/6.4.19208000.1)).

```lean
-- The regulator of `K` is within `10^-10` of `15.959695183485`
theorem regulator_mem (grh : GeneralizedRiemannHypothesis DegSix.K₆) (rh : RiemannHypothesis) :
    |regulator K - 15.959695183485| < 1e-10 := by
  exact (classNumberFormula grh rh).2.1
```

It is conditional on GRH, the fact that a given list of norms corresponds to
the norms of all the prime ideals of `K` with norm `< 1000`, a theorem of Belabas and Friedman
on approximations of the residue of the Dedekind zeta function and the Newton–Kantorovich theorem (TODO cite Lean proof). GRH and RH appear as explicit hypotheses; the remaining assumptions are stated as axioms. A key element of the proof is the Class Number Formula, which allows one to upgrade approximations of the quantities appearing in it to exact values when they are integers, and to refine precision when they are real.