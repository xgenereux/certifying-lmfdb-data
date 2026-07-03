/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import CertifyingLmfdbData.IntervalArithmetic.Dyadic

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.Real.Pi.Leibniz
public import Mathlib.Analysis.SpecificLimits.Normed
public import CertifyingLmfdbData.IntervalArithmetic.Core
public import CertifyingLmfdbData.IntervalArithmetic.Dyadic
public import CertifyingLmfdbData.IntervalArithmetic.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
## `dyadic_interval` tactic

This file impliments the `dyadic_interval` tactics for solving real inequalities and interval
containment goals using interval arithmetic (with dyadic approximations).

-/

@[expose] public section

open Nat

namespace IntervalArithmetic

meta section Elab

instance : Repr Dyadic where
  reprPrec d := reprPrec d.toRat
open Lean Expr Meta Elab Command Tactic

syntax (name := dyadic_interval) "dyadic_interval" ("[" interval_setting,*"]")? : tactic

@[tactic dyadic_interval]
def DyadicInterval : Tactic
  | `(tactic| dyadic_interval $[[$settings?:interval_setting,*]]?) => withMainContext do
    let default := 0
    let (opConfig, approxParam) := ← do
      if let some settings := settings? then
        let (opConfig, n?) ← intervalSettingParser `DyadicReal settings.getElems
        let approxParam := if let some n := n? then n else default
        pure (opConfig, approxParam)
      else
        pure ({}, default)
    intervalTactic Dyadic `DyadicReal opConfig approxParam
  | _ => throwUnsupportedSyntax

end Elab

def dyadic_to_real : Dyadic → ℝ := fun x ↦ x.toRat

@[interval_arithmetic_decl DyadicReal]
theorem strictMono_dyadic_to_real : StrictMono dyadic_to_real := by
  intro x y hxy
  simp [dyadic_to_real, hxy]

/- Numerals -/

def nat_const (n : ℕ) : Interval Dyadic :=
  ⟨some ⟨true, (n : Dyadic)⟩, some ⟨true, (n : Dyadic)⟩⟩

@[interval_op DyadicReal NatCast]
theorem nat_cast_inclusion (n : ℕ) : ↑n ∈ (nat_const n).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, Dyadic.toRat_natCast,
    dyadic_to_real]

@[interval_op DyadicReal OfNat]
theorem of_nat_inclusion (n : ℕ) : (OfNat.ofNat n) ∈ (nat_const n).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, nat_const, Dyadic.toRat_natCast,
    Semiring.toGrindSemiring_ofNat, dyadic_to_real]

def int_const (z : ℤ) : Interval Dyadic :=
  ⟨some ⟨true, (z : Dyadic)⟩, some ⟨true, (z : Dyadic)⟩⟩

@[interval_op DyadicReal IntCast]
theorem int_const_inclusion (z : ℤ) : ↑z ∈ (int_const z).toSet dyadic_to_real := by
  simp [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, int_const, Dyadic.toRat_intCast,
    dyadic_to_real]

def rat_const (approxParam : ℕ) (q : ℚ) : Interval Dyadic :=
  ⟨some ⟨true, q.toDyadic approxParam⟩, some ⟨true, -(-q).toDyadic approxParam⟩⟩

@[interval_op DyadicReal RatCast]
theorem rat_const_inclusion (approxParam : ℕ) (q : ℚ) :
    ↑q ∈ (rat_const approxParam q).toSet dyadic_to_real := by
  rw [Interval.mem_toSet]
  refine ⟨?_, ?_⟩
  · show ((q.toDyadic approxParam).toRat : ℝ) ≤ (q : ℝ)
    have h : (q.toDyadic approxParam).toRat ≤ q := Rat.toRat_toDyadic_le
    exact_mod_cast h
  · show (q : ℝ) ≤ ((-(-q).toDyadic approxParam).toRat : ℝ)
    have h : ((-q).toDyadic approxParam).toRat ≤ -q := Rat.toRat_toDyadic_le
    have hc : (((-q).toDyadic approxParam).toRat : ℝ) ≤ -(q : ℝ) := by exact_mod_cast h
    rw [Dyadic.toRat_neg]
    push_cast
    linarith

@[interval_op DyadicReal OfScientific]
theorem rat_of_scientific_inclusion (approxParam : ℕ) (m : ℕ) (s : Bool) (e : ℕ) :
    ↑(OfScientific.ofScientific (α := ℝ) m s e)
      ∈ (rat_const approxParam (Rat.ofScientific m s e)).toSet dyadic_to_real := by
  exact rat_const_inclusion _ _

/- Exact Operations -/

def Interval.add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | ⊥, _ | _, ⊥ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩
  ub := match x.ub, y.ub with
    | ⊤, _ | _, ⊤ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ + a₂⟩

@[interval_op DyadicReal Add]
theorem dyadic_add_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    (r + s) ∈ (x.add y).toSet dyadic_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.add,
    dyadic_to_real] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.lb
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.ub
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;> simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def Interval.sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | ⊥, _ | _, ⊤ => ⊥
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩
  ub := match x.ub, y.lb with
    | ⊤, _ | _, ⊥ => ⊤
    | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ => some ⟨c₁ && c₂, a₁ - a₂⟩

@[interval_op DyadicReal Sub]
theorem dyadic_sub_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    (r - s) ∈ (x.sub y).toSet dyadic_to_real := by
  simp only [Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds, Interval.sub,
    dyadic_to_real] at hrx hsy ⊢
  constructor
  · cases hx : x.lb <;> cases hy : y.ub
    case left.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp
  · cases hx : x.ub <;> cases hy : y.lb
    case right.some.some b₁ b₂ =>
      cases h₁ : b₁.1 <;> cases h₂ : b₂.1 <;>
       simp [hx, hy, h₁, h₂] at hrx hsy ⊢ <;> grind
    all_goals simp

def Interval.neg (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.ub with
    | ⊤ => ⊥
    | some ⟨c, a⟩ => some ⟨c, -a⟩
  ub := match x.lb with
    | ⊥ => ⊤
    | some ⟨c, a⟩ => some ⟨c, -a⟩

@[interval_op DyadicReal Neg]
theorem neg_inclusion {r : ℝ} (x : Interval Dyadic) (hrx : r ∈ x.toSet dyadic_to_real) :
    -r ∈ (x.neg.toSet dyadic_to_real) := by
  simp only [Interval.neg, Interval.mem_toSet, LowerBound.Bounds, UpperBound.Bounds,
    dyadic_to_real] at hrx ⊢
  constructor
  · cases hx : x.ub <;> simp [hx] at hrx ⊢; grind
  · cases hx : x.lb <;> simp [hx] at hrx ⊢; grind

section Mul

inductive IntervalSignClass
  | nonneg
  | nonpos
  | mixed

def Interval.toIntervalSignClass (x : Interval Dyadic) : IntervalSignClass :=
  let zero_lb : LowerBound Dyadic := some ⟨true, 0⟩
  let zero_ub : UpperBound Dyadic := some ⟨true, 0⟩
  if zero_lb ≤ x.lb then .nonneg
  else if x.ub ≤ zero_ub then .nonpos
  else .mixed

def LowerBound.mul (lb₁ lb₂ : LowerBound Dyadic) : LowerBound Dyadic :=
  match lb₁, lb₂ with
  | ⊥, ⊥ => ⊥
  | some ⟨c, a⟩, ⊥ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | ⊥, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊥
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def UpperBound.mul (ub₁ ub₂ : UpperBound Dyadic) : UpperBound Dyadic :=
  match ub₁, ub₂ with
  | ⊤, ⊤ => ⊤
  | ⊤, some ⟨c, a⟩ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c, a⟩, ⊤ => if a = 0 ∧ c then some ⟨true, 0⟩ else ⊤
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then some ⟨true, 0⟩
      else if a₂ = 0 ∧ c₂ then some ⟨true, 0⟩
      else some ⟨c₁ && c₂, a₁ * a₂⟩

def Interval.mul (x y : Interval Dyadic) : Interval Dyadic :=
  match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg => ⟨x.lb.mul y.lb, x.ub.mul y.ub⟩
  | .nonneg, .nonpos => ⟨x.ub.toLowerBound.mul y.lb, x.lb.toUpperBound.mul y.ub⟩
  | .nonneg, .mixed => ⟨x.ub.toLowerBound.mul y.lb, x.ub.mul y.ub⟩
  | .nonpos, .nonneg => ⟨x.lb.mul y.ub.toLowerBound, x.ub.mul y.lb.toUpperBound⟩
  | .nonpos, .nonpos => ⟨x.ub.mul y.ub |>.toLowerBound, x.lb.mul y.lb |>.toUpperBound⟩
  | .nonpos, .mixed => ⟨x.lb.mul y.ub.toLowerBound, x.lb.mul y.lb |>.toUpperBound⟩
  | .mixed, .nonneg => ⟨x.lb.mul y.ub.toLowerBound, x.ub.mul y.ub⟩
  | .mixed, .nonpos => ⟨x.ub.toLowerBound.mul y.lb, x.lb.mul y.lb |>.toUpperBound⟩
  | .mixed, .mixed =>
      ⟨min (x.lb.mul y.ub.toLowerBound) (x.ub.toLowerBound.mul y.lb),
       max (x.lb.mul y.lb |>.toUpperBound) (x.ub.mul y.ub)⟩

lemma dyadic_to_real_zero : dyadic_to_real 0 = 0 := by simp [dyadic_to_real]

@[simp]
lemma dyadic_to_real_mul (a b : Dyadic) :
    dyadic_to_real (a * b) = dyadic_to_real a * dyadic_to_real b := by
  simp [dyadic_to_real]

lemma dyadic_to_real_nonneg {a : Dyadic} (h : 0 ≤ a) : 0 ≤ dyadic_to_real a := by
  have := strictMono_dyadic_to_real.monotone h
  simpa [dyadic_to_real_zero] using this

lemma dyadic_to_real_nonpos {a : Dyadic} (h : a ≤ 0) : dyadic_to_real a ≤ 0 := by
  have := strictMono_dyadic_to_real.monotone h
  simpa [dyadic_to_real_zero] using this

lemma dyadic_to_real_pos {a : Dyadic} (h : 0 < a) : 0 < dyadic_to_real a := by
  have := strictMono_dyadic_to_real h
  simpa [dyadic_to_real_zero] using this

/-- The zero lower bound `[0`.  Defined so comparisons pick the `WithBot` order instance. -/
def zeroLB : LowerBound Dyadic := some ⟨true, 0⟩
/-- The zero upper bound `0]`.  Defined so comparisons pick the `WithTop` order instance. -/
def zeroUB : UpperBound Dyadic := some ⟨true, 0⟩

/- The sign-class conditions, phrased with `zeroLB`/`zeroUB` so that the `≤` picks the correct
order instance (matching what `split_ifs` produces from the definition). -/

lemma Interval.zeroLB_le_lb_of_nonneg {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .nonneg) : zeroLB ≤ x.lb := by
  rw [Interval.toIntervalSignClass] at hx
  split_ifs at hx with g1 g2 <;> first | exact IntervalSignClass.noConfusion hx | exact g1

lemma Interval.ub_le_zeroUB_of_nonpos {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .nonpos) : x.ub ≤ zeroUB := by
  rw [Interval.toIntervalSignClass] at hx
  split_ifs at hx with g1 g2 <;> first | exact IntervalSignClass.noConfusion hx | exact g2

lemma Interval.lb_le_zeroLB_of_mixed {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .mixed) : x.lb ≤ zeroLB := by
  rw [Interval.toIntervalSignClass] at hx
  split_ifs at hx with g1 g2 <;>
    first | exact IntervalSignClass.noConfusion hx | exact (not_le.mp g1).le

lemma Interval.zeroUB_le_ub_of_mixed {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .mixed) : zeroUB ≤ x.ub := by
  rw [Interval.toIntervalSignClass] at hx
  split_ifs at hx with g1 g2 <;>
    first | exact IntervalSignClass.noConfusion hx | exact (not_le.mp g2).le

/- Sign of a member of a nonneg/nonpos interval, via `bounds_of_bounds`. -/

lemma Interval.nonneg_of_mem_nonneg_toSet {r : ℝ} {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .nonneg) (hrx : r ∈ x.toSet dyadic_to_real) : 0 ≤ r := by
  have := LowerBound.bounds_of_bounds strictMono_dyadic_to_real
    (Interval.zeroLB_le_lb_of_nonneg hx) hrx.1
  simpa [zeroLB, LowerBound.Bounds, dyadic_to_real_zero] using this

lemma Interval.nonpos_of_mem_nonpos_toSet {r : ℝ} {x : Interval Dyadic}
    (hx : x.toIntervalSignClass = .nonpos) (hrx : r ∈ x.toSet dyadic_to_real) : r ≤ 0 := by
  have := UpperBound.bounds_of_bounds strictMono_dyadic_to_real
    (Interval.ub_le_zeroUB_of_nonpos hx) hrx.2
  simpa [zeroUB, UpperBound.Bounds, dyadic_to_real_zero] using this

/- Value-sign of the far endpoint, derived from membership. -/

lemma Interval.zeroUB_le_ub_of_mem {r : ℝ} {x : Interval Dyadic}
    (hr : 0 ≤ r) (hrx : x.ub.Bounds dyadic_to_real r) : zeroUB ≤ x.ub := by
  rcases hu : x.ub with _ | ⟨c, a⟩
  · exact le_top
  · rw [hu] at hrx
    have ha : (0 : Dyadic) ≤ a := by
      have h : (0 : ℝ) ≤ dyadic_to_real a := by
        cases c <;> simp [UpperBound.Bounds] at hrx <;> linarith
      rw [← dyadic_to_real_zero] at h; exact strictMono_dyadic_to_real.le_iff_le.mp h
    have hane : c = false → (0 : Dyadic) < a := by
      intro hc; rw [hc] at hrx; simp [UpperBound.Bounds] at hrx
      have h : (0 : ℝ) < dyadic_to_real a := lt_of_le_of_lt hr hrx
      rw [← dyadic_to_real_zero] at h; exact strictMono_dyadic_to_real.lt_iff_lt.mp h
    rw [zeroUB]
    cases c
    · exact WithTop.coe_le_coe.mpr (by simpa using hane rfl)
    · exact WithTop.coe_le_coe.mpr (by simpa using ha)

lemma Interval.lb_le_zeroLB_of_mem {r : ℝ} {x : Interval Dyadic}
    (hr : r ≤ 0) (hrx : x.lb.Bounds dyadic_to_real r) : x.lb ≤ zeroLB := by
  rcases hl : x.lb with _ | ⟨c, a⟩
  · exact bot_le
  · rw [hl] at hrx
    have ha : a ≤ (0 : Dyadic) := by
      have h : dyadic_to_real a ≤ 0 := by
        cases c <;> simp [LowerBound.Bounds] at hrx <;> linarith
      rw [← dyadic_to_real_zero] at h; exact strictMono_dyadic_to_real.le_iff_le.mp h
    have hane : c = false → a < (0 : Dyadic) := by
      intro hc; rw [hc] at hrx; simp [LowerBound.Bounds] at hrx
      have h : dyadic_to_real a < 0 := lt_of_lt_of_le hrx hr
      rw [← dyadic_to_real_zero] at h; exact strictMono_dyadic_to_real.lt_iff_lt.mp h
    rw [zeroLB]
    cases c
    · exact WithBot.coe_le_coe.mpr (by simpa using hane rfl)
    · exact WithBot.coe_le_coe.mpr (by simpa using ha)

/-- Reduce `zeroLB ≤ some ⟨c, a⟩` to `0 ≤ a`. -/
lemma zeroLB_le_coe {c : Bool} {a : Dyadic} (h : zeroLB ≤ (some ⟨c, a⟩ : LowerBound Dyadic)) :
    (0 : Dyadic) ≤ a := by rw [zeroLB] at h; simpa using WithBot.coe_le_coe.mp h

/-- Reduce `zeroUB ≤ some ⟨c, a⟩` to `0 ≤ a`. -/
lemma zeroUB_le_coe {c : Bool} {a : Dyadic} (h : zeroUB ≤ (some ⟨c, a⟩ : UpperBound Dyadic)) :
    (0 : Dyadic) ≤ a := by
  rw [zeroUB] at h; have hh := WithTop.coe_le_coe.mp h
  cases c <;> simp [FiniteUpperBound.le_def] at hh <;> first | exact hh | exact hh.le

/- Building block: lower bound of a nonneg × nonneg product. -/

lemma LowerBound.mul_bounds_nonneg {r s : ℝ} {l₁ l₂ : LowerBound Dyadic}
    (h1 : zeroLB ≤ l₁) (h2 : zeroLB ≤ l₂)
    (hr : l₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    (l₁.mul l₂).Bounds dyadic_to_real (r * s) := by
  rcases l₁ with _ | ⟨c₁, a₁⟩ <;> rcases l₂ with _ | ⟨c₂, a₂⟩
  · exact (WithBot.not_coe_le_bot _ h1).elim
  · exact (WithBot.not_coe_le_bot _ h1).elim
  · exact (WithBot.not_coe_le_bot _ h2).elim
  · have ha₁ : 0 ≤ a₁ := zeroLB_le_coe h1
    have ha₂ : 0 ≤ a₂ := zeroLB_le_coe h2
    have hn₁ := dyadic_to_real_nonneg ha₁
    have hn₂ := dyadic_to_real_nonneg ha₂
    have hp₁ : a₁ = 0 ∨ 0 < dyadic_to_real a₁ := (eq_or_lt_of_le ha₁).imp Eq.symm dyadic_to_real_pos
    have hp₂ : a₂ = 0 ∨ 0 < dyadic_to_real a₂ := (eq_or_lt_of_le ha₂).imp Eq.symm dyadic_to_real_pos
    cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [LowerBound.mul, LowerBound.Bounds, hc₁, hc₂, hz₁, hz₂,
        dyadic_to_real_mul, dyadic_to_real_zero] at hr hs ⊢ <;>
      grind [mul_nonneg, mul_le_mul, mul_lt_mul, mul_lt_mul', mul_pos,
        dyadic_to_real_zero, dyadic_to_real_mul]

/- Building block: lower bound `x.ub.toLowerBound * y.lb` (nonneg × nonpos / mixed × nonpos). -/
lemma LowerBound.mul_toLowerBound_bounds_left {r s : ℝ} {u₁ : UpperBound Dyadic}
    {l₂ : LowerBound Dyadic} (hu0 : zeroUB ≤ u₁) (hs0 : s ≤ 0)
    (hr : u₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    (u₁.toLowerBound.mul l₂).Bounds dyadic_to_real (r * s) := by
  rcases u₁ with _ | ⟨c₁, a₁⟩ <;> rcases l₂ with _ | ⟨c₂, a₂⟩
  · simp [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds]
  · simp only [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds, UpperBound.Bounds] at hs ⊢
    cases hc₂ : c₂ <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [hc₂, hz₂, dyadic_to_real_zero] at hs ⊢ <;>
      first | trivial | (have : s = 0 := le_antisymm hs0 hs; simp [this, dyadic_to_real_zero])
  · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe hu0)
    simp only [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds, UpperBound.Bounds] at hr ⊢
    cases hc₁ : c₁ <;> by_cases! hz₁ : a₁ = 0 <;>
      simp [hc₁, hz₁, dyadic_to_real_zero] at hr ⊢ <;>
      first | trivial | nlinarith [mul_nonneg (neg_nonneg.mpr hr) (neg_nonneg.mpr hs0)]
  · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe hu0)
    have hb₂ : dyadic_to_real a₂ ≤ 0 := by
      cases hc₂ : c₂ <;> simp [LowerBound.Bounds, hc₂] at hs <;> linarith
    have hs₁ : c₁ = false → 0 < dyadic_to_real a₁ := by
      intro hc; rw [hc, zeroUB] at hu0
      exact dyadic_to_real_pos (by simpa [FiniteUpperBound.le_def] using WithTop.coe_le_coe.mp hu0)
    have hp₁ : a₁ = 0 ∨ 0 < dyadic_to_real a₁ :=
      (eq_or_lt_of_le (zeroUB_le_coe hu0)).imp Eq.symm dyadic_to_real_pos
    have hp₂ : a₂ = 0 ∨ dyadic_to_real a₂ < 0 := by
      rcases eq_or_lt_of_le hb₂ with h | h
      · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
      · exact Or.inr h
    cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds, UpperBound.Bounds,
        hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
        reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
      (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
      first
      | exact absurd (hs₁ hc₁) (by rw [hz₁]; simp [dyadic_to_real_zero])
      | (rcases lt_or_eq_of_le hs0 with hslt | rfl
         · nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ - r by linarith)
             (show (0:ℝ) < -s by linarith), hr, hs, ha₁, hb₂, hs0]
         · nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ by linarith)
             (show (0:ℝ) < -dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂])
      | (have hd : (0:ℝ) ≤ dyadic_to_real a₁ - r := by linarith
         have he : (0:ℝ) ≤ s - dyadic_to_real a₂ := by linarith
         nlinarith [mul_nonneg (neg_nonneg.mpr hs0) hd, mul_nonneg ha₁ he, hr, hs, ha₁, hb₂, hs0])

/-- Reduce `some ⟨c, a⟩ ≤ zeroLB` to `a ≤ 0`. -/
lemma coe_le_zeroLB {c : Bool} {a : Dyadic}
    (h : (↑(⟨c, a⟩ : FiniteLowerBound Dyadic) : LowerBound Dyadic) ≤ zeroLB) : a ≤ (0 : Dyadic) := by
  rw [zeroLB] at h; have hh := WithBot.coe_le_coe.mp h
  cases c <;> simp [FiniteLowerBound.le_def] at hh <;> first | exact hh | exact hh.le

/-- Reduce `some ⟨c, a⟩ ≤ zeroUB` to `a ≤ 0`. -/
lemma coe_le_zeroUB {c : Bool} {a : Dyadic}
    (h : (↑(⟨c, a⟩ : FiniteUpperBound Dyadic) : UpperBound Dyadic) ≤ zeroUB) : a ≤ (0 : Dyadic) := by
  rw [zeroUB] at h; have hh := WithTop.coe_le_coe.mp h
  cases c <;> simp [FiniteUpperBound.le_def] at hh <;> first | exact hh | exact hh.le

lemma LowerBound.mul_comm (l₁ l₂ : LowerBound Dyadic) : l₁.mul l₂ = l₂.mul l₁ := by
  rcases l₁ with _ | ⟨c₁, a₁⟩ <;> rcases l₂ with _ | ⟨c₂, a₂⟩ <;>
    simp only [LowerBound.mul] <;>
    first
    | rfl
    | (split_ifs <;> first | rfl | (rw [mul_comm, Bool.and_comm]) | grind)

lemma UpperBound.mul_comm (u₁ u₂ : UpperBound Dyadic) : u₁.mul u₂ = u₂.mul u₁ := by
  rcases u₁ with _ | ⟨c₁, a₁⟩ <;> rcases u₂ with _ | ⟨c₂, a₂⟩ <;>
    simp only [UpperBound.mul] <;>
    first
    | rfl
    | (split_ifs <;> first | rfl | (rw [mul_comm, Bool.and_comm]) | grind)

/- Building block: lower bound `x.ub.toLowerBound * y.lb`, nonneg-`r` case. -/
lemma LowerBound.mul_toLowerBound_bounds_left_of_nonneg {r s : ℝ} {u₁ : UpperBound Dyadic}
    {l₂ : LowerBound Dyadic} (hu0 : zeroUB ≤ u₁) (hl0 : l₂ ≤ zeroLB) (hr0 : 0 ≤ r)
    (hr : u₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    (u₁.toLowerBound.mul l₂).Bounds dyadic_to_real (r * s) := by
  rcases u₁ with _ | ⟨c₁, a₁⟩ <;> rcases l₂ with _ | ⟨c₂, a₂⟩
  · simp [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds]
  · have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB hl0)
    simp only [UpperBound.toLowerBound, LowerBound.mul]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [LowerBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hs ⊢
      exact mul_nonneg hr0 hs
    · exact LowerBound.bot_Bounds _ _
  · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe hu0)
    simp only [UpperBound.toLowerBound, LowerBound.mul]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [LowerBound.Bounds, UpperBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hr ⊢
      have hre : r = 0 := le_antisymm hr hr0
      simp [hre]
    · exact LowerBound.bot_Bounds _ _
  · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe hu0)
    have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB hl0)
    have hs₁ : c₁ = false → 0 < dyadic_to_real a₁ := by
      intro hc; rw [hc, zeroUB] at hu0
      exact dyadic_to_real_pos (by simpa [FiniteUpperBound.le_def] using WithTop.coe_le_coe.mp hu0)
    have hs₂ : c₂ = false → dyadic_to_real a₂ < 0 := by
      intro hc; rw [hc, zeroLB] at hl0
      have h2 : a₂ < 0 := by simpa [FiniteLowerBound.le_def] using WithBot.coe_le_coe.mp hl0
      simpa [dyadic_to_real_zero] using strictMono_dyadic_to_real h2
    have hp₁ : a₁ = 0 ∨ 0 < dyadic_to_real a₁ :=
      (eq_or_lt_of_le (zeroUB_le_coe hu0)).imp Eq.symm dyadic_to_real_pos
    have hp₂ : a₂ = 0 ∨ dyadic_to_real a₂ < 0 := by
      rcases eq_or_lt_of_le hb₂ with h | h
      · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
      · exact Or.inr h
    cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [UpperBound.toLowerBound, LowerBound.mul, LowerBound.Bounds, UpperBound.Bounds,
        hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
        reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
      (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
      first
      | exact absurd (hs₁ hc₁) (by rw [hz₁]; simp [dyadic_to_real_zero])
      | exact absurd (hs₂ hc₂) (by rw [hz₂]; simp [dyadic_to_real_zero])
      | (have hd : (0:ℝ) ≤ dyadic_to_real a₁ - r := by linarith
         have he : (0:ℝ) ≤ s - dyadic_to_real a₂ := by linarith
         nlinarith [mul_nonneg (neg_nonneg.mpr hb₂) hd, mul_nonneg hr0 he, hr, hs, ha₁, hb₂, hr0])
      | (rcases lt_or_eq_of_le hr0 with hrlt | rfl
         · first
           | nlinarith [mul_pos hrlt (show (0:ℝ) < s - dyadic_to_real a₂ by linarith),
               hr, hs, ha₁, hb₂, hrlt]
           | nlinarith [mul_pos (show (0:ℝ) < -dyadic_to_real a₂ by linarith)
               (show (0:ℝ) < dyadic_to_real a₁ - r by linarith), hr, hs, ha₁, hb₂, hrlt]
         · nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ by linarith)
             (show (0:ℝ) < -dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂])

/- Building block: lower bound `x.ub.toLowerBound * y.lb`, disjunction of signs. -/
lemma LowerBound.mul_toLowerBound_bounds_left' {r s : ℝ} {u₁ : UpperBound Dyadic}
    {l₂ : LowerBound Dyadic} (hu0 : zeroUB ≤ u₁) (hl0 : l₂ ≤ zeroLB) (hrs : 0 ≤ r ∨ s ≤ 0)
    (hr : u₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    (u₁.toLowerBound.mul l₂).Bounds dyadic_to_real (r * s) := by
  rcases hrs with hr0 | hs0
  · exact LowerBound.mul_toLowerBound_bounds_left_of_nonneg hu0 hl0 hr0 hr hs
  · exact LowerBound.mul_toLowerBound_bounds_left hu0 hs0 hr hs

/- Building block: lower bound `x.lb * y.ub.toLowerBound`, disjunction of signs. -/
lemma LowerBound.mul_toLowerBound_bounds_right {r s : ℝ} {l₁ : LowerBound Dyadic}
    {u₂ : UpperBound Dyadic} (hl0 : l₁ ≤ zeroLB) (hu0 : zeroUB ≤ u₂) (hrs : r ≤ 0 ∨ 0 ≤ s)
    (hr : l₁.Bounds dyadic_to_real r) (hs : u₂.Bounds dyadic_to_real s) :
    (l₁.mul u₂.toLowerBound).Bounds dyadic_to_real (r * s) := by
  rw [LowerBound.mul_comm l₁ (u₂.toLowerBound), _root_.mul_comm r s]
  exact LowerBound.mul_toLowerBound_bounds_left' hu0 hl0 hrs.symm hs hr

/- Building block: lower bound `(x.ub * y.ub).toLowerBound` (nonpos × nonpos). -/
lemma LowerBound.toLowerBound_mul_bounds_nonpos {r s : ℝ} {u₁ u₂ : UpperBound Dyadic}
    (h1 : u₁ ≤ zeroUB) (h2 : u₂ ≤ zeroUB)
    (hr : u₁.Bounds dyadic_to_real r) (hs : u₂.Bounds dyadic_to_real s) :
    ((u₁.mul u₂).toLowerBound).Bounds dyadic_to_real (r * s) := by
  rcases u₁ with _ | ⟨c₁, a₁⟩
  · exact absurd (top_le_iff.mp h1) (by simp [zeroUB])
  · rcases u₂ with _ | ⟨c₂, a₂⟩
    · exact absurd (top_le_iff.mp h2) (by simp [zeroUB])
    · have ha₁ : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB h1)
      have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB h2)
      have hrle : r ≤ 0 := by
        have hh := hr; cases hc : c₁ <;> simp [UpperBound.Bounds, hc] at hh <;> linarith
      have hsle : s ≤ 0 := by
        have hh := hs; cases hc : c₂ <;> simp [UpperBound.Bounds, hc] at hh <;> linarith
      have hp₁ : a₁ = 0 ∨ dyadic_to_real a₁ < 0 := by
        rcases eq_or_lt_of_le ha₁ with h | h
        · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
        · exact Or.inr h
      have hp₂ : a₂ = 0 ∨ dyadic_to_real a₂ < 0 := by
        rcases eq_or_lt_of_le hb₂ with h | h
        · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
        · exact Or.inr h
      cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
        simp only [UpperBound.mul, UpperBound.toLowerBound, LowerBound.Bounds, UpperBound.Bounds,
          hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
          Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
          reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
        (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
        first
        | nlinarith [mul_nonneg (neg_nonneg.mpr hrle) (neg_nonneg.mpr hsle), hrle, hsle]
        | (have hd : (0:ℝ) ≤ dyadic_to_real a₁ - r := by linarith
           have he : (0:ℝ) ≤ dyadic_to_real a₂ - s := by linarith
           nlinarith [mul_nonneg (neg_nonneg.mpr hrle) he, mul_nonneg (neg_nonneg.mpr hb₂) hd,
             hr, hs, ha₁, hb₂, hrle, hsle])
        | (rcases lt_or_eq_of_le hrle with hrlt | rfl
           · first
             | nlinarith [mul_pos (show (0:ℝ) < -r by linarith) (show (0:ℝ) < -s by linarith),
                 hr, hs, ha₁, hb₂, hrlt, hsle]
             | nlinarith [mul_pos (show (0:ℝ) < -r by linarith)
                 (show (0:ℝ) < dyadic_to_real a₂ - s by linarith), hr, hs, ha₁, hb₂, hrlt, hsle]
             | nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ - r by linarith)
                 (show (0:ℝ) < -dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂, hrlt, hsle]
           · nlinarith [hr, hs, ha₁, hb₂])

/- Building block: upper bound `x.ub * y.ub`, nonneg-`r` case. -/
lemma UpperBound.mul_bounds_of_nonneg {r s : ℝ} {u₁ u₂ : UpperBound Dyadic}
    (h1 : zeroUB ≤ u₁) (h2 : zeroUB ≤ u₂) (hr0 : 0 ≤ r)
    (hr : u₁.Bounds dyadic_to_real r) (hs : u₂.Bounds dyadic_to_real s) :
    (u₁.mul u₂).Bounds dyadic_to_real (r * s) := by
  rcases u₁ with _ | ⟨c₁, a₁⟩ <;> rcases u₂ with _ | ⟨c₂, a₂⟩
  · simp [UpperBound.mul, UpperBound.Bounds]
  · simp only [UpperBound.mul]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [UpperBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hs ⊢
      nlinarith [mul_nonneg hr0 (neg_nonneg.mpr hs)]
    · exact UpperBound.top_Bounds _ _
  · simp only [UpperBound.mul]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [UpperBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hr ⊢
      have hre : r = 0 := le_antisymm hr hr0
      simp [hre]
    · exact UpperBound.top_Bounds _ _
  · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe h1)
    have hb₂ : 0 ≤ dyadic_to_real a₂ := dyadic_to_real_nonneg (zeroUB_le_coe h2)
    have hs₁ : c₁ = false → 0 < dyadic_to_real a₁ := by
      intro hc; rw [hc, zeroUB] at h1
      exact dyadic_to_real_pos (by simpa [FiniteUpperBound.le_def] using WithTop.coe_le_coe.mp h1)
    have hs₂ : c₂ = false → 0 < dyadic_to_real a₂ := by
      intro hc; rw [hc, zeroUB] at h2
      exact dyadic_to_real_pos (by simpa [FiniteUpperBound.le_def] using WithTop.coe_le_coe.mp h2)
    have hp₁ : a₁ = 0 ∨ 0 < dyadic_to_real a₁ :=
      (eq_or_lt_of_le (zeroUB_le_coe h1)).imp Eq.symm dyadic_to_real_pos
    have hp₂ : a₂ = 0 ∨ 0 < dyadic_to_real a₂ :=
      (eq_or_lt_of_le (zeroUB_le_coe h2)).imp Eq.symm dyadic_to_real_pos
    cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [UpperBound.mul, UpperBound.Bounds,
        hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
        reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
      (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
      first
      | exact absurd (hs₁ hc₁) (by rw [hz₁]; simp [dyadic_to_real_zero])
      | exact absurd (hs₂ hc₂) (by rw [hz₂]; simp [dyadic_to_real_zero])
      | (have hd : (0:ℝ) ≤ dyadic_to_real a₁ - r := by linarith
         have he : (0:ℝ) ≤ dyadic_to_real a₂ - s := by linarith
         nlinarith [mul_nonneg hr0 he, mul_nonneg hd hb₂, hr, hs, ha₁, hb₂, hr0])
      | (rcases lt_or_eq_of_le hr0 with hrlt | rfl
         · first
           | nlinarith [mul_pos hrlt (show (0:ℝ) < dyadic_to_real a₂ - s by linarith),
               hr, hs, ha₁, hb₂, hrlt]
           | nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ - r by linarith)
               (show (0:ℝ) < dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂, hrlt]
           | nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ - r by linarith)
               (show (0:ℝ) < dyadic_to_real a₂ - s by linarith), hr, hs, ha₁, hb₂, hrlt]
         · nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ by linarith)
             (show (0:ℝ) < dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂])

/- Building block: upper bound `x.lb.toUpperBound * y.ub` (nonneg × nonpos). -/
lemma UpperBound.toUpperBound_mul_bounds_left {r s : ℝ} {l₁ : LowerBound Dyadic}
    {u₂ : UpperBound Dyadic} (hl0 : zeroLB ≤ l₁) (hu0 : u₂ ≤ zeroUB) (hs0 : s ≤ 0)
    (hr : l₁.Bounds dyadic_to_real r) (hs : u₂.Bounds dyadic_to_real s) :
    ((l₁.toUpperBound).mul u₂).Bounds dyadic_to_real (r * s) := by
  rcases l₁ with _ | ⟨c₁, a₁⟩
  · exact absurd (le_bot_iff.mp hl0) (by simp [zeroLB])
  · rcases u₂ with _ | ⟨c₂, a₂⟩
    · exact absurd (top_le_iff.mp hu0) (by simp [zeroUB])
    · have ha₁ : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroLB_le_coe hl0)
      have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB hu0)
      have hp₁ : a₁ = 0 ∨ 0 < dyadic_to_real a₁ :=
        (eq_or_lt_of_le (zeroLB_le_coe hl0)).imp Eq.symm dyadic_to_real_pos
      have hp₂ : a₂ = 0 ∨ dyadic_to_real a₂ < 0 := by
        rcases eq_or_lt_of_le hb₂ with h | h
        · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
        · exact Or.inr h
      cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
        simp only [LowerBound.toUpperBound, UpperBound.mul, UpperBound.Bounds, LowerBound.Bounds,
          hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
          Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
          reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
        (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
        first
        | nlinarith [mul_nonneg (show (0:ℝ) ≤ r by linarith) (neg_nonneg.mpr hs0), hr, hs, ha₁, hb₂]
        | (have hd : (0:ℝ) ≤ r - dyadic_to_real a₁ := by linarith
           have he : (0:ℝ) ≤ dyadic_to_real a₂ - s := by linarith
           nlinarith [mul_nonneg hd (neg_nonneg.mpr hs0), mul_nonneg ha₁ he, hr, hs, ha₁, hb₂, hs0])
        | (rcases lt_or_eq_of_le hs0 with hslt | rfl
           · first
             | nlinarith [mul_pos (show (0:ℝ) < r - dyadic_to_real a₁ by linarith)
                 (show (0:ℝ) < -s by linarith), hr, hs, ha₁, hb₂, hslt]
             | nlinarith [mul_pos (show (0:ℝ) < dyadic_to_real a₁ by linarith)
                 (show (0:ℝ) < dyadic_to_real a₂ - s by linarith), hr, hs, ha₁, hb₂, hslt]
           · nlinarith [hr, hs, ha₁, hb₂])

/- Building block: upper bound `(x.lb * y.lb).toUpperBound`, nonpos-`r` case. -/
lemma UpperBound.toUpperBound_mul_bounds_nonpos_left {r s : ℝ} {l₁ l₂ : LowerBound Dyadic}
    (h1 : l₁ ≤ zeroLB) (h2 : l₂ ≤ zeroLB) (hr0 : r ≤ 0)
    (hr : l₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    ((l₁.mul l₂).toUpperBound).Bounds dyadic_to_real (r * s) := by
  rcases l₁ with _ | ⟨c₁, a₁⟩ <;> rcases l₂ with _ | ⟨c₂, a₂⟩
  · simp [LowerBound.mul, LowerBound.toUpperBound, UpperBound.Bounds]
  · have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB h2)
    simp only [LowerBound.mul, LowerBound.toUpperBound]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [UpperBound.Bounds, LowerBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hs ⊢
      nlinarith [mul_nonneg (neg_nonneg.mpr hr0) hs]
    · exact UpperBound.top_Bounds _ _
  · have ha₁ : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB h1)
    simp only [LowerBound.mul, LowerBound.toUpperBound]
    split_ifs with hcond
    · obtain ⟨ha, hc⟩ := hcond; subst ha
      simp only [UpperBound.Bounds, LowerBound.Bounds, hc, dyadic_to_real_zero, reduceIte] at hr ⊢
      have hre : r = 0 := le_antisymm hr0 hr
      simp [hre]
    · exact UpperBound.top_Bounds _ _
  · have ha₁ : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB h1)
    have hb₂ : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB h2)
    have hs₁ : c₁ = false → dyadic_to_real a₁ < 0 := by
      intro hc; rw [hc, zeroLB] at h1
      have hh : a₁ < 0 := by simpa [FiniteLowerBound.le_def] using WithBot.coe_le_coe.mp h1
      simpa [dyadic_to_real_zero] using strictMono_dyadic_to_real hh
    have hs₂ : c₂ = false → dyadic_to_real a₂ < 0 := by
      intro hc; rw [hc, zeroLB] at h2
      have hh : a₂ < 0 := by simpa [FiniteLowerBound.le_def] using WithBot.coe_le_coe.mp h2
      simpa [dyadic_to_real_zero] using strictMono_dyadic_to_real hh
    have hp₁ : a₁ = 0 ∨ dyadic_to_real a₁ < 0 := by
      rcases eq_or_lt_of_le ha₁ with h | h
      · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
      · exact Or.inr h
    have hp₂ : a₂ = 0 ∨ dyadic_to_real a₂ < 0 := by
      rcases eq_or_lt_of_le hb₂ with h | h
      · exact Or.inl (strictMono_dyadic_to_real.injective (h.trans dyadic_to_real_zero.symm))
      · exact Or.inr h
    cases hc₁ : c₁ <;> cases hc₂ : c₂ <;> by_cases! hz₁ : a₁ = 0 <;> by_cases! hz₂ : a₂ = 0 <;>
      simp only [LowerBound.mul, LowerBound.toUpperBound, UpperBound.Bounds, LowerBound.Bounds,
        hc₁, hc₂, hz₁, hz₂, dyadic_to_real_mul, dyadic_to_real_zero, Bool.and_true, Bool.and_false,
        Bool.true_and, Bool.false_and, and_true, and_false, true_and, false_and, reduceCtorEq,
        reduceIte, if_true, if_false, mul_zero, zero_mul] at hr hs ⊢ <;>
      (try have hpb := hp₁.resolve_left hz₁) <;> (try have hnb := hp₂.resolve_left hz₂) <;>
      first
      | exact absurd (hs₁ hc₁) (by rw [hz₁]; simp [dyadic_to_real_zero])
      | exact absurd (hs₂ hc₂) (by rw [hz₂]; simp [dyadic_to_real_zero])
      | nlinarith [mul_nonneg (neg_nonneg.mpr hr0) (show (0:ℝ) ≤ s by linarith), hr0]
      | (have hre : r = 0 := le_antisymm hr0 (by linarith); simp [hre])
      | (have hd : (0:ℝ) ≤ r - dyadic_to_real a₁ := by linarith
         have he : (0:ℝ) ≤ s - dyadic_to_real a₂ := by linarith
         nlinarith [mul_nonneg (neg_nonneg.mpr hb₂) hd, mul_nonneg (neg_nonneg.mpr hr0) he,
           hr, hs, ha₁, hb₂, hr0])
      | (rcases lt_or_eq_of_le hr0 with hrlt | rfl
         · first
           | nlinarith [mul_pos (show (0:ℝ) < -r by linarith)
               (show (0:ℝ) < s - dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂, hrlt]
           | nlinarith [mul_pos (show (0:ℝ) < r - dyadic_to_real a₁ by linarith)
               (show (0:ℝ) < -dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂, hrlt]
         · nlinarith [mul_pos (show (0:ℝ) < -dyadic_to_real a₁ by linarith)
             (show (0:ℝ) < -dyadic_to_real a₂ by linarith), hr, hs, ha₁, hb₂])

/- Building block: upper bound `x.ub * y.ub`, disjunction of signs. -/
lemma UpperBound.mul_bounds {r s : ℝ} {u₁ u₂ : UpperBound Dyadic}
    (h1 : zeroUB ≤ u₁) (h2 : zeroUB ≤ u₂) (hrs : 0 ≤ r ∨ 0 ≤ s)
    (hr : u₁.Bounds dyadic_to_real r) (hs : u₂.Bounds dyadic_to_real s) :
    (u₁.mul u₂).Bounds dyadic_to_real (r * s) := by
  rcases hrs with hr0 | hs0
  · exact UpperBound.mul_bounds_of_nonneg h1 h2 hr0 hr hs
  · rw [UpperBound.mul_comm, _root_.mul_comm r s]
    exact UpperBound.mul_bounds_of_nonneg h2 h1 hs0 hs hr

/- Building block: upper bound `x.ub * y.lb.toUpperBound` (nonpos × nonneg). -/
lemma UpperBound.mul_toUpperBound_bounds_right {r s : ℝ} {u₁ : UpperBound Dyadic}
    {l₂ : LowerBound Dyadic} (hu0 : u₁ ≤ zeroUB) (hl0 : zeroLB ≤ l₂) (hr0 : r ≤ 0)
    (hr : u₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    (u₁.mul (l₂.toUpperBound)).Bounds dyadic_to_real (r * s) := by
  rw [UpperBound.mul_comm u₁ (l₂.toUpperBound), _root_.mul_comm r s]
  exact UpperBound.toUpperBound_mul_bounds_left hl0 hu0 hr0 hs hr

/- Building block: upper bound `(x.lb * y.lb).toUpperBound`, disjunction of signs. -/
lemma UpperBound.toUpperBound_mul_bounds {r s : ℝ} {l₁ l₂ : LowerBound Dyadic}
    (h1 : l₁ ≤ zeroLB) (h2 : l₂ ≤ zeroLB) (hrs : r ≤ 0 ∨ s ≤ 0)
    (hr : l₁.Bounds dyadic_to_real r) (hs : l₂.Bounds dyadic_to_real s) :
    ((l₁.mul l₂).toUpperBound).Bounds dyadic_to_real (r * s) := by
  rcases hrs with hr0 | hs0
  · exact UpperBound.toUpperBound_mul_bounds_nonpos_left h1 h2 hr0 hr hs
  · rw [LowerBound.mul_comm, _root_.mul_comm r s]
    exact UpperBound.toUpperBound_mul_bounds_nonpos_left h2 h1 hs0 hs hr

@[interval_op DyadicReal Mul]
theorem Interval.rat_mul_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    r * s ∈ (x.mul y).toSet dyadic_to_real := by
  cases hx : x.toIntervalSignClass <;> cases hy : y.toIntervalSignClass <;>
    simp only [Interval.mem_toSet, Interval.mul, hx, hy]
  · -- nonneg, nonneg
    have hr0 : 0 ≤ r := nonneg_of_mem_nonneg_toSet hx hrx
    have hxu := zeroUB_le_ub_of_mem hr0 hrx.2
    have hyu := zeroUB_le_ub_of_mem (nonneg_of_mem_nonneg_toSet hy hsy) hsy.2
    exact ⟨LowerBound.mul_bounds_nonneg (zeroLB_le_lb_of_nonneg hx) (zeroLB_le_lb_of_nonneg hy)
        hrx.1 hsy.1, UpperBound.mul_bounds hxu hyu (Or.inl hr0) hrx.2 hsy.2⟩
  · -- nonneg, nonpos
    have hr0 : 0 ≤ r := nonneg_of_mem_nonneg_toSet hx hrx
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hxu := zeroUB_le_ub_of_mem hr0 hrx.2
    have hyl := lb_le_zeroLB_of_mem hs0 hsy.1
    exact ⟨LowerBound.mul_toLowerBound_bounds_left' hxu hyl (Or.inl hr0) hrx.2 hsy.1,
      UpperBound.toUpperBound_mul_bounds_left (zeroLB_le_lb_of_nonneg hx)
        (ub_le_zeroUB_of_nonpos hy) hs0 hrx.1 hsy.2⟩
  · -- nonneg, mixed
    have hr0 : 0 ≤ r := nonneg_of_mem_nonneg_toSet hx hrx
    have hxu := zeroUB_le_ub_of_mem hr0 hrx.2
    have hyu := zeroUB_le_ub_of_mixed hy
    exact ⟨LowerBound.mul_toLowerBound_bounds_left' hxu (lb_le_zeroLB_of_mixed hy) (Or.inl hr0)
        hrx.2 hsy.1, UpperBound.mul_bounds hxu hyu (Or.inl hr0) hrx.2 hsy.2⟩
  · -- nonpos, nonneg
    have hr0 : r ≤ 0 := nonpos_of_mem_nonpos_toSet hx hrx
    have hs0 : 0 ≤ s := nonneg_of_mem_nonneg_toSet hy hsy
    have hxl := lb_le_zeroLB_of_mem hr0 hrx.1
    have hyu := zeroUB_le_ub_of_mem hs0 hsy.2
    exact ⟨LowerBound.mul_toLowerBound_bounds_right hxl hyu (Or.inl hr0) hrx.1 hsy.2,
      UpperBound.mul_toUpperBound_bounds_right (ub_le_zeroUB_of_nonpos hx)
        (zeroLB_le_lb_of_nonneg hy) hr0 hrx.2 hsy.1⟩
  · -- nonpos, nonpos
    have hr0 : r ≤ 0 := nonpos_of_mem_nonpos_toSet hx hrx
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hxl := lb_le_zeroLB_of_mem hr0 hrx.1
    have hyl := lb_le_zeroLB_of_mem hs0 hsy.1
    exact ⟨LowerBound.toLowerBound_mul_bounds_nonpos (ub_le_zeroUB_of_nonpos hx)
        (ub_le_zeroUB_of_nonpos hy) hrx.2 hsy.2,
      UpperBound.toUpperBound_mul_bounds hxl hyl (Or.inl hr0) hrx.1 hsy.1⟩
  · -- nonpos, mixed
    have hr0 : r ≤ 0 := nonpos_of_mem_nonpos_toSet hx hrx
    have hxl := lb_le_zeroLB_of_mem hr0 hrx.1
    have hyu := zeroUB_le_ub_of_mixed hy
    exact ⟨LowerBound.mul_toLowerBound_bounds_right hxl hyu (Or.inl hr0) hrx.1 hsy.2,
      UpperBound.toUpperBound_mul_bounds hxl (lb_le_zeroLB_of_mixed hy) (Or.inl hr0) hrx.1 hsy.1⟩
  · -- mixed, nonneg
    have hs0 : 0 ≤ s := nonneg_of_mem_nonneg_toSet hy hsy
    have hxl := lb_le_zeroLB_of_mixed hx
    have hxu := zeroUB_le_ub_of_mixed hx
    have hyu := zeroUB_le_ub_of_mem hs0 hsy.2
    exact ⟨LowerBound.mul_toLowerBound_bounds_right hxl hyu (Or.inr hs0) hrx.1 hsy.2,
      UpperBound.mul_bounds hxu hyu (Or.inr hs0) hrx.2 hsy.2⟩
  · -- mixed, nonpos
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hxl := lb_le_zeroLB_of_mixed hx
    have hxu := zeroUB_le_ub_of_mixed hx
    have hyl := lb_le_zeroLB_of_mem hs0 hsy.1
    exact ⟨LowerBound.mul_toLowerBound_bounds_left' hxu hyl (Or.inr hs0) hrx.2 hsy.1,
      UpperBound.toUpperBound_mul_bounds hxl hyl (Or.inr hs0) hrx.1 hsy.1⟩
  · -- mixed, mixed
    have hxl := lb_le_zeroLB_of_mixed hx
    have hxu := zeroUB_le_ub_of_mixed hx
    have hyl := lb_le_zeroLB_of_mixed hy
    have hyu := zeroUB_le_ub_of_mixed hy
    refine ⟨?_, ?_⟩
    · rcases le_total r 0 with hr0 | hr0
      · exact LowerBound.bounds_of_bounds strictMono_dyadic_to_real (min_le_left _ _)
          (LowerBound.mul_toLowerBound_bounds_right hxl hyu (Or.inl hr0) hrx.1 hsy.2)
      · exact LowerBound.bounds_of_bounds strictMono_dyadic_to_real (min_le_right _ _)
          (LowerBound.mul_toLowerBound_bounds_left' hxu hyl (Or.inl hr0) hrx.2 hsy.1)
    · rcases le_total r 0 with hr0 | hr0
      · exact UpperBound.bounds_of_bounds strictMono_dyadic_to_real (le_max_left _ _)
          (UpperBound.toUpperBound_mul_bounds hxl hyl (Or.inl hr0) hrx.1 hsy.1)
      · exact UpperBound.bounds_of_bounds strictMono_dyadic_to_real (le_max_right _ _)
          (UpperBound.mul_bounds hxu hyu (Or.inl hr0) hrx.2 hsy.2)

end Mul

section Pow

def Interval.pow (x : Interval Dyadic) (n : ℕ) : Interval Dyadic :=
  let zero_lb : LowerBound Dyadic := some ⟨true, 0⟩
  let zero_ub : UpperBound Dyadic := some ⟨true, 0⟩
  if n = 0 then nat_const 1
  else if zero_lb ≤ x.lb || n % 2 = 1 then
    let lb := match x.lb with | ⊥ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.ub with | ⊤ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else if decide (x.ub ≤ zero_ub) then
    let lb := match x.ub with | ⊤ => ⊥ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    let ub := match x.lb with | ⊥ => ⊤ | some ⟨c, q⟩ => some ⟨c, q ^ n⟩
    ⟨lb, ub⟩
  else
    let ub := match x.lb, x.ub with
    | some ⟨c₁, q₁⟩, some ⟨c₂, q₂⟩ =>
      let q₁' := if 0 ≤ q₁ then q₁ else -q₁ -- q₁.abs
      if q₁' < q₂ then some ⟨c₂, q₂ ^ n⟩
      else if q₁' = q₂ then some ⟨c₁ || c₂, q₂ ^ n⟩
      else some ⟨c₁, q₁' ^ n⟩
    | _, _ => ⊤
    ⟨zero_lb, ub⟩


/-- Powers commute with `dyadic_to_real`. -/
@[simp]
lemma dyadic_to_real_pow (a : Dyadic) (n : ℕ) :
    dyadic_to_real (a ^ n) = (dyadic_to_real a) ^ n := by
  simp only [dyadic_to_real, Dyadic.toRat_pow]
  norm_cast

/-- Negation commutes with `dyadic_to_real`. -/
lemma dyadic_to_real_neg (a : Dyadic) :
    dyadic_to_real (-a) = -(dyadic_to_real a) := by
  simp only [dyadic_to_real, Dyadic.toRat_neg]
  norm_cast

/-- Transfer a lower bound through `q ↦ q ^ n` (monotone direction). -/
lemma lbBounds_pow {n : ℕ} {c : Bool} {q : Dyadic} {r : ℝ}
    (hle : dyadic_to_real q ≤ r → (dyadic_to_real q) ^ n ≤ r ^ n)
    (hlt : dyadic_to_real q < r → (dyadic_to_real q) ^ n < r ^ n)
    (hb : LowerBound.Bounds dyadic_to_real (some ⟨c, q⟩) r) :
    LowerBound.Bounds dyadic_to_real (some ⟨c, q ^ n⟩) (r ^ n) := by
  cases c <;>
    simp only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte, dyadic_to_real_pow] at hb ⊢
  · exact hlt hb
  · exact hle hb

/-- Transfer an upper bound through `q ↦ q ^ n` (monotone direction). -/
lemma ubBounds_pow {n : ℕ} {c : Bool} {q : Dyadic} {r : ℝ}
    (hle : r ≤ dyadic_to_real q → r ^ n ≤ (dyadic_to_real q) ^ n)
    (hlt : r < dyadic_to_real q → r ^ n < (dyadic_to_real q) ^ n)
    (hb : UpperBound.Bounds dyadic_to_real (some ⟨c, q⟩) r) :
    UpperBound.Bounds dyadic_to_real (some ⟨c, q ^ n⟩) (r ^ n) := by
  cases c <;>
    simp only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte, dyadic_to_real_pow] at hb ⊢
  · exact hlt hb
  · exact hle hb

/-- Transfer an upper bound to a lower bound through `q ↦ q ^ n` (antitone/flip). -/
lemma ubBounds_flip_pow {n : ℕ} {c : Bool} {q : Dyadic} {r : ℝ}
    (hle : r ≤ dyadic_to_real q → (dyadic_to_real q) ^ n ≤ r ^ n)
    (hlt : r < dyadic_to_real q → (dyadic_to_real q) ^ n < r ^ n)
    (hb : UpperBound.Bounds dyadic_to_real (some ⟨c, q⟩) r) :
    LowerBound.Bounds dyadic_to_real (some ⟨c, q ^ n⟩) (r ^ n) := by
  cases c <;>
    simp only [UpperBound.Bounds, LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte,
      dyadic_to_real_pow] at hb ⊢
  · exact hlt hb
  · exact hle hb

/-- Transfer a lower bound to an upper bound through `q ↦ q ^ n` (antitone/flip). -/
lemma lbBounds_flip_pow {n : ℕ} {c : Bool} {q : Dyadic} {r : ℝ}
    (hle : dyadic_to_real q ≤ r → r ^ n ≤ (dyadic_to_real q) ^ n)
    (hlt : dyadic_to_real q < r → r ^ n < (dyadic_to_real q) ^ n)
    (hb : LowerBound.Bounds dyadic_to_real (some ⟨c, q⟩) r) :
    UpperBound.Bounds dyadic_to_real (some ⟨c, q ^ n⟩) (r ^ n) := by
  cases c <;>
    simp only [LowerBound.Bounds, UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte,
      dyadic_to_real_pow] at hb ⊢
  · exact hlt hb
  · exact hle hb

/-- For even `n`, `· ^ n` is monotone in `|·|` (non-strict). -/
lemma even_pow_le_of_abs_le {n : ℕ} (hn : Even n) {a b : ℝ} (h : |a| ≤ |b|) :
    a ^ n ≤ b ^ n := by
  rw [← hn.pow_abs a, ← hn.pow_abs b]
  exact pow_le_pow_left₀ (abs_nonneg a) h n

/-- For even `n`, `· ^ n` is monotone in `|·|` (strict). -/
lemma even_pow_lt_of_abs_lt {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) {a b : ℝ} (h : |a| < |b|) :
    a ^ n < b ^ n := by
  rw [← hn.pow_abs a, ← hn.pow_abs b]
  exact pow_lt_pow_left₀ h (abs_nonneg a) hn0

/-- Build a powered upper bound from an `|·|`-comparison (for even `n`, mixed sign). -/
lemma ubBounds_pow_abs {n : ℕ} {c : Bool} {v : Dyadic} {r : ℝ} (hn : Even n) (hn0 : n ≠ 0)
    (hle : |r| ≤ |dyadic_to_real v|) (hlt : c = false → |r| < |dyadic_to_real v|) :
    UpperBound.Bounds dyadic_to_real (some ⟨c, v ^ n⟩) (r ^ n) := by
  cases c <;>
    simp only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte, dyadic_to_real_pow]
  · exact even_pow_lt_of_abs_lt hn hn0 (hlt rfl)
  · exact even_pow_le_of_abs_le hn hle

@[interval_op DyadicReal Pow]
theorem rat_pow_inclusion {r : ℝ} {x : Interval Dyadic} (n : ℕ) (hrx : r ∈ x.toSet dyadic_to_real) :
    (r ^ n) ∈ (x.pow n).toSet dyadic_to_real := by
  obtain ⟨L, U⟩ := x
  rw [Interval.mem_toSet] at hrx
  obtain ⟨hlb, hub⟩ := hrx
  simp only [Interval.pow]
  split_ifs with h0 h2 h3
  · -- Branch 1: n = 0
    subst h0
    rw [pow_zero]
    simpa using nat_cast_inclusion 1
  · -- Branch 2: base nonneg or n odd (endpoint-wise)
    have hn0 : n ≠ 0 := h0
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
    rw [Interval.mem_toSet]
    rcases h2 with hnn | hodd
    · -- base nonneg
      have hr0 : (0 : ℝ) ≤ r := by
        have := LowerBound.bounds_of_bounds strictMono_dyadic_to_real hnn hlb
        simpa [LowerBound.Bounds, dyadic_to_real_zero] using this
      refine ⟨?_, ?_⟩
      · rcases L with _ | ⟨cl, ql⟩
        · exact (WithBot.not_coe_le_bot _ hnn).elim
        · have hql0 : (0 : ℝ) ≤ dyadic_to_real ql := dyadic_to_real_nonneg (zeroLB_le_coe hnn)
          exact lbBounds_pow (fun h => pow_le_pow_left₀ hql0 h n)
            (fun h => pow_lt_pow_left₀ h hql0 hn0) hlb
      · rcases U with _ | ⟨cu, qu⟩
        · exact UpperBound.top_Bounds _ _
        · exact ubBounds_pow (fun h => pow_le_pow_left₀ hr0 h n)
            (fun h => pow_lt_pow_left₀ h hr0 hn0) hub
    · -- n odd
      have hodd' : Odd n := Nat.odd_iff.mpr hodd
      refine ⟨?_, ?_⟩
      · rcases L with _ | ⟨cl, ql⟩
        · exact LowerBound.bot_Bounds _ _
        · exact lbBounds_pow (fun h => (hodd'.pow_le_pow).mpr h)
            (fun h => (hodd'.pow_lt_pow).mpr h) hlb
      · rcases U with _ | ⟨cu, qu⟩
        · exact UpperBound.top_Bounds _ _
        · exact ubBounds_pow (fun h => (hodd'.pow_le_pow).mpr h)
            (fun h => (hodd'.pow_lt_pow).mpr h) hub
  · -- Branch 3: base nonpos, n even (flip)
    have hn0 : n ≠ 0 := h0
    simp only [decide_eq_true_eq] at h3
    have hev : Even n := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h2
      obtain ⟨-, h2r⟩ := h2
      exact Nat.even_iff.mpr (by omega)
    have hr0 : r ≤ 0 := by
      have := UpperBound.bounds_of_bounds strictMono_dyadic_to_real h3 hub
      simpa [UpperBound.Bounds, dyadic_to_real_zero] using this
    rw [Interval.mem_toSet]
    refine ⟨?_, ?_⟩
    · -- lower bound of pow, from U (flip)
      rcases U with _ | ⟨cu, qu⟩
      · exact LowerBound.bot_Bounds _ _
      · have hqu0 : dyadic_to_real qu ≤ 0 := by
          have hqud : qu ≤ (0 : Dyadic) := by simpa using WithTop.coe_le_coe.mp h3
          exact dyadic_to_real_nonpos hqud
        exact ubBounds_flip_pow
          (fun h => even_pow_le_of_abs_le hev
            (by rw [abs_of_nonpos hqu0, abs_of_nonpos (h.trans hqu0)]; linarith))
          (fun h => even_pow_lt_of_abs_lt hev hn0
            (by rw [abs_of_nonpos hqu0, abs_of_nonpos (le_of_lt (lt_of_lt_of_le h hqu0))]; linarith))
          hub
    · -- upper bound of pow, from L (flip)
      rcases L with _ | ⟨cl, ql⟩
      · exact UpperBound.top_Bounds _ _
      · have hql0 : dyadic_to_real ql ≤ 0 := by
          cases cl <;>
            simp only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte] at hlb <;> linarith
        exact lbBounds_flip_pow
          (fun h => even_pow_le_of_abs_le hev
            (by rw [abs_of_nonpos hr0, abs_of_nonpos hql0]; linarith))
          (fun h => even_pow_lt_of_abs_lt hev hn0
            (by rw [abs_of_nonpos hr0, abs_of_nonpos hql0]; linarith))
          hlb
  · -- Branch 4: mixed, n even
    have hn0 : n ≠ 0 := h0
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h2
    obtain ⟨hlneg, h2r⟩ := h2
    simp only [decide_eq_true_eq] at h3
    have hev : Even n := Nat.even_iff.mpr (by omega)
    rcases L with _ | ⟨cl, ql⟩
    · -- L = ⊥ ⇒ upper bound is ⊤
      rw [Interval.mem_toSet]
      refine ⟨?_, ?_⟩
      · simp only [LowerBound.Bounds, ↓reduceIte, dyadic_to_real_zero]
        exact hev.pow_nonneg r
      · exact UpperBound.top_Bounds _ _
    · rcases U with _ | ⟨cu, qu⟩
      · -- U = ⊤ ⇒ upper bound is ⊤
        rw [Interval.mem_toSet]
        refine ⟨?_, ?_⟩
        · simp only [LowerBound.Bounds, ↓reduceIte, dyadic_to_real_zero]
          exact hev.pow_nonneg r
        · exact UpperBound.top_Bounds _ _
      · -- both endpoints finite: the genuinely mixed case
        have hqld : ql < (0 : Dyadic) := by
          by_contra hc
          rw [not_lt] at hc
          exact hlneg (WithBot.coe_le_coe.mpr (by simpa [FiniteLowerBound.le_def] using hc))
        have hqud : (0 : Dyadic) < qu := by
          by_contra hc
          rw [not_lt] at hc
          exact h3 (WithTop.coe_le_coe.mpr (by simpa [FiniteUpperBound.le_def] using hc))
        have haR0 : dyadic_to_real ql ≤ 0 := dyadic_to_real_nonpos hqld.le
        have hbR0 : (0 : ℝ) ≤ dyadic_to_real qu := (dyadic_to_real_pos hqud).le
        have hlble : dyadic_to_real ql ≤ r := by
          cases cl <;>
            simp only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte] at hlb <;> linarith
        have huble : r ≤ dyadic_to_real qu := by
          cases cu <;>
            simp only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte] at hub <;> linarith
        have hlblt : cl = false → dyadic_to_real ql < r := by
          intro hc
          simp only [hc, LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte] at hlb
          exact hlb
        have hublt : cu = false → r < dyadic_to_real qu := by
          intro hc
          simp only [hc, UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte] at hub
          exact hub
        rw [Interval.mem_toSet]
        refine ⟨?_, ?_⟩
        · simp only [LowerBound.Bounds, ↓reduceIte, dyadic_to_real_zero]
          exact hev.pow_nonneg r
        · dsimp only
          simp only [if_neg (not_le.mpr hqld)]
          split_ifs with hcmp1 hcmp2
          · -- -ql < qu ⇒ upper endpoint qu
            have h1R : -dyadic_to_real ql < dyadic_to_real qu := by
              have := strictMono_dyadic_to_real hcmp1; rwa [dyadic_to_real_neg] at this
            refine ubBounds_pow_abs hev hn0 ?_ ?_
            · rw [abs_of_nonneg hbR0, abs_le]; constructor <;> linarith
            · intro hc; rw [abs_of_nonneg hbR0, abs_lt]; exact ⟨by linarith, hublt hc⟩
          · -- -ql = qu ⇒ upper endpoint qu, closedness cl || cu
            have h2R : -dyadic_to_real ql = dyadic_to_real qu := by
              have := congrArg dyadic_to_real hcmp2; rwa [dyadic_to_real_neg] at this
            refine ubBounds_pow_abs hev hn0 ?_ ?_
            · rw [abs_of_nonneg hbR0, abs_le]; constructor <;> linarith
            · intro hc; rw [abs_of_nonneg hbR0, abs_lt, Bool.or_eq_false_iff] at *
              exact ⟨by linarith [hlblt hc.1], hublt hc.2⟩
          · -- qu < -ql ⇒ upper endpoint -ql
            have h3R : dyadic_to_real qu < -dyadic_to_real ql := by
              have hlt' : qu < -ql := lt_of_le_of_ne (not_lt.mp hcmp1) (Ne.symm hcmp2)
              have := strictMono_dyadic_to_real hlt'; rwa [dyadic_to_real_neg] at this
            refine ubBounds_pow_abs hev hn0 ?_ ?_
            · rw [dyadic_to_real_neg, abs_neg, abs_of_nonpos haR0, abs_le]
              constructor <;> linarith
            · intro hc
              rw [dyadic_to_real_neg, abs_neg, abs_of_nonpos haR0, abs_lt]
              exact ⟨by linarith [hlblt hc], by linarith⟩

end Pow


-- # CHATGPT AFTER THIS POINT:

section Div

namespace Dyadic

/--
`divDown approxParam a b` is the dyadic approximation of `a / b` rounded downward
to precision `approxParam`.
-/
def divDown (approxParam : ℕ) (a b : Dyadic) : Dyadic :=
  Dyadic.divAtPrec a b (approxParam : Int)

/--
`divUp approxParam a b` is the dyadic approximation of `a / b` rounded upward
to precision `approxParam`.
-/
def divUp (approxParam : ℕ) (a b : Dyadic) : Dyadic :=
  - divDown approxParam (-a) b

end Dyadic

/-- `divDown` rounds down: its real value is at most the true quotient, for ANY denominator
(including negative or zero, where the quotient degenerates to `0`). -/
lemma divDown_le_all (p : ℕ) (a b : Dyadic) :
    dyadic_to_real (Dyadic.divDown p a b) ≤ dyadic_to_real a / dyadic_to_real b := by
  have hle : (Dyadic.divDown p a b).toRat ≤ a.toRat / b.toRat := by
    rw [Dyadic.divDown]
    cases b with
    | zero => simp [Dyadic.divAtPrec]
    | ofOdd n e hn => simp only [Dyadic.divAtPrec]; exact Rat.toRat_toDyadic_le
  have hcast := (Rat.cast_le (K := ℝ)).mpr hle
  rw [Rat.cast_div] at hcast
  simpa only [dyadic_to_real] using hcast

/-- `divUp` rounds up: its real value is at least the true quotient, for ANY denominator. -/
lemma le_divUp_all (p : ℕ) (a b : Dyadic) :
    dyadic_to_real a / dyadic_to_real b ≤ dyadic_to_real (Dyadic.divUp p a b) := by
  have h := divDown_le_all p (-a) b
  rw [dyadic_to_real_neg, neg_div] at h
  rw [Dyadic.divUp, dyadic_to_real_neg]
  linarith

def LowerBound.dyadic_div
    (approxParam : ℕ) (lb₁ : LowerBound Dyadic) (ub₂ : UpperBound Dyadic)
    (lb₂ : LowerBound Dyadic) :
    LowerBound Dyadic :=
  match lb₁, ub₂ with
  | ⊥, ⊤ => ⊥
  | ⊥, some ⟨c, a⟩ =>
      if a = 0 ∧ c ∧ lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        ⊥
  | some ⟨c, a⟩, ⊤ =>
      if lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then
        some ⟨true, 0⟩
      else if a₂ = 0 then
        if lb₂ = some ⟨true, 0⟩ then
          some ⟨true, 0⟩
        else
          ⊥
      else if lb₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨c₁ && c₂, Dyadic.divDown approxParam a₁ a₂⟩

def UpperBound.dyadic_div
    (approxParam : ℕ) (ub₁ : UpperBound Dyadic) (lb₂ : LowerBound Dyadic)
    (ub₂ : UpperBound Dyadic) :
    UpperBound Dyadic :=
  match ub₁, lb₂ with
  | ⊤, ⊥ => ⊤
  | ⊤, some ⟨c, a⟩ =>
      if a = 0 ∧ c ∧ ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        ⊤
  | some ⟨c, a⟩, ⊥ =>
      if ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨a = 0 ∧ c, 0⟩
  | some ⟨c₁, a₁⟩, some ⟨c₂, a₂⟩ =>
      if a₁ = 0 ∧ c₁ then
        some ⟨true, 0⟩
      else if a₂ = 0 then
        if ub₂ = some ⟨true, 0⟩ then
          some ⟨true, 0⟩
        else
          ⊤
      else if ub₂ = some ⟨true, 0⟩ then
        some ⟨true, 0⟩
      else
        some ⟨c₁ && c₂, Dyadic.divUp approxParam a₁ a₂⟩

def Interval.dyadic_div (approxParam : ℕ) (x y : Interval Dyadic) : Interval Dyadic :=
  match x.toIntervalSignClass, y.toIntervalSignClass with
  | .nonneg, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.ub y.lb,
       x.ub.dyadic_div approxParam y.lb y.ub⟩
  | .nonpos, .nonpos =>
      ⟨x.ub.toLowerBound.dyadic_div approxParam y.lb.toUpperBound y.ub.toLowerBound,
       x.lb.toUpperBound.dyadic_div approxParam y.ub.toLowerBound y.lb.toUpperBound⟩
  | .nonpos, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.lb.toUpperBound y.ub.toLowerBound,
       x.ub.dyadic_div approxParam y.ub.toLowerBound y.lb.toUpperBound⟩
  | .nonneg, .nonpos =>
      ⟨x.ub.toLowerBound.dyadic_div approxParam y.ub y.lb,
       x.lb.toUpperBound.dyadic_div approxParam y.lb y.ub⟩
  | .mixed, .nonneg =>
      ⟨x.lb.dyadic_div approxParam y.lb.toUpperBound y.ub.toLowerBound,
       x.ub.dyadic_div approxParam y.lb y.ub⟩
  | .mixed, .nonpos =>
      ⟨x.ub.toLowerBound.dyadic_div approxParam y.ub y.lb,
       x.lb.toUpperBound.dyadic_div approxParam y.ub.toLowerBound y.lb.toUpperBound⟩
  | .nonneg, .mixed =>
      if x = ⟨some ⟨true, 0⟩, some ⟨true, 0⟩⟩ then
        x
      else
        ⟨⊥, ⊤⟩
  | .nonpos, .mixed =>
      ⟨⊥, ⊤⟩
  | .mixed, .mixed =>
      ⟨⊥, ⊤⟩

lemma dyadic_to_real_ne_zero {a : Dyadic} (h : a ≠ 0) : dyadic_to_real a ≠ 0 := by
  intro hc
  exact h (strictMono_dyadic_to_real.injective (by rw [hc, dyadic_to_real_zero]))

/-- Extract the non-strict inequality from a finite lower bound. -/
lemma LowerBound.some_le {c : Bool} {a : Dyadic} {r : ℝ}
    (h : LowerBound.Bounds dyadic_to_real (some ⟨c, a⟩) r) : dyadic_to_real a ≤ r := by
  cases c <;> simp only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte] at h <;> linarith

/-- Extract the strict inequality from an open finite lower bound. -/
lemma LowerBound.some_lt {c : Bool} {a : Dyadic} {r : ℝ}
    (h : LowerBound.Bounds dyadic_to_real (some ⟨c, a⟩) r) (hc : c = false) :
    dyadic_to_real a < r := by
  subst hc; simpa only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte] using h

/-- Extract the non-strict inequality from a finite upper bound. -/
lemma UpperBound.some_le {c : Bool} {a : Dyadic} {r : ℝ}
    (h : UpperBound.Bounds dyadic_to_real (some ⟨c, a⟩) r) : r ≤ dyadic_to_real a := by
  cases c <;> simp only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte] at h <;> linarith

/-- Extract the strict inequality from an open finite upper bound. -/
lemma UpperBound.some_lt {c : Bool} {a : Dyadic} {r : ℝ}
    (h : UpperBound.Bounds dyadic_to_real (some ⟨c, a⟩) r) (hc : c = false) :
    r < dyadic_to_real a := by
  subst hc; simpa only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte] using h

lemma UpperBound.toLowerBound_eq_some {u : UpperBound Dyadic} {c : Bool} {a : Dyadic}
    (h : u.toLowerBound = some ⟨c, a⟩) : u = some ⟨c, a⟩ := by
  rcases u with _ | ⟨c', a'⟩
  · simp only [UpperBound.toLowerBound] at h; exact absurd h (by simp)
  · simp only [UpperBound.toLowerBound, Option.some.injEq, FiniteLowerBound.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

lemma LowerBound.toUpperBound_eq_some {l : LowerBound Dyadic} {c : Bool} {a : Dyadic}
    (h : l.toUpperBound = some ⟨c, a⟩) : l = some ⟨c, a⟩ := by
  rcases l with _ | ⟨c', a'⟩
  · simp only [LowerBound.toUpperBound] at h; exact absurd h (by simp)
  · simp only [LowerBound.toUpperBound, Option.some.injEq, FiniteUpperBound.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

/-- Division monotonicity (positive denominators), non-strict. -/
lemma real_div_le_div_pos {A₁ A₂ r s : ℝ} (hA₂ : 0 < A₂) (hs : 0 < s) (h : A₁ * s ≤ r * A₂) :
    A₁ / A₂ ≤ r / s := (div_le_div_iff₀ hA₂ hs).mpr h

/-- Division monotonicity (positive denominators), strict. -/
lemma real_div_lt_div_pos {A₁ A₂ r s : ℝ} (hA₂ : 0 < A₂) (hs : 0 < s) (h : A₁ * s < r * A₂) :
    A₁ / A₂ < r / s := (div_lt_div_iff₀ hA₂ hs).mpr h

/-- Division monotonicity (negative denominators), non-strict. -/
lemma real_div_le_div_neg {A₁ A₂ r s : ℝ} (hA₂ : A₂ < 0) (hs : s < 0) (h : A₁ * s ≤ r * A₂) :
    A₁ / A₂ ≤ r / s := by
  rw [← neg_div_neg_eq A₁ A₂, ← neg_div_neg_eq r s]
  exact real_div_le_div_pos (by linarith) (by linarith) (by nlinarith [h])

/-- Division monotonicity (negative denominators), strict. -/
lemma real_div_lt_div_neg {A₁ A₂ r s : ℝ} (hA₂ : A₂ < 0) (hs : s < 0) (h : A₁ * s < r * A₂) :
    A₁ / A₂ < r / s := by
  rw [← neg_div_neg_eq A₁ A₂, ← neg_div_neg_eq r s]
  exact real_div_lt_div_pos (by linarith) (by linarith) (by nlinarith [h])

/-- A closed lower bound at `0` is valid whenever `0 ≤ q`. -/
lemma lb_closed_zero {q : ℝ} (h : 0 ≤ q) :
    LowerBound.Bounds dyadic_to_real (some ⟨true, 0⟩ : LowerBound Dyadic) q := by
  simpa [LowerBound.Bounds, dyadic_to_real_zero] using h

/-- A closed upper bound at `0` is valid whenever `q ≤ 0`. -/
lemma ub_closed_zero {q : ℝ} (h : q ≤ 0) :
    UpperBound.Bounds dyadic_to_real (some ⟨true, 0⟩ : UpperBound Dyadic) q := by
  simpa [UpperBound.Bounds, dyadic_to_real_zero] using h

/-- A lower bound with value `0` and closedness `c`: valid if `0 ≤ q`, and if open (`c = false`)
we additionally need `0 < q`. -/
lemma lb_zero_Bounds {c : Bool} {q : ℝ} (h0 : 0 ≤ q) (hpos : c = false → 0 < q) :
    LowerBound.Bounds dyadic_to_real (some ⟨c, 0⟩ : LowerBound Dyadic) q := by
  cases c <;>
    simp only [LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte, dyadic_to_real_zero]
  · exact hpos rfl
  · exact h0

/-- An upper bound with value `0` and closedness `c`: valid if `q ≤ 0`, and if open (`c = false`)
we additionally need `q < 0`. -/
lemma ub_zero_Bounds {c : Bool} {q : ℝ} (h0 : q ≤ 0) (hneg : c = false → q < 0) :
    UpperBound.Bounds dyadic_to_real (some ⟨c, 0⟩ : UpperBound Dyadic) q := by
  cases c <;>
    simp only [UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte, dyadic_to_real_zero]
  · exact hneg rfl
  · exact h0

/-- Contract for the lower bound of interval division. `lb₁` lower-bounds the numerator `r`;
`ub₂` is the divisor endpoint (we divide by it); `lb₂` is the other denominator endpoint,
used only for zero-detection. The hypotheses discharge each structural branch. -/
lemma LowerBound.dyadic_div_Bounds (p : ℕ) {lb₁ : LowerBound Dyadic}
    {ub₂ : UpperBound Dyadic} {lb₂ : LowerBound Dyadic} {q : ℝ}
    (hz : lb₂ = some ⟨true, 0⟩ → 0 ≤ q)
    (hn1 : ∀ c₁ a₁, lb₁ = some ⟨c₁, a₁⟩ → a₁ = 0 → c₁ = true → 0 ≤ q)
    (htop0 : ub₂ = ⊤ → 0 ≤ q)
    (htoppos : ∀ c₁ a₁, ub₂ = ⊤ → lb₁ = some ⟨c₁, a₁⟩ → ¬(a₁ = 0 ∧ c₁ = true) →
        lb₂ ≠ some ⟨true, 0⟩ → 0 < q)
    (hmain : ∀ c₁ a₁ c₂ a₂, lb₁ = some ⟨c₁, a₁⟩ → ub₂ = some ⟨c₂, a₂⟩ →
        ¬(a₁ = 0 ∧ c₁ = true) → a₂ ≠ 0 → lb₂ ≠ some ⟨true, 0⟩ →
        dyadic_to_real a₁ / dyadic_to_real a₂ ≤ q ∧
        ((c₁ = false ∨ c₂ = false) → dyadic_to_real a₁ / dyadic_to_real a₂ < q)) :
    (LowerBound.dyadic_div p lb₁ ub₂ lb₂).Bounds dyadic_to_real q := by
  rcases lb₁ with _ | ⟨c₁, a₁⟩ <;> rcases ub₂ with _ | ⟨c₂, a₂⟩ <;>
    simp only [LowerBound.dyadic_div]
  · exact LowerBound.bot_Bounds _ _
  · split_ifs with h
    · exact lb_closed_zero (hz h.2.2)
    · exact LowerBound.bot_Bounds _ _
  · split_ifs with h
    · exact lb_closed_zero (hz h)
    · exact lb_zero_Bounds (htop0 rfl)
        (fun hc => htoppos c₁ a₁ rfl rfl (decide_eq_false_iff_not.mp hc) h)
  · split_ifs with h1 h2 h3 h4
    · exact lb_closed_zero (hn1 c₁ a₁ rfl h1.1 h1.2)
    · exact lb_closed_zero (hz h3)
    · exact LowerBound.bot_Bounds _ _
    · exact lb_closed_zero (hz h4)
    · obtain ⟨hle, hlt⟩ := hmain c₁ a₁ c₂ a₂ rfl rfl h1 h2 h4
      simp only [LowerBound.Bounds]
      split_ifs with hcc
      · exact (divDown_le_all p a₁ a₂).trans hle
      · have hcc' : c₁ = false ∨ c₂ = false := by rcases c₁ <;> rcases c₂ <;> simp_all
        exact (divDown_le_all p a₁ a₂).trans_lt (hlt hcc')

/-- Contract for the upper bound of interval division. `ub₁` upper-bounds the numerator `r`;
`lb₂` is the divisor endpoint (we divide by it); `ub₂` is the other denominator endpoint,
used only for zero-detection. -/
lemma UpperBound.dyadic_div_Bounds (p : ℕ) {ub₁ : UpperBound Dyadic}
    {lb₂ : LowerBound Dyadic} {ub₂ : UpperBound Dyadic} {q : ℝ}
    (hz : ub₂ = some ⟨true, 0⟩ → q ≤ 0)
    (hn1 : ∀ c₁ a₁, ub₁ = some ⟨c₁, a₁⟩ → a₁ = 0 → c₁ = true → q ≤ 0)
    (hbot0 : lb₂ = ⊥ → q ≤ 0)
    (hbotneg : ∀ c₁ a₁, lb₂ = ⊥ → ub₁ = some ⟨c₁, a₁⟩ → ¬(a₁ = 0 ∧ c₁ = true) →
        ub₂ ≠ some ⟨true, 0⟩ → q < 0)
    (hmain : ∀ c₁ a₁ c₂ a₂, ub₁ = some ⟨c₁, a₁⟩ → lb₂ = some ⟨c₂, a₂⟩ →
        ¬(a₁ = 0 ∧ c₁ = true) → a₂ ≠ 0 → ub₂ ≠ some ⟨true, 0⟩ →
        q ≤ dyadic_to_real a₁ / dyadic_to_real a₂ ∧
        ((c₁ = false ∨ c₂ = false) → q < dyadic_to_real a₁ / dyadic_to_real a₂)) :
    (UpperBound.dyadic_div p ub₁ lb₂ ub₂).Bounds dyadic_to_real q := by
  rcases ub₁ with _ | ⟨c₁, a₁⟩ <;> rcases lb₂ with _ | ⟨c₂, a₂⟩ <;>
    simp only [UpperBound.dyadic_div]
  · exact UpperBound.top_Bounds _ _
  · split_ifs with h
    · exact ub_closed_zero (hz h.2.2)
    · exact UpperBound.top_Bounds _ _
  · split_ifs with h
    · exact ub_closed_zero (hz h)
    · exact ub_zero_Bounds (hbot0 rfl)
        (fun hc => hbotneg c₁ a₁ rfl rfl (decide_eq_false_iff_not.mp hc) h)
  · split_ifs with h1 h2 h3 h4
    · exact ub_closed_zero (hn1 c₁ a₁ rfl h1.1 h1.2)
    · exact ub_closed_zero (hz h3)
    · exact UpperBound.top_Bounds _ _
    · exact ub_closed_zero (hz h4)
    · obtain ⟨hle, hlt⟩ := hmain c₁ a₁ c₂ a₂ rfl rfl h1 h2 h4
      simp only [UpperBound.Bounds]
      split_ifs with hcc
      · exact hle.trans (le_divUp_all p a₁ a₂)
      · have hcc' : c₁ = false ∨ c₂ = false := by rcases c₁ <;> rcases c₂ <;> simp_all
        exact (hlt hcc').trans_le (le_divUp_all p a₁ a₂)

lemma LowerBound.toUpperBound_ne_top {l : LowerBound Dyadic} (h : l ≠ ⊥) :
    l.toUpperBound ≠ ⊤ := by
  rcases l with _ | ⟨c, a⟩
  · exact absurd rfl h
  · simp [LowerBound.toUpperBound]

lemma UpperBound.toLowerBound_ne_bot {u : UpperBound Dyadic} (h : u ≠ ⊤) :
    u.toLowerBound ≠ ⊥ := by
  rcases u with _ | ⟨c, a⟩
  · exact absurd rfl h
  · simp [UpperBound.toLowerBound]

/-- If a nonneg lower endpoint is not the closed bound `0`, the bounded value is strictly
positive. -/
lemma pos_of_nonneg_lb_ne {s : ℝ} {yl : LowerBound Dyadic} (h0 : zeroLB ≤ yl)
    (hb : LowerBound.Bounds dyadic_to_real yl s) (hne : yl ≠ some ⟨true, 0⟩) : 0 < s := by
  rcases yl with _ | ⟨c, a⟩
  · exact absurd (le_bot_iff.mp h0) (by simp [zeroLB])
  · have ha : 0 ≤ dyadic_to_real a := dyadic_to_real_nonneg (zeroLB_le_coe h0)
    cases c
    · exact lt_of_le_of_lt ha (LowerBound.some_lt hb rfl)
    · exact lt_of_lt_of_le (lt_of_le_of_ne ha
        (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne (by rw [hh]))))) (LowerBound.some_le hb)

/-- If a nonpos upper endpoint is not the closed bound `0`, the bounded value is strictly
negative. -/
lemma neg_of_nonpos_ub_ne {s : ℝ} {yu : UpperBound Dyadic} (h0 : yu ≤ zeroUB)
    (hb : UpperBound.Bounds dyadic_to_real yu s) (hne : yu ≠ some ⟨true, 0⟩) : s < 0 := by
  rcases yu with _ | ⟨c, a⟩
  · exact absurd (top_le_iff.mp h0) (by simp [zeroUB])
  · have ha : dyadic_to_real a ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB h0)
    cases c
    · exact lt_of_lt_of_le (UpperBound.some_lt hb rfl) ha
    · exact lt_of_le_of_lt (UpperBound.some_le hb) (lt_of_le_of_ne ha
        (dyadic_to_real_ne_zero (fun hh => hne (by rw [hh]))))

@[interval_op DyadicReal Div]
theorem Interval.dyadic_div_inclusion {r s : ℝ} {x y : Interval Dyadic}
    (approxParam : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) (hsy : s ∈ y.toSet dyadic_to_real) :
    r / s ∈ (x.dyadic_div approxParam y).toSet dyadic_to_real := by
  cases hx : x.toIntervalSignClass <;> cases hy : y.toIntervalSignClass <;>
    simp only [Interval.mem_toSet, Interval.dyadic_div, hx, hy]
  · -- nonneg, nonneg
    have hr0 : 0 ≤ r := nonneg_of_mem_nonneg_toSet hx hrx
    have hs0 : 0 ≤ s := nonneg_of_mem_nonneg_toSet hy hsy
    have hq0 : 0 ≤ r / s := div_nonneg hr0 hs0
    have hxlb : zeroLB ≤ x.lb := zeroLB_le_lb_of_nonneg hx
    have hylb : zeroLB ≤ y.lb := zeroLB_le_lb_of_nonneg hy
    refine ⟨?_, ?_⟩
    · -- lower: LowerBound.dyadic_div p x.lb y.ub y.lb  (divisor y.ub, zero-detect y.lb)
      refine LowerBound.dyadic_div_Bounds approxParam (fun _ => hq0) (fun _ _ _ _ _ => hq0)
        (fun _ => hq0) ?_ ?_
      · intro c₁ a₁ _ he1 hne1 hne3
        have hsp : 0 < s := pos_of_nonneg_lb_ne hylb hsy.1 hne3
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.1
        have hxlb' : zeroLB ≤ (some ⟨c₁, a₁⟩ : LowerBound Dyadic) := by rw [← he1]; exact hxlb
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroLB_le_coe hxlb')
        have hrp : 0 < r := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hA1nn (LowerBound.some_lt hbr rfl)
          · exact lt_of_lt_of_le (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))) (LowerBound.some_le hbr)
        exact div_pos hrp hsp
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hsp : 0 < s := pos_of_nonneg_lb_ne hylb hsy.1 hne3
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.1
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.2
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hxlb' : zeroLB ≤ (some ⟨c₁, a₁⟩ : LowerBound Dyadic) := by rw [← he1]; exact hxlb
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroLB_le_coe hxlb')
        have hA2p : 0 < dyadic_to_real a₂ := lt_of_lt_of_le hsp hsA2
        have hrp : 0 < r := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hA1nn (LowerBound.some_lt hbr rfl)
          · exact lt_of_lt_of_le (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))) hA1r
        refine ⟨real_div_le_div_pos hA2p hsp ?_, fun hopen => real_div_lt_div_pos hA2p hsp ?_⟩
        · nlinarith [mul_nonneg (sub_nonneg.2 hA1r) hsp.le, mul_nonneg hr0 (sub_nonneg.2 hsA2)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (sub_pos.2 (LowerBound.some_lt hbr hc)) hsp,
              mul_nonneg hr0 (sub_nonneg.2 hsA2)]
          · nlinarith [mul_pos hrp (sub_pos.2 (UpperBound.some_lt hbs hc)),
              mul_nonneg (sub_nonneg.2 hA1r) hsp.le]
    · -- upper: UpperBound.dyadic_div p x.ub y.lb y.ub  (divisor y.lb, zero-detect y.ub)
      refine UpperBound.dyadic_div_Bounds approxParam ?_ ?_ ?_ ?_ ?_
      · intro hub
        have h := hsy.2; rw [hub] at h
        have hsu : s ≤ 0 := by simpa [dyadic_to_real_zero] using UpperBound.some_le h
        rw [le_antisymm hsu hs0]; simp
      · intro c₁ a₁ hu ha _
        have h := hrx.2; rw [hu] at h
        have hru : r ≤ 0 := by
          have := UpperBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        rw [le_antisymm hru hr0]; simp
      · intro hb; rw [hb] at hylb; simp [zeroLB] at hylb
      · intro c₁ a₁ hb _ _ _; rw [hb] at hylb; simp [zeroLB] at hylb
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.2
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.1
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hylb' : zeroLB ≤ (some ⟨c₂, a₂⟩ : LowerBound Dyadic) := by rw [← he2]; exact hylb
        have hA2nn : 0 ≤ dyadic_to_real a₂ := dyadic_to_real_nonneg (zeroLB_le_coe hylb')
        have hA2p : 0 < dyadic_to_real a₂ :=
          lt_of_le_of_ne hA2nn (Ne.symm (dyadic_to_real_ne_zero hne2))
        have hsp : 0 < s := lt_of_lt_of_le hA2p hA2s
        have hA1nn : 0 ≤ dyadic_to_real a₁ := le_trans hr0 hru
        have hA1p : 0 < dyadic_to_real a₁ := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hr0 (UpperBound.some_lt hbu rfl)
          · refine lt_of_le_of_ne hA1nn (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_pos hsp hA2p ?_, fun hopen => real_div_lt_div_pos hsp hA2p ?_⟩
        · nlinarith [mul_nonneg (sub_nonneg.2 hru) hsp.le, mul_nonneg hr0 (sub_nonneg.2 hA2s)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (sub_pos.2 (UpperBound.some_lt hbu hc)) hsp,
              mul_nonneg hr0 (sub_nonneg.2 hA2s)]
          · nlinarith [mul_pos hA1p (sub_pos.2 (LowerBound.some_lt hbs hc)),
              mul_nonneg (sub_nonneg.2 hru) hsp.le]
  · -- nonneg, nonpos
    have hr0 : 0 ≤ r := nonneg_of_mem_nonneg_toSet hx hrx
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hqle : r / s ≤ 0 := by
      have h := div_nonneg hr0 (neg_nonneg.2 hs0); rw [div_neg] at h; linarith
    have hxlb : zeroLB ≤ x.lb := zeroLB_le_lb_of_nonneg hx
    have hyub : y.ub ≤ zeroUB := ub_le_zeroUB_of_nonpos hy
    have hyubnt : y.ub ≠ ⊤ := fun h => by rw [h] at hyub; simp [zeroUB] at hyub
    refine ⟨?_, ?_⟩
    · -- lower: LowerBound.dyadic_div p (x.ub.toLowerBound) y.ub y.lb
      refine LowerBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hyubnt)
        (fun _ _ h _ _ _ => absurd h hyubnt) ?_
      · intro hlb
        have h := hsy.1; rw [hlb] at h
        have hsl : 0 ≤ s := by simpa [dyadic_to_real_zero] using LowerBound.some_le h
        rw [le_antisymm hs0 hsl, div_zero]
      · intro c₁ a₁ hu ha _
        have hxu := UpperBound.toLowerBound_eq_some hu
        have h := hrx.2; rw [hxu] at h
        have hru : r ≤ 0 := by
          have := UpperBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        rw [le_antisymm hru hr0, zero_div]
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxu := UpperBound.toLowerBound_eq_some he1
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxu]; exact hrx.2
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.2
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hyub' := he2 ▸ hyub
        have hA2np : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB hyub')
        have hA2n : dyadic_to_real a₂ < 0 := lt_of_le_of_ne hA2np (dyadic_to_real_ne_zero hne2)
        have hsn : s < 0 := lt_of_le_of_lt hsA2 hA2n
        have hA1nn : 0 ≤ dyadic_to_real a₁ := le_trans hr0 hru
        have hA1p : 0 < dyadic_to_real a₁ := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hr0 (UpperBound.some_lt hbu rfl)
          · exact lt_of_le_of_ne hA1nn (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_neg hA2n hsn ?_, fun hopen => real_div_lt_div_neg hA2n hsn ?_⟩
        · nlinarith [mul_nonneg hr0 (sub_nonneg.2 hsA2),
            mul_nonneg (neg_nonneg.2 hs0) (sub_nonneg.2 hru)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (neg_pos.2 hsn) (sub_pos.2 (UpperBound.some_lt hbu hc)),
              mul_nonneg hr0 (sub_nonneg.2 hsA2)]
          · nlinarith [mul_pos hA1p (sub_pos.2 (UpperBound.some_lt hbs hc)),
              mul_nonneg (sub_nonneg.2 hru) (neg_nonneg.2 hA2np)]
    · -- upper: UpperBound.dyadic_div p (x.lb.toUpperBound) y.lb y.ub
      refine UpperBound.dyadic_div_Bounds approxParam (fun _ => hqle) (fun _ _ _ _ _ => hqle)
        (fun _ => hqle) ?_ ?_
      · intro c₁ a₁ _ hu hne1 hne3
        have hxl := LowerBound.toUpperBound_eq_some hu
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxl]; exact hrx.1
        have hxlb' : zeroLB ≤ (some ⟨c₁, a₁⟩ : LowerBound Dyadic) := by rw [← hxl]; exact hxlb
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroLB_le_coe hxlb')
        have hrp : 0 < r := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hA1nn (LowerBound.some_lt hbr rfl)
          · exact lt_of_lt_of_le (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))) (LowerBound.some_le hbr)
        exact div_neg_of_pos_of_neg hrp (neg_of_nonpos_ub_ne hyub hsy.2 hne3)
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxl := LowerBound.toUpperBound_eq_some he1
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxl]; exact hrx.1
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.1
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hxlb' : zeroLB ≤ (some ⟨c₁, a₁⟩ : LowerBound Dyadic) := by rw [← hxl]; exact hxlb
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroLB_le_coe hxlb')
        have hsn : s < 0 := neg_of_nonpos_ub_ne hyub hsy.2 hne3
        have hA2np : dyadic_to_real a₂ ≤ 0 := le_trans hA2s hs0
        have hA2n : dyadic_to_real a₂ < 0 := lt_of_le_of_ne hA2np (dyadic_to_real_ne_zero hne2)
        have hrp : 0 < r := by
          rcases c₁ with _ | _
          · exact lt_of_le_of_lt hA1nn (LowerBound.some_lt hbr rfl)
          · exact lt_of_lt_of_le (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))) hA1r
        refine ⟨real_div_le_div_neg hsn hA2n ?_, fun hopen => real_div_lt_div_neg hsn hA2n ?_⟩
        · nlinarith [mul_nonneg (neg_nonneg.2 hsn.le) (sub_nonneg.2 hA1r),
            mul_nonneg hr0 (sub_nonneg.2 hA2s)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (neg_pos.2 hsn) (sub_pos.2 (LowerBound.some_lt hbr hc)),
              mul_nonneg hr0 (sub_nonneg.2 hA2s)]
          · nlinarith [mul_pos hrp (sub_pos.2 (LowerBound.some_lt hbs hc)),
              mul_nonneg (neg_nonneg.2 hsn.le) (sub_nonneg.2 hA1r)]
  · -- nonneg, mixed
    split_ifs with hxe
    · rw [hxe] at hrx ⊢
      have h1 := LowerBound.some_le hrx.1
      have h2 := UpperBound.some_le hrx.2
      simp only [dyadic_to_real_zero] at h1 h2
      have hrs : r / s = 0 := by rw [le_antisymm h2 h1, zero_div]
      exact ⟨lb_closed_zero (le_of_eq hrs.symm), ub_closed_zero (le_of_eq hrs)⟩
    · exact ⟨LowerBound.bot_Bounds _ _, UpperBound.top_Bounds _ _⟩
  · -- nonpos, nonneg
    have hr0 : r ≤ 0 := nonpos_of_mem_nonpos_toSet hx hrx
    have hs0 : 0 ≤ s := nonneg_of_mem_nonneg_toSet hy hsy
    have hqle : r / s ≤ 0 := by
      have h := div_nonneg (neg_nonneg.2 hr0) hs0; rw [neg_div] at h; linarith
    have hxub : x.ub ≤ zeroUB := ub_le_zeroUB_of_nonpos hx
    have hylb : zeroLB ≤ y.lb := zeroLB_le_lb_of_nonneg hy
    have hylbnb : y.lb ≠ ⊥ := fun h => by rw [h] at hylb; simp [zeroLB] at hylb
    have hntop : y.lb.toUpperBound ≠ ⊤ := LowerBound.toUpperBound_ne_top hylbnb
    refine ⟨?_, ?_⟩
    · -- lower: LowerBound.dyadic_div p x.lb (y.lb.toUpperBound) (y.ub.toLowerBound)
      refine LowerBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hntop)
        (fun _ _ h _ _ _ => absurd h hntop) ?_
      · intro hlb
        have hyu := UpperBound.toLowerBound_eq_some hlb
        have h := hsy.2; rw [hyu] at h
        have hsu : s ≤ 0 := by simpa [dyadic_to_real_zero] using UpperBound.some_le h
        rw [le_antisymm hsu hs0, div_zero]
      · intro c₁ a₁ hl ha _
        have h := hrx.1; rw [hl] at h
        have hrl : 0 ≤ r := by
          have := LowerBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        rw [le_antisymm hr0 hrl, zero_div]
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hyl := LowerBound.toUpperBound_eq_some he2
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.1
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyl]; exact hsy.1
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hylb' : zeroLB ≤ (some ⟨c₂, a₂⟩ : LowerBound Dyadic) := by rw [← hyl]; exact hylb
        have hA2nn : 0 ≤ dyadic_to_real a₂ := dyadic_to_real_nonneg (zeroLB_le_coe hylb')
        have hA2p : 0 < dyadic_to_real a₂ :=
          lt_of_le_of_ne hA2nn (Ne.symm (dyadic_to_real_ne_zero hne2))
        have hA1np : dyadic_to_real a₁ ≤ 0 := le_trans hA1r hr0
        have hA1neg : dyadic_to_real a₁ < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (LowerBound.some_lt hbr rfl) hr0
          · exact lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩))
        refine ⟨real_div_le_div_pos hA2p (lt_of_lt_of_le hA2p hA2s) ?_,
          fun hopen => real_div_lt_div_pos hA2p (lt_of_lt_of_le hA2p hA2s) ?_⟩
        · nlinarith [mul_nonneg hA2p.le (sub_nonneg.2 hA1r),
            mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos hA2p (sub_pos.2 (LowerBound.some_lt hbr hc)),
              mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
          · nlinarith [mul_pos (neg_pos.2 hA1neg) (sub_pos.2 (LowerBound.some_lt hbs hc)),
              mul_nonneg hA2p.le (sub_nonneg.2 hA1r)]
    · -- upper: UpperBound.dyadic_div p x.ub (y.ub.toLowerBound) (y.lb.toUpperBound)
      refine UpperBound.dyadic_div_Bounds approxParam (fun _ => hqle) (fun _ _ _ _ _ => hqle)
        (fun _ => hqle) ?_ ?_
      · intro c₁ a₁ _ hu hne1 hne3
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hu]; exact hrx.2
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB (hu ▸ hxub))
        have hrneg : r < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (UpperBound.some_lt hbu rfl) hA1np
          · exact lt_of_le_of_lt (UpperBound.some_le hbu)
              (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        exact div_neg_of_neg_of_pos hrneg (pos_of_nonneg_lb_ne hylb hsy.1 (fun h => hne3 (by simp only [h, LowerBound.toUpperBound])))
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hyu := UpperBound.toLowerBound_eq_some he2
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.2
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyu]; exact hsy.2
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB (he1 ▸ hxub))
        have hsp : 0 < s := pos_of_nonneg_lb_ne hylb hsy.1 (fun h => hne3 (by simp only [h, LowerBound.toUpperBound]))
        have hA2p : 0 < dyadic_to_real a₂ := lt_of_lt_of_le hsp hsA2
        have hrneg : r < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (UpperBound.some_lt hbu rfl) hA1np
          · exact lt_of_le_of_lt hru
              (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_pos hsp hA2p ?_, fun hopen => real_div_lt_div_pos hsp hA2p ?_⟩
        · nlinarith [mul_nonneg hsp.le (sub_nonneg.2 hru),
            mul_nonneg (neg_nonneg.2 hr0) (sub_nonneg.2 hsA2)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos hsp (sub_pos.2 (UpperBound.some_lt hbu hc)),
              mul_nonneg (neg_nonneg.2 hr0) (sub_nonneg.2 hsA2)]
          · nlinarith [mul_pos (neg_pos.2 hrneg) (sub_pos.2 (UpperBound.some_lt hbs hc)),
              mul_nonneg hsp.le (sub_nonneg.2 hru)]
  · -- nonpos, nonpos
    have hr0 : r ≤ 0 := nonpos_of_mem_nonpos_toSet hx hrx
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hq0 : 0 ≤ r / s := by
      rw [← neg_div_neg_eq]; exact div_nonneg (neg_nonneg.2 hr0) (neg_nonneg.2 hs0)
    have hxub : x.ub ≤ zeroUB := ub_le_zeroUB_of_nonpos hx
    have hyub : y.ub ≤ zeroUB := ub_le_zeroUB_of_nonpos hy
    have hyubnt : y.ub ≠ ⊤ := fun h => by rw [h] at hyub; simp [zeroUB] at hyub
    have hnbot : y.ub.toLowerBound ≠ ⊥ := UpperBound.toLowerBound_ne_bot hyubnt
    refine ⟨?_, ?_⟩
    · -- lower: (x.ub.toLowerBound).dyadic_div p (y.lb.toUpperBound) (y.ub.toLowerBound)
      refine LowerBound.dyadic_div_Bounds approxParam (fun _ => hq0) (fun _ _ _ _ _ => hq0)
        (fun _ => hq0) ?_ ?_
      · -- htoppos
        intro c₁ a₁ _ he1 hne1 hne3
        have hxu := UpperBound.toLowerBound_eq_some he1
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxu]; exact hrx.2
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB (hxu ▸ hxub))
        have hrneg : r < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (UpperBound.some_lt hbu rfl) hA1np
          · exact lt_of_le_of_lt (UpperBound.some_le hbu)
              (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        have hsn : s < 0 :=
          neg_of_nonpos_ub_ne hyub hsy.2 (fun h => hne3 (by simp only [h, UpperBound.toLowerBound]))
        rw [← neg_div_neg_eq]; exact div_pos (neg_pos.2 hrneg) (neg_pos.2 hsn)
      · -- hmain
        intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxu := UpperBound.toLowerBound_eq_some he1
        have hyl := LowerBound.toUpperBound_eq_some he2
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxu]; exact hrx.2
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyl]; exact hsy.1
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB (hxu ▸ hxub))
        have hsn : s < 0 :=
          neg_of_nonpos_ub_ne hyub hsy.2 (fun h => hne3 (by simp only [h, UpperBound.toLowerBound]))
        have hA2n : dyadic_to_real a₂ < 0 := lt_of_le_of_lt hA2s hsn
        have hrneg : r < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (UpperBound.some_lt hbu rfl) hA1np
          · exact lt_of_le_of_lt (UpperBound.some_le hbu)
              (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_neg hA2n hsn ?_, fun hopen => real_div_lt_div_neg hA2n hsn ?_⟩
        · nlinarith [mul_nonneg (neg_nonneg.2 hA2n.le) (sub_nonneg.2 hru),
            mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (neg_pos.2 hA2n) (sub_pos.2 (UpperBound.some_lt hbu hc)),
              mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
          · nlinarith [mul_pos (neg_pos.2 hrneg) (sub_pos.2 (LowerBound.some_lt hbs hc)),
              mul_nonneg (sub_nonneg.2 hru) (neg_nonneg.2 hsn.le)]
    · -- upper: (x.lb.toUpperBound).dyadic_div p (y.ub.toLowerBound) (y.lb.toUpperBound)
      refine UpperBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hnbot)
        (fun _ _ h _ _ _ => absurd h hnbot) ?_
      · -- hz: ub₂ = y.lb.toUpperBound = ⟨true,0⟩ → q ≤ 0 ; s = 0
        intro hub
        have hyl := LowerBound.toUpperBound_eq_some hub
        have h := hsy.1; rw [hyl] at h
        have hsl : 0 ≤ s := by simpa [dyadic_to_real_zero] using LowerBound.some_le h
        rw [le_antisymm hs0 hsl, div_zero]
      · -- hn1: x.lb = ⟨true,0⟩ → r = 0 → q = 0
        intro c₁ a₁ hu ha _
        have hxl := LowerBound.toUpperBound_eq_some hu
        have h := hrx.1; rw [hxl] at h
        have hrl : 0 ≤ r := by
          have := LowerBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        rw [le_antisymm hr0 hrl, zero_div]
      · -- hmain
        intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxl := LowerBound.toUpperBound_eq_some he1
        have hyu := UpperBound.toLowerBound_eq_some he2
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxl]; exact hrx.1
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyu]; exact hsy.2
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hA1np : dyadic_to_real a₁ ≤ 0 := le_trans hA1r hr0
        have hA2np : dyadic_to_real a₂ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroUB (hyu ▸ hyub))
        have hA2n : dyadic_to_real a₂ < 0 := lt_of_le_of_ne hA2np (dyadic_to_real_ne_zero hne2)
        have hsn : s < 0 := lt_of_le_of_lt hsA2 hA2n
        have hA1neg : dyadic_to_real a₁ < 0 := by
          rcases c₁ with _ | _
          · exact lt_of_lt_of_le (LowerBound.some_lt hbr rfl) hr0
          · exact lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩))
        refine ⟨real_div_le_div_neg hsn hA2n ?_, fun hopen => real_div_lt_div_neg hsn hA2n ?_⟩
        · nlinarith [mul_nonneg (neg_nonneg.2 hsn.le) (sub_nonneg.2 hA1r),
            mul_nonneg (neg_nonneg.2 hr0) (sub_nonneg.2 hsA2)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (neg_pos.2 hsn) (sub_pos.2 (LowerBound.some_lt hbr hc)),
              mul_nonneg (neg_nonneg.2 hr0) (sub_nonneg.2 hsA2)]
          · nlinarith [mul_pos (neg_pos.2 hA1neg) (sub_pos.2 (UpperBound.some_lt hbs hc)),
              mul_nonneg (neg_nonneg.2 hA2n.le) (sub_nonneg.2 hA1r)]
  · -- nonpos, mixed
    exact ⟨LowerBound.bot_Bounds _ _, UpperBound.top_Bounds _ _⟩
  · -- mixed, nonneg
    have hs0 : 0 ≤ s := nonneg_of_mem_nonneg_toSet hy hsy
    have hxlbm : x.lb ≤ zeroLB := lb_le_zeroLB_of_mixed hx
    have hxubm : zeroUB ≤ x.ub := zeroUB_le_ub_of_mixed hx
    have hylb : zeroLB ≤ y.lb := zeroLB_le_lb_of_nonneg hy
    have hylbnb : y.lb ≠ ⊥ := fun h => by rw [h] at hylb; simp [zeroLB] at hylb
    have hntop : y.lb.toUpperBound ≠ ⊤ := LowerBound.toUpperBound_ne_top hylbnb
    refine ⟨?_, ?_⟩
    · -- lower: LowerBound.dyadic_div p x.lb (y.lb.toUpperBound) (y.ub.toLowerBound)
      refine LowerBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hntop)
        (fun _ _ h _ _ _ => absurd h hntop) ?_
      · intro hlb
        have hyu := UpperBound.toLowerBound_eq_some hlb
        have h := hsy.2; rw [hyu] at h
        have hsu : s ≤ 0 := by simpa [dyadic_to_real_zero] using UpperBound.some_le h
        rw [le_antisymm hsu hs0, div_zero]
      · intro c₁ a₁ hl ha _
        have h := hrx.1; rw [hl] at h
        have hr : 0 ≤ r := by
          have := LowerBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        exact div_nonneg hr hs0
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hyl := LowerBound.toUpperBound_eq_some he2
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.1
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyl]; exact hsy.1
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB (he1 ▸ hxlbm))
        have hylb' : zeroLB ≤ (some ⟨c₂, a₂⟩ : LowerBound Dyadic) := by rw [← hyl]; exact hylb
        have hA2p : 0 < dyadic_to_real a₂ :=
          lt_of_le_of_ne (dyadic_to_real_nonneg (zeroLB_le_coe hylb'))
            (Ne.symm (dyadic_to_real_ne_zero hne2))
        have hsp : 0 < s := lt_of_lt_of_le hA2p hA2s
        have hpos : 0 < r ∨ dyadic_to_real a₁ < 0 := by
          rcases c₁ with _ | _
          · rcases eq_or_lt_of_le hA1np with heq | hlt
            · exact Or.inl (heq ▸ LowerBound.some_lt hbr rfl)
            · exact Or.inr hlt
          · exact Or.inr (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_pos hA2p hsp ?_, fun hopen => real_div_lt_div_pos hA2p hsp ?_⟩
        · nlinarith [mul_nonneg hA2p.le (sub_nonneg.2 hA1r),
            mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos hA2p (sub_pos.2 (LowerBound.some_lt hbr hc)),
              mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hA2s)]
          · rcases hpos with hrp | hA1neg
            · nlinarith [mul_pos hrp hA2p, mul_nonneg (neg_nonneg.2 hA1np) hsp.le]
            · nlinarith [mul_pos (neg_pos.2 hA1neg) (sub_pos.2 (LowerBound.some_lt hbs hc)),
                mul_nonneg hA2p.le (sub_nonneg.2 hA1r)]
    · -- upper: UpperBound.dyadic_div p x.ub y.lb y.ub
      refine UpperBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hylbnb)
        (fun _ _ h _ _ _ => absurd h hylbnb) ?_
      · intro hub
        have h := hsy.2; rw [hub] at h
        have hsu : s ≤ 0 := by simpa [dyadic_to_real_zero] using UpperBound.some_le h
        rw [le_antisymm hsu hs0, div_zero]
      · intro c₁ a₁ hu ha _
        have h := hrx.2; rw [hu] at h
        have hr : r ≤ 0 := by
          have := UpperBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        have hh := div_nonneg (neg_nonneg.2 hr) hs0; rw [neg_div] at hh; linarith
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← he1]; exact hrx.2
        have hbs : LowerBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.1
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hA2s : dyadic_to_real a₂ ≤ s := LowerBound.some_le hbs
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe (he1 ▸ hxubm))
        have hylb' : zeroLB ≤ (some ⟨c₂, a₂⟩ : LowerBound Dyadic) := by rw [← he2]; exact hylb
        have hA2p : 0 < dyadic_to_real a₂ :=
          lt_of_le_of_ne (dyadic_to_real_nonneg (zeroLB_le_coe hylb'))
            (Ne.symm (dyadic_to_real_ne_zero hne2))
        have hsp : 0 < s := lt_of_lt_of_le hA2p hA2s
        have hpos : 0 < dyadic_to_real a₁ ∨ r < 0 := by
          rcases c₁ with _ | _
          · rcases eq_or_lt_of_le hA1nn with heq | hlt
            · exact Or.inr (heq ▸ UpperBound.some_lt hbu rfl)
            · exact Or.inl hlt
          · exact Or.inl (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩))))
        refine ⟨real_div_le_div_pos hsp hA2p ?_, fun hopen => real_div_lt_div_pos hsp hA2p ?_⟩
        · nlinarith [mul_nonneg hA1nn (sub_nonneg.2 hA2s), mul_nonneg hA2p.le (sub_nonneg.2 hru)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos hA2p (sub_pos.2 (UpperBound.some_lt hbu hc)),
              mul_nonneg hA1nn (sub_nonneg.2 hA2s)]
          · rcases hpos with hA1p | hrneg
            · nlinarith [mul_pos hA1p (sub_pos.2 (LowerBound.some_lt hbs hc)),
                mul_nonneg hA2p.le (sub_nonneg.2 hru)]
            · nlinarith [mul_pos hA2p (sub_pos.2 (lt_of_lt_of_le hrneg hA1nn)),
                mul_nonneg hA1nn (sub_nonneg.2 hA2s)]
  · -- mixed, nonpos
    have hs0 : s ≤ 0 := nonpos_of_mem_nonpos_toSet hy hsy
    have hxlbm : x.lb ≤ zeroLB := lb_le_zeroLB_of_mixed hx
    have hxubm : zeroUB ≤ x.ub := zeroUB_le_ub_of_mixed hx
    have hyub : y.ub ≤ zeroUB := ub_le_zeroUB_of_nonpos hy
    have hyubnt : y.ub ≠ ⊤ := fun h => by rw [h] at hyub; simp [zeroUB] at hyub
    have hnbot : y.ub.toLowerBound ≠ ⊥ := UpperBound.toLowerBound_ne_bot hyubnt
    refine ⟨?_, ?_⟩
    · -- lower: (x.ub.toLowerBound).dyadic_div p y.ub y.lb
      refine LowerBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hyubnt)
        (fun _ _ h _ _ _ => absurd h hyubnt) ?_
      · intro hlb
        have h := hsy.1; rw [hlb] at h
        have hsl : 0 ≤ s := by simpa [dyadic_to_real_zero] using LowerBound.some_le h
        rw [le_antisymm hs0 hsl, div_zero]
      · intro c₁ a₁ hu ha _
        have hxu := UpperBound.toLowerBound_eq_some hu
        have h := hrx.2; rw [hxu] at h
        have hr : r ≤ 0 := by
          have := UpperBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        rw [← neg_div_neg_eq]; exact div_nonneg (neg_nonneg.2 hr) (neg_nonneg.2 hs0)
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxu := UpperBound.toLowerBound_eq_some he1
        have hbu : UpperBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxu]; exact hrx.2
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← he2]; exact hsy.2
        have hru : r ≤ dyadic_to_real a₁ := UpperBound.some_le hbu
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hA1nn : 0 ≤ dyadic_to_real a₁ := dyadic_to_real_nonneg (zeroUB_le_coe (hxu ▸ hxubm))
        have hA2n : dyadic_to_real a₂ < 0 :=
          lt_of_le_of_ne (dyadic_to_real_nonpos (coe_le_zeroUB (he2 ▸ hyub)))
            (dyadic_to_real_ne_zero hne2)
        have hsn : s < 0 := lt_of_le_of_lt hsA2 hA2n
        have hpos : 0 < dyadic_to_real a₁ ∨ r < 0 := by
          rcases c₁ with _ | _
          · rcases eq_or_lt_of_le hA1nn with heq | hlt
            · exact Or.inr (heq ▸ UpperBound.some_lt hbu rfl)
            · exact Or.inl hlt
          · exact Or.inl (lt_of_le_of_ne hA1nn
              (Ne.symm (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩))))
        refine ⟨real_div_le_div_neg hA2n hsn ?_, fun hopen => real_div_lt_div_neg hA2n hsn ?_⟩
        · nlinarith [mul_nonneg (sub_nonneg.2 hru) (neg_nonneg.2 hA2n.le),
            mul_nonneg hA1nn (sub_nonneg.2 hsA2)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (sub_pos.2 (UpperBound.some_lt hbu hc)) (neg_pos.2 hA2n),
              mul_nonneg hA1nn (sub_nonneg.2 hsA2)]
          · rcases hpos with hA1p | hrneg
            · nlinarith [mul_pos hA1p (sub_pos.2 (UpperBound.some_lt hbs hc)),
                mul_nonneg (sub_nonneg.2 hru) (neg_nonneg.2 hA2n.le)]
            · nlinarith [mul_pos (sub_pos.2 (lt_of_lt_of_le hrneg hA1nn)) (neg_pos.2 hA2n),
                mul_nonneg hA1nn (sub_nonneg.2 hsA2)]
    · -- upper: (x.lb.toUpperBound).dyadic_div p (y.ub.toLowerBound) (y.lb.toUpperBound)
      refine UpperBound.dyadic_div_Bounds approxParam ?_ ?_ (fun h => absurd h hnbot)
        (fun _ _ h _ _ _ => absurd h hnbot) ?_
      · intro hub
        have hyl := LowerBound.toUpperBound_eq_some hub
        have h := hsy.1; rw [hyl] at h
        have hsl : 0 ≤ s := by simpa [dyadic_to_real_zero] using LowerBound.some_le h
        rw [le_antisymm hs0 hsl, div_zero]
      · intro c₁ a₁ hu ha _
        have hxl := LowerBound.toUpperBound_eq_some hu
        have h := hrx.1; rw [hxl] at h
        have hr : 0 ≤ r := by
          have := LowerBound.some_le h; rw [ha] at this; simpa [dyadic_to_real_zero] using this
        have hh := div_nonneg hr (neg_nonneg.2 hs0); rw [div_neg] at hh; linarith
      · intro c₁ a₁ c₂ a₂ he1 he2 hne1 hne2 hne3
        have hxl := LowerBound.toUpperBound_eq_some he1
        have hyu := UpperBound.toLowerBound_eq_some he2
        have hbr : LowerBound.Bounds dyadic_to_real (some ⟨c₁, a₁⟩) r := by rw [← hxl]; exact hrx.1
        have hbs : UpperBound.Bounds dyadic_to_real (some ⟨c₂, a₂⟩) s := by rw [← hyu]; exact hsy.2
        have hA1r : dyadic_to_real a₁ ≤ r := LowerBound.some_le hbr
        have hsA2 : s ≤ dyadic_to_real a₂ := UpperBound.some_le hbs
        have hA1np : dyadic_to_real a₁ ≤ 0 := dyadic_to_real_nonpos (coe_le_zeroLB (hxl ▸ hxlbm))
        have hA2n : dyadic_to_real a₂ < 0 :=
          lt_of_le_of_ne (dyadic_to_real_nonpos (coe_le_zeroUB (hyu ▸ hyub)))
            (dyadic_to_real_ne_zero hne2)
        have hsn : s < 0 := lt_of_le_of_lt hsA2 hA2n
        have hpos : dyadic_to_real a₁ < 0 ∨ 0 < r := by
          rcases c₁ with _ | _
          · rcases eq_or_lt_of_le hA1np with heq | hlt
            · exact Or.inr (heq ▸ LowerBound.some_lt hbr rfl)
            · exact Or.inl hlt
          · exact Or.inl (lt_of_le_of_ne hA1np (dyadic_to_real_ne_zero (fun hh => hne1 ⟨hh, rfl⟩)))
        refine ⟨real_div_le_div_neg hsn hA2n ?_, fun hopen => real_div_lt_div_neg hsn hA2n ?_⟩
        · nlinarith [mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hsA2),
            mul_nonneg (neg_nonneg.2 hA2n.le) (sub_nonneg.2 hA1r)]
        · rcases hopen with hc | hc
          · nlinarith [mul_pos (neg_pos.2 hA2n) (sub_pos.2 (LowerBound.some_lt hbr hc)),
              mul_nonneg (neg_nonneg.2 hA1np) (sub_nonneg.2 hsA2)]
          · rcases hpos with hA1neg | hrp
            · nlinarith [mul_pos (neg_pos.2 hA1neg) (sub_pos.2 (UpperBound.some_lt hbs hc)),
                mul_nonneg (neg_nonneg.2 hA2n.le) (sub_nonneg.2 hA1r)]
            · nlinarith [mul_neg_of_pos_of_neg hrp hA2n,
                mul_nonneg (neg_nonneg.2 hA1np) (neg_nonneg.2 hsn.le)]
  · -- mixed, mixed
    exact ⟨LowerBound.bot_Bounds _ _, UpperBound.top_Bounds _ _⟩

end Div

section Sqrt

namespace Dyadic

/--
`sqrtFloorAndExact approxParam q` returns `(m, exact)` where

* `m / 2^approxParam ≤ sqrt q`;
* `exact = true` iff `m / 2^approxParam = sqrt q`.

For negative `q` we return `(0, true)`, matching `Real.sqrt`'s behavior on negative inputs.
-/
def sqrtFloorAndExact (approxParam : ℕ) (q : Dyadic) : Int × Bool :=
  match q with
  | zero => (0, true)
  | .ofOdd n k _ =>
      if n < 0 then
        (0, true)
      else
        let N : Nat := n.natAbs
        let shift : Int := 2 * (approxParam : Int) - k
        match shift with
        | Int.ofNat s =>
            let scaled : Nat := N <<< s
            let m : Nat := Nat.sqrt scaled
            ((m : Int), if m * m = scaled then true else false)
        | Int.negSucc s =>
            let t : Nat := s + 1
            let denom : Nat := (1 : Nat) <<< t
            let scaledFloor : Nat := N / denom
            let m : Nat := Nat.sqrt scaledFloor
            ((m : Int), if (m * m) * denom = N then true else false)

/-- Dyadic lower approximation to `sqrt q`. -/
def sqrtDown (approxParam : ℕ) (q : Dyadic) : Dyadic :=
  let r := sqrtFloorAndExact approxParam q
  Dyadic.ofIntWithPrec r.1 approxParam

/-- Dyadic upper approximation to `sqrt q`. -/
def sqrtUp (approxParam : ℕ) (q : Dyadic) : Dyadic :=
  let r := sqrtFloorAndExact approxParam q
  let m := r.1
  let exact := r.2
  Dyadic.ofIntWithPrec (if exact then m else m + 1) approxParam

/-- Whether `sqrt q` is exactly representable at precision `approxParam`. -/
def sqrtExact (approxParam : ℕ) (q : Dyadic) : Bool :=
  (sqrtFloorAndExact approxParam q).2

end Dyadic

def Interval.dyadic_sqrt (approxParam : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb :=
    match x.lb with
    | ⊥ => some ⟨true, 0⟩
    | some ⟨c, a⟩ =>
        if a < 0 then
          some ⟨true, 0⟩
        else
          let r := Dyadic.sqrtFloorAndExact approxParam a
          some ⟨c && r.2, Dyadic.ofIntWithPrec r.1 approxParam⟩
  ub :=
    match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ =>
        if a ≤ 0 then
          some ⟨true, 0⟩
        else
          let r := Dyadic.sqrtFloorAndExact approxParam a
          let m := if r.2 then r.1 else r.1 + 1
          some ⟨c && r.2, Dyadic.ofIntWithPrec m approxParam⟩

/-- Real value of a dyadic built by `ofIntWithPrec`, namely `i * 2 ^ (-prec)`. -/
lemma dyadic_to_real_ofIntWithPrec (i : ℤ) (prec : ℕ) :
    dyadic_to_real (Dyadic.ofIntWithPrec i prec) = (i : ℝ) / (2 : ℝ) ^ prec := by
  simp only [dyadic_to_real, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  push_cast
  rw [zpow_neg, zpow_natCast]
  ring

/-- Real value of a dyadic `ofOdd n k`, namely `n * 2 ^ (-k)`. -/
lemma dyadic_to_real_ofOdd (n k : ℤ) (hn : n % 2 = 1) :
    dyadic_to_real (Dyadic.ofOdd n k hn) = (n : ℝ) * (2 : ℝ) ^ (-k) := by
  simp only [dyadic_to_real, Dyadic.toRat_ofOdd_eq_mul_two_pow]
  push_cast
  ring

private lemma ite_true_eq_true_iff {P : Prop} [Decidable P] :
    ((if P then (true : Bool) else false) = true) ↔ P := by
  by_cases h : P <;> simp [h]

/--
Correctness of `Dyadic.sqrtFloorAndExact`. Writing `m := (sqrtFloorAndExact prec a).1` and
`e := (sqrtFloorAndExact prec a).2`, for a nonnegative dyadic `a` we have:
* the dyadic `m / 2 ^ prec` squares to at most `a`;
* the dyadic `(m + 1) / 2 ^ prec` squares to strictly more than `a`;
* `e = true` iff `(m / 2 ^ prec) ^ 2 = a` exactly.
-/
lemma sqrtFloorAndExact_bounds (prec : ℕ) (a : Dyadic) (ha : 0 ≤ a) :
    0 ≤ (Dyadic.sqrtFloorAndExact prec a).1 ∧
    (dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec)) ^ 2
        ≤ dyadic_to_real a ∧
    dyadic_to_real a <
        (dyadic_to_real (Dyadic.ofIntWithPrec ((Dyadic.sqrtFloorAndExact prec a).1 + 1) prec)) ^ 2 ∧
    ((Dyadic.sqrtFloorAndExact prec a).2 = true ↔
      (dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec)) ^ 2
        = dyadic_to_real a) := by
  have hA : (0 : ℝ) ≤ dyadic_to_real a := dyadic_to_real_nonneg ha
  have hD2 : (0 : ℝ) < ((2 : ℝ) ^ prec) ^ 2 := by positivity
  suffices h : 0 ≤ (Dyadic.sqrtFloorAndExact prec a).1 ∧
      ((Dyadic.sqrtFloorAndExact prec a).1 : ℝ) ^ 2 ≤ dyadic_to_real a * ((2 : ℝ) ^ prec) ^ 2 ∧
      dyadic_to_real a * ((2 : ℝ) ^ prec) ^ 2 <
        (((Dyadic.sqrtFloorAndExact prec a).1 : ℝ) + 1) ^ 2 ∧
      ((Dyadic.sqrtFloorAndExact prec a).2 = true ↔
        ((Dyadic.sqrtFloorAndExact prec a).1 : ℝ) ^ 2 = dyadic_to_real a * ((2 : ℝ) ^ prec) ^ 2) by
    obtain ⟨hm0, hlbS, hubS, hexS⟩ := h
    refine ⟨hm0, ?_, ?_, ?_⟩
    · rw [dyadic_to_real_ofIntWithPrec, div_pow, div_le_iff₀ hD2]; exact hlbS
    · rw [dyadic_to_real_ofIntWithPrec, div_pow, lt_div_iff₀ hD2]; push_cast; exact hubS
    · rw [dyadic_to_real_ofIntWithPrec, div_pow, div_eq_iff (ne_of_gt hD2)]; exact hexS
  rcases a with _ | ⟨n, k, hn⟩
  · refine ⟨le_refl 0, ?_, ?_, ?_⟩ <;>
      simp only [Dyadic.sqrtFloorAndExact, Dyadic.zero_eq, dyadic_to_real_zero, Int.cast_zero,
        zero_mul] <;> norm_num
  · have h2k : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
    have hApos : (0 : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ (-k) := by rw [← dyadic_to_real_ofOdd]; exact hA
    have hn0r : (0 : ℝ) ≤ (n : ℝ) := by
      by_contra hcon; rw [not_le] at hcon
      exact absurd hApos (not_le.mpr (mul_neg_of_neg_of_pos hcon h2k))
    have hn0 : 0 ≤ n := by exact_mod_cast hn0r
    have hn_pos : 0 < n := by
      rcases hn0.lt_or_eq with h | h
      · exact h
      · omega
    have hNr : ((n.natAbs : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast (n.natAbs), Int.natAbs_of_nonneg hn_pos.le]
    have hpow : ((2 : ℝ) ^ prec) ^ 2 = (2 : ℝ) ^ (2 * (prec : ℤ)) := by
      rw [← pow_mul, ← zpow_natCast (2 : ℝ) (prec * 2)]; congr 1; push_cast; ring
    have hSeq : dyadic_to_real (Dyadic.ofOdd n k hn) * ((2 : ℝ) ^ prec) ^ 2
        = (n : ℝ) * (2 : ℝ) ^ (2 * (prec : ℤ) - k) := by
      rw [dyadic_to_real_ofOdd, hpow, mul_assoc, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
        neg_add_eq_sub]
    rw [hSeq]
    simp only [Dyadic.sqrtFloorAndExact]
    split_ifs with hlt
    · exfalso; omega
    · split
      · rename_i s heq
        dsimp only
        rw [heq, Int.ofNat_eq_natCast, zpow_natCast]
        have hscaled : ((n.natAbs <<< s : ℕ) : ℝ) = (n : ℝ) * (2 : ℝ) ^ s := by
          rw [Nat.shiftLeft_eq]; push_cast; rw [hNr]
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · rw [← hscaled]; push_cast; exact_mod_cast Nat.sqrt_le' (n.natAbs <<< s)
        · rw [← hscaled]; push_cast
          have := Nat.lt_succ_sqrt' (n.natAbs <<< s)
          simp only [Nat.succ_eq_add_one] at this
          exact_mod_cast this
        · rw [ite_true_eq_true_iff, ← hscaled, pow_two]; push_cast
          constructor <;> intro h <;> exact_mod_cast h
      · rename_i s heq
        dsimp only
        have hdenom : ((1 <<< (s + 1) : ℕ) : ℝ) = (2 : ℝ) ^ (s + 1) := by
          rw [Nat.one_shiftLeft]; push_cast; ring
        have hSneg : (n : ℝ) * (2 : ℝ) ^ (2 * (prec : ℤ) - k) = (n : ℝ) / (2 : ℝ) ^ (s + 1) := by
          rw [heq, Int.negSucc_eq, zpow_neg,
            show ((s : ℤ) + 1) = ((s + 1 : ℕ) : ℤ) from by push_cast; ring, zpow_natCast]
          ring
        rw [hSneg]
        have hdenpos : (0 : ℝ) < (2 : ℝ) ^ (s + 1) := by positivity
        have hdenpos_nat : 0 < (1 <<< (s + 1) : ℕ) := by
          rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos _
        refine ⟨by positivity, ?_, ?_, ?_⟩
        · push_cast
          calc ((Nat.sqrt (n.natAbs / 1 <<< (s + 1)) : ℝ)) ^ 2
              = ((Nat.sqrt (n.natAbs / 1 <<< (s + 1)) ^ 2 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((n.natAbs / 1 <<< (s + 1) : ℕ) : ℝ) := by exact_mod_cast Nat.sqrt_le' _
            _ ≤ ((n.natAbs : ℕ) : ℝ) / ((1 <<< (s + 1) : ℕ) : ℝ) := Nat.cast_div_le
            _ = (n : ℝ) / (2 : ℝ) ^ (s + 1) := by rw [hNr, hdenom]
        · push_cast
          have hd1 : (n : ℝ) / (2 : ℝ) ^ (s + 1) < ((n.natAbs / 1 <<< (s + 1) : ℕ) : ℝ) + 1 := by
            rw [div_lt_iff₀ hdenpos, ← hNr, ← hdenom]
            have hnat : n.natAbs < (n.natAbs / 1 <<< (s + 1) + 1) * (1 <<< (s + 1)) := by
              have := Nat.lt_mul_div_succ n.natAbs hdenpos_nat
              rw [Nat.mul_comm] at this; exact this
            exact_mod_cast hnat
          have hd2 : ((n.natAbs / 1 <<< (s + 1) : ℕ) : ℝ) + 1
              ≤ ((Nat.sqrt (n.natAbs / 1 <<< (s + 1)) : ℝ) + 1) ^ 2 := by
            have hsq : n.natAbs / 1 <<< (s + 1) + 1
                ≤ (Nat.sqrt (n.natAbs / 1 <<< (s + 1)) + 1) ^ 2 := by
              have := Nat.lt_succ_sqrt' (n.natAbs / 1 <<< (s + 1))
              simp only [Nat.succ_eq_add_one] at this; omega
            calc ((n.natAbs / 1 <<< (s + 1) : ℕ) : ℝ) + 1
                = (((n.natAbs / 1 <<< (s + 1)) + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ (((Nat.sqrt (n.natAbs / 1 <<< (s + 1)) + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hsq
              _ = ((Nat.sqrt (n.natAbs / 1 <<< (s + 1)) : ℝ) + 1) ^ 2 := by push_cast; ring
          linarith
        · rw [ite_true_eq_true_iff, eq_div_iff (ne_of_gt hdenpos), pow_two, ← hdenom, ← hNr]
          push_cast
          constructor <;> intro h <;> exact_mod_cast h

/-- `Real.sqrt` form of `sqrtFloorAndExact_bounds`: the lower dyadic is `≤ √a`, the upper dyadic
is `> √a`, and the exactness flag records when the lower dyadic equals `√a`. -/
lemma sqrtFloorAndExact_sqrt_bounds (prec : ℕ) (a : Dyadic) (ha : 0 ≤ a) :
    0 ≤ dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec) ∧
    dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec)
        ≤ √(dyadic_to_real a) ∧
    √(dyadic_to_real a) <
        dyadic_to_real (Dyadic.ofIntWithPrec ((Dyadic.sqrtFloorAndExact prec a).1 + 1) prec) ∧
    ((Dyadic.sqrtFloorAndExact prec a).2 = true ↔
      dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec)
        = √(dyadic_to_real a)) := by
  obtain ⟨hm0, hlb, hub, hex⟩ := sqrtFloorAndExact_bounds prec a ha
  have hA : (0 : ℝ) ≤ dyadic_to_real a := dyadic_to_real_nonneg ha
  have hL0 : 0 ≤ dyadic_to_real (Dyadic.ofIntWithPrec (Dyadic.sqrtFloorAndExact prec a).1 prec) := by
    rw [dyadic_to_real_ofIntWithPrec]
    apply div_nonneg
    · exact_mod_cast hm0
    · positivity
  have hU0 : 0 < dyadic_to_real
      (Dyadic.ofIntWithPrec ((Dyadic.sqrtFloorAndExact prec a).1 + 1) prec) := by
    rw [dyadic_to_real_ofIntWithPrec]
    apply _root_.div_pos
    · exact_mod_cast (by omega : (0 : ℤ) < (Dyadic.sqrtFloorAndExact prec a).1 + 1)
    · positivity
  refine ⟨hL0, (Real.le_sqrt hL0 hA).mpr hlb, (Real.sqrt_lt' hU0).mpr hub, ?_⟩
  rw [hex]
  constructor
  · intro h; rw [← h]; exact (Real.sqrt_sq hL0).symm
  · intro h; rw [h]; exact Real.sq_sqrt hA

@[interval_op DyadicReal Sqrt]
theorem Interval.dyadic_sqrt_inclusion {r : ℝ} {x : Interval Dyadic} (approxParam : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) :
    √ r ∈ (x.dyadic_sqrt approxParam).toSet dyadic_to_real := by
  have hlt_sqrt : ∀ {u v : ℝ}, u < v → 0 < v → √u < √v := by
    intro u v huv hv
    by_cases hu : 0 ≤ u
    · exact Real.sqrt_lt_sqrt hu huv
    · rw [not_le] at hu; rw [Real.sqrt_eq_zero_of_nonpos hu.le]; exact Real.sqrt_pos.mpr hv
  rw [Interval.mem_toSet] at hrx
  obtain ⟨hlb, hub⟩ := hrx
  rw [Interval.mem_toSet]
  refine ⟨?_, ?_⟩
  · -- Lower bound of the square-root interval.
    rcases hxlb : x.lb with _ | ⟨c, a⟩ <;> rw [hxlb] at hlb <;>
      simp only [Interval.dyadic_sqrt, hxlb]
    · simp only [LowerBound.Bounds, dyadic_to_real_zero, if_true]
      exact Real.sqrt_nonneg r
    · by_cases ha0 : a < 0
      · rw [if_pos ha0]
        simp only [LowerBound.Bounds, dyadic_to_real_zero, if_true]
        exact Real.sqrt_nonneg r
      · rw [if_neg ha0]
        have ha : (0 : Dyadic) ≤ a := not_lt.mp ha0
        obtain ⟨hL0, hLsqrt, hsqrtU, hexiff⟩ := sqrtFloorAndExact_sqrt_bounds approxParam a ha
        simp only [LowerBound.Bounds] at hlb ⊢
        cases c
        · simp only [Bool.false_and, if_false, Bool.false_eq_true] at hlb ⊢
          exact lt_of_le_of_lt hLsqrt
            (hlt_sqrt hlb (lt_of_le_of_lt (dyadic_to_real_nonneg ha) hlb))
        · simp only [Bool.true_and, if_true] at hlb ⊢
          have hAr : √(dyadic_to_real a) ≤ √r := Real.sqrt_le_sqrt hlb
          split_ifs with he
          · rw [hexiff.mp he]; exact hAr
          · exact lt_of_lt_of_le (lt_of_le_of_ne hLsqrt (fun heq => he (hexiff.mpr heq))) hAr
  · -- Upper bound of the square-root interval.
    rcases hxub : x.ub with _ | ⟨c, a⟩ <;> rw [hxub] at hub <;>
      simp only [Interval.dyadic_sqrt, hxub]
    · simp only [UpperBound.Bounds]
    · by_cases ha0 : a ≤ 0
      · rw [if_pos ha0]
        simp only [UpperBound.Bounds, dyadic_to_real_zero, if_true]
        have hAnp : dyadic_to_real a ≤ 0 := dyadic_to_real_nonpos ha0
        simp only [UpperBound.Bounds] at hub
        have hr0 : r ≤ 0 := by
          cases c
          · simp only [Bool.false_eq_true, if_false] at hub; linarith
          · simp only [if_true] at hub; linarith
        rw [Real.sqrt_eq_zero_of_nonpos hr0]
      · rw [if_neg ha0]
        have ha : (0 : Dyadic) ≤ a := le_of_lt (not_le.mp ha0)
        have hApos : (0 : ℝ) < dyadic_to_real a := dyadic_to_real_pos (not_le.mp ha0)
        obtain ⟨hL0, hLsqrt, hsqrtU, hexiff⟩ := sqrtFloorAndExact_sqrt_bounds approxParam a ha
        simp only [UpperBound.Bounds] at hub ⊢
        cases c
        · simp only [Bool.false_and, if_false, Bool.false_eq_true] at hub ⊢
          split_ifs with he
          · rw [hexiff.mp he]; exact hlt_sqrt hub hApos
          · exact lt_of_le_of_lt (Real.sqrt_le_sqrt hub.le) hsqrtU
        · simp only [Bool.true_and, if_true] at hub ⊢
          split_ifs with he
          · rw [hexiff.mp he]; exact Real.sqrt_le_sqrt hub
          · exact lt_of_le_of_lt (Real.sqrt_le_sqrt hub) hsqrtU

end Sqrt

section Exp

def bitLenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
      if n = 0 then
        0
      else
        1 + bitLenAux fuel (n / 2)

def _root_.Nat.bitLen (n : ℕ) : ℕ :=
  bitLenAux n n

/--
Choose the number of Taylor terms from the dyadic precision.

This is a cheap Stirling-style heuristic for the reduced range `0 ≤ x ≤ 1/2`.
It is not needed for soundness: any number of Taylor terms gives a valid
enclosure, just possibly a wider one.
-/
def expTaylorTerms (prec : ℕ) : ℕ :=
  let L := prec.bitLen
  let LL := L.bitLen
  let denom := max 1 (L - LL + 1)
  max 8 (prec / denom + 80)

def _root_.Dyadic.divPowTwo (x : Dyadic) (k : ℕ) : Dyadic :=
  match x with
  | zero => 0
  | .ofOdd n e _ => Dyadic.ofIntWithPrec n (e + k)

def squareIter : ℕ → Dyadic → Dyadic
  | 0, x => x
  | k + 1, x => squareIter k (x * x)

def expReductionSteps (x : Dyadic) : ℕ :=
  match x with
  | zero => 0
  | .ofOdd n e _ =>
      let L := n.natAbs.bitLen
      match e with
      | Int.ofNat eNat => L - eNat
      | Int.negSucc s => L + (s + 1)

def expTaylorLowerAux (prec : ℕ) (x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic
  | 0, _k, _term, sum => sum
  | n + 1, k, term, sum =>
      let next := Dyadic.divDown prec (term * x) ((k + 1 : ℕ) : Dyadic)
      if next = 0 then
        sum
      else
        expTaylorLowerAux prec x n (k + 1) next (sum + next)

def expTaylorLower (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  expTaylorLowerAux prec x terms 0 1 1

def expTaylorUpperAux (prec : ℕ) (x : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic × Dyadic × ℕ
  | 0, k, term, sum =>
      let next := Dyadic.divUp prec (term * x) ((k + 1 : ℕ) : Dyadic)
      (sum, next, k + 1)
  | n + 1, k, term, sum =>
      let next := Dyadic.divUp prec (term * x) ((k + 1 : ℕ) : Dyadic)
      expTaylorUpperAux prec x n (k + 1) next (sum + next)

def expTaylorUpper (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let st := expTaylorUpperAux prec x terms 0 1 1
  let sum := st.1
  let next := st.2.1
  let k := st.2.2
  let K : Dyadic := ((k + 1 : ℕ) : Dyadic)
  sum + Dyadic.divUp prec (next * K) (K - x)

/-- Lower approximation for `exp x`, intended for `0 ≤ x`. -/
def expNonnegDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps x
  let x' := x.divPowTwo k
  squareIter k (expTaylorLower prec terms x')

/-- Upper approximation for `exp x`, intended for `0 ≤ x`. -/
def expNonnegUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  let k := expReductionSteps x
  let x' := x.divPowTwo k
  squareIter k (expTaylorUpper prec terms x')

def expDown (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    Dyadic.divDown prec 1 (expNonnegUp prec terms (-x))
  else
    expNonnegDown prec terms x

def expUp (prec terms : ℕ) (x : Dyadic) : Dyadic :=
  if x < 0 then
    Dyadic.divUp prec 1 (expNonnegDown prec terms (-x))
  else
    expNonnegUp prec terms x

def Interval.dyadic_exp (approxParam : ℕ) (x : Interval Dyadic) : Interval Dyadic where
  lb :=
    match x.lb with
    | ⊥ => some ⟨false, 0⟩
    | some ⟨c, a⟩ =>
        some ⟨c, expDown approxParam (expTaylorTerms approxParam) a⟩
  ub :=
    match x.ub with
    | ⊤ => ⊤
    | some ⟨c, a⟩ =>
        some ⟨c, expUp approxParam (expTaylorTerms approxParam) a⟩

/-! ### Helper lemmas for `exp` soundness

These prove that the `exp` interval operation is sound. The strategy:
* `divDown`/`divUp` round toward/away giving one-sided real bounds;
* `squareIter`/`divPowTwo` transfer to `(·)^(2^k)` and `·/2^k`;
* `expReductionSteps` reduces the argument to `0 ≤ x' < 1`;
* the truncated Taylor sums bracket `exp x'` (lower: `Real.sum_le_exp_of_nonneg`;
  upper: partial sum plus a sharp geometric tail bound). -/

lemma dyadic_to_real_one : dyadic_to_real 1 = 1 := by
  have h : (1 : Dyadic).toRat = 1 := by decide
  rw [dyadic_to_real, h, Rat.cast_one]

lemma dyadic_to_real_natCast (n : ℕ) : dyadic_to_real (n : Dyadic) = n := by
  rw [dyadic_to_real, Dyadic.toRat_natCast]; norm_cast

lemma dyadic_to_real_add (a b : Dyadic) :
    dyadic_to_real (a + b) = dyadic_to_real a + dyadic_to_real b := by
  simp only [dyadic_to_real, Dyadic.toRat_add]; norm_cast

lemma dyadic_to_real_sub (a b : Dyadic) :
    dyadic_to_real (a - b) = dyadic_to_real a - dyadic_to_real b := by
  simp only [dyadic_to_real, Dyadic.toRat_sub]; norm_cast

lemma dyadic_to_real_ofIntWithPrec_int (i prec : ℤ) :
    dyadic_to_real (Dyadic.ofIntWithPrec i prec) = (i : ℝ) / (2 : ℝ) ^ prec := by
  rw [dyadic_to_real, Dyadic.toRat_ofIntWithPrec_eq_mul_two_pow]
  push_cast
  rw [zpow_neg]
  ring

/-- `divDown` rounds down: its real value is at most the true quotient. -/
lemma divDown_le (p : ℕ) {a b : Dyadic} (hb : 0 < b) :
    dyadic_to_real (Dyadic.divDown p a b) ≤ dyadic_to_real a / dyadic_to_real b := by
  have hbr : 0 < dyadic_to_real b := dyadic_to_real_pos hb
  have key : Dyadic.divDown p a b * b ≤ a := Dyadic.divAtPrec_mul_le hb (p : ℤ)
  have hmono := strictMono_dyadic_to_real.monotone key
  rw [dyadic_to_real_mul] at hmono
  rw [le_div_iff₀ hbr]
  exact hmono

/-- `divUp` rounds up: its real value is at least the true quotient. -/
lemma le_divUp (p : ℕ) {a b : Dyadic} (hb : 0 < b) :
    dyadic_to_real a / dyadic_to_real b ≤ dyadic_to_real (Dyadic.divUp p a b) := by
  have h := divDown_le p (a := -a) hb
  rw [dyadic_to_real_neg, neg_div] at h
  rw [Dyadic.divUp, dyadic_to_real_neg]
  linarith

/-- `divDown` of a nonnegative numerator by a positive denominator is nonnegative. -/
lemma divDown_nonneg (p : ℕ) {a b : Dyadic}
    (ha : 0 ≤ dyadic_to_real a) (hb : 0 < dyadic_to_real b) :
    0 ≤ dyadic_to_real (Dyadic.divDown p a b) := by
  have har : (0 : ℚ) ≤ a.toRat := by rw [dyadic_to_real] at ha; exact_mod_cast ha
  have hbr : (0 : ℚ) < b.toRat := by rw [dyadic_to_real] at hb; exact_mod_cast hb
  rw [dyadic_to_real]
  have hnn : (0 : ℚ) ≤ (Dyadic.divDown p a b).toRat := by
    cases b with
    | zero => rw [show (Dyadic.zero).toRat = (0 : ℚ) from rfl] at hbr; exact absurd hbr (lt_irrefl 0)
    | ofOdd n e hn =>
      simp only [Dyadic.divDown, Dyadic.divAtPrec]
      rw [Rat.toRat_toDyadic]
      apply div_nonneg _ (by positivity)
      have hx0 : (0 : ℚ) ≤ a.toRat / (Dyadic.ofOdd n e hn).toRat * 2 ^ (p : ℤ) :=
        mul_nonneg (div_nonneg har hbr.le) (by positivity)
      exact_mod_cast Int.floor_nonneg.mpr hx0
  exact_mod_cast hnn

/-- Iterated squaring computes `(·)^(2^k)`. -/
lemma dyadic_to_real_squareIter (k : ℕ) (y : Dyadic) :
    dyadic_to_real (squareIter k y) = (dyadic_to_real y) ^ (2 ^ k) := by
  induction k generalizing y with
  | zero => simp [squareIter]
  | succ k ih =>
    rw [squareIter, ih, dyadic_to_real_mul,
      show dyadic_to_real y * dyadic_to_real y = (dyadic_to_real y) ^ 2 from (sq _).symm,
      ← pow_mul]
    congr 1
    rw [pow_succ]; ring

/-- Dividing by `2^k` via `divPowTwo`. -/
lemma dyadic_to_real_divPowTwo (x : Dyadic) (k : ℕ) :
    dyadic_to_real (x.divPowTwo k) = dyadic_to_real x / 2 ^ k := by
  cases x with
  | zero => simp [Dyadic.divPowTwo, dyadic_to_real_zero]
  | ofOdd n e hn =>
    rw [Dyadic.divPowTwo, dyadic_to_real_ofIntWithPrec_int, Dyadic.ofOdd_eq_ofIntWithPrec,
      dyadic_to_real_ofIntWithPrec_int, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast,
      div_div]

/-- `n < 2 ^ (bitLenAux fuel n)` when `fuel` is at least `n`. -/
lemma bitLenAux_lt (fuel : ℕ) : ∀ n, n ≤ fuel → n < 2 ^ (bitLenAux fuel n) := by
  induction fuel with
  | zero => intro n hn; simp only [bitLenAux, pow_zero]; omega
  | succ fuel ih =>
    intro n hn
    rw [bitLenAux]
    by_cases h0 : n = 0
    · subst h0; simp
    · simp only [h0, if_false]
      have hn2 : n / 2 ≤ fuel := by omega
      have hb := ih (n / 2) hn2
      calc n < 2 * (n / 2 + 1) := by omega
        _ ≤ 2 * 2 ^ (bitLenAux fuel (n / 2)) := by omega
        _ = 2 ^ (1 + bitLenAux fuel (n / 2)) := by rw [pow_add]; ring

/-- A natural number is below `2` to the power of its bit-length. -/
lemma lt_two_pow_bitLen (n : ℕ) : n < 2 ^ n.bitLen := bitLenAux_lt n n le_rfl

/-- The reduction exponent `expReductionSteps` is large enough: `L ≤ e + k`. -/
lemma le_e_add_expReductionSteps (n e : ℤ) (hn : n % 2 = 1) :
    (n.natAbs.bitLen : ℤ) ≤ e + (expReductionSteps (Dyadic.ofOdd n e hn) : ℤ) := by
  cases e with
  | ofNat eNat =>
    have hval : expReductionSteps (Dyadic.ofOdd n (Int.ofNat eNat) hn)
        = n.natAbs.bitLen - eNat := rfl
    rw [hval, Int.ofNat_eq_natCast]; omega
  | negSucc s =>
    have hval : expReductionSteps (Dyadic.ofOdd n (Int.negSucc s) hn)
        = n.natAbs.bitLen + (s + 1) := rfl
    rw [hval]; omega

/-- The range-reduced argument is nonnegative. -/
lemma expReduction_nonneg {x : Dyadic} (hx : 0 ≤ x) :
    0 ≤ dyadic_to_real (x.divPowTwo (expReductionSteps x)) := by
  rw [dyadic_to_real_divPowTwo]
  exact div_nonneg (dyadic_to_real_nonneg hx) (by positivity)

/-- The range-reduced argument is `< 1`. -/
lemma expReduction_lt_one {x : Dyadic} (hx : 0 ≤ x) :
    dyadic_to_real (x.divPowTwo (expReductionSteps x)) < 1 := by
  cases x with
  | zero => rw [dyadic_to_real_divPowTwo]; simp [dyadic_to_real_zero]
  | ofOdd n e hn =>
    have hxnn : (0 : ℝ) ≤ dyadic_to_real (Dyadic.ofOdd n e hn) := dyadic_to_real_nonneg hx
    rw [dyadic_to_real_ofOdd] at hxnn
    have h2e : (0 : ℝ) < 2 ^ (-e) := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := (mul_nonneg_iff_of_pos_right h2e).mp hxnn
    have hn0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    rw [Dyadic.divPowTwo, dyadic_to_real_ofIntWithPrec_int, div_lt_one (by positivity)]
    have hL := le_e_add_expReductionSteps n e hn
    have hnabs : (n : ℝ) = (n.natAbs : ℝ) := by
      have h : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn0'
      calc (n : ℝ) = ((n.natAbs : ℤ) : ℝ) := by rw [h]
        _ = (n.natAbs : ℝ) := Int.cast_natCast _
    calc (n : ℝ) = (n.natAbs : ℝ) := hnabs
      _ < ((2 ^ n.natAbs.bitLen : ℕ) : ℝ) := by exact_mod_cast lt_two_pow_bitLen n.natAbs
      _ = (2 : ℝ) ^ (n.natAbs.bitLen : ℤ) := by simp [zpow_natCast]
      _ ≤ (2 : ℝ) ^ (e + (expReductionSteps (Dyadic.ofOdd n e hn) : ℤ)) :=
          zpow_le_zpow_right₀ (by norm_num) hL

/-- Range reduction for `exp`: `exp X = (exp (X / 2^k))^(2^k)`. -/
lemma exp_range_reduction (X : ℝ) (k : ℕ) :
    Real.exp X = (Real.exp (X / 2 ^ k)) ^ (2 ^ k) := by
  have hne : (2 : ℝ) ^ k ≠ 0 := by positivity
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- `N! * (N+1)^i ≤ (N+i)!`: each of the `i` extra factors of `(N+i)!/N!` is `≥ N+1`. -/
lemma nat_factorial_mul_pow_le (N : ℕ) :
    ∀ i, N.factorial * (N + 1) ^ i ≤ (N + i).factorial := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    calc N.factorial * (N + 1) ^ (i + 1)
        = N.factorial * (N + 1) ^ i * (N + 1) := by ring
      _ ≤ (N + i).factorial * (N + 1) := mul_le_mul_right' ih _
      _ ≤ (N + i).factorial * (N + i + 1) := mul_le_mul_left' (by omega) _
      _ = (N + (i + 1)).factorial := by
          rw [show N + (i + 1) = (N + i) + 1 from rfl, Nat.factorial_succ]; ring

/-- Sharp upper bound: `exp Y` is at most the truncated Taylor sum plus a geometric tail
`(Y^N / N!) · (N+1)/((N+1) - Y)`, valid for `0 ≤ Y < 1`. This is the key estimate matching
the tail term used by `expTaylorUpper`. -/
lemma exp_le_sum_range_add_geom_tail {Y : ℝ} (hY0 : 0 ≤ Y) (hY1 : Y < 1) (N : ℕ) :
    Real.exp Y ≤ (∑ j ∈ Finset.range N, Y ^ j / j.factorial)
      + (Y ^ N / N.factorial) * (((N : ℝ) + 1) / (((N : ℝ) + 1) - Y)) := by
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set K : ℝ := (N : ℝ) + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hYK1 : Y / K < 1 := by rw [div_lt_one hKpos, hKdef]; linarith
  have hYK0 : 0 ≤ Y / K := div_nonneg hY0 hKpos.le
  have hKY : (0 : ℝ) < K - Y := by rw [hKdef]; linarith
  -- `Y^j/j!` sums to `exp Y`.
  have hExp : HasSum (fun j : ℕ => Y ^ j / j.factorial) (Real.exp Y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp Y
  -- The tail from index `N` sums to `exp Y - (partial sum)`.
  have hTail : HasSum (fun i : ℕ => Y ^ (i + N) / (i + N).factorial)
      (Real.exp Y - ∑ j ∈ Finset.range N, Y ^ j / j.factorial) :=
    (hasSum_nat_add_iff' N).mpr hExp
  -- The dominating geometric series.
  have hGeom : HasSum (fun i : ℕ => (Y ^ N / N.factorial) * (Y / K) ^ i)
      ((Y ^ N / N.factorial) * (1 - Y / K)⁻¹) :=
    (hasSum_geometric_of_lt_one hYK0 hYK1).mul_left _
  -- Termwise domination of the tail by the geometric series.
  have hterm : ∀ i, Y ^ (i + N) / (i + N).factorial ≤ (Y ^ N / N.factorial) * (Y / K) ^ i := by
    intro i
    have hfact : (N.factorial : ℝ) * K ^ i ≤ ((N + i).factorial : ℝ) := by
      calc (N.factorial : ℝ) * K ^ i = ((N.factorial * (N + 1) ^ i : ℕ) : ℝ) := by
            rw [hKdef]; push_cast; ring
        _ ≤ ((N + i).factorial : ℝ) := by exact_mod_cast nat_factorial_mul_pow_le N i
    have hYpow : (0 : ℝ) ≤ Y ^ (N + i) := by positivity
    have hd1 : (0 : ℝ) < ((N + i).factorial : ℝ) := by exact_mod_cast (N + i).factorial_pos
    have hd2 : (0 : ℝ) < (N.factorial : ℝ) * K ^ i :=
      mul_pos (by exact_mod_cast N.factorial_pos) (pow_pos hKpos i)
    have hcancel : (Y ^ N / N.factorial) * (Y / K) ^ i
        = Y ^ (N + i) / ((N.factorial : ℝ) * K ^ i) := by rw [div_pow, pow_add]; ring
    rw [add_comm i N, hcancel, div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hYpow
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hd2 hfact
  have hle := hasSum_le hterm hTail hGeom
  have hId : (1 - Y / K)⁻¹ = K / (K - Y) := by
    have h1 : (K - Y) / K = 1 - Y / K := by rw [sub_div, div_self hKpos.ne']
    rw [← h1, inv_div]
  rw [hId] at hle
  linarith

/-- Positivity of `↑(k+1)` as a dyadic. -/
lemma dyadic_natCast_add_one_pos (k : ℕ) : (0 : Dyadic) < ((k + 1 : ℕ) : Dyadic) := by
  rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, dyadic_to_real_natCast]
  positivity

/-- Rewriting the successor Taylor term: `Y^(k+1)/(k+1)! · (k+1) = Y^k/k! · Y`. -/
lemma next_term_eq (Y : ℝ) (k : ℕ) :
    Y ^ (k + 1) / (k + 1).factorial * ((k + 1 : ℕ) : ℝ) = Y ^ k / k.factorial * Y := by
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- Invariant for the lower Taylor accumulator: the result is between the running `sum`
(which never decreases) and `exp y`, given the running `term`/`sum` bracket the true series. -/
lemma expTaylorLowerAux_bounds (p : ℕ) (y : Dyadic) (hy : 0 ≤ dyadic_to_real y) :
    ∀ (n k : ℕ) (term sum : Dyadic),
      0 ≤ dyadic_to_real term →
      dyadic_to_real term ≤ (dyadic_to_real y) ^ k / k.factorial →
      dyadic_to_real sum ≤ ∑ j ∈ Finset.range (k + 1), (dyadic_to_real y) ^ j / j.factorial →
      dyadic_to_real sum ≤ dyadic_to_real (expTaylorLowerAux p y n k term sum) ∧
      dyadic_to_real (expTaylorLowerAux p y n k term sum) ≤ Real.exp (dyadic_to_real y) := by
  intro n
  induction n with
  | zero =>
    intro k term sum _ _ hsum
    exact ⟨le_refl _, le_trans hsum (Real.sum_le_exp_of_nonneg hy (k + 1))⟩
  | succ n ih =>
    intro k term sum hterm0 htermle hsumle
    have hkpos' := dyadic_natCast_add_one_pos k
    have hkposR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hnext0 : 0 ≤ dyadic_to_real (Dyadic.divDown p (term * y) ((k + 1 : ℕ) : Dyadic)) :=
      divDown_nonneg p (by rw [dyadic_to_real_mul]; exact mul_nonneg hterm0 hy)
        (by rw [dyadic_to_real_natCast]; exact hkposR)
    have hnextle : dyadic_to_real (Dyadic.divDown p (term * y) ((k + 1 : ℕ) : Dyadic))
        ≤ (dyadic_to_real y) ^ (k + 1) / (k + 1).factorial := by
      have hd := divDown_le p (a := term * y) hkpos'
      rw [dyadic_to_real_mul, dyadic_to_real_natCast] at hd
      refine le_trans hd ?_
      rw [div_le_iff₀ hkposR, next_term_eq]
      exact mul_le_mul_of_nonneg_right htermle hy
    simp only [expTaylorLowerAux]
    split_ifs with hz
    · exact ⟨le_refl _, le_trans hsumle (Real.sum_le_exp_of_nonneg hy (k + 1))⟩
    · have hsum' : dyadic_to_real (sum + Dyadic.divDown p (term * y) ((k + 1 : ℕ) : Dyadic))
          ≤ ∑ j ∈ Finset.range (k + 1 + 1), (dyadic_to_real y) ^ j / j.factorial := by
        rw [dyadic_to_real_add, Finset.sum_range_succ]
        linarith [hsumle, hnextle]
      obtain ⟨h1, h2⟩ := ih (k + 1) _ _ hnext0 hnextle hsum'
      refine ⟨?_, h2⟩
      have hmono : dyadic_to_real sum
          ≤ dyadic_to_real (sum + Dyadic.divDown p (term * y) ((k + 1 : ℕ) : Dyadic)) := by
        rw [dyadic_to_real_add]; linarith [hnext0]
      linarith [hmono, h1]

/-- Top-level lower Taylor bound: `1 ≤ expTaylorLower ≤ exp y` for `0 ≤ y`. -/
lemma expTaylorLower_bounds (p t : ℕ) {y : Dyadic} (hy : 0 ≤ dyadic_to_real y) :
    1 ≤ dyadic_to_real (expTaylorLower p t y) ∧
    dyadic_to_real (expTaylorLower p t y) ≤ Real.exp (dyadic_to_real y) := by
  have h1 : (0 : ℝ) ≤ dyadic_to_real (1 : Dyadic) := by rw [dyadic_to_real_one]; norm_num
  have h2 : dyadic_to_real (1 : Dyadic) ≤ (dyadic_to_real y) ^ 0 / (0 : ℕ).factorial := by
    rw [dyadic_to_real_one]; simp
  have h3 : dyadic_to_real (1 : Dyadic)
      ≤ ∑ j ∈ Finset.range 1, (dyadic_to_real y) ^ j / j.factorial := by
    rw [dyadic_to_real_one]; simp
  obtain ⟨hle1, hle2⟩ := expTaylorLowerAux_bounds p y hy t 0 1 1 h1 h2 h3
  rw [expTaylorLower]
  rw [dyadic_to_real_one] at hle1
  exact ⟨hle1, hle2⟩

/-- Invariant for the upper Taylor accumulator: `sum` dominates the true partial sum, the
carried `next` dominates the next true term, and the index counter equals `k + n + 1`. -/
lemma expTaylorUpperAux_bounds (p : ℕ) (y : Dyadic) (hy : 0 ≤ dyadic_to_real y) :
    ∀ (n k : ℕ) (term sum : Dyadic),
      (dyadic_to_real y) ^ k / k.factorial ≤ dyadic_to_real term →
      (∑ j ∈ Finset.range (k + 1), (dyadic_to_real y) ^ j / j.factorial) ≤ dyadic_to_real sum →
      (∑ j ∈ Finset.range (k + n + 1), (dyadic_to_real y) ^ j / j.factorial)
          ≤ dyadic_to_real (expTaylorUpperAux p y n k term sum).1 ∧
      (dyadic_to_real y) ^ (k + n + 1) / (k + n + 1).factorial
          ≤ dyadic_to_real (expTaylorUpperAux p y n k term sum).2.1 ∧
      (expTaylorUpperAux p y n k term sum).2.2 = k + n + 1 := by
  intro n
  induction n with
  | zero =>
    intro k term sum htermge hsumge
    have hkpos' := dyadic_natCast_add_one_pos k
    have hkposR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    refine ⟨?_, ?_, rfl⟩
    · show (∑ j ∈ Finset.range (k + 1), (dyadic_to_real y) ^ j / j.factorial) ≤ dyadic_to_real sum
      exact hsumge
    · show (dyadic_to_real y) ^ (k + 1) / (k + 1).factorial
          ≤ dyadic_to_real (Dyadic.divUp p (term * y) ((k + 1 : ℕ) : Dyadic))
      have hd := le_divUp p (a := term * y) hkpos'
      rw [dyadic_to_real_mul, dyadic_to_real_natCast] at hd
      refine le_trans ?_ hd
      rw [le_div_iff₀ hkposR, next_term_eq]
      exact mul_le_mul_of_nonneg_right htermge hy
  | succ n ih =>
    intro k term sum htermge hsumge
    have hkpos' := dyadic_natCast_add_one_pos k
    have hkposR : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hnextge : (dyadic_to_real y) ^ (k + 1) / (k + 1).factorial
        ≤ dyadic_to_real (Dyadic.divUp p (term * y) ((k + 1 : ℕ) : Dyadic)) := by
      have hd := le_divUp p (a := term * y) hkpos'
      rw [dyadic_to_real_mul, dyadic_to_real_natCast] at hd
      refine le_trans ?_ hd
      rw [le_div_iff₀ hkposR, next_term_eq]
      exact mul_le_mul_of_nonneg_right htermge hy
    have hsumge' : (∑ j ∈ Finset.range (k + 1 + 1), (dyadic_to_real y) ^ j / j.factorial)
        ≤ dyadic_to_real (sum + Dyadic.divUp p (term * y) ((k + 1 : ℕ) : Dyadic)) := by
      rw [dyadic_to_real_add, Finset.sum_range_succ]
      linarith [hsumge, hnextge]
    simp only [expTaylorUpperAux]
    obtain ⟨hA, hB, hC⟩ := ih (k + 1) _ _ hnextge hsumge'
    refine ⟨?_, ?_, ?_⟩
    · rw [show k + (n + 1) + 1 = k + 1 + n + 1 from by omega]; exact hA
    · rw [show k + (n + 1) + 1 = k + 1 + n + 1 from by omega]; exact hB
    · rw [hC]; omega

/-- Top-level upper Taylor bound: `exp y ≤ expTaylorUpper` for `0 ≤ y < 1`. -/
lemma le_expTaylorUpper (p t : ℕ) {y : Dyadic}
    (hy0 : 0 ≤ dyadic_to_real y) (hy1 : dyadic_to_real y < 1) :
    Real.exp (dyadic_to_real y) ≤ dyadic_to_real (expTaylorUpper p t y) := by
  have hterm0 : (dyadic_to_real y) ^ 0 / (0 : ℕ).factorial ≤ dyadic_to_real (1 : Dyadic) := by
    rw [dyadic_to_real_one]; simp
  have hsum0 : (∑ j ∈ Finset.range (0 + 1), (dyadic_to_real y) ^ j / j.factorial)
      ≤ dyadic_to_real (1 : Dyadic) := by rw [dyadic_to_real_one]; simp
  obtain ⟨hA, hB, hC⟩ := expTaylorUpperAux_bounds p y hy0 t 0 1 1 hterm0 hsum0
  simp only [Nat.zero_add] at hA hB hC
  have habs := exp_le_sum_range_add_geom_tail hy0 hy1 (t + 1)
  rw [show (((t + 1 : ℕ) : ℝ) + 1) = (t : ℝ) + 2 from by push_cast; ring] at habs
  simp only [expTaylorUpper]
  set st := expTaylorUpperAux p y t 0 1 1 with hstdef
  set Y := dyadic_to_real y with hYdef
  have hKR : dyadic_to_real ((st.2.2 + 1 : ℕ) : Dyadic) = ((t : ℝ) + 2) := by
    rw [dyadic_to_real_natCast, hC]; push_cast; ring
  have hKYpos : (0 : ℝ) < ((t : ℝ) + 2) - Y := by
    have h := Nat.cast_nonneg (α := ℝ) t; linarith
  have hKYdyadic : (0 : Dyadic) < ((st.2.2 + 1 : ℕ) : Dyadic) - y := by
    rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, dyadic_to_real_sub, hKR]
    exact hKYpos
  have hdiv := le_divUp p (a := st.2.1 * ((st.2.2 + 1 : ℕ) : Dyadic)) hKYdyadic
  rw [dyadic_to_real_mul, dyadic_to_real_sub, hKR] at hdiv
  have hfac : (0 : ℝ) ≤ ((t : ℝ) + 2) / (((t : ℝ) + 2) - Y) := by positivity
  have hBscaled := mul_le_mul_of_nonneg_right hB hfac
  have hmuleq : dyadic_to_real st.2.1 * (((t : ℝ) + 2) / (((t : ℝ) + 2) - Y))
      = (dyadic_to_real st.2.1 * ((t : ℝ) + 2)) / (((t : ℝ) + 2) - Y) := by ring
  rw [dyadic_to_real_add]
  linarith [habs, hA, hBscaled, hmuleq, hdiv]

/-- Lower enclosure for `exp` on nonnegative arguments. -/
lemma expNonnegDown_le (p t : ℕ) {x : Dyadic} (hx : 0 ≤ x) :
    dyadic_to_real (expNonnegDown p t x) ≤ Real.exp (dyadic_to_real x) := by
  simp only [expNonnegDown]
  rw [dyadic_to_real_squareIter]
  have hx'0 : 0 ≤ dyadic_to_real (x.divPowTwo (expReductionSteps x)) := expReduction_nonneg hx
  obtain ⟨hL1, hL2⟩ := expTaylorLower_bounds p t hx'0
  have hxeq : dyadic_to_real (x.divPowTwo (expReductionSteps x))
      = dyadic_to_real x / 2 ^ (expReductionSteps x) :=
    dyadic_to_real_divPowTwo x (expReductionSteps x)
  rw [exp_range_reduction (dyadic_to_real x) (expReductionSteps x), ← hxeq]
  exact pow_le_pow_left₀ (by linarith [hL1]) hL2 _

/-- The lower enclosure on nonnegative arguments is at least `1` (hence positive). -/
lemma one_le_expNonnegDown (p t : ℕ) {x : Dyadic} (hx : 0 ≤ x) :
    1 ≤ dyadic_to_real (expNonnegDown p t x) := by
  simp only [expNonnegDown]
  rw [dyadic_to_real_squareIter]
  have hx'0 : 0 ≤ dyadic_to_real (x.divPowTwo (expReductionSteps x)) := expReduction_nonneg hx
  obtain ⟨hL1, _⟩ := expTaylorLower_bounds p t hx'0
  calc (1 : ℝ) = 1 ^ (2 ^ (expReductionSteps x)) := (one_pow _).symm
    _ ≤ (dyadic_to_real (expTaylorLower p t (x.divPowTwo (expReductionSteps x))))
          ^ (2 ^ (expReductionSteps x)) := pow_le_pow_left₀ zero_le_one hL1 _

/-- Upper enclosure for `exp` on nonnegative arguments. -/
lemma le_expNonnegUp (p t : ℕ) {x : Dyadic} (hx : 0 ≤ x) :
    Real.exp (dyadic_to_real x) ≤ dyadic_to_real (expNonnegUp p t x) := by
  simp only [expNonnegUp]
  rw [dyadic_to_real_squareIter]
  have hx'0 : 0 ≤ dyadic_to_real (x.divPowTwo (expReductionSteps x)) := expReduction_nonneg hx
  have hx'1 : dyadic_to_real (x.divPowTwo (expReductionSteps x)) < 1 := expReduction_lt_one hx
  have hU := le_expTaylorUpper p t hx'0 hx'1
  have hxeq : dyadic_to_real (x.divPowTwo (expReductionSteps x))
      = dyadic_to_real x / 2 ^ (expReductionSteps x) :=
    dyadic_to_real_divPowTwo x (expReductionSteps x)
  rw [exp_range_reduction (dyadic_to_real x) (expReductionSteps x), ← hxeq]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) hU _

/-- `exp` lower endpoint bound: `expDown a ≤ exp a` for all dyadic `a`. -/
lemma expDown_le (p t : ℕ) (a : Dyadic) :
    dyadic_to_real (expDown p t a) ≤ Real.exp (dyadic_to_real a) := by
  rw [expDown]
  split_ifs with ha
  · have hda : dyadic_to_real a < 0 := by
      have := strictMono_dyadic_to_real ha; rwa [dyadic_to_real_zero] at this
    have hnega : (0 : Dyadic) ≤ -a := by
      rw [← strictMono_dyadic_to_real.le_iff_le, dyadic_to_real_zero, dyadic_to_real_neg]; linarith
    have hUP := le_expNonnegUp p t hnega
    rw [dyadic_to_real_neg] at hUP
    have hEpos : (0 : ℝ) < dyadic_to_real (expNonnegUp p t (-a)) :=
      lt_of_lt_of_le (Real.exp_pos _) hUP
    have hEdyadic : (0 : Dyadic) < expNonnegUp p t (-a) := by
      rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero]; exact hEpos
    have hd := divDown_le p (a := 1) hEdyadic
    rw [dyadic_to_real_one] at hd
    have hexp : Real.exp (dyadic_to_real a) = 1 / Real.exp (-dyadic_to_real a) := by
      rw [Real.exp_neg, one_div, inv_inv]
    rw [hexp]
    have h1 : 1 / dyadic_to_real (expNonnegUp p t (-a)) ≤ 1 / Real.exp (-dyadic_to_real a) :=
      one_div_le_one_div_of_le (Real.exp_pos _) hUP
    linarith [hd, h1]
  · exact expNonnegDown_le p t (not_lt.mp ha)

/-- `exp` upper endpoint bound: `exp a ≤ expUp a` for all dyadic `a`. -/
lemma le_expUp (p t : ℕ) (a : Dyadic) :
    Real.exp (dyadic_to_real a) ≤ dyadic_to_real (expUp p t a) := by
  rw [expUp]
  split_ifs with ha
  · have hda : dyadic_to_real a < 0 := by
      have := strictMono_dyadic_to_real ha; rwa [dyadic_to_real_zero] at this
    have hnega : (0 : Dyadic) ≤ -a := by
      rw [← strictMono_dyadic_to_real.le_iff_le, dyadic_to_real_zero, dyadic_to_real_neg]; linarith
    have hD1 := one_le_expNonnegDown p t hnega
    have hDpos : (0 : ℝ) < dyadic_to_real (expNonnegDown p t (-a)) := by linarith
    have hDdyadic : (0 : Dyadic) < expNonnegDown p t (-a) := by
      rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero]; exact hDpos
    have hDN := expNonnegDown_le p t hnega
    rw [dyadic_to_real_neg] at hDN
    have hd := le_divUp p (a := 1) hDdyadic
    rw [dyadic_to_real_one] at hd
    have hexp : Real.exp (dyadic_to_real a) = 1 / Real.exp (-dyadic_to_real a) := by
      rw [Real.exp_neg, one_div, inv_inv]
    rw [hexp]
    have h1 : 1 / Real.exp (-dyadic_to_real a) ≤ 1 / dyadic_to_real (expNonnegDown p t (-a)) :=
      one_div_le_one_div_of_le hDpos hDN
    linarith [hd, h1]
  · exact le_expNonnegUp p t (not_lt.mp ha)

@[interval_op DyadicReal Exp]
theorem Interval.dyadic_exp_inclusion {r : ℝ} {x : Interval Dyadic} (approxParam : ℕ)
    (hrx : r ∈ x.toSet dyadic_to_real) :
    Real.exp r ∈ (x.dyadic_exp approxParam).toSet dyadic_to_real := by
  rw [Interval.mem_toSet] at hrx ⊢
  obtain ⟨hlb, hub⟩ := hrx
  constructor
  · cases hx : x.lb with
    | none =>
        simp only [Interval.dyadic_exp, hx, LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte,
          dyadic_to_real_zero]
        exact Real.exp_pos r
    | some fb =>
        obtain ⟨c, a⟩ := fb
        rw [hx] at hlb
        have hkey := expDown_le approxParam (expTaylorTerms approxParam) a
        simp only [Interval.dyadic_exp, hx, LowerBound.Bounds] at hlb ⊢
        cases c
        · simp only [Bool.false_eq_true, ↓reduceIte] at hlb ⊢
          linarith [Real.exp_lt_exp.mpr hlb, hkey]
        · simp only [↓reduceIte] at hlb ⊢
          linarith [Real.exp_le_exp.mpr hlb, hkey]
  · cases hx : x.ub with
    | none => simp only [Interval.dyadic_exp, hx]; exact UpperBound.top_Bounds _ _
    | some fb =>
        obtain ⟨c, a⟩ := fb
        rw [hx] at hub
        have hkey := le_expUp approxParam (expTaylorTerms approxParam) a
        simp only [Interval.dyadic_exp, hx, UpperBound.Bounds] at hub ⊢
        cases c
        · simp only [Bool.false_eq_true, ↓reduceIte] at hub ⊢
          linarith [Real.exp_lt_exp.mpr hub, hkey]
        · simp only [↓reduceIte] at hub ⊢
          linarith [Real.exp_le_exp.mpr hub, hkey]

end Exp

section Pi

namespace Dyadic

/--
Number of arctan terms to use for a given dyadic precision.

For `atan (1 / 5)`, each two-step reduction gains roughly `log₂ 25 ≈ 4.64` bits,
so `prec / 4 + 4` is conservative. This is just for sharpness, not soundness:
any number of terms gives valid alternating-series bounds.
-/
def atanTerms (prec : ℕ) : ℕ :=
  prec / 4 + 4

/--
Computes lower and upper approximations to the alternating arctangent partial sum.

If `q ≥ 0`, this processes terms

`q - q^3 / 3 + q^5 / 5 - ...`

The pair `(lo, hi)` satisfies:
* `lo ≤` the exact partial sum,
* the exact partial sum `≤ hi`.

Positive terms are rounded outward as:
* lower sum adds lower term bound,
* upper sum adds upper term bound.

Negative terms are rounded outward as:
* lower sum subtracts upper term bound,
* upper sum subtracts lower term bound.
-/
def atanBoundsAux (prec : ℕ) (qSq : Dyadic) :
    ℕ → ℕ → Bool → Dyadic → Dyadic → Dyadic → Dyadic → Dyadic × Dyadic
  | 0, _d, _pos, _termLo, _termHi, lo, hi => (lo, hi)
  | n + 1, d, pos, termLo, termHi, lo, hi =>
      let lo' := if pos then lo + termLo else lo - termHi
      let hi' := if pos then hi + termHi else hi - termLo
      let d' := d + 2
      let termLo' := Dyadic.divDown prec (termLo * qSq * (d : Dyadic)) (d' : Dyadic)
      let termHi' := Dyadic.divUp prec (termHi * qSq * (d : Dyadic)) (d' : Dyadic)
      atanBoundsAux prec qSq n d' (!pos) termLo' termHi' lo' hi'

/--
Bounds for the partial arctangent sum through term `n`.

The term index convention matches:

* `n = 0`: `q`
* `n = 1`: `q - q^3 / 3`
* `n = 2`: `q - q^3 / 3 + q^5 / 5`
-/
def atanBounds (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic × Dyadic :=
  atanBoundsAux prec (q * q) (n + 1) 1 true q q 0 0

/-- Lower bound for `atan q`, using an odd partial sum. -/
def atanLower (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic :=
  (atanBounds prec q (2 * n + 1)).1

/-- Upper bound for `atan q`, using an even partial sum. -/
def atanUpper (prec : ℕ) (q : Dyadic) (n : ℕ) : Dyadic :=
  (atanBounds prec q (2 * n)).2

end Dyadic

def Interval.dyadicPi (approxParam : ℕ) : Interval Dyadic :=
  let terms := Dyadic.atanTerms approxParam
  -- Lower/upper dyadic enclosures of the rational constants.
  let q₁Lo := Dyadic.divDown approxParam 1 (5 : Dyadic)
  let q₁Hi := Dyadic.divUp approxParam 1 (5 : Dyadic)
  let q₂Lo := Dyadic.divDown approxParam 1 (239 : Dyadic)
  let q₂Hi := Dyadic.divUp approxParam 1 (239 : Dyadic)
  -- π = 16 atan(1/5) - 4 atan(1/239)
  let lb := 16 * Dyadic.atanLower approxParam q₁Lo terms
      - 4 * Dyadic.atanUpper approxParam q₂Hi terms
  let ub := 16 * Dyadic.atanUpper approxParam q₁Hi terms
      - 4 * Dyadic.atanLower approxParam q₂Lo terms
  { lb := some ⟨false, lb⟩
    ub := some ⟨false, ub⟩ }

/-! ### Helper lemmas for `π` soundness

Strategy: Machin's formula `π = 16 arctan(1/5) - 4 arctan(1/239)`, the alternating arctan
series (`Real.hasSum_arctan`, with the boundary `x = 1` handled by Leibniz's
`tendsto_sum_pi_div_four`), and a recursion invariant for `atanBoundsAux` mirroring
`expTaylorUpperAux_bounds`. -/

/-- The (unsigned) `n`-th term of the arctan Maclaurin series. -/
noncomputable def atanSeriesTerm (x : ℝ) (i : ℕ) : ℝ := x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)

/-- The `m`-th partial sum of the alternating arctan series. -/
noncomputable def atanPartialSum (x : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, (-1) ^ i * atanSeriesTerm x i

lemma atanSeriesTerm_succ_eq (x : ℝ) (i : ℕ) :
    atanSeriesTerm x i * (x * x) * ((2 * i + 1 : ℕ) : ℝ) / ((2 * i + 1 + 2 : ℕ) : ℝ)
      = atanSeriesTerm x (i + 1) := by
  unfold atanSeriesTerm
  have hx2 : x * x = x ^ 2 := (sq x).symm
  rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 from by ring, pow_add, hx2]
  have hne1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * i + 1 ≠ 0)
  have hne2 : ((2 * i + 1 + 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : 2 * i + 1 + 2 ≠ 0)
  field_simp
  ring

lemma atanSeriesTerm_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (atanSeriesTerm x) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold atanSeriesTerm
  have hnum : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden : ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * (n + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  have hnn : (0 : ℝ) ≤ x ^ (2 * n + 1) := by positivity
  have hdpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n + 1)
  calc x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ)
      ≤ x ^ (2 * n + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ) := by gcongr
    _ ≤ x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_left hnn hdpos hden

lemma atanSeriesTerm_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (n : ℕ) :
    atanSeriesTerm x (n + 1) < atanSeriesTerm x n := by
  unfold atanSeriesTerm
  have hnum : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one hx0.le hx1 (by omega)
  calc x ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ)
      ≤ x ^ (2 * n + 1) / ((2 * (n + 1) + 1 : ℕ) : ℝ) := by gcongr
    _ < x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
        apply div_lt_div_of_pos_left (pow_pos hx0 _)
        · exact_mod_cast (by omega : 0 < 2 * n + 1)
        · exact_mod_cast (by omega : 2 * n + 1 < 2 * (n + 1) + 1)

open Filter Topology in
lemma tendsto_atanPartialSum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Tendsto (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * atanSeriesTerm x i) atTop
      (𝓝 (Real.arctan x)) := by
  rcases eq_or_lt_of_le hx1 with heq | hlt
  · subst heq
    rw [Real.arctan_one]
    have hfun : (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * atanSeriesTerm 1 i)
        = (fun k => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i / (2 * i + 1)) := by
      funext k
      apply Finset.sum_congr rfl
      intro i _
      unfold atanSeriesTerm
      simp only [one_pow]
      push_cast
      ring
    rw [hfun]
    exact Real.tendsto_sum_pi_div_four
  · have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hlt
    have hbase := (Real.hasSum_arctan hnorm).tendsto_sum_nat
    have hfun : (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * atanSeriesTerm x i)
        = (fun m => ∑ i ∈ Finset.range m, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) := by
      funext m
      apply Finset.sum_congr rfl
      intro i _
      unfold atanSeriesTerm
      rw [mul_div_assoc]
    rw [hfun]
    exact hbase

lemma atanPartialSum_even_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    atanPartialSum x (2 * k) ≤ Real.arctan x :=
  Antitone.alternating_series_le_tendsto (tendsto_atanPartialSum hx0 hx1)
    (atanSeriesTerm_antitone hx0 hx1) k

lemma le_atanPartialSum_odd {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    Real.arctan x ≤ atanPartialSum x (2 * k + 1) :=
  Antitone.tendsto_le_alternating_series (tendsto_atanPartialSum hx0 hx1)
    (atanSeriesTerm_antitone hx0 hx1) k

lemma atanPartialSum_step (x : ℝ) (m : ℕ) :
    atanPartialSum x (m + 2)
      = atanPartialSum x m + (-1) ^ m * (atanSeriesTerm x m - atanSeriesTerm x (m + 1)) := by
  unfold atanPartialSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring

lemma atanPartialSum_even_lt {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    atanPartialSum x (2 * k) < Real.arctan x := by
  have hstep : atanPartialSum x (2 * k) < atanPartialSum x (2 * k + 2) := by
    rw [atanPartialSum_step]
    have hlt : atanSeriesTerm x (2 * k + 1) < atanSeriesTerm x (2 * k) :=
      atanSeriesTerm_lt hx0 hx1 (2 * k)
    have hsign : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
    rw [hsign]; linarith
  have hle : atanPartialSum x (2 * k + 2) ≤ Real.arctan x := by
    have := atanPartialSum_even_le hx0.le hx1 (k + 1)
    rwa [show 2 * (k + 1) = 2 * k + 2 from by ring] at this
  linarith

lemma lt_atanPartialSum_odd {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    Real.arctan x < atanPartialSum x (2 * k + 1) := by
  have hstep : atanPartialSum x (2 * k + 1 + 2) < atanPartialSum x (2 * k + 1) := by
    rw [atanPartialSum_step]
    have hlt : atanSeriesTerm x (2 * k + 1 + 1) < atanSeriesTerm x (2 * k + 1) :=
      atanSeriesTerm_lt hx0 hx1 (2 * k + 1)
    have hsign : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hsign]; linarith
  have hle : Real.arctan x ≤ atanPartialSum x (2 * k + 1 + 2) := by
    have := le_atanPartialSum_odd hx0.le hx1 (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 from by ring] at this
  linarith

/-- Recursion invariant for `atanBoundsAux`: outward-rounded terms keep `lo`/`hi` bracketing
the exact partial sum. Mirrors `expTaylorUpperAux_bounds`. -/
lemma atanBoundsAux_bracket (prec : ℕ) (q : Dyadic) (hq0 : 0 ≤ dyadic_to_real q) :
    ∀ (n i d : ℕ) (pos : Bool) (termLo termHi lo hi : Dyadic),
      d = 2 * i + 1 →
      ((-1 : ℝ)) ^ i = (if pos then 1 else -1) →
      0 ≤ dyadic_to_real termLo →
      dyadic_to_real termLo ≤ atanSeriesTerm (dyadic_to_real q) i →
      atanSeriesTerm (dyadic_to_real q) i ≤ dyadic_to_real termHi →
      dyadic_to_real lo ≤ atanPartialSum (dyadic_to_real q) i →
      atanPartialSum (dyadic_to_real q) i ≤ dyadic_to_real hi →
      dyadic_to_real (Dyadic.atanBoundsAux prec (q * q) n d pos termLo termHi lo hi).1
          ≤ atanPartialSum (dyadic_to_real q) (i + n) ∧
      atanPartialSum (dyadic_to_real q) (i + n)
          ≤ dyadic_to_real (Dyadic.atanBoundsAux prec (q * q) n d pos termLo termHi lo hi).2 := by
  intro n
  induction n with
  | zero =>
      intro i d pos termLo termHi lo hi _ _ _ _ _ hlo hhi
      simp only [Dyadic.atanBoundsAux, Nat.add_zero]
      exact ⟨hlo, hhi⟩
  | succ n ih =>
      intro i d pos termLo termHi lo hi hd hsign ht0 htlo hthi hlo hhi
      have hqq0 : (0 : ℝ) ≤ dyadic_to_real (q * q) := by rw [dyadic_to_real_mul]; positivity
      have hdpos : (0 : Dyadic) < ((d + 2 : ℕ) : Dyadic) := by
        rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, dyadic_to_real_natCast]
        exact_mod_cast (by omega : 0 < d + 2)
      have hthi0 : (0 : ℝ) ≤ dyadic_to_real termHi := le_trans ht0 (le_trans htlo hthi)
      have hnumLo : (0 : ℝ) ≤ dyadic_to_real (termLo * (q * q) * ((d : ℕ) : Dyadic)) := by
        rw [dyadic_to_real_mul, dyadic_to_real_mul, dyadic_to_real_natCast]
        exact mul_nonneg (mul_nonneg ht0 hqq0) (Nat.cast_nonneg d)
      have htlo' : dyadic_to_real (Dyadic.divDown prec (termLo * (q * q) * ((d : ℕ) : Dyadic))
            ((d + 2 : ℕ) : Dyadic)) ≤ atanSeriesTerm (dyadic_to_real q) (i + 1) := by
        have hdd := divDown_le prec (a := termLo * (q * q) * ((d : ℕ) : Dyadic)) hdpos
        simp only [dyadic_to_real_mul, dyadic_to_real_natCast] at hdd
        refine le_trans hdd ?_
        rw [hd, ← atanSeriesTerm_succ_eq (dyadic_to_real q) i]
        gcongr
      have hthi' : atanSeriesTerm (dyadic_to_real q) (i + 1)
            ≤ dyadic_to_real (Dyadic.divUp prec (termHi * (q * q) * ((d : ℕ) : Dyadic))
              ((d + 2 : ℕ) : Dyadic)) := by
        have hdd := le_divUp prec (a := termHi * (q * q) * ((d : ℕ) : Dyadic)) hdpos
        simp only [dyadic_to_real_mul, dyadic_to_real_natCast] at hdd
        refine le_trans ?_ hdd
        rw [hd, ← atanSeriesTerm_succ_eq (dyadic_to_real q) i]
        gcongr
      have ht0' : (0 : ℝ) ≤ dyadic_to_real (Dyadic.divDown prec
            (termLo * (q * q) * ((d : ℕ) : Dyadic)) ((d + 2 : ℕ) : Dyadic)) := by
        apply divDown_nonneg
        · exact hnumLo
        · rw [dyadic_to_real_natCast]; exact_mod_cast (by omega : 0 < d + 2)
      have hPS1 : atanPartialSum (dyadic_to_real q) (i + 1)
          = atanPartialSum (dyadic_to_real q) i
            + (-1) ^ i * atanSeriesTerm (dyadic_to_real q) i := by
        unfold atanPartialSum; rw [Finset.sum_range_succ]
      have hlo' : dyadic_to_real (if pos then lo + termLo else lo - termHi)
          ≤ atanPartialSum (dyadic_to_real q) (i + 1) := by
        rw [hPS1]
        cases pos with
        | true =>
            have hs : (-1 : ℝ) ^ i = 1 := by simpa using hsign
            simp only [if_true, hs, dyadic_to_real_add]; linarith
        | false =>
            have hs : (-1 : ℝ) ^ i = -1 := by simpa using hsign
            simp only [Bool.false_eq_true, if_false, hs, dyadic_to_real_sub]; linarith
      have hhi' : atanPartialSum (dyadic_to_real q) (i + 1)
          ≤ dyadic_to_real (if pos then hi + termHi else hi - termLo) := by
        rw [hPS1]
        cases pos with
        | true =>
            have hs : (-1 : ℝ) ^ i = 1 := by simpa using hsign
            simp only [if_true, hs, dyadic_to_real_add]; linarith
        | false =>
            have hs : (-1 : ℝ) ^ i = -1 := by simpa using hsign
            simp only [Bool.false_eq_true, if_false, hs, dyadic_to_real_sub]; linarith
      rw [show Dyadic.atanBoundsAux prec (q * q) (n + 1) d pos termLo termHi lo hi
          = Dyadic.atanBoundsAux prec (q * q) n (d + 2) (!pos)
              (Dyadic.divDown prec (termLo * (q * q) * ((d : ℕ) : Dyadic)) ((d + 2 : ℕ) : Dyadic))
              (Dyadic.divUp prec (termHi * (q * q) * ((d : ℕ) : Dyadic)) ((d + 2 : ℕ) : Dyadic))
              (if pos then lo + termLo else lo - termHi)
              (if pos then hi + termHi else hi - termLo) from rfl]
      rw [show i + (n + 1) = (i + 1) + n from by omega]
      refine ih (i + 1) (d + 2) (!pos) _ _ _ _ (by omega) ?_ ht0' htlo' hthi' hlo' hhi'
      rw [pow_succ, hsign]; cases pos <;> simp

private lemma atanSeriesTerm_zero (x : ℝ) : atanSeriesTerm x 0 = x := by
  unfold atanSeriesTerm; norm_num

private lemma atanPartialSum_zero (x : ℝ) : atanPartialSum x 0 = 0 := by
  unfold atanPartialSum; simp

/-- `atanLower prec q n` is the lower endpoint of `atanBounds prec q (2n+1)`. -/
private lemma atanLower_eq (prec n : ℕ) (q : Dyadic) :
    Dyadic.atanLower prec q n
      = (Dyadic.atanBoundsAux prec (q * q) (2 * n + 2) 1 true q q 0 0).1 := rfl

/-- `atanUpper prec q n` is the upper endpoint of `atanBounds prec q (2n)`. -/
private lemma atanUpper_eq (prec n : ℕ) (q : Dyadic) :
    Dyadic.atanUpper prec q n
      = (Dyadic.atanBoundsAux prec (q * q) (2 * n + 1) 1 true q q 0 0).2 := rfl

lemma atanLower_le_atanPartialSum (prec n : ℕ) {q : Dyadic} (hq0 : 0 ≤ dyadic_to_real q) :
    dyadic_to_real (Dyadic.atanLower prec q n) ≤ atanPartialSum (dyadic_to_real q) (2 * n + 2) := by
  obtain ⟨h1, _⟩ := atanBoundsAux_bracket prec q hq0 (2 * n + 2) 0 1 true q q 0 0
    (by norm_num) (by simp) hq0 (atanSeriesTerm_zero _).ge (atanSeriesTerm_zero _).le
    (by simp [dyadic_to_real_zero, atanPartialSum_zero]) (by simp [dyadic_to_real_zero, atanPartialSum_zero])
  rw [atanLower_eq]
  simpa using h1

lemma atanPartialSum_le_atanUpper (prec n : ℕ) {q : Dyadic} (hq0 : 0 ≤ dyadic_to_real q) :
    atanPartialSum (dyadic_to_real q) (2 * n + 1) ≤ dyadic_to_real (Dyadic.atanUpper prec q n) := by
  obtain ⟨_, h2⟩ := atanBoundsAux_bracket prec q hq0 (2 * n + 1) 0 1 true q q 0 0
    (by norm_num) (by simp) hq0 (atanSeriesTerm_zero _).ge (atanSeriesTerm_zero _).le
    (by simp [dyadic_to_real_zero, atanPartialSum_zero]) (by simp [dyadic_to_real_zero, atanPartialSum_zero])
  rw [atanUpper_eq]
  simpa using h2

lemma atanLower_le_arctan (prec n : ℕ) {q : Dyadic}
    (hq0 : 0 ≤ dyadic_to_real q) (hq1 : dyadic_to_real q ≤ 1) :
    dyadic_to_real (Dyadic.atanLower prec q n) ≤ Real.arctan (dyadic_to_real q) := by
  have h1 := atanLower_le_atanPartialSum prec n hq0
  have hle := atanPartialSum_even_le hq0 hq1 (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring] at hle
  linarith

lemma arctan_le_atanUpper (prec n : ℕ) {q : Dyadic}
    (hq0 : 0 ≤ dyadic_to_real q) (hq1 : dyadic_to_real q ≤ 1) :
    Real.arctan (dyadic_to_real q) ≤ dyadic_to_real (Dyadic.atanUpper prec q n) := by
  have h2 := atanPartialSum_le_atanUpper prec n hq0
  have hle := le_atanPartialSum_odd hq0 hq1 n
  linarith

lemma atanLower_lt_arctan (prec n : ℕ) {q : Dyadic}
    (hq0 : 0 < dyadic_to_real q) (hq1 : dyadic_to_real q ≤ 1) :
    dyadic_to_real (Dyadic.atanLower prec q n) < Real.arctan (dyadic_to_real q) := by
  have h1 := atanLower_le_atanPartialSum prec n hq0.le
  have hlt := atanPartialSum_even_lt hq0 hq1 (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring] at hlt
  linarith

lemma arctan_lt_atanUpper (prec n : ℕ) {q : Dyadic}
    (hq0 : 0 < dyadic_to_real q) (hq1 : dyadic_to_real q ≤ 1) :
    Real.arctan (dyadic_to_real q) < dyadic_to_real (Dyadic.atanUpper prec q n) := by
  have h2 := atanPartialSum_le_atanUpper prec n hq0.le
  have hlt := lt_atanPartialSum_odd hq0 hq1 n
  linarith

private lemma neg_one_le_divDown_neg_one (p : ℕ) {b : Dyadic} (hb : 1 ≤ dyadic_to_real b) :
    (-1 : ℝ) ≤ dyadic_to_real (Dyadic.divDown p (-1) b) := by
  have hbr : (1 : ℚ) ≤ b.toRat := by rw [dyadic_to_real] at hb; exact_mod_cast hb
  have hbr0 : (0 : ℚ) < b.toRat := by linarith
  rw [dyadic_to_real]
  have hnn : (-1 : ℚ) ≤ (Dyadic.divDown p (-1) b).toRat := by
    cases b with
    | zero =>
        rw [show (Dyadic.zero).toRat = (0 : ℚ) from rfl] at hbr0; exact absurd hbr0 (lt_irrefl 0)
    | ofOdd m e hm =>
        simp only [Dyadic.divDown, Dyadic.divAtPrec]
        rw [Rat.toRat_toDyadic, show ((-1 : Dyadic).toRat) = (-1 : ℚ) from by decide]
        set c : ℚ := (2 : ℚ) ^ (p : ℤ) with hc
        have hcpos : (0 : ℚ) < c := by rw [hc]; positivity
        rw [le_div_iff₀ hcpos]
        have hz : (-1 : ℚ) * c = ((-(2 ^ p) : ℤ) : ℚ) := by
          rw [hc]; push_cast [zpow_natCast]; ring
        rw [hz]
        have hfl : (-(2 ^ p) : ℤ) ≤ ⌊(-1 / (Dyadic.ofOdd m e hm).toRat) * c⌋ := by
          apply Int.le_floor.mpr
          rw [← hz]
          apply mul_le_mul_of_nonneg_right _ hcpos.le
          rw [neg_div, neg_le_neg_iff, div_le_one hbr0]
          exact hbr
        exact_mod_cast hfl
  exact_mod_cast hnn

lemma divUp_one_le_one (p : ℕ) {b : Dyadic} (hb : 1 ≤ dyadic_to_real b) :
    dyadic_to_real (Dyadic.divUp p 1 b) ≤ 1 := by
  rw [Dyadic.divUp, dyadic_to_real_neg]
  have := neg_one_le_divDown_neg_one p hb
  linarith

lemma pi_eq_machin : Real.pi = 16 * Real.arctan (5 : ℝ)⁻¹ - 4 * Real.arctan (239 : ℝ)⁻¹ := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  linarith

@[interval_op DyadicReal Pi]
theorem Interval.mem_dyadicPi (approxParam : ℕ) :
    Real.pi ∈ (Interval.dyadicPi approxParam).toSet dyadic_to_real := by
  -- Numeric constants.
  have h5 : dyadic_to_real (5 : Dyadic) = 5 := by
    rw [dyadic_to_real, show (5 : Dyadic).toRat = (5 : ℚ) from by decide]; norm_num
  have h239 : dyadic_to_real (239 : Dyadic) = 239 := by
    rw [dyadic_to_real, show (239 : Dyadic).toRat = (239 : ℚ) from by decide]; norm_num
  have h4 : dyadic_to_real (4 : Dyadic) = 4 := by
    rw [dyadic_to_real, show (4 : Dyadic).toRat = (4 : ℚ) from by decide]; norm_num
  have h16 : dyadic_to_real (16 : Dyadic) = 16 := by
    rw [dyadic_to_real, show (16 : Dyadic).toRat = (16 : ℚ) from by decide]; norm_num
  have h1d : dyadic_to_real (1 : Dyadic) = 1 := dyadic_to_real_one
  have h5pos : (0 : Dyadic) < 5 := by
    rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, h5]; norm_num
  have h239pos : (0 : Dyadic) < 239 := by
    rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, h239]; norm_num
  -- Bounds on the four rounded rational constants.
  have hq1Lo_le : dyadic_to_real (Dyadic.divDown approxParam 1 5) ≤ (5 : ℝ)⁻¹ := by
    have := divDown_le approxParam (a := 1) h5pos
    rw [h1d, h5, one_div] at this; exact this
  have hq1Lo_0 : 0 ≤ dyadic_to_real (Dyadic.divDown approxParam 1 5) :=
    divDown_nonneg approxParam (by rw [h1d]; norm_num) (by rw [h5]; norm_num)
  have hq1Lo_1 : dyadic_to_real (Dyadic.divDown approxParam 1 5) ≤ 1 :=
    le_trans hq1Lo_le (by norm_num)
  have hq1Hi_ge : (5 : ℝ)⁻¹ ≤ dyadic_to_real (Dyadic.divUp approxParam 1 5) := by
    have := le_divUp approxParam (a := 1) h5pos
    rw [h1d, h5, one_div] at this; exact this
  have hq1Hi_1 : dyadic_to_real (Dyadic.divUp approxParam 1 5) ≤ 1 :=
    divUp_one_le_one approxParam (by rw [h5]; norm_num)
  have hq1Hi_0 : 0 < dyadic_to_real (Dyadic.divUp approxParam 1 5) :=
    lt_of_lt_of_le (by norm_num) hq1Hi_ge
  have hq2Lo_le : dyadic_to_real (Dyadic.divDown approxParam 1 239) ≤ (239 : ℝ)⁻¹ := by
    have := divDown_le approxParam (a := 1) h239pos
    rw [h1d, h239, one_div] at this; exact this
  have hq2Lo_0 : 0 ≤ dyadic_to_real (Dyadic.divDown approxParam 1 239) :=
    divDown_nonneg approxParam (by rw [h1d]; norm_num) (by rw [h239]; norm_num)
  have hq2Lo_1 : dyadic_to_real (Dyadic.divDown approxParam 1 239) ≤ 1 :=
    le_trans hq2Lo_le (by norm_num)
  have hq2Hi_ge : (239 : ℝ)⁻¹ ≤ dyadic_to_real (Dyadic.divUp approxParam 1 239) := by
    have := le_divUp approxParam (a := 1) h239pos
    rw [h1d, h239, one_div] at this; exact this
  have hq2Hi_1 : dyadic_to_real (Dyadic.divUp approxParam 1 239) ≤ 1 :=
    divUp_one_le_one approxParam (by rw [h239]; norm_num)
  have hq2Hi_0 : 0 < dyadic_to_real (Dyadic.divUp approxParam 1 239) :=
    lt_of_lt_of_le (by norm_num) hq2Hi_ge
  rw [Interval.mem_toSet]
  constructor
  · simp only [Interval.dyadicPi, LowerBound.Bounds, Bool.false_eq_true, ↓reduceIte]
    rw [pi_eq_machin, dyadic_to_real_sub, dyadic_to_real_mul, dyadic_to_real_mul, h16, h4]
    have hAL : dyadic_to_real (Dyadic.atanLower approxParam (Dyadic.divDown approxParam 1 5)
          (Dyadic.atanTerms approxParam)) ≤ Real.arctan (5 : ℝ)⁻¹ :=
      le_trans (atanLower_le_arctan _ _ hq1Lo_0 hq1Lo_1) (Real.arctan_le_arctan_iff.mpr hq1Lo_le)
    have hAU : Real.arctan (239 : ℝ)⁻¹ < dyadic_to_real (Dyadic.atanUpper approxParam
          (Dyadic.divUp approxParam 1 239) (Dyadic.atanTerms approxParam)) :=
      lt_of_le_of_lt (Real.arctan_le_arctan_iff.mpr hq2Hi_ge)
        (arctan_lt_atanUpper _ _ hq2Hi_0 hq2Hi_1)
    linarith
  · simp only [Interval.dyadicPi, UpperBound.Bounds, Bool.false_eq_true, ↓reduceIte]
    rw [pi_eq_machin, dyadic_to_real_sub, dyadic_to_real_mul, dyadic_to_real_mul, h16, h4]
    have hAU : Real.arctan (5 : ℝ)⁻¹ < dyadic_to_real (Dyadic.atanUpper approxParam
          (Dyadic.divUp approxParam 1 5) (Dyadic.atanTerms approxParam)) :=
      lt_of_le_of_lt (Real.arctan_le_arctan_iff.mpr hq1Hi_ge)
        (arctan_lt_atanUpper _ _ hq1Hi_0 hq1Hi_1)
    have hAL : dyadic_to_real (Dyadic.atanLower approxParam (Dyadic.divDown approxParam 1 239)
          (Dyadic.atanTerms approxParam)) ≤ Real.arctan (239 : ℝ)⁻¹ :=
      le_trans (atanLower_le_arctan _ _ hq2Lo_0 hq2Lo_1) (Real.arctan_le_arctan_iff.mpr hq2Lo_le)
    linarith

end Pi

/- ## Transcendental Functions -/

/- ## Transcendental Functions -/

section Log

/--
Number of `atanh`-series terms used for `log`.

For `1 ≤ x ≤ 2`, we use

  `log x = 2 * (z + z^3 / 3 + z^5 / 5 + ...)`

where

  `z = (x - 1) / (x + 1)`.

Since `0 ≤ z ≤ 1 / 3`, this converges fairly quickly.
-/
def logTaylorTerms (approxParam : ℕ) : ℕ :=
  approxParam / 3 + 8

def logSeriesLowerAux (approxParam : ℕ) (z2 : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic
  | 0, _i, _zpow, acc => acc
  | n + 1, i, zpow, acc =>
      let denom : Dyadic := (2 * i + 1 : ℕ)
      let term := Dyadic.divDown approxParam zpow denom
      logSeriesLowerAux approxParam z2 n (i + 1) (zpow * z2) (acc + term)

def logSeriesUpperAux (approxParam : ℕ) (z2 : Dyadic) :
    ℕ → ℕ → Dyadic → Dyadic → Dyadic
  | 0, _i, _zpow, acc => acc
  | n + 1, i, zpow, acc =>
      let denom : Dyadic := (2 * i + 1 : ℕ)
      let term := Dyadic.divUp approxParam zpow denom
      logSeriesUpperAux approxParam z2 n (i + 1) (zpow * z2) (acc + term)

def logSeriesLower (approxParam terms : ℕ) (z : Dyadic) : Dyadic :=
  logSeriesLowerAux approxParam (z * z) terms 0 z 0

def logSeriesUpper (approxParam terms : ℕ) (z : Dyadic) : Dyadic :=
  logSeriesUpperAux approxParam (z * z) terms 0 z 0

/--
Bounds for `log x` when `1 ≤ x ≤ 2`.

Uses

  `log x = 2 * atanh ((x - 1) / (x + 1))`

i.e.

  `log x = 2 * Σ z^(2i+1)/(2i+1)`.
-/
def logUnitBounds (approxParam terms : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  let zLower := Dyadic.divDown approxParam (x - 1) (x + 1)
  let zUpper := Dyadic.divUp approxParam (x - 1) (x + 1)
  let lower := (2 : Dyadic) * logSeriesLower approxParam terms zLower
  let upperSeries := (2 : Dyadic) * logSeriesUpper approxParam terms zUpper
  /-
  Crude positive tail bound.

  For normalized inputs `1 ≤ x ≤ 2`, we have `0 ≤ z ≤ 1/3`.
  The omitted tail of

    2 * Σ z^(2i+1)/(2i+1)

  is bounded by something crude like

    3 * z^(2*terms+1).

  This is deliberately simple and kernel-friendly.
  -/
  let tail := (3 : Dyadic) * (zUpper ^ (2 * terms + 1))
  (lower, upperSeries + tail)

/--
Normalize a positive dyadic as

  `x = m * 2^e`

with approximately

  `1 ≤ m < 2`.

If

  `x = n * 2^(-k)`

and `L = n.natAbs.bitLen`, then

  `m = n * 2^(-(L - 1))`,
  `e = (L - 1) - k`.

This reuses the `_root_.Nat.bitLen` you already defined in the `Exp` section.
-/
def logNormalizePos (x : Dyadic) : Dyadic × Int :=
  match x with
  | .zero => (1, 0)
  | .ofOdd n k _ =>
      let L := n.natAbs.bitLen
      let p : Int := (L - 1 : ℕ)
      (Dyadic.ofIntWithPrec n p, p - k)

def intAsDyadic (z : Int) : Dyadic :=
  Dyadic.ofIntWithPrec z 0

def mulIntLogBounds (e : Int) (lo hi : Dyadic) : Dyadic × Dyadic :=
  let eD := intAsDyadic e
  if e < 0 then
    (eD * hi, eD * lo)
  else
    (eD * lo, eD * hi)

/--
Core logarithm approximation for positive dyadics.

Range reduction:

  `x = m * 2^e`, with `1 ≤ m < 2`.

Then

  `log x = log m + e * log 2`.
-/
def logBoundsCore
    (approxParam terms : ℕ) (logTwoBounds : Dyadic × Dyadic) (x : Dyadic) :
    Dyadic × Dyadic :=
  let (m, e) := logNormalizePos x
  let (mLower, mUpper) := logUnitBounds approxParam terms m
  let (twoLower, twoUpper) := logTwoBounds
  let (eLower, eUpper) := mulIntLogBounds e twoLower twoUpper
  (mLower + eLower, mUpper + eUpper)

/--
Bounds for `log x` for positive dyadic `x`.

This recomputes bounds for `log 2`, so interval operations should usually use
`logBoundsCore` and share `logTwoBounds`.
-/
def logBounds (approxParam : ℕ) (x : Dyadic) : Dyadic × Dyadic :=
  let terms := logTaylorTerms approxParam
  let logTwoBounds := logUnitBounds approxParam terms (2 : Dyadic)
  logBoundsCore approxParam terms logTwoBounds x

/--
Interval extension of real logarithm.

If the interval is not bounded away from zero on the left, this conservatively
returns the full interval.
-/
def Interval.dyadic_log (approxParam : ℕ) (x : Interval Dyadic) : Interval Dyadic :=
  let terms := logTaylorTerms approxParam
  let logTwoBounds := logUnitBounds approxParam terms (2 : Dyadic)
  match x.lb, x.ub with
  | some ⟨_, a⟩, some ⟨_, b⟩ =>
      if 0 < a then
        let lo := (logBoundsCore approxParam terms logTwoBounds a).1
        let hi := (logBoundsCore approxParam terms logTwoBounds b).2
        ⟨some ⟨true, lo⟩, some ⟨true, hi⟩⟩
      else
        ⟨⊥, ⊤⟩
  | some ⟨_, a⟩, ⊤ =>
      if 0 < a then
        let lo := (logBoundsCore approxParam terms logTwoBounds a).1
        ⟨some ⟨true, lo⟩, ⊤⟩
      else
        ⟨⊥, ⊤⟩
  | _, _ => ⟨⊥, ⊤⟩

/-! ### Helper lemmas for `log` soundness -/

lemma dyadic_to_real_two : dyadic_to_real (2 : Dyadic) = 2 := by
  have h : (2 : Dyadic).toRat = 2 := by decide
  rw [dyadic_to_real, h]; norm_num

lemma dyadic_to_real_three : dyadic_to_real (3 : Dyadic) = 3 := by
  have h : (3 : Dyadic).toRat = 3 := by decide
  rw [dyadic_to_real, h]; norm_num

/-- Invariant for the lower `atanh`-series accumulator: the accumulated value stays below the
partial sum of the positive series `∑ z^(2i+1)/(2i+1)`, since each term is rounded down. -/
lemma logSeriesLowerAux_le (p : ℕ) (z : Dyadic) :
    ∀ (n i : ℕ) (zpow acc : Dyadic),
      dyadic_to_real zpow = (dyadic_to_real z) ^ (2 * i + 1) →
      dyadic_to_real (logSeriesLowerAux p (z * z) n i zpow acc)
        ≤ dyadic_to_real acc
          + ∑ j ∈ Finset.range n,
              (dyadic_to_real z) ^ (2 * (i + j) + 1) / ((2 * (i + j) + 1 : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero => intro i zpow acc _; simp [logSeriesLowerAux]
  | succ n ih =>
    intro i zpow acc hzpow
    have hdenom : (0 : Dyadic) < ((2 * i + 1 : ℕ) : Dyadic) := by
      rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, dyadic_to_real_natCast]
      positivity
    have hterm : dyadic_to_real (Dyadic.divDown p zpow ((2 * i + 1 : ℕ) : Dyadic))
        ≤ (dyadic_to_real z) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ) := by
      have hd := divDown_le p (a := zpow) hdenom
      rwa [dyadic_to_real_natCast, hzpow] at hd
    have hzpow' : dyadic_to_real (zpow * (z * z)) = (dyadic_to_real z) ^ (2 * (i + 1) + 1) := by
      rw [dyadic_to_real_mul, dyadic_to_real_mul, hzpow,
        show 2 * (i + 1) + 1 = (2 * i + 1) + 2 from by ring, pow_add]; ring
    have hreindex : (∑ j ∈ Finset.range n,
          (dyadic_to_real z) ^ (2 * ((i + 1) + j) + 1) / ((2 * ((i + 1) + j) + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.range n,
          (dyadic_to_real z) ^ (2 * (i + (j + 1)) + 1) / ((2 * (i + (j + 1)) + 1 : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by rw [show (i + 1) + j = i + (j + 1) from by omega])
    simp only [logSeriesLowerAux]
    refine le_trans (ih (i + 1) (zpow * (z * z))
      (acc + Dyadic.divDown p zpow ((2 * i + 1 : ℕ) : Dyadic)) hzpow') ?_
    rw [dyadic_to_real_add, Finset.sum_range_succ', hreindex]
    simp only [Nat.add_zero]
    linarith [hterm]

/-- The lower series `logSeriesLower` underestimates the partial sum of `∑ z^(2i+1)/(2i+1)`. -/
lemma logSeriesLower_le (p terms : ℕ) (z : Dyadic) :
    dyadic_to_real (logSeriesLower p terms z)
      ≤ ∑ j ∈ Finset.range terms,
          (dyadic_to_real z) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
  have hinv : dyadic_to_real z = (dyadic_to_real z) ^ (2 * 0 + 1) := by norm_num
  have h := logSeriesLowerAux_le p z terms 0 z 0 hinv
  rw [dyadic_to_real_zero, zero_add] at h
  rw [logSeriesLower]
  refine h.trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
  rw [Nat.zero_add]

/-- Invariant for the upper `atanh`-series accumulator: the accumulated value stays above the
partial sum, since each term is rounded up. -/
lemma le_logSeriesUpperAux (p : ℕ) (z : Dyadic) :
    ∀ (n i : ℕ) (zpow acc : Dyadic),
      dyadic_to_real zpow = (dyadic_to_real z) ^ (2 * i + 1) →
      dyadic_to_real acc
        + ∑ j ∈ Finset.range n,
            (dyadic_to_real z) ^ (2 * (i + j) + 1) / ((2 * (i + j) + 1 : ℕ) : ℝ)
      ≤ dyadic_to_real (logSeriesUpperAux p (z * z) n i zpow acc) := by
  intro n
  induction n with
  | zero => intro i zpow acc _; simp [logSeriesUpperAux]
  | succ n ih =>
    intro i zpow acc hzpow
    have hdenom : (0 : Dyadic) < ((2 * i + 1 : ℕ) : Dyadic) := by
      rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, dyadic_to_real_natCast]
      positivity
    have hterm : (dyadic_to_real z) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)
        ≤ dyadic_to_real (Dyadic.divUp p zpow ((2 * i + 1 : ℕ) : Dyadic)) := by
      have hd := le_divUp p (a := zpow) hdenom
      rwa [dyadic_to_real_natCast, hzpow] at hd
    have hzpow' : dyadic_to_real (zpow * (z * z)) = (dyadic_to_real z) ^ (2 * (i + 1) + 1) := by
      rw [dyadic_to_real_mul, dyadic_to_real_mul, hzpow,
        show 2 * (i + 1) + 1 = (2 * i + 1) + 2 from by ring, pow_add]; ring
    have hreindex : (∑ j ∈ Finset.range n,
          (dyadic_to_real z) ^ (2 * ((i + 1) + j) + 1) / ((2 * ((i + 1) + j) + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.range n,
          (dyadic_to_real z) ^ (2 * (i + (j + 1)) + 1) / ((2 * (i + (j + 1)) + 1 : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun j _ => by rw [show (i + 1) + j = i + (j + 1) from by omega])
    simp only [logSeriesUpperAux]
    refine le_trans ?_ (ih (i + 1) (zpow * (z * z))
      (acc + Dyadic.divUp p zpow ((2 * i + 1 : ℕ) : Dyadic)) hzpow')
    rw [dyadic_to_real_add, Finset.sum_range_succ', hreindex]
    simp only [Nat.add_zero]
    linarith [hterm]

/-- The upper series `logSeriesUpper` overestimates the partial sum of `∑ z^(2i+1)/(2i+1)`. -/
lemma le_logSeriesUpper (p terms : ℕ) (z : Dyadic) :
    ∑ j ∈ Finset.range terms,
        (dyadic_to_real z) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)
      ≤ dyadic_to_real (logSeriesUpper p terms z) := by
  have hinv : dyadic_to_real z = (dyadic_to_real z) ^ (2 * 0 + 1) := by norm_num
  have h := le_logSeriesUpperAux p z terms 0 z 0 hinv
  rw [dyadic_to_real_zero, zero_add] at h
  rw [logSeriesUpper]
  refine (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))).trans h
  rw [Nat.zero_add]

/-- The real `atanh` series identity: for `1 ≤ m ≤ 2`, with `z = (m-1)/(m+1)`,
`log m = 2 * ∑ z^(2k+1)/(2k+1)`, i.e. `∑ z^(2k+1)/(2k+1)` sums to `log m / 2`. -/
lemma log_atanh_hasSum {m : ℝ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    HasSum (fun k : ℕ => ((m - 1) / (m + 1)) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      (Real.log m / 2) := by
  have hmpos : (0 : ℝ) < m + 1 := by linarith
  have hm1ne : (m : ℝ) + 1 ≠ 0 := ne_of_gt hmpos
  set z := (m - 1) / (m + 1) with hz
  have hz0 : 0 ≤ z := by rw [hz]; exact div_nonneg (by linarith) (by linarith)
  have hzlt1 : z < 1 := by rw [hz, div_lt_one hmpos]; linarith
  have hzabs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hzlt1
  have h1z : (1 : ℝ) + z ≠ 0 := ne_of_gt (by linarith)
  have h1z' : (1 : ℝ) - z ≠ 0 := ne_of_gt (by linarith)
  have hzeq : z * (m + 1) = m - 1 := by rw [hz]; field_simp
  have hval : (1 + z) / (1 - z) = m := by
    rw [div_eq_iff h1z']; linear_combination hzeq
  have hkey := Real.hasSum_log_sub_log_of_abs_lt_one hzabs
  have hlogm : Real.log (1 + z) - Real.log (1 - z) = Real.log m := by
    rw [← Real.log_div h1z h1z', hval]
  rw [hlogm] at hkey
  have hgf : (fun k : ℕ => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))
      = fun k : ℕ => (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) / 2 := by
    funext k
    have hk : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
    rw [hk]; ring
  rw [hgf]
  exact hkey.div_const 2

/-- Geometric tail bound: the tail of `∑ Z^(2k+1)/(2k+1)` beyond `N` terms, for `0 ≤ Z ≤ 1/3`,
is at most `(3/2)·Z^(2N+1)`. -/
lemma log_series_tail_le {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ13 : Z ≤ 1 / 3) (N : ℕ) {L : ℝ}
    (hSum : HasSum (fun k : ℕ => Z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) L) :
    L - ∑ j ∈ Finset.range N, Z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)
      ≤ (3 / 2) * Z ^ (2 * N + 1) := by
  have hZ2_9 : Z ^ 2 ≤ 1 / 9 := by
    have h : Z ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hZ0 hZ13 2
    have h9 : ((1 : ℝ) / 3) ^ 2 = 1 / 9 := by norm_num
    linarith [h, h9]
  have hZ2_0 : (0 : ℝ) ≤ Z ^ 2 := sq_nonneg Z
  have hZ2_1 : Z ^ 2 < 1 := by linarith
  have hden : (0 : ℝ) < 1 - Z ^ 2 := by linarith
  set S := fun k : ℕ => Z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) with hS
  have hTail : HasSum (fun i : ℕ => S (i + N)) (L - ∑ j ∈ Finset.range N, S j) :=
    (hasSum_nat_add_iff' N).mpr hSum
  have hGeom : HasSum (fun i : ℕ => Z ^ (2 * N + 1) * (Z ^ 2) ^ i)
      (Z ^ (2 * N + 1) * (1 - Z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hZ2_0 hZ2_1).mul_left _
  have hterm : ∀ i, S (i + N) ≤ Z ^ (2 * N + 1) * (Z ^ 2) ^ i := by
    intro i
    have hpe : Z ^ (2 * N + 1) * (Z ^ 2) ^ i = Z ^ (2 * (i + N) + 1) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [hpe]
    simp only [hS]
    apply div_le_self (pow_nonneg hZ0 _)
    exact_mod_cast Nat.le_add_left 1 (2 * (i + N))
  have hle := hasSum_le hterm hTail hGeom
  have hinv_le : (1 - Z ^ 2)⁻¹ ≤ 3 / 2 := by
    rw [← one_div, div_le_iff₀ hden]; linarith
  refine hle.trans ?_
  rw [mul_comm ((3 : ℝ) / 2) (Z ^ (2 * N + 1))]
  exact mul_le_mul_of_nonneg_left hinv_le (pow_nonneg hZ0 _)

/-- Soundness of `logUnitBounds`: for a dyadic `m` with `1 ≤ m ≤ 2`, the returned pair
brackets `log m`. -/
lemma logUnitBounds_correct (p terms : ℕ) {m : Dyadic}
    (hm1 : 1 ≤ dyadic_to_real m) (hm2 : dyadic_to_real m ≤ 2) :
    dyadic_to_real (logUnitBounds p terms m).1 ≤ Real.log (dyadic_to_real m) ∧
    Real.log (dyadic_to_real m) ≤ dyadic_to_real (logUnitBounds p terms m).2 := by
  have hSum := log_atanh_hasSum hm1 hm2
  have hmpos : (0 : ℝ) < dyadic_to_real m + 1 := by linarith
  set zR := (dyadic_to_real m - 1) / (dyadic_to_real m + 1) with hzR
  have hz0 : 0 ≤ zR := by rw [hzR]; exact div_nonneg (by linarith) (by linarith)
  have hz13 : zR ≤ 1 / 3 := by rw [hzR, div_le_iff₀ hmpos]; linarith
  have hmm1 : dyadic_to_real (m - 1) = dyadic_to_real m - 1 := by
    rw [dyadic_to_real_sub, dyadic_to_real_one]
  have hmp1 : dyadic_to_real (m + 1) = dyadic_to_real m + 1 := by
    rw [dyadic_to_real_add, dyadic_to_real_one]
  have hm1pos_d : (0 : Dyadic) < m + 1 := by
    rw [← strictMono_dyadic_to_real.lt_iff_lt, dyadic_to_real_zero, hmp1]; linarith
  have hzL_le : dyadic_to_real (Dyadic.divDown p (m - 1) (m + 1)) ≤ zR := by
    have h := divDown_le p (a := m - 1) hm1pos_d
    rw [hmm1, hmp1] at h; rw [hzR]; exact h
  have hzL0 : 0 ≤ dyadic_to_real (Dyadic.divDown p (m - 1) (m + 1)) :=
    divDown_nonneg p (by rw [hmm1]; linarith) (by rw [hmp1]; linarith)
  have hzU_ge : zR ≤ dyadic_to_real (Dyadic.divUp p (m - 1) (m + 1)) := by
    have h := le_divUp p (a := m - 1) hm1pos_d
    rw [hmm1, hmp1] at h; rw [hzR]; exact h
  have hnn : ∀ j : ℕ, (0 : ℝ) ≤ zR ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) :=
    fun j => div_nonneg (pow_nonneg hz0 _) (by positivity)
  have hpartial_le := sum_le_hasSum (Finset.range terms) (fun j _ => hnn j) hSum
  constructor
  · -- lower endpoint
    have hlo : (logUnitBounds p terms m).1
        = (2 : Dyadic) * logSeriesLower p terms (Dyadic.divDown p (m - 1) (m + 1)) := rfl
    rw [hlo]
    simp only [dyadic_to_real_mul, dyadic_to_real_two]
    have hstep1 : dyadic_to_real (logSeriesLower p terms (Dyadic.divDown p (m - 1) (m + 1)))
        ≤ Real.log (dyadic_to_real m) / 2 := by
      refine le_trans (logSeriesLower_le p terms _)
        (le_trans (Finset.sum_le_sum ?_) hpartial_le)
      intro j _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hzL0 hzL_le _) (by positivity)
    linarith [hstep1]
  · -- upper endpoint
    have hhi : (logUnitBounds p terms m).2
        = (2 : Dyadic) * logSeriesUpper p terms (Dyadic.divUp p (m - 1) (m + 1))
          + (3 : Dyadic) * (Dyadic.divUp p (m - 1) (m + 1)) ^ (2 * terms + 1) := rfl
    rw [hhi]
    simp only [dyadic_to_real_add, dyadic_to_real_mul, dyadic_to_real_two, dyadic_to_real_three,
      dyadic_to_real_pow]
    have htail := log_series_tail_le hz0 hz13 terms hSum
    have hzUpow : zR ^ (2 * terms + 1)
        ≤ (dyadic_to_real (Dyadic.divUp p (m - 1) (m + 1))) ^ (2 * terms + 1) :=
      pow_le_pow_left₀ hz0 hzU_ge _
    have hSigma : (∑ j ∈ Finset.range terms, zR ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ))
        ≤ dyadic_to_real (logSeriesUpper p terms (Dyadic.divUp p (m - 1) (m + 1))) := by
      refine le_trans (Finset.sum_le_sum ?_) (le_logSeriesUpper p terms _)
      intro j _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 hzU_ge _) (by positivity)
    linarith [htail, hSigma, hzUpow]

/-- A `zpow` identity for the range-reduction correctness. -/
lemma div_zpow_mul_zpow (b : ℝ) (p k : ℤ) :
    b / (2 : ℝ) ^ p * (2 : ℝ) ^ (p - k) = b * (2 : ℝ) ^ (-k) := by
  rw [div_mul_eq_mul_div, mul_div_assoc, ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
    show p - k - p = -k from by ring]

/-- Lower bound complementing `lt_two_pow_bitLen`: `2 ^ bitLen n ≤ 2 * n` for `n ≥ 1`. -/
lemma bitLenAux_two_pow_le :
    ∀ (fuel n : ℕ), n ≤ fuel → 1 ≤ n → 2 ^ (bitLenAux fuel n) ≤ 2 * n := by
  have hzero : ∀ f, bitLenAux f 0 = 0 := by intro f; cases f <;> simp [bitLenAux]
  intro fuel
  induction fuel with
  | zero => intro n hn h1; omega
  | succ fuel ih =>
    intro n hn h1
    have hn0 : ¬ (n = 0) := by omega
    rw [bitLenAux, if_neg hn0, pow_add, pow_one]
    by_cases h2 : n = 1
    · subst h2; simp [hzero]
    · have hle : n / 2 ≤ fuel := by omega
      have h1' : 1 ≤ n / 2 := by omega
      have hih := ih (n / 2) hle h1'
      have hhalf : 2 * (n / 2) ≤ n := by omega
      linarith [hih, hhalf]

lemma two_pow_bitLen_le {n : ℕ} (h1 : 1 ≤ n) : 2 ^ n.bitLen ≤ 2 * n := by
  rw [Nat.bitLen]
  exact bitLenAux_two_pow_le n n le_rfl h1

/-- Correctness of `logNormalizePos`: for `0 < x`, writing `(m, e) = logNormalizePos x`,
we have `m * 2^e = x` and `1 ≤ m ≤ 2`. -/
lemma logNormalizePos_spec {x : Dyadic} (hx : 0 < dyadic_to_real x) :
    dyadic_to_real (logNormalizePos x).1 * (2 : ℝ) ^ (logNormalizePos x).2 = dyadic_to_real x ∧
    1 ≤ dyadic_to_real (logNormalizePos x).1 ∧ dyadic_to_real (logNormalizePos x).1 ≤ 2 := by
  rcases x with _ | ⟨n, k, hn⟩
  · exact absurd hx (by rw [Dyadic.zero_eq, dyadic_to_real_zero]; exact lt_irrefl 0)
  · rw [dyadic_to_real_ofOdd] at hx
    have h2k : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
    have hnR : 0 < (n : ℝ) := by
      rcases mul_pos_iff.mp hx with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith
    have hn_pos : 0 < n := by exact_mod_cast hnR
    have hnatAbs1 : 1 ≤ n.natAbs := by omega
    have hnabs : (n : ℝ) = (n.natAbs : ℝ) := by
      have h : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn_pos.le
      calc (n : ℝ) = ((n.natAbs : ℤ) : ℝ) := by rw [h]
        _ = (n.natAbs : ℝ) := Int.cast_natCast _
    have hupper : n.natAbs < 2 ^ n.natAbs.bitLen := lt_two_pow_bitLen n.natAbs
    have hlower : 2 ^ n.natAbs.bitLen ≤ 2 * n.natAbs := two_pow_bitLen_le hnatAbs1
    have hL1 : 1 ≤ n.natAbs.bitLen := by
      rcases Nat.eq_zero_or_pos n.natAbs.bitLen with h0 | h0
      · rw [h0, pow_zero] at hupper; omega
      · exact h0
    have hfst : (logNormalizePos (Dyadic.ofOdd n k hn)).1
        = Dyadic.ofIntWithPrec n ((n.natAbs.bitLen - 1 : ℕ) : ℤ) := rfl
    have hsnd : (logNormalizePos (Dyadic.ofOdd n k hn)).2
        = ((n.natAbs.bitLen - 1 : ℕ) : ℤ) - k := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hfst, hsnd, dyadic_to_real_ofIntWithPrec_int, dyadic_to_real_ofOdd]
      exact div_zpow_mul_zpow _ _ _
    · rw [hfst, dyadic_to_real_ofIntWithPrec_int,
        le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ ((n.natAbs.bitLen - 1 : ℕ) : ℤ)),
        one_mul, zpow_natCast, hnabs]
      have hthis : 2 ^ (n.natAbs.bitLen - 1) ≤ n.natAbs := by
        have hLs : n.natAbs.bitLen = (n.natAbs.bitLen - 1) + 1 := by omega
        have h := hlower
        rw [hLs, pow_succ] at h
        omega
      exact_mod_cast hthis
    · rw [hfst, dyadic_to_real_ofIntWithPrec_int,
        div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ ((n.natAbs.bitLen - 1 : ℕ) : ℤ)),
        zpow_natCast, hnabs]
      have hthis : n.natAbs < 2 * 2 ^ (n.natAbs.bitLen - 1) := by
        have hLs : n.natAbs.bitLen = (n.natAbs.bitLen - 1) + 1 := by omega
        have h := hupper
        rw [hLs, pow_succ] at h
        omega
      exact_mod_cast le_of_lt hthis

/-- Correctness of `mulIntLogBounds`: given bounds `lo ≤ L ≤ hi`, the pair brackets `e * L`. -/
lemma mulIntLogBounds_correct (e : Int) {lo hi : Dyadic} {L : ℝ}
    (hlo : dyadic_to_real lo ≤ L) (hhi : L ≤ dyadic_to_real hi) :
    dyadic_to_real (mulIntLogBounds e lo hi).1 ≤ (e : ℝ) * L ∧
    (e : ℝ) * L ≤ dyadic_to_real (mulIntLogBounds e lo hi).2 := by
  have heD : dyadic_to_real (intAsDyadic e) = (e : ℝ) := by
    rw [intAsDyadic, dyadic_to_real_ofIntWithPrec_int]; norm_num
  by_cases he : e < 0
  · have hpair : mulIntLogBounds e lo hi = (intAsDyadic e * hi, intAsDyadic e * lo) := by
      simp only [mulIntLogBounds, if_pos he]
    have h1 : (mulIntLogBounds e lo hi).1 = intAsDyadic e * hi := by rw [hpair]
    have h2 : (mulIntLogBounds e lo hi).2 = intAsDyadic e * lo := by rw [hpair]
    rw [h1, h2, dyadic_to_real_mul, dyadic_to_real_mul, heD]
    have heR : (e : ℝ) ≤ 0 := by exact_mod_cast le_of_lt he
    exact ⟨mul_le_mul_of_nonpos_left hhi heR, mul_le_mul_of_nonpos_left hlo heR⟩
  · have hpair : mulIntLogBounds e lo hi = (intAsDyadic e * lo, intAsDyadic e * hi) := by
      simp only [mulIntLogBounds, if_neg he]
    have h1 : (mulIntLogBounds e lo hi).1 = intAsDyadic e * lo := by rw [hpair]
    have h2 : (mulIntLogBounds e lo hi).2 = intAsDyadic e * hi := by rw [hpair]
    rw [h1, h2, dyadic_to_real_mul, dyadic_to_real_mul, heD]
    have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast not_lt.mp he
    exact ⟨mul_le_mul_of_nonneg_left hlo heR, mul_le_mul_of_nonneg_left hhi heR⟩

/-- Correctness of `logBoundsCore`: for `0 < x` and valid `logTwoBounds` (bracketing `log 2`),
the returned pair brackets `log x`. -/
lemma logBoundsCore_correct (p terms : ℕ) (logTwoBounds : Dyadic × Dyadic) {x : Dyadic}
    (hx : 0 < dyadic_to_real x)
    (hlo2 : dyadic_to_real logTwoBounds.1 ≤ Real.log 2)
    (hhi2 : Real.log 2 ≤ dyadic_to_real logTwoBounds.2) :
    dyadic_to_real (logBoundsCore p terms logTwoBounds x).1 ≤ Real.log (dyadic_to_real x) ∧
    Real.log (dyadic_to_real x) ≤ dyadic_to_real (logBoundsCore p terms logTwoBounds x).2 := by
  obtain ⟨hprod, hm1, hm2⟩ := logNormalizePos_spec hx
  have hmpos : 0 < dyadic_to_real (logNormalizePos x).1 := by linarith
  have hlogx : Real.log (dyadic_to_real x)
      = Real.log (dyadic_to_real (logNormalizePos x).1)
        + ((logNormalizePos x).2 : ℝ) * Real.log 2 := by
    rw [← hprod, Real.log_mul (ne_of_gt hmpos)
      (by positivity : (0 : ℝ) < (2 : ℝ) ^ (logNormalizePos x).2).ne', Real.log_zpow]
  obtain ⟨hmL, hmU⟩ := logUnitBounds_correct p terms hm1 hm2
  obtain ⟨heL, heU⟩ := mulIntLogBounds_correct (logNormalizePos x).2 hlo2 hhi2
  have hfst : (logBoundsCore p terms logTwoBounds x).1
      = (logUnitBounds p terms (logNormalizePos x).1).1
        + (mulIntLogBounds (logNormalizePos x).2 logTwoBounds.1 logTwoBounds.2).1 := rfl
  have hsnd : (logBoundsCore p terms logTwoBounds x).2
      = (logUnitBounds p terms (logNormalizePos x).1).2
        + (mulIntLogBounds (logNormalizePos x).2 logTwoBounds.1 logTwoBounds.2).2 := rfl
  rw [hfst, hsnd, dyadic_to_real_add, dyadic_to_real_add, hlogx]
  exact ⟨by linarith [hmL, heL], by linarith [hmU, heU]⟩

@[interval_op DyadicReal Real.log]
theorem Interval.dyadic_log_inclusion {r : ℝ} {x : Interval Dyadic}
    (approxParam : ℕ) (hrx : r ∈ x.toSet dyadic_to_real) :
    Real.log r ∈ (x.dyadic_log approxParam).toSet dyadic_to_real := by
  have h2m1 : (1 : ℝ) ≤ dyadic_to_real (2 : Dyadic) := by rw [dyadic_to_real_two]; norm_num
  have h2m2 : dyadic_to_real (2 : Dyadic) ≤ 2 := by rw [dyadic_to_real_two]
  obtain ⟨hlo2, hhi2⟩ :=
    logUnitBounds_correct approxParam (logTaylorTerms approxParam) h2m1 h2m2
  rw [dyadic_to_real_two] at hlo2 hhi2
  obtain ⟨xlb, xub⟩ := x
  rw [Interval.mem_toSet] at hrx ⊢
  obtain ⟨hlb, hub⟩ := hrx
  cases xlb with
  | none =>
    cases xub <;> refine ⟨?_, ?_⟩ <;>
      simp only [Interval.dyadic_log, LowerBound.bot_Bounds, UpperBound.top_Bounds]
  | some flb =>
    obtain ⟨cl, a⟩ := flb
    have harle : dyadic_to_real a ≤ r := by
      simp only [LowerBound.Bounds] at hlb
      cases cl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hlb; linarith
      · simpa only [↓reduceIte] using hlb
    cases xub with
    | none =>
      simp only [Interval.dyadic_log]
      split_ifs with ha
      · refine ⟨?_, UpperBound.top_Bounds _ _⟩
        have haR : 0 < dyadic_to_real a := dyadic_to_real_pos ha
        obtain ⟨hloA, _⟩ := logBoundsCore_correct approxParam (logTaylorTerms approxParam)
          (logUnitBounds approxParam (logTaylorTerms approxParam) 2) haR hlo2 hhi2
        simp only [LowerBound.Bounds, ↓reduceIte]
        exact le_trans hloA (Real.log_le_log haR harle)
      · exact ⟨LowerBound.bot_Bounds _ _, UpperBound.top_Bounds _ _⟩
    | some fub =>
      obtain ⟨cu, b⟩ := fub
      have hrb : r ≤ dyadic_to_real b := by
        simp only [UpperBound.Bounds] at hub
        cases cu
        · simp only [Bool.false_eq_true, ↓reduceIte] at hub; linarith
        · simpa only [↓reduceIte] using hub
      simp only [Interval.dyadic_log]
      split_ifs with ha
      · have haR : 0 < dyadic_to_real a := dyadic_to_real_pos ha
        have hrpos : 0 < r := lt_of_lt_of_le haR harle
        have hbR : 0 < dyadic_to_real b := lt_of_lt_of_le hrpos hrb
        obtain ⟨hloA, _⟩ := logBoundsCore_correct approxParam (logTaylorTerms approxParam)
          (logUnitBounds approxParam (logTaylorTerms approxParam) 2) haR hlo2 hhi2
        obtain ⟨_, hhiB⟩ := logBoundsCore_correct approxParam (logTaylorTerms approxParam)
          (logUnitBounds approxParam (logTaylorTerms approxParam) 2) hbR hlo2 hhi2
        refine ⟨?_, ?_⟩
        · simp only [LowerBound.Bounds, ↓reduceIte]
          exact le_trans hloA (Real.log_le_log haR harle)
        · simp only [UpperBound.Bounds, ↓reduceIte]
          exact le_trans (Real.log_le_log hrpos hrb) hhiB
      · exact ⟨LowerBound.bot_Bounds _ _, UpperBound.top_Bounds _ _⟩

end Log

end IntervalArithmetic
