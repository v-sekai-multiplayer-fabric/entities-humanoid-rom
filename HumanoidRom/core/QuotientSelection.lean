-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Choosing a representative from a quotient, and the two ways it goes wrong.
--
-- ## The shape of the bug
--
-- A direction is a point on a sphere. A rotation is a point on a sphere with its antipode
-- glued to it, because a quaternion and its negation are the same rotation. Neither has a
-- canonical representative, and an operation that combines several of them has to choose one
-- for each before it can start.
--
-- There are exactly two ways that goes wrong, and this project has now met both.
--
-- **Averaging instead of selecting.** `KusudamaSolver` built the pole of its projection by
-- summing every cone centre and normalising. Three equidistant cones sum to zero, and
-- `normalize` of zero is undefined, so one unit in the last place moved the pole 45 degrees.
-- A mean of directions is not a direction. See `KusudamaEncoding`.
--
-- **Selecting with an order that is not total.** Godot's `spherical_cubic_interpolate`
-- selects a sign for each of three quaternions relative to a reference:
--
--     flip1 = signbit(from.dot(pre))
--     flip2 = signbit(from.dot(to))
--     flip3 = flip2 ? to.dot(post) <= 0 : signbit(to.dot(post))
--
-- The tie is `dot = 0`, which is a relative rotation of exactly 180 degrees, and that is a
-- pose that occurs rather than an exotic one. At the tie:
--
--   * `signbit` flips only when the zero is **negative** zero. `signbit(+0.0)` is false and
--     `signbit(-0.0)` is true.
--   * `<= 0` always flips.
--
-- A signed zero is a real feature of the format. It records the sign a quantity had before it
-- underflowed, so `-1e-300 * 1e-300` is `-0.0` and the sign is information. `signbit` is the
-- right question after an underflow and a meaningless one after an exact cancellation, where
-- there was no sign to remember. Here it is being read as though it were `d < 0`, and those
-- two differ only at `-0.0`.
--
-- **The authored case is not noisy.** IEEE gives `+0.0` for that dot product every time,
-- because `+0 * x` is `+0` and `+0 + +0` is `+0`. So the quaternion fault is deterministic
-- and inconsistent, rather than flaky: `flip1` and `flip2` never flip, `flip3` always does,
-- on every run and every machine.
--
-- That is a better account of why it survived than rarity. A flaky fault gets chased. One
-- that is wrong the same way every time, on an input the test data cannot produce, gets
-- shipped.
--
-- So the same tie is resolved two different ways inside one function. Neither is wrong on its
-- own. Being inconsistent is.
--
-- ## Why one broke and the other did not
--
-- The quaternion inconsistency has sat in a shipping engine unnoticed, and the kusudama one
-- broke a solve. Measuring where the two rules actually disagree says why:
--
--     d > 0                      agree
--     d < 0                      agree
--     d = -0.0                   agree
--     cos(pi/2), a computed 180  agree      the dot is 6.123e-17, not zero
--     d = +0.0, authored         DISAGREE
--
-- **They differ at exactly one value.** A computed half turn never lands on it, because
-- `cos(pi/2)` is 6.123e-17. Reaching it needs an authored key, a quaternion written literally
-- as (0, 1, 0, 0) against an identity reference. A test suite built from captured or computed
-- motion cannot produce it.
--
-- So the rule is not that ties are dangerous. It is:
--
-- **A degenerate point matters in proportion to how much the operation amplifies near it.**
--
--   * `normalize(sum)` divides by a quantity that goes to zero. One unit in the last place
--     becomes 45 degrees, and the whole neighbourhood of the tie is wrong, not just the tie.
--     That fires on ordinary input.
--   * `signbit(dot)` reads a sign. It is discontinuous at one point and correct everywhere
--     else, including 6.123e-17 away from it. That fires on authored input only.
--
-- Both deserve a total order. Only the first was going to be found by using the software.
--
-- ## The rule
--
-- **Pick one reference, apply one total order, and define it at the tie.**
--
-- Total is the word doing the work. An order that is undefined on equal elements is not an
-- order, and the place it is undefined is exactly the symmetric case, which is the case a
-- well-formed input produces. Both bugs above are the same bug at different points of that
-- sentence: one had no order, one had two.

import Shared.Types

namespace PredictiveBVH.QuotientSelection

/-- A quaternion, in thousandths, so every proof here is decidable without Mathlib. -/
structure Quat where
  w : Int
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq

def Quat.neg (q : Quat) : Quat := { w := -q.w, x := -q.x, y := -q.y, z := -q.z }

def dot (a b : Quat) : Int := a.w * b.w + a.x * b.x + a.y * b.y + a.z * b.z

/-- The identity rotation. -/
def ident : Quat := { w := 1000, x := 0, y := 0, z := 0 }

/-- A half turn about x. Exactly orthogonal to the identity, so `dot` is exactly zero.
    This is the tie, and it is an ordinary pose. -/
def halfTurnX : Quat := { w := 0, x := 1000, y := 0, z := 0 }

/-- A half turn about y. Also exactly orthogonal to the identity. -/
def halfTurnY : Quat := { w := 0, x := 0, y := 1000, z := 0 }

theorem half_turn_is_the_tie : dot ident halfTurnX = 0 := by decide

theorem half_turn_y_is_also_the_tie : dot ident halfTurnY = 0 := by decide

-- ── A total order on the representative ────────────────────────────────────

/-- Lexicographic sign of the first component that is not zero.

    This is the tie break, and it is a fact about the numbers rather than about how they were
    computed. A quaternion and its negation always differ here, because negation flips every
    component, so exactly one of the two is chosen and the choice never depends on a rounding
    mode, a sign of zero, or an evaluation order. -/
def leadingSignPositive (q : Quat) : Bool :=
  if q.w != 0 then q.w > 0
  else if q.x != 0 then q.x > 0
  else if q.y != 0 then q.y > 0
  else q.z ≥ 0

/-- Choose the representative of `q` that lies with `ref`, and at the tie choose by the
    leading sign. One rule, applied everywhere, defined everywhere. -/
def align (ref q : Quat) : Quat :=
  let d := dot ref q
  if d > 0 then q
  else if d < 0 then q.neg
  else if leadingSignPositive q then q else q.neg

-- ── What the rule buys ─────────────────────────────────────────────────────

/-- The tie has an answer. This is the property `signbit` did not have. -/
theorem align_is_defined_at_the_tie :
    align ident halfTurnX = halfTurnX := by decide

/-- And the negation of the same rotation gives the same representative. That is what makes
    it a choice of representative rather than a coin toss: both spellings of one rotation
    land on the same answer. -/
theorem align_agrees_on_both_spellings :
    align ident halfTurnX = align ident halfTurnX.neg := by decide

theorem align_agrees_on_both_spellings_y :
    align ident halfTurnY = align ident halfTurnY.neg := by decide

/-- Away from the tie the rule is the ordinary shortest path, so nothing else changes. -/
def quarterTurnX : Quat := { w := 707, x := 707, y := 0, z := 0 }

theorem align_is_shortest_path_away_from_the_tie :
    align ident quarterTurnX = quarterTurnX := by decide

theorem align_flips_the_far_side :
    align ident quarterTurnX.neg = quarterTurnX := by decide

/-- Applying it twice changes nothing. An operation that combines several elements may run it
    on each without worrying about the order they arrive in. -/
theorem align_is_idempotent :
    align ident (align ident halfTurnX) = align ident halfTurnX := by decide

theorem align_is_idempotent_far :
    align ident (align ident quarterTurnX.neg) = align ident quarterTurnX.neg := by decide

-- ── The two failures, side by side ─────────────────────────────────────────

/-- Godot resolves the tie one way in `flip1` and `flip2`, and the other way in `flip3` when
    `flip2` fired. Modelled here: `signbit` on a positive zero does not flip, and `<= 0`
    does. Both cannot be right for one rotation. -/
def flipBySignbit (positiveZero : Bool) : Bool := if positiveZero then false else true

def flipByLessEqual (_positiveZero : Bool) : Bool := true

theorem the_two_rules_disagree_at_the_tie :
    flipBySignbit true ≠ flipByLessEqual true := by decide

/-- And they agree away from the tie, which is why this survived. A bug that only appears on
    a symmetric input is invisible to a test suite written from asymmetric examples. -/
theorem the_two_rules_agree_on_a_negative_zero :
    flipBySignbit false = flipByLessEqual false := by decide

end PredictiveBVH.QuotientSelection
