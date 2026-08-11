-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Choosing a representative from a quotient.
--
-- A direction is a point on a sphere. A rotation is a point on a sphere with its antipode
-- glued to it, because a quaternion and its negation are the same rotation. Neither has a
-- canonical representative, so an operation combining several of them chooses one for each
-- before it starts.
--
-- **Pick one reference, apply one total order, and define it at the tie.**
--
-- Total is the word doing the work. An order undefined on equal elements is not an order, and
-- the place it is undefined is the symmetric case, which is what a well-formed input produces.
--
-- ## Where the rule comes from
--
-- One place, and not two. `KusudamaSolver` derived the pole of its projection by summing every
-- cone centre and normalising. Three equidistant cones sum to zero, `normalize` of zero is
-- undefined, and one unit in the last place moved the pole 45 degrees. A mean of directions is
-- not a direction, and the repair is a different algorithm rather than a corrected line. See
-- `KusudamaEncoding`.
--
-- The sharp part of that finding is not the tie. It is:
--
-- **A degenerate point matters in proportion to how much the operation amplifies near it.**
-- `normalize(sum)` divides by a quantity going to zero, so the whole neighbourhood of the tie
-- is wrong and not merely the tie. That is why it fired on ordinary input.
--
-- ## What this file is not evidence of
--
-- Godot's `spherical_cubic_interpolate` picks a sign for three quaternions with two different
-- tie breaks, `signbit` for two of them and `<= 0` for the third. They differ at exactly one
-- value, `+0.0`, which a computed rotation never produces and an authored key does.
--
-- **That is a deletable inconsistency and not a second instance of the rule.** One line
-- disagrees with two lines; make them agree and it is gone, with no design change. Treating it
-- as evidence for a principle would inflate a typo into a category, and the principle above
-- stands on the kusudama finding alone.
--
-- What survives from it is `align` below, which is a total order on the representative and is
-- worth having on its own terms. It is a definition this project can use, not an argument.

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

-- ── A fix must not change the answers that were already right ──────────────

/-- The shortest path rule, as it behaves away from the tie: keep `q` when the dot is
    positive and negate it when the dot is negative. This is what `signbit` computes, and
    what `<= 0` computes, wherever the two agree. -/
def shortestPath (ref q : Quat) : Quat :=
  if dot ref q > 0 then q else q.neg

/-- **The fix changes nothing that was already defined.** For every input whose dot is not
    zero, `align` returns exactly what the old rule returned. So the whole neighbourhood of
    working behaviour is preserved, and only the point that had no answer gains one.

    This is the property a degeneracy fix has to have. Without it the change is not a fix, it
    is a different algorithm with a different output on inputs that were never broken. -/
theorem align_agrees_away_from_the_tie (ref q : Quat) (h : dot ref q ≠ 0) :
    align ref q = shortestPath ref q := by
  unfold align shortestPath
  by_cases hp : dot ref q > 0
  · simp [hp]
  · have hn : dot ref q < 0 := by omega
    simp [hp, hn]

/-- And at the tie it differs from both of the old rules, which is the entire change. -/
theorem align_differs_only_at_the_tie :
    align ident halfTurnX ≠ halfTurnX.neg := by decide

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
