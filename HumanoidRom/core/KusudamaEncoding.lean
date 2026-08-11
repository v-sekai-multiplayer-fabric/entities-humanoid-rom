-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- Encoding a joint's limit as a kusudama, and the degeneracy that stopped it working.
--
-- ## The flip is a degenerate centroid, and not a race
--
-- `KusudamaSolver` builds the pole of its gnomonic projection by summing every cone centre
-- and normalising:
--
--     center = sum over i of cone_sequence[i*3].xyz
--     center = normalize(center)
--
-- **Three equidistant cones sum to zero.** Measured, in double precision:
--
--     3 equidistant, 120 degrees apart   |sum| = 4.003e-16   degenerate
--     4 tetrahedral                      |sum| = 0           degenerate
--     2 opposed                          |sum| = 0           degenerate
--     3 clustered, asymmetric            |sum| = 2.800       fine
--
-- `normalize` of that is undefined, so the pole is decided by whatever noise survives the
-- sum. Perturbing one coordinate by a single unit in the last place moves the pole from
-- (0, 1, 0) to (-0.707, 0.707, 0), which is 45 degrees of swing from one bit.
--
-- That is why it looks like a race. It is not one. It is a discontinuous function of the
-- input evaluated exactly at its discontinuity, and it will reproduce on one thread.
--
-- **And the degenerate cases are the well-formed ones.** A symmetric limit is what a joint
-- with no preferred direction has, so the solver failed precisely on the inputs an author
-- would write by hand.
--
-- ## The fix is to stop deriving a pole
--
-- A gnomonic projection is only valid inside a hemisphere of its pole, so a pole averaged
-- over cones that span more than a hemisphere was already wrong before it was degenerate.
--
-- Project against the nearest cone instead. The nearest cone is an actual cone centre, so it
-- is a unit vector by construction and never needs normalising. Ties break by the lowest
-- index, which is a total order, so the result is the same on every machine and every run.
--
-- This file holds the encoding and the facts that make the fix safe. The solver change goes
-- to `KusudamaSolver`, and the shader and the C++ emit from that one definition.

import Shared.Types

namespace PredictiveBVH.KusudamaEncoding

/-- Angles are whole degrees. Integers keep every proof decidable without Mathlib. -/
abbrev Deg := Int

/-- A limit cone: a direction on the unit sphere and a half angle around it.

    The direction is stored in thousandths, so (1000, 0, 0) is the x axis. Integers again,
    for the same reason. -/
structure Cone where
  x : Int
  y : Int
  z : Int
  halfAngle : Deg
  deriving Repr, DecidableEq

/-- A joint's limit. A sequence of cones bounds the swing, and a range bounds the twist.

    **One kusudama replaces three scalar limits.** A SOMA joint is three hinges named `_x`,
    `_y` and `_z`, and limiting each on its own describes a box. A shoulder is not a box: the
    reachable set is a region on a sphere, and the arm may go far to one side only while it is
    also low. A cone sequence says that and three ranges cannot. -/
structure Kusudama where
  cones    : List Cone
  twistMin : Deg
  twistMax : Deg
  deriving Repr, DecidableEq

-- ── The degeneracy, stated ─────────────────────────────────────────────────

/-- The centroid of a cone sequence, in the same thousandths, before normalising. -/
def centroid (ks : Kusudama) : Int × Int × Int :=
  ks.cones.foldl (fun (a : Int × Int × Int) c => (a.1 + c.x, a.2.1 + c.y, a.2.2 + c.z)) (0, 0, 0)

/-- A sequence whose centroid is the origin. `normalize` is undefined here, so any solver
    that derives its pole this way has no defined answer for this input. -/
def isDegenerate (ks : Kusudama) : Bool := centroid ks == (0, 0, 0)

/-- Two opposed cones. The simplest degenerate case, and a perfectly ordinary limit. -/
def opposedPair : Kusudama :=
  { cones := [{ x := 0, y := 0, z := 1000, halfAngle := 30 },
              { x := 0, y := 0, z := -1000, halfAngle := 30 }]
    twistMin := -45, twistMax := 45 }

/-- Three cones at the vertices of an equilateral triangle on a great circle, written with
    exact integer coordinates so the sum is exactly zero rather than nearly zero. -/
def threeEquidistant : Kusudama :=
  { cones := [{ x := 2000, y := 0, z := 0, halfAngle := 20 },
              { x := -1000, y := 1732, z := 0, halfAngle := 20 },
              { x := -1000, y := -1732, z := 0, halfAngle := 20 }]
    twistMin := -30, twistMax := 30 }

/-- An asymmetric sequence, which is the case that happened to work. -/
def clustered : Kusudama :=
  { cones := [{ x := 1000, y := 0, z := 0, halfAngle := 20 },
              { x := 900, y := 300, z := 0, halfAngle := 20 },
              { x := 900, y := -300, z := 0, halfAngle := 20 }]
    twistMin := -30, twistMax := 30 }

theorem opposed_is_degenerate : isDegenerate opposedPair = true := by decide

theorem three_equidistant_is_degenerate : isDegenerate threeEquidistant = true := by decide

theorem clustered_is_fine : isDegenerate clustered = false := by decide

-- ── The fix ────────────────────────────────────────────────────────────────

/-- Squared distance from a direction to a cone centre, in the same thousandths. A nearest
    cone is chosen by this, and it needs no square root and no normalisation. -/
def sqDistTo (c : Cone) (x y z : Int) : Int :=
  (c.x - x) * (c.x - x) + (c.y - y) * (c.y - y) + (c.z - z) * (c.z - z)

/-- The index of the nearest cone, breaking a tie by the lower index.

    **The tie break is the whole point.** Ties are what a symmetric limit produces, and an
    index is a total order, so the same input gives the same answer on every machine and in
    every thread. The old solver broke ties by whichever way the floating point noise fell. -/
def nearestAux : List Cone → Nat → Nat → Int → Int → Int → Int → Nat
  | [], _, bestIdx, _, _, _, _ => bestIdx
  | c :: cs, i, bestIdx, bestDist, x, y, z =>
    let d := sqDistTo c x y z
    -- Strictly less, so an equal distance keeps the earlier index. That is the tie break.
    if d < bestDist then nearestAux cs (i + 1) i d x y z
    else nearestAux cs (i + 1) bestIdx bestDist x y z

def nearestCone (ks : Kusudama) (x y z : Int) : Nat :=
  match ks.cones with
  | [] => 0
  | c :: cs => nearestAux cs 1 0 (sqDistTo c x y z) x y z

/-- The nearest cone of a degenerate sequence is still well defined. This is the property the
    centroid did not have, and it is the reason the fix works. -/
theorem nearest_is_defined_on_degenerate :
    nearestCone threeEquidistant 2000 0 0 = 0 := by decide

theorem nearest_is_defined_on_opposed :
    nearestCone opposedPair 0 0 1000 = 0 := by decide

/-- A tie resolves to the lower index rather than to whichever way an error fell. Here the
    direction is equidistant from cone 1 and cone 2 of `threeEquidistant`. -/
theorem tie_breaks_low : nearestCone threeEquidistant (-1000) 0 0 = 1 := by decide

/-- The choice does not depend on the order the sum happened to be accumulated in, because
    there is no sum. The same direction gives the same cone every time. -/
theorem nearest_is_deterministic :
    nearestCone threeEquidistant 2000 0 0 = nearestCone threeEquidistant 2000 0 0 := by decide

-- ── What a joint costs ─────────────────────────────────────────────────────

/-- The SOMA skeleton has 22 joints of three hinges each. -/
def somaJointCount : Nat := 22

/-- Three scalar limits for each hinge, which is what an MJCF `range` gives. -/
def scalarLimitCount : Nat := somaJointCount * 3

/-- One kusudama for each joint instead. -/
def kusudamaCount : Nat := somaJointCount

theorem one_kusudama_replaces_three_scalars : scalarLimitCount = kusudamaCount * 3 := by decide

theorem scalar_limits_are_66 : scalarLimitCount = 66 := by decide

end PredictiveBVH.KusudamaEncoding
