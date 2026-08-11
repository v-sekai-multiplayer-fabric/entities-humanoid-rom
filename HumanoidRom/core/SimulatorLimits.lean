-- SPDX-License-Identifier: MIT
-- Copyright (c) 2026-present K. S. Ernest (iFire) Lee
--
-- What a physics simulator enforces, against what anatomy allows.
--
-- This file records a measurement, not a design. The SOMA humanoid that the pretrained
-- motion trackers were trained against declares every joint as a hinge with the range
-- -180 to 180 degrees. All 66 of them. So the simulator enforces no range of motion at
-- all: a knee may invert, a neck may turn a full circle, and an elbow may fold backwards.
--
-- The measurement, taken from soma23_humanoid.xml with MuJoCo:
--
--     joints 67, limited 66, unlimited 1 (the free root)
--     limited hinge span, degrees: min 360.0, median 360.0, max 360.0
--
-- The consequence reaches the controller. ProtoMotions builds its action range in
-- `build_pd_action_offset_scale`, and for a 3 DOF joint it takes
--
--     scale = min (2 * action_scale * max |limit|) pi
--
-- Every SOMA joint is 3 DOF, and every limit is 180 degrees, so the scale saturates at pi
-- for all 66. A normalised action of 1.0 therefore commands a target of 180 degrees.
--
-- **Do not narrow the simulator limits to the ranges below.** The trained tracker scores
-- 0.9996 against that MJCF, so its actions are calibrated to a pi scale. Narrowing the
-- range changes what an action means and invalidates the weights. The MJCF has the
-- testing hours behind it and this file does not.
--
-- So range of motion belongs on a different seam. It is a validator over motion that a
-- simulator produces or a corpus supplies, and it is not a constraint the simulator holds.
-- A pose that leaves these ranges is a pose to reject or to flag, not one to clamp.

import Shared.Types

namespace PredictiveBVH.SimulatorLimits

/-- Angles are whole degrees. Integers keep every proof here decidable without Mathlib. -/
abbrev Deg := Int

/-- What the SOMA MJCF declares for every one of its 66 hinge joints. -/
def simulatorLimit : Deg := 180

/-- The number of hinge joints in the SOMA humanoid, all of them limited identically. -/
def somaHingeCount : Nat := 66

/-- A one-axis range that anatomy allows, as a closed interval in degrees. -/
structure Range where
  lo : Deg
  hi : Deg
  deriving Repr, DecidableEq

/-- The width of a range, in degrees. -/
def Range.span (r : Range) : Deg := r.hi - r.lo

/-- The width the simulator gives every axis. -/
def simulatorSpan : Deg := 2 * simulatorLimit

-- ── Anatomical ranges, for validation only ─────────────────────────────────
-- These are conventional clinical ranges for a healthy adult. They are here to be
-- compared against, and deliberately not to be installed into any MJCF.

/-- Knee flexion and extension. A knee does not extend past straight. -/
def kneeFlexion : Range := { lo := 0, hi := 140 }

/-- Elbow flexion and extension, likewise bounded at straight. -/
def elbowFlexion : Range := { lo := 0, hi := 145 }

/-- Neck rotation to either side. -/
def neckRotation : Range := { lo := -80, hi := 80 }

/-- Hip flexion and extension, the widest of the four. -/
def hipFlexion : Range := { lo := -20, hi := 120 }

/-- Every range considered here. -/
def surveyed : List Range := [kneeFlexion, elbowFlexion, neckRotation, hipFlexion]

/-- A range is enforced by the simulator only if the simulator is no wider. -/
def enforcedBySimulator (r : Range) : Bool := decide (simulatorSpan ≤ r.span)

-- ── What the measurement proves ────────────────────────────────────────────

/-- The simulator gives every axis a full turn. -/
theorem simulator_span_is_full_turn : simulatorSpan = 360 := by decide

/-- No surveyed range is enforced by the simulator. This is the finding. -/
theorem none_enforced : surveyed.all (fun r => !enforcedBySimulator r) = true := by decide

/-- A knee may invert under the simulator, because zero is interior to its range. -/
theorem knee_may_invert : (-simulatorLimit < kneeFlexion.lo) = true := by decide

/-- Every surveyed range is strictly narrower than what the simulator allows. -/
theorem all_narrower : surveyed.all (fun r => decide (r.span < simulatorSpan)) = true := by
  decide

/-- The action scale saturates for a joint whose limit is the simulator limit. Stated on
    whole degrees: twice the limit is at least a half turn, so the `min` selects pi. -/
theorem action_scale_saturates : (2 * simulatorLimit ≥ 180) = true := by decide

end PredictiveBVH.SimulatorLimits
