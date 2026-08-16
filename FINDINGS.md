# Findings

Moved out of `README.md` when the forty-line rule went in. Each of these is a measurement and
what follows from it, and each names the Lean file that records the measurement itself -- so
the file is the source and this page is the argument, not a second copy of the numbers.

## the simulator enforces no range of motion

`HumanoidRom/core/SimulatorLimits.lean` records a measurement taken from the SOMA humanoid
that the pretrained motion trackers were trained against. Every one of its 66 hinge joints
declares the range -180 to 180 degrees:

    joints 67, limited 66, unlimited 1 (the free root)
    limited hinge span, degrees: min 360.0, median 360.0, max 360.0

So a knee may invert and an elbow may fold backwards, and the simulator raises no objection.
It also sets the controller's action range. ProtoMotions derives a 3 DOF action scale as
`min (2 * action_scale * max |limit|) pi`, every SOMA joint is 3 DOF, and every limit is 180
degrees, so the scale saturates at pi for all 66. A normalised action of 1.0 commands a
target of 180 degrees.

**The MJCF is not changed to match this repository.** The tracker scores 0.9996 against that
file, so its actions are calibrated to a pi scale, and narrowing the ranges would change what
an action means and invalidate the weights. The MJCF has the testing hours and this repository
does not.

Range of motion therefore belongs on a different seam. It validates motion that a simulator
produces or that a corpus supplies. It is not a constraint the simulator holds, and a pose
outside these ranges is one to reject or to flag rather than one to clamp.

## the kusudama flip is a degenerate centroid

`HumanoidRom/core/KusudamaEncoding.lean` records why a kusudama solve flips when three cones
are equidistant, and it is not a race.

`KusudamaSolver` builds the pole of its gnomonic projection by summing every cone centre and
normalising. **Three equidistant cones sum to zero.** Measured in double precision:

    3 equidistant, 120 degrees apart   |sum| = 4.003e-16   degenerate
    4 tetrahedral                      |sum| = 0           degenerate
    2 opposed                          |sum| = 0           degenerate
    3 clustered, asymmetric            |sum| = 2.800       fine

`normalize` of zero is undefined, so the pole follows whatever noise survives the sum.
Perturbing one coordinate by a single unit in the last place moves it from (0, 1, 0) to
(-0.707, 0.707, 0), which is 45 degrees of swing from one bit. That reproduces on one thread,
so it is a discontinuous function evaluated at its discontinuity rather than a race.

The degenerate cases are the well-formed ones. A symmetric limit is what a joint with no
preferred direction has, so the solver failed exactly on the limits an author writes by hand.

**The fix is to stop deriving a pole.** A gnomonic projection is only valid inside a hemisphere
of its pole, so a pole averaged over cones that span more than a hemisphere was wrong before it
was degenerate. Project against the nearest cone instead: it is a real cone centre, so it is a
unit vector by construction and never needs normalising, and ties break by the lower index,
which is a total order and gives the same answer on every machine and in every thread.

The file proves the degeneracy of the opposed and equidistant cases, that an asymmetric case is
fine, and that the nearest cone is defined and deterministic on both degenerate inputs.

## a joint limit is one kusudama, not three ranges

A SOMA joint is three hinges named `_x`, `_y` and `_z`, and an MJCF `range` on each describes a
box. A shoulder is not a box. The reachable set is a region on a sphere, and an arm may reach
far to one side only while it is also low, which a cone sequence says and three ranges cannot.

So 66 scalar limits become 22 kusudamas, one for each joint, each a swing cone sequence with a
twist range.
