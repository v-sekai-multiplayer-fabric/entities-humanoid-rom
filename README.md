# lean-humanoid-rom

Humanoid range-of-motion / IK-constraint hexagon: ROM math, Kusudama, muscle/prismatic constraints (core); B3D/AddBiomechanics parsers + GPU shader + python tools (adapters). See `CITATIONS.bib` for the body-model / biomechanics / IK references.

> Split out of the [`lean-predictive-bvh`](https://github.com/v-sekai-multiplayer-fabric/lean-predictive-bvh) monorepo (now archived). Each hexagon cluster is its own repo following the `core/ports/adapters` convention; cross-cluster wiring is via Lake `require ... from git`.

## Dependencies

- [`lean-shared-core`](v-sekai-multiplayer-fabric/lean-shared-core) — common primitive types
- [`LeanSlang`](https://github.com/V-Sekai-fire/lean-slang) — Slang/HLSL AST for the Kusudama shader (pure-Lean use; no FFI link)

## Build

```sh
lake build         # production gate: typecheck the  cluster
lake build Research  # research-tier (non-gating; may fail)
```

## Hexagon layout

- `core/` — dependency-free domain logic + proofs
- `ports/` — narrow driving (source) / driven (sink) contracts
- `adapters/` — concrete I/O at the edges

## Remark: the simulator enforces no range of motion

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
