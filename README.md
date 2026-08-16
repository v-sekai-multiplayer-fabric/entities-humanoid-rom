# entities-humanoid-rom

Humanoid range-of-motion and IK-constraint hexagon: ROM math, Kusudama, muscle and prismatic constraints (core); B3D/AddBiomechanics parsers, a GPU shader and python tools (adapters). See `CITATIONS.bib` for the body-model, biomechanics and IK references.

> Split out of the [`lean-predictive-bvh`](https://github.com/v-sekai-multiplayer-fabric/lean-predictive-bvh) monorepo (now archived). Each hexagon cluster is its own repository following the `core/ports/adapters` convention; cross-cluster wiring is via Lake `require ... from git`.

## Dependencies

- [`entities-lean-shared`](https://github.com/v-sekai-multiplayer-fabric/entities-lean-shared) — common primitive types
- [`LeanSlang`](https://github.com/V-Sekai-fire/lean-slang) — Slang/HLSL AST for the Kusudama shader (pure-Lean use; no FFI link)

## Build

```sh
lake build           # production gate: typecheck the cluster
lake build Research  # research-tier (non-gating; may fail)
```

## Hexagon layout

- `core/` — dependency-free domain logic and proofs
- `ports/` — narrow driving (source) and driven (sink) contracts
- `adapters/` — concrete I/O at the edges

## Findings

`FINDINGS.md` carries three, each with the Lean file that records its measurement:

- **The simulator enforces no range of motion.** All 66 SOMA hinge joints declare -180 to 180 degrees, so a knee may invert and the simulator raises no objection. The MJCF is not changed to match this repository, and the reason is in the file.
- **The kusudama flip is a degenerate centroid, not a race.** Three equidistant cones sum to zero, and one unit in the last place moves the derived pole by 45 degrees. The fix is to stop deriving a pole.
- **A joint limit is one kusudama, not three ranges.** A shoulder's reachable set is a region on a sphere, so 66 scalar limits become 22 kusudamas.
