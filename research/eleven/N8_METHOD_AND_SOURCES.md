# Lessons from the eight-square proof

The n=11 project follows the staged hand-proof workflow of PR #9 and the
explicit verification boundary of PR #10. Its geometry must be established
afresh. In particular, neither a unique central square nor an exterior cycle
with ten squares is assumed.

## Pinned source record

| Source | Snapshot | Use |
| --- | --- | --- |
| [Repository definitions](https://github.com/vltanh/lean4-squares-in-circles/blob/4bea747b3efa13c869b956cb28435efaf21526fa/SquaresInCircles/Geometry.lean) | main `4bea747` | Independently oriented closed unit squares, open-interior disjointness, nonnegative radius, rotation-only congruence |
| [n=8 consolidated hand proof](https://github.com/vltanh/lean4-squares-in-circles/blob/a21c91f54039e805a637e983bc612bd130f39ee7/research/eight/UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md) | PR #9 `a21c91f` | Geometric extraction before finite classification; original-witness and equality recovery |
| [n=8 formalization roadmap](https://github.com/vltanh/lean4-squares-in-circles/blob/a21c91f54039e805a637e983bc612bd130f39ee7/research/eight/LEAN_FORMALIZATION_ROADMAP.md) | PR #9 `a21c91f` | Explicit contracts, cover obligations, separate verification stages |
| [n=8 table-free hand theorem](https://github.com/vltanh/lean4-squares-in-circles/blob/7c7e6fd1bcd21048876bb7aee3fa47e1f1405d96/research/eight/formalization/HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md) | PR #10 `7c7e6fd` | Recover equality at the original radius and original centers |
| [n=8 canonical handoff](https://github.com/vltanh/lean4-squares-in-circles/blob/7c7e6fd1bcd21048876bb7aee3fa47e1f1405d96/research/eight/formalization/TABLEFREE_HANDOFF_CURRENT.md) | PR #10 `7c7e6fd` | Hand proof, source draft, public assembly, and kernel verification have separate statuses |
| [n=9 deep roadmap](https://github.com/vltanh/lean4-squares-in-circles/blob/102dfaed077fac4965858a67aa1a426af21a7fe7/research/nine/DEEP_GATED_ROADMAP.md) | PR #11 `102dfae` | Conditional coordinate-separable results do not settle unrestricted oblique packings; stressed cores need all physical completions |

These were read through the GitHub connector. The n=9 source is a research
dependency map, not a theorem imported into this work.

## What made the n=8 classification legitimate

Sections 3–6 of the consolidated proof establish the central core, an exterior
boundary reduction preserving signed separating witnesses, forward-axis
restrictions, and frame concentration before deriving discrete quarter words.
The resulting words have length seven, digits in {0,1,2}, sum four, no cyclic
000, and at most one 2. These restrictions give 70 labeled words and seven
dihedral classes. All 128 radial assignments remain in the cover.

Those counts illustrate a proved reduction. They provide no n=11 cover.
For eleven squares there are 55 unordered pairs; even a raw owner cover must
account for independently oriented squares, both signs, all four own axes,
and every weak tie. Any later short class list needs a new coverage proof.

## Rules adopted here

1. State an implication from arbitrary physical Packing to the proposed
   finite signatures before marking a classifier complete. A huge raw finite
   cover and a useful reduced terminal inventory are different gates.
2. Preserve the chosen separator's physical owner, sign, frame, and original
   radius. A deformed necessary system need not remain a physical packing.
3. Use closed domains and weak inequalities for touching configurations.
   Deterministic tie choices must agree everywhere that a witness is reused.
4. Prove terminal inequalities for entire stated continuous domains. Sampling,
   optimizer output, a contact sketch, and successful arithmetic checks are
   discovery or regression evidence, not universal lower bounds.
5. Track unstressed or sliding squares. Equality requires necessity on the
   original configuration and a converse construction for every parameter.
6. Keep one current status table and an append-only checkpoint history. Every
   closure identifies its hypotheses, mathematical output, evidence, and
   remaining dependency. A false proposed reduction gets a counterexample
   record instead of a silent deletion.
7. Hand arguments here are not kernel-verified. Future Lean implementation,
   build, axiom audit, and public integration remain separate later gates.
