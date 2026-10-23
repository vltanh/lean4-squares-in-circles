# Ten unit squares in a circle

Research checkpoint: 2026-10-23 (UTC), based on main commit
`4bea747b3efa13c869b956cb28435efaf21526fa`.

**Unrestricted optimality and equality classification are OPEN.** The proposed
sharp radius is `R* = 3/√2`, with squared radius `Q = 9/2`. This directory starts
the n=10 work; it does not extend the public n≤8 Lean theorems.

Erich Friedman's [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page, consulted on 2026-10-23, lists this n=10 radius and credits the construction
to Friedman (1997). It lists only n=1–8 as proved optimal. The coordinates and
arguments below are derived and checked here; the reference is provenance for
the known bound, not a lower-bound proof.

## What is established here

| Result | Evidence | Scope |
| --- | --- | --- |
| Ten squares fit at `Q = 9/2` | [Exact hand proof](CONSTRUCTION.md), [rational witness](construction.json), [checker](check_construction.py) | Upper bound only |
| A six-parameter family fits at the same radius | [Construction family](CONSTRUCTION.md#six-parameter-family) | Sufficient family; not exhaustive |
| Sharp radius and equality for at most three columns | [Three-column theorem](THREE_COLUMN_THEOREM.md) | Common square orientation; lines parallel to an edge axis |
| Sharp lower bound from four anchors | [Four-anchor bound](FOUR_ANCHOR_BOUND.md) | Four common-frame squares with the stated coordinate gaps |
| Exact finite formulation and existence of a minimizer | [Unrestricted model](UNRESTRICTED_MODEL.md) | Arbitrary individual orientations; no sharp lower bound |

The hand arguments have received a separate mathematical review in this work
session. The rational checker certifies the displayed witness. **No n=10 Lean
source has been compiled or kernel-checked.**

![Ten-square construction at squared radius 9/2](construction.svg)

## Roadmap and next obligation

| Gate | Status | Required result |
| --- | --- | --- |
| G0: source and model | Hand argument complete | Use unrestricted `Packing`; preserve boundary contact |
| G1: attaining construction | Hand proof and exact arithmetic check complete | `∃ S : Fin 10 → UnitSquare, Packing S (0,0) (3/√2)` |
| G2: restricted geometry | Three-column theorem and four-anchor bound complete by hand | Derive exhaustive structure from arbitrary `Packing` |
| G3: unrestricted lower bound | OPEN | Every unrestricted packing has `R² ≥ 9/2` |
| G4: equality necessity | OPEN | Classify all packings at `R² = 9/2`, including translations of individual squares |
| G5: Lean formalization | OPEN | Elaborate proofs, audit axioms, and verify statements against `Packing` |
| G6: public integration | OPEN | Extend the registry and public theorem range only after verification |

The next mathematical task is a lower-bound argument covering configurations
outside the three-column class. Even the explicit family here can have five
distinct x-coordinates. A reduction to three columns would therefore need to
preserve radius and explain its effect on equality; it cannot simply assert that
every equality packing already has three columns. The general all-parallel
case and configurations with independently rotated squares both remain open
in this work.

For the eventual Lean construction, the existing
[`Common/Constructions.lean`](../../SquaresInCircles/Common/Constructions.lean)
provides `axis_packing`. The new witness can be defined in a separate n=10 module
without changing `optimalRadius`, whose value at 10 is currently a placeholder.
The unrestricted formulation uses the interfaces of
[`Geometry.lean`](../../SquaresInCircles/Geometry.lean) and
[`Common/SeparatingAxes.lean`](../../SquaresInCircles/Common/SeparatingAxes.lean).

## Reproduce the checks

From the repository root, with Python 3 and no external packages:

```sh
python3 research/ten/check_construction.py --self-test
python3 -B research/ten/plot_construction.py
```

The first command checks all 40 vertices and 45 pairs using `Fraction`, identifies
the four tight corners, and rejects deliberately overlapping, exterior, and
floating-point witnesses. Vertex containment implies whole-square containment
by convexity of the disk. The figure uses floating point only for drawing and
is not a proof input.

This checkpoint changes only `research/ten/`. No Lean build, axiom audit,
Comparator run, or external kernel replay is claimed. Commits use `[skip ci]`
for this research-only draft, following the existing research PR convention.
