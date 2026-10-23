# Ten unit squares in a circle

Research checkpoint: 2026-10-23 (UTC), based on main commit
`4bea747b3efa13c869b956cb28435efaf21526fa`.

**The sharp radius and complete equality family are proved by hand for the
entire common-coordinate-separated class, including independently rotated
squares, and for unrestricted packings with eight square centers at distance
at least `1` from the disk center. The remaining unrestricted cases are OPEN.**
The radius is `R* = 3/√2`, with squared radius `Q = 9/2`. Common-coordinate
separation means that one fixed pair of perpendicular directions separates
every square pair by disjoint projection interiors along at least one of
the directions. This is an additional hypothesis on `Packing`.

This research does not extend the public n≤8 Lean theorems.

Erich Friedman's [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page, consulted on 2026-10-23, lists this n=10 radius and credits the construction
to Friedman (1997). It lists only n=1–8 as proved optimal. The coordinates and
arguments below are derived and checked here; the reference is provenance for
the known bound, not a lower-bound proof.

## What is established here

| Result | Evidence | Scope |
| --- | --- | --- |
| Ten squares fit at `Q = 9/2` | [Exact hand proof](CONSTRUCTION.md), [rational witness](construction.json), [checker](check_construction.py) | Upper bound only |
| Sharp radius and complete six-parameter equality family for all parallel packings | [All-parallel theorem](ALL_PARALLEL_THEOREM.md) | Arbitrary centres; common square orientation |
| Same sharp theorem with independent orientations and common-coordinate separation | [Rectification theorem](COORDINATE_RECTIFICATION.md) | One common orthogonal separating frame |
| Complete physical completion of four anchors | [Anchored equality classification](ANCHORED_EQUALITY_CLASSIFICATION.md) | Remaining six orientations initially unrestricted |
| Three squares in a sharp cap force alignment and boundary anchors | [Three-square cap](THREE_SQUARE_CAP.md) | Arbitrary orientations, all wholly beyond a line at distance `1/2` from the disk centre |
| A square in an outward quadrant forces the sharp corner bound | [Corner rigidity](CORNER_RIGIDITY.md) | Arbitrary orientation |
| At least two squares enter the central disk of radius `1/2` | [Exterior-arc bound](CENTRAL_DISK_REDUCTION.md) | Arbitrary orientations; squared containing radius at most `9/2` |
| Eight exterior squares force four anchors; the exactly-two-central case is closed | [Sharp exterior ring](SHARP_EXTERIOR_RING.md) | Arbitrary orientations; no common separating frame assumed |
| Eight centers outside the open unit disk force four anchors | [Center-radius reduction](CENTER_RADIUS_REDUCTION.md) | Arbitrary orientations; a smaller ten-packing must have exactly 3, 4, or 5 centers in the open unit disk |
| Sharp lower bound from four anchors | [Four-anchor bound](FOUR_ANCHOR_BOUND.md) | Four common-frame squares with the stated coordinate gaps |
| Exact finite formulation and existence of a minimizer | [Unrestricted model](UNRESTRICTED_MODEL.md) | Arbitrary individual orientations; no sharp lower bound |

The earlier [three-column theorem](THREE_COLUMN_THEOREM.md) is retained as a
short special case; the all-parallel theorem removes its column hypothesis.
The [six-parameter family](CONSTRUCTION.md#six-parameter-family) is now proved
exhaustive within the common-coordinate class and within the four-anchor
class. Global exhaustiveness is not proved.

The hand arguments have received separate mathematical review within this
work session. The rational checker certifies the displayed witness; it is
not a premise of the lower-bound proofs. **No n=10 Lean source has been
compiled or kernel-checked.**

![Ten-square construction at squared radius 9/2](construction.svg)

## Roadmap and next obligation

| Gate | Status | Required result |
| --- | --- | --- |
| G0: source and model | Hand argument complete | Use unrestricted `Packing`; preserve boundary contact |
| G1: attaining construction | Hand proof and exact arithmetic check complete | `∃ S : Fin 10 → UnitSquare, Packing S (0,0) (3/√2)` |
| G2: common-coordinate theorem | CLOSED by hand, including equality | All-parallel chain argument, then disk-preserving rectification |
| G3: unrestricted lower bound | OPEN; eight-outer-center case closed | Exclude packings below `9/2` with exactly 3, 4, or 5 centers in `B(0,1)` |
| G4: unrestricted equality necessity | OPEN; eight-outer-center case closed | Exclude or classify equality structures with at least three centers in `B(0,1)` |
| G5: Lean formalization | OPEN | Elaborate proofs, audit axioms, and verify statements against `Packing` |
| G6: public integration | OPEN | Extend the registry and public theorem range only after verification |

The next mathematical task is a lower-bound argument covering configurations
outside the common-coordinate class. The rectification proof preserves
separation because it shrinks each square's bounding box. For a merely
physical packing those bounding boxes can overlap, so that argument does
not supply a global reduction.

The cap and corner theorems give precise unrestricted necessary conditions:
in a hypothetical packing with `q<9/2`, every central open strip of width one
meets at least six squares, and every square meets the union of the two such
perpendicular strips. These conditions have not been shown contradictory.
Finding a sharp cap triple in some frame would close the lower bound, but
no universal cap-extraction theorem is claimed.

The sharp exterior-ring theorem uses the circle of radius
`sqrt(1+1/sqrt(2))`: every square avoiding `B(0,1/2)` occupies an arc of angle
at least `pi/4`. Eight such squares must alternate two equality types and
therefore supply the four anchors. This proves that every hypothetical
ten-square packing below `9/2` has **at least three central squares**. It also
closes the complete equality classification when exactly two are central.

The center-radius strengthening proves the same minimum arc angle whenever
the square's center has norm at least `1`, even if the square intersects
`B(0,1/2)`. Its third possible equality type cannot occur in an eight-arc
ring. Consequently any smaller ten-packing must have at least three centers
in `B(0,1)`; pairwise center distances of at least one bound this count by
five. The precise remaining counts are therefore **3, 4, and 5 inner centers**.

A [rational six-square example](SIX_CENTRAL_SQUARES.md) rules out the shortcut
that at most four or five squares can meet the small disk. It is not a
ten-square packing. The remaining argument must use the interaction between
central and exterior squares; a small central count alone is insufficient.

Even the established equality family can have five distinct x-coordinates;
the all-parallel proof handles those configurations directly. No unproved
three-column normalization is used.

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
python3 research/ten/check_core_obstruction.py
python3 -B research/ten/plot_construction.py
```

The first command checks all 40 vertices and 45 pairs using `Fraction`, identifies
the four tight corners, and rejects deliberately overlapping, exterior, and
floating-point witnesses. Vertex containment implies whole-square containment
by convexity of the disk. The central-obstruction checker verifies six squares,
all 15 separating pairs, and strict near/far distance bounds using rational
arithmetic. The figure uses floating point only for drawing and is not a proof
input.

This checkpoint changes only `research/ten/`. No Lean build, axiom audit,
Comparator run, or external kernel replay is claimed. Commits use `[skip ci]`
for this research-only draft, following the existing research PR convention.
