# Layout

[Back to the README](../README.md)

```text
SquaresInCircles.lean      the main theorems, for all six cases
Challenge.lean             the statement alone, for the Palomar registry
SquaresInCircles/
├── Geometry.lean          the statement: squares, disks, Packing, Congruent,
│                          the optimal radii and models
├── Common/                tools shared by several cases
├── One/                   n = 1
├── Two/                   n = 2
├── Three/                 n = 3
├── Four/                  n = 4
├── Five/                  n = 5
└── Seven/                 n = 7
```

`Geometry.lean` holds everything the main theorems state, the optimal radius
and the optimal models of every case included, and `Challenge.lean` restates it
word for word, followed by the main theorems with `sorry`. Lean moves the proofs
inside a definition, such as the proof of `Nat.AtLeastTwo 2` behind the real
numeral `2`, into auxiliary lemmas named after the first definition in the file
that needs them, so the two files elaborate to identical definitions only while
every definition stays in one file, in the same order. Edit `Geometry.lean`
only: `scripts/verify-comparator.sh --write` copies its definitions into
`Challenge.lean`. `comparator.json` names
the two theorems that `lake comparator` compares between `Challenge.lean` and
the root module `SquaresInCircles` ([Verification](verification.md)).

Every case folder has the same two core files: `Construction.lean` (the
optimal models pack the disk) and `Uniqueness.lean`, which ends with the
case's `optimum`: the construction, a point of each model on the circle of the
optimal radius and uniqueness, together as an `Optimum`
(`Common/Optimum.lean`). No case proves its own lower bound; `Optimum.lean`
derives it from uniqueness once for all cases. Three, four and five squares add
`Exterior.lean` (the contact polygon, and the arcs of the squares that do not
contain the disk centre), and three and five squares also `Containing.lean`
(the square that does). Seven squares spread the pair theorem, the ring and
the middle column over the files listed [below](#seven). No case imports
another: each imports only `Common/` and its own folder.

## `Common/`

| File | Contents |
| --- | --- |
| `Basic.lean` | Vector operations, square frames and vertices, `InteriorDisjoint`, the farthest-vertex bound `phi`, inscribed disks |
| `Separation.lean` | Open squares are convex; the Hahn–Banach supporting functional for two squares with disjoint interiors |
| `Tangents.lean` | The tangent identity for `phi`; the octagon `P8` |
| `Support.lean` | Octagon support for every normal; the radial sweep stays disjoint from the other squares; a closed square misses a disjoint open one |
| `AngularBudget.lean` | `OpenArc` witnesses on circles about the disk centre, and the Haar-measure budget |
| `ArcMetric.lean` | Midpoint separation of disjoint arcs; circle perimeter inequality; three-arc budget |
| `Charts.lean` | `SquareChart`: membership seen from the disk centre, sorted coordinates, arcs from chart intervals, the half circle of a square with `a = 1/2` |
| `Coordinates.lean` | Points in a rotated frame at the disk centre; a chart in Cartesian coordinates |
| `RectangleArcs.lean` | Arcs of an exterior square: between its edges, and the cap on small circles |
| `ArcBudget.lean` | The budget of a packing: some square avoids the disk centre, and the square that contains it can be replaced by its radial sweep |
| `ElementaryTrig.lean` | Arcsine and cosine estimates with exact rational constants |
| `Constructions.lean` | Axis-parallel squares centred at given points: membership, disjointness and containment |
| `Congruence.lean` | Congruence to a model from square-by-square slots; open squares determine closed ones; configurations congruent to a packing are packings; the rigid-motion witness |
| `Optimum.lean` | `Optimum`, the statement every case proves; the lower bound, the least radius and the converse of uniqueness for all cases |
| `Angles.lean` | `m` directions pairwise at least `2π/m` apart form a regular polygon; disjoint half circles are opposite; quarter turns of a frame |
| `Contacts.lean` | Disjoint squares have centres at least 1 apart; at distance exactly 1 they are side-neighbours; squares with parallel sides in one frame |

## The cases

| File | One | Two | Three | Four | Five | Seven |
| --- | --- | --- | --- | --- | --- | --- |
| `Construction.lean` | the centred square | the 2×1 rectangle | the T | the 2×2 block | the plus | the column packings |
| `Exterior.lean` | | | the 16-gon; caps of at least `120°` on the circle of radius `3/8`, and their two tight types | the diamond; arcs of at least `90°` on the circle of radius `1/2` | the 12-gon; arcs over `72°` on the circle of radius `5/6` | |
| `Containing.lean` | | | no square contains `o` | | the sweep of a square that contains `o` holds `72°`, unless the square is centred at `o` | |
| `Uniqueness.lean` | centred at `o` | both centres `1/2` from `o`; opposite half circles | caps of exactly `120°`; one square of type A and two of type B rebuild the T | `o` a vertex of every square; a quarter grid of arcs | a square centred at `o`, the others its side-neighbours; closed 12-gon rigidity | a square contains `o`; the ring and the middle column; congruence to a column packing |

Each case has a `radius`, its `centers` (the optimal packing in the frame of
its disk centre) and its `model`, the axis-parallel squares at those centres,
all defined in `Geometry.lean`; its `Construction.lean` proves that the model
packs the disk of that radius. Seven squares instead have the column packings
`columnModel c`, in which each of the three middle squares has its own height;
their `Construction.lean` also defines `centers` and `model`, the column centred
at the disk centre.

## Seven

The proof of seven squares is uniqueness at the optimal radius, in five steps
([seven.md](proof/seven.md)). Steps 1 to 3, the states and markers, the marker
arc and the pair theorem, take 24 files beside `Construction.lean`; steps 4 and
5, the ring of six squares and the middle column, take `Uniqueness.lean` and
the 2 files in `Seven/Uniqueness/`:

| part | files | contents |
| --- | --- | --- |
| construction | `Construction.lean` | the column packings pack the disk; the four gaps of a column |
| states and markers | `Labels.lean`, `Support.lean`, `PairModel.lean` | states, labels and markers; the support function; the support sums of a canonical pair |
| the marker arc | `Analysis.lean`, `MarkerArc.lean` | monotonicity, curvature, Taylor and Bernstein bounds in one variable; the arc of half-width `801/1600` |
| tools for the sectors | `Contacts.lean`, `LabelBoundary.lean`, `BoundarySegments.lean`, `BoundaryProfiles.lean`, `TargetBoundaryMonotonicity.lean` | contacts; the boundary of the label regions, segments of constant label, and profiles along the boundary |
| the gap of `π/3` | `EasySectors.lean`, `InwardAxialTarget.lean`, `InwardSideTarget.lean`, `InwardOppositeMinima.lean`, `InwardOpposite.lean`, `ForwardNegativeTarget.lean`, `ForwardBothNegative.lean`, `OppositeForward.lean`, `FixedGap.lean` | the outward, backward, inward and forward axes, sector by sector, with their zeros, and their assembly |
| all gaps | `SmoothMinima.lean`, `AllGaps.lean` | leftmost and smooth minima of a support sum; every gap below `π/3` |
| the pair theorem | `SeparatingAxes.lean`, `CanonicalPair.lean`, `MarkerSeparation.lean` | the separating-axis theorem; canonical pairs; markers at least `π/3` apart, and contacts at exactly `π/3` |
| the ring and the middle column | `Uniqueness/ContactCycle.lean`, `Uniqueness/CentralSquare.lean`, `Uniqueness.lean` | the regular hexagon of markers and the ring of six squares; the square in the middle; a square contains the disk centre, congruence to a column packing, and the optimum |
