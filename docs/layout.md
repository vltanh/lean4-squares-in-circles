# Layout

[Back to the README](../README.md)

```text
SquaresInCircles.lean      the main theorems, for all seven cases
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
├── Six/                   n = 6
└── Seven/                 n = 7
```

`Geometry.lean` holds everything the main theorems state, including every
case's optimal radius and models. `Challenge.lean` restates it word for word
and states the main theorems with `sorry`; `comparator.json` has
`lake comparator` check them against the root module
([Verification](verification.md)). The definitions must stay in one file, in
one order: Lean names the auxiliary lemmas inside a definition, such as the
proof of `Nat.AtLeastTwo 2` behind the real numeral `2`, after the first
definition in the file that needs them. Edit `Geometry.lean` only;
`scripts/verify-comparator.sh --write` copies its definitions into
`Challenge.lean`.

Every case folder has two core files: `Construction.lean` (the models pack the
disk) and `Uniqueness.lean`, which ends with the case's `optimum`, an `Optimum`
(`Common/Optimum.lean`) bundling the construction, a point of each model on the
circle, and uniqueness; `Optimum.lean` derives every lower bound from
uniqueness. Three to five squares add `Exterior.lean` (the contact polygon, and
the arcs of the squares that avoid the disk centre) and `Containing.lean` (the
square that contains it). Six squares spread their
normalization, separators and estimates over the files [below](#six), and seven
squares the pair theorem, the ring and the middle column over the files
[below](#seven). Each case imports only `Common/` and its own folder.

## `Common/`

| File | Contents |
| --- | --- |
| `Basic.lean` | Vector operations and the Cauchy–Schwarz inequality, square frames and vertices, `InteriorDisjoint`, the farthest-vertex bound `phi` and its converse, the centre and the nearest point of a square in a disk, inscribed disks |
| `Separation.lean` | Open squares are convex; the Hahn–Banach supporting functional for two squares with disjoint interiors |
| `Tangents.lean` | The tangent identity for `phi` |
| `Support.lean` | The radial sweep stays disjoint from the other squares when every centre is within distance 1 of the disk centre; a closed square misses a disjoint open one |
| `AngularBudget.lean` | `OpenArc` witnesses on circles about the disk centre, and the Haar-measure budget |
| `ArcMetric.lean` | Midpoint separation of disjoint arcs; circle perimeter inequality; three-arc budget |
| `Charts.lean` | `SquareChart`: membership seen from the disk centre, sorted coordinates, arcs from chart intervals, the half circle of a square with `a = 1/2` |
| `Coordinates.lean` | Points in a rotated frame at the disk centre; a chart in Cartesian coordinates |
| `ExteriorCharts.lean` | `ExteriorChart`: the sorted chart of an exterior square in a disk of squared radius `Q`, with its far corner in the disk and its centre within `√(Q - 1/4) - 1/2` of the disk centre; the nearest point of a square in chart coordinates |
| `RectangleArcs.lean` | Arcs of an exterior square: between its edges, bounded by the four sums `2A`, `A + U`, `A + V`, `U + V`, and the cap on small circles |
| `ArcBudget.lean` | The budget of a packing: some square avoids the disk centre, and the square that contains it can be replaced by its radial sweep |
| `Analysis.lean` | Monotonicity and concavity from derivatives, positivity from a curvature bound and one value, the largest value at a peak, leftmost minima |
| `Trigonometry.lean` | Bounds for `π`, `sin`, `cos` and `arcsin`: small angles, Taylor brackets, concave first harmonics, radicals and rotating lengths, half angles |
| `SeparatingAxes.lean` | The separating-axis theorem: disjoint squares are separated along one of their four edge axes, each with its threshold; for two oriented squares, the threshold `1/2 + angularWidth d` and the offset of the centres in either frame |
| `Constructions.lean` | Axis-parallel squares centred at given points: membership, disjointness and containment |
| `Congruence.lean` | Congruence to a model from square-by-square slots; open squares determine closed ones; configurations congruent to a packing are packings; the rigid-motion witness; the square at given coordinates in a rotated frame (`modelSquare`, `orientedSquare`) |
| `Optimum.lean` | `Optimum`, the statement every case proves; the lower bound, the least radius and the converse of uniqueness for all cases |
| `Angles.lean` | `m` directions pairwise at least `g` apart have `mg ≤ 2π`, and form a regular polygon when `mg = 2π`; disjoint half circles are opposite; quarter turns of a frame |
| `Contacts.lean` | Disjoint squares have centres at least 1 apart; at distance exactly 1 they are side-neighbours; squares with parallel sides in one frame |
| `Frames.lean` | A square read in another frame (`pullSquare`); packings under a change of frame, a relabelling and the reflection in the diagonal; composing congruences; the frame of a square that contains the disk centre |

## The cases

| File | One | Two | Three | Four | Five | Seven |
| --- | --- | --- | --- | --- | --- | --- |
| `Construction.lean` | the centred square | the 2×1 rectangle | the T | the 2×2 block | the plus | the column packings |
| `Exterior.lean` | | | the 16-gon; caps of at least `120°` on the circle of radius `3/8`, and their two tight types | the diamond; arcs of at least `90°` on the circle of radius `1/2` | the 12-gon; arcs over `72°` on the circle of radius `5/6` | |
| `Containing.lean` | | | no square contains `o` | a square whose closed square contains `o` holds a quarter circle | the sweep of a square that contains `o` holds `72°`, unless the square is centred at `o` | |
| `Uniqueness.lean` | centred at `o` | both centres `1/2` from `o`; opposite half circles | caps of exactly `120°`; one square of type A and two of type B rebuild the T | `o` a vertex of every square; a quarter grid of arcs | a square centred at `o`, the others its side-neighbours; closed 12-gon rigidity | a square contains `o`; the ring and the middle column; congruence to a column packing |

Each case has a `radius`, its `centers` (the optimal packing in the frame of
its disk centre) and its `model`, the axis-parallel squares at those centres,
all defined in `Geometry.lean`, except six squares, whose model has a turned
square and so no `centers`; its `Construction.lean` proves that the model
packs the disk of that radius. Seven squares instead have the column packings
`columnModel c`, in which each of the three middle squares has its own height;
their `Construction.lean` also defines `centers` and `model`, the column centred
at the disk centre.

## Six

The proof of six squares is uniqueness at the optimal radius, in 43 files and
about 19,000 lines, most of them estimates in one variable on whole intervals
of angles:

| part | files | contents |
| --- | --- | --- |
| construction | `Constants.lean`, `Construction.lean` | the constants of the model, their identities and rational brackets; the model packs the disk |
| tools | `Supports.lean` | the support of a square in the disk |
| the central square | `Normalization/CentralSquare.lean` | a square contains the disk centre, by the arcs that the other squares hold on the circle of radius `9/10`; the box of its centre |
| normalization | the other 8 files of `Normalization/` | charts and the separating axes of the central square; squares in a deep cap; the five pins, the labels, their windows and order; `D` separated from the central square along its own axis; normalized packings and the axes of their pairs |
| separators | `Separators/` (9 files) | the axes that separate consecutive squares; the angle of `D` exceeds `1/2`; the profile of `D`; walls, missing wings and the signs of the wings |
| wings | `Wings/` (11 files) | no wing is missing: `D` is separated from `W` and from `S` along their axes, case by case |
| tails | `Tails/West.lean`, `Tails/South.lean` | the angles of `W` and `S` when they are separated along their own axes |
| the stress bound | `Stress/` (6 files) | the pair and diagonal estimates; at the optimal radius the stress forces the angles of the model and its eight contacts |
| equality | `Equality/Contacts.lean`, `Equality/Reflection.lean`, `Uniqueness.lean` | the eight contacts fix every centre; the diagonal reflection; congruence to the model and the optimum |

## Seven

The proof of seven squares is uniqueness at the optimal radius, in five steps
([seven.md](proof/seven.md)). Steps 1 to 3, the states and markers, the marker
arc and the pair theorem, take 22 files beside `Construction.lean`; steps 4 and
5, the ring of six squares and the middle column, take `Uniqueness.lean` and
the 2 files in `Seven/Uniqueness/`:

| part | files | contents |
| --- | --- | --- |
| construction | `Construction.lean` | the column packings pack the disk; the four gaps of a column |
| states and markers | `Labels.lean`, `Support.lean`, `PairModel.lean` | states, labels and markers; the support function; the support sums of a canonical pair |
| the marker arc | `MarkerArc.lean` | the arc of half-width `1/2` |
| tools for the sectors | `Contacts.lean`, `LabelBoundary.lean`, `BoundarySegments.lean`, `BoundaryProfiles.lean`, `TargetBoundaryMonotonicity.lean` | contacts; the boundary of the label regions, segments of constant label, and profiles along the boundary |
| the gap of `π/3` | `EasySectors.lean`, `InwardAxialTarget.lean`, `InwardSideTarget.lean`, `InwardOppositeMinima.lean`, `InwardOpposite.lean`, `ForwardNegativeTarget.lean`, `ForwardBothNegative.lean`, `OppositeForward.lean`, `FixedGap.lean` | the outward, backward, inward and forward axes, sector by sector, with their zeros, and their assembly |
| all gaps | `SmoothMinima.lean`, `AllGaps.lean` | leftmost and smooth minima of a support sum; every gap below `π/3` |
| the pair theorem | `CanonicalPair.lean`, `MarkerSeparation.lean` | canonical pairs; markers at least `π/3` apart, and contacts at exactly `π/3` |
| the ring and the middle column | `Uniqueness/ContactCycle.lean`, `Uniqueness/CentralSquare.lean`, `Uniqueness.lean` | the regular hexagon of markers and the ring of six squares; the square in the middle; a square contains the disk centre, congruence to a column packing, and the optimum |
