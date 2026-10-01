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
uniqueness. From three squares on, every case also has `Exterior.lean`, what a
square that avoids the disk centre holds (an arc or a cap of a circle about the
disk centre, or for seven squares a marker and the arc about it), and
`Containing.lean`, what becomes of the square that contains it. Six and seven
squares put the long middle of their proofs in folders: six squares their
normalization, separators, wings, tails, stress bound and equality case
([below](#six)), seven squares the pair theorem in `Pair/`
([below](#seven)). Each case imports only `Common/` and its own folder.

## `Common/`

| File | Contents |
| --- | --- |
| `Basic.lean` | Vector operations and the Cauchy–Schwarz inequality, square frames and vertices, `InteriorDisjoint`, the farthest-vertex bound `phi` and its converse, the centre and the nearest point of a square in a disk, inscribed disks |
| `Tangents.lean` | The tangent identity for `phi`, the lines of the contact polygons |
| `Separation.lean` | Open squares are convex; the Hahn–Banach supporting functional for two squares with disjoint interiors; the projections of a square on a direction |
| `Arcs.lean` | `OpenArc` witnesses on circles about the disk centre; the budget of arcs in disjoint regions; the separation of their centres and the budget of three arcs |
| `Sweep.lean` | The radial sweep of a square stays disjoint from the other squares when every centre is within distance 1 of the disk centre; the budget with a sweep |
| `Charts.lean` | `SquareChart`: membership seen from the disk centre, sorted coordinates, arcs from chart intervals, the half circle of a square with `a = 1/2`; points in a rotated frame and the Cartesian form of a chart |
| `ExteriorCharts.lean` | `ExteriorChart`: the sorted chart of an exterior square in a disk of squared radius `Q`, with its far corner in the disk and its centre within `√(Q - 1/4) - 1/2` of the disk centre; the nearest point of a square in chart coordinates |
| `ExteriorArcs.lean` | Arcs of an exterior square: between its edges, bounded by the four sums `2A`, `A + U`, `A + V`, `U + V`, and the cap on small circles |
| `DiskSupport.lean` | Cauchy–Schwarz on a disk; the support of a square in a disk from its far vertex; the support function of an axis-parallel square and its lower bound from the distance of the centre |
| `Analysis.lean` | Monotonicity and concavity from derivatives, positivity from a curvature bound and one value, the largest value at a peak, leftmost minima |
| `Trigonometry.lean` | Bounds for `π`, `sin`, `cos` and `arcsin`: small angles, Taylor brackets, concave first harmonics, radicals and rotating lengths, half angles |
| `Constructions.lean` | Axis-parallel squares centred at given points: membership, disjointness and containment |
| `Congruence.lean` | Congruence to a model from square-by-square slots; open squares determine closed ones; configurations congruent to a packing are packings; the rigid-motion witness; the square at given coordinates in a rotated frame (`modelSquare`, `orientedSquare`) |
| `Contacts.lean` | Disjoint squares have centres at least 1 apart; at distance exactly 1 they are side-neighbours; squares with parallel sides in one frame |
| `Angles.lean` | `m` directions pairwise at least `g` apart have `mg ≤ 2π`, and form a regular polygon when `mg = 2π`; disjoint half circles are opposite; quarter turns of a frame |
| `SeparatingAxes.lean` | The separating-axis theorem: disjoint squares are separated along one of their four edge axes, each with its threshold; for two oriented squares, the threshold `1/2 + angularWidth d` and the offset of the centres in either frame |
| `Frames.lean` | A square read in another frame (`pullSquare`); packings under a change of frame, a relabelling and the reflection in the diagonal; composing congruences; the frame of a square that contains the disk centre |
| `Optimum.lean` | `Optimum`, the statement every case proves; the lower bound, the least radius and the converse of uniqueness for all cases |

## The cases

| File | One | Two | Three | Four | Five | Six | Seven |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Construction.lean` | the centred square | the 2×1 rectangle | the T | the 2×2 block | the plus | the central square, four neighbours and the turned square | the column packings |
| `Exterior.lean` | | | the 16-gon; caps of at least `120°` on the circle of radius `3/8`, and their two tight types | the diamond; arcs of at least `90°` on the circle of radius `1/2` | the 12-gon; arcs over `72°` on the circle of radius `5/6` | arcs over `60°` on the circle of radius `9/10` | states, labels and markers; the marker arc of half-width `1/2` |
| `Containing.lean` | | | no square contains `o` | a square whose closed square contains `o` holds a quarter circle | the sweep of a square that contains `o` holds `72°`, unless the square is centred at `o` | exactly one square contains `o`; the box of its centre | some square contains `o`; it sits in the middle column |
| `Uniqueness.lean` | centred at `o` | both centres `1/2` from `o`; opposite half circles | caps of exactly `120°`; one square of type A and two of type B rebuild the T | `o` a vertex of every square; a quarter grid of arcs | a square centred at `o`, the others its side-neighbours; closed 12-gon rigidity | the stress bound and the eight contacts rebuild the model | the ring and the middle column; congruence to a column packing |

Each case has a `radius`, its `centers` (the optimal packing in the frame of
its disk centre) and its `model`, the axis-parallel squares at those centres,
all defined in `Geometry.lean`, except six squares, whose model has a turned
square and so no `centers`; its `Construction.lean` proves that the model
packs the disk of that radius. Seven squares instead have the column packings
`columnModel c`, in which each of the three middle squares has its own height;
their `Construction.lean` also defines `centers` and `model`, the column centred
at the disk centre.

## Six

The proof of six squares is uniqueness at the optimal radius
([09-six.md](proof/09-six.md)), in 44 files and about 18,000 lines, most of them
estimates in one variable on whole intervals of angles, in the order of
Chapter 9 and Appendices B to E:

| part | files | contents |
| --- | --- | --- |
| construction | `Constants.lean`, `Construction.lean` | the constants of the model, their identities and rational brackets; the model packs the disk |
| the exterior and the central squares | `Exterior.lean`, `Containing.lean` | the arcs that the exterior squares hold on the circle of radius `9/10`; a square contains the disk centre, and the box of its centre |
| supports | `Supports.lean` | the supports of a chart in the disk of radius `R0`: the cap and the cones; the box of the centre of C |
| normalization | `Normalization/` (8 files) | charts and the separating axes of the central square; squares in a deep cap; the five pins, the labels, their windows and order; `D` separated from the central square along its own axis; normalized packings and the axes of their pairs |
| separators | `Separators/` (9 files) | the axes that separate consecutive squares; the angle of `D` exceeds `1/2`; the profile of `D`; walls, missing wings and the signs of the wings |
| wings | `Wings/` (11 files) | no wing is missing: `D` is separated from `W` and from `S` along their axes, case by case |
| tails | `Tails/West.lean`, `Tails/South.lean` | the angles of `W` and `S` when they are separated along their own axes |
| the stress bound | `Stress/` (6 files) | the pair and diagonal estimates; at the optimal radius the stress forces the angles of the model and its eight contacts |
| equality | `Equality/Contacts.lean`, `Equality/Reflection.lean`, `Uniqueness.lean` | the eight contacts fix every centre; the diagonal reflection; congruence to the model and the optimum |

## Seven

The proof of seven squares is uniqueness at the optimal radius, in five steps
([10-seven.md](proof/10-seven.md)): the states and markers with the marker arc, the
pair theorem, the containing square, the ring of six squares and the middle
column. The pair theorem takes the folder `Pair/` and `Pair.lean`, 17 files in
the order of Chapter 10 and Appendices G to I:

| part | files | contents |
| --- | --- | --- |
| construction | `Construction.lean` | the column packings pack the disk; the four gaps of a column |
| states and markers | `Exterior.lean` | states, labels and markers; the support of an admissible square; the marker arc of half-width `1/2` |
| a pair in one frame | `Pair/Frame.lean`, `Pair/Contacts.lean` | the support sums of a pair in the frame of its first square, and the separating axes of a disjoint pair; contacts |
| the label regions | `Pair/LabelBoundary.lean`, `Pair/LabelSegments.lean`, `Pair/BoundaryProfiles.lean`, `Pair/AxialBoundary.lean` | the boundary of the label regions, segments of constant label, profiles along the boundary, and the target support on the axial boundary |
| the critical gap `π/3` | `Pair/EasySectors.lean`, `Pair/Inward/` (4 files), `Pair/Forward/` (3 files), `Pair/CriticalGap.lean` | the outward, backward, inward and forward axes, sector by sector, with their zeros, and their assembly |
| the smaller gaps | `Pair/SmallerGaps.lean` | leftmost and smooth minima of a support sum; every gap below `π/3` |
| the pair theorem | `Pair.lean` | markers at least `π/3` apart, and contacts at exactly `π/3` |
| the containing square, the ring | `Containing.lean`, `Ring.lean`, `Uniqueness.lean` | a square contains the disk centre and sits in the middle column; the regular hexagon of markers and the ring of six squares; congruence to a column packing, and the optimum |
