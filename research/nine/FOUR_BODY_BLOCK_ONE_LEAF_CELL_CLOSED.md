# C1.4.b1: the entire four-body-block-plus-leaf cell is closed

**Status: complete whole-cell hand assembly; root and two separate independent
assembly audits passed.** In a hypothetical nine-unit-square radius
counterexample, choose a radius minimizer which also minimizes the sum
of squared center norms among all radius minimizers. Work in the
explicit prior-theorem window
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]
Its necessary physical certificate can be chosen so that its positive
component is not a four-body biconnected block with one bridge to a
leaf. This is the entire coarse cell **C1.4.b1**, with five positive
bodies and four other arbitrary physical squares.

All underlying block graphs, both attachment orbits where relevant,
both radial leaf types, every circle-load allocation, every physical
circle-corner mask, all actual contact means and every completion
square are retained. The theorem has the canonical lower-bound scope
stated above. It does not assert that every arbitrary stress on an
original noncanonical equality packing has this exclusion.

## 1. Canonical choice and common certificate

At the least radius, the labeled physical packing space is compact.
The continuous quantity
\[
                         \Phi=\sum_{i=1}^9 |c_i|^2
\]
therefore attains a minimum there. Make this secondary choice before
selecting common point normals or extracting any multipliers. This
remains a radius minimizer, so all the preceding necessary physical
certificate theorems still apply.

Use the existing strictly exposing, nonradial point-normal convention,
matched four-square-junction parameters, physical uncrossing, sparse
positive support and unique-positive-component framework. The finite
compatible generic conditions and the additional strict neighborhoods
needed by the source theorems are imposed before multiplier extraction.
No obtained force is subsequently rotated.

The secondary choice is required by the completed opposite-loaded-pair
C4 theorem. Every other graph and load branch used below is a direct
core exclusion or a completed whole-packing capacity theorem. The
proof does not silently export the canonical motion to arbitrary
packings.

The lower endpoint in (1) is the inherited n=8 input assembled in
`LOWER_WINDOW_FROM_EIGHT.md`. This source neither replaces that input
nor claims to remove its existing arithmetic-table dependencies.

## 2. There are exactly three underlying four-body blocks

The positive pair graph is simple after aggregating atoms for the same
body pair. A biconnected simple graph on four vertices has at least
four edges. With four edges, every vertex has degree two and the graph
is C4. With five edges it is K4 with one edge deleted, the diamond.
With six edges it is K4. These are all possibilities.

The one remaining bridge leads from a block vertex to the fifth body,
which is a leaf. The radial leaf theorem makes this body a radial S or
radial D square and makes its articulation physically circle-clear.
The entire finite graph cover is therefore:

| Positive block | Attachment possibilities | Complete exclusion |
| --- | --- | --- |
| K4 | One vertex orbit | `NO_POSITIVE_K4_SUBGRAPH.md` excludes every such positive subgraph, including its occurrence in this five-body component. |
| Diamond K4 minus one edge | Hub or tip | `DIAMOND_LEAF_BLOCK_CLOSED.md` exhausts both orbits, both leaf types and all physical/load masks. |
| C4 | One vertex orbit | Sections 3--4 below exhaust every cycle load allocation. |

The K4 theorem is for the selected physical planar certificate and
retains arbitrarily small junction routings. The diamond theorem
keeps the correct positive degree three at its second hub; it never
substitutes a degree-two equation there. Their conclusions retain all
four additional squares without moving them.

## 3. Exhaustive load cover for the C4 block

Label the cycle and leaf as
\[
                       A-B-U-C-A,\qquad A-L,
 \tag{2}
\]
with A the articulation. The radial leaf is loaded and A is physically
clear. Only B,U,C can supply other circle load in this component.

If none of B,U,C is loaded, the global circle-force sum has just one
nonzero positive radial leaf vector, impossible. If exactly one is
loaded, the entire component has exactly two loaded bodies, excluded
by `TREE_AND_TWO_LOAD_COMPLETION.md`, Corollary TL. That whole
component theorem retains every other square and applies to cyclic
as well as tree pair graphs.

It remains that exactly two or all three of B,U,C are loaded. Up to
reflection, the following list is exhaustive.

| Positive cycle load set | Complete source | Scope needed here |
| --- | --- | --- |
| B and U, or U and C | `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md` | Direct core exclusion for both radial leaves, every transmitter width, every frame and every actual mean. The zero-load cycle body may still physically touch the circle. |
| B and C | `FOUR_CYCLE_OPPOSITE_LOAD_BRANCH_CLOSED.md` | Complete opposite-pair exclusion at the canonical minimizer. Its physical-mask and owner cover retains every actual channel mean and all four extras. |
| B, U and C | `FOUR_CYCLE_THREE_LOAD_BRANCH_CLOSED.md` | Complete core exclusion for the entire S and D articulation families, every physical mask and all singleton/shared endpoints. No secondary motion is used in this branch. |

A zero individual corner weight never changes a body's physical
one-corner/two-corner classification. Likewise, a circle-touching body
with zero total circle weight remains in every physical contact and
completion premise.

## 4. Why the last three-loaded branch is a whole exclusion

The final row of the table has no remaining continuous parameter or
contact-feature gate. For an S leaf, its articulation is either the
full aligned slider family or the full tilted right-vertex family.
`FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md` and
`FOUR_CYCLE_TILTED_S_ARTICULATION_EXCLUSION.md` exclude those two
complete families using actual boundary-center geometry.

For a D leaf, the articulation is an aligned unit rectangle with its
leaf application in the relative interior of the right side. The
nonparallel cycle reactions are exhausted by the two-left-vertex,
right-vertex, vertical-singleton and vertical-shared-side theorems.
The latter retains its variable mean and selects only strict normals
near permissible axis endpoints before extraction.

For parallel D reactions, opposite horizontal signs are first
excluded by proper concurrence, circle order and global vertical
balance. The two remaining reactions point left at actual opposite-sign
wall heights. Each wall tip is then physically unique-corner. The
complete aligned-tip theorem gives a nonnegative first component for
its outward normal toward U. The complete tilted-tip theorem gives a
strictly positive first component, using the western inner-circle arc
budget and a support screen for every remaining negative-x feature.
Thus U's two outward pair forces have nonpositive first components,
while its positive circle resultant points strictly west. Its
horizontal balance is impossible.

This final argument retains U's entire physical two-corner mask,
including either zero individual corner weight. It does not assume
that U has a common frame with A or either tip, and it does not assume
or add an AU force.

## 5. Preservation of the four extras and final scope

The only branch here using a secondary physical motion is the earlier
opposite-loaded-pair C4 branch. Its source proves that the entire newly
occupied strip is in the empty C4 hole and excludes every completion
square interior from that strip. Hence its translation preserves the
whole nine-square packing while strictly decreasing Phi. This is why
the four completion squares cannot be dropped from that premise.

All newly completed three-loaded and diamond branches instead rule
out the core itself. The two-loaded component theorem is a full
capacity theorem with arbitrary other frames. The K4 exclusion also
keeps every physical square in its routing and winding argument.
Every row therefore applies to the same complete hypothetical packing.

All three block graphs and every C4 load allocation have now been
excluded. The selected necessary certificate at the canonical radius
minimizer has **no C1.4.b1 component**. This is a whole-cell closure,
not merely a list of restricted angle boxes or isolated poses.

The other coarse cyclic cells, larger mixed positive components, the
unrestricted nine-square lower bound and the classification of every
original equality packing require their own completed arguments.
This assembly does not change the status of any such unsolved parent
claim. No Lean compilation, CI or numerical infeasibility assertion is
used or claimed.
