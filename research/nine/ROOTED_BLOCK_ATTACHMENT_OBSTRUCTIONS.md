# Whole rooted block attachments excluded by their unchanged local degrees

**Status: complete hand structural implications; root and separate
independent full hand audits passed.** Work with the same compatible
selected physical certificate in
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Additional positive forces at the stated attachment root are retained.
The assertions below need the exact positive degrees explicitly listed
at the other vertices. They do not apply a whole smaller-component
theorem to a block after deleting its external forces.

## 1. Two local facts with their exact premises

An unloaded body of exact positive degree two has opposite positive
pair forces. Its two neighbors lie beyond its opposite supporting
lines, whose gap is the strictly positive square width. Consequently
those two neighbors cannot physically touch. In particular, an exact
degree-two tip of an actual contact triangle must have positive circle
load.

NO_UNLOADED_DIAMOND_HUB.md gives a second, radius-free fact for the
selected certificate: the three physical neighbors of an unloaded
body of exact positive degree three induce at most one physical edge.
If two such neighbor edges are present, that body has positive circle
load. No load or degree assumption is imposed on those neighbors.

Every loaded body physically touches the circle. The full physical
circle-touching graph is a path forest in (1), by the boundary cycle
and C7 capacity-one results. In particular it has no physical triangle
or four-cycle. We also use NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md:
two distinct physical bodies cannot have three common selected
positive circle-touching neighbors.

## 2. A diamond attached only through one tip is impossible

Let H,K be the diamond hubs, and A,U its tips. Its five positive
edges are
\[
                         HK,\ HA,\ HU,\ KA,\ KU.
\tag{2}
\]
Allow arbitrary further positive neighbors at A. Require that H,K
retain their exact positive degree three and U its exact positive
degree two. No premise is imposed on A's circle mask, load, degree,
or the graph beyond A.

At H, the other hub K physically touches both A and U. Its three
neighbors therefore have the two edges KA and KU. The degree-three
fact forces H to be loaded. Interchanging H,K forces K to be loaded.
The neighbors H,K of U physically touch, so the degree-two fact
forces U to be loaded as well.

Thus H,K,U are three physical circle-touching bodies with all three
pair contacts HK,HU,KU. This is a forbidden physical boundary triangle.
The entire stated rooted diamond domain is impossible.

The distinction between a tip and a hub is essential. If extra forces
attach at a hub instead, the opposite hub and the two tips induce a
path, not a triangle. This argument makes no exclusion of that domain.

## 3. A three-page book attached only through a hub is impossible

Let H,K be the book hubs with positive edge HK and let T1,T2,T3
be the three page tips. Each Ti has exactly the two positive neighbors
H,K. Allow arbitrary additional positive neighbors at H or K, or both.
The tips must retain those exact degree-two neighborhoods.

Each Ti is loaded by Section1, since H,K physically touch. Hence
H,K have three distinct common positive circle-touching neighbors.
NO_THREE_BOUNDARY_COMMON_NEIGHBORS.md excludes this entire domain.
No equation at either hub has been simplified or discarded.

## 4. A four-rim wheel attached only through its hub is impossible

Let H be the wheel hub and let A0,A1,A2,A3 form its positive rim
four-cycle, with each Ai also joined positively to H. Allow arbitrary
additional positive neighbors at H. Each Ai retains exact positive
degree three with neighborhood
\[
                         \{H,A_{i-1},A_{i+1}\},
\tag{3}
\]
where indices are taken modulo four.

The hub physically touches both of the other two neighbors in (3).
Section1 therefore forces every rim vertex to be loaded. Their four
rim edges are a physical boundary four-cycle, a contradiction. This
excludes the full hub-rooted wheel, independently of H's true number
of forces and of all circle masks at the rim.

## 5. Five complete six-body attachment exits

Apply these three uniform implications to the exhaustive cover in
SIX_BODY_CYCLIC_FRONTIER.md. In each case all three extra physical
squares remain arbitrary and fixed.

| Coarse row | Entire attachment now excluded | Exact reason |
| --- | --- | --- |
| C1.4.b2 | Diamond with a length-two bridge arm at a tip | Only that tip acquires further positive edges; Section2 |
| C1.4.b2 | Diamond with two leaves at the same tip | Both additional positive forces stay at that tip; Section2 |
| C1.5.b1 | Three-page book with its leaf at a hub | All three page tips retain degree two; Section3 |
| C1.5.b1 | Four-rim wheel with its leaf at the hub | All four rim vertices retain degree three; Section4 |
| C2.34.b0 | Triangle and diamond meeting at a diamond tip | All extra triangle edges meet that tip; Section2 |

Consequently nine of the eleven four-body-block/two-bridge attachment
classes remain, fourteen of the sixteen five-body-block/leaf root
classes remain, and two of the three triangle/four-body-block layouts
remain. These are whole attachment counts, not pose or load-mask counts.

All six six-body coarse rows remain open. No graph beyond the three
explicit rooted hypotheses is removed. All owners, actual shared means,
individual zero circle weights and further physical zero-weight contacts
are retained. No numerical pose sample, secondary minimizer, Lean
compilation or CI is used.
