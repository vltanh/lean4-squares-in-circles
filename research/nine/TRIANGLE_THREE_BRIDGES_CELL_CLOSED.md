# The complete triangle-plus-three-bridges cell is excluded

**Status: complete whole-cell hand assembly; root and separate
independent full hand audits passed.** Work at a nine-square
radius minimizer in the declared window
\[
                         79/40\le R\le\sqrt{1105}/16
\tag{1}
\]
and use the common selected necessary physical certificate.

**Theorem.** No selected positive component has coarse profile
C1.3.b3: one cyclic triangle block and exactly three bridges.
The statement covers every attachment of the three other bodies,
every physical circle-load mask, both genuine radial leaf types,
all actual transmitter widths and every aggregate side mean.
All three additional physical squares remain in place.

The critical-radius arguments below are completion exclusions.
Accordingly, this theorem concerns a component in the full
nine-square minimizer; it does not assert that every abstract
six-body subconfiguration is physically impossible in isolation.

## 1. Exactly seven rooted attachments

Write the triangle as A,B,C. Deleting its edges leaves trees,
each attached to exactly one triangle vertex. A tree attached
to two triangle vertices would put its connecting edges on a
cycle, contradicting the bridge premise. A detached tree would
contradict connectedness.

The three outside vertices are distributed among these trees
as 3, 2+1, or 1+1+1. If all three attach at one root, the rooted
tree has four vertices. Its root degree in that tree is one,
two or three:

* Degree one leaves either a path or a fork beyond the first edge.
* Degree two gives a direct leaf and a separate two-edge arm.
* Degree three gives three direct leaves.

The distribution 2+1 gives either a two-edge arm or two direct
leaves at the first root, and one direct leaf at a different root.
The distribution 1+1+1 gives one direct leaf at every root.
These are exactly the seven classes proved in
SIX_BODY_CYCLIC_FRONTIER.md, Section 2.

The following table supplies a complete exclusion for each class.

| Attachment, with the triangle retained | Complete source | Scope used |
| --- | --- | --- |
| A–U–V–L | TRIANGLE_THREE_BRIDGES_LONG_CHAIN_EXCLUSION.md | Whole length-three chain, including the initially possible load at U |
| A–U, U–L1, U–L2 | OUTER_BRIDGED_TRIANGLE_EXCLUSION.md, Section 5 | Whole fork beyond one bridge |
| A–L0 and A–U–L1 | TRIANGLE_THREE_BRIDGES_MIXED_ARMS_EXCLUSION.md | Both direct-leaf types and every arm alternative |
| A–L1, A–L2, A–L3 | ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md | One exact triangle petal and three genuine leaves |
| A–U–L1 and B–L2 | TRIANGLE_THREE_BRIDGES_DISTINCT_ARM_EXCLUSION.md | Whole distinct-root arm-and-leaf attachment |
| A–L1, A–L2 and B–L3 | TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md | Whole two-leaves-at-one-root attachment |
| A–L1, B–L2, C–L3 | TRIANGLE_THREE_DISTINCT_LEAVES_EXCLUSION.md | Whole one-leaf-at-each-root attachment |

These rows are actual graph alternatives, not choices of a
numerical pose or a restricted contact owner.

## 2. Every body keeps its actual degree and all loads

The sources establish their load and transmission premises
before using any corresponding equation.

In the long-chain row, the intermediate U is not assumed
unloaded: the complete possible radial-S load at U is first
excluded by the width of V. In the fork row, the full local
all-bridge law and the two-leaf central-disk lemma are proved
before the actual outward end-triangle theorem is applied.

In the two mixed-arm rows, the triangle roots retain the
additional arm and leaf forces in their full equations.
The same-root articulation has degree four. The distinct
roots each have degree three. Neither proof imports the
equilibrium of a smaller triangle-with-leaf component.

The double-leaf-root source retains the full four-force
equation at the first root, including its exact critical-radius
exception. The one-leaf-at-each-root source keeps three
degree-three roots and the three actual radial external
resultants. Its positive concurrence theorem is applied only
after the common zero-moment alternative is exhausted; a
parallel root is never assigned a fictitious concurrence.

Finally, the same-root three-leaf row uses the uniform
one-articulation theorem with one genuine triangle petal.
Only the two unchanged triangle tips have degree two, exactly
as required by its end-triangle pressure input.

Thus no exact smaller-component theorem is obtained by
deleting a positive external force.

## 3. The critical completion exits retain all three extras

Let
\[
                        d=\sqrt{R^2-\tfrac14}-1.
\tag{2}
\]
The two sources that need a physical completion argument
at d=1 use the full nine-square geometry.

For the same-root mixed arms, the opposite-leaf endpoint
contains the actual four-square P skeleton. P_ALL_COMPLETION.md
excludes its five other physical squares. Those five include
both triangle tips and all three squares outside the positive
component.

For one leaf at each triangle root, the source first excludes
a root having the origin in a relative side interior. Each
remaining root has the origin as a vertex, with its genuine
S leaf along one incident side. The three occupied root-and-
terminal rays then route all six nonterminal units into the
three closed origin wedges. Positive radial force balance
makes all three apertures strictly smaller than 180 degrees,
and one is at most 120 degrees. The complete wedge theorems
give total capacity at most 2+2+1=5. The six units being
counted are the three roots and all three additional squares.

Every endpoint of the physical circle weights and every
actual contact mean is included in those capacity arguments.
They do not remove a leaf, rotate an extracted square, or
replace the remaining squares by their centers.

## 4. One common selected certificate

The component is extracted only after the established finite
normal conditions have been imposed simultaneously on all
physical candidate junctions. The attachment proofs use those
same conditions, including the already proved radial bridge
and leaf law, physical uncrossing and compatible strict
point-contact choices.

Any end-triangle theorem is applied only where its two tips
have their required exact positive degree two. Every shared
side keeps its actual aggregate application in the complete
closed segment. A physically two-circle-corner square retains
both nonnegative corner weights, even when one of them is zero.
No normal or mean is chosen again after extraction.

The seven rows therefore hold for the same certificate.
They exhaust the graph classification of Section 1 and
exclude the whole C1.3.b3 cell in a nine-square minimizer.

This closes one entire six-body coarse profile. It does not
exclude the other five six-body profiles, a triangle block
with further positive attachments, or arbitrary larger
components merely containing one of the displayed graphs.
No secondary minimizer, numerical pose sampling, Lean
compilation or CI is used.

