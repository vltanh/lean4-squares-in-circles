# The smallest k=7/B3 radial positive stress leaf is never an actual one-contact leaf

**2026-10-13. Complete conditional whole-contact normal form.**
This corollary unifies the entire radial SS interface
exclusion with exact contact-minimal leaf rigidity.
The underlying SS exclusion uses the independently
computer-certified unrestricted coarse bound
\(R_8^2>19/5\), explicitly recorded in
GLOBAL_LOWER_BOUND.md.

## Theorem

Choose a radius-minimizing packing of eight genuine
unit squares with **the fewest actual contacting
pairs**, satisfying the established disk ceiling
\(R^2\le9789/2500\).
Assume k=7 exterior outer centers, no full actual
seven-outer ring, and the **smallest central-branching
positive-stress component**
\[
C-X-Y-C\quad\text{plus radial positive bridge }C-Z.
\]
The positive radial bridge has Z as a
**degree-one vertex of the POSITIVE stress graph**,
while other actual zero-weight contacts are allowed.

Then Z must have **at least two distinct ACTUAL
square-contact neighbors**:
\[
\boxed{\deg_{\rm actual}(Z)\ge2.}                \tag{1}
\]
More exactly:

1. The genuine C--Z radial bridge cannot be in SS
   side-to-side interface mode.
2. Its only remaining SAT-owner interfaces are
   **CS (C radial corner/Z true side)** or
   **SD (C side/Z inward diagonal corner)**.
3. The Z square must have at least one
   additional **zero-positive-stress** actual
   contact with a *circularly adjacent exterior
   spectator* square.
4. If the central C square has **exactly three
   actual neighbors X,Y,Z**, the resulting
   actual outer graph must include the
   **entire** Y--Z or Z--X spectator arc.
   The isolated-spectator pattern is impossible.

With X,Y a consecutive outer-ray pair,
there are 21 labeled positive-stress
X/Y/Z triples, two remaining radial bridge
SAT interfaces CS/SD, and two possible
complete spectator arc directions.
Thus the **C-actual-degree-three** subbranch
has at most
\[
\boxed{21\cdot2\cdot2=84}
\]
labeled **graph-plus-radial-interface
templates**, before any continuous
geometric feasibility checks. These are
not 84 certified packings.

## Proof

The genuine three-interface radial bridge
theorem
HUMAN_RADIAL_BRIDGE_THREE_SAT_INTERFACES.md
proves that every positive radial
C--Z bridge leaf is one of SS,CS,SD.

The complete global
[HUMAN_B3_RADIAL_SS_FULL_EXCLUSION.md]
(HUMAN_B3_RADIAL_SS_FULL_EXCLUSION.md)
proves SS impossible under the precise
smallest B3 positive graph hypotheses
and established radius bounds.
The proof uses the rigorous previously
computer-certified \(R_8^2>19/5\)
only to derive a strict SS side-plus-
corner incidence normal form;
the final positive X--Y contact
contradiction is elementary true
full-square vertical separation.

The existing exact contact-minimal
[HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md]
(HUMAN_B3_RADIAL_STRESS_LEAF_BRACING.md)
theorem proves that a CS or SD
radial positive bridge square Z
cannot have only the positive
actual C neighbor. If it had
actual degree one, the genuine
minimum-contact actual-leaf theorem
would force the two square frames
C and Z parallel, hence the
SS interface already excluded.
Thus a CS/SD Z has an additional
actual contact with some square.

Because the seven exterior centers
are all outer, the strict outer-ray
angular-visibility theorem allows
Z to touch only its two immediate
outer-ray neighbors, neither of
which is X or Y. Those neighbors
are **spectator squares** outside
the unique positive-stress component.
Their additional Z contacts carry
zero chosen positive stress.
This proves 1--3 and (1).

If C has only its three actual positive
neighbors, the complete-spectator-arc
theorem
HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md
proves that each complementary
spectator path must be fully present
or fully absent; the full outer ring
is explicitly excluded. Since Z
has at least one spectator contact,
exactly one of those two arcs is
fully present. This proves 4.

The graph count is direct:
7 placements for XY, 3
non-neighbor placements for Z,
2 CS/SD interface choices and
2 full spectator arc directions.
No graph count is a statement of
geometric realizability. QED.

## Remaining full proof obligations

The minimized four-square positive
component has now **no genuine radial
actual leaf**, despite having a
degree-one *positive-stress* vertex.
This distinction is essential.

The remaining **CS** Z frame is
side-radial, with two equal-weight
disk-circle vertices and a corner
contact at C. The **SD** Z frame
has a diagonal radial corner with
one disk-circle vertex and a
C-side contact. Both have actual
zero-stress spectator bracing.

The zero-weight auxiliary spectator
path needs genuine circle-contact
anchors or an aligned
distance-one transmitter,
depending on its length.
If C has extra actual
zero-weight spectator contacts,
the simple complete-arc graph form
does not automatically hold.

The unrestricted sharp radius
\(R_8\ge\widehat R\),
the equality ring root A,
B2 m4..6, larger B3,
exterior root X and low-k
remain OPEN.
