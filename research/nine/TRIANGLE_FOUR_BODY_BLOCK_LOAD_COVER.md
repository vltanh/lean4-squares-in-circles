# A triangle attached to a four-body block: the complete remaining load cover

**Status: complete hand load cover and whole load-family exclusions;
root and separate independent full hand audits passed.**
Use the common selected certificate in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60.

The entire six-body positive component has a triangle H--X--Y--H
and a four-body block sharing only H. There are no bridges. The
triangle tips X,Y have exact positive degree two; the root has its
actual additional block forces. All three other physical packing
squares remain arbitrary and present.

SIX_BODY_CYCLIC_FRONTIER.md proves the complete three-layout cover:
C4 at its unique root orbit, diamond at a hub, and diamond at a tip.
The positive K4 subgraph is excluded in every attachment. The diamond-
tip attachment is already wholly excluded. This source gives every
necessary positive-load orbit of the two remaining layouts and two
complete C4 load exits.

## 1. The genuine end triangle and common root

X,Y are loaded: an unloaded degree-two transmitter cannot have its
two neighbors physically touching. H is physically circle-clear,
since a boundary H together with X,Y would form a forbidden physical
boundary triangle.

Write M=F_X+F_Y. The complete end-triangle theorem gives M nonzero,
with all physical circle masks and original contact means retained.
The four-body block therefore contains at least one other positive
load: otherwise global force balance would give M=0.

No isolated C4 or diamond equation is applied at H. Its actual total
positive degree is four for the C4, five for a diamond hub, and four
for a diamond tip.

## 2. C4 labels and the complete initial load cover

Write the four-cycle in order

    H--A--B--C--H.

The nonroot vertices A,B,C have actual positive degree two. H is
clear, and at least one of A,B,C is loaded. The reflection fixing
H and B exchanges A,C. Its complete initial load representatives
are

    one load:   A, B;
    two loads:  AB, AC;
    three loads: ABC.                              (1)

The triangle tips are additional loads in every set and are not
omitted from any force balance. The positive complement on the full
loaded set is connected: its two nonempty groups {X,Y} and the block
loads have all cross-group complement edges. Thus no isolated-block
loaded-complement exclusion is imported into (1).

### 2.1. The whole one-adjacent-load family is impossible

With exact block loadsA, the true degree-two bodies B,C are unloaded.
The path A--B--C--H is an actual positive-width normal channel, while
its endpoints A,H physically touch through their positive edge.
The channel's separated support half-planes contradict that contact.
This excludes the whole family and its reflected single-C image,
with all actual endpoint forces, means and three extras retained.

### 2.2. Two true parallel transmitters align both endpoints

Consider the remaining one-block-load family B. Its two actual
unloaded degree-two bodies A,C are transmitters between H and B.
Each is a physical unit bypass for the other's channel, so both
channels have reserve1. The unique shortest-displacement relation
makes their directions identical.

Both endpoint squares H,B own this common side axis. For clarity,
if an endpoint did not own it, its support face would be a single
vertex. The two disjoint side-transmitter intervals would have to
meet at that vertex, making both positive contacts singleton
vertex/vertex with a forbidden transmitter-axis endpoint normal.
Thus both endpoints are aligned with the transmitters. This is
exactly the two-channel conclusion proved in Sections1--2 of
TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md; no third bypass
premise is used until that source's Section3.

Choose the common unit direction n from H toward B. The real B
has two incoming pair forces in direction -n and no other positive
neighbors. Its true circle resultant is therefore

    F_B=beta n,   beta>0.                           (2)

Because B's frame owns n, a physical unique circle corner cannot
supply (2): in its own frame a farthest circle corner has nonzero
coordinates of magnitude at least1/2 along both side axes.
Thus B has two physical circle corners and is radial S along one
of its own axes. Its circle force has a nonzero component along
that radial axis, so (2) selects the positive n-axis, not either
transverse axis or -n. The transverse force component also forces
the two actual circle weights equal. Hence the actual unit is

    B=[d,d+1]n+[-1/2,1/2]Jn.                        (3)

This conclusion is proved from B's original two pair forces and
physical mask; B has not been assumed to be a genuine leaf.

### 2.3. The entire one-opposite-load family is excluded

The actual reserve1 channel and (3) give

    h_H(n)=d-1.

H is aligned with n and has width1, so

    h_H(-n)=2-d>59/60.                             (4)

X,Y and B are exactly the loaded bodies of this entire component.
Summing all genuine force equations therefore gives

    M=F_X+F_Y=-F_B=-beta n.

Thus the whole end-triangle resultant is along the H side axis -n.
END_TRIANGLE_AXIS_RESULTANT_SUPPORT_BOUND.md applies at the true
degree-four H and gives

    h_H(-n)<59/60,

contradicting (4). This excludes the complete one-opposite-load
family for every original circle mask, contact owner and side mean.
It needs no completion motion or secondary minimizer and retains
all three extra physical squares.

### 2.4. The precise full C4 residue

After Sections2.1 and2.3, exactly the necessary block-load sets

    AB,   AC,   ABC                                (5)

remain up to the true root reflection. All four-circle-force sums
for the two-load cases and all five-circle-force sums for ABC are
kept. No physical uniqueness assumption is imposed on a loaded body.

In AB, the true unloaded transmitter C has unit bypass A, touching
both endpoints H,B, so its actual reserve is1. Reflection covers BC.
In AC, the true unloaded transmitter B has unit bypass H, so its
reserve is again1. H is a genuine degree-four root, not a transmitter.
In ABC there is no unloaded block transmitter. These are complete
necessary width restrictions, not exclusions of the three whole
residual load families.

## 3. Both diamond root orbits

Use diamond hubs H,K and tips A,B, with exact edges

    HK, HA, HB, KA, KB.

First attach the triangle at hub H. X,Y,A,B are all genuine loaded
degree-two triangle tips. K retains exact positive degree three;
its neighbors H,A,B contain the physical edges HA,HB, so
NO_UNLOADED_DIAMOND_HUB.md forces K loaded as well. H is clear.
Thus the sole positive block-load set is

    KAB.                                          (6)

The three block loads form the positive boundary path A--K--B,
while X,Y form a separate positive boundary edge. All five circle
resultants participate in the actual global force balance. The
root H retains all five of its positive pair forces.

If the triangle is attached at a diamond tip instead, both unchanged
hubs and the other unchanged tip are forced loaded by the same true-
degree rules. They form a physical boundary triangle, impossible.
This is the already closed entire tip attachment in
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md; the new proof does not
reopen it or claim its changed root has degree two.

## 4. Complete remaining roadmap and exact exit contracts

| Four-body block/root | Remaining necessary positive block loads | Whole parent status |
| --- | --- | --- |
| C4, root H | AC; ABC | OPEN; both single-load orbits and the whole adjacent-pair orbit are excluded |
| Diamond, hub H | KAB | OPEN; every one of its five circle resultants retained |
| Diamond, tip | None | CLOSED by the full unchanged-degree obstruction |

There are three remaining necessary whole graph/load orbits in the
two open layouts. The complete one-adjacent and one-opposite C4
load exits are proved above; the entire adjacent-pair orbit is now
excluded by TRIANGLE_C4_ADJACENT_LOAD_EXCLUSION.md. The opposite-load
unique/unique mask is also excluded at the declared canonical minimizer.
The mixed AC mask and whole ABC orbit still prevent full C4 closure.
No table entry asserts a physical realization.

### Full parallel C4 exit and exact negative-endpoint mask domains

FOUR_CYCLE_PARALLEL_BYPASS_GENERAL_EXCLUSION.md excludes the whole
opposite-load C4 domain in which H is parallel to its true unloaded
transmitter. All additional H forces remain. A shared root interface
forces an actual radial endpoint and makes the other endpoint circle-
clear. With two point interfaces, the complete physical masks become
two unique corners at(-m,-3/2),(-m,3/2). Both genuine tip torque equations
use the same original channel mean and force equal circle scales,
then a forbidden equality of the two independently selected slopes.
No radial leaf, small-root premise or canonical motion is used.

BOUNDARY_THREE_PATH_RESULTANT_CONE.md proves that the middle actual
circle force on a physical three-body boundary path belongs to the
open positive cone of its two endpoint forces. The complete force
span is<174degrees, and both successive gaps are>10degrees. Thus the
negative pressure required by the intact end triangle occurs at a
genuine endpoint tip, in both C4 loadsABC and diamond-hub loadsKAB.
After the actual root reflection, label that endpoint A: it is uniquely
circle-touching withc_H.z_A<0. The other endpoint and middle body retain
either physical mask. Each full family has four necessary mask
representatives, in order(middle,A,other endpoint):SUS,UUS,SUU,UUU.
The entire both-radial-endpoint domain is excluded, including the
formerly open unique-hub/two-radial-tip diamond mask.

NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md proves every actual H/A
contact lies on A's two inner faces, with both outward circle-corner
coordinates>3/5 and distance<79/160 from its true opposite corner.
ForR²>=17/4 these improve to>19/20 and distance<5/38. The full root
bound|c_H|²<9/2-R²<1 also holds; in that high-radius domain the circle
origin is strictly insideH. All bounds preserve the true origin and
every original mean; no contact is reset to a corner. Root and
independent full audits passed all three complete sources and both
actual attachment applications. The later complete adjacent-load exit
leaves three whole graph/load orbits open. The coarse inventory stays
nine closed/49 open.

## Adjacent C4 closed, opposite unique mask closed, and diagonal C6 pocket empty

TRIANGLE_C4_ADJACENT_LOAD_EXCLUSION.md closes the entire adjacent
block-load orbit AB and its reflected BC image. The actual side channel
and bypass force the root-normal signs. Genuine loaded-tip concurrences
put the root-line intersection on the positive intact-petal ray. If the
channel support were nonpositive, both real petal applications would
lie on a side of height at least one, contradicting the complete
high-face theorem. Thus the full remaining domain has positive channel
support below 1/60. The actual return square then contradicts the exact
narrow-cap and boundary angular-shadow estimates. Every physical mask,
owner and original mean remains; no canonical premise is needed.

TRIANGLE_C4_OPPOSITE_LOAD_CANONICAL_CONTACT.md proves real hub/transmitter
contact in the whole opposite-load AC orbit at the existing canonical
radius/center-norm minimizer. A negative actual neighbor corner bounds
the hub center. The complete C4 hole is empty, and any positive
transverse gap admits an inward transmitter translation decreasing its
corner radii and the secondary norm, while preserving all nine physical
squares. The hub is oblique and both hub/tip contacts are singleton;
the physical hub/transmitter contact is not assigned positive stress.

TRIANGLE_C4_OPPOSITE_UNIQUE_TIPS_EXCLUSION.md closes the entire
unique/unique physical mask in that canonical domain. Fixed-tip and
whole shared-block virtual-work arguments remove every free root
normal while retaining both original channel means. The full owner
cover leaves one exact two-hub-owned endpoint. Its true block force
points opposite to the intact petal force, and the actual hub center
violates the petal's strict positive pressure. The mixed unique/radial
mask remains open, including all radial corner weights.

SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md excludes the entire actual
diagonal exterior pocket of the physical-unique, one-diagonal
alternating C6 family. The complete occupied cap strip and all
separating-axis owners are covered. Four exact polynomial identities
prove strict positivity on complete parameter rectangles; 202 exact
coefficient lower bounds are positive, with no sampled angle or
subdivision. The vertical case checks the whole center cap and every
northwest normal, including the auxiliary intermediate direction.
Together with central capacity one, at least two of the three extras
must lie in the two side pockets. Their joint capacity is still open.

Root and separate independent full audits passed all four complete
sources. The triangle/four-block branch now has three remaining whole
graph/load orbits: C4 AC, C4 ABC and diamond-hub KAB. Only the mixed
physical mask remains in AC at the canonical minimizer. Four six-body
coarse parents remain; the authoritative inventory is nine closed and
49 open. Unrestricted sharpness, original equality and full earlier
prerequisite-chain audit remain OPEN. PR #11 stays draft; no Lean
compilation or CI was run.

Every remaining orbit must receive a whole core contradiction,
a sharp radius theorem or a joint capacity bound excluding all
three arbitrary extra squares. Every true higher-degree root
force, physical zero-weight contact, individual zero circle-corner
weight and original shared-side mean remains. The exact-component
four-cycle and diamond-plus-leaf theorems cannot be applied after
removing any of the triangle forces at the root.

C2.34.b0 remains open with one of its three full attachment types
closed. No numerical graph enumeration, angle sampling, Lean
compilation or CI is used. Unrestricted sharpness, original equality
and the full earlier prerequisite-chain audit remain separate open
obligations.
