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

## 4. Current complete remaining roadmap and exact exit contracts

| Four-body block/root | Remaining necessary positive block loads | Whole parent status |
| --- | --- | --- |
| C4, root H | ABC | OPEN; both single-load and both two-load orbits are excluded |
| Diamond, hub H | KAB | OPEN; all five circle resultants and true H/K degrees retained |
| Diamond, tip | None | CLOSED by the full unchanged-degree obstruction |

There are exactly two remaining whole graph/load orbits in the two
open layouts. The full single-load exits are proved above.
TRIANGLE_C4_ADJACENT_LOAD_EXCLUSION.md excludes the whole AB/BC orbit
without a canonical premise. TRIANGLE_C4_OPPOSITE_LOAD_BRANCH_CLOSED.md
excludes the entire AC orbit at the common canonical minimizer.

For C4 ABC, the actual boundary path A-B-C has its middle circle force
inside the strict positive cone of the endpoint forces. For diamond
KAB, the same theorem applies to A-K-B with K's true degree three.
The intact H-X-Y end triangle has positive pressure at c_H, while the
other complete block must have negative pressure. Thus a genuine
endpoint is uniquely circle-touching with c_H.z_A<0; label it A by the
actual root reflection. The four necessary mask representatives in
order(middle,A,other endpoint) are SUS,UUS,SUU,UUU in each orbit.
Both-radial-endpoint masks are already excluded, including the
unique-middle/two-radial-endpoint limit. No force at the middle body
is deleted or split into artificial tips.

NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md gives every real H/A point
on A's two inner faces, within79/160 of its actual opposite corner;
both outward circle coordinates exceed3/5. On R²>=17/4 the bounds
improve to5/38 and19/20. The true center bound|c_H|²<9/2-R² puts the
origin strictly inside H only in that high-radius domain. The new
whole free-endpoint theorem below additionally uses the real physical
H/K contact in the diamond; it cannot be imported into ABC by
inventing an H/B edge.

## Entire opposite-load triangle/C4 branch closed; two load orbits remain

TRIANGLE_C4_OPPOSITE_LOAD_BRANCH_CLOSED.md closes the entire AC
block-load orbit at the existing canonical radius/Phi minimizer. It
assembles the physical two/two, unique/unique and both ordered mixed
masks with all true degrees, original channel means, individual zero
radial weights and all three other physical squares retained. The
canonical packing is fixed before normal selection; any selected
candidate with a positive hub/transmitter gap contradicts that same
packing's secondary minimality. No packing or certificate is changed.

TRIANGLE_C4_OPPOSITE_MIXED_TIPS_EXCLUSION.md supplies the final complete
mask exit. A parallel radial tip would make the real channel point
too central for the unique loaded tip. Whole fixed-tip/shared-block
virtual-work arguments remove every free unique-root interface. The
full radial-tip feature cover then gives a genuine inner-face parameter,
strictly greater than one half when that tip owns its root interface.
A unique-tip-owned interface contradicts the actual hub diameter.
With the hub owning that interface and the unique tip oblique, the
complete circle and contact equations force a radial sine greater
than one half, then a unique-tip sine below one tenth and an actual
radial-side parameter above nine tenths. Two actual hub points would
have vertical separation greater than 29/20, exceeding its diameter.

The entire parallel-unique-tip branch retains its original shared
channel mean. C4_MIXED_PARALLEL_TIP_SCALAR_BOUND.md proves the required
positive-pressure inequality on its full continuous domain. A concavity
bound gives the strict derivative reserve; two monotone comparisons
and exact endpoint inequalities give Delta<9/40 and rho>8/9. The final
whole-domain pressure margin is greater than3233/2408000. These are
analytic comparisons across full domains, with no angle boxes or
sampled signs. The actual geometry proves every scalar hypothesis.

NEGATIVE_UNIQUE_TRIANGLE_FREE_ENDPOINT_HIGH_RADIUS.md is a separate
uniform local theorem for the remaining diamond-hub orbit. A true
negative unique endpoint in a physical H-A-K triangle has no free HA
contact when R²>=17/4. The complete shared-AK chart retains its actual
mean and forces a positive physical offset. K's exact circle equation
makes that offset exceed one half, and the actual H/K contact transfers
the bound to H's frame. Cauchy--Schwarz then gives
c_H.z_A>R²-R sqrt(5/2+sqrt(3))>0, a contradiction. Only A has a
degree-two equation; H and K retain all their other forces. The
singleton-AK selection exit holds across the full radius window.

TRIANGLE_C4_THREE_LOAD_PARALLEL_DOMAIN.md excludes the whole opposite-
normal ABC root domain. Equal normals force an actual hub wall, support
between1/40 and1/2, opposite true application heights and height sum
at most one. Every such application has norm squared below13/16, so
both endpoint physical masks are unique. The full aligned/tilted
endpoint descriptions keep every mean and proper-length endpoint;
the wall support also exceeds sqrt((R-sqrt(2))²-1/4)>1/4. Its
actual hub center lies in the open radius-1/4 disk over the entire
same-normal domain. The full same-normal wall and nonparallel domains
remain open.

Root and separate independent full audits passed all five sources,
the complete mixed geometry, every analytic scalar inequality and the
whole AC assembly. The only remaining triangle/four-block graph/load
orbits are C4 ABC and diamond-hub KAB. Each retains four exact
negative-endpoint physical-mask families. Their whole exits and the
C2.34.b0 parent are OPEN. The coarse inventory remains nine closed and
49 open; four six-body coarse parents and all larger mixed parents
remain. Unrestricted sharpness, original equality and full earlier
prerequisite-chain audit remain OPEN. PR #11 stays draft; no Lean
compilation or CI was run.

Every remaining orbit must receive a whole core contradiction, sharp
radius theorem or joint capacity bound excluding all three arbitrary
extras. Every true higher-degree force, zero individual corner weight,
unused physical contact and original shared-side mean remains.
C2.34.b0 stays open with one of three complete attachment layouts
closed. The current two-orbit cover asserts no physical realization
and does not discharge the original equality or earlier dependency audit.

## 5. Exact new endpoint exits in both remaining load orbits

TRIANGLE_C4_ALIGNED_WALL_TIP_SIGN.md covers the entire actual ABC
wall support/radius/mean domain. Every aligned endpoint has nonnegative
horizontal outgoing normal toward B: otherwise its lower-left support
would exceed R²/4>=R-1 and no contained unit could touch beyond it.
The two-aligned-endpoint family is wholly excluded by the actual B
equation and physical circle-corner acuteness. Every surviving wall
therefore has a tilted endpoint with a westward outgoing normal, at
its lower vertex or outer lower face. Both physical B masks and all
original side means remain. The full nonparallel root domain remains.

NEGATIVE_UNIQUE_TRIANGLE_TIP_OWNED_EXCLUSION.md closes every A-owned
negative HA in the diamond, including the entire shared-interface
domain. Its proper-coordinate polynomial estimate and complete two
other-normal alternatives use no degree equation at H or K.
The residual owner cover is H-owned singleton across the full radius
window, or free HA with shared AK below R²=17/4. All four physical
K/A/B masks, H's five forces and K's three forces remain.
Both complete sources passed root and separate independent audits;
neither remaining whole graph/load orbit is yet closed.

