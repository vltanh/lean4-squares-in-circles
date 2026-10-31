# C3.334.b0: the whole two-triangle and four-body-block cell

Date: October 26, 2026.

**Status: ACCEPTED after complete root and independent C6 original-cell
reviews.** The full audits are
`REVIEW_C3_334_NO_BRIDGE_CELL_ROOT_2026_10_26.md` and
`REVIEW_C3_334_NO_BRIDGE_CELL_C6_2026_10_26.md`, both at the unchanged
mathematical source pin
`1a5fedd976d15b7e3ff3276be10a4cd1c5ee6716e8893ffa0f731c5347be4773`.
All named terminal C4 and diamond sources also have complete root and
independent acceptance. This acceptance-only status edit changes no
mathematics. No original checklist or shared ledger is edited here.

Choose the common canonical nine-square radius minimizer, with the
sum of squared center norms minimized among radius minimizers, before
the compatible physical normal selection and stress extraction. Work
in the inherited window

    79/40<=R<=sqrt(1105)/16.

The same-nine measure theorem supplies R>2 wherever a cited source
uses it. The canonical secondary choice is needed only by the
opposite-load bouquet pressure theorem used below; it does not
remove any actual physical body or permit changing a force after
extraction.

**Theorem.** The selected positive component cannot have exactly
three cyclic blocks of orders 3,3,4 and no bridges. This is the
entire original coarse cell C3.334.b0, including every underlying
four-body adjacency, every block-cut attachment, every load mask
and every physical completion.

The exact block identity gives

    n=1+(3-1)+(3-1)+(4-1)=8.

Thus there are eight actual bodies in this component and one other
arbitrary physical square in the same nine-square packing. That
ninth square stays present throughout every argument, including
the canonical opposite-load theorem. Every original positive force,
true degree, circle atom, individual zero weight, actual common
mean, selected normal and zero-weight physical contact is retained.

## 1. Complete graph and attachment cover

The block-cut incidence graph is a tree, by the exact block
decomposition in `CYCLIC_BLOCK_INVENTORY.md`. Its three cyclic
block nodes, with no bridge nodes, have only these possibilities:

1. All three blocks meet at the same articulation H: a bouquet.
2. They form a chain with two distinct articulation vertices in
   its middle block.

Indeed, if there is only one articulation joining the blocks,
all three meet it. Otherwise the two incidences joining three
block nodes give a chain. Distinct maximal blocks cannot share
two vertices, and any further incidence cycle would merge them
into a larger biconnected block. There is no additional pendant
body or branch because the given cell has exactly these blocks
and no bridges.

Each order-three block is the full triangle. The order-four
simple biconnected block has minimum degree at least two. With
four edges it is C4; with five it is K4 minus one edge, the
diamond; with six it is K4. These exhaust the complete adjacency
cover. `NO_POSITIVE_K4_SUBGRAPH.md` excludes every K4 occurrence
with arbitrary additional root forces, so only C4 and diamond
need remain in the subsequent cases.

Every terminal triangle has two private true degree-two tips.
An unloaded tip would transmit a positive-width channel between
its two physically touching neighbors, so both tips are loaded.
The complete `ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md` makes its
actual articulation contain O in its open interior. Its theorem
retains every other force and any true degree at that articulation.

## 2. A four-body middle block with distinct triangle roots

Suppose the four-body block is the middle of a chain and its two
triangle attachments occur at distinct actual vertices H_1,H_2.
Both triangles are terminal and intact, by the true degree
argument in Section 1. Thus O lies in int H_1 and int H_2.
The original physical units would have overlapping open interiors.
This excludes all such chains at once, irrespective of the
four-block graph, both attachment vertex orbits, or any of its
loads. No force at either root was removed to make the terminal
tips degree two.

If the two attachments use the same vertex, the graph is exactly
the bouquet treated next; it is not a missing middle-block case.

## 3. The whole bouquet, including every private C4 load mask

Let H be the common root of the four-body block and the two
intact triangles. Write M_1,M_2 for the complete actual circle
resultants of the two tip pairs. The intact-root theorem gives
O in int H, and hence H is physically circle-clear. The full
end-triangle pressure theorem gives

    c_H.M_1>0,       c_H.M_2>0,                           (1)

with all other H forces retained. Their four private tips are
distinct actual bodies of true degree two.

### 3.1. A small own-side height is incompatible with two intact petals

We record the exact geometric corollary needed for the sole
opposite private C4 load. Put epsilon=max(d-1,0)<1/60, where
d=sqrt(R^2-1/4)-1. At a root of two intact petals, no actual
own side can have positive height h<=epsilon.

For each intact petal the full common-side/origin theorem gives
an actual root face of height P with

    1/5<P<39/40,

and its two actual transverse port coordinates have strictly
opposite signs. The lower bound follows from a straddling port
of transverse magnitude at most 1/2 and the boundary-point
floor |p|>67/120. The accepted
`GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md`,
Section 2, also proves that at most one intact petal can use
any given actual H side.

Suppose an own side has normal e and height 0<h<=epsilon.
Its opposite height is 1-h. Neither can be the common petal
face: h<1/5 and 1-h>59/60>39/40. Thus both petals must use
the two sides perpendicular to e. On either such actual face,
strict port straddling in the transverse e-coordinate gives
one original boundary-tip application P N+w e with

    0<w<=h<=epsilon<1/60.

Therefore

    P^2>(67/120)^2-(1/60)^2=299/960>1/4,

so P>1/2. The one-petal-per-face theorem forces the two petals
to use opposite perpendicular faces, whose heights sum to the
unit width one. Both cannot exceed 1/2. This proves the stated
small-own-side obstruction.

This is the same local face argument as Section 3 of the cited
common-root source after an actual own side is already supplied.
There is no invocation of a bridge theorem on a cyclic edge and
no claim that a channel's individual side mean is radial.

### 3.2. All zero- and one-private-load C4 masks

For a C4 write its exact order as H-U-V-W-H. The nonroot
vertices U,V,W retain true degree two. If none is loaded,
the complete unloaded-appendage identity CY.LOAD.1 in
`CYCLIC_BLOCK_INVENTORY.md` applies to {U,V,W}, whose only
positive external neighbor is H, and gives a contradiction.

If the only private load is adjacent to H, take it to be U
after the root reflection. The true unloaded V,W give a
positive-width normal channel U-V-W-H, contrary to the actual
direct UH contact. This is the full normal-channel obstruction,
not an isolated-cycle force equation at H.

If the sole private load is the opposite vertex V, the two
unloaded U,W are genuine parallel transmitters from H to V.
Sections 1--2 of
`TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md` force both widths
to be one, the same direction n, and both endpoints to own
that actual side axis. The true V2 force equation then makes
V radial S in direction n:

    V=[d,d+1]n+[-1/2,1/2]Jn,
    h_H(n)=d-1.

All original channel means are retained; only the actual
support value is determined. Since O is in int H, d-1>0.
It equals epsilon and contradicts the small-own-side theorem
in Section 3.1. Thus every zero/one private-load mask is gone.

### 3.3. Both adjacent-private-two-load C4 masks

Suppose U,V are loaded and W is unloaded; the other adjacent
mask is its reflection. The true channel H-W-V and physical
unit bypass U give the actual frame

    H subset {x<=a},       V subset {x>=a+1},
    a+1<=d,

with reserve one. Because O is openly in H, a>0. Hence
0<a<1/60 and R>sqrt(17)/2.

Section 2 of the complete accepted
`ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md` excludes
this positive-height channel using only the actual channel,
the two loaded endpoints, their real HU and UV applications,
and physical containment. Its root-circle and middle-triangle
force arguments occur only in later sections and are not used
here. Explicitly, every point of V has angle from e_x less
than atan(13/20). The actual HU application Q in the boundary
U has |Q|>3/5 and Q_x<1/60, so its angle is greater than
acos(1/36). The other actual U point in V is within atan(13/20)
of e_x, while U's full angular shadow is less than atan(23/16).
These conflict because

    cos(atan(13/20)+atan(23/16))
      =21/sqrt(446665)>1/36.

Thus the full adjacent pair domain is excluded without replacing
the sum of two petal resultants by one physical petal.

### 3.4. Opposite-private-two and full-three C4 masks

In the opposite mask U,W are loaded and V is unloaded. The
full canonical theorem
`POSITIVE_ROOT_PRESSURE_OPPOSITE_C4_EXCLUSION.md`, Section 6,
applies directly with zero leaves and two intact end triangles
at H. It explicitly permits this entire same-root family and
all arbitrary other physical squares. Equivalently its arbitrary-
root pressure form in
`ORIGIN_ROOT_C4_PRESSURE_AND_BOUQUET_CLOSURE.md`, Section 4,
gives nonnegative pressure of the actual private C4 sum S.
Together with (1) this contradicts the full component equation
S+M_1+M_2=0. The canonical secondary minimizer and all original
outside physical squares are retained as required by that input.

In the full-three mask, the same pressure source's Section 1
gives c_H.S>=0 for the true private U2/V2/W2 and the actual
O in H. It permits arbitrary additional root forces and true
degree, here H6. The strict pressures (1) and the unchanged
full component balance again contradict one another.

The list none; sole U or W; sole V; adjacent UV or VW;
opposite UW; all UVW is every subset of {U,V,W}. No mask or
individual corner-weight endpoint has been omitted. The H6
C4 bouquet is therefore entirely excluded.

### 3.5. Both diamond root orbits

If the common articulation H is a diamond tip, both private
hubs retain true degree three and the other private tip true
degree two. The full unchanged-degree theorem
`ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md`, Section 2, forces
those three private bodies to be a physical boundary triangle.
It allows arbitrary other forces at H and excludes this whole
root orbit.

If H is a hub, the other hub keeps K3 and the tips keep U2,W2.
The complete arbitrary-root theorem
`DIAMOND_ROOT_PRESSURE_AND_MIXED_BOUQUET_CLOSURE.md` gives
nonnegative pressure of their actual full circle sum S. Its
Section 5 explicitly includes one diamond, no leaves and two
intact end triangles, with eight bodies and one arbitrary extra.
Using (1) in S+M_1+M_2=0 gives the contradiction. H has its
true degree seven; neither K3 nor either tip equation is reduced.

All bouquet graph types and load possibilities are now covered.

## 4. A middle triangle and the whole terminal four-body block

The only remaining block-cut shape is a chain with a triangle
as the middle block. Name that triangle A-H-C, with the terminal
triangle at A and the terminal four-body block at H. Its two
articulation vertices A,H are distinct. The untouched C has
true degree two and is loaded because A and H physically touch.

The intact terminal triangle at A gives O in int A. Form each
complete external system of the middle triangle by summing the
actual private branch equations and adding the root's own
original circle resultant. Internal forces and origin moments
cancel at their genuine common applications. Every original
circle atom has zero origin moment. This gives exactly the
full external systems required by the following sources, without
silently dropping a possible H circle load.

For a terminal C4, H keeps degree four and the other three
block bodies retain true degree two. The complete private-load
cover and its full sources are:

| Actual private load set, in H-U-V-W-H order | Complete exclusion |
| --- | --- |
| Empty, sole U, sole V, sole W | `ROOTED_C4_ZERO_ONE_PRIVATE_LOAD_EXCLUSION.md` |
| U,V or V,W | `ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md` |
| U,W | `ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md` |
| U,V,W | `ROOTED_C4_THREE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md` |

The adjacent source proves the actual H circle resultant zero
before identifying its whole external force with the private
sum; physical boundary contact with zero weight is still kept.
The sole-opposite source proves H physically clear from its
true two-channel geometry. The opposite-two source uses the
three actual boundary neighbors U,W,C, and the full-three source
uses the actual physical boundary four-cycle obstruction.
Every source therefore has the precise root-load scope needed
in this full original chain.

For a terminal diamond rooted at a tip, the same unchanged
private-hub/tip obstruction used in Section 3.5 excludes it.
For a terminal diamond rooted at a hub, apply
`ROOTED_HUB_DIAMOND_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md`.
It has exactly the original H5/K3/U2/W2 degrees, full private
loads, original HK force and means, all physical masks, and
the present origin-interior A with its full middle forces.
Its physical-triangle coefficient and actual outer-ring winding
proof excludes every contact and root-pair alternative, without
splitting K's circle load or deleting the chord.

K4 was already excluded globally in Section 1. These are all
four-body block adjacency/root possibilities, so every chain
with a middle triangle is excluded.

## 5. Complete original-cell conclusion

Sections 2--4 exhaust the entire block-cut tree: the four-body
middle with two distinct roots, the shared-root bouquet, and
the two images of a middle triangle with a terminal four-body
block. Section 1 exhausts every four-body graph. The terminal
and bouquet analyses separately retain every private-load mask
and every possible circle force at a higher-degree articulation
until its genuine clearance or force sum has been established.

All arguments refer to the same common selected certificate
at the same canonical nine-square packing. Compatible local
normal selections have their accepted simultaneous arbitrary-
root scopes. No block is isolated by deleting an original
positive force. The ninth physical square and all zero-stress
contacts remain in every completion and canonical premise.

Therefore the entire original C3.334.b0 cell is excluded.
This proof does not treat the one-bridge C3.334.b1 cell, a
different cyclic-size profile, the unrestricted n=9 theorem,
or every original equality packing as closed. No new deep
checklist ID is introduced merely by this assembly.

No numerical pose, sampled orientation, force replacement,
physical motion, Lean compilation, CI, remote action or
shared-ledger edit was performed in this source.
