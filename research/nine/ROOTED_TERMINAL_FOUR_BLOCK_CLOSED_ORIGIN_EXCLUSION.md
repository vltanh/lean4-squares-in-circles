# A terminal four-body block excludes every distinct closed-origin unit

Date: October 27, 2026.

**Status: complete proposed uniform closed-origin extension and disjoint
terminal-block consequence, pending full root and separate independent
review.** No original gate or shared ledger is changed.

Keep all nine actual interior-disjoint unit squares and the common
compatible selected physical certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    r=R-sqrt(2)>67/120>1/2,
    M_*=91/60.

Every contained center has norm less than M_*. A contained neighbor
beyond a supporting half-plane of height h requires h<=d. Distinct
actual unit centers are at distance at least one. These are the exact
geometric bounds in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1.
All original positive forces, actual application means, circle atoms,
individual zero weights, and selected contact normals remain.

## 1. Statements and unchanged private scope

Let Q be an actual four-body biconnected positive block with attachment
root H and three private bodies. Every positive pair edge at a private
body belongs to Q. H may have arbitrary other positive pair forces,
circle loads and true degree. A private transmitter is always a true
unloaded degree-two body, not a body obtained by deleting a force.

**Closed-origin theorem.** No actual square E outside Q can contain O
even on its boundary.

The complete arbitrary-root private calculations have already been
proved in ROOTED_FOUR_BODY_TERMINAL_ORIGIN_UNIT_EXCLUSION.md. That
source assumes O lies openly in E. Here the new work is the full
boundary-origin cover. No statement about H's resultant ray, pressure
or circle clearance is assumed.

**Disjoint-terminal-block corollary.** Two vertex-disjoint terminal
four-body blocks of this scope cannot occur in the same actual packing.
They need not have a triangle between them, and their roots retain all
forces in the intervening original graph.

The proof uses the actual physical embedding and contact loops. Its
auxiliary concurrences and positive coefficients are geometric tools;
they are not newly assigned physical force magnitudes or redistributed
circle loads.

## 2. Whole-unit capacity of every remaining four-ring

The degree-free equality theorem in
FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md, equivalently
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md, Section 2, says that an actual
four-ring enclosing a whole distinct unit must be the exact aligned
five-unit cross. This includes all weak junctions and contact-polygon
degeneracies. The enclosed unit shares its four entire sides with the
four ring units.

If a ring unit T is a true unloaded degree-two private body, its two
actual ring contacts are the two ends of its inward side. At a lower
cross arm the two actual outward normals have forms

    (-a,b), (c,f), a,b,c,f>0.

Their unchanged positive forces have a strictly positive upward sum,
contradicting the full unloaded T equation. These strict signs hold
also at a contact equal to O. PHYSICAL_BODY_GRAPH_UNCROSSING.md,
Section 2, selects strict exposure at every point-only vertex/vertex
contact; at O only the additional nonradial assertion is omitted.
No new selection is made here.

If all three private ring units are physically boundary, the same
cross has three boundary arms, forcing R^2=5/2 by the full elementary
cross calculation in FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md. This is
outside the radius window. For opposite two boundary ring units, the
degree-free opposite-boundary calculation in
SPANNING_K23_LEAF_BLOCK_EXCLUSION.md, Section 3.1, gives the same
contradiction using containment of the other two arms.

Thus each ring below has zero whole-unit inner capacity: a C4 with a
private unloaded transmitter, a C4 with all three private loads, and
the outer ring of a hub-rooted diamond with three loaded private
bodies. No argument at an arbitrary-degree root is replaced by the
unloaded degree-two argument.

## 3. Local facts when E contains O only on its boundary

Assume a distinct actual E outside Q contains O closed. No Q unit can
contain O in its open interior: any such unit would meet a full-
dimensional portion of E near O, contrary to disjoint interiors.

Two elementary consequences handle the new boundary cases.

### 3.1. A chord joining two boundary neighbors avoids O

Suppose P_1,P_2 are two actual root applications in H, each also in a
physical boundary neighbor. Then |P_i|>=r>1/2. If their segment
contained O, an own supporting line of H through O would contain both
endpoints, because O is not interior to H. They would therefore lie
on one actual side of length one, on opposite sides of O. But

    |P_1-P_2|=|P_1|+|P_2|>1,

which is impossible. Thus [P_1,P_2] avoids O, including all coincident
or side-endpoint alternatives.

Choose D in int H, for example its center. The triangle
conv(D,P_1,P_2) also avoids O. If O belongs to H's boundary, any point
of that triangle on an active own line through O must be on the base
[P_1,P_2]; the preceding argument excludes it there.

### 3.2. An unloaded-body replacement remains valid at boundary origin

Let T be a private transmitter with actual application segment
[P,P'] avoiding O. Replacing the center-to-contact path by [P,P']
uses conv(c_T,P,P'). This triangle avoids O: if T contains O on a
boundary, only its base could meet that active boundary, and the
base avoids O by hypothesis. No T can contain O openly.

For a loaded private body with actual positive radial concurrence
q_T=t_T F_T, every x in T satisfies

    F_T.x>0,

because each original circle corner z has
`z.x>=R^2-R sqrt(2)>0`. The whole conv(T,q_T) therefore avoids O,
including a two-circle-corner concurrence outside T. A true loaded
three-force diamond hub is kept at its real center; no two-force
concurrence is assigned to it.

Every finite representative loop and homotopy used below consequently
avoids a small fixed neighborhood of O once its stated chord conditions
are checked. If it has nonzero winding about O, choose an actual point
z in int E sufficiently close to O. Its winding is the same. The
connected int E avoids every closed ring unit and every occupied
representative path, so its winding is constant and nonzero. The
whole actual E is enclosed, contradicting Section 2.

The selected physical plane embedding can be taken in arbitrarily
small neighborhoods of its actual center/contact representation.
At weak junctions choose those neighborhoods to avoid the fixed z.
This is the same physical embedding argument used in the accepted
whole-ring theorem; no empty capacity is assigned to a routing disk.

## 4. The nonparallel root correction with an own margin equal to zero

Retain the exact nonparallel private-path hypotheses and notation of
ROOTED_FOUR_BODY_TERMINAL_ORIGIN_UNIT_EXCLUSION.md, Section 3:

    q=-alpha u-beta v, alpha,beta>0,
    P_1=q+a u, P_2=q+b v,

where u,v are the actual positive root-edge vectors and a,b are
arbitrary real port coefficients. The permitted private representative
path gives an auxiliary loop through q of winding one. Assume
[P_1,P_2] avoids O and all the private replacements satisfy Section 3.

The two root lines avoid O because u,v are independent and
alpha,beta>0. The actual minus auxiliary loop is exactly

    D--P_1--q--P_2--D.

Its triangle D--P_1--P_2--D lies in H and avoids O by Section 3.
The other triangle P_1--q--P_2--P_1 has no edge through O. If O is
outside it, the correction has winding zero and the actual ring
encloses the whole E by Section 3. This is impossible by Section 2.

If O is strictly inside it, coordinates in the independent basis
u,v based at q give

    q=(0,0), P_1=(a,0), P_2=(0,b), O=(alpha,beta).

Thus a,b>0: both original root ports are proper in precisely this
remaining case. Since O is not interior to H, choose and reflect an
actual own coordinate so

    H=[h,h+1] times [l,l+1], h>=0.

Strict triangle interiority forces q_x<0. Indeed every point of
[P_1,P_2] has x>=0, and q_x>=0 would leave O on or outside the
triangle's boundary. Put N=-q=alpha u+beta v, so N_x>0. Properness
forces both actual unit normals n_i to have positive x component,
and both ports lie on the far side

    x=A=h+1>=1.

Here the weak equality A=1 is sufficient; the old theorem's strict
origin-free margin is not being assumed. For completeness, let mu_i
be the positive auxiliary coefficients of N along the two fixed unit
normals, and write P_i=q+b_i n_i with b_i>0. The actual convex mean
with weights proportional to mu_i/b_i is

    P_bar=q+N/W=(1/W-1)N in H,
    W=mu_1/b_1+mu_2/b_2.

Its x coordinate is A>0, so its coefficient along N is positive.
The proper-port own-frame calculation puts q_y between the two
actual port heights. These heights and P_bar therefore put zero
between the transverse side coordinates. With P_i=(A,y_i), the
unchanged line concurrence gives the geometric moment identity

    A N_y=sum_i mu_i y_i(n_i)_x.

Thus N_y/N_x is a positive weighted mean of y_i/A. The normal slope
is a positive weighted mean of that ratio and its own y_i/A. An
upper endpoint has nonnegative transverse normal component, a lower
endpoint nonpositive component, and a horizontal normal retains its
actual side mean. Exactly as in the reviewed weak-cap calculation of
GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md, Section 1.1,

    h_H(n_i)>=A/(n_i)_x>=1/(n_i)_x.

The actual contained neighbors give

    (n_i)_x>60/61, |(n_i)_y|<11/61, h_H(n_i)>=1.

Their real centers have projection at least 3/2 in their respective
normal directions, norm less than M_*, and transverse magnitude less
than sqrt(181)/60<27/120. On the same fixed own x axis both satisfy

    (c_i)_x>(3/2)(60/61)-(27/120)(11/61)=3501/2440=:L.

The common cap has squared diameter

    (M_*-L)^2+4(M_*^2-L^2)=52124381/53582400<1.

This contradicts the two real incircles. All auxiliary coefficients
in this paragraph belong to a geometric two-neighbor calculation.
No physical stress, original magnitude or circle load is changed.
The full nonparallel implication is therefore valid at boundary O.

## 5. The parallel root correction with boundary O

Retain the exact parallel private-path hypotheses in the earlier
terminal-four-block theorem, Section 4. Both original root normals
equal e, their actual ports P_+,P_- have strictly opposite transverse
signs, their endpoint representatives lie forward on these same
normal lines, and the actual private path has one angular interval
shorter than pi bracketing e.

The two distinct root ports force side ownership, so

    H=[s-1,s]e+[b,b+1]Je, b<0<b+1.

Since O is not interior to H, either s<=0 or s>=1. If s>=1,
both actual neighbor centers have e projection at least 3/2; their
strict containing cap has squared diameter less than or equal to

    (M_*-3/2)^2+4(M_*^2-9/4)=29/144<1.

If s<0, the original negative-axis representative with
`D=(s-1/2)e` has winding minus one: its upper segment advances
`theta_+-pi`, its short private path advances `theta_--theta_+`,
and its lower segment advances `-pi-theta_-`. The sum is -2pi.
The whole E is enclosed by Section 3, a contradiction.

For the remaining s=0 case, the full-three, opposite-two and diamond
applications have both ports in physical boundary neighbors. Their
strict transverse straddling gives

    |P_+-P_-|=|P_+|+|P_-|>2r>1,

contradicting the actual unit side. The adjacent-two mask below has
strictly negative channel height and hence already has s<0. These
are every parallel boundary alternative required here.

## 6. Every two- or three-private-load C4 mask

Write the actual C4 as H-U-V-W-H with U,V,W true degree two.

### 6.1. Opposite private loads

Let U,W be loaded and V unloaded. The root-independent private
calculations in ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md,
Sections 2--5, prove both endpoint stars nonparallel, their positive
proper concurrences, and a width-one channel whose actual mean height
is nonzero. The loaded resultant rays are independent and span less
than pi. A nonparallel root has q=-t(u+v), t>0; a parallel root has
equal normals and strict port straddling. These are the exact facts
used in Section 6 of the earlier uniform terminal-block theorem,
before any outside-unit premise.

The unloaded V segment avoids O because its actual channel height
is nonzero. Its boundary-origin replacement is valid by Section 3.2.
Both H ports belong to the loaded U,W, so Section 3.1 excludes O
from their chord. The same original auxiliary triangle and private
path therefore satisfy Sections 4--5. The resulting enclosed E is
impossible by either the true unloaded V cross or the opposite-
boundary cross. This retains all original H circle forces.

### 6.2. All three private loads

The root-independent calculation in
ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md gives the complete
positive proper private concurrences, strict three-boundary resultant
cone, negative nonparallel root concurrence, and equal-direction
parallel-root alternative. The ordered private path and auxiliary
force loop are exactly those in the earlier uniform theorem, Section 7.
All private replacements avoid O by their original positive circle
half-planes. Both H ports are in boundary neighbors, so their chord
avoids O. Sections 4--5 and the three-boundary capacity theorem exclude
the entire mask, with no changed root equation.

### 6.3. Adjacent private loads, including zero channel height

Let U,V be loaded and W unloaded; reflection gives the other mask.
Use the exact channel/bypass frame from
ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md, Sections 1--3:

    W=[alpha,alpha+1] times [z,z+1],
    H subset {x<=alpha}, V subset {x>=alpha+1},
    P=(alpha,y_0) in H intersect W,
    Q in H intersect U, Q_x<=alpha,
    alpha+1<=d.

We strengthen its pure cap observation to

    alpha<0.                                           (12)

Suppose alpha>=0. Then d>=1 and R>=sqrt(17)/2, including equality.
The actual V lies entirely in x>=1, so the orientation-uniform cap
lemma of FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md, Section 1, puts all
its rays strictly within beta=arctan(13/20) of the positive x axis.
The actual Q lies in boundary U, whence

    |Q|>=R-sqrt(2)>3/5,
    Q_x<=alpha<1/60,
    angle(e_x,Q)>arccos(1/36).

The strict local boundary-shadow estimate in
BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md, Section 2, holds at every
`R>=sqrt(17)/2`, including equality, and gives shadow width less than
`omega=arctan(23/16)`. An actual U-V contact belongs to both squares,
so the angle of Q from e_x is less than beta+omega. But

    beta+omega<pi/2,
    cos(beta+omega)=21/sqrt(446665)>1/36,

where `756^2=571536>446665`. This is a contradiction and proves (12).
In particular H avoids the entire closed origin, independently of
its other forces.

The same exact private solve gives y_0<0 in both root alternatives.
In the nonparallel case q=-t(u+v), t>0; in the parallel case both
normals are e_x and the two root ports strictly straddle height zero.
Both loaded concurrences are positive and proper. The actual unloaded
W segment has constant height y_0<0 and therefore avoids O.
Section 3.2 applies if W contains O on a boundary; the root chord lies
in the origin-free H. The original short private path and auxiliary
triangle are precisely those in the earlier uniform theorem, Section 8.
Sections 4--5 and the true unloaded W cross contradiction exclude
the full adjacent mask. No later middle-triangle or clearance premise
from the old adjacent source is used.

## 7. Every zero- or one-private-load C4 mask

An empty private load set is the impossible nonempty unloaded
appendage attached only at H, by CY.LOAD.1. A sole adjacent private
load leaves a positive-length two-transmitter channel between the
already touching H and that loaded endpoint. These exits use no root
force or origin premise.

For a sole opposite load V, the complete original two-channel theorem
gives, with every mean retained,

    V=[d,d+1] times [-1/2,1/2],
    H=[d-2,d-1] times J_H,
    U=[d-1,d] times I_U,
    W=[d-1,d] times I_W,                              (13)

where all three transverse intervals have length one, I_U and I_W
have disjoint interiors, and each has positive-length overlap with
both J_H and [-1/2,1/2]. H and V own the actual channel axis. The
true loaded V2 equation gives radial S and a positive weighted mean
zero of the two original channel heights y_U,y_W. Thus 0 belongs to
J_H. These are Sections 3--5 of ROOTED_C4_ZERO_ONE_PRIVATE_LOAD_EXCLUSION.md,
before its former root-ray use.

If either height is zero, both are zero. The two disjoint-interior
length-one intervals containing zero must then be [-1,0] and [0,1].
Their positive-length intersections with J_H force zero into int J_H.
For d>1, the x interval [d-2,d-1] straddles zero strictly, so O lies
in int H, impossible beside E. For d<1, the two transmitter x
intervals straddle zero strictly and their union contains an open
neighborhood of O. For d=1, H fills the left local half-plane and
the two transmitters fill the upper-right and lower-right local
quadrants. Their actual union again contains an open neighborhood
of O. In both latter cases no full-dimensional actual E containing
O closed can have interior disjoint from that union. All zero-height
possibilities are excluded without moving a mean.

Hence y_U,y_W are nonzero and opposite. They put zero strictly inside
J_H. The d>1 case again makes H origin-interior and is impossible.
Retain d<=1, including d=1. Choose

    D_H=(d-3/2,0) in int H,
    D_V=(d+1/2,0) in int V.

The upper actual horizontal channel gives a path from D_H to D_V
strictly above the axis except at its two ends; the lower actual
channel gives the return below it. The H pieces lie in x<=d-1<=0
and meet the axis only at the strictly negative point D_H. The V
pieces lie at positive x. This actual center/channel representative
has winding minus one about O, also when d=1. All its vertices and
segments avoid O because both channel heights are nonzero.

For any boundary-origin transmitter, its replacement triangle avoids
O by Section 3.2. Alternatively the representative itself already
has nonzero winding at every sufficiently near point of int E; all
physical edge homotopies avoid that point. Thus the unchanged whole
E is enclosed. Either true unloaded private channel contradicts the
cross in Section 2. The sole-opposite mask is completely excluded.

Together Sections 6--7 cover every one of the eight private C4 masks.

## 8. Both diamond roots and K4

For a hub-rooted diamond, keep the actual private K3 and U2,W2
equations in full. Their accepted load argument forces all three
private units loaded. The complete original coefficient cover in
ROOTED_HUB_DIAMOND_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md gives either

    q=-alpha u-beta v, alpha,beta>0,

for the nonparallel outer root pair, or all three actual H-to-diamond
forces parallel with the same sign. This retains the HK chord and
does not split its loaded K3 equation.

The actual U-K-W boundary path has one angular interval shorter than
pi; the private coefficient identity puts -q strictly in its endpoint
cone. The original auxiliary path therefore has winding one in the
nonparallel case. In the parallel case its true endpoint rays, proper
ports and moment give exactly the strict straddling of Section 5.
These are the root-independent inputs in Section 10 of the earlier
uniform theorem. The two outer H ports belong to loaded neighbors,
so their chord avoids O by Section 3.1. Every private replacement is
in a strict original circle half-plane, or in the unchanged loaded K.
Sections 4--5 and the three-boundary outer-ring capacity exclude the
entire hub-rooted diamond at the new closed-origin scope.

A tip-rooted diamond is already impossible by the original private
hub-degree-three and remaining tip-degree-two argument in
ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md, Section 2. Arbitrary root
forces are allowed there. The arbitrary-attachment positive-K4 theorem
excludes K4. These are the full simple four-body biconnected graph and
root orbits. The closed-origin theorem is proved.

## 9. The exact origin-free loop consequence

The preceding proof, before using the actual E, also supplies the
following fact. If all four closed units of a terminal four-body block
avoid O, then either the block is already excluded by its private
equations or its actual outer ring has nonzero winding about O and
has the zero whole-unit capacity of Section 2.

Here is the complete scope check. For full-three, opposite-two and
hub-diamond cases the original private path/negative-concurrence
calculation still holds; the nonparallel correction-interior case is
excluded by the same geometric cap, while its exterior case gives
actual winding one. A parallel root either enters the cap or the
strict negative-axis winding construction. For adjacent-two the
actual channel has negative height and the same complete correction
proof applies. For a sole opposite load, H's origin avoidance and
its actual zero transverse mean force d<1; an original mean of zero
would put O in a transmitter. Thus the same two nonzero channel
heights produce winding. Empty/sole-adjacent masks, tip diamond and
K4 were already impossible without E.

All homotopies here avoid O directly because every original block
body avoids it and every loaded concurrence lies in a strict circle
half-plane. In the nonparallel correction the actual root chord
cannot meet O. This consequence is not an inference of an outside
physical square from an abstract winding point.

## 10. Two vertex-disjoint terminal four-blocks are impossible

Suppose Q_1,Q_2 are vertex-disjoint and both satisfy the terminal
private-degree hypotheses. If any unit of Q_1 contained O closed,
it would be an actual outside E forbidden by the closed-origin
theorem for Q_2. The same argument reverses the two. Thus all eight
block units avoid O, and Section 9 supplies two actual nonzero-winding
outer rings, each with zero whole-unit inner capacity.

Use their common selected physical plane embedding, in sufficiently
small neighborhoods avoiding O. Since the two blocks have disjoint
vertices, their simple ring curves are disjoint. Both enclose O, so
one lies inside the other's bounded side. Choose an actual unit center
on the inner ring. It is strictly inside the outer embedded cycle and
has positive distance from all closed outer ring units. The outer
center/contact homotopy can therefore be chosen to avoid it. The
connected open interior of this actual inner-ring unit avoids every
outer occupied path, so the outer contact loop encloses its whole
unit interior. This contradicts its zero whole-unit capacity.

The usual coincident-contact alternatives do not create an exception:
a four-contact polygon with a repeated vertex has inner area strictly
below one, while a simple nonzero-winding embedded cycle can be
approximated in the stated actual physical neighborhoods. This is
the full area/embedding argument of the accepted four-ring theorem.
It does not give a physical meaning to a region occupied by a routing
disk, nor does it replace a body by its center for capacity counting.

The disjoint-terminal-block corollary is proved with every intervening
force and every original circle mask retained.

## 11. Exact C3.344.b0 consequence and retained bouquet

The original no-bridge cell has one triangle and two four-body blocks,
with exactly `1+2+3+3=9` positive bodies. A block-cut tree with three
blocks either has a common articulation, or has one middle block with
two distinct attachment roots.

If the middle block is the triangle, the two terminal four-blocks are
vertex-disjoint. Section 10 excludes the whole arrangement, including
all actual middle-triangle moments, root circle masks and private
four-block load subsets.

If a four-block is middle, the terminal intact triangle has an actual
origin-interior root A by ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md. The
other terminal four-block is attached at a distinct root of the middle
block and does not contain A. The already accepted open-origin
terminal theorem, or the stronger theorem above, excludes that entire
arrangement.

Thus all non-bouquet arrangements of C3.344.b0 are excluded. The
common-root bouquet still has its actual origin-interior articulation
inside both four-blocks and is not an outside E for either. That whole
remaining bouquet is explicitly not claimed closed by this source.
No fine label, coarse count, Lean file, CI result or remote state is
changed here.
