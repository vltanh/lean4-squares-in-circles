# A far four-spoke unloaded end cannot share its boundary return side

Date: October 28, 2026 UTC. Authors: root and h4_parallel continuation.

**Status: complete proposed hand exclusion of the entire shared-DE
interface below, frozen for full root and separate independent review.**
It closes the whole positive-length shared-DE interface of the original
four-load H4_D0.L0124 family. It does not close that whole load family,
its graph parent, or the three-load family. Every original shared-side
mean, actual support normal, true degree, force and physical circle mask
is retained.

## 1. Original whole scope and the stronger far-angle premise

Retain the same original nine actual contained unit squares and their
unchanged circle origin O, in

    79/40<=R<=sqrt(1105)/16.

The entire positive six-body component is

    HA,HB,HC,HD,AB,BC,CD,DE,EA,
    (A,B,C,D,E)=(0,1,2,3,4).

H is the actual unloaded degree-four hub. D is unloaded of true degree
three, with exactly the positive neighbors H,C,E. C is true loaded3,
and E is true loaded2 with neighbors D,A. The original H--E physical
closed-disjoint restriction remains. The actual H--C contact remains.
No additional force is discarded at any of these units.

Assume A physically touches the circle, D is physically circle-clear,
and all three unchanged additional squares are in the genuine closing
C--D--E exterior pocket. Thus A,B,C,E are four actual physical boundary
units. A may have zero total circle load. Assume also that the actual
minor center angle of C and E satisfies

    gamma>=5*pi/6.                                      (1)

**Theorem.** The original physical D--E intersection cannot have
positive length.

In H4_D0.L0124 all of these premises follow at the actual end D from
the full loaded boundary path E--A--B--C and the existing original
occupied-pocket reduction. Its actual gamma is strictly greater than
5*pi/6, so the weak endpoint in (1) is more than sufficient.

For H4_D0.L124 the theorem applies only when the chosen actual end has
both the stronger angle (1) and the other unloaded end A physically
boundary. The balanced-three theorem by itself guarantees a weaker
angle, and this source does not replace it by (1). The refinement
with both unloaded ends physically circle-clear remains outside the
genuine E2 boundary-neighbor argument below.

## 2. The full D3 and actual H--C triangle give an exhaustive feature cover

Suppose DE has positive shared length. Its normal is an own axis of
both actual units. Rotate and translate the physical chart so that

    D=[0,1]^2, n_DE=West,
    E=[-1,0] times [v,v+1], P_E=(0,e),
    0<=e<=1, v<=e<=v+1.                                (2)

The entire original shared interval, its true mean e and either mean
endpoint remain. The actual circle origin has coordinates (X,Y) in
this chart; it is not moved to D's center or an application.

First suppose one of n_DH,n_DC is an own axis of D. If it is North
or South, the full vertical force balance, since DE is West, forces
the other normal to have a strictly opposite vertical component. But
the physical triangle DHC forbids a negative dot product between a
D-owned side normal and its touching return neighbor's normal.
For completeness, at a North support the entire first neighbor lies
in y>=1; a neighbor supported by a normal with negative y component
lies strictly in y<1, by the unit support-span argument. They cannot
touch. Reflections give the other axes.

If the axis is West, full positive D force balance makes the other
normal East; the corresponding whole neighbor units lie beyond the
opposite vertical D supports and cannot touch. If the axis is East,
vertical balance makes the other normal horizontal. West is again
excluded by those separated supports, so both are East. This is the
entire all-parallel interface, already excluded by
INNER_PENTAGON_FOUR_SPOKE_PARALLEL_UNLOADED_END_COMPLETE_INTERFACE_EXCLUSION.md.
All its original hypotheses hold here: (1) implies its far-angle
premise, A is physical boundary, and all three extras are in this
same original D pocket. Its complete proof includes shared DE means.

Thus in any remaining case both n_DH and n_DC strictly expose D
vertices. Full vertical balance makes their vertical components
nonzero and opposite. Two opposite strict D vertices cannot have
touching returned units: the standard whole-unit support-span bounds
would put any common point inside the open D. To see this directly,
strict NE support at (1,1) puts its entire neighbor in x>0,y>0,
while strict SW support at (0,0) puts its entire neighbor in x<1,y<1;
their intersection would be in int(D). The other opposite pair is
its reflection. A closed point of another unit in int(D) would force
an open-interior overlap, which is impossible.

With opposite vertical signs, the only nonopposite pair of strict
vertices is the two vertices on the same vertical D side. They cannot
both be on the left: both normals would then have negative horizontal
components, as does the positive DE force. Hence both are on the right.
Reflect vertically if necessary, keeping every physical unit and load
role, so that the actual normals and applications have the form

    P_H=(1,0), F_H=(f,-t), f,t>0,
    P_C=(1,1), F_Cpair=(s,t), s>0.                       (3)

These are the full original pair-force vectors on D, not radial circle
resultants at C. In particular both DH and DC are physical singletons
on D, while their support owners at H and C remain arbitrary.

The complete D force equation makes the original DE magnitude f+s.
Full D torque about the coordinate origin gives

    -t+(t-s)+(f+s)e=0,
    e=s/(f+s), 0<e<1.                                  (4)

This includes every original shared DE mean that can satisfy the full
three-force system. The strict inequalities are proved consequences
of the two positive horizontal force components; neither endpoint has
been discarded by a convention or a selected replacement mean.

The actual H port is on the lower/right occupied D arc. The genuine
closing D arc goes from P_C=(1,1) across the top and down the left
side to the gap-facing end of the actual DE segment. That end has
height at least e, so this physical closing arc is contained in the
complete top/left arc from P_C to the original mean P_E.

## 3. True E2 puts O below the shared mean and strictly to its right

The original occupied order is E--A--B--C, counterclockwise in the
chart (3). The physical closing circle arc runs counterclockwise
from C to E. These orientations follow from the actual inner H port
on the complementary lower/right D arc; weak/shared junctions retain
their order through the compatible physical uncrossing.

The boundary-contact moment theorem at the genuine physical E--A
edge gives a strictly positive origin moment in that order. E has
exactly its two original positive pair forces, and all circle forces
have zero origin moment. Its complete torque equation therefore yields

    det(P_E-O,n_DE)>0,
    Y<e.                                               (5)

Both C and E have center norms greater than 5/4 in the original radius
window. Since (1) implies gamma>acos(-4/5), the force-free far-center
all-port theorem applies at the unchanged actual P_C and P_E. Put
s0=1-e>0 and y=e-Y>0. Its origin-projection strip reads

    0<X-s0*y<1+s0^2,
    X>0.                                               (6)

No normal owner at C, concurrence at C, or reduced equation at H
is used in (5)--(6). The shared mean P_E remains the original one.

## 4. Every point of the upper/left D arc is farther than 3/10

The same-nine lower-radius theorem supplies R>2. Set r0=R-sqrt(2).
Every point of a physical boundary unit has norm at least r0. At
the two actual ports this gives

    X^2+(e-Y)^2>=r0^2,
    (1-X)^2+(1-Y)^2>=r0^2,
    r0^2>(2-sqrt(2))^2>17/50.                          (7)

The last strict inequality uses sqrt(2)<283/200, whose squared reserve
is 89/40000. It is independent of which physical corner has positive
weight.

The left closing segment {(0,z):e<=z<=1} is closest to O at P_E,
because Y<e, and thus has distance at least r0. On the top segment,
if X>=1 its nearest point is P_C and also has distance at least r0.
If 0<X<1, its distance is 1-Y. Were 1-Y<=3/10, both vertical port
differences e-Y and 1-Y would be at most 3/10. Equation (7) would
then force both X>1/2 and 1-X>1/2, a contradiction.

Consequently the entire actual top/left D arc between the original
means, and hence its subarc between physical gap-facing contact ends,
has distance strictly greater than 3/10 from O.

## 5. The actual whole closing pocket is also farther than 3/10

This is an occupied-boundary statement, not an inference from endpoint
distances. The entire angular shadow of each physical boundary unit
has width strictly less than pi/2: its center radius is greater than
5/4, its center circumradius is 1/sqrt(2), and the full center-cone
argument bounds each deviation strictly below pi/4.

Both P_C and P_E lie strictly above O by (5). Every upper direction
has minor angular distance strictly greater than pi/2 from the downward
vertical direction. Therefore the whole C and E angular shadows avoid
that downward ray. The complete top/left D arc avoids it too, since
all its points have height at least e>Y.

The two endpoint shadows are disjoint because their center gap is at
least 5*pi/6, greater than the sum of their two strict pi/4 cone
bounds. Cut the direction circle at the downward vertical ray. In
the lift (-pi/2,3*pi/2), both ports have upper-half-plane arguments
and

    det(P_C-O,P_E-O)=y+s0*X>0.

Their arguments, and therefore their disjoint whole shadow intervals,
are ordered C before E. Thus the actual counterclockwise closing
outer-circle arc between the gap-facing physical circle corners also
misses the cut ray.

Use the actual P_C, the gap-facing extreme of the unchanged shared
DE segment, the real top/left D subarc, paths within the actual C,E
to their gap-facing physical circle corners, and the closing circle
arc. These are the actual occupied crosscut and its boundary. The
physical uncrossing theorem supplies compatible weak-junction Jordan
resolutions without crossing an original extra's open interior.
The original pocket assignment is preserved on every compact subset
of that interior. Additional actual contacts only subdivide or remove
free regions.

Every point of the occupied boundary has norm strictly greater than
3/10, by Section 4, the endpoint-unit bound r0, and the outer radius.
The whole downward ray misses that boundary, so O is on the unbounded
side. The connected closed radius-3/10 disk misses the boundary and
lies on the same side. Compactness gives a strict additional margin,
and the compatible resolutions can be chosen within it and off the
ray. Hence every whole original extra in the genuine closing pocket
has distance strictly greater than 3/10 from O.

No auxiliary concurrence path serves as a physical barrier. Every
part used for the occupied crosscut is in the actual original units,
their boundary, or the actual outer circle.

## 6. Both H and D are near O; the H support gives a two-way bound

The exact critical-clearance theorem for the same nine units says
at least two distinct actual units have distance strictly less than

    0<delta=sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1)-1<1/4.

The four actual physical boundary units A,B,C,E have distance at
least R-sqrt(2)>3/10. The three actual extras have distance greater
than 3/10 by Section 5. Thus the two near units must be precisely
the original H and D:

    dist(O,H)<delta, dist(O,D)<delta.                    (8)

Nearness to D implies

    -delta<X<1+delta, -delta<Y<1+delta.

We already know X>0 and Y<e<1. Write the unchanged unit D-to-H
normal as n_DH=(a,-b), a,b>0, a^2+b^2=1. H lies wholly beyond
its actual support at (1,0), so (8) implies

    a(1-X)+bY<delta.                                   (9)

This inequality holds even if its left side is negative: every point
of H has that scalar displacement or larger, and a point of H within
distance delta of O gives a strict upper bound delta by Cauchy.

If X<=1-delta and Y>=delta, the left side of (9) would be at
least delta(a+b)>delta. Therefore every actual configuration in
this complete interface satisfies the disjunction

    X>1-delta  or  Y<delta.                            (10)

This is a consequence of the whole original H support and near-unit
count; it is not an assumption on a center or on a deleted force.

## 7. The actual center of C is above O in both parts of (10)

Let sigma=1/sqrt(2), and let (C_x,C_y) be the actual center vector
of C relative to O. Since P_C=(1,1) is a real point of C and its
distance to C's center is at most sigma,

    1-X-sigma<=C_x<=1-X+sigma,
    C_y>=1-Y-sigma.                                    (11)

If X>1-delta, near-D gives X<1+delta. Thus

    |C_x|<delta+sigma<1,
    C_y> -sigma>-3/4,

where Y<1 was used. Since C is physically boundary, |c_C|>5/4.
It follows that |C_y|>3/4, and the negative alternative has just
been excluded. Therefore C_y>3/4 in this entire branch.

If Y<delta, (11) directly gives

    C_y>1-delta-sigma>0,

using delta<1/4 and sigma<3/4. The two branches cover (10), so in
every case

    C_y>0.                                            (12)

No degree-two, proper-concurrence or unique-circle-mask assertion
has been applied to C. Only its actual point, whole center distance
and physical boundary status were used.

## 8. E's complete physical mask gives a second upper center and an exact radius

The true degree-two all-mask proper-concurrence lemma applies to E,
because its other actual neighbor A physically touches the circle.
It supplies

    q=P_E+ell*n_DE, ell>=0,

with q-O a positive multiple of E's full nonzero circle resultant.
Its vertical coordinate relative to O is e-Y>0. From (2), the
actual E center relative to O is

    c_E=(-X-1/2,V), V=v+1/2-Y.

If V<0, its unique farthest and hence unique physical circle corner
is the lower-left corner, since X>0. That corner has negative
vertical coordinate relative to O, contradicting the positive
vertical component of the full resultant. Thus

    V>=0.                                             (13)

When V=0 both left-side corners remain physical, and their individual
original weights may be zero. No equality or positivity of both
weights is assumed. In every physical mask, the actual farthest
upper-left corner gives the exact equation

    R^2=(X+1)^2+(V+1/2)^2.                             (14)

The concurrence need not belong to E. Its proper direction and
positive radial multiple are all that was used from the full lemma.

## 9. Two upper centers at angle at least 150 degrees violate (14)

By (12) the C center angle theta_C belongs to (0,pi). By (13) and
X>0 the E center angle theta_E belongs to [pi/2,pi]. If their minor
separation is at least 5*pi/6, it cannot be theta_C-theta_E, which
is less than pi/2. Thus

    theta_C<=pi/6, theta_E>=5*pi/6.                    (15)

Every physical boundary center has radius at least R-sigma. The
same-nine R>2 and the strict rational bounds

    sigma<5/7, sqrt(3)/2>6/7

therefore give

    C_x=|c_C|cos(theta_C)>(2-5/7)*(6/7)=54/49.         (16)

The two radical reserves are 25/49-1/2=1/98 and
3/4-36/49=3/196. Combining (11), sigma<5/7 and (16),

    54/49<C_x<12/7-X,
    0<X<30/49.                                       (17)

The E angle in (15) and V>=0 give

    V/(X+1/2)<=tan(pi/6)=1/sqrt(3)<3/5,

including V=0. The last comparison follows from 1/3<9/25.
Using (17), both positive terms in (14) consequently satisfy

    X+1<79/49,
    V+1/2<(3/5)*(30/49+1/2)+1/2=286/245.

Equation (14) now yields the exact contradiction

    R^2<(79/49)^2+(286/245)^2
        =4-2279/60025<4,

whereas the unchanged nine-unit packing has R>2.

This proves the entire nonparallel shared-DE branch. Together with
the full parallel exclusion in Section 2, every positive shared DE
feature of Section 1 is impossible, for every original mean and
physical mask.

## 10. Complete original join and precise remaining boundary

For H4_D0.L0124 the actual loaded units are A,B,C,E. The full
six-body sum is F_E+F_A+F_B+F_C=0 and the actual path is
E--A--B--C. FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md gives
gamma>5*pi/6 for its two actual endpoint centers. It assumes no
two-force equation at the loaded C3 or internal A3,B3.

The complete occupied-pentagon theorem retains all nine units,
excludes an interior extra, and places all three extras in the single
C--D--E pocket. D is physically clear, because otherwise the actual
rim would be a forbidden physical boundary five-cycle. E's other
neighbor A is truly physical boundary. Thus all hypotheses in
Section 1 are literal original conclusions and the whole shared-DE
interface of L0124 is excluded.

For L124, the same local conclusion remains valid whenever its actual
selected end satisfies gamma>=5*pi/6 and its other unloaded end A
physically touches the circle. The existing physical refinement then
empties A's two direct pockets and places all extras in the D pocket.
However the general balanced-three far-pair bound is only
pi-(1/2)acos(9/25), which is below 5*pi/6. The present proof therefore
does not close the entire shared-DE interface of L124. Nor does it
apply the E2 boundary-neighbor lemma when A is physically clear.

The D-owned singleton DE case is not asserted to be a positive-length
shared side by this source. Other return features and the complete H4
family cover remain separate obligations. No original family/parent
flag, fine/coarse count, or global theorem is closed here.

## 11. Exact sources, contributions and review requirement

| Source | SHA256 | Exact use |
| --- | --- | --- |
| INNER_PENTAGON_FOUR_SPOKE_PARALLEL_UNLOADED_END_COMPLETE_INTERFACE_EXCLUSION.md | b8bc5e9ab0f9f17c06966b228fdeeffe2f71f49e3a9b446c76898cb6b39d2dec | Entire all-parallel original-D3 branch, including shared returns and means |
| FAR_BOUNDARY_CENTER_PAIR_ALL_CONTACT_PORTS_STRADDLE_ORIGIN.md | 73aac9b69b62aabaf94971abf97a1b2903cf3a0fed1cab9e8fc380fbf96678ee | Whole actual port strip and whole-unit center cones |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Only physical boundary-edge moment Lemma 1.1 at true E2 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only full true-degree-two all-mask Lemma 2.1 at E |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual occupied order and compatible weak/shared junctions |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Degree-free owned-axis triangle and whole-unit support-span facts, restated in Section 2 |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 | Entire original graph/load domains, physical refinements and whole-extra pocket allocation |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 | Same-nine exact critical two-near-unit count |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Entire original four-load endpoint angle bound |

Root supplied the shared-DE geometric organization, the H-support
near-unit dichotomy, the two C-center sign branches and the final
aligned-E radius contradiction. H4_parallel supplied the complete
D3 feature reduction, checked the full shared means and physical masks,
and wrote the entire actual-pocket and original-caller assembly. Both
contributions are construction work. This new source requires a full
separate independent review; neither author's earlier review of a
different source supplies that review.

All numerical comparisons are printed exact rational/radical bounds.
There was no numerical pose search, sampled angle premise, new scalar
certificate or old checker replay. No selected normal, original mean,
actual body, force, or circle weight was changed. No Lean/Lake, CI,
workflow dispatch, commit, merge, ledger mutation or remote write was
used in this proof.
