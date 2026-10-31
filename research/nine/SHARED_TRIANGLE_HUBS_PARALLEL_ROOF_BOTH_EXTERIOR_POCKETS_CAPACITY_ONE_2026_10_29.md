# Shared triangle hubs behind a parallel roof: each whole exterior pocket has capacity one

Date: October 29, 2026 UTC. Author: shared_terminal continuation.

**Status: complete proposed uniform hand theorem, frozen for full separate
review.** A force-free half-plane and circle-measure argument bounds each
whole exterior pocket of the shared-hub, parallel-roof feature by one
additional actual unit. The proof retains every shared mean and every
physical mask. It supplies the individual pocket capacities left open by
the recovered shared-rectangle theorem; it does not yet exclude the entire
three-extra allocation in either original D02.L135 or D02.L1345.

The main physical theorem below also applies without a second hub or any
force equation, whenever its actual three-unit chart and pocket are given.

## 1. Exact physical chart and complete pocket theorem

Keep actual closed unit squares with pairwise disjoint open interiors in
the unchanged disk D_R about O=0, with

    2<=R<=sqrt(Q), Q=1105/256,
    d=sqrt(R^2-1/4)-1, a=d-1.

In one orthonormal frame suppose the actual units V,A are

    V=[d,d+1] times [-1/2,1/2],
    A=[a,d] times [h,h+1], -1/2<h<1/2.                (1)

Let B be a distinct actual physical boundary unit. Assume the following
whole physical statements:

    S=(a,h+1) belongs to B,
    A intersect B={S},
    min_B y>h, max_B x<d.                             (2)

B's true degree, total circle load, original contact owners and all
other forces are arbitrary. Its circle contact may have zero coefficient.
No equation at B is used.

Choose either actual V circle corner z_V=(d+1,+/-1/2) and any actual B
circle corner z_B. Put G=(d,1/2). Define the upper occupied crosscut

    z_V -- G -- (d,h+1) -- S -- z_B.                  (3)

Close it by the upper counterclockwise containing-circle arc from z_V to
z_B. The proof below establishes that this is a simple closed physical
loop with an unambiguous upper arc. Its bounded side is the upper pocket.
Every actual further unit assigned to that pocket is kept as a whole
square; its open interior lies on the bounded side and its closure stays
there. Additional occupied barriers can only reduce the available region.

**Theorem A.** The upper pocket contains at most one further actual unit
square. Every point of its closed bounded region has norm strictly greater
than 1/2. The theorem includes either original V corner, every actual B
circle corner, every B physical mask, and every weak contact of an extra
with the occupied boundary.

Reflection in the horizontal axis gives the identical lower-pocket result.
These are statements about the actual whole regions and physical units,
not merely their center directions.

## 2. Every actual return point lies in one fixed open half-plane

First the complete radius interval gives

    -1/15<a<1/60, d>9/10.                            (4)

Indeed at the low endpoint
`15/4-(29/15)^2=11/900>0`, and at the high endpoint
`(121/60)^2-(Q-1/4)=31/57600>0`. These imply d>14/15 and
d<61/60, stronger than the other bound displayed in (4).

Write c=(c_x,c_y) for B's actual center. Its actual point S is at distance
at most 1/sqrt(2) from c. Since 1/sqrt(2)<17/24, (4) gives

    -31/40<c_x<29/40,
    |c_x|<31/40.                                    (5)

For example the lower bound is exactly
`-1/15-17/24=-31/40`; the upper one is
`1/60+17/24=29/40`.

Since min_B y>h and every unit has vertical half-width at least 1/2,

    c_y>h+1/2>0.                                    (6)

Physical circle contact and the half-diagonal bound give

    |c|>=R-1/sqrt(2)>31/24.

Consequently (5)--(6) imply the strict bound

    c_y^2>(31/24)^2-(31/40)^2=(31/30)^2,
    c_y>31/30.                                      (7)

Now use the fixed actual-coordinate vector v=(5,14). Every point z of
the whole B satisfies

    v.z >= v.c-|v|/sqrt(2)
         > -5*(31/40)+14*(31/30)-sqrt(221/2)
          =1271/120-sqrt(221/2)>0.                  (8)

The final strict comparison has the exact positive squared reserve

    (1271/120)^2-221/2=24241/14400>0.

Both sides being compared are positive. Thus the entire unchanged B,
including all its sides, all its corners and every original mean, lies
strictly in the same half-plane

    5x+14y>0.                                      (9)

Two auxiliary consequences will identify the original upper circle arc.
For all z in B, (5),(7) and the half-diagonal bound give

    |z_x|<31/40+17/24=89/60<3/2,
    z_y>31/30-17/24=13/40>0.

Hence every actual B circle corner obeys

    (z_B)_y>sqrt(7)/2.                              (10)

These are physical statements about all circle corners, independent of
which coefficients are positive.

## 3. The full original loop and strict half-disk clearance

The first segment in (3) lies in V and, away from G, has x>d. The next
two lie on A's actual right and top sides. The last lies in B. The
strict max_B x<d makes B and V closed-disjoint. The only possible A--B
intersection is S by (2). Thus the crosscut is simple and has only its
two endpoints on the containing circle. The strict inequalities
h<1/2<h+1 cover both V-corner choices without a collapsed A segment.

The complete crosscut lies in the open half-plane (9). At either V
circle corner,

    v.z_V>=5(d+1)-7>0,

using d>9/10. Also v.G=5d+7>0. The entire right A segment has x=d
and y>=1/2. The entire upper A segment has x>=a>-1/15 and
y=h+1>1/2, so v.z> -1/3+7>0 there. The last segment lies in the
whole B, already covered by (8).

The open v-positive semicircle has its usual angular lift

    -atan(5/14)<theta<pi-atan(5/14).                 (11)

Both V-corner directions lie in it by the preceding positive projection.
Every z_B lies in it by (8) and in the upper semicircle by (10). Its
angle is strictly greater than either z_V angle: if it is in the second
quadrant this is immediate; if in the first, its y coordinate is greater
than 1/2 while the equal-radius V corner has y=1/2. The upper interval
between the chosen endpoints is therefore contained in (11). This is
the upper circle arc in the theorem, and the whole closed loop lies in
the same strict half-plane.

Every point of the loop has norm strictly greater than 1/2. Along A the
displayed pieces have either x=d>9/10 or y=h+1>1/2. Along either
physical boundary endpoint unit, the diameter bound from any actual
circle corner gives distance at least R-sqrt(2)>=2-sqrt(2)>1/2.
The remaining outer arc has radius R>=2.

The loop is compact, so it has a strict distance reserve above 1/2.
Its v-negative ray from O reaches infinity without meeting the loop;
hence O is on its unbounded side. The whole closed half-disk is connected
and disjoint from the loop, so is on that same side. The bounded region
has strict distance greater than 1/2. It also lies in (9), since every
point of the complementary closed half-plane can reach infinity without
crossing a loop contained in (9).

These statements concern the closed bounded region. A whole extra's
connected open interior cannot cross the actual occupied crosscut. At a
weak junction the usual compact-interior routing convention fixes its
bounded-side label first and retains the full square by closure. The
present physical crosscut uses actual A/V/B boundary pieces; no original
shared application is moved to G or S in a force equation.

## 4. A global arc sum inside that half-plane excludes two extras

Set rho=5/4. The complete sharp quarter-clear arc theorem gives, for
any contained actual unit K with dist(O,K)>=1/4,

    measure{theta:rho*(cos theta,sin theta) in int K}>=Lambda,
    Lambda=pi/2-2 asin((sqrt(1105/512)-1)/(5/4))>4/5.  (12)

The final strict rational lower bound is the complete Section 5 estimate
of the physical-boundary centered-arc source. That estimate concerns the
constant Lambda itself, so it also applies to a quarter-clear unit that
has no physical circle contact. Its use does not impose a boundary mask
on an extra. No centered-arc or center-angle routing assertion is needed
for the following measure sum.

Suppose two distinct actual extras E_1,E_2 occupy the upper pocket.
Section 3 makes each whole unit strictly half-disk clear and contained
in (9). The actual B is also half-disk clear and is wholly in (9).
The three actual open-square intersections with the radius-rho circle
therefore lie wholly in the same open semicircle (11), and each has
measure at least Lambda>4/5.

The radial V contributes an additional explicit interval in that same
semicircle. On the radius-rho circle its open square intersection is
exactly

    -asin(2/5)<theta<asin(2/5).                      (13)

Indeed its y bounds give those endpoints. On that arc the x coordinate
is at least sqrt(21)/4>d, while its maximum 5/4 is below d+1. The first
comparison follows from d<61/60 and
`21/16-(61/60)^2=251/900>0`. Thus no additional x cutoff is omitted.

Since atan(5/14)<asin(2/5), the part of (13) in (11) has length

    asin(2/5)+atan(5/14)>3/4.                       (14)

Here is a fully exact check. Integrating
`(1-t^2)^(-1/2)>=1+t^2/2` and
`(1+t^2)^(-1)>=1-t^2` on the respective positive intervals gives

    asin(2/5)>2/5+4/375,
    atan(5/14)>5/14-125/8232.

Their sum exceeds 3/4 by exactly 2701/1029000. The comparison of the
two angles follows also from `25/221<4/25`, by comparing their sines.

All four actual open square interiors V,B,E_1,E_2 are disjoint. Their
displayed circle subsets in one open semicircle must therefore have
total angular measure at most pi. But (12)--(14) give a total strictly
greater than

    3*(4/5)+3/4=63/20>22/7>pi,
    63/20-22/7=1/140.                               (15)

This contradiction proves Theorem A. The whole actual arcs of all
three other units are used; no free interval is guessed from their
center directions and no part of an extra is cut off.

## 5. Complete shared-hub parallel-roof entry

The preceding physical theorem has the following full-star application.
Let actual A,D be genuinely unloaded with entire positive neighborhoods
{D,V,B} and {A,V,C}, respectively. Let V have exactly its two positive
neighbors A,D and strictly positive total circle load. Suppose the
original A-to-V and D-to-V normals are equal to one direction e, and
the actual A--D intersection has positive length. Keep the actual B,C
as distinct physically boundary units of arbitrary further degrees and
loads. Every original positive coefficient and full shared-side mean
remains unchanged.

### 5.1. Every actual V mask gives the radial S roof

Let its full circle resultant be F_V. Its full equation gives
F_V=(mu+nu)e, mu,nu>0. If V has a unique physical circle corner,
that corner is parallel to e and its opposite vertex is the unique
minimum-e point of V. If V has two physical circle corners and their
weights are unequal, the direction of their full resultant strictly
exposes one inner V vertex as the minimum-e point. These statements
include a zero individual coefficient in a physically two-corner mask.

In either of those alternatives both actual roof applications are the
same point P, and both A,D maximize e at P. Positive-length A--D contact
makes their frames identical modulo quarter turns. If e is not one of
their axes, their maximizing offsets are identical, so their equal
maximizing point would force their centers to coincide, impossible.
If e is one of their axes, their maximum-e sides can have only a common
endpoint: positive side overlap would put their interiors on the same
side and make them overlap. Thus P is a vertex of both A and D.

The alleged V minimum is a vertex in these alternatives, and e strictly
exposes it in V. Each roof intersection is therefore a physical singleton
at two actual vertices. But its retained normal e is an A/D side axis,
contradicting the common strict point-only vertex/vertex convention.
This covers the entire common-application alternative, including an
endpoint-valued mean elsewhere on the shared A--D side.

The remaining physical V mask is the radial S square with equal positive
circle coefficients. After rotating e to East, it is exactly V in (1).
This mask conclusion uses V's actual full equation and all its physical
corners. It is not an imposed symmetry of the force means.

### 5.2. The actual shared pair is the complete aligned stack

The identical A,D frames and their common maximum East support d make
their centers have equal East coordinate. Write their center displacement
as +/-u+delta w in their shared orthonormal axes, with |delta|<1, where
u is normal to their actual positive shared side. If East were not an
own axis, both maximum points would be unique vertices. Their displacement
would have length

    sqrt(1+delta^2)>1,

because the zero East component forces delta nonzero. Both vertices
belong to V's one-unit inner side, impossible. Thus East is an own axis;
the shared side is horizontal and delta=0. Label the upper hub A. The
whole actual stack is therefore

    A=[a,d] times [h,h+1],
    D=[a,d] times [h-1,h],
    -1/2<h<1/2.                                    (16)

The initial closed bounds on h follow from contact with V. Either equality
would make one roof contact a point-only pair of aligned vertices with
normal East, again violating the strict singleton convention. Thus both
actual roof intersections have positive length. All original means are
retained in their full closed intervals:

    p_AV=(d,y_A), y_A in [h,1/2],
    p_DV=(d,y_D), y_D in [-1/2,h],
    p_AD=(a+x,h), x in [0,1].                        (17)

No y_A,y_D or x is set to a selected convenient value. In particular
both roof means may coincide at (d,0) when permitted by the full equations.

### 5.3. Full hub balance gives the exact two return vertices

Let gamma>0 be the unchanged A--D magnitude. The full unloaded equations
are

    mu East-gamma North+F_AB=0,
    nu East+gamma North+F_DC=0.

Hence F_AB=(-mu,gamma) and F_DC=(-nu,-gamma). Their two components
are strict, so they expose respectively the actual vertices

    S_B=(a,h+1), S_C=(a,h-1).                        (18)

The original A--B and D--C intersections are physical singletons at those
points. The complete minimum-support span lemma for a unit says that,
at a minimum-n support point p, projection in a unit direction u with
u.n<0 has strict forward reach less than one. It covers vertex supports,
relative side points and side endpoints. Applying it at S_B with u=East
and u=South gives precisely

    max_B x<d, min_B y>h.

Reflection gives max_C x<d and max_C y<h. No full equation at B or C
has been shortened. Thus Theorem A applies to the upper V--A--B loop
and its reflection applies to the lower C--D--V loop, for all actual
original means in (17).

**Theorem B.** In this entire shared-hub, parallel-roof domain each of
those two whole exterior pockets has unit capacity at most one. Their
combined capacity is at most two. The individual statement covers every
mask, mean endpoint and positive force ratio allowed by the stated stars.

## 6. Literal original D02 applications and the remaining joint problem

Keep the full original rim 01,12,23,34,45,50 and chord02. In both
original load rows L135 and L1345 use

    A=0, D=2, V=1, B=5, C=3, N=4.

A,D are genuinely unloaded degree three, V is genuinely loaded degree
two, and B,C are genuine loaded boundary units. In the full feature that
the actual A--D intersection has positive length and the two original
roof normals agree, Section 5 supplies all physical chart hypotheses.
The two actual original exterior routes are V--A--B and C--D--V.

Both A and D are physically clear in (16): their corner norms squared
are strictly below `(61/60)^2+(3/2)^2<4<=R^2`. The compatible exterior
cycle and protected circle spokes identify their upper/lower circle
closures with the actual loops of Theorem A. All other actual component
circle directions occur on the complementary B-to-C route. Additional
zero-stress contacts may subdivide these pockets but cannot enlarge them
through their occupied boundaries. The three original extras remain.

This proves the whole individual hub-pocket capacities for both load
rows and all their full-data graph-preserving reflections. It does not
declare the full rows closed. With both hub pockets of capacity one,
three extras can still require one in each and one in a remaining
central or B--N--C region. The relation between those remaining regions
and simultaneous occupation of both hub pockets needs a separate joint
proof. In L1345 the real N is loaded and is never called a transmitter.

Other A--D owner features and nonparallel roof normals also remain outside
Theorem B. No original fine/coarse flag or denominator is changed here.

## 7. Exact inputs, provenance and verification boundary

The center cap, common half-plane, complete physical loop, arc sum, shared
stack entry and original feature joins are proved above. The quantitative
arc inputs and support convention are used at their stated scopes:

| Complete input | SHA256 | Exact use |
| --- | --- | --- |
| SHARP_QUARTER_CLEAR_RADIUS_FIVE_QUARTERS_ARC_AND_INTERVAL_CAPACITY.md | bca528af5320cc8314839eb0d53cf6f15ec381ac42d5bd353f62a27a47101f67 | Whole actual open-circle angular measure at least Lambda; no presumed center routing |
| BOUNDARY_UNIT_CENTERED_RADIUS_FIVE_QUARTERS_ARC.md | a431e5073be53ccc82dfc0e9924ca55db2cd51f53cbef1dad52fd90d890116e1 | Section 5 only, the complete constant bound Lambda>4/5 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete radius-free minimum-support strict span, with all actual side points |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full stars, strict point-only convention, every physical mask and full shared mean |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original D02 graph/load roles and all retained extras |

The recovered historical manuscript
`SHARED_TWO_HUB_RADIAL_ROOF_RECTANGLE_HALF_DISK_POCKETS_AND_JOINT_ANGULAR_BUDGET.md`
motivated the chart and occupied-loop form. Its missing individual hub
capacity is proved here by the new fixed half-plane and arc argument.
It is not needed as a missing operative dependency: the actual chart,
both circle-corner choices, whole loop and half-disk clearance are printed
above. The full-mask parallel-roof entry likewise covers coincident means
directly and does not invoke an unpublished classification.

Exact rational arithmetic corroborated the displayed three new reserves
24241/14400, 2701/1029000 and 1/140. The proof is over the whole continuous
physical domain. No pose sampling, new packing certificate, force deletion,
normal reselection, application change, compilation, CI, remote write or
merge was used. A separate full independent review remains required.
