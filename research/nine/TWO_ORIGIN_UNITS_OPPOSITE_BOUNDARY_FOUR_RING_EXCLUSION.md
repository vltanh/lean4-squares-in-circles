# Two origin-containing units cannot be opposite the boundary pair of a selected four-ring

Date: October 28, 2026 UTC. Root continuation, from a geometric strategy
and quantitative chart supplied by recovery_audit. Root completed and
independently rederived the physical contact classification, theta-graph
argument, endpoint bounds, and the full-radius caller below. A separate
reviewer who did not develop these arguments is required before adoption.

**Status: complete proposed geometric theorem, frozen for full independent
review.** The theorem uses whole actual squares and the existing compatible
selected graph. It does not use force equations or shorten any original
star. Its full-window consequence strengthens a necessary moment reduction
for the original D0235.L0134 family; that family remains open.

Keep the same actual unit squares with disjoint open interiors in the
unchanged disk about O, with

    79/40 <= R <= sqrt(1105)/16.                         (1)

Suppose the retained compatible positive graph has the four-ring

    E--B--F--C--E,                                      (2)

where the distinct actual units E,F both contain O and B,C physically
touch the circle. Their true degrees, other contacts, loads, individual
circle weights, original normals and actual means are arbitrary.

**Theorem.** This complete physical domain is impossible.

All other actual units remain. No new force is put on EF, even when
E and F physically touch; an auxiliary arc used below is only a drawing.

## 1. Geometric inputs and the complete E/F intersection cover

Every actual point p of a physical boundary unit satisfies

    |p-O| >= R-sqrt(2) > 11/20.                         (3)

Indeed its distance to any one of that unit's actual circle corners is
at most sqrt(2), and sqrt(2)<57/40. The complete physical angular-shadow
theorem gives every such unit a closed angular interval of width strictly
less than pi/3. These statements depend on physical boundary contact,
not on positive individual corner multipliers.

E and F are physically circle-clear: any point of either is at distance
at most sqrt(2) from its actual point O, whereas R>sqrt(2). O cannot be
an interior point of either, because it belongs to the other full square;
approximating O by interior points of the latter would contradict the
disjoint open interiors. Thus O lies on the boundary of both units.

Their physical intersection, being an intersection of interior-disjoint
convex squares, is either a singleton or a positive-length segment on a
side of each. Since it contains O, the singleton alternative is exactly
{O}. A positive-length intersection gives common side axes and is handled
in Sections 2--5. The entire singleton alternative, including vertex/side
and vertex/vertex configurations, is handled in Sections 6--8. These are
physical contact sets, independently of any selected EF force or mean.

We also use the radius-free selected-center-order lemma proved in
ROOTED_HIGH_RADIUS_TWO_NEAR_BOUNDARY_FOUR_RING_EXCLUSION.md Section 2.
For clarity, its premises are only that distinct unit centers are at
least one apart, touching centers are at most sqrt(2) apart, and the
selected graph does not contain both crossing opposite pairs of one
aligned four-unit junction. A crossing of two selected center edges
would force exactly that aligned 2-by-2 junction. A four-cycle is then
convex apart from its exact aligned T endpoint. Consequently, when an
opposite pair of centers is at distance less than two, the other pair
lies strictly on opposite sides of their line. The T endpoint is
included: its length-two opposite pair cannot be the given pair, and
the other diagonal still separates the two remaining centers strictly.
No high-radius estimate from that source is used in this center lemma.

## 2. Shared E/F side: an exact chart with O retained

Assume the E/F intersection has positive length. Rotate their own axes,
possibly reflect horizontally, and exchange their names so that

    E=[h-1,h] x [0,1],
    F=[h+delta-1,h+delta] x [-1,0],
    0<=delta<1, 0<=h<=1-delta.                         (4)

The horizontal overlap is [h+delta-1,h], of positive length 1-delta.
The closed h interval follows precisely from O=(0,0) belonging to both
units. A rotation by pi followed by exchanging E,F replaces h by
1-delta-h and keeps delta. We shall use that symmetry only on the whole
actual configuration.

Let J be any actual common neighbor of E,F. Its y=0 slice is nonempty,
since it has points of nonnegative and nonpositive height. This slice
cannot meet the open common segment (h+delta-1,h) x {0}. At any such
point the union E,F occupies a full neighborhood on both vertical sides
of their common side; an interior approximation within J would overlap
one of them. The slice is convex, so it lies entirely in one of

    x>=h, or x<=h+delta-1.                            (5)

Call these the right and left classes respectively. A single J cannot
belong to both, because the two closed intervals in (5) are disjoint.
We give the complete right-class classification; the rotation/exchange
above gives the left class without changing any square or contact.

## 3. Every right-class common neighbor: all frames and endpoints

First every actual point z of J intersect E has x=h. To see this,
choose q in J with y=0 and q_x>=h. If z_x<h and z_y=0, the right-slice
condition already fails. If z_x<h and 0<z_y<=1, the segment from z
toward q enters the open rectangle E: near z its x coordinate is
strictly between h-1 and h, and its height strictly between zero and
one. This includes the possible z_x=h-1 or z_y=1 endpoints. Convexity
of J then contradicts its interior disjointness from E.

The whole J in fact lies in x>=h. If one E contact (h,v) has 0<v<1,
the actual E side interior forces this supporting half-plane directly.
At v=0, E and F both occupy points immediately to the left, above and
below the endpoint (h,0). Any J point with x<h would give a segment
from this endpoint entering one of those open rectangles, so is again
impossible. These statements include delta=0.

The sole remaining E contact can be (h,1). Choose any physical common
support there. Its E-to-J normal lies in the closed Northeast cone.
If its y component were positive, the complete unit support-span lemma
would give J a strictly smaller than one downward reach from (h,1).
It could not touch F, whose points all have y<=0. Thus a horizontal
East support is necessary, and again J lies in x>=h. This uses only
physical separation; no original force normal is replaced.

If J is nonparallel to the displayed axes, its unique minimum-x vertex
and entire actual frame therefore have the form

    V=(h,v), 0<=v<=1,
    J=V+[0,1](c,-s)+[0,1](s,c),
    c,s>0, c^2+s^2=1.                                (6)

Touching F requires v<=s<1. If delta=0, only V can lie on x=h,
so its actual F contact forces v=0.

Suppose delta>0. Every F contact has y=0. Indeed J has x>=h, and
its minimum height v-s is strictly above -1. A contact at negative
height could consequently be only on F's right side x=h+delta.
The segment toward V=(h,v), with v>=0 and h<h+delta, would then
enter int F near that contact. This contradiction excludes every
negative-height F contact, including either possible right-side owner.

If v<s, the left endpoint of the actual y=0 slice is

    (h+c*v/s,0).

If c*v/s<delta, points immediately below that endpoint along the
downward-right edge would enter int F. If c*v/s>delta, the whole
slice would miss F. Therefore c*v/s=delta, which also implies delta<c.
If v=s, the slice consists of the actual lowest vertex (h+c,0);
it belongs to F exactly when c<=delta. The two full cases, including
their common closed endpoint, are precisely

    v=s*min(1,delta/c).                              (7)

For aligned J, write J=[h,h+1] x [k,k+1]. When delta>0, an actual
negative-height portion would overlap F in their positive horizontal
overlap; touching F therefore forces k=0. When delta=0, their vertical
side intervals only have to meet both E and F, giving -1<=k<=0.
Thus the complete aligned cover is

    delta>0: J=[h,h+1] x [0,1],
    delta=0: J=[h,h+1] x [k,k+1], -1<=k<=0.          (8)

No force application or shared-side mean has been chosen in (4)--(8).
They describe whole physical common neighbors, including singleton
contacts at every closed vertex/side transition.

## 4. Selected center order places the boundary neighbors in the two classes

The line through the actual E,F centers is

    x+delta*y = h+(delta-1)/2.                        (9)

For the nonparallel right neighbor (6), its center's left side minus
the right side of (9) is exactly

    [1-delta+(1+delta)c+(1-delta)s]/2 + delta*v > 0.   (10)

For the aligned alternatives (8) it is exactly one. The left-class
centers are strictly on the other side, by the whole rotation/exchange.

The actual E/F center distance is sqrt(1+delta^2)<sqrt(2)<2.
The selected-center-order lemma from Section 1 therefore puts c_B,c_C
strictly on opposite sides of (9). Since each is a physical common
neighbor and has the complete classification (5), exactly one is a
right-class neighbor and exactly one a left-class neighbor.

Apply the legitimate rotation/exchange if necessary to arrange

    0<=h<=(1-delta)/2.                              (11)

There is still a physical boundary common neighbor in the right class.
Denote that actual unit by J and retain its entire frame and contact
parameters. We show it is too close to O to touch the circle.

## 5. A full corner bound: every right-class J lies in radius sqrt(15)/2

For (6), two potentially farthest corners suffice:

    U=V+(s,c),
    T=V+(c,-s)+(s,c).

V has no larger norm than U, because both coordinates of V are
nonnegative and increase to those of U. The other corner Q=V+(c,-s)
satisfies

    |T|^2-|Q|^2=1+2s*h+2c*v>0.

All corner x coordinates are nonnegative. Their squared norms increase
with h, so (11) permits the uniform upper comparison h=(1-delta)/2.

On 0<=delta<=c, (7) gives v=(s/c)delta. The coordinates of U and T
are affine in delta. Their squared norms are convex on that entire
closed interval, so their maxima occur at delta=0 or delta=c. For
c<=delta<1, v=s is fixed and their nonnegative x coordinates decrease
as delta increases; the same upper endpoint value delta=c suffices.

At delta=0 the two exact squared norms are

    |U|^2=5/4+s<=9/4,
    |T|^2=9/4+c+s<15/4,                              (12)

using c+s<=sqrt(2)<3/2. At delta=c they are

    |U|^2=9/4-c/2-3c^2/4+(1+c)s <=15/4,
    |T|^2=5/4+c/2+c^2/4+(1+c)s <=7/2.                (13)

For the first comparison use s<=1 and cs<=1/2 and drop the two
nonpositive terms. For the second also use c<=1 and c^2<=1. These
closed inequalities cover the whole physical interval without an
angular subdivision or an assumed mean value.

For either aligned row (8), h<=1/2 and every point has |y|<=1,
so its farthest squared corner norm is at most (3/2)^2+1=13/4.
Therefore every corner in the entire right class satisfies

    |z|^2 <=15/4 < (79/40)^2 <=R^2,
    (79/40)^2-15/4=241/1600>0.                       (14)

The norm squared is convex on the square, so the same strict circle
clearance holds for all of J. This contradicts J's actual physical
boundary status. The entire shared E/F intersection is excluded.

## 6. Singleton E/F contact: two actual free gaps and the plane theta graph

Now E intersect F={O}. Each actual tangent sector at O has angle
pi/2 at a vertex or pi at a side interior. Two side-interior sectors
would be complementary half-planes with a common side interval, so
cannot occur here. If a boundary ray of the two remaining sectors
coincided, the two unit sides from O would give a positive-length
intersection. Thus the two complementary free tangent gaps are both
strictly positive.

Add the auxiliary geometric arc

    center(E)--O--center(F)                           (15)

to the actual selected four-ring drawing. Its two open segments lie
inside E and F. It is disjoint from the actual B,C and their contacts:
B,C avoid O by (3), and their closed squares cannot meet int E or
int F. It carries no force and changes no selected edge or application.

Use the existing compatible physical routing at any coincident contact
of the selected ring. The actual E--B--F path and E--C--F path can
be routed as internally disjoint simple arcs with centers E,F fixed.
The auxiliary arc (15) is disjoint from those routes apart from the
two centers. To justify preservation even at a weak contact, each
selected contact point lies in E or F and in the relevant boundary
unit, so differs from O. A radial segment from the center of E to
its boundary point meets the radial segment toward O only at the
center, and the same holds in F. Thus finite contact-routing disks
can be taken disjoint from (15). The three arcs form a plane theta
graph with the unchanged E,F sectors at O.

Both B and C are on its unbounded face. The actual segment from a
boundary center to any of its physical circle corners, extended
outside the disk, gives its circle access. Its interior lies in that
unit and meets neither other units' open center/contact arcs nor
(15). Its circle corner cannot be an E or F contact, because E,F
are circle-clear. The finite compatible routing can preserve these
circle accesses, exactly as in the original simultaneous-access
construction. The selected contact neighborhoods themselves remain
strictly inside the disk.

In a plane theta graph, if the internal vertices B and C of two of
its three arcs both belong to the unbounded face, those two arcs
form that face's boundary. The third arc lies between them. Thus
the two bounded theta faces are the E--B--F face and E--C--F face,
one on each side of (15). Near O, these faces contain the two
different free tangent gaps between E and F. Indeed the two radial
directions in (15) lie strictly within the respective tangent sectors;
each of the two angular intervals between them contains exactly one
of the free gaps.

Fix a direction strictly in one of those gaps. Its ray never enters
either whole E or whole F: both units lie in their own tangent cones
at O. Initially the ray lies in the associated bounded theta face.
It must exit that bounded face and cannot do so through an arc in E
or F or through (15). It must therefore meet the corresponding
boundary unit B or C.

This last statement remains a statement about the actual unit at a
weak routed contact. For the fixed strict gap direction, its angular
distance from the closed tangent cones of E and F is positive.
All contact-routing neighborhoods on the face boundary are centered
at actual E or F points different from O. They can be taken too
small to meet this ray. Its exit is then on the unchanged path
portion inside the corresponding actual B or C. No artificial
routing point is substituted for a physical point of that unit.

It follows that each full open gap is contained in the angular shadow
of its corresponding boundary unit. The shadow is closed, so its
closure contains the gap endpoints as well. By the strict shadow
theorem, each of the two gap widths is strictly less than pi/3.

## 7. Two vertex sectors are impossible

If O is a vertex of both E and F, their two occupied sectors have
total angle pi. The two positive free gaps therefore have total
angle pi. Section 6 would put each below pi/3 and their sum below
2pi/3, a contradiction.

This includes every pair of nonparallel vertex sectors and the
opposite aligned sectors. The excluded zero-gap positions were
already handled by the positive-length shared-side case.

## 8. A side-interior sector and a vertex sector are impossible

It remains that O is in a side interior of one square, say E, and
is a vertex of F. In actual own coordinates write

    E=[-a,1-a] x [-1,0], 0<a<1.

The two inward axes of F have angles theta and theta+pi/2, where
0<theta<pi/2. Its actual tangent sector lies above E. The right
free gap is (0,theta), and the left gap is (theta+pi/2,pi).
The two strict shadow bounds give

    pi/6<theta<pi/3.                                 (16)

Let B_R and B_L denote the actual boundary neighbors associated
to these right and left gaps. Choose actual E-contact points p_R
and p_L with those units. They are nonzero by (3), lie in the lower
half-plane, and satisfy (3) themselves.

The angular shadow of B_R is a single interval of width less than
pi/3 containing the entire closed direction interval [0,theta].
Its direction of p_R must consequently lie in

    (theta-pi/3,0].

It cannot use another lower-half-plane lift because the same short
interval already contains both 0 and theta. Therefore

    (p_R)_x > (11/20) cos(pi/3-theta).                 (17)

Likewise the shadow of B_L contains [theta+pi/2,pi], so its direction
of p_L lies in [pi,theta+5pi/6). Consequently

    -(p_L)_x > (11/20) cos(theta-pi/6).                (18)

The two nonnegative angles in (17),(18) sum to pi/6. Concavity of
cosine on [0,pi/6], or the exact sum formula with its symmetric
endpoint minimum, gives

    cos(pi/3-theta)+cos(theta-pi/6) >= 1+cos(pi/6).

But E's actual horizontal interval has length exactly one, whereas

    1 >= (p_R)_x-(p_L)_x
      > (11/20)(1+cos(pi/6))
      > (11/20)(1+5/6)=121/120>1.                    (19)

Here cos(pi/6)=sqrt(3)/2>5/6, with squared reserve 1/18. This is
a contradiction through the entire angle interval (16), not just
its endpoints. All physical E-side positions a and every original
contact mean remain; the two points were used only as actual points
of the unchanged E and boundary units.

Sections 2--8 exhaust the entire E/F intersection cover and prove
the theorem stated above.

## 9. Full-window two-near four-ring theorem and the original moment caller

Put

    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose in the selected actual four-ring (2) both E and F meet the
closed disk D_epsilon, while B,C are physically boundary.
If d<=1, epsilon=0, so both E and F contain O and the present theorem
applies. This includes the exact critical radius R=sqrt(17)/2.
If d>1, the complete high-radius two-near four-ring theorem applies
at its own literal strict radius range. Thus the same four-ring is
impossible throughout the entire original window (1), with every
physical mask, shared mean, weak junction and true degree retained.

For the unchanged original M6.B6.HEXAGON.D0235.L0134 graph, the
accepted nine-unit boundary-triangle theorem gives the exact original
torque parameters

    m_01=m_12=x>0, m_34=m_45=y>0,
    m_23=m_50=r, m_02=r-x, m_35=r-y.

It proves throughout (1) that r<=x forces unit 2 to meet D_epsilon,
and r<=y forces unit 5 to meet D_epsilon. The actual four-ring is
0--2--3--5--0, with physical boundary opposite units 0 and 3. The
full-window theorem now proves throughout (1), including every low
and critical-radius case,

    r>min(x,y)>0.                                    (20)

This is a complete exclusion of that original continuous moment
domain, including both zero-chord boundaries. It is still a necessary
restriction, not an exclusion of the surviving r>min(x,y) domain.
No original fine or coarse flag changes. The actual unloaded 2 and 5
retain their true degree three; the loaded 0 and 3 retain degree
three; loaded 1 and 4 retain degree two. All six original rim edges,
both original chords, all nine squares and all three extras remain.

## 10. Exact direct source pins and review boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Complete physical boundary angular shadow, with zero individual circle coefficients allowed |
| ROOTED_HIGH_RADIUS_TWO_NEAR_BOUNDARY_FOUR_RING_EXCLUSION.md | f31c67f46c3d4318d67c887afbb4ee93997ac8e587c6d7f3d5a7bdc9fcb28b10 | Radius-free Section 2 selected-center order, and Section 9's separate strict high-radius join |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Section 2's complete actual minimum-support span, without a pentagon or degree premise |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Compatible selected four-cycle routing and simultaneous physical circle accesses at weak junctions |
| NINE_UNIT_BOUNDARY_TRIANGLES_ZERO_ORIGIN_WINDING.md | cb5ec72a1199615b5f25293ef6280b6ad456ec94f0d7c495d275fc7be79c87aa | Section 9 only: exact original D0235 full-star moments and the two complete nearness implications |

This source contains no pose search, numerical geometric exclusion,
normal reselection, moved mean, false smaller star, Lean compilation,
CI, workflow, metadata change, commit or remote mutation. The geometric
strategy and quantitative chart were supplied by recovery_audit;
that collaborator cannot count as the independent reviewer of this
new source. Root's authorship and rederivation are likewise not a
separate independent review.
