# Four asymmetric central units and a complete arbitrary-block arm/leaf exclusion

Date: October 29, 2026 UTC. Author: pentagon/global continuation.

**Status: complete proposed uniform hand theorems, frozen for full
independent review.** A new force-free four-center theorem removes
the private-degree restriction from the high S-side-arm argument.
Together with the complete previous low/type and D-root theorems,
it excludes a genuine short arm and a direct genuine leaf at two
distinct roots of any actual cyclic block throughout the original
nine-square radius window. No fine or coarse flag is changed here.

All original physical squares, forces, selected normals, applications,
whole side means, circle masks, zero individual circle coefficients
and true positive degrees remain. The physical count in Sections 1--5
uses every original square, including all arbitrary completions.

## 1. A force-free theorem with four different center bounds

Let pairwise interior-disjoint actual unit squares lie in a disk
centered at O with R^2<=1105/256. Put

    a=99/140,       b=719/1000,
    c=76/105,       d_*=731/1000,
    M=91/60,       p=1309/2000.

Here d_* is just a fixed center-bound constant, distinct from the
radial leaf parameter d used later. These constants satisfy

    0<p<a<b<c<d_*<3/4<1<M.

**Asymmetric four-center theorem.** If four distinct actual unit
centers can be labeled z_a,z_b,z_c,z_d so that

    |z_a|<=a, |z_b|<=b, |z_c|<=c, |z_d|<=d_*,          (1)

then there are at most eight actual squares in total.

The entire closed domain (1) is included. This is a physical theorem
with arbitrary orientations, contacts, force data and further units.
No actual pose, contact frame, angular discretization or generated
packing datum is an input.

Every actual center z has |z|<M. In the square's own orthonormal
axes u,v, its farthest corner has squared norm

    |z|^2+1/2+|z.u|+|z.v| >= |z|^2+|z|+1/2.

The strict reserve at M is

    M^2+M+1/2-1105/256=31/57600>0.                    (2)

Distinct actual centers have distance at least one, since their
open radius-1/2 incircles are disjoint. None of the four centers
in (1) is O, and no two have the same direction: either alternative
would give distance less than d_*<1 to another named center.

For positive x,y define

    f(x,y)=(x^2+y^2-1)/(2xy).

On 0<x,y<1 this increases strictly in either variable; for example
its derivative in x has the positive numerator x^2-y^2+1.
The cosine law therefore bounds the cosine of a named pair's
minor angular separation by f of its two upper radius bounds.

We will use the following exact rational comparisons. Every entry
in the second column is positive and is strictly below its third
column, which in turn is below 3/50.

| Pair | Exact expression | Strict upper bound |
| --- | --- | --- |
| a,b | f(a,b) | 168/10000 |
| a,c | f(a,c) | 234/10000 |
| a,d_* | f(a,d_*) | 333/10000 |
| b,c | f(b,c) | 393/10000 |
| b,d_* | f(b,d_*) | 489/10000 |
| c,d_* | f(c,d_*) | 551/10000 |

All are obtained by substituting the displayed rational constants
and multiplying positive denominators. For additional precision,
the six positive upper-bound differences, in that order, are

    9721/138407500,
    299/112860000,
    24413/1688610000,
    481907/11475240000,
    403021/5255890000,
    508451/11666760000.                                (3)

The elementary bound

    arcsin x <= (501/500)x,          0<=x<=3/50         (4)

follows by integrating the derivative: its upper bound 501/500
is justified by

    (501/500)^2(1-(3/50)^2)-1=243491/625000000>0.

For negative x in [-1,0], arcsin x<=x. These two continuous
inequalities, not sampled angle values, supply all angular estimates.

## 2. Every named radius exceeds p, and every central gap is short

Order the four named center directions cyclically. Each consecutive
gap is at least the arccosine of f of its endpoint radius bounds.
If a consecutive gap exceeds pi, this remains true automatically;
otherwise it is exactly the minor angle controlled by the cosine
law. Thus there is no advance assumption that a gap is a minor one.

### 2.1. The exact common lower radius

Suppose one named radius were at most p. The other three upper
bounds, sorted increasingly, are no larger than b,c,d_*. Assign
these three larger permissible bounds to them in that order.
All relevant cosine comparisons remain valid by monotonicity of f.
The exact negative bounds are

    f(p,b)<-29/500,
    f(p,c)<-1/20,
    f(p,d_*)<-389/10000.                              (5)

The positive differences between the right and left sides are,
respectively,

    10104/117646375,
    628319/1671331200,
    461569/9568790000.

The four consecutive gap bounds sum to 2pi minus the sum of
the corresponding four arcsines. Exactly one of b,c,d_* is
opposite the proposed p-bounded center in the cyclic order.
Using (3)--(5) gives the following strict upper bounds for that
arcsine sum, over all three possible positions:

| Opposite bound | Upper bound for the four-arcsine sum |
| --- | --- |
| b | -1/20-389/10000+(501/500)(393/10000+489/10000) = -1309/2500000 |
| c | -29/500-389/10000+(501/500)(393/10000+551/10000) = -2889/1250000 |
| d_* | -29/500-1/20+(501/500)(489/10000+551/10000) = -237/62500 |

Each is negative. The sum of the four consecutive gaps would
therefore be greater than 2pi, impossible. Consequently

    p<|z_i|<=d_*               for all four named centers.             (6)

This argument includes every assignment of the four different
bounds to their actual cyclic positions and every unequal radius.

### 2.2. One bound for every consecutive central gap

Set s=16/125. We claim that every consecutive gap g satisfies

    g<pi/2+s.                                                        (7)

The other three consecutive gaps form a path visiting all four
named centers. Their lower arccosine bounds make

    g<=pi/2+sum_(three path pairs ij) arcsin f(m_i,m_j),

where the m_i are the actual assigned constants a,b,c,d_*.
The three positive cosines are all below 3/50, so (4) applies.

For completeness, the largest possible sum of these three
f-values needs no list of angular orderings. The two outside
edges of a four-vertex path form a perfect matching. For
0<A<=B<=C<=D<1 the exact identities are

    f(A,D)+f(B,C)-f(A,C)-f(B,D)
      =(A-B)(C-D)(AB+CD+1)/(2ABCD)>=0,

    f(A,D)+f(B,C)-f(A,B)-f(C,D)
      =(A-C)(B-D)(AC+BD+1)/(2ABCD)>=0.                (8)

Thus any such matching has f-sum at most f(a,d_*)+f(b,c).
The middle edge has f-value at most f(c,d_*) by monotonicity.
The table in Section 1 gives the whole path bound

    sum f(m_i,m_j) < (333+393+551)/10000=1277/10000.

Finally

    s-(501/500)(1277/10000)=223/5000000>0.

This proves (7) simultaneously for all four gaps and every order.
In particular each gap is less than 3pi/4: s<pi/4, for example
from pi>3. The four actual directions cover the full circle with
these uniformly short gaps.

## 3. Every other actual center has radius greater than one

Let z be any further center. A zero center would have distance
less than one to every named center. Otherwise (7) gives a named
center whose direction is at angular distance theta<3pi/8 from z.
Write r for its radius. Then

    0<r<=d_*<3/4<2cos(3pi/8)<2cos(theta).              (9)

The middle inequality follows by squaring positive quantities:
2cos(3pi/8)=sqrt(2-sqrt(2))>3/4, since sqrt(2)<23/16.

If |z|=t<=1, its squared distance to that named center is

    t^2+r^2-2tr cos(theta).

As a convex quadratic in t on [0,1], its maximum is at an
endpoint. At t=0 it is r^2<1; at t=1 it is less than one by
(9). This contradicts the actual center separation. Every further
actual center therefore satisfies

    1<|z|<M.                                                        (10)

## 4. Each remaining angular sector has a strict diameter reserve

Put

    q=f(M,p)=62231329/71471400,
    alpha=arccos(q),
    w=pi/2+s-2alpha,
    T_*=1-1/(2M^2)=6481/8281.                         (11)

For a further center of radius t in (1,M) and any named center
of radius r in (p,d_*], their actual separation gives

    cos(theta)<=f(t,r)<f(M,r)<f(M,p)=q.                (12)

The first strict step uses the derivative in t, positive since
r<1. For the second, the derivative of f(M,r) has the sign of
r^2-M^2+1<0 throughout r<=d_*<3/4 and M>3/2. Thus every
further center direction is more than alpha from every named one.
In each of the four gaps it lies in the open interval left after
removing alpha from both ends. By (7), that interval has length
strictly less than w; a nonpositive interval contains no center.

We prove the exact reserve

    cos(w)>38225817/48828125>T_*.                     (13)

Here 0<q<1 and q^2>3/4, with the latter reserve

    q^2-3/4=41617545636241/5108161017960000>0.

Consequently 0<alpha<pi/6 and 0<w<pi/2+s<3pi/4.
Set u=2177/2500. The rational comparisons

    u-q=149153/1786785000>0,

    4u^2(1-u^2)-(107/125)^2
       =3941879759/9765625000000>0                   (14)

give, using the strictly decreasing function 2x sqrt(1-x^2)
on 1/sqrt(2)<x<1,

    2q sqrt(1-q^2)>107/125,
    0<2q^2-1<2u^2-1.

The angle identity and the continuous elementary estimates
cos s>=1-s^2/2 and sin s<=s now yield

    cos(w)=2q sqrt(1-q^2) cos s-(2q^2-1) sin s
      >(107/125)(1-s^2/2)-(2u^2-1)s
       =38225817/48828125.

All substituted factors have the displayed positive signs.
The last comparison in (13) has exact reserve

    38225817/48828125-6481/8281
      =92912452/404345703125>0.

In particular w<pi/2, since 0<w<3pi/4 and cos(w)>T_*>0.
This covers every angular endpoint uniformly without an angle mesh.

## 5. The physical capacity is at most eight

Suppose two further centers lay in the same remaining angular
interval. Their minor angle is less than w, so its cosine exceeds
T_* by (13). With their radii t_1,t_2 in (1,M), their squared
distance is strictly less than

    F(t_1,t_2)=t_1^2+t_2^2-2T_*t_1t_2.

This is separately convex on [1,M]^2. Its four corner values
satisfy

    F(1,1)=1/M^2<1,
    F(M,M)=1,
    F(1,M)=F(M,1)<1,

where the last inequality is equivalent to

    T_*-M/2=24149/993720>0.

Thus the actual squared distance is strictly less than one,
contradicting the two disjoint open unit incircles. Each of the
four angular intervals contains at most one further center.
There are at most four further units, hence at most eight total.
This proves the complete closed-domain theorem of Section 1.

## 6. Exact arbitrary-block arm and distinct-leaf statement

Return to all nine original physical units and one unchanged
compatible selected certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let Q be any maximal cyclic biconnected positive block. Suppose
H and C are distinct actual Q vertices with original attachments

    H--X--L,       C--E,

where X is truly unloaded degree two with exactly H,L as its
positive neighbors, and L,E are genuine positive degree-one leaves.
The only positive edge at H outside Q is HX. In particular H
retains all of its actual block forces. There is no restriction
on Q's size, chords, other true degrees, physical masks or further
branches at vertices different from H. Every further original
equation, physical contact and completion square remains.

**Arbitrary-block theorem.** This entire configuration is impossible
throughout the displayed window, for every genuine leaf type,
every actual channel width and every original owner and mean.

Sections 7--10 prove the new complete high S/side case. Section 11
joins every other original radius/type domain using its full inputs.

## 7. The whole high S-side entry retains the full H star

Assume d=1+epsilon>1 and that the genuine L is S with actual
side width one at X. Rotate its real radial direction to e.
The unchanged true X2 force and torque equations give

    L=[d,d+1]e+[-1/2,1/2]Je,
    X=[epsilon,d]e+J_X Je,
    0 belongs to the actual closed unit interval J_X,
    P=p_HX=epsilon e,
    H subset {z:e.z<=epsilon}.                        (15)

The actual inward unit segment from P is in H, so O belongs to
closed H. Because |P|=epsilon<R-sqrt(2), H is physically circle-
clear. Its only positive outside-Q force is the original beta e,
beta>0. Hence its complete unchanged force equation is

    sum_(T an actual Q-neighbor of H) mu_T n_HT=-beta e,
    mu_T>0.                                          (16)

There is no selected subset of H's star in (16).

A genuine D at C would put O openly in C and overlap H. Thus
the actual direct E is S. If f is its real radial direction,
the complete genuine-root geometry gives

    epsilon f belongs to C,       f!=e.               (17)

Equality of directions would make the two distinct genuine leaves
E,L the same occupied S square. No force equation at C is reduced.

## 8. The physical exterior arc and the complete H owner cover

We use the full force-free corner-reach lemma of
TWO_LEAF_S_SIDE_ARM_NEAR_VERTEX_BLOCK_EXCLUSION.md, Section 1:
for an actual unit p+[0,1]u+[0,1]v, any other actual unit meeting
both far half-planes u.(z-p)>=1 and v.(z-p)>=1 has
|c_T-p|^2>=5/2. It includes different reaching points, all
separating-axis owners and touching equalities.

If the reference vertex satisfies |p|<1/40, that is impossible
here, since

    |c_T-p|<91/60+1/40=37/24,
    5/2-(37/24)^2=71/576>0.                           (18)

Thus the opposite vertex F=p+u+v and its entire outward diagonal
ray F+t(u+v), t>=0, avoid every other closed unit. The ray has
genuine exterior access and there is no original block port at F.

The real arm H--X--L has exterior access from H in the same
compatible embedding of Q: a positive path from H to its physical
boundary leaf cannot start inside a bounded face of Q and reach
the unbounded face without crossing a block cycle. The free ray
gives another exterior access. In a plane biconnected graph the
outer face visits H only once. All original Q spokes therefore
occupy one complementary boundary interval. All non-P block ports
lie on one of the two actual H-boundary arcs from P to F, with
one common arc choice.

The full coincident-P cover is the one in Section 2 of
FOUR_BODY_BLOCK_HIGH_SIDE_ARM_AND_DISTINCT_LEAF_EXCLUSION.md:
expand the actual compatible tangent-sector order at P, retain
the arm in its real exterior sector, and collapse back without
moving any application. The entire original cone at P satisfies
both closed component inequalities used below, so either endpoint
assignment gives the same force bound. The same routing preserves
the empty ray and every exterior spoke. This argument uses Q's
biconnectivity and the real arm, not a bound on the number or
degree of its other vertices.

If e is not an own side axis of H, P is its strict maximum-e
vertex. Write

    H=P+[0,1]u+[0,1]v,
    e=-A u-B v,       A,B>0.

Here |P|=epsilon<1/40, so (18) applies. Along the boundary arc
P to P+u to F, every outward normal has v component at most
zero; along the other arc, every outward normal has u component
at most zero. The full P cone has both properties. But (16)
has resultant beta A u+beta B v, with both components positive.
Neither arc is possible. This excludes every tilted H at its full
original degree and every actual mean.

Therefore H is aligned with e and has an actual frame
[epsilon-1,epsilon]e+J_H Je with 0 in J_H. The point epsilon f
of C cannot lie in int(H). By f!=e its longitudinal coordinate
lies strictly between epsilon-1 and epsilon. One of the actual
transverse origin margins is consequently at most epsilon.
After a common reflection the full closed chart is

    H=[epsilon-1,epsilon] times [-h,1-h],
    0<=h<=epsilon,
    P=(epsilon,0),       e=(1,0).                     (19)

The lower-right vertex p_0=(epsilon,-h) has norm at most
sqrt(2)epsilon<1/40. Its opposite F=(epsilon-1,1-h) has the
free northwest ray. The two boundary arcs from P to F are

    upper: P -> (epsilon,1-h) -> F;
    lower: P -> (epsilon,-h) -> (epsilon-1,-h) -> F.

Every upper-arc normal has nonnegative x component and so cannot
give (16). Every lower-arc normal has nonpositive y component;
their full y sum is zero by (16), so positivity forces each
individual y component to vanish. At P, h>0 gives only East;
h=0 gives the full southeast cone, satisfying both required closed
sign inequalities. No endpoint or shared-mean case is discarded.

Every original Q-neighbor of H therefore has horizontal normal,
East or West. An East port is necessarily

    p_HT=(epsilon,t),       -h<=t<=0.                 (20)

These are the same full-star reductions as Sections 1--4 of the
old four-body source, whose steps have been reproduced here at
their degree-free scope. Its private-degree argument is not used.

## 9. Every possible East neighbor violates the new physical count

Let T be any actual East Q-neighbor of H. Its whole square is
in x>=epsilon and contains the unchanged point (20).
It cannot be C: (17) and x>=epsilon would force f_x>=1,
hence f=e and duplication of the actual genuine leaf L.

Thus H,X,C,T are four distinct original units: H,C,T are the
displayed distinct Q vertices, while the true arm body X is
outside every cyclic block. Their actual centers satisfy all
four bounds of Section 1, as follows.

First the aligned H in (19) has

    c_H=(epsilon-1/2,1/2-h),
    |c_H|<=1/sqrt(2)<a,
    a^2-1/2=1/19600>0.                               (21)

Second write J_X=[z,z+1], -1<=z<=0. The exact X frame gives

    c_X=(epsilon+1/2,z+1/2),
    |c_X|^2< (31/60)^2+1/4=1861/3600<b^2,
    b^2-1861/3600=149/9000000>0.                      (22)

Third the actual point epsilon f of C is within distance
1/sqrt(2) of its actual center. Therefore

    |c_C|<=epsilon+1/sqrt(2)<1/60+1/sqrt(2)<c,
    (c-1/60)^2-1/2=1/19600>0.                        (23)

Finally the actual T point (20) has norm at most
sqrt(2)epsilon. With no hypothesis on T's orientation, degree,
mask or force system,

    |c_T|<=sqrt(2)epsilon+1/sqrt(2)
          <31sqrt(2)/60<d_*,
    d_*^2-961/1800=4249/9000000>0.                    (24)

The full asymmetric four-center theorem now gives at most eight
physical units. This contradicts the unchanged nine actual units.
Every East neighbor is excluded, regardless of its actual positive
degree, additional neighbors or physical circle data. No equation
at T is used, and no diamond-hub or unloaded-two premise is assigned.

## 10. The complete West cap closes the high S-side domain

Every original Q-neighbor of H would now have West normal. There
are at least two distinct such neighbors, since H belongs to a
cyclic biconnected block. Their whole squares are in x<=epsilon-1,
so every such actual center w satisfies

    w_x<=epsilon-3/2<-89/60,
    |w|<91/60.

This circular cap lies in a rectangle of horizontal width 2/60
and vertical width 2sqrt(1/10). Its squared diameter is

    (2/60)^2+4/10=361/900<1.

Two distinct actual centers in this cap would be less than one
apart, contradicting their open unit incircles. This finishes the
entire high S/side case for every Q size and chord pattern. It
retains h=0, every original H owner, every coincident port, full
side means and all individual zero circle weights.

## 11. Complete original radius/type join at arbitrary Q degrees

The full local theorem
SHORT_ARM_DISTINCT_GENUINE_ROOT_LOW_CRITICAL_AND_TYPE_FRESH_EXCLUSION.md
has precisely the following premises: true unloaded X2 on H--X--L,
genuine L,E, distinct H,C, and at least two actual nonleaf neighbors
at the cyclic root C. All other original forces at H,C are arbitrary,
and no HC edge is assumed. These premises hold here for every Q.
Its complete proof removes all of the following original domains:

| Original domain | Complete exit |
| --- | --- |
| The direct leaf E is D, at any radius | Its open-origin C chart either overlaps X or invokes the whole two-near-unit D-root obstruction using the actual H,X |
| Either genuine arm type with diagonal X width sqrt(2) | The actual X contains D_epsilon openly while the distinct genuine C meets it |
| Any remaining d<1 | The full opposite aligned side-root chart forces the real H to overlap the other real S leaf |
| Any remaining d=1 | The complete three-origin-unit vertex/side-interior sector cover, physical support equalities and full H/C equations |

The only remaining domain from that theorem is therefore d>1,
direct E=S, and L either S or D with side width one at X.

If L=D, X is a genuine D root outside Q, and Q contains the
different genuine leaf root C. The whole arbitrary-block theorem
D_ROOT_EXCLUDES_SEPARATE_CYCLIC_BLOCK_CONTAINING_A_LEAF_ROOT.md
applies with its E=X, L_E=L, X=C and L_X=E. It excludes
this entire case independently of Q's size, chords, degrees,
load mask and other branches. The actual D root is outside Q
because the true degree-two X has a genuine leaf as one neighbor.
No radial contact or artificial star is newly assigned to C.

If L=S, Sections 7--10 supply the complete remaining high
S/side exclusion. These alternatives exhaust both original
genuine leaf types, both original channel widths, all radii in
the window, every owner and every mean. This proves the full
arbitrary-block theorem of Section 6.

## 12. Literal forest consequences and precise remaining scope

For a single five- or six-body cyclic block with three original
bridges, consider the forest shape consisting of a genuine length-
two arm H--X--L and a genuine direct leaf C--E with H!=C.
The shape has exactly the displayed true X2, L1 and E1, no
additional outside force at H, and full block degrees at both
roots. The theorem applies to every ordered pair of distinct
block vertices, without a distance, adjacency or common-neighbor
premise and without listing graph orbits individually.

In C1.5.b3 this retains all eight positive bodies and the ninth
arbitrary physical completion. In C1.6.b3 it retains all nine
positive bodies. Every original block load mask and every permitted
chord is included. The same theorem applies to other block sizes
or graphs with the exact Section 6 attachment hypotheses.

This is the whole distinct-root arm-plus-leaf shape. It does not
by itself exclude the same-root arm-plus-leaf shape, nor three
direct genuine leaves at distinct roots. Those remain separate
forest obligations unless their own complete proofs are supplied.
No whole C1.5.b3 or C1.6.b3 coarse closure is asserted here.

The physical four-center theorem is available independently of
the stressed-graph caller. Its four specific center bounds must
actually be supplied in another application; this source does
not replace them by four unspecified small centers.

## 13. Complete inputs read and exact source identities

The new capacity theorem is proved in full in Sections 1--5.
The actual arm-circle entry, geometric exterior-arc argument and
complete joins use the following unchanged complete manuscripts
and their displayed independent reviews. Every one was read in
full at its exact operative scope. The inherited selected physical
certificate and common embedding retain their existing acceptance
boundary; no recursive global prerequisite audit is asserted.

| Complete source or review | SHA256 | Exact role |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | All original force/torque, true degrees, selected normals, means and masks |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine S/D geometry, inward unit segment, original true-X2 channel |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | One compatible embedding and protected physical exterior paths |
| TWO_LEAF_S_SIDE_ARM_NEAR_VERTEX_BLOCK_EXCLUSION.md | 721fb76dc356eaa5e31e6719f202c4718de6701e50dfe17d1c01b8a11a6b1971 | Complete force-free corner reach and real empty-ray access |
| FOUR_BODY_BLOCK_HIGH_SIDE_ARM_AND_DISTINCT_LEAF_EXCLUSION.md | a8d64410422fe481d39dc077b19cb6c9fcad6315ae412fc05c71a3c18bb76826 | Complete Sections 1--4 physical/full-star reductions, including coincident P and h=0; its private-degree exit is not used |
| REVIEW_HIGH_SIDE_DISTINCT_LEAF_ROOT_2026_10_27.md | d0557c71aa3044a1fdc5005d898ccf4c0c1961463729e69f1029efc52b069ea3 | Full prior review of the exact geometric and mean-endpoint input |
| SHORT_ARM_DISTINCT_GENUINE_ROOT_LOW_CRITICAL_AND_TYPE_FRESH_EXCLUSION.md | fa43c1e85ac5f290430c0440f2c36dca1333058df6a0b0fda272fa3d0469a729 | Complete low/critical and type theorem with arbitrary H,C stars and no HC edge premise |
| REVIEW_SHORT_ARM_DISTINCT_ROOT_LOW_CRITICAL_TYPES_ROOT_2026_10_27.md | 9d3a4a0ae6796f66fb6bfaf817852b5d2c611fd612c73ef1f1e15086a8dac0ba | Full prior original-scope review of every low/type and critical-sector exit |
| D_ROOT_EXCLUDES_SEPARATE_CYCLIC_BLOCK_CONTAINING_A_LEAF_ROOT.md | c71d7c384700c563477ea8535af327c5e5bd53411e3452a5c083bd0e8a3334f2 | Entire arbitrary-block D-root theorem, with literal X-outside-Q and C-in-Q caller |
| REVIEW_D_ROOT_SEPARATE_CYCLIC_LEAF_ROOT_INDEPENDENT_2026_10_28.md | e9f5fcb3d74f0607fc254b30896b849a472168fcae2ff08536ebd9eccdd3ecc0 | Full independent review of the preceding degree-free D-root theorem |

The old physical eight-unit capacity method motivated the use of
center angles, but no former uniform 1/60-disk theorem is applied
outside its scope. Every asymmetric bound, continuous inequality
and actual center count needed here is proved in Sections 1--5.

This source assigns no original flag or count. It changes no pose,
physical contact, selected normal, mean, force, degree, circle mask,
completion unit or historical source. Exact scalar identities were
checked only as algebra. No numerical pose search, angle grid,
optimizer, generated packing certificate, Lean/Lake compilation,
build, CI/workflow dispatch, metadata edit, commit or remote write
was used. Full independent review is required before adoption.
