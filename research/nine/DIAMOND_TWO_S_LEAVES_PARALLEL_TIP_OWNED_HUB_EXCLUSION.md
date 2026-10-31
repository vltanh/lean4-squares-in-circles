# Two S leaves in a diamond: a parallel tip cannot meet an owned hub side

Date: October 27, 2026.

**Status: complete hand exclusion of the stated entire high-radius
interface, submitted for full root and separate independent review.**
This does not by itself close the remaining whole S/S fine gate.

Keep all nine original physical units, the common compatible selected
certificate, and the exact positive component

    HK, HB, HC, KB, KC, HL, BM.

H and B are genuine S-leaf roots, with leaves L and M respectively.
The true degrees remain H4,K3,B3,C2,L1,M1. K and C have positive total
circle loads. All three other original units, every actual normal,
shared-side mean, physical circle mask and individual zero weight stay
in place. The low and critical domain has its separate complete
ADJACENT_LEAF_ROOT_TRIANGLE_LOW_CRITICAL_EXCLUSION.md proof.

Here assume

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,       R^2<=1105/256,
    r=R-sqrt(2)>129/200,  |c_T|<91/60=:M_0.

**Theorem.** The original pair forces from B to H and K cannot be
parallel if the actual HB normal is an owned side axis of H.

The argument never gives K degree two and never deletes HK. It uses
C's proper radial concurrence only with its genuine true degree two
and physical boundary neighbor K.

## 1. The original parallel tip and all actual means

Opposite parallel B normals would put H and K beyond opposite B
supports and prevent their actual contact. Thus both normals have
the same sign and, by the full B3 force equation, point opposite to
the real S-leaf direction e_M. Rotate so e_M=e_x.

B must be aligned with that direction. Otherwise its unique western
vertex is the common application of both pair forces. Their full
origin torque makes that vertex horizontal. In the full tilted
S-root chart this forces equal inward side components, putting the
vertex at (d-sqrt(2),0), of norm below sqrt(2)-1<r. It cannot belong
to the physical boundary K. Therefore the complete remaining frame is

    B=[epsilon,d] times [a-1,a],       0<=a<=1.

Write the unchanged actual B applications as

    P_H=(epsilon,y),       P_K=(epsilon,z).

The actual B torque says mu_H*y+mu_K*z=0, with positive magnitudes.
Since P_K belongs to boundary K,

    |z|>16/25.

Indeed r^2-epsilon^2>(129/200)^2-1/3600>(16/25)^2. Neither y nor z
is zero, and they have opposite signs. Reflect vertically so

    z<-16/25<0<y<9/25,       0<a<9/25.                 (1)

The final two bounds use the original common side length one, not
a new choice of its means. Also z>=a-1>-1; all subsequent uses need
only z>-1, and the actual side-mean endpoint remains permitted.

By the theorem's owned-hub premise, the actual H frame is

    H=[epsilon-1,epsilon] times [h-1,h],       y in [h-1,h].

Put p=1-epsilon, so p>59/60. The whole physical K satisfies x<=epsilon.
The actual H-to-B normal is east and is H-owned. The physical triangle
H,B,K therefore makes the H-to-K normal have nonnegative x component,
by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md.

## 2. Exhaustive genuine S-leaf features of the owned hub

The actual H leaf application is d*e_L and is a radial outward
support point of H. Its four owned axes and four vertices give a
short complete feature cover.

The east and west axis heights are epsilon and p, both below d.
A south S axis would give h=-epsilon<0, contrary to y>0. The north
axis gives h=d, so the entire H is above y=epsilon>0.

At a strict right-hand vertex, norm d and the outward radial signs
give top height sqrt(d^2-epsilon^2)=sqrt(1+2*epsilon)>1, or bottom
height -sqrt(1+2*epsilon), respectively. The first again puts H
wholly above y=0; the second puts its top below zero and contradicts
y>0. The corresponding left-hand vertex alternatives are exactly

    h=s or h=1-s,       s=2*sqrt(epsilon),
    e_L=(-p,s)/d or e_L=(-p,-s)/d, respectively.        (2)

There are no zero-coordinate vertex endpoints omitted: their norm
would be p or epsilon rather than d. We shall use the strict bounds

    0<s<13/50<4/15,       q:=1-s>11/15.               (3)

### 2.1. Every hub lying wholly above zero is impossible

Such an H requires max_y K>0 because K physically touches H.
But K has maximum-x support epsilon through the actual point
(epsilon,z), where -1<z<0. Translate just for this estimate by
-epsilon*e_x. A unit with right support zero through (0,z), -1<z<0,
and maximum y at least zero has all corner squared norms at most 3.
Here is the full frame calculation.

If the right support is a side, the unit is [-1,0] times [k,k+1]
with -1<=k<0, so all corner norms squared are at most 2. Otherwise
its inward sides at (0,z) are (-c,t),(-t,-c), c,t>0 and c^2+t^2=1.
Reaching zero height gives z+t>=0. The upper adjacent corner has
norm squared at most 1, the lower one at most t^2+(c+t)^2<=3,
and the opposite corner has horizontal magnitude c+t<=sqrt(2)
and vertical magnitude at most one. The original support point
also has norm below one. This covers every side and vertex limit.

Restoring the translation, every actual K corner has norm at most
sqrt(3)+epsilon<7/4<R. This contradicts K's physical circle contact.
Thus only the two left-vertex alternatives in (2) survive.

## 3. The lower-left leaf alternative contradicts full circle balance

First let h=1-s and e_L=(-p,-s)/d. Set f=J e_L=(s,-p)/d.
At the actual K point P_K=(epsilon,z), (1)--(3) give

    P_K.f > |det(P_K,f)|.

For an explicit positive reserve before division by d, subtract
the absolute determinant and use

    (p-s)|z|-epsilon(p+s)
      >(43/60)(16/25)-(1/60)(19/15)=1969/4500>0.

Every actual circle corner of K is within a strict right-angle
half-width pi/4 of the direction of P_K, by
ACUTE_LOADED_CONTACT_GRAPH.md, Section 1. The displayed inequality
puts f within that same strict pi/4 cone about P_K. Thus every such
corner has strictly positive scalar product with f.

K and C are physical boundary neighbors of the genuine S root H
and physically touch each other. The complete geometric two-arc
theorem in S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, Sections 1--2,
therefore puts all their physical circle corners on the same strict
side of the H-leaf axis. Since K's side is positive f, C's is too.
This use is independent of either body's degree and retains zero
individual circle weights.

The real M resultant is a positive multiple of e_x and has positive
f component s/d. The real L resultant has zero f component. Summing
all original component equations would consequently give a strictly
positive f component from M,K,C and zero from L. This contradicts
the full circle-force balance. No root equation was truncated.

## 4. The upper-left leaf gives exact order and center constraints

It remains

    H=[-p,epsilon] times [-q,s],
    e_L=(-p,s)/d,       p=1-epsilon, q=1-s.

Write c_H=(h_x,h_y)=(epsilon-1/2,s-1/2).

The H-to-K normal cannot be east, because K would then lie both
in x>=epsilon and x<=epsilon. It cannot be north or northeast:
its H support is on the top side or at the upper-right vertex,
whereas the actual point (epsilon,z) of K has z<0. Thus

    n_HK=(u,-v),       u>=0, v>0.

Its H support is u*epsilon+v*q, including the full south side when
u=0. Applying this inequality to the actual B--K point gives
z<=-q. Since z>=a-1, this proves a<=s. For the actual K center,
the minimum horizontal halfwidth and minimum normal halfwidth give

    (c_K)_x<=epsilon-1/2=h_x,
    (c_K)_y<=-q-(1+u)/(2v)<=h_y-1.                    (4)

The selected positive graph has its actual straight-center plane
embedding, by TWO_NEAR_HUBS_BOUNDARY_DIAMOND_EXCLUSION.md, Section 1.
The boundary center C is exterior. The genuine M leaf has an exterior
boundary center too; its actual positive edge BM makes B exterior
to the diamond. Therefore in the unchanged straight diamond drawing,
B and C are on opposite sides of the interior diagonal HK. This is
the same exterior-page argument as Section 2 of that source; it
does not require B itself to be physically boundary.

Write

    c_K-c_H=(-eta,-zeta),       eta>=0, zeta>=1,
    c_B-c_H=(1,-delta),         delta=s-a>=0.

The determinant of these two vectors is eta*delta+zeta>0. Hence
whenever (c_C)_y<h_y, the opposite-side property gives

    (c_C)_x<h_x.                                     (5)

All inequalities use the existing selected plane graph, not a new
choice of normals or a relaxation to arbitrary physical diagonals.

## 5. The complete original HC support cover

The actual upper-left H vertex is the real L application and cannot
be shared by another unit: H's strict vertex sector and the S leaf's
half-plane leave only sectors narrower than a right angle. A north
HC normal is excluded by nonobtuseness with the strictly downward
HK normal. The upper-right vertex has norm below r, so cannot belong
to boundary C. The positive-height part of the right face has norm
below r as well.

The remaining right-side interior points belong to the actual side
of B, since a<=s and a-1<=-q; an eastward HC application there would
enter B. The only possible nonwestern right-side exception is the
bottom-right vertex P_0=(epsilon,-q), with an east or southeast normal.
If a<s, P_0 is in B's relative side interior; the actual inward
segment from P_0 into C has positive x component and immediately
enters int B. If a=s, then z=-q and K also contains P_0. H and B
occupy the two upper quadrants there. The two distinct additional
units K,C must occupy the two lower quadrants, since their tangent
angles are each at least pi/2. The positive x component into C
assigns C to the southeast quadrant and K to the southwest one.
But B and K then have a singleton vertex/vertex contact at P_0
with the original west B--K side-axis normal. That is forbidden by
the common strict point-normal convention. This includes the east
axis limit and introduces no new contact selection.

Consequently the exhaustive remaining actual HC normals are

    west, south, or strictly southwest.               (6)

### 5.1. A west normal contradicts the real H leaf's angular separation

Suppose HC is west, with actual P_C=(-p,y_C), -q<=y_C<=s.
The actual loaded C2 has boundary neighbor K. Its full proper
concurrence lemma gives

    q_C=P_C-l e_x,       l>=0,
    q_C is a positive multiple of F_C.

Let g be the C-to-K unit normal and T its original application.
The same properness gives T=q_C+t*g, t>=0. The pair normals at C
are nonparallel by that lemma. Since C lies in x<=-p, the actual
K support from Section 4 gives

    T_y<=-q+(u/v)(T_x-epsilon)<=-q-u/v.

If g_y>0, properness would give T_y>=y_C>=-q. For u>0 this is
already impossible. For u=0 it forces equality and t=0; then T is
on K's top line y=-q, while the actual inward segment in direction
g would enter y>-q, also impossible. The case g_y=0 contradicts
the actual nonparallel C pair. Hence g_y<0.

C's full force equation is F_C=-mu*e_x-nu*g, mu,nu>0. Therefore
(F_C)_y>0, so 0<y_C<=s. Its positive radial concurrence has
x coordinate at most -p. Its direction consequently lies between
the real leaf direction (-p,s) and west, a gap of size at most
arctan(s/p)<pi/12<pi/9. For the strict angle comparison, (3) gives
s/p<78/295<2-sqrt(3), the last inequality following from
512^2>3*295^2.

But any distinct physical boundary unit's circle-resultant direction
differs from the S-leaf center direction by strictly more than pi/9.
Indeed boundary centers are separated by more than 2*pi/9 by
CENTERED_INNER_ARC.md, and all physical circle corners, hence any
positive-weight resultant, differ from their own center by less
than pi/9 by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Lemma 2.1.
This contradicts the actual direction of F_C.

### 5.2. A south normal puts two actual centers in a small cap

For a south HC normal, the actual C center has y<=h_y-1<-1.
Equation (5) gives its x<h_x<-29/60. The same inequalities hold
for K by (4). Both centers have norm below M_0=91/60.

Any such point has x>-23/20, since

    M_0^2-1=4681/3600<(23/20)^2.

Thus both centers lie in the rectangle

    (-23/20,-29/60) times (-91/60,-1),

of squared diameter

    (40/60)^2+(31/60)^2=2561/3600<1.                 (7)

Distinct unit centers have distance at least one. This is impossible.

### 5.3. Every strict southwest normal gives the same contradiction

Write the actual HC normal as n=(-a_0,-b_0), with a_0,b_0>0 and
a_0^2+b_0^2=1. Its original H port is P=(-p,-q), and its minimum
support on C is

    g=p*a_0+q*b_0<=d.                                (8)

If a_0>=b_0, then g>=p. This follows by minimizing the concave
function p*cos(theta)+q*sin(theta) on [0,pi/4], using
q>(sqrt(2)-1)*p. The actual inward unit segment from P in direction
n lies in C. Its endpoint would have squared norm

    |P+n|^2=p^2+q^2+1+2g
       >=(p+1)^2+q^2>16097/3600>1105/256>=R^2.

This is a physical containment contradiction for every C owner.

It remains a_0<b_0. On k=a_0/b_0 in [0,1], the support expression
(p*k+q)/sqrt(1+k^2) increases, since p-q*k>0. At k=2/5 it is
strictly greater than

    169/(30*sqrt(29))>61/60>d,

where 338^2>61^2*29. Consequently (8) forces k<2/5.
The minimum normal halfwidth of C and its actual center-radius bound
now give

    (c_C)_y
      <=-q-1/(2*b_0)-(a_0/b_0)((c_C)_x+p)
       <-q-1/2+(2/5)(M_0-p)
       <-11/15-1/2+(2/5)(8/15)=-51/50<-1.

Since h_y>-1/2, equation (5) again gives (c_C)_x<h_x<-29/60.
K satisfies the same cap bounds by (4), contradicting (7).
Every strict southwest normal is therefore excluded as well.

## 6. Accepted domain after review

Sections 2--3 exhaust the real H S-leaf support features, and
Sections 4--5 exhaust every original HC owner in the only remaining
frame. Thus the entire parallel-tip/owned-hub interface is impossible
at d>1, including all original side means and weak physical limits.

The exact remaining original parent is

    M6.B4L2.DIAMOND.HUB_TIP.LKC.SS.

Its low/critical portion is closed separately. This source does not
claim the high nonparallel-tip or unowned-hub interfaces. K's genuine
degree three and its KC force remain throughout. No artificial
triangle stress, numerical pose, altered normal, Lean compilation,
CI run, remote mutation or shared-ledger edit is used.
