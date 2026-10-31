# A balanced middle and two small North/South roots have total capacity at most eight

Date: October 29, 2026 UTC. Author: capacity continuation.

**Status: complete new force-free hand theorem, submitted for full independent
review.** The theorem below has explicit physical hypotheses and keeps all nine
actual units. It applies to arbitrary positive degrees, every physical circle
mask and every original shared-contact mean. It does not assert that all
three-genuine-root configurations have these hypotheses.

The proof also gives two standalone uniform improvements: a balanced near unit
and two other near units force every fourth unit to clear the closed radius-1/8
disk; every contained unit with that clearance occupies one connected inner
arc longer than `acos(19/25)`, strictly stronger than forty degrees.

## 1. Complete physical statement

Put

    Q=1105/256, rho=9/8, d=1+epsilon,
    0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q.

All units in this manuscript are actual closed unit squares with pairwise
disjoint open interiors, contained in the same original radius-R disk about
the unchanged origin. Let three distinct actual roots be T,H,K. Their three
distinct actual real radial-S leaves are L_0,L_+,L_-, distinct also from all
three roots. For a unit direction e, a real radial-S leaf means the actual
square

    L(e)=[d,d+1]e+[-1/2,1/2]Je,

and its root has the actual point d e as a maximum-e support point. These
are physical hypotheses, not a substituted force resultant.

The middle root and its real leaf have the unchanged chart

    T=[epsilon,d] x [-b,a], a+b=1, a,b>=1/4,
    L_0=L(East).

The two other actual root charts are

    H=P_+ +[0,1]f_+ +[0,1]j_+,
    P_+=(epsilon,t_+),
    f_+=(-c_+,-s_+), j_+=(-s_+,c_+),

    K=P_- +[0,1]f_- +[0,1]j_-,
    P_-=(epsilon,-t_-),
    f_-=(-c_-,s_-), j_-=(-s_-,-c_-),

    0<=t_+,t_-<=11epsilon/10,
    0<=s_+,s_-<=9epsilon/4,
    c_+,c_->0, c_+^2+s_+^2=c_-^2+s_-^2=1.           (1)

Thus an actually aligned upper or lower root is included by s=0. The
original root contacts, side positions and force applications are not
specified or replaced by (1).

The real leaf directions e_+,e_- satisfy

    (e_+)_y>0, (e_-)_y<0,
    |(e_+)_x|<=3/80, |(e_-)_x|<=3/80.                (2)

**Theorem.** These six actual units cannot belong to a nine-unit collection
in the same disk. Equivalently, at most two further actual unit squares can
be added while retaining pairwise interior disjointness and containment.

The exact East/North/South arrangement is included. Conditions (1)--(2)
also permit the complete small tilts occurring in the original parallel
middle triangle charts. No graph, stress equation or normal selection is
used anywhere in the physical proof.

## 2. A balanced near unit forces every fourth unit outside the one-eighth disk

This intermediate theorem is independent of the leaf directions and of the
small-root charts (1).

**Clearance lemma.** Suppose T has the chart in Section 1 and two other
actual units meet the closed disk D_epsilon. Then every fourth actual unit
E has

    dist(O,E)>1/8.                                   (3)

Use the comparison circle |z|=1/4. The entire T open intersection is the
arc x>epsilon. Its angular length is

    pi-2 asin(4epsilon).

The far T side is beyond this circle, and a,b>=1/4 retain both transverse
endpoints: every circle point with x>epsilon has |y|<1/4.

For any unit U meeting D_delta, choose an actual point z in that disk.
In each of its two own-axis directions choose the sign with at least 1/2
distance from z to the far side. Let these perpendicular unit vectors be
u,v. Then z+[0,1/2]u+[0,1/2]v is a subset of the actual U. On a circle
of radius r with r+delta<1/2, every point x satisfying

    x.u>delta, x.v>delta

lies in int U: each actual coordinate of x-z is strictly positive and
strictly less than 1/2. These points form one open arc of length

    pi/2-2 asin(delta/r).                            (4)

No assertion about connectedness of the whole U intersection is needed.

The other two near units therefore each occupy at least
pi/2-2 asin(4epsilon) on the radius-1/4 circle. If a fourth E met
D_(1/8), (4) would supply another arc of length pi/6. The four disjoint
open-interior circle sets would have total angular measure at least

    2pi-6 asin(4epsilon)+pi/6>2pi.                   (5)

Here 4epsilon<1/15, and for 0<=x<=1/15 the derivative of asin is
strictly less than 15/14, since sqrt(1-x^2)>14/15. Consequently
asin(1/15)<1/14. Thus 6 asin(4epsilon)<3/7<1/2<pi/6,
proving the strict inequality in (5). This contradicts disjointness
and proves (3), including the proposed distance endpoint 1/8.

Each of the three roots in Section 1 meets D_epsilon. Indeed the whole
actual radial segment [epsilon e,d e] lies in its root. At a maximum-e
vertex the two inward own-edge components of -e lie in [0,1]; at a side
point one such component is zero and the original transverse coordinate
is retained. Moving a distance one in direction -e therefore stays in
that same actual unit. In particular the actual point epsilon e belongs
to the root. The clearance lemma applies to all three roots without using
their degrees or their force equations.

## 3. A stronger complete connected-arc theorem

Set

    gamma=acos(19/25), C=19/25, S=sqrt(264)/25.

**Arc lemma.** Every actual unit E contained in D_(sqrt(Q)) with
dist(O,E)>1/8 has one connected open-interior intersection with |z|=rho.
Its angular length is strictly greater than gamma, and it contains the
radius-rho point in the actual center direction.

The proof reproduces the complete continuous geometry underlying the
accepted forty-degree theorem, at this stronger exact angle. The relevant
elementary bounds are

    2pi/9<gamma<pi/3,
    3/5<S<13/20,
    cos(gamma/2)^2=22/25,
    sin(gamma/2)^2=3/25.                             (6)

For the first lower bound, 4x^3-3x is increasing at x>1/2 and

    -1/2-(4(19/25)^3-3(19/25))=753/31250>0.

The comparison with cos(2pi/9), whose triple cosine is -1/2, gives
gamma>2pi/9. The sine upper bound has squared reserve 1/10000.

Choose only signs and order of E's own orthonormal coordinates about the
unchanged origin, so

    E=[A,a] x [B,b], A=a-1, B=b-1,
    a>=b>=1/2, q=a^2+b^2<=Q.

The actual square center has nonnegative own coordinates in this frame,
so (a,b) is a farthest actual corner. In particular A<61/60 and B<1/2.

### 3.1. The whole a>rho domain

Here A>1/8, -1/2<=B<1/2 and q>97/64. For fixed q put t=a+b.
Exact expansion gives

    E_0=A^2+B^2+2SAB
       =(1-S)q+S t^2-2(1+S)t+2(1+S).

This expression is convex in t. On the enlarged full set a>=b>=1/2
with fixed q, its endpoints occur at b=1/2 and a=b. It suffices to
bound these two values.

At b=1/2 put A_0=sqrt(q-1/4)-1. Then 1/8<A_0<61/60, and

    E_0=A_0^2+1/4-S A_0
       <A_0^2+1/4-(3/5)A_0<=97/144.

The last convex quadratic has enlarged endpoint values 61/320 and
97/144. At a=b=v, one has 3/4<v<147/100 and |v-1|<47/100, so

    E_0=2(1+S)(v-1)^2<72897/100000.

Both upper bounds are strictly less than

    rho^2 C^2=29241/40000,                           (7)

with respective reserves 20669/360000 and 411/200000. Convexity proves
E_0<rho^2 C^2 on the entire a>rho domain.

Define

    alpha=acos(A/rho), beta=asin(B/rho),
    eta=asin(min(b/rho,1)).

The complete closed intersection is exactly

    [max(-alpha,beta), min(alpha,eta)].              (8)

The open-interior intersection uses the corresponding strict inequalities.
The first own coordinate is positive, the far first side is beyond the
circle, and the remaining three faces give precisely (8). The formal
eta=pi/2 endpoint for b>=rho is superseded by alpha<pi/2.

From (7),

    (A+S B)^2<C^2(rho^2-B^2),
    A<C sqrt(rho^2-B^2)-S B=rho cos(beta+gamma).

Here |beta|<pi/6 and pi/6<gamma<pi/3, so
0<beta+gamma<pi/2. Therefore alpha-beta>gamma.

Also A/rho<122/135<cos(gamma/2) and
eta>=asin(4/9)>gamma/2. Their exact squared reserves are

    22/25-(122/135)^2=1154/18225,
    (4/9)^2-3/25=157/2025.

Consequently 2alpha>gamma and alpha+eta>gamma. Finally the actual
unit-strip angle eta-beta has minimum 2asin(4/9)>gamma when b<=rho;
the minimum is at b=1/2, as differentiation shows. When b>rho it is
greater than pi/3>gamma. The endpoint b=rho is retained.

All four upper-minus-lower endpoint differences in (8) exceed gamma.
The actual open intersection is thus one nonempty open arc longer than
gamma throughout a>rho.

### 3.2. The whole a<=rho domain

The strict clearance gives

    0<B<=A<=1/8, A^2+B^2>1/64,
    A>1/(8sqrt(2))>1/12, a>13/12, b>1.

If B<=0, the actual distance would be at most A<=1/8, so no omitted
nonpositive-B feature remains. The square lies in the first quadrant.
Set

    alpha=acos(A/rho), beta=asin(B/rho),
    theta=acos(a/rho), eta=asin(b/rho).

Its complete closed intersection is

    [max(beta,theta), min(alpha,eta)].               (9)

The same actual inequalities retain a=rho and b=rho. Each of the four
endpoint differences exceeds gamma:

* alpha-beta>=pi/2-2asin(1/9), whose cosine is
  8sqrt(5)/81<19/25.
* The two unit-strip differences are at least asin(8/9)>gamma,
  since 8/9>S.
* For the two outer faces, eta-theta is in [-pi/2,pi/2] and

      sin(eta-theta)
        =[ab-sqrt((rho^2-a^2)(rho^2-b^2))]/rho^2
        >(13/12-31/192)/(81/64)=59/81>S.

  Here the product under the radical is less than
  (53/576)(17/64)=901/36864<(31/192)^2. Sine is increasing on
  the whole stated difference interval.

Thus (9) too is one open arc of length greater than gamma.

The actual incircle gives |c_E|>5/8=rho-1/2, by the strict clearance.
Containment gives |c_E|^2+|c_E|+1/2<=Q; its left side at 91/60
exceeds Q by 31/57600. Therefore

    rho-1/2<|c_E|<91/60<rho+1/2.

The point rho c_E/|c_E| is strictly inside E's actual incircle. It
lies in the unique arc already proved. This finishes the arc lemma,
with all actual orientation, support-owner and physical-mask endpoints.

## 4. Each small root occupies more than thirty degrees in the western gap

Put delta=1/40 and theta_0=acos(13/15). The near vertices in (1) satisfy

    |P_+|^2,|P_-|^2<=221epsilon^2/100
       <9epsilon^2/4<1/1600=delta^2.                (10)

The middle strict inequality has coefficient reserve 1/25. If a point
z on |z|=rho has both own inward coordinates in (0,1-delta), with
each smaller coordinate larger than delta, then z belongs to the open
actual root: subtracting the corresponding coordinates of P, whose
absolute values are less than delta, leaves both coordinates in (0,1).

In the own quadrant of either root, the circle arc with both coordinates
less than 1-delta has length

    pi/2-2acos((1-delta)/rho)
      =pi/2-2theta_0>pi/6.                          (11)

The strict inequality follows from (13/15)^2-3/4=1/900. Every point
of this arc has both coordinates greater than

    sqrt(rho^2-(1-delta)^2)=sqrt(63/200)>delta.

Thus (11) is an actual open-interior root arc. The near vertex is not
replaced by O, and no whole-root intersection is assumed connected.

Set nu=asin(3/80). The frame angles phi_+=asin(s_+) and
phi_-=asin(s_-) lie in [0,nu), because epsilon<1/60. We will use

    nu<3/79<1/25, theta_0>pi/8>nu.                  (12)

For the first bound integrate the derivative of asin on [0,3/80],
using sqrt(1-x^2)>79/80. For the theta_0 comparison, its cosine
13/15 has square less than 17/20, whereas
cos(pi/8)^2=(2+sqrt(2))/4>17/20.

Choose actual leaf directions on the increasing angular lift as

    theta_+ in [pi/2-nu,pi/2+nu],
    theta_- in [3pi/2-nu,3pi/2+nu].                 (13)

The actual H arc constructed in (11) lies at angles

    pi/2+phi_++theta_0 < theta < pi+phi_+-theta_0;

the actual K arc lies at angles

    pi-phi_-+theta_0 < theta < 3pi/2-phi_--theta_0.

By (12), each of these intervals is strictly between theta_+ and
theta_-. The actual root interiors are disjoint from both real leaf
interiors and from their closed circle arcs. Therefore both complete
chosen root arcs lie in the one western gap between those leaf arcs.
They are mutually disjoint and occupy total length strictly greater
than pi/3 in that gap.

The use of closed leaf arcs is legitimate: an interior point of one
square cannot be a closed point of a distinct square with disjoint open
interiors, because interior points of the latter approach every one of
its closed points.

## 5. The real leaf arcs and the three actual complementary intervals

Each complete closed real-S intersection on |z|=rho is the arc about
its actual direction of halfwidth

    alpha(d)=min(acos(d/rho),beta_0),
    beta_0=asin(4/9).

The actual far radial side is beyond the circle, and the inner and two
transverse sides give exactly this expression. Uniformly,

    alpha(d)>alpha_0=acos(122/135),
    pi/8<alpha_0<pi/6, beta_0<pi/6.                 (14)

The first bound uses d<61/60 and
(122/135)^2-65/81=259/18225>0 to compare beta_0 with alpha_0.
For alpha_0>pi/8, use
17/20-(122/135)^2=2429/72900>0 and the half-angle formula above.
The upper pi/6 bounds follow by positive squaring.

The three real leaf arcs are physically disjoint. Their complement has
the upper East-to-North gap, the western North-to-South gap and the
lower South-to-East gap. Their lengths are respectively

    theta_+-2alpha,
    theta_--theta_+-2alpha,
    2pi-theta_--2alpha.                              (15)

Degenerate empty gaps only strengthen the bounds below. Every one of
the three actual completion squares has clearance (3), hence a single
connected arc longer than gamma by Section 3. That entire arc avoids
the full closed leaf arcs, so it lies in one of the three intervals
(15). No additional disconnected component of a completion square is
discarded: Section 3 proved its full intersection connected.

### 5.1. The western gap has completion capacity at most one

Its length is less than pi+2nu-2alpha_0. The two actual root arcs from
Section 4 occupy more than pi/3 inside it. The remaining total measure
is therefore less than

    2pi/3+2nu-2alpha_0
      <5pi/12+2/25<4pi/9<2gamma.                   (16)

The middle comparison follows from 2/25<pi/36, using pi>3. Thus
two completion arcs, each longer than gamma, cannot both occupy this
gap. This is a measure bound on actual disjoint arcs and requires no
claim that the root complement in the gap is connected.

### 5.2. Each small gap has completion capacity at most one

Each of the first and third lengths in (15) is less than

    pi/2+nu-2alpha_0<pi/4+1/25<4pi/9<2gamma.        (17)

Thus at most one completion arc can occupy either of those gaps.

### 5.3. At least one small gap is empty

Since a+b=1, suppose first a>=1/2. The East leaf and the actual T
together occupy every radius-rho point with angle in [0,beta_0].
Indeed the leaf covers [0,alpha]. If alpha<beta_0, then
alpha=acos(d/rho), and for alpha<=theta<=beta_0 the point has

    epsilon<rho cos(theta)<=d,
    0<rho sin(theta)<=1/2<=a.

It belongs to the actual closed T. Its first coordinate is at least
rho cos(beta_0)=sqrt(65)/8>1>epsilon. Every endpoint, including
a=1/2 and alpha=beta_0, is retained.

Any completion arc in the upper small gap must consequently lie in an
interval of length at most

    theta_+-alpha-beta_0
      <D:=pi/2+nu-alpha_0-beta_0<gamma.              (18)

The final strict comparison is proved exactly in Section 6. This gap
cannot contain a completion arc longer than gamma. If instead b>=1/2,
reflect the whole physical picture in the horizontal axis; the same
proof empties the lower small gap. Both conclusions apply when a=b=1/2.

One small gap has capacity zero, the other at most one, and the western
gap at most one. Three actual completion squares are impossible. This
proves the theorem of Section 1.

## 6. Exact comparison closing the tilted small-gap endpoint

This is one continuous angle comparison, with no angle mesh. Put
A=alpha_0+beta_0. From (14), A<pi/3, and A>alpha_0>pi/8>nu.
Hence D=pi/2+nu-A lies in (0,pi/2), the interval on which sine
is strictly increasing. The addition formulas give

    cos A=(122sqrt(65)-4sqrt(3341))/1215,
    sin A=(sqrt(217165)+488)/1215,
    sin D=cos(A-nu)
      =[(122sqrt(65)-4sqrt(3341))sqrt(6391)
         +3(sqrt(217165)+488)]/97200.

The first bracket is positive: sqrt(65)>8 and sqrt(3341)<58 give
the lower bound 744. The exact strict radical comparisons

    sqrt(65)<129/16,
    sqrt(3341)>289/5,
    sqrt(6391)<80,
    sqrt(217165)<467

therefore imply

    sin D<[(122(129/16)-4(289/5))80+3(467+488)]/97200
          =63059/97200<649/1000<sqrt(264)/25=sin gamma.

The radical square reserves are 1/256, 4/25, 9 and 924, respectively.
The final rational and squared reserves are

    649/1000-63059/97200=119/486000,
    264/625-(649/1000)^2=1199/1000000.

Since gamma lies in (0,pi/2), the sine comparison proves D<gamma.
This retains both extreme leaf-direction inequalities (2), the complete
closed original upper radius, the middle a=1/2 endpoint and every
individual original circle coefficient endpoint.

## 7. Literal small-chart transfer and exact remaining scope

The geometric input (1) includes each aligned upper root

    [epsilon-1,epsilon] x [q,q+1],
    q=epsilon or q=sqrt(1+2epsilon)-1,

since 0<q<=epsilon and one may take s_+=0. It includes its full lower
reflection. It also includes the complete small tilted upper chart

    P_+=(epsilon,t), 0<t<11epsilon/10,
    f=(-c,-s), j=(-s,c), 0<s<9epsilon/4,

and the full lower reflection. If its real North leaf is in the owned
j direction, then its horizontal direction component is -s. If its
real North leaf uses the strict vertex P_++j, the unit radial direction
is (P_++j)/d, with horizontal component (epsilon-s)/d. Thus in either
case the full actual leaf direction satisfies (2); in the strict case

    |epsilon-s|/d<5epsilon/4<1/48<3/80.

The lower calculation is its whole-data reflection. The owned versus
strict endpoint is not deleted, and no original force application is
reset to one of these geometric vertices.

Consequently every original parallel-middle branch with these two
small upper/lower charts and with a,b>=1/4 is excluded, at arbitrary
outer true degrees and without using any external-neighbor restriction.
This includes the full balanced interval
353/1000<=a,b<=647/1000 supplied by the accepted boundary-flanked-root
theorem whenever its own literal graph hypotheses have been proved.

This manuscript does not prove that a,b>=1/4 in every parallel-middle
triangle. It also does not replace a West-type outer leaf by a North
or South one, or claim that every broad-root configuration has the
small charts (1). A caller must separately close such alternatives or
derive the displayed physical premises before marking an original row.
No entire original house, fan, six-body or coarse parent is marked closed
by this standalone source alone.

## 8. Proof provenance and preservation

Sections 2--6 contain the complete physical proof; there is no unproved
force, selection or graph premise internal to the theorem. Section 3
reconstructs and strengthens the continuous calculation in
FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md rather than relying
on a forty-degree statement to justify the stronger angle. The complete
connected-arc endpoint formulas of
NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md were read and reproduced.

The original full-window high-S reduction, when needed by a graph caller,
is supplied separately by THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md.
The exact small chart transfers in Section 7 reproduce the physical
domains in THREE_LEAF_DIAMOND_PARALLEL_ONE_TILTED_HUB_FRESH_EXCLUSION.md
and THREE_LEAF_DIAMOND_PARALLEL_TWO_TILTED_HUBS_FRESH_EXCLUSION.md.
Their diamond private-star equations are not used or exported to larger
root degrees.

The new theorem requires its own full independent review before adoption.
No original unit, force, normal, mean, physical mask or coefficient was
altered. No numerical pose search, angle mesh, new packing certificate,
Lean/Lake compilation, CI/workflow dispatch, metadata edit, remote mutation
or merge was performed.
