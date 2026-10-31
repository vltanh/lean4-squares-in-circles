# A radial North-incoming boundary star cannot return through the loaded middle

Date: October 27, 2026.

**Status: complete hand local theorem and two literal S123 callers,
submitted for full root and separate independent review.** This closes
the whole two-physical-circle-corner B mask at the shared strict
incoming North vertex. It includes the tilted-root owned-side feature
and the high aligned root's South feature. The other B physical mask
and the B-owned incoming axis are not asserted closed here.

## 1. Exact original local scope

Keep the original nine physical units in

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60.

Use fixed orthonormal coordinates e1,e2. The actual B is a
true loaded degree-two body. Its original force from its other
neighbor into B has direction e2 and actual application

    P=(-A0,F),       A0>0,       37/50<F<1.

Assume that B does not own e2, so P is its actual strict
minimum-e2 vertex. In this source B has two physical circle
corners, with arbitrary nonnegative individual weights of
positive total.

Its other actual neighbor is the true loaded degree-two body M.
M's other actual neighbor is the physical radial square

    C=[d,d+1]n+[-1/2,1/2]f,
    n=x e1-t e2,       f=t e1+x e2,
    x>0, t>=0, x^2+t^2=1.

The unchanged C-to-M normal h satisfies h_f>0,h_n<=0.
Consequently its complete actual contact has the form

    P_CM=X*n+(1/2)f,       d<=X<=d+1,                (1)

with X=d when h_n<0. Keep all original side means, B2 and
M2 equations, physical masks and zero individual corner weights.
No equation at B's other neighbor is assumed in the local proof.

Use the existing compatible initial selection conventions:
GENERAL_FIXED_TIP_NORMAL_SELECTION.md and the radial-pair
open near-bisector restriction in Section1 of
ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md.
Both are imposed on the fixed physical pose before taking
multipliers. Section6 below recalls the precise radial-pair
scope; no obtained force normal is changed.

## 2. The actual radial B frame and the full force-cone bound

Write B's two inward axes at P as

    u=(c,s),       v=(-s,c),
    c,s>0, c^2+s^2=1.

The physical circle point P cannot be shared, so P is not a
circle corner. The two-corner radial classification leaves
either radial direction u or radial direction v. The former
would give P=d*u-v/2 with positive first coordinate dc+s/2,
contrary to P_1=-A0<0. Thus the full actual B is

    B=[-1/2,1/2]u+[d,d+1]v,
    P=d*v-u/2,
    A0=d*s+c/2,       F=d*c-s/2.                     (2)

Both of its original physical circle weights remain.

B has the actual boundary neighbor M, so the full original
two-force theorem, TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md,
Lemma2.1, applies. Its pair lines are nonparallel and have a
positive radial concurrence with proper incoming length

    q_B=P+delta*e2,       delta>=0.

This does not assert that q_B lies inside radial B. In the
u,v frame it is exactly

    q_B=(-1/2+delta*s)u+(d+delta*c)v.

The full physical B circle cone, including either zero
individual weight, gives

    |q_B.u|/(q_B.v)<=1/[2(d+1)].

Its lower inequality implies the important unchanged bound

    delta >=1/[c+2(d+1)s]>0.                        (3)

## 3. Actual M reach and the complete B return cover

Apply the complete force-free theorem
RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md to the actual
boundary M containing (1). Every point of M has n projection
strictly greater than epsilon.

Every B point has second coordinate at least F>0. A B--M
point therefore has positive first coordinate, since x>0,t>=0.
The actual maximum first coordinate of B is c-A0. Hence

    c>A0,       r:=s/c<1/(2d).                       (4)

Set

    alpha=n.u=c*x-s*t,
    beta=-n.v=s*x+c*t>0,
    alpha^2+beta^2=1.

If alpha<=0, then |alpha|<=s*t and beta>=c*t.
Here t>0, and (4) makes
(1/2)|alpha|-d*beta <=t(s/2-d*c)<0. This is incompatible
with a positive-n B--M point. Thus alpha>0, and the exact
maximum B support in direction n is alpha/2-d*beta. Therefore

    alpha/2-d*beta>epsilon,
    0<v0:=beta/alpha<1/(2d),
    r<=v0,       beta>=s.                            (5)

The last two inequalities express that the actual channel
angle t/x is nonnegative. They also follow directly by
expanding beta/alpha and beta-s with alpha>0.

The negative-u B face has strictly negative n projection,
so it cannot meet M. The positive-v face has support d+1>d
and cannot support any contained unit. Its endpoints are
also unshareable physical circle corners. A negative-v
owned return is an inner-face radial contact; C7_FORCE_POLYGON.md,
Lemma2.1, makes its neighbor circle-clear, contrary to M's
physical boundary load.

The complete remaining actual return cover is consequently

* B-owned +u, with its original mean Q=(1/2,Y) in u,v;
* the strict inner-right vertex Q0=u/2+d*v, with
  g=g_u*u+g_v*v, g_u>0>g_v.

All axis endpoints belong to their stated owned-side cases.
No original mean is replaced by Q0.

## 4. The entire B-owned +u return is impossible

Its full B2 proper line preserves the v coordinate, so

    Y=d+delta*c
       >=d+1/[1+2(d+1)r].                            (6)

First suppose r<=1/3. Then Y>=d+3/(2d+5). Any actual
unit M supported beyond u=1/2 at Q=(1/2,Y) has an actual
point of squared norm at least Y^2+9/4. Indeed, if M owns
u, its inward unit segment contains Q+u. Otherwise Q is
its strict minimum-u vertex, and one of its inward unit axes
has both u,v components nonnegative. Since Y>1/2, the
dot product of Q with that axis is at least1/2, giving the
same bound at its actual adjacent corner.

This lower bound exceeds R^2. Exactly,

    [d+3/(2d+5)]^2-[(d+1)^2-2]
      =1-2d+6d/(2d+5)+9/(2d+5)^2
      >-31/30+6/7+8100/44521
       =53723/9349410>0.                            (7)

Only 1<d<61/60 was used. Thus no M orientation or endpoint
is possible when r<=1/3.

Now suppose r>1/3. Then s>1/sqrt(10)>3/10. Equations
(4),(6) give Y>d+d/(2d+1)>4/3. A unit supported beyond
u=1/2 at the actual Q can extend by at most one in the
negative v direction: this is immediate on an owned-u side,
and at a strict vertex only one inward axis has negative
v component, of magnitude at most one. Thus every M point
has v coordinate greater than1/3.

But (5) makes the actual maximum v coordinate of C equal to

    -d*beta+alpha/2 <1/2-3/10=1/5.

The physical M--C contact is impossible. This excludes the
whole original B-owned mean for every r, without using a
degree-two equation at C or an assumed M orientation.

## 5. The exact inner-vertex formulas

Only Q0=u/2+d*v remains. Its channel coordinates satisfy

    Q_n=alpha/2-d*beta>epsilon,
    Q_f=beta/2+d*alpha>d>1,
    |Q0|^2=d^2+1/4<(23/20)^2.                       (8)

For Q_f>d, write Q_f=(d+v0/2)/sqrt(1+v0^2);
it increases on0<=v0<1/(2d), starting at d.

The proper B line has

    Q0-q_B=(1-delta*s)u-delta*c*v.

Since its actual direction is strict, 1-delta*s>0.
Put k=-g_v/g_u. Equations (3)--(5) give

    k=delta*c/(1-delta*s)
       >=1/[1+(2d+1)r]
       >2d/(4d+1)>2/5,                              (9)
    g_n proportional to alpha+k*beta>0,
    g_f proportional to beta-k*alpha.               (10)

These formulas retain every original B proper length and
both of its physical circle weights.

## 6. A physical radial M is impossible with the original selected normal

For two actual radial S units in this radius window, their
physical contact fixes the center-direction gap to2theta0,
where theta0=atan(1/(2d)); it is a singleton between their
two inner corners. This is the complete force-free reflection
calculation in Section1 of the cited two-corner-mask source.

If M is radial too, its actual B and C contacts consequently
give a B,C endpoint angle4theta0. The same angle in our
actual frame is pi/2+phi+theta, where phi=atan(r) and
theta>=0 is the channel's clockwise tilt from e1. Equations
(5) put phi+theta between zero and theta0, so this is the
minor endpoint angle. The actual three-boundary path puts
M between B,C. Hence

    r<=tan(phi+theta)
       =tan(4theta0-pi/2)<7/24.                     (11)

Here d>1 gives theta0<atan(1/2), and exactly
tan(4atan(1/2)-pi/2)=7/24. If the intermediate angle were
nonpositive it would already contradict phi+theta>0.

At the actual B--M radial pair, the existing initial open
restriction keeps its unchanged unit normal within Euclidean
distance1/1000 of the perpendicular-bisector normal. In the
B frame write it as

    g=b1*u-a1*v,       a1,b1>0.

Its ideal coefficients are

    a*=1/[2sqrt(d^2+1/4)]<9/20,
    b*=d/sqrt(d^2+1/4)>89/100.

Thus the actual selected coefficients satisfy
a1<451/1000 and b1>889/1000. Equation (9), or the
same full circle-cone inequality before division, yields

    r >=(b1-a1)/[(2d+1)a1]
       >13140/41041
        =3/10+8277/410410>3/10>7/24.                (12)

The final gap is1/120. This contradicts (11).

This uses precisely the existing initial convention at every
physical radial/radial pair. Such a contact is not a four-square
junction, because its two frames differ by a nonzero angle
strictly below pi/2. The strict bisector belongs to a nonempty
open common-normal interval. The finite open restrictions are
compatible with all the original polynomial avoidances and
fixed-tip prelists; uncrossing does not change these point-only
radial pairs. No normal of the current stress is altered.
Both original radial-M weights were retained until this
physical-mask contradiction.

## 7. In the unique-M mask, M owns the unchanged B--M normal

The B contact Q0 is a fixed physical vertex. Its normal is
strictly between the B axes, so if M did not own it, the
actual B--M edge would be a free point contact and Q0
would also be an M vertex.

If C uses its strict inner vertex, P_CM is fixed as well.
If C owns f but M does not own f, P_CM is an actual M
vertex, hence is again a fixed physical singleton. These two
points are distinct by (8), since P_CM has f coordinate1/2.
The full original unique-tip fixed-point selection therefore
excludes a free B--M normal.

It remains to check the only possible shared C--M side:
if M owns f, its f interval is [1/2,3/2]. If g_f>0,
its minimum-g support has f=1/2, contrary to Q_f>1.
If g_f<0 it has f=3/2, contrary to |Q0|<23/20.
If g_f=0 then g=n, and the actual M frame already owns g.
Thus this shared-side case also cannot leave a free B--M
normal. The original actual g is M-owned in every case.

This argument does not fix a variable CM mean or invoke
fixed-point selection on a genuinely shared-side mean.
It uses the actual selected certificate, with all original
generic-avoidance and radial-pair conventions simultaneously
compatible before extraction.

## 8. Both possible transverse signs give complete exits

### 8.1. Negative transverse component

If g_f<0, apply the complete independently reviewed theorem
RADIAL_BOUNDARY_UPPER_CONTACT_OWNED_MIDDLE_PORT_EXCLUSION.md,
SHA256 5c53db2bd1d275a80a36abed3a17f0428af76e6f33dfe516f4de74f26d8d833e,
with REVIEW_RADIAL_UPPER_OWNED_MIDDLE_WEAK_PORT_HEXAGON_2026_10_27.md.
The actual owner is supplied by Section7. Equations (8),(10)
give all positive-coordinate and sign hypotheses, and the
norm hypothesis holds at its retained equality. The full
M2 proper conclusion holds because both original neighbors
B,C are physical boundary bodies. That theorem treats both
supports (1), every original mean and its weak radial equality.
No inside-M premise is assigned to a two-corner mask.

### 8.2. Nonnegative transverse component

Suppose g_f>=0. Equations (9),(10) imply
k<=v0 and r<=v0. Consequently

    v0+(2d+1)v0^2>=1.

At v0<=3/7 the left side is at most

    3/7+(91/30)(3/7)^2=69/70<1.

Thus v0>3/7, and (5),(8)--(10) give

    0<Q_n<1/14,
    0<=g_f/g_n=(v0-k)/(1+k*v0)<1/10.

Write the actual unit g=(c_g,s_g) in n,f coordinates.
Then0<=s_g<1/10,c_g>9/10. Since M owns g, its exact
minimum g support is

    0<G=Q0.g<1/14+23/200=261/1400<1/5.              (13)

Put j_g=Jg. At its actual C point (1),

    149/600<P_CM.j_g=-s_g*X+c_g/2<=1/2.

Here X<=d+1<121/60 was retained. The actual M g interval
is [G,G+1], contained in(0,6/5), and its length-one j_g
interval containing P_CM has every coordinate in(-1,3/2].
Every actual M corner therefore has squared norm strictly below

    (6/5)^2+(3/2)^2=369/100<17/4<R^2.

The reserve is14/25. M is physically circle-clear, contrary
to its genuine positive load. This includes g_f=0 and both
C-owned side endpoints.

Sections4 and6--8 exhaust every original B return and every
physical M mask. The local radial-B feature is impossible.

## 9. The two literal S123 callers

For the tilted-root A-owned direct-side feature, the accepted
S_LEAF_C5_THREE_LOAD_RADIAL_ROOT_HALFPLANES.md gives actual
own axes f1,f2, direct incoming e2=f2 and application
P=(-a_root*q,1-d*b_root). Here a_root,q>0 and
37/50<1-d*b_root<1. Its actual C direction is
n=x*f1-t*f2, x>0,t>=0, and its radial incoming mean has
negative f coordinate. Full C2 gives exactly (1) and the
normal signs used here. This is the entire physical radial-B
mask of the strict B incoming vertex; its other neighbor
A remains true3 and its loaded middle M remains true2.

For the high aligned root with actual South direct normal,
retain A=[epsilon,d]x[-b,a], a+b=1, n=(-c0,s0),
c0,s0>0. The unchanged A3 torque gives the original South
side mean (q,-b), with

    q=epsilon+a*c0/s0,       epsilon<=q<=d.

The complete local small-port and C-mask proof in Sections2--4
of S_LEAF_C5_ALIGNED_SOUTHEAST_DIRECT_EXCLUSION.md uses only
this q<=d. It therefore gives C radial and

    0<a<11/60,       b>49/60,
    a*s0=epsilon(1+c0),
    q=epsilon/(1-c0),       a=q*s0.

In the actual reflected axes e1=West,e2=South the same
incoming point is P=(-q,b), and C has direction
n=c0*e1-s0*e2. Its incoming transverse mean is -a<0.
Thus every stated local hypothesis holds, with the stronger
height b>49/60. This excludes the entire physical radial-B
strict-incoming mask for that aligned South caller as well.

Both callers preserve the actual graph A--B--M--C--U--A,
A--L, all true degrees, both C weights, the real U width,
all nine bodies and every original mean. The physical unique-B
strict vertex and the B-owned incoming axis remain separate
until their own whole sources are joined. No whole S123 gate,
shared metadata change, numerical pose, compilation, CI or
remote action is claimed here.
