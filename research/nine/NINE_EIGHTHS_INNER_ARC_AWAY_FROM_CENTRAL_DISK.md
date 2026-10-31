# A connected nine-eighths arc outside the central disk

Date: October 27, 2026.

**Status: complete force-free hand theorem; restored from the preserved
complete argument after the workspace snapshot reset.** The mathematical
scope is the same as the previously independently accepted source.
The restored file has its own new byte pin and is submitted for readback
and independent repinning.

Put

    Q=1105/256,       rho=9/8,
    gamma=arccos(4/5),       sin(gamma)=3/5.

**Theorem.** Let E be any actual closed unit square contained in the
closed disk of squared radius Q. If

    dist(O,E)>sqrt(2)/8,                                 (1)

then int(E) meets the radius-rho circle in exactly one connected open
arc of angular length strictly greater than gamma. The arc contains
the point rho*c_E/|c_E| in the actual center direction.

The statement includes every square orientation and every actual
physical side/corner endpoint. It has no force, degree, contact-normal
or circle-mask premise. The origin is the original containing-circle
origin throughout.

## 1. The complete actual own-coordinate interval

Choose only signs and order of the actual orthonormal own axes, so

    E=[A,a] times [B,b],
    A=a-1,       B=b-1,
    a>=b>=1/2,
    q=a^2+b^2<=Q.

The squared distance from the origin to this actual rectangle is
max(A,0)^2+max(B,0)^2. If a<=rho, both positive parts are at most
1/8, contradicting (1). Therefore

    a>rho,       1/8<A<61/60,
    -1/2<=B<1/2,       b>=1/2,
    q>97/64.                                            (2)

For the upper A bound, use a^2<=Q-1/4=1041/256<(121/60)^2.
For B<1/2, use b^2<=Q/2<(3/2)^2. The strict lower q bound is
a^2+b^2>rho^2+1/4=97/64.

Define the actual angles

    alpha=arccos(A/rho),
    beta=arcsin(B/rho),
    eta=arcsin(min(b/rho,1)).

Since 0<A<rho, all points of E on the radius-rho circle belong to
the right-half-plane angular chart. Its complete closed intersection
is exactly

    [max(-alpha,beta), min(alpha,eta)].                  (3)

For open interior the relevant inequalities are strict. When b>=rho,
the formal eta=pi/2 endpoint is already excluded by alpha<pi/2;
no extra isolated point or separate arc is created. We will prove that
all four upper-minus-lower differences in (3) exceed gamma.

## 2. A fixed-q convexity bound for the inner two faces

Let

    E0=A^2+B^2+(6/5)A*B.

For fixed q put t=a+b. Exact expansion gives

    E0=(2/5)q+(3/5)t^2-(16/5)t+16/5.                  (4)

This is convex in t. On the complete enlarged interval a>=b>=1/2
with fixed q, the endpoints are b=1/2 and a=b.

At b=1/2 write A0=sqrt(q-1/4)-1. By (2),

    1/8<A0<61/60,
    E0=A0^2-(3/5)A0+1/4.

This convex quadratic has endpoint values

    61/320       at A0=1/8,
    97/144       at A0=61/60.

Thus it is below 4/5 on the full enlarged interval.

At a=b=v, the q bounds give 3/4<v<3/2. Therefore

    E0=(16/5)(v-1)^2<4/5.

Fixed-q convexity in (4) proves throughout the actual domain

    E0<4/5<81/100=rho^2*(4/5)^2.                       (5)

This comparison retains the full square frame; it does not select a
sampled angle or replace the actual square by a favorable subrectangle.

## 3. All four actual angular differences

Rewrite (5) as

    (A+(3/5)B)^2<(4/5)^2*(rho^2-B^2).

Taking the upper square-root inequality, which remains valid even
when its left unsquared expression is negative, gives

    A<(4/5)*sqrt(rho^2-B^2)-(3/5)B
      =rho*cos(beta+gamma).

We have |beta|<=arcsin(4/9)<pi/6 and pi/6<gamma<pi/3.
Hence 0<beta+gamma<pi/2. The cosine comparison can be inverted
there, giving

    alpha-beta>gamma.                                  (6)

For the other two individual bounds, use

    A/rho<122/135<3/sqrt(10)=cos(gamma/2),
    eta>=arcsin(4/9)>arcsin(1/sqrt(10))=gamma/2.

Thus

    2alpha>gamma,       alpha+eta>gamma.                (7)

Finally consider the complete unit-strip difference eta-beta. For
1/2<=b<=rho it equals

    arcsin(b/rho)-arcsin((b-1)/rho).

Its derivative is nonnegative on this interval because
b>=|b-1|, and its minimum at b=1/2 is 2arcsin(4/9)>gamma.
The endpoint b=rho is included by continuity. For b>rho,
eta=pi/2 and beta<pi/6, so eta-beta>pi/3>gamma. Therefore

    eta-beta>gamma.                                    (8)

Equations (6)--(8) are exactly the four upper-minus-lower differences
in (3). Its open-interior interval has positive length greater than
gamma and is the entire intersection. This proves connectedness and
the strict arc-length conclusion.

## 4. The actual center direction belongs to that open arc

The square's actual radius-1/2 incircle is contained in E. From (1),

    |c_E|>1/2+sqrt(2)/8>rho-1/2.

The farthest-corner formula in actual center coordinates gives

    |c_E|^2+|c_E|+1/2<=Q.

Since the left side at 91/60 exceeds Q, this implies

    |c_E|<91/60<rho+1/2.

Consequently |rho-|c_E||<1/2. The point rho*c_E/|c_E| lies
strictly in that actual incircle and hence in int(E). It belongs to
the unique open arc already established.

## 5. Exact physical capacity export

For distinct actual squares with disjoint open interiors, these open
arcs are disjoint. After a caller proves that each complete arc lies
in one actual free interval, a free interval of length at most n*gamma
can contain at most n-1 such arcs, for every positive integer n.

In particular an interval of length at most gamma contains none,
and one of length at most 3gamma contains at most two. The strict
arc lengths retain equality in the interval-length bounds. The caller
must establish the actual occupied closed arcs and their endpoint
routing; this theorem does not infer that from center angles alone.

This is a whole physical theorem with all actual orientations and
endpoints. It uses no selected stress, force deletion, numerical pose,
compilation, CI, remote action or shared-metadata edit.
