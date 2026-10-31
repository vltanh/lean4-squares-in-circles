# A forty-degree inner arc for every unit outside the one-eighth disk

Date: October 27, 2026.

**Status: complete force-free hand strengthening, submitted for full
root and separate independent review.** This sharpens the accepted
arc length in `NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md` while
retaining exactly its strict central-clearance premise. It does not
assert an original graph-family closure by itself.

Put

    Q=1105/256,       rho=9/8,       delta=2*pi/9.

**Theorem.** If an actual closed unit square E is contained in the
closed disk of squared radius Q and dist(O,E)>1/8, its open interior
meets the radius-rho circle in one connected open arc of angular
length strictly greater than delta. The arc contains the radius-rho
point in the actual center direction. Every actual orientation and
physical side/corner endpoint is included.

## 1. Exact trigonometric bounds and the original coordinate split

Write c=cos(delta), s=sin(delta). The function 4x^3-3x is
strictly increasing for x>1/2. Its values at 19/25 and 4/5 are
respectively -8189/15625<-1/2 and -44/125>-1/2. Since
cos(3delta)=-1/2, this gives

    19/25<c<4/5,
    3/5<s<13/20.                                 (1)

For the last upper bound, c>19/25 gives s^2<264/625<169/400.
Also the same cubic comparison at delta/2=pi/9 gives

    cos(delta/2)>15/16,
    sin(delta/2)<sqrt(31)/16<4/9,                 (2)

because 4*(15/16)^3-3*(15/16)=495/1024<1/2.

Choose only signs and order of the actual own axes, about the unchanged
original circle origin, so that

    E=[A,a] times [B,b],
    A=a-1,       B=b-1,
    a>=b>=1/2,  q=a^2+b^2<=Q.

As in the complete accepted one-eighth theorem, retain both a>rho
and a<=rho. In the second case the strict distance hypothesis gives
0<B<=A<=1/8 and a>13/12. No outer-face case is discarded.

## 2. The whole a>rho domain has a stronger quadratic estimate

Here

    1/8<A<61/60,       -1/2<=B<1/2,
    q>97/64.

We prove

    E_0=A^2+B^2+2sAB<rho^2*c^2.                 (3)

For fixed q, put t=a+b. Exact expansion gives

    E_0=(1-s)q+s*t^2-2(1+s)t+2(1+s).

This is convex in t. On the full enlarged interval a>=b>=1/2
with fixed q, its endpoints occur at b=1/2 and a=b.

At b=1/2 write A_0=sqrt(q-1/4)-1. The bounds above give
1/8<A_0<61/60, so (1) gives

    E_0=A_0^2+1/4-s*A_0
       <A_0^2+1/4-(3/5)A_0
       <=97/144.

The last convex quadratic has enlarged endpoint values 61/320 and
97/144, as in the earlier exact arc proof.

At a=b=v, containment gives v<147/100, and q>97/64 gives
v>3/4. Thus |v-1|<47/100. Using (1),

    E_0=2(1+s)(v-1)^2
       <(33/10)*(47/100)^2
       =72897/100000.

Both endpoint bounds are strictly below

    29241/40000=rho^2*(19/25)^2<rho^2*c^2.

The difference between the latter rational number and
72897/100000 is exactly 411/200000. Fixed-q convexity therefore
proves (3) over the entire actual orientation domain.

## 3. All four actual a>rho endpoint differences exceed forty degrees

Define

    alpha=arccos(A/rho),
    beta=arcsin(B/rho),
    eta=arcsin(min(b/rho,1)).

The exact closed circle intersection is

    [max(-alpha,beta), min(alpha,eta)].           (4)

For open interior the corresponding inequalities are strict. The
formal eta=pi/2 endpoint when b>=rho cannot create an isolated
point, since alpha<pi/2 already excludes that direction.

First, (3) gives

    (A+sB)^2<c^2*(rho^2-B^2),
    A<c*sqrt(rho^2-B^2)-sB=rho*cos(beta+delta).

We have |beta|<=arcsin(4/9)<pi/6 and pi/6<delta<pi/3.
Hence 0<beta+delta<pi/2, and inversion of the cosine comparison
gives alpha-beta>delta.

Next A/rho<122/135<15/16, so (2) gives alpha>delta/2.
Since b>=1/2, (2) also gives eta>=arcsin(4/9)>delta/2.
Thus 2alpha>delta and alpha+eta>delta.

Finally eta-beta>delta by the complete unit-strip calculation:
for b<=rho its minimum is 2arcsin(4/9)>delta, attained at
the centered strip b=1/2, and for b>rho it is greater than
pi/3>delta. The strip endpoint b=rho is included by continuity.

All four upper-minus-lower differences in (4) exceed delta.
Therefore the actual open-interior intersection is one connected
open arc longer than forty degrees.

## 4. The complete outer-face domain has still more angular room

When a<=rho, the actual bounds and interval from Section 3 of
`NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md` are

    0<B<=A<=1/8,       a>13/12,       b>1,

    [max(beta,theta), min(alpha,eta)],
    alpha=arccos(A/rho), beta=arcsin(B/rho),
    theta=arccos(a/rho), eta=arcsin(b/rho).

That entire first-quadrant feature proof retains a=rho and b=rho.
Each of its four bounds also exceeds the present larger delta:

* The inner/inner difference is at least pi/2-2arcsin(1/9).
  Its cosine is 8sqrt(5)/81<19/25<c, so the difference is
  greater than delta.
* Each unit-strip difference is at least arcsin(8/9)>delta,
  since 8/9>13/20>s.
* The outer/outer difference lies in [-pi/2,pi/2] and its
  exact sine is strictly greater than 59/81>13/20>s.
  Strict monotonicity of sine on that difference interval therefore
  gives a difference greater than delta.

For the last bound the unchanged physical calculation is

    sin(eta-theta)
     =[ab-sqrt((rho^2-a^2)(rho^2-b^2))]/rho^2
     >(13/12-31/192)/(81/64)=59/81,

using sqrt(901)<31. This transfers the full actual square and
all of its endpoints, not a sampled orientation or a selected
subarc. It proves the forty-degree statement throughout a<=rho.

## 5. Center point, capacity rule and the strict threshold

The center-point argument is unchanged. The unit incircle and
dist(O,E)>1/8 give |c_E|>5/8=rho-1/2. Actual containment gives

    |c_E|^2+|c_E|+1/2<=Q,
    |c_E|<91/60<rho+1/2.

Thus rho*c_E/|c_E| lies strictly inside that actual incircle and
in the unique open arc proved above.

For distinct actual units with disjoint open interiors these arcs
are disjoint. After a caller proves their actual free-gap routing,
an interval of length at most n*delta contains at most n-1 of
them, for every positive integer n. In particular a gap of at most
forty degrees holds none, and one of at most 120 degrees holds at
most two. The strict arc lengths cover the interval-length equality
cases.

The hypothesis dist(O,E)>1/8 remains strict. The actual unit
[1/8,9/8] times [-1/2,1/2] has the two open arcs described in
the earlier source and still prevents a connected-arc assertion at
that equality. No force, graph degree, circle mask or point-normal
selection is used anywhere in the proof.

No numerical pose, compilation, CI, remote mutation or shared metadata
edit is used.
