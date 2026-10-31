# A short boundary path cannot join two outward owned sides with these tangent signs

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: new complete proposed hand theorem, frozen for separate full
independent review and root adoption.** This is a fresh manuscript, not
a byte reconstruction of a lost earlier positive-return draft. It has
no upper-radius restriction. It uses the actual endpoint side positions
and actual circle corners, but no local force equation and no equation
at an internal path body. In particular it does not turn a loaded
degree-three or degree-four endpoint into a two-force body.

## 1. General physical statement

Keep the original circle origin O=0. Let R>=79/40, and let a path of
between two and four distinct actual unit squares be contained in the
closed radius-R disk, with disjoint open interiors. Every path square
physically touches the circle, and consecutive path squares physically
touch each other. Denote the first and last squares by E and C.

Assume the actual center directions traverse the containing circle
counterclockwise along this path: there are lifts

    alpha_E < alpha_1 < ... < alpha_C < alpha_E+2*pi,

and every successive gap is less than pi. Thus every edge uses its
actual counterclockwise minor center arc. This is an explicit physical
order premise. In an occupied-rim application it must be supplied by
the original embedding and actual circle spokes, not by an arbitrary
ordering of a force polygon.

Suppose there is an orthonormal positively oriented chart (e,f) about
the unchanged origin in which the two original endpoint points are

    P_E=(-X_E,h), P_C=(X_C,h),
    X_E>0, X_C>0, h>=0, X_E+X_C<=sqrt(2).                 (1)

They are actual minimum-support points on endpoint sides with inward
unit normals

    n_E=(-b_E,a_E), n_C=(b_C,a_C),
    0<a_i<b_i, a_i^2+b_i^2=1.                            (2)

Here an owned side means that n_i is an actual square axis. Each point
may occupy any position on its full closed side, including either end.
Put j_i=J n_i, where J is counterclockwise quarter-turn. Give each
endpoint any nonzero nonnegative combination F_i of its own physical
circle-corner position vectors. Individual physical-corner coefficients
may vanish. Assume only the two tangent signs

    F_E dot j_E <= 0,        F_C dot j_C >= 0.             (3)

**Theorem.** No such physical configuration exists.

The theorem does not assume balance of the endpoint resultants or of
the path, concurrence, original degrees, normal owners at any other
contact, or a fixed shared mean. All additional packing units may remain
present. Its hypotheses concern the two actual endpoint sides, the
original circle and the actual path order only.

## 2. An endpoint tangent sign locates its actual center

First consider the right endpoint, omitting its C subscript. Its entire
actual pose is

    K=P+[0,1]n+[-rho,1-rho]j,  0<=rho<=1,
    P=(X,h), n=(b,a), j=(-a,b).                            (4)

In these own axes the normal coordinate of P is

    N=P dot n=b*X+a*h>0.

Write tau=P dot j+1/2-rho for the center's tangent coordinate.
The center is exactly

    c=(N+1/2)n+tau*j.                                    (5)

Every physical circle corner lies on the far normal side, whose normal
coordinate is N+1. Indeed its corresponding near-side corner has the
same tangent coordinate and a strictly smaller squared norm, since
(N+1)^2-N^2=2*N+1>0.

If tau<0, the unique farthest tangent coordinate is tau-1/2<0. Hence
every physical circle corner would have strictly negative j coordinate,
and the nonzero nonnegative resultant F would satisfy F dot j<0.
This contradicts (3). Therefore tau>=0. When tau=0 both far-side
corners may be physical circle corners; the argument preserves both
and either possible zero individual coefficient.

In particular c dot f>0, by (5). Its e coordinate is also positive,
directly from the actual full side in (4):

    c dot e=X+b/2-a*(1/2-rho)
           >=X+(b-a)/2>0.                               (6)

Let delta in(0,pi/2) be the center angle above the positive e axis,
and let phi=atan(a/b) in(0,pi/4). Equation (5), N+1/2>0 and tau>=0
give delta>=phi. Put v=delta-phi>=0 and r=|c|.

For the left endpoint reflect only the displayed e coordinate. Under
this reflection n_E becomes (b_E,a_E), while j_E becomes the negative
of the new counterclockwise tangent. Thus its sign in (3) becomes the
same nonnegative tangent sign just treated. Consequently its actual
center has negative e coordinate, positive f coordinate, and angle
pi-delta_E with

    0<phi_E<=delta_E<pi/2.

For the right endpoint its angle is delta_C, with the analogous
inequalities. No circle force was replaced by the center in this
argument; the signs of the physical corner resultants determined the
sign of the actual center's own tangent coordinate.

## 3. Three actual contacts force a very small upper angular gap

Every physical circle-touching unit has center radius at least

    r>=R-1/sqrt(2)>5/4,                                  (7)

because R>=79/40 and 1/sqrt(2)<29/40. Consecutive physical unit
centers have distance at most sqrt(2), by going through any actual
common point. For their minor angle gamma the cosine law gives

    cos(gamma)
      =1-[|c-c'|^2-(|c|-|c'|)^2]/[2*|c|*|c'|]
      >1-16/25=9/25.

The strict sign remains when the numerator is nonpositive, since
then the cosine is at least one. Thus every actual path-edge angle
is less than theta=acos(9/25).

By Section 2 and the actual counterclockwise lift premise, the total
endpoint angle along the path is precisely

    L=pi+delta_E+delta_C.                                (8)

It is between pi and 2*pi, so no extra turn is hidden in this equality.
There are at most three contacts, whence

    delta_E+delta_C<alpha:=3*theta-pi.                    (9)

If there are fewer than three contacts the same conclusion follows
from the still stronger L<k*theta, k<=2; in fact that already
contradicts L>pi since theta<pi/2.

Here pi/3<theta<pi/2 and the triple-angle identity gives

    cos(alpha)=13959/15625,
    sin(alpha)=1204*sqrt(34)/15625.

Since alpha lies in(0,pi/2), the exact positive comparisons

    4*13959^2>3*15625^2,
    100*13959>89*15625,
    400*1204^2*34<81*15625^2

give

    0<alpha<pi/6,   cos(alpha)>89/100,
                     sin(alpha)<9/20.                  (10)

Only the complete radius lower bound (7) was used. There is no upper
radius bound in this theorem.

## 4. A continuous lower bound for each original endpoint abscissa

Return to the right endpoint notation of Section 2. By (9),

    0<=v=delta-phi<=delta<pi/6.

The farthest actual corner has own coordinates

    (r*cos(v)+1/2, r*sin(v)+1/2).

For v=0 this remains an actual physical corner even if its individual
circle coefficient is zero. Thus, in the entire closed mask interval,

    R^2=r^2+r*(cos(v)+sin(v))+1/2.                        (11)

Set

    d=sqrt(R^2-1/4)-1,     r_0=d+1/2.

We have d>9/10: at R=79/40 the positive squared reserve over
(19/10)^2 is

    (79/40)^2-1/4-(19/10)^2=13/320>0.

Also R^2=r_0^2+r_0+1/2. Subtraction from (11) yields the exact
identity

    (r_0-r)*(r_0+r+1)=r*(cos(v)+sin(v)-1).                (12)

Its right side is nonnegative, so r<=r_0. Since
r/(r_0+r+1)<1/2 and cos(v)+sin(v)-1<=sin(v), we obtain

    r>=r_0-(1/2)*sin(v),                                 (13)

with equality allowed at v=0. Every side position rho in(4) gives

    X=r*cos(delta)-b/2+a*(1/2-rho)
      >=r*cos(delta)-(cos(phi)+sin(phi))/2.                (14)

We now prove, on the whole continuous interval,

    X>=g(delta):=d*cos(delta)-(3/5)*sin(delta).             (15)

Put c=cos(delta), s=sin(delta). Combining (13)--(14), (15) follows
once

    c+(6/5)*s
      >=cos(phi)+sin(phi)+c*sin(delta-phi)                 (16)

is proved. The right side of (16) is exactly

    (1+c*s)*cos(phi)+s^2*sin(phi)
      <=sqrt((1+c*s)^2+s^4)=sqrt(1+2*c*s+s^2)

by Cauchy--Schwarz. The left side of (16) is positive, and its squared
excess over the last radicand is

    (c+(6/5)*s)^2-(1+2*c*s+s^2)
      =(2/25)*s*(5*c-7*s)>=0.                            (17)

Indeed delta<pi/6 gives 7*s<5*c; the closed endpoint delta=0 is
harmless. This proves (16) and (15) without sampling or a local
orientation expansion. The reflected left endpoint satisfies the
identical lower bound with its original X_E and delta_E.

## 5. The two actual abscissae exceed a unit diagonal

On [0,alpha], the function g is positive and strictly decreasing:

    g(delta)>=(9/10)*cos(alpha)-(3/5)*sin(alpha)
             >(9/10)*(89/100)-(3/5)*(9/20)>0,
    g'(delta)=-d*sin(delta)-(3/5)*cos(delta)<0.

It is strictly concave because g''=-g<0. For positive x,y with
x+y<alpha, concavity on [0,x+y] therefore gives

    g(x)+g(y)>=g(0)+g(x+y)>g(0)+g(alpha).                 (18)

Apply this to the actual delta_E,delta_C from (9), using (15) for
both original endpoint sides. We obtain

    X_E+X_C
      >=g(delta_E)+g(delta_C)
      >d*(1+cos(alpha))-(3/5)*sin(alpha)
      >(9/10)*(1+89/100)-(3/5)*(9/20)
       =1431/1000>10/7>sqrt(2).                          (19)

The last two strict comparisons are the integer facts
1431*7>10000 and 100>98. Equation (19) contradicts the complete
endpoint-distance premise in (1). This proves the theorem.

## 6. Preservation and use boundary

The proof covers every actual endpoint side coordinate, all physical
circle masks and every individual zero circle weight. It proves the
whole continuous orientation interval by (12)--(18). It introduces
no substitute contact point, no new square at an averaged force
application, no equation at an internal path unit, and no restriction
on any other body's true degree. The circle origin is never translated
to a hub corner.

For a graph caller, the actual counterclockwise minor path order,
the endpoint side axes, both tangent signs and the common-height
chart must all be established. A local graph reduction alone does
not imply these premises. This file changes no original fine or
coarse gate, ledger, source, Lean file or external branch.

The theorem itself is self-contained: all geometric, trigonometric
and scalar comparisons used in it are proved above. Its forthcoming
four-spoke pentagon application supplies the signs from the original
E2 and complete C3 equations; the theorem never assumes those degrees.
