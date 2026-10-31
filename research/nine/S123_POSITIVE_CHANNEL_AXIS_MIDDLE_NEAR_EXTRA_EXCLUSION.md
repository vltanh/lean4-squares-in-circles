# Every extra clears the origin in the positive-channel axis-middle frame

Date: October 27, 2026.

**Status: complete physical theorem with an exact rational separating-axis
certificate, submitted for full independent and root review.** Both
entire original t>0 root rows are covered. All original means, circle
masks, forces and nine units remain; the canonical transmitter is
used only after the complete actual hole/slider theorem establishes it.
No exterior-arc routing is asserted in this source.

## 1. Literal actual frame and a uniform positive channel angle

Keep the exact scope of
S123_POSITIVE_CHANNEL_AXIS_MIDDLE_HOLE_AND_SLIDER.md. Its hypotheses
and conclusion, together with the independently accepted
S123_OWNED_EAST_AXIS_MIDDLE_BOTTOM_GAP.md, give

    d=1+epsilon, 0<epsilon<1/597,
    n=(x,-t), f=(t,x), x^2+t^2=1,
    0<t<1/10, x>99/100,
    0<V<1/40, F=1-V, |r|<=epsilon,

    A=[r-1,r] times[-V,F],
    U=[epsilon,d]n+[kappa-1,kappa]f,
    99/250<kappa<1/2.                            (1)

This is the actual U at the existing secondary-minimal packing.
Its full original application mean remains inside its unchanged
two sides, as proved in the complete same-nine slider argument.

The genuine S leaf can be written uniformly as

    L=[d,d+1]e+[-1/2,1/2]g,
    e=(-X_L,-Y_L)/d, g=(Y_L,-X_L)/d,
    X_L^2+Y_L^2=d^2,
    1-epsilon<=X_L<=d<501/500,
    0<=Y_L<1/40.                                 (2)

For the tilted root, X_L=1-r and Y_L=V. For aligned South,
X_L=d and Y_L=0. No tilted-leaf identity is imposed on the
aligned root.

The complete actual channel satisfies the further uniform bound

    t>1/50.                                      (3)

For aligned South this follows from the stronger t>7/200 proved
in Section4.1 of the accepted gap source. For the tilted strict
channel, that source proves V/t<13/25 and

    eta=arcsin(V/d)+arcsin(t)>7/200.

If t<=1/50, both arguments of arcsine lie in[0,1/50]. On this
whole interval the derivative is strictly less than11/10. Thus

    eta<(11/10)(1+13/25)t
          <=418/12500
           =7/200-39/25000,

a contradiction. This proves (3) for both literal rows without
discarding any original channel mean.

**Theorem 1.1.** Any other actual unit E whose open interior is
disjoint from the actual A,U,L in (1)--(2) satisfies

    dist(O,E)>1/8.                               (4)

No circle, orientation, force or graph premise on E is needed.

## 2. Four fixed rectangles are physically occupied

The following four closed rectangles have their open interiors
inside the indicated actual open unit interiors:

    A0=[-99/100,-1/500] times[0,3/4]             inside A,
    U0=[3/100,9/10] times[-1/4,1/4]            inside U,
    L0=[-7/4,-501/500] times[-9/20,-1/4]       inside L,
    U1=[-3/1000,9/10] times[-9/20,-1/4]        inside U. (5)

A0 follows immediately from |r|<=epsilon<1/597<1/500 and
0<V<1/40. Its whole x interval is strictly between r-1 and r,
and its y interval is strictly between -V and F.

For U0, its exact n-coordinate bounds are

    n.p>(99/100)(3/100)-(1/10)(1/4)
            =47/10000>1/597>epsilon,
    n.p<9/10+1/40=37/40<d.

Its f coordinate is greater than -1/4>kappa-1 and less than
9/100+1/4=17/50<99/250<kappa. Hence the entire rectangle
is strictly inside the actual U slab in both own coordinates.

For U1, (3) gives

    n.p> -3/1000+(1/50)(1/4)=1/500>epsilon,
    n.p<9/10+(1/10)(9/20)=189/200<d.

Its f coordinate is greater than -4503/10000>-1/2>kappa-1
and less than

    9/100-(99/100)(1/4)=-63/400<0<kappa.

Thus U1 is another genuine occupied subset of the same unchanged U.
They are not two different squares and are used only as overlapping
test rectangles within the one original transmitter.

For L0, the minimum radial numerator -X_L*p_x-Y_L*p_y is
(501/500)X_L+Y_L/4. Its excess over d^2 is exactly

    X_L(501/500-X_L)+Y_L(1/4-Y_L)>0,             (6)

including the aligned endpoint Y_L=0. The strict inequality follows
from X_L>0, X_L<501/500 and0<=Y_L<1/40. Its maximum is
less than

    (7/4)d+9/800 <(1409/800)d<2d<d(d+1).

The transverse numerator Y_L*p_x-X_L*p_y is greater than
-7/160>-d/2 and at most(9/20)d<d/2. These full corner
bounds prove L0 lies strictly in L for both real leaf types.
This establishes all four physical inclusions in (5).

## 3. The universal actual-orientation rectangle obstruction

Let an arbitrary unit E have actual orthonormal axes

    u=(c,s), v=(-s,c), c,s>=0, c^2+s^2=1,
    c_E=a*u+b*v.

Signs and quarter-turns of its own frame represent every square
orientation this way. If E meets the closed radius1/8 disk,
the actual intersection point gives |a|<=5/8 and |b|<=5/8.
Consequently it suffices to prove open overlap with one rectangle
in (5) throughout the complete closed box

    -5/8<=a,b<=5/8, 0<=z<=1,
    c=(1-z^2)/(1+z^2), s=2z/(1+z^2).             (7)

Here z=tan(theta/2) is only the actual orientation parameter.
No sampled frame or actual pose is reselected.

For clarity, the full geometric test is the same exact four-axis
criterion used in the separately accepted zero-channel near theorem.
For R=[l_x,h_x] times[l_y,h_y], set

    X=a*c-b*s, Y=a*s+b*c, r_E=(c+s)/2,
    R_u=[l_x*c+l_y*s,h_x*c+h_y*s],
    R_v=[-h_x*s+l_y*c,-l_x*s+h_y*c].

The actual open interiors overlap if all eight quantities

    X+r_E-l_x, h_x-X+r_E,
    Y+r_E-l_y, h_y-Y+r_E,
    a+1/2-min R_u, max R_u-a+1/2,
    b+1/2-min R_v, max R_v-b+1/2                   (8)

are positive. These are precisely strict projection overlap on
the two side axes of each rectangle. Their completeness is the
separating-axis theorem for the two actual rectangles.

## 4. Complete exact rational certificate

The entire proof of positivity for the box (7) is the standalone
integer certificate

    certificates/s123_positive_channel_axis_middle_near_extra_certificate.py.

It uses only integers and the standard-library Counter. There are
no floating-point operations, external libraries, solver calls,
sampled poses, tolerances, or data inputs.

Every interval is an outward enclosure on the lattice N=2^40.
A rational p/q is enclosed by floor(Np/q) and ceil(Np/q).
Addition, negation and subtraction are exact. Multiplication takes
all four endpoint products and divides by N with floor at the lower
endpoint and ceiling at the upper. Halving rounds the same way.
For z in[l/N,h/N], its complete exact monotonic rational bounds are

    c in[(N^2-h^2)/(N^2+h^2),(N^2-l^2)/(N^2+l^2)],
    s in[2lN/(N^2+l^2),2hN/(N^2+h^2)].             (9)

They are rounded outwards on the same lattice. Both closed angle
endpoints are retained, and any loss of correlation only enlarges
the interval domain.

Start with the whole box (7). Test the complete inequalities (8)
for A0,U0,L0,U1 in that order. Accept a box only if one rectangle
has all eight strictly positive lower bounds. Otherwise bisect a
longest normalized side, comparing width(a), width(b), and
floor(5*width(z)/4), choosing the first on a tie. Use the integer
midpoint and retain the common closed face in both children.
Visit the lower child first. The complete terminal table is:

| Actual occupied subset | Terminal boxes | Minimum positive numerator over 2^40 |
| --- | ---: | ---: |
| A0 | 128 | 133955327 |
| U0 | 26 | 1660125402 |
| L0 | 2250 | 810566 |
| U1 | 1248 | 1141741 |

There are exactly 3,651 internal splits, 3,652 terminal boxes,
7,303 visited boxes, and maximum depth33. The standalone checker
asserts every displayed count and every exact positive margin.
No unresolved leaf or non-strict separating inequality is accepted.

The initial closed box is the union of its terminal closed boxes,
and every terminal box proves an actual open overlap with an
occupied subset from (5). This is an exact finite proof for the
entire orientation/center domain, not numerical evidence for it.

## 5. Exact physical conclusion and remaining scope

If E met the closed radius1/8 disk, its actual signed own-center
coordinates would belong to (7), because an intersection point has
each own coordinate within1/8 of O and within1/2 of the center.
The exact certificate would force an open overlap with A0, U0,
L0 or U1. Section2 places that overlap inside one of the actual
original units A,U,L, a contradiction. Compactness now gives the
strict clearance (4), including every weak nearest-point endpoint.

Thus every arbitrary completion square in both complete canonical
t>0, axis-M root rows satisfies the literal premise of
RADIUS_DEPENDENT_NINE_EIGHTHS_INNER_ARC.md. Its actual connected
radius9/8 arc has length at least delta(R), with the sharp equality
retained. Routing those arcs is a separate physical obligation.

No original square, mean, circle mask, force or normal is changed.
This theorem does not apply the positive-channel lower bound to
t=0 or to strict-incoming M. No compilation, CI, remote mutation,
or shared metadata edit is performed.
