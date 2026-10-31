# A shallow strip at an origin root has room for at most one true loaded degree-two neighbor

Date: October 27, 2026.

**Status: complete proposed uniform local theorem, pending full root and
separate independent review.** No original gate or shared ledger is
changed.

Keep all nine actual unit squares and the common compatible physical
certificate. Write

    D=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60, R<=sqrt(1105)/16.

In particular R>sqrt(17)/2. Suppose an actual origin-interior root has
own coordinates

    H=[-sigma,1-sigma] times [-w,1-w],
    0<sigma<=epsilon, 0<w<1/2.                         (1)

H's actual degree and complete external forces are arbitrary.

**Theorem 1.** At most one actual positive neighbor Z of H can have
both its true degree equal to two and positive total circle load,
while its unchanged actual HZ application lies in the closed strip

    -sigma<=x<=0.                                    (2)

Every physical circle mask, individual zero corner weight, contact
owner and side-mean endpoint is retained. The conclusion concerns
the actual positive application, not every zero-stress contact of Z.

The proof puts all such real centers in one rectangle whose squared
diameter is 71549/90000<1. It needs no assumption on the other
positive neighbor of Z, and gives no degree-two equation to H.

## 1. The actual port is high, small in radius, and has a nonpositive-x circle corner

Every contained unit center has norm less than 91/60, by
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1. Every physical
boundary center has norm greater than 27/20 in the present strict
high-radius interval: R>103/50 and 1/sqrt(2)<71/100 give

    |c_Z|>=R-1/sqrt(2)>27/20.                          (3)

Also

    r=R-sqrt(2)>129/200.

Let p=(x,y) be any actual application in (2). It belongs to the
boundary of H. Since Z physically touches the containing circle,

    |p|>=r.

If y<=0, then |p|^2<=epsilon^2+w^2<1/3600+1/4<r^2,
a contradiction. In fact

    y>16/25,

because

    (129/200)^2-(1/60)^2-(16/25)^2=2213/360000>0.

At the same time (1) gives y<=1-w<1 and |x|<=epsilon, so

    |p|^2<epsilon^2+1<D^2.                            (4)

A unit with two physical circle corners is the physical radial S
form, all of whose points have norm at least D. Thus Z has exactly
one physical circle corner z. Its total circle load is positive.

The complete loaded-degree-two parallel cover is the one in
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, Lemma N.4, together with
the contained-neighbor exclusion of opposite parallel directions
recorded in TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1.
It applies with arbitrary neighboring degrees. The only same-sign
parallel possibilities are radial S or D with their actual inner
applications. The S possibility was just excluded by (4). In the
D possibility all actual pair applications equal its radial inner
vertex p, so z is a positive multiple of p and z_x<=0.

If Z's original pair lines are nonparallel, the conditional part
of that same genuine loaded-tip theorem gives a positive proper
radial concurrence, without needing a physical boundary neighbor:

    q_Z=t*z, t>0,
    q_Z=p+alpha*n, alpha>=0,                           (5)

where n is the unchanged H-to-Z normal. The separate boundary-
neighbor condition in the stronger usual formulation is used only
to establish nonparallelism; here this is already the stated case.

Every outward H normal at a point of (2) has n_x<=0. A positive
x component would expose the opposite own side x=1-sigma>0.
Therefore (5) gives q_Z,x<=p_x<=0, and hence z_x<=0.

We have proved in the complete original parallel/nonparallel cover

    p_y>16/25, |p|<D, z_x<=0.                          (6)

The possible radial D endpoint remains in (6); no false positive
proper length is imposed on it.

## 2. The actual center also has nonpositive x coordinate

We prove c_Z,x<=0 by the complete support-feature cover of the
unchanged port p. This implication is geometric once (6) holds.

### 2.1. A relative interior point on H's left side

Here the H-to-Z normal is west, and the entire Z lies in
x<=-sigma. Its center is therefore strictly negative in x.
The lower-left H corner is impossible by p_y>16/25, so only
the top-left corner remains for Section 2.3.

### 2.2. A relative interior point on H's top side

Here the normal is north and the whole Z lies in y>=p_y. If Z
has a horizontal bottom side, it is aligned with H; a positive
center x coordinate would make its physical far circle corner
the positive-x corner, contrary to z_x<=0.

Otherwise p is its unique lowest vertex. Write

    Z=p+[0,1]u+[0,1]v,
    u=(C,S), v=(-S,C), C,S>0, C^2+S^2=1.

The actual own projections satisfy

    p.u=x*C+y*S>-sigma>-1/2,
    p.v=-x*S+y*C>0.

Thus both own center coordinates are positive. Its unique farthest
corner is the opposite vertex z=p+u+v=2c_Z-p. Consequently

    c_Z,x=(p_x+z_x)/2<=0.

### 2.3. The actual top-left H corner, with every Z feature

Now p=(-sigma,1-w). H's open tangent quadrant at p is southeast.
The unchanged normal is northwest, allowing either axis endpoint.

If p is in a relative interior of a Z side, write its inward
normal from H as n=(-a,b), a,b>=0, a^2+b^2=1, and take the
perpendicular tangent t=(b,a). Then

    c_Z=p+(1/2)n+tau*t, |tau|<=1/2.

The axis endpoints are already the preceding side calculations.
For a,b>0, suppose c_Z,x>0. In the n,t frame,

    c_Z.n=p.n+1/2=sigma*a+p_y*b+1/2>0,
    c_Z,x=-a(c_Z.n)+b(c_Z.t)>0.

Hence c_Z.t>0 as well. The actual farthest circle corner is
therefore z=c_Z+(n+t)/2. But

    c_Z,x<=-sigma+(b-a)/2.

Its assumed positive sign implies b>a and therefore
z_x=c_Z,x+(b-a)/2>0, contrary to (6).

If p is a Z vertex, its ninety-degree inward tangent cone must
avoid H's open southeast quadrant. Its ordered inward axes may
therefore be written

    u=(cos(theta),sin(theta)),
    v=(-sin(theta),cos(theta)), 0<=theta<=pi.

These are all allowed cones, including both quadrant endpoints.
If c_Z,x>0, the identity

    c_Z,x=-sigma+(cos(theta)-sin(theta))/2

forces 0<=theta<pi/4. Both axes then have nonnegative upward
components. Since p_y>0 and sigma<1/60, their own projections
satisfy p.u>-1/2 and p.v>0. Thus the unique farthest corner is
again z=2c_Z-p, whose x coordinate would be positive. This is
the same contradiction.

Side endpoints belong to this vertex case. There is no possibility
that p is in the open interior of Z, by physical disjointness.
All support features have now been covered, proving c_Z,x<=0.

## 3. One exact center rectangle proves uniqueness

Every actual point of a unit is at distance at most 1/sqrt(2) from
its center. From (6), the bound 1/sqrt(2)<71/100, and Section 2,

    -109/150<c_Z,x<=0,
    c_Z,y>16/25-71/100=-7/100.                         (7)

If c_Z,y<=0, then (7) would give

    |c_Z|^2<(109/150)^2+(7/100)^2<(27/20)^2,

contrary to (3); the exact reserve is 5803/4500. Hence c_Z,y>0.
Using (3) once more,

    c_Z,y^2>(27/20)^2-(109/150)^2
            =1+26501/90000>1.

All possible centers therefore lie in the same rectangle

    -109/150<x<=0, 1<y<91/60.

Its squared diameter is

    (109/150)^2+(91/60-1)^2=71549/90000<1.              (8)

Two distinct actual unit squares have centers at least one apart,
since their open radius-1/2 incircles are disjoint. Equation (8)
therefore permits at most one such actual Z. This proves Theorem 1.

## 4. Exact terminal-four-block consequence

Suppose H also carries a genuine terminal C4 with both endpoint
tips loaded and all private degrees two, or a terminal hub diamond
with its true private K3 and two true loaded tip2 stars. Suppose
some further actual true loaded degree-two neighbor B, distinct
from those private vertices, has its actual H port in (2).

By Theorem 1, neither of the terminal block's two genuine loaded
endpoint tips can have its original application in (2). Both
applications therefore have positive x coordinate. The unchanged
private C4/diamond equations and the full coupled cap/parallel
cover in ROOTED_SHALLOW_INTACT_FOUR_BLOCK_EXCLUSION.md,
Sections 1,3--5, now apply exactly at this fixed-port scope.

For clarity, the nonparallel outer root intersection is a negative
positive combination of the two original outer forces. Since their
port x coordinates are positive, their normal x components are
nonnegative; the negative intersection makes both components
strictly positive. Both ports are proper and belong to the far
own side x=1-sigma>59/60. The exact moment-slope estimate gives
support at least (1-sigma)/n_x, and the coupled neighbor-center
cap has squared diameter 713/720<1. The full parallel cover has
the near side forbidden, the far side cap 361/900<1, and a
negative-x port on either transverse side by strict straddling.

Thus the entire displayed terminal block is impossible. Its private
hub in the diamond retains all three real forces. The additional
neighbor B is used only with its actual loaded degree-two equation;
H's full aggregate, additional loads and every other actual body
remain unchanged. This is a local implication, not a declaration
that a complete original coarse family has already been covered.
