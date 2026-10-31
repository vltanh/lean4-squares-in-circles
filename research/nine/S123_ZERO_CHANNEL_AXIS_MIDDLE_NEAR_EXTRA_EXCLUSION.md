# No near-origin extra in the zero-channel axis-middle S123 frame

Date: October 27, 2026.

**Status: complete physical theorem with an exact rational separating-axis
certificate, submitted for full root and separate independent review.**
This closes the near-origin-extra obligation in the entire t=0,
M-owned-East frame. It retains every original U and C mean before the
accepted canonical-slider conclusion is applied. It does not yet assert
the final exterior-arc routing or whole S123 exclusion.

## 1. Exact actual frame and accepted prerequisites

Keep the original nine-unit packing and the actual component
A--B--M--C--U--A with A--L. A is the true degree-three root;
B,M,C retain their complete loaded degree-two systems; U is the actual
unloaded side transmitter. Suppose that the original channel has t=0
and that the original incoming East force at M is owned by M.

The complete accepted source S123_OWNED_EAST_AXIS_MIDDLE_BOTTOM_GAP.md
gives, with no replacement of either original side mean,

    d=1+epsilon, X_A=1-epsilon, F=1-V,
    V^2=4epsilon,
    29/1250<V<233/10000<1/40,
    0<epsilon<1/7000,

    A=[epsilon-1,epsilon] times[-V,F],
    C=[d,d+1] times[-1/2,1/2].                     (1)

The genuine radial S leaf is the actual square

    L=[d,d+1] e+[-1/2,1/2] f,
    e=(-X_A,-V)/d, f=(V,-X_A)/d.                  (2)

The identity X_A^2+V^2=d^2 makes e,f actual orthonormal axes.
The whole zero-channel hole and canonical-slider theorem
S123_ZERO_CHANNEL_OWNED_RETURN_HOLE_EMPTY.md gives, at the existing
secondary minimum of the sum of squared center norms,

    U=[epsilon,d] times[-1/2,1/2].                 (3)

This is the original canonical packing, not a new chosen transmitter
pose. The same actual original mean -T remains on its two sides. That
source first excludes every inner unit at the full original U position,
then proves (3) by an admissible same-nine motion. Its complete separate
independent review is
REVIEW_S123_ZERO_CHANNEL_HOLE_AND_SLIDER_TRIANGLE_BRIDGES_2026_10_27.md.

The radius-dependent gap source in (1) and its complete exact bounds
have separate independent acceptance in
REVIEW_RADIUS_DEPENDENT_ARC_AND_AXIS_MIDDLE_GAP_ROOTED_BLOCKS_2026_10_27.md.

**Theorem 1.1.** Every other actual unit E, disjoint in its open interior
from the actual A,U,L in (1)--(3), satisfies

    dist(O,E)>1/8.                                (4)

In particular this applies to every arbitrary completion square, with
no orientation, circle mask, graph degree, or force assumption on E.

## 2. Three fixed rectangles inside the actual occupied units

The following rectangles are actual occupied subsets:

    A0=[-99/100,0] times[-23/1000,3/4]  subset A,
    U0=[1/7000,1] times[-1/2,1/2]       subset U,
    L0=[-7/4,-199/200] times[-9/20,-1/4] subset L. (5)

Every open rectangle interior is contained in the corresponding open
unit interior. For A0 and U0 this follows directly from the strict
inequalities in (1). The two horizontal boundary lines of U0 coincide
with the actual U lines, which does not affect its open interior.

Here is the complete verification for L0. At every point (p,q) of L0,
the radial numerator is -X_A*p-V*q. Its minimum is

    (199/200)X_A+V/4.

Subtracting d^2 and using epsilon=V^2/4 gives exactly

    -1/200+V/4-(599/800)V^2-V^4/16
      >-1/200+29/5000-599/(800*1600)-1/(16*40^4)
       =13599/40960000>0.                         (6)

Its maximum is less than

    7/4+(9/20)(1/40)=1409/800<2<d(d+1).

Thus the complete radial coordinate is strictly between d and d+1.
The transverse numerator V*p-X_A*q is greater than -7/160 and less
than 9/20. These bounds lie strictly between -d/2 and d/2, so (2)
contains L0 strictly. This proves (5), including all rectangle edges.

## 3. A universal three-rectangle obstruction

We prove a stronger elementary statement than needed for (4):

**Lemma 3.1.** Let E be any actual unit square. Choose signs and order
of its actual own axes so that

    u=(c,s), v=(-s,c), c,s>=0, c^2+s^2=1,
    c_E=a*u+b*v.

If |a|<=5/8 and |b|<=5/8, then the open interior of E overlaps at
least one of the three fixed open rectangles in (5).

Every square orientation is represented, since a square's axis frame
may be rotated by an integer multiple of pi/2. Both axis endpoints
are retained. Set z=tan(theta/2), where (c,s)=(cos theta,sin theta).
The entire parameter box is

    -5/8<=a,b<=5/8, 0<=z<=1,
    c=(1-z^2)/(1+z^2), s=2z/(1+z^2).              (7)

The proof is an explicit finite rational interval certificate for this
whole closed box. Its only geometric test is the separating-axis
criterion for two rectangles, whose complete formulas follow.

Write an arbitrary rectangle from (5) as

    R=[l_x,h_x] times[l_y,h_y].

The actual E center and world-coordinate halfwidth are

    X=a*c-b*s, Y=a*s+b*c, r_E=(c+s)/2.

Its own projections are [a-1/2,a+1/2] and [b-1/2,b+1/2].
The rectangle's own-axis projection intervals are

    R_u=[l_x*c+l_y*s, h_x*c+h_y*s],
    R_v=[-h_x*s+l_y*c, -l_x*s+h_y*c].              (8)

The interiors overlap if and only if all eight following quantities
are positive:

    X+r_E-l_x, h_x-X+r_E,
    Y+r_E-l_y, h_y-Y+r_E,
    a+1/2-min R_u, max R_u-a+1/2,
    b+1/2-min R_v, max R_v-b+1/2.                  (9)

Indeed these are exactly the strict projection-overlap inequalities
on the two actual own axes of each rectangle. A separating axis of
two rectangles is parallel to one of those four side normals. Thus
(9) proves overlap of their open interiors, including arbitrary closed
side/contact endpoints in the original parameter box.

## 4. Exact complete certificate and positive margins

The complete independently executable arithmetic is saved at

    certificates/s123_zero_channel_axis_middle_near_extra_certificate.py.

It uses only integer arithmetic and the Python standard-library Counter.
There are no floating-point operations, solver calls, numerical
optimizers, external data, or sampled poses. Here are all its interval
rules and covering rules, so its positive conclusion is a finite
mathematical certificate rather than a numerical premise.

Fix N=2^40. Every interval [L,H] represents the exact enclosure
[L/N,H/N]. A rational p/q is enclosed by floor(Np/q), ceil(Np/q).
Interval addition, negation, and subtraction are exact. Interval
multiplication takes the minimum and maximum of the four endpoint
products, dividing by N with floor for the lower and ceiling for the
upper endpoint. Halving uses the same directed rounding.

On an interval [l/N,h/N] for z, the exact monotonicity of the two
rational functions in (7) gives

    c in [(N^2-h^2)/(N^2+h^2), (N^2-l^2)/(N^2+l^2)],
    s in [2lN/(N^2+l^2), 2hN/(N^2+h^2)].           (10)

Those rational endpoints are enclosed on the same lattice with the
same floor/ceiling rule. The function for s is weakly increasing on
the complete closed interval, including z=1. No dependence is falsely
discarded: separate interval enclosures only enlarge the possibilities.

Start with exactly the box in (7). For each box, evaluate (8)--(9)
with outward arithmetic for A0, then U0, then L0. If one rectangle
has all eight strictly positive lower bounds, accept that whole box.
Otherwise bisect a longest normalized side. Specifically compare the
integer widths of a, b, and floor(5*width(z)/4), taking the first in
that order on a tie. Bisect at the integer midpoint, retaining the
common closed face in both children. Visit the lower child first.

The resulting exhaustive tree has precisely the following terminal
rows. Each margin is the minimum of every one of the eight certified
lower bounds in every box assigned to the indicated rectangle.

| Occupied rectangle | Terminal boxes | Minimum positive numerator over 2^40 |
| --- | ---: | ---: |
| A0 | 92 | 575796686 |
| U0 | 388 | 45834217 |
| L0 | 397 | 261885178 |

There are 876 internal splits, 877 terminal boxes, 1,753 visited
boxes, and maximum depth 27. The executable checks every displayed
count and every margin exactly. No unresolved box, precision endpoint,
or non-strict projection comparison is accepted. All terminal margins
are strictly positive rational numbers.

Every parameter in the initial closed box lies in a terminal box,
and that whole terminal box satisfies (9) for an actual occupied
rectangle. This proves Lemma 3.1 for all parameters in (7).

## 5. Complete near-extra conclusion

Suppose an actual E meets the closed disk of radius 1/8. Take an
actual p in that intersection. Since its displacement from the center
has each own coordinate in [-1/2,1/2],

    |a|=|u.c_E|<=|u.p|+1/2<=5/8,
    |b|=|v.c_E|<=|v.p|+1/2<=5/8.

Lemma 3.1 gives an open overlap of E with one of A0,U0,L0.
Section2 places that open rectangle inside the corresponding actual
unit. This contradicts actual interior disjointness. The closed disk
is therefore avoided and (4) follows strictly by compactness.

Consequently each arbitrary extra in this entire canonical t=0,
axis-M frame satisfies the literal premise of
RADIUS_DEPENDENT_NINE_EIGHTHS_INNER_ARC.md. It has one connected
actual radius-9/8 arc of length at least delta(R), containing its
radial center point. The weak arc-length equality remains retained.

This proof does not place those arcs in a particular complementary
interval. The exact bottom-gap theorem gives a strict gap shorter
than 3delta(R), but its full exterior routing must still be supplied
before this frame or the original S123 family is declared closed.
The strict-channel t>0 and strict-M cases are separate physical
domains and are not asserted to satisfy the fixed rectangles (5).

No actual force, normal, physical mask, contact mean, or unit position
is altered in this theorem. No compilation, CI, remote action, or
shared metadata edit is performed.
