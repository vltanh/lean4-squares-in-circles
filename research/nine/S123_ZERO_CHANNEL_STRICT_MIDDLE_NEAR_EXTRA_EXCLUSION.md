# No near-origin extra in the full zero-channel strict-middle S123 frame

Date: October 27, 2026.

**Status: complete physical theorem with an exact four-variable
separating-axis certificate, submitted for full independent and root
review.** The original strict-middle necessary-domain source27eee13e
supplies the literal caller below; its separate full review must be
retained when this theorem is joined into an original proof family.
The physical theorem itself states all of its premises explicitly.

## 1. The actual root, leaf and transmitter strip

Let actual interior-disjoint unit squares A,U,L have the following
fixed-origin chart:

    1/50<V<13/50,       epsilon=V^2/4,       d=1+epsilon,
    A=[epsilon-1,epsilon] times[-V,1-V],

    e=(-(1-epsilon),-V)/d,
    j=(V,-(1-epsilon))/d,
    L=[d,d+1]e+[-1/2,1/2]j,

    [epsilon,d] times[-79/200,1/2] subset U.        (1)

The displayed e,j are actual orthonormal axes, since
(1-epsilon)^2+V^2=d^2. The full actual U need only contain
the displayed closed rectangle. No U center, whole transverse
interval or original channel mean is selected.

**Theorem 1.1.** Every other actual unit E whose open interior is
disjoint from A,U,L satisfies

    dist(O,E)>1/8.                                  (2)

There is no degree, frame, circle-mask or force premise on E.
The proof uses the actual V-dependent A and real tilted L,
not a fixed-orientation replacement of either square.

## 2. The deeper part of the complete V interval

If V>=13/100, the actual union A union U contains the entire
closed rectangle

    [-13/100,13/100] times[-13/100,13/100].

Indeed A covers the part x<=epsilon, and the contained U strip
covers the part x>=epsilon. Their common line leaves no gap.
The left A side is less than-13/100, the right U side exceeds
13/100, A's top exceeds37/50, and U contains the full vertical
interval[-79/200,1/2].

The open rectangle is contained in the interior of that union.
An interior point of another actual unit cannot meet the closed
union of these interior-disjoint occupied squares. Thus any such
E avoids the open disk of radius13/100. This already implies
dist(O,E)>=13/100>1/8.

It remains to treat the complete closed interval

    1/50<=V<=13/100.                                (3)

Including the two endpoints only strengthens the physical result.

## 3. Complete actual square parameters and the distance guard

Choose an actual axis frame of E with angle in[0,pi/2]:

    u=(c,s), v=(-s,c), c,s>=0, c^2+s^2=1,
    c_E=a*u+b*v,
    E=c_E+[-1/2,1/2]u+[-1/2,1/2]v.

Every unit orientation is included by rotating its own frame by
an integer multiple of pi/2. The signed center coordinates are
not made nonnegative or reordered.

If E meets the closed D_(1/8), necessarily

    -5/8<=a,b<=5/8.                                 (4)

Its exact squared distance from O is

    max(|a|-1/2,0)^2+max(|b|-1/2,0)^2.               (5)

Set z=tan(theta/2), so the whole actual angle interval is

    0<=z<=1,
    c=(1-z^2)/(1+z^2), s=2z/(1+z^2).                (6)

Our complete parameter box consists of (3),(4),(6).
A box may be excluded solely when the lower bound from (5)
is strictly greater than1/64. Equality is retained. Every
other accepted box proves an actual open overlap with A,
the contained U strip, or the real L.

## 4. Complete separating-axis formulas

For any axis-aligned actual rectangle
R=[l_x,h_x] times[l_y,h_y], let

    X=a*c-b*s, Y=a*s+b*c, r=(c+s)/2,
    R_u_min=l_x*c+l_y*s, R_u_max=h_x*c+h_y*s,
    R_v_min=-h_x*s+l_y*c, R_v_max=-l_x*s+h_y*c.

The complete eight strict overlap inequalities are positivity of

    X+r-l_x, h_x-X+r, Y+r-l_y, h_y-Y+r,
    a+1/2-R_u_min, R_u_max-a+1/2,
    b+1/2-R_v_min, R_v_max-b+1/2.                     (7)

We use (7) for the actual V-dependent A and the actual contained
U rectangle in (1), with epsilon=V^2/4 retained throughout.

Here are the full additional formulas for the real tilted leaf.
Put

    alpha=(1-epsilon)/d, beta=V/d,
    H=alpha*c+beta*s>0,
    K=beta*c-alpha*s,
    r_L=(H+|K|)/2,       C0=d+1/2.

The leaf center's E-axis coordinates are -C0 H,-C0 K.
The actual E center's leaf-axis coordinates are

    E_e=-H*a-K*b,       E_j=K*a-H*b.

Thus its complete eight strict overlap inequalities with L are

    E_e+r_L-d, d+1-E_e+r_L,
    E_j+r_L+1/2, 1/2-E_j+r_L,
    a+1/2+C0 H+r_L, -C0 H+r_L-a+1/2,
    b+1/2+C0 K+r_L, -C0 K+r_L-b+1/2.                (8)

These are again the two actual own axes of each of the two
rectangles. They retain every sign of K. The same r_L is
valid in both frames because their rotation has absolute
entries H and |K|.

For two rectangles the four actual side-normal directions are
the complete separating-axis cover. Therefore positivity of
all eight inequalities in either (7) or (8) proves overlap of
their open interiors. No contact normal or degree of E is
assumed.

## 5. Entire exact rational interval certificate

The complete standalone checker is

    certificates/s123_zero_channel_strict_middle_near_extra_certificate.py.

It uses only integers and the standard-library Counter. There
are no floating-point operations, samples, external solvers,
selected poses or unreported discarded regions.

Use the lattice N=2^40. An integer interval[L,H] represents
[L/N,H/N]. Rational inputs use floor and ceiling; addition,
negation and subtraction are exact. Multiplication takes all
four endpoint products and rounds outward. Squares use zero
as the lower numerator exactly when the interval contains
zero. Absolute values use the complete sign cover. Division
uses the reciprocal interval of a strictly positive divisor,
again rounded outward. Every divisor in the displayed geometry
is positive throughout the complete parameter box.

The functions in (6) are evaluated by their exact monotonicity
on[0,1]: c decreases and s weakly increases. The interval
endpoints are rational functions of the actual z endpoints
and are rounded outward. All remaining quantities in
Sections3--4 are evaluated with these outward rules. Separate
intervals enlarge correlated possibilities; they never
restrict them.

For a given box, first evaluate the exact own-center lower
distance bound (5). If it is strictly above1/64, classify
the whole box as missing the required closed disk. Otherwise
evaluate (7) for A, (7) for the U strip, and (8) for L in
that order. Accept the whole box only when one of these
three tests has all eight lower margins strictly positive.

If no such test succeeds, bisect a longest normalized side.
The four compared integer widths are

    width(a), width(b), floor(5 width(z)/4),
    floor(125 width(V)/11).

Take the first side in that order on a tie, split at its
integer midpoint, retain the common closed face in both
children, and visit the lower child first. The rational V
endpoints in (3) are initially rounded outward, so the
complete real box is included.

The full exact output is:

| Terminal classification | Boxes | Minimum positive overlap numerator over2^40 |
| --- | ---: | ---: |
| Actual A overlap | 1278 | 20622436 |
| Actual U-strip overlap | 4126 | 4372443 |
| Actual real-leaf overlap | 5442 | 471919 |
| Exact distance guard excludes D_(1/8) | 163 | not an overlap test |

There are11008 internal splits,11009 terminal boxes,22017
visited boxes and maximum depth32. The frozen executable
asserts all counts and all three overlap margins exactly.
No unresolved depth, rounding or zero-margin box is accepted.

Every real parameter in the initial closed box lies in a
terminal box. A true near-origin E cannot lie in a distance-
excluded box and must therefore overlap an actual occupied
open interior by (7) or (8). This proves (2) in (3).
Section2 proves the remaining whole V range.

## 6. Literal complete zero-channel strict-M caller

The original common root chart at t=0 satisfies

    A=[epsilon-1,epsilon] times[-V,1-V],
    V^2=4epsilon,

with its actual genuine leaf exactly as in (1).
The complete remaining-domain source

    S123_OWNED_EAST_STRICT_MIDDLE_REMAINING_DOMAIN.md
    SHA256 27eee13ea9a64985b2abd8d5f004603cd92e806c42bfa9db73f53f148ce66a0c

retains both the unique opposite circle corner and the physical
radial M mask. It proves V>1/50 and, using the independently
accepted actual hole/slider theorem, the literal U bounds

    U=[epsilon,d] times[z,z+1],
    1/2<=z+1<=121/200.

Thus z<=-79/200, and the full actual U contains the strip
in (1). The radial-M case has the stronger centered U
conclusion; neither result changes the original channel mean.

Once that complete remaining-domain source has its separate
full review, this is a whole near-extra exit for both remaining
physical M masks, with all original forces, degrees, side means
and all nine actual units retained. The local physical theorem
and certificate in Sections1--5 do not depend on a selected
normal, physical circle mask or a changed U position.

Every arbitrary extra therefore has one complete connected
radius-9/8 arc of at least the accepted delta(R), containing
its actual center direction. Actual exterior routing and the
corresponding free-gap capacity remain separate obligations.
No whole S123 fine or coarse closure is claimed here.

No compilation, CI, remote mutation or shared metadata edit
is used.

