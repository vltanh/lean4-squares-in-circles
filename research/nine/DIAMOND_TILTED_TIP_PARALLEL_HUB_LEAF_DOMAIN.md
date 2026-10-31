# A parallel hub in the tilted-tip S/S diamond has a lower outer leaf

Date: October 27, 2026.

**Status: complete fresh hand necessary-domain theorem; full independent
review requested.** This is a complete genuine-leaf feature reduction,
not an exclusion of the remaining lower-leaf domain. Keep the actual
H4/K3/B3/C2 graph, both real S leaves, every original mean and all nine
squares from DIAMOND_NONPARALLEL_S_TIP_FULL_DEGREE_DOMAIN.md.

Use that source's tilted B axes and suppose B owns HB East and H owns
the reverse horizontal axis. Thus the actual rectangles and mean are

    B=[-U,delta] times[-V,1-V], delta=1-U,
    U=d*a, V=d*b, a>b>0, U^2+V^2=d^2,
    H=[delta,delta+1] times[h-1,h],
    P_HB=(delta,-t*b), t=d-sigma, 0<=sigma<=1/a.

Write D=1-V and A=1+delta. The complete original B-to-K alternatives
are owned North, or the strict Northeast vertex W=(delta,D). In
particular K contains W in the latter alternative; in the former it
lies wholly in y>=D. Retain

    |delta|<=epsilon<1/60, 0<V<13/50,
    d=1+epsilon, R^2=(d+1)^2+1/4<=1105/256.

**Theorem.** The real H leaf is necessarily strict at its lower outer
vertex (A,-v), where

    H=[delta,1+delta] times[-v,1-v],
    0<v<13/50, A^2+v^2=d^2,
    -epsilon<delta<epsilon,
    V^2+v^2=4epsilon+2epsilon^2-2delta^2.             (1)

No H3 or K2 equation is assigned. The proof below retains the actual
full H4 equation whenever it is used.

## 1. A small owned face cannot carry two physical boundary neighbors

We first prove the exact physical fact needed here. Let an actual
unit have a vertical face x=epsilon whose height interval is contained
in[-1,1] and has length one. Two distinct physical boundary neighbors
cannot both lie beyond that face in x<=epsilon and touch it.

Every actual port (epsilon,y) belonging to a physical boundary square
has |y|>3/5, since

    (R-sqrt(2))^2>419/1000>1/3600+9/25.

The two ports cannot have opposite signs: their vertical distance
would exceed6/5, whereas the actual face has length one. Reflect
vertically so both heights are positive. Each neighbor center has

    epsilon-1/sqrt(2)<=c_x<=epsilon-1/2,
    c_y>3/5-1/sqrt(2)>-3/20.

The first interval follows from the actual square halfwidth in the
face-normal direction; the second uses its actual port-to-center
distance at most1/sqrt(2). In particular |c_x|<3/4. Every boundary
center has norm greater than27/20, so

    c_y^2>729/400-9/16=63/50>1.

The lower bound c_y>-3/20 selects c_y>1. Every contained center has
norm less than91/60. Thus the two actual centers lie in a rectangle
of width less than1/4 and height less than3/5. Its squared diameter
is less than1/16+9/25=169/400<1. This contradicts the disjoint
open radius-1/2 incircles of two distinct unit squares. All actual
face endpoints and both physical circle masks are included.

## 2. An owned East genuine H leaf is impossible

Such a leaf requires delta=epsilon and0<=h<=1. The actual H leaf
force and HB force are horizontal. In the physical H-B-K triangle,
HB is H-owned West, so n_HK has nonpositive x component.

If HK is owned North or South, the pure unit-triangle side-normal
lemma at H in H-K-C gives HC the same weak vertical sign. The full
H4 vertical equation is then impossible. If HK is owned West, that
same physical lemma and the full vertical equation force HC to be
West too. Section1 excludes these two actual boundary neighbors on
the one small H face.

Otherwise HK strictly exposes the Northwest or Southwest H vertex.
The full H4 vertical equation forces HC to have the opposite strict
vertical sign. A vertical H-owned HC axis is forbidden by the
physical side-normal dot-product test; a horizontal axis cannot
balance that nonzero component. The strict opposite vertex is
forbidden by the actual H-K-C triangle. Consequently HK and HC must
use the two left vertices. Their respective heights h and h-1 both
have absolute value greater than3/5 by the boundary-point bound.
This contradicts h+(1-h)=1. This exhausts the original normal cover.

## 3. The remaining genuine H features

Owned West is impossible because its support is -delta<d. An owned
North leaf requires h=d and delta<=0. But t>=-delta/a>=0, so the
actual HB mean has height -t*b<=0, below H's bottom epsilon>0.
A strict upper-left leaf likewise requires delta<0 and
h=sqrt(d^2-delta^2)>1; again the HB mean is negative, below H.

All near and zero-coordinate endpoints of these cases are the owned
axes just handled. A strict upper-right or lower-right leaf must
have outer x coordinate A and nonzero vertical coordinate of absolute
value v with A^2+v^2=d^2. In particular0<v<13/50. Besides these
two outer vertices, only the following near-South possibilities
remain:

* an owned South leaf, H top h=-epsilon and delta<=0;
* a strict lower-left leaf, delta<0 and H top
  h=1-sqrt(d^2-delta^2) in[-epsilon,0).

We now exclude the upper-right and both near-South possibilities,
including their actual shared HB endpoints.

## 4. Physical routing to K above the H top

In each of those three possibilities, H top h is strictly below
B top D. In the upper-right case h=v<13/50<D. In the near-South
cases -epsilon<=h<=0<D. Since the original HB mean belongs to both
squares, h>=-V. The H-B triangle side-normal test still gives
(n_HK)_x<=0.

An owned South HK normal cannot reach W or any unit in y>=D.
For the strict Southwest H vertex, the vertical distance to W is

    D-(h-1)=2-V-h>37/25>sqrt(2)

in the upper-right case and is still larger in the near-South cases.
It therefore cannot belong to K in the strict-W row. In the
owned-North B row, K lies above D and cannot reach any H point at
all; that whole row is already impossible here.

Consider an owned West HK in the strict-W row. K would lie in
x<=delta and contain both W=(delta,D) and an actual H-face point
(delta,y), y<=h<D. These distinct points force a vertical K face.
The open segment between them includes an open interval of B's
right face, since h>=-V. Both K and B have their interior on its
left. Their interiors would overlap. This includes y=h=-V.

A strict Northwest HK could act only at R=(delta,h). If h>-V,
B fills the left local half-plane there, while H occupies the
lower-right quadrant. A third unit at R must occupy the exact
upper-right quadrant: its connected local sector has angle at
least90 degrees. It is then aligned, with a positive shared segment
on H's top, so the actual HK normal is North, not strict Northwest.
If h=-V, B and H occupy the upper-left and lower-right quadrants.
The two remaining components are the upper-right and lower-left
quadrants. The latter cannot contain W above R. The same exact
upper-right conclusion follows. All actual coincident endpoints
are therefore covered.

Positive-x HK features were already excluded by the H-owned HB
axis. The complete physical cover leaves only

    n_HK=North, K subset{y>=h},

in the strict-W row, and leaves no possibility in the owned-North
B row.

## 5. The upper-right H leaf contradicts the full H4 equation

Its real leaf force has a strictly positive vertical component.
HB is horizontal, HK is North by Section4, and the physical H-K-C
side-normal lemma makes the HC vertical component nonnegative.
The full actual H4 vertical equation cannot sum to zero. No
equation or degree restriction at K or C was used.

## 6. Every near-South H leaf makes K circle-clear

Write h=-w,0<=w<=epsilon. By Section4, HK is North and K contains
the strict B port W=(delta,D), D>37/50. If K owns its minimum-y
support, it is parallel to B and H. Its minimum support for the
strict Northeast B-to-K normal is then its lower-left vertex at
height -w. It cannot contain W at that support, since D>0.

Otherwise K has an actual unique bottom vertex T and a full frame

    K=T+[0,1]u+[0,1]v,
    u=(c,s), v=(-s,c), c,s>0, c^2+s^2=1,
    T_y=-w.

The actual B-to-K normal N has both components positive, so N.u>0.
Its minimum support on K is either T, the full side T+[0,1]v, or
T+v. Since W_y=D>0, it is not T. Hence the unchanged point W has
the literal form

    W=T+lambda*v, 0<lambda<=1,
    T=(delta+lambda*s,-w), lambda*c=D+w.

This retains every actual K-owned side mean as well as the strict
left-vertex alternative. The four actual K corners are

    T,
    T+u=(delta+lambda*s+c,s-w),
    T+v=(delta-(1-lambda)*s,c-w),
    T+u+v=(delta+c-(1-lambda)*s,c+s-w).

For T and T+v, the horizontal magnitude is less than61/60 and
the vertical magnitude is at most1. For T+u it is less than43/30
and at most1, respectively, using sqrt(2)<17/12. For the opposite
corner the magnitudes are less than61/60 and17/12. Every one is
strictly circle-clear, since

    (43/30)^2+1=2749/900<17/4,
    (61/60)^2+(17/12)^2=10946/3600<17/4.

This contradicts the actual positive total circle load on K.
No K3 force or circle weight was replaced or shortened.

## 7. Exact surviving domain

Only the lower-right strict genuine leaf remains. Its radius identity,
combined with U=1-delta, gives exactly(1). The two strict positive
depths give -epsilon<delta<epsilon. All actual HB and BK means
remain; this theorem has not chosen a new HK normal in the surviving
domain or asserted that any of its configurations exists.

The pure triangle normal/vertex facts used above are Section1 of
RADIAL_TRIANGLE_CONCURRENCE.md only. Its positive-radial aggregate
theorem is not applied to the present H4 or K3. This proof invokes
no absent earlier hub/tip proof, numerical pose, metadata edit,
remote write, compilation or CI.
