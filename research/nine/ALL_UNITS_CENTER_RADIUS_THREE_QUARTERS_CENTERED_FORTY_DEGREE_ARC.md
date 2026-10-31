# Every contained unit with center radius at least three quarters contains a centered forty-degree arc

Date: October 28, 2026 UTC. Author: pentagon continuation.
Read base: `c31ecd109097dde3c8faa1db11a84655575e87ab`.

**Status: complete proposed force-free hand theorem and literal caller
assessment, submitted for full root and separate independent review.**
The proof is self-contained. It uses one affine center-radius bound and
one two-square identity, without coefficient tables, pose samples,
normal selection, or computational proof premises. No original
checkbox or existing frozen source is changed.

## 1. Uniform statement for actual boundary and completing units

Put

    Q=1105/256,       rho=9/8,       theta=pi/9.

Let E be an actual closed unit square contained in the disk D_(sqrt(Q))
about the unchanged origin. If its actual center c satisfies

    |c|>=3/4,

then the entire **closed** radius-rho arc centered at arg(c), with
halfwidth theta, belongs to the **open** interior of E.

There is no physical circle-contact, force, degree, origin-clearance,
normal-owner, mean, graph, or other-body premise. In particular the
square may be an arbitrary physical completion unit. Every actual
orientation and every endpoint of the center-radius domain is included.

Consequences are:

1. The minor center-direction separation of two such interior-disjoint
   actual units is strictly greater than 2pi/9.
2. A packing in D_(sqrt(Q)) contains at most eight units whose center
   radii are at least 3/4.
3. Every physical boundary unit in the **whole original window**
   79/40<=R<=sqrt(Q) has this actual centered forty-degree arc on the
   radius-9/8 circle. No high-radius restriction is needed.

These are physical angular statements. A caller locating a whole
completion intersection in a pocket must still prove its actual
connectedness or the required center-direction routing.

## 2. A sharper affine center-radius bound on the entire orientation domain

Choose signs of the actual own axes so c=r(x,y), with

    r=|c|>0,       x,y>=0,       x^2+y^2=1.

The actual farthest corner gives

    r^2+r(x+y)+1/2 <= Q.                                 (1)

Let t=x+y, so 1<=t<=sqrt(2), and set

    L(t)=673/360-(127/360)t.

Then

    r<L(t).                                              (2)

Here is a whole-interval proof. The nonnegative-radius expression
z^2+tz+1/2 is strictly increasing in z, and L(t)>0. Its excess above Q
at z=L(t) is the concave quadratic

    P(t)=-(29591/129600)t^2
            +(35669/64800)t-166709/518400.                (3)

Both endpoint values are positive:

    P(1)=31/57600>0,

    P(sqrt(2))=-134479/172800+(35669/64800)sqrt(2)
               >1383149/6480000000>0.                   (4)

For the strict lower comparison in (4), use
sqrt(2)>141421/100000. Its exact squared reserve is

    2-(141421/100000)^2=100759/10000000000>0.

A concave quadratic is at least its smaller endpoint value on an
interval. Thus (3)--(4) prove (2) for all actual orientations, including
both axis and diagonal-center endpoints. No derivative enclosure,
orientation partition, or numerical coefficient table is used.

## 3. Exact twenty-degree comparisons and one positive two-square identity

The elementary bounds needed below are

    rho cos(theta)>1057/1000,
    rho sin(theta)<77/200,
    cos(theta)>15/16.                                   (5)

For the first, put c0=1057/1125. It lies in (1/2,1), and

    1/2-(4c0^3-3c0)=2964331/2847656250>0.

Since 4z^3-3z is strictly increasing for z>1/2 and
cos(3theta)=1/2, it follows that cos(theta)>c0. Multiplication by
rho=9/8 gives the first inequality of (5).

For the second, put s0=77/225 in (0,1/2). The cubic 3z-4z^3 is
strictly increasing on that interval, and

    3s0-4s0^3=9868243/11390625>0,
    (3s0-4s0^3)^2-3/4
       =289865956321/518985351562500>0.

Comparing with sin(3theta)=sqrt(3)/2 gives sin(theta)<s0, hence
the second inequality. The third follows from the first, since
1057/1125>15/16. All comparisons are strict and all trigonometric
branches are specified.

For x,y on the unit circle the following exact identity holds:

    1/2-(13/16)x-(77/200)y
          +(127/360)x^2+(127/360)xy
      = (167/360)(x+(127/334)y-585/668)^2
        +(10591/240480)(y-91449/105910)^2
        +53509/190638000.                              (6)

A direct check expands the right side to

    (167/360)x^2+(127/360)xy+(1/9)y^2
          -(13/16)x-(77/200)y+7/18.

Its difference from the left side is exactly
(1/9)(x^2+y^2-1), which vanishes. Both square coefficients and the
final rational remainder are strictly positive. Thus, throughout
the actual quadrant,

    (13/16)x-(127/360)x^2-(127/360)xy+(77/200)y
        <=1/2-53509/190638000<1/2.                      (7)

This is one global completed-square proof, not a hidden sign table.
The four rational quantities in (6) are stated explicitly and its
full expansion is provided.

## 4. The entire centered arc, including both center-radius regimes

### 4.1. Centers from three quarters through nine eighths

Suppose 3/4<=r<=rho. For any actual radius-rho point P with angular
displacement |tau|<=theta from c,

    |P-c|^2=r^2+rho^2-2r rho cos(tau)
       <r^2+rho^2-2r rho*(15/16).                       (8)

The last quadratic is convex in r. At r=3/4 it equals63/256;
at r=rho it equals81/512. Both are strictly less than1/4.
Hence every such P lies in the actual open radius-1/2 incircle
of E and therefore in int E. This includes r=3/4, r=rho, and
both tau endpoints, without any containing-boundary assumption.

### 4.2. All larger centers

Now suppose r>=rho. In the actual own frame, the first coordinate
of P relative to c is

    (rho cos(tau)-r)x-rho sin(tau)y.                     (9)

The first term is nonpositive. Its positive part is therefore
at most rho sin(theta)<77/200<1/2.

For the negative part, (2) and (5) give

    (r-rho cos(tau))x+rho sin(tau)y
       <=(r-rho cos(theta))x+rho sin(theta)y
       <=(13/16)x-(127/360)x^2-(127/360)xy+(77/200)y
       <1/2.                                            (10)

The coefficient weakening used here is exact:

    673/360-1057/1000=914/1125<13/16,
    13/16-914/1125=1/18000>0.

The final bound is (7). Interchanging x,y and reversing tau proves
both strict bounds for the second own coordinate as well. Thus
both deviations are strictly between-1/2 and1/2, exactly membership
in the original unit's open interior. Every orientation and both
closed-arc endpoints are retained.

The two regimes cover all r>=3/4. No original square, frame, circle
center, selected normal, or application has been altered.

## 5. Pair separation, packing count, and the full-window boundary corollary

If two actual center directions had minor separation at most2theta,
the midpoint of that minor angular interval would belong to both
closed centered radius-rho arcs. Sections 2--4 put that point in both
open square interiors, a contradiction. The separation is therefore
strictly greater than2theta=2pi/9.

For the packing count, each closed centered arc is compact and lies
inside an open unit. The actual open-interior intersection with the
circle consequently contains a slightly longer arc of angular length
strictly greater than2pi/9. These occupied open arcs are disjoint for
distinct physical squares. Nine such units would have total angular
measure strictly greater than2pi, impossible. No connectedness of the
**entire** intersection is presumed in this count; one enlarged actual
arc per unit is enough.

Finally a physical boundary unit in the original window has an actual
circle corner at distance1/sqrt(2) from its center. Thus

    |c|>=R-1/sqrt(2)>79/40-17/24=19/15>3/4,

where (17/24)^2-1/2=1/576>0. This proves the full-window boundary
corollary with all physical masks and zero circle weights included.
Unlike the old radius-9/8 centered-arc theorem, this conclusion needs
neither R>=sqrt(17)/2 nor the auxiliary center threshold27/20.

## 6. A direct high-boundary contact exclusion with the new threshold

There is a further complete geometric consequence useful for actual
paths. Let A,X,E be three distinct original contained units, with
A physically touching the circle at R>=sqrt(17)/2, A physically
touching X, and

    |c_X|>=3/4,       |c_E|>=3/4.

Then E's center direction does not lie on the closed minor arc from
c_A to c_X. Moreover their minor center gap is strictly between

    2pi/9 and 4pi/9.                                    (11)

Indeed every contained center has radius less than M=91/60, by
r^2+r+1/2<=Q and the reserve31/57600 at M. The actual boundary A
satisfies |c_A|>27/20 using
sqrt(17)/2>103/50 and1/sqrt(2)<71/100. Their squared reserves are
4/625 and41/10000. The actual contact gives |c_A-c_X|<=sqrt(2).

Writing r=|c_A| and s=|c_X|, its angle omega obeys

    cos(omega)>=(r^2+s^2-2)/(2rs)>77/405.                (12)

For the last comparison the right-side fraction is increasing in r
on r>=27/20, 3/4<=s<M, since r^2-s^2+2>0. At r=27/20 it is
increasing in s, because2-(27/20)^2>0. Its endpoint value at
s=3/4 is exactly77/405; the strict boundary-center lower bound
makes (12) strict.

Also cos(4pi/9)<3/16<77/405. For the first comparison, on (0,1/2)
the cubic4z^3-3z is strictly decreasing, its value at3/16 is
-549/1024<-1/2, and cos(3*(4pi/9))=-1/2. The second comparison
has reserve17/6480. Thus omega<4pi/9. The lower bound in (11)
is the pair separation already proved.

If E's center were on that closed minor arc, its two respective
subangles to A and X would each exceed2pi/9 by the same pair theorem.
Their sum would exceed4pi/9, contradicting (11). This includes both
endpoint rays and uses no force, contact normal, mean, circle load at
X or E, or connected-intersection premise.

The earlier mixed-contact theorem remains stronger in its separate
allowance |c_E|>=2/3. The present consequence lowers X's threshold
from5/6 to3/4 while requiring3/4 for E as well. No broader substitution
is made when a caller permits an E below3/4.

## 7. Literal existing callers and the remaining pentagon capacity issue

Four current proof sources invoke the older
`BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md` directly:

- `CENTRAL_S_ROOT_THREE_BOUNDARY_PATH_CAPACITY.md`;
- `S123_POSITIVE_CHANNEL_RADIAL_MIDDLE_COMPLETE_EXCLUSION.md`;
- `S123_POSITIVE_CHANNEL_UNIQUE_MIDDLE_COMPLETE_EXCLUSION.md`;
- `S123_ZERO_CHANNEL_STRICT_MIDDLE_COMPLETE_EXCLUSION.md`.

All their actual boundary units satisfy the new theorem. In the last
three sources each consecutive boundary center gap is less than3pi/8.
Their corresponding free interval can therefore now be bounded by

    3pi/8-2pi/9=11pi/72<2pi/9,

directly, replacing the old halfwidth atan(7/20)>pi/12 comparison.
This is a strengthening of the same occupied intervals; their full
original routing, connected-extra arcs, side means and other proof
steps remain necessary and unchanged. It adds no fine count.

For the central-S-root source, every actual nonroot unit has
clearance at least1/5 and center radius at least7/10. A center radius
below3/4 must **not** be silently discarded. Its accepted
`NEAR_CENTER_UNIT_CENTERED_NINE_EIGHTHS_ARC.md` supplies the wider
halfwidth alpha=atan(2/5) whenever the center radius is at most5/6.
Consequently every nonroot unit there has a centered arc of at least
halfwidth pi/9: use the present theorem for r>=3/4 and that near-center
source for r<3/4. The strict inequality alpha>pi/9 follows from
cos(pi/9)>15/16 and sqrt(31)/15<2/5.

In that caller's low-intermediary branch, replacing the actual boundary
halfwidth beta by pi/9 makes its required residual-gap inequality
particularly short:

    atan(6)-alpha-pi/9 < pi/3-pi/9 = 2pi/9.

Indeed atan(6)-alpha=atan(28/17)<pi/3, since(28/17)^2<3.
The old stronger near-center arc and its literal clearance premise
remain. The parent capacity proof is not broadened past its stated
root and radius assumptions merely by this substitution.

For the five open inner-pentagon masks, the occupied-hub localization
puts every extra in the stated one- or two-pocket exterior union.
This new theorem supplies actual centered arcs whenever their centers
are at least3/4, and the contact consequence supplies additional
conditional path restrictions. But the existing pentagon hypotheses do
not prove that **every** completion center is at least3/4, nor do they
prove the same1/5-clearance premise for low-center extras. They also do
not by themselves bound the whole remaining exterior angular union
by enough multiples of2pi/9. The exact open pentagon IDs therefore
remain open. No independent one-per-pocket capacity is claimed.

The new theorem and contact corollary are uniform complete physical
results, with no new original gate credit. They introduce no coefficient
table or numerical certificate and do not alter the separately frozen
exact fourteen-coefficient replacement source. Adoption as a dependency
requires full root and independent review. No ledger, remote state,
Lean file, compilation, CI, or workflow is changed by this artifact.
