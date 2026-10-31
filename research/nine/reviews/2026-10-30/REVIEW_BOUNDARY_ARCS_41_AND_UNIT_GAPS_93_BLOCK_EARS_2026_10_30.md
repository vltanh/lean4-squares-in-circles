# Independent review of the complete 41-degree and 93-degree geometric profiles

Date: October 30, 2026 UTC.

**Verdict: PASS for the entire frozen source. No repair requested.**

## 1. Literal source and review scope

Read the whole current manuscript

`BOUNDARY_ARCS_41_AND_UNIT_GAPS_93_DEGREES_EXCLUDE_FIVE_LOAD_EIGHT_CYCLES_2026_10_30.md`

- Size: 16,429 bytes.
- SHA256: `aec4e482006c95ceadb6e3c9456c900ff6321511ea7bf61b1f7db2468c6c4c09`.
- Git blob: `ed35a105b97ed7988841259230e8a8c794f75210`.

The reviewer independently reconstructed every continuous geometric
estimate, both full closed-arc claims, all displayed polynomial and
trigonometric comparisons, and the complete cycle joins. Exact
rational arithmetic independently confirmed both quartic shifts,
their lower margins, the second-coordinate split and all displayed
trigonometric reserves.

The reviewer authored the imported base marked-cycle theorem and
previously independently reviewed the imported long/diagonal angle
source. This note does not claim independent authorship of those
inputs. Their literal hashes are unchanged:

- Base marked-cycle theorem: `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.
- Long/diagonal refinement: `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc`.

## 2. Both complete arc profiles and the exact radial tangent

The two profiles have the stated squared radii:

    (117/100)^2+(439/1000)^2=1561621/1000000,
    (103/100)^2+(9/25)^2=2381/2000.

Their reserves below (5/4)^2 are respectively 879/1000000 and 93/250.
Every physical boundary center in the full radius window is strictly
outside radius 5/4. Thus each entire arc has positive inward radial
displacement from its original square center.

Completing the actual farthest-corner equality gives

    r+(s+c)/2=sqrt(R^2-1/4+s*c/2).

At s*c=3/8 and R^2=Q, the radicand is (33/16)^2. The exact square-
root tangent inequality therefore yields

    r<=355/176+(4/33)*s*c-(s+c)/2.

This is valid across the entire own-frame interval and at its tangent
equality case.

For every theta in either full arc, the radial displacement K and
transverse displacement L satisfy 0<K<=r-A and |L|<=B. This controls
both own coordinates by F1,F2 on the whole arc. The argument does not
infer arc containment from two endpoint points.

## 3. First-coordinate quartics on the whole orientation interval

The coefficient B-s/2+(4/33)*s^2 is positive throughout both profiles:
it decreases through [0,3/4] and is at least 117/2200 at the endpoint
when B=9/25. Consequently substituting c<=1-s^2/2 in the radial bound
has the correct inequality direction and gives the displayed quartic G.

### 3.1 Boundary profile

The expansion at z=s-9/25 is exactly

    1/2-G
      =50801/17187500-(5961/2750000)*z
         +(123887/330000-(179/1100)*z+(2/33)*z^2)*z^2.

For every actual z<39/100 the coefficient of z^2 is at least
6434/20625>0, including all negative z. The negative linear term is
bounded below by its value at 39/100, leaving the positive reserve
580337/275000000. Thus F1<1/2 everywhere.

Here A+B=1609/1000>M, so F1-F2=(c-s)*(A+B-r)>=0. Both coordinates
of every point of the full boundary profile are strictly interior.

### 3.2 Unit-gap profile

The expansion at z=s-2/3 is exactly

    1/2-G
      =829/534600-(1247/356400)*z
         +(1091/4950-(35/396)*z+(2/33)*z^2)*z^2.

For z<1/12 its quadratic coefficient is at least 25309/118800>0.
The same full-interval argument leaves the strict reserve 359/285120.
This proves F1<1/2 for every orientation of the gap profile.

## 4. The gap profile's second coordinate is completely covered

For s<=1/2, the coefficient E-s/2 is positive. Replacing its factor c
by 1-s^2/2 therefore bounds F2 by the stated cubic

    U(s)=2143/4400-(31/1650)*s+(57/8800)*s^2+(17/132)*s^3.

Its second derivative is positive on [0,1/2], so its maximum occurs
at an endpoint. The exact endpoint values are below one half by
57/4400 and 163/35200 respectively. In particular
U(1/2)=17437/35200, as printed.

For s>=1/2, monotonicity of s+sqrt(1-s^2) gives s+c>34/25. If
r>=139/100=A+B, the actual farthest-corner expression would exceed

    (139/100)^2+(34/25)*(139/100)+1/2=Q+39/6400.

Hence r<A+B and F1>=F2 on this entire second interval. Its already
proved strict F1 bound controls F2. The split includes s=1/2 on both
sides and includes the diagonal endpoint s=1/sqrt(2). Thus neither
profile has an unproved second-coordinate or intermediate-arc case.

## 5. All elementary angular comparisons

The displayed positive integral proves pi<22/7; polynomial division
of its integrand matches the stated quotient and remainder.

At twenty degrees, the triple-angle cosine test values at 31/33 and
47/50 correctly lie below and above one half. The sine test at
137/400 exceeds 13/15 by exactly 5941/48000000, and 13/15 exceeds
sqrt(3)/2 by positive squaring. All monotonicity branches are specified
correctly.

With h=11/1260>pi/360, the addition formulas and elementary sine/
cosine bounds give the printed rational bounds

    C0=981141437/1047816000,
    S0=44189/126000.

Their exact reserve is

    3*C0-8*S0=1206173/349272000>0.

Hence tan(20.5 degrees)<3/8<439/1170, with the latter reserve 1/4680.
The boundary profile therefore has halfwidth strictly exceeding
20.5 degrees. Two centers at separation at most 41 degrees would
share a point of the common-radius closed interior arcs, contradicting
physical nonoverlap.

For delta=pi/120, the inequality

    67*cos(delta)+139*sin(delta)
      <29669/420<707/10<50*sqrt(2)

is valid. The middle reserve is 5/84, and the final radical comparison
uses sqrt(2)>707/500. No rounded trigonometric value is a premise.

## 6. Strict ninety-three-degree set-gap conclusion

For two center directions at +-theta/2, choose the facing gap-profile
points. Their distance is exactly

    2*|A*sin(theta/2)-B*cos(theta/2)|.

The inner expression strictly increases on 0<=theta/2<=46.5 degrees.
Its initial value is -9/25, and its final value is

    (67*cos(delta)+139*sin(delta))/(100*sqrt(2))<1/2.

Its absolute value is therefore strictly below one half throughout.
The two actual interior points have distance strictly below one,
contradicting a set gap at least one. This proves the strict greater-
than-93-degree conclusion, including theta=93 degrees and all independent
endpoint frames. It uses the true set distance, rather than substituting
an insufficient center-gap condition.

## 7. Literal compatible-cycle sum and all family consequences

The frozen base supplies actual cyclic marked-center order and one full
turn under the same compatible physical embedding. A common-normal
singleton run has endpoint set gap at least one by its unchanged
support identity. The new angle costs are therefore 41 and 93 degrees
for direct and general singleton runs; the imported diagonal and long
costs remain 105 and 175 degrees.

With d a subset of singleton count k1, the exact sum is

    41*k0+93*(k1-d)+105*d+175*ell
      =41*m+11*k1+12*d+52*ell<360.

The integer expression is thus at most 359. Every direction gap is
at least its minor endpoint angle; no force-polygon turn or origin-
containment assumption replaces the proven order.

For m=8, ell=0 follows from 328+52>359, and the remaining inequality
is 11*k1+12*d<=31. Hence k1<=2 and there are at least six marks. At
six marks k1=2 and d=0; at seven marks k1=1 and d<=1; at eight marks
k1=d=0. These are necessary counts, not existence claims.

The entire five-mark family would have three singleton and two direct
runs, whose angle sum exceeds 3*93+2*41=361 degrees. The exclusion
covers arbitrary singleton orientations and every cyclic placement.
The six-mark family with one diagonal has angle sum exceeding
4*41+93+105=362 degrees and is also excluded.

The geometric budget remains force-free once common normals are given.
Full translational balance on genuinely unloaded true-degree-two
internals supplies those normals. Calling its d=0 conclusion an
all-side classification correctly requires the same full moment
certificate. Extra marked endpoint edges and actual means remain.

The record orbit (2,0,1,0) gives 287+11+52=350 and is preserved. The
source correctly leaves the six-or-more-mark C8 rows, remaining
seven-body blocks and additional forces at circle-clear cycle vertices
beyond the new conclusion. No automatic original coarse-row credit,
Lean compilation, CI, numerical pose search, finite certificate or
remote write is claimed by this review.
