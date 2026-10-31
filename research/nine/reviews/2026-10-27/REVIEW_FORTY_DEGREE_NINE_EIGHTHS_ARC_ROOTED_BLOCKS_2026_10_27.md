# Independent review: the complete forty-degree inner-arc strengthening

Date: October 27, 2026.

Reviewer: rooted_blocks, independently of the source author hexagon.

**Verdict: ACCEPTED.** I read the full source and the complete earlier
one-eighth-clearance theorem, re-derived every endpoint estimate and the
fixed-radius convexity calculation, and checked the strict threshold,
center-direction conclusion and arbitrary-orientation scope. No
correction is requested.

Reviewed source:

    FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md
    SHA-256 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517

The direct complete prerequisite is
NINE_EIGHTHS_INNER_ARC_OUTSIDE_ONE_EIGHTH.md at
f554268a5cd8edc5fb01db116e285ddc51da4ba611c000ec62f6d7c181b662b1,
independently reviewed separately in
REVIEW_NINE_EIGHTHS_ARC_ONE_EIGHTH_CLEARANCE_ROOTED_BLOCKS_2026_10_27.md.

## 1. Exact trigonometric and fixed-q estimates

For delta=2pi/9 the cubic 4x^3-3x is strictly increasing on
(1/2,1). Its evaluations correctly give
19/25<cos(delta)<4/5 and 3/5<sin(delta)<13/20. The final sine
upper-square reserve is 1/10000. The half-angle comparison uses
4(15/16)^3-3(15/16)=495/1024<1/2 and gives the asserted
strict cos(delta/2)>15/16.

For the actual ordered own frame E=[a-1,a] times [b-1,b],
a>=b>=1/2, the a>9/8 branch has the stated A,B and q bounds.
I expanded the new quantity independently:

    A^2+B^2+2sAB=(1-s)q+s(a+b)^2
                         -2(1+s)(a+b)+2(1+s).

It is convex in a+b for fixed q, so the two enlarged endpoints
b=1/2 and a=b suffice. At b=1/2 the negative cross term is
correctly bounded using s>3/5, giving the old exact endpoint bound
97/144. At a=b, containment gives v<147/100 with reserve
2(147/100)^2-Q=863/160000. The diagonal bound is therefore
72897/100000. Its difference from 29241/40000 is exactly
411/200000. Both complete endpoints are below rho^2 cos^2(delta),
so the full fixed-q inequality holds.

## 2. All four differences in the a>rho circle interval are covered

The complete actual interval is
[max(-alpha,beta),min(alpha,eta)] with the stated meanings.
The quadratic inequality gives
(A+sB)^2<c^2(rho^2-B^2), hence A<rho cos(beta+delta).
The compared angle beta+delta is strictly in (0,pi/2), so the
cosine inversion is valid even when A+sB is negative. It gives
alpha-beta>delta.

The two remaining individual lower bounds alpha>delta/2 and
eta>delta/2 follow from A/rho<122/135<15/16 and the exact
half-angle sine bound. Thus 2alpha and alpha+eta exceed delta.
The full unit-strip difference eta-beta is minimized at the centered
unit strip when b<=rho; its value there is 2asin(4/9)>delta.
For b>rho the strict >pi/3 bound remains valid. The b=rho
endpoint and the formal eta=pi/2 upper limit cause no extra component.

These are exactly the four upper-minus-lower differences, not a chosen
subarc. The a>rho open-interior intersection is one connected arc
longer than forty degrees for every actual square orientation.

## 3. The entire a<=rho branch and its weak face endpoints survive

The strict central clearance gives 0<B<=A<=1/8, a>13/12 and
b>1. I checked the complete first-quadrant interval from the direct
prerequisite. Its inner/inner difference has cosine at most
8sqrt(5)/81<19/25. Each of its two unit-strip differences is
at least asin(8/9)>delta. Its outer/outer difference lies in the
sine-monotonic interval [-pi/2,pi/2] and has exact sine strictly
greater than 59/81. The latter exceeds 13/20 by 127/1620,
so it too exceeds delta.

The radical estimate uses the actual bounds a>13/12, b>1 and
sqrt(901)<31, and includes a=rho or b=rho. No outer-face feature
is dropped. Thus all four differences cover this whole actual branch.

## 4. Center direction, capacity consequence and strict premise

The actual incircle gives |c_E|>5/8 from dist(O,E)>1/8.
Containment gives |c_E|<91/60<rho+1/2. The radius-rho point in
the actual center direction is therefore strictly inside the incircle,
and hence lies in the unique open arc already proved. The origin is
never translated to a different center.

Distinct squares' open arcs are disjoint. Once a caller establishes
actual free-gap routing, the stated at-most-n-minus-one rule follows
from the strict arc lengths, including equality in the gap-length
bound. The equality example [1/8,9/8] times [-1/2,1/2] really has
two open arcs separated by its far-side midpoint, so the source
correctly retains the strict distance premise.

This is a full force-free physical export. It assumes no graph degree,
circle mask, stress or contact-normal convention and does not claim a
graph-family closure without its required physical gap caller. No
compilation, CI, numerical pose, remote action or shared-metadata edit
was used in this independent review.

## 5. Restored prerequisite readback after the workspace reset

The forty-degree source itself was restored byte-identically at the
reviewed5c0da364 pin. Its direct one-eighth prerequisite has reconstructed
wording at4930d66aaeb88b786bd010469636f5e25684d0e266f9af90ccc0fbe694d81366,
and the older fixed-q source at4da80eec56859a863f042257d8ae391c17409e2b0e82dbee2e6b7173838fa54b.
I read both restored proofs completely. The full physical intervals,
all four comparisons, strict clearance and center-direction conclusions
are unchanged; the exact Section3 outer-face export used here remains
valid. The restored one-eighth source has a separate fresh full acceptance
in REVIEW_NINE_EIGHTHS_ARC_ONE_EIGHTH_CLEARANCE_ROOTED_BLOCKS_2026_10_27.md.
The present full forty-degree acceptance is unchanged.

