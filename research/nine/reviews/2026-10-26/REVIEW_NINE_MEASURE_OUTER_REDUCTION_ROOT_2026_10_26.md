# Root review: three fixed charges replace the complete outer curve

Date: October26,2026.

**Verdict: PASS for NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md
and NINE_RADIUS_TWO_MEASURE_OUTER_THREE_POINT_CHECK.py.** This is a
complete branch, convexity, exact-arithmetic and original-domain audit.
The currently accepted global208-check files remain unchanged until
the reviewed reductions are explicitly integrated. No Lean or CI ran.

## 1. Exhaustive exact angular branches

For a=sqrt(4-b^2), 1/2<=b<=sqrt(2), the actual lower x bound
a-1 is positive and the upper x bound exceeds every measure radius.
The origin and radius1/10 circle are absent. The remaining arc is
exactly the positive-x circle interval between the clipped ordinates
b-1 and b. I reconstructed all three transitions:
upper clipping is equivalent to a=(5-r^2)/2; radius1 lower clipping
is equivalent to a+b=5/2. These give the displayed b0,b1,b2.
For the larger radii there is no lower clipping, since the opposite
vertex norm squared is at most5-sqrt(15)<6/5<(11/10)^2.
The closed branch transitions and both endpoints are included.

## 2. Whole-domain monotonicity and convexity

Writing A=a-1,w=b-1,t^2=r^2-A^2,v^2=r^2-w^2, I derived

    g'=b/(a*t)-1/v,
    g''=(4*t^2-a*b^2*A)/(a^3*t^3)-w/v^3.

For the first derivative I checked the exact identity

    b^2*v^2-a^2*t^2
      =-(a-b)*((a+b-2)^2+(r^2-1)*(a+b)).

All factors compared before squaring are positive. Thus g decreases
strictly before the diagonal and has derivative zero at it.
The exact numerator identity for the second derivative is

    4*t^2-a*b^2*A=a*(2-a)^2*(a+3)+4*(r^2-1)>0.

This proves convexity directly when b<=1. When b>=1, t<=v
permits the stated lower bound with bracket
a^2*(a-b)-8*a+12. The use of a+b<=2*sqrt(2)<99/35 gives
the cubic p(a). I rebuilt its translation at a=7/4:
constant9/160, linear19/40 and quadratic bracket537/70+2*y.
For y>-7/20 that bracket exceeds6. The final quadratic's negative
discriminant has exact reserve1799/1600. Hence g is strictly convex
on the entire domain for every r>=1, with no parameter grid.

I also checked the h derivatives. Their monotonicity and convexity
hold on the stated full strip domain, including h'(1/2)=0.

## 3. Endpoint and tangent comparisons cover the continuum

On the initial interval, L2 and L3 increase. L1 increases until b0
and then decreases, so its minimum is at an interval endpoint.
The signed sine/cosine comparisons prove L1(b1)>3/4>L1(1/2).
Therefore the full initial charge is at least its b=1/2 value.
On the final interval all three terms decrease, giving the diagonal
endpoint as a global lower comparison.

On the entire middle interval, the exact expression has two convex
capped terms and one strip term. I checked the strict lower bound

    h''>4800/19683-250/2197>1/8.

The negative-term estimate is valid on both sides of b=1.
Using pi<22/7 gives M''>1/30 with the displayed positive reserve.
At the fixed point b=13/12, the exact charge and derivative bounds
give M>201/200 and |M'|<1/150. The global tangent/curvature estimate
then yields

    M(b)>201/200-|b-13/12|/150+(b-13/12)^2/60
         >=3013/3000>1.

I checked the completion of the square and the direction of the
strict inequalities. This applies through both branch endpoints by
continuity; no unproved critical root is isolated or used.

## 4. Fixed arithmetic and interval direction

I inspected the standalone checker and ran it exactly. Its derivative
enclosure checks every positive radical bound and uses sign-correct
denominator rounding in the three-term derivative sum. The resulting
raw derivative lies strictly between the two displayed rational
endpoints, both inside(-40,0). Division by2000*pi with pi>3 proves
the required absolute derivative bound.

The mass boxes enclose the exact parameters b=1/2, b=13/12 and
a=b=sqrt(2). Integer square roots round a outward; the tangent's
a bounds use opposite b endpoints, and both diagonal coordinates
enclose the same sqrt(2). Every common open rectangle is contained
in its exact reference square. The three large-circle charges alone
are included; no atom or small-circle mass is credited.

The already independently reviewed atan/asin/acos primitives are
reproduced with the same outward floor/ceiling directions. Quadrant
arc lower bounds are compared to the upper pi normalization at the
higher target201/200. Exact margins are2486115696770948576,
1716983502928824028 and336341375099883104, all positive.
No floating-point value enters the checker.

## 5. Exact replacement scope

This complete analytic branch cover replaces97 adaptive outer charge
checks by3 fixed charges and1 explicitly retained fixed derivative
enclosure. It also removes the3 old outer empty-region tests by using
the exact interval[1/2,sqrt(2)] directly.

Combined with the independently reviewed line reduction and the
unchanged corner/middle regions, it would give21 charge checks,
3 corner empty tests and the fixed derivative enclosure. Further
reductions require their own complete proofs. This is not a
certificate-free theorem. Every orientation and physical pattern
of all nine original squares remains in the global measure domain.

