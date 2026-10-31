# Independent full review of the general endpoint tangent-sign obstruction

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Result: PASS of the complete newly written theorem, with no requested
source edit. The stated absence of an upper-radius bound is valid.**

## 1. Exact source and full scope

I read and independently rederived every section of
`FOUR_BOUNDARY_PATH_OWNED_ENDPOINT_TANGENT_SIGN_OBSTRUCTION.md`, SHA-256
`5e8cba82367da03c15710cd6060c3a009323413465a78acaf965f4b07ff29536`.
This review is of these new bytes, not an adoption of a lost earlier
draft or its review.

The hypotheses are an actual counterclockwise physical boundary path
of two through four units in radius `R>=79/40`, two original endpoint
side points at `(-X_E,h),(X_C,h)` with `X_E,X_C>0`, `h>=0` and total
abscissa at most `sqrt(2)`, outward-from-the-common-core inward axes
`(-b_E,a_E),(b_C,a_C)` with `0<a_i<b_i`, and the two stated signs of
the actual nonzero circle resultants against their own tangents.
The path-order premise is explicit and cannot be supplied by an
unproved force-polygon ordering.

There is no force or degree premise on an endpoint or internal unit.
Each original side parameter ranges over its entire closed interval.
The physical two-corner mask and either zero individual coefficient
are retained. No upper bound on R is used anywhere below.

## 2. The tangent signs locate actual centers correctly

At the right endpoint, the normal coordinate `N=b*X+a*h` is strictly
positive. Consequently every physical farthest corner is on the actual
far normal side. If the center tangent coordinate were negative, the
unique farthest tangent coordinate would also be negative; every
physical circle corner and every nonzero nonnegative combination of
them would have negative tangent component. This contradicts the
given sign. Thus the actual center tangent coordinate is nonnegative.

The full side-position formula gives strictly positive horizontal
center coordinate `X+(b-a)/2` or more, and the normal/tangent formula
gives strictly positive vertical coordinate. Therefore the actual
center angle satisfies `0<phi<=delta<pi/2`. Reflecting the left
endpoint reverses the tangent orientation, exactly converting its
nonpositive sign to the same right-endpoint argument. Neither endpoint
resultant is equated with its center.

## 3. Full physical angular bound and endpoint traversal

The actual boundary center radius is at least `R-1/sqrt(2)>5/4`.
Each true contact gives center distance at most `sqrt(2)`. The cosine
law therefore gives `cos(gamma)>9/25` for every actual minor edge
angle. Together with the actual path lift, the quadrant positions in
Section 2 force the path's total advance to be precisely
`pi+delta_E+delta_C`, rather than the shorter upper complementary arc.
At most three contacts then imply

    delta_E+delta_C < alpha=3*acos(9/25)-pi.

The triple-angle expressions for both sine and cosine are correct.
Their displayed integer comparisons give `0<alpha<pi/6`,
`cos(alpha)>89/100`, and `sin(alpha)<9/20`. With at most two contacts
there is already an immediate contradiction because the path advance
exceeds pi while two edge advances total less than pi. This endpoint
case is retained, not silently assumed away.

## 4. The complete continuous scalar estimate

For `v=delta-phi>=0`, the actual farthest corner gives

    R^2=r^2+r*(cos(v)+sin(v))+1/2.

Writing `d=sqrt(R^2-1/4)-1` and `r_0=d+1/2`, direct subtraction
gives the printed identity

    (r_0-r)*(r_0+r+1)=r*(cos(v)+sin(v)-1).

It implies `r<=r_0` and `r>=r_0-sin(v)/2` over the whole interval,
including `v=0`. The lower bound `d>9/10` follows from the exact
positive reserve `13/320` at the smallest permitted radius.

I independently expanded the key Cauchy comparison. With
`c=cos(delta), s=sin(delta)`, its right side is

    (1+c*s)*cos(phi)+s^2*sin(phi),

whose norm bound is `sqrt(1+2*c*s+s^2)`. The squared excess of
`c+(6/5)*s` is exactly

    (2/25)*s*(5*c-7*s)>=0.

The sign holds throughout `0<=delta<pi/6`; there is no orientation
sample or local expansion. Combined with the full original side
parameter, this proves `X>=g(delta)=d*cos(delta)-(3/5)*sin(delta)`.

The function g is positive, decreasing and concave on `[0,alpha]`.
For the two actual endpoint angles, concavity yields
`g(delta_E)+g(delta_C)>=g(0)+g(delta_E+delta_C)>g(0)+g(alpha)`.
The resulting strict lower bound is exactly `1431/1000`, and
`1431/1000>10/7>sqrt(2)` follows from the printed integer comparisons.
It contradicts the original endpoint-abscissa sum.

## 5. Scope and preservation

The proof is self-contained at its stated physical hypotheses. It
does not assume that a two-corner concurrence lies inside a unit,
because it uses no concurrence at all. It retains original side
points, full closed intervals and all actual physical circle masks.
Arbitrary other units and every additional endpoint/internal force
may remain. A graph caller must separately prove the two tangent
signs, common-height chart and actual minor-arc traversal.

This review changes no source bytes, original ID, flag, count, ledger,
metadata or external branch. No Lean compilation, CI, workflow,
numerical pose search or computational exclusion packet was used.

