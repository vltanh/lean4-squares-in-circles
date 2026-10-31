# Independent review: the complete nine-eighths inner-arc theorem

Reviewer: hexagon. Date: 2026-10-27.

**Disposition: ACCEPTED in full.** This review was reconstructed after the
workspace reset, following a complete fresh read of the restored proof.
The accepted restored source is
`NINE_EIGHTHS_INNER_ARC_AWAY_FROM_CENTRAL_DISK.md`, SHA-256
`4da80eec56859a863f042257d8ae391c17409e2b0e82dbee2e6b7173838fa54b`.
It has the same mathematical statement and argument as the earlier accepted
source `fcf347b2a0abfb740d35fd58d8227fbc8954caab3f2a77ef1b7bf980096901ce`.
The new pin is necessary because its prose was reconstructed, rather than
recovered byte for byte.

## Whole-domain geometric check

The only physical assumptions are an actual closed unit square inside the
original disk of squared radius1105/256 and strict origin clearance greater
than sqrt(2)/8. Reordering and changing signs of its actual own axes is
legitimate and does not translate the origin. The resulting far coordinates
a>=b>=1/2 have a^2+b^2<=Q. The distance formula excludes a<=9/8 including
the equality case, hence A=a-1>1/8. The upper bounds A<61/60 and B<1/2
follow from actual far-corner containment; both strict comparisons have
the displayed rational reserves.

Since A>0, every circle point in the square is in the same right-half-plane
angular chart. The complete interval is exactly
[max(-alpha,beta),min(alpha,eta)]. The upper outer x face is inactive because
a>rho. When b>=rho the formal eta=pi/2 endpoint is already excluded by
alpha<pi/2, so neither an isolated endpoint nor a second arc is lost.

## Exact estimate and all four differences

I re-expanded the fixed-q expression as
(2/5)q+(3/5)t^2-(16/5)t+16/5. Convexity in t on the enlarged fixed-q
interval is valid even if its diagonal endpoint lies outside a>rho.
At b=1/2, the allowed A0 interval is strictly between1/8 and61/60;
the two quadratic values are61/320 and97/144. At a=b=v, the actual q
bounds give3/4<v<3/2, hence(16/5)(v-1)^2<4/5. Thus the entire domain
has E0<4/5<81/100, with no sampled orientation.

The square-root step remains valid when A+(3/5)B is negative. The angular
range0<beta+gamma<pi/2 is justified independently, so inversion of cosine
gives alpha-beta>gamma. The two half-angle inequalities give2alpha>gamma
and alpha+eta>gamma. The full unit-strip derivative has the claimed sign
for b>=1/2, includes b=rho by continuity, and the b>rho part is separately
strict. These are precisely all four upper-minus-lower differences in the
actual interval. Their minimum is strictly greater than gamma, proving
the entire connected open arc statement, not just a subarc.

## Center direction and exact export

The actual radius1/2 incircle gives |c|>1/2+sqrt(2)/8. The actual farthest
corner gives |c|^2+|c|+1/2<=Q; the displayed91/60 comparison is strict.
Therefore the radius-rho point in the actual center direction lies strictly
inside the incircle and hence on the one complete open arc. Distinct square
interiors give disjoint arcs. The capacity export correctly requires the
caller to establish actual occupied closed arcs and complete free-gap
routing; it does not infer these from center angles alone. Strict arc
lengths correctly retain equality in a gap of length n*gamma.

No force, degree, boundary-mask, contact-point or normal assumption has
been introduced. No numerical test or formal compilation is being counted
as proof. No mathematical correction is requested.
