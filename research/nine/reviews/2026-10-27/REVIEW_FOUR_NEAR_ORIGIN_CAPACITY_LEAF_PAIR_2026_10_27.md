# Independent review: four near-origin units force total capacity at most eight

Date: October 27, 2026.

**Result: PASS** for the complete physical theorem in
`FOUR_NEAR_ORIGIN_UNITS_NINE_CAPACITY_EXCLUSION.md`.

Reviewed mathematical source SHA-256:

    ebc839772dd650bf4307e6be4164b6422c6c71a17fb18ac27c207d5859e5291e

The reviewer read the entire saved source. Its center estimates,
angular cover and capacity proof are self-contained; no hidden stress
selection, private-body degree, physical boundary status or force
equation is required. This review covers the complete stated theorem,
not Lean/kernel verification or the unrelated earlier prerequisite
chain.

## 1. Actual physical centers and the complete angular cover

Each original unit's open incircle has radius one half, so distinct
actual centers have distance at least one. The true farthest-corner
formula proves the uniform strict center bound M=91/60. A square
meeting the closed disk D_(1/60) has center radius strictly less than
a=76/105; the strictness follows from the explicit rational estimate
99/140>1/sqrt(2), not from assuming the near-origin point lies in an
open disk or a square interior.

All four named centers are nonzero and have distinct directions:
otherwise their distances, at radii less than a<1, would be less
than one. The maximum-distance comparison on [0,a]^2 is valid by
separate convexity. For angular separation at most
delta=arccos(527/11552), its only possible unit-valued corner is
(a,a); the actual strictly smaller radii yield distance strictly
less than one. Therefore every pair has smaller angular separation
greater than delta.

Each consecutive cyclic gap is consequently greater than delta,
and the other three gaps bound it strictly above by 2pi-3delta.
At each central direction at least one adjacent gap is less than
pi-delta, because the other two gaps exceed delta. That adjacent
gap is itself less than pi, so its cosine is strictly greater than
-cos(delta). The subsequent distance estimate and positive rational
reserve force every central radius to exceed p=48/73. This argument
retains arbitrarily unequal central radii and gaps.

## 2. Every additional center lies in one of four small sectors

The coarse gap bound makes every direction within 3pi/8 of a
central direction. The inequality a<2cos(3pi/8) is exact, using
a^2<4/7 and sqrt(2)<10/7. Convexity in the candidate additional
radius on [0,1] gives squared distance strictly less than one at
both endpoints. Thus every further center has radius strictly
between one and M. The zero-center case is explicitly covered
before assigning it a direction.

The cosine bound for a further center and each named center uses
the correct monotonicities. The ratio is strictly increasing in
the further radius s at fixed r<1. After replacing s by M, it is
strictly decreasing in r on [p,a], since a^2<M^2-1. Replacing the
actual s<M and r>p therefore gives a strict angle exclusion
theta>alpha=arccos(33239449/38263680).

Every further direction lies strictly between a pair of consecutive
central directions and more than alpha from each endpoint. Each
remaining sector has width less than w=2pi-3delta-2alpha. If a gap
leaves no sector, it contributes no center; the proof never assumes
all four sectors are nonempty. The exact coarse angle bounds place
w in (pi/6,pi/2), where cosine is strictly decreasing.

## 3. Independent exact arithmetic and trigonometric sign check

The reviewer independently recomputed the stated fractions with
Python's exact `Fraction` arithmetic. All nineteen identity, order
and sign checks passed. In particular the computations verified:

- C=1-1/(2a^2)=527/11552;
- Q=(M^2+p^2-1)/(2Mp)=33239449/38263680;
- T=1-1/(2M^2)=6481/8281;
- the full lower-radius reserve 362639/1116292275;
- the full displayed large numerator and denominator in the squared
  trigonometric reserve, without rounding either side;
- T-M/2=24149/993720;
- both initial strict center estimates, the interval p<a<1, the
  monotonicity-domain inequality a^2<M^2-1, all angle-sign bounds,
  and each corner of the final radial-distance rectangle.

The trigonometric identity has the correct sign. With C=cos(delta)
and Q=cos(alpha), sin(3delta)=(4C^2-1)sqrt(1-C^2) is negative.
Hence

    cos(w)=(4C^3-3C)(2Q^2-1)
             +2Q(1-4C^2)sqrt((1-C^2)(1-Q^2)).

Both the radical coefficient and the radical are positive, and
T-A is positive because A<0. Thus the strictly positive exact
comparison B^2 K-(T-A)^2 can indeed be square-rooted in the stated
direction. It proves cos(w)>T over the whole geometric domain;
no decimal angle or numerical pose is used.

These finite calculations verify fixed rational identities in the
proof, not a sampled configuration or an external coefficient
certificate for a varying geometry.

## 4. Complete eight-unit count and endpoint scope

Two further centers in one sector have angular separation less than
w<pi/2 and cosine greater than T. Their squared distance is strictly
less than the separately convex function on the full rectangle
[1,M]^2. The equal-small-radius corner is less than one, the
equal-large-radius corner equals one, and both mixed corners are
strictly less than one. The actual strict cosine bound therefore
gives distance strictly less than one even at the only weak corner
of that comparison. This contradicts the actual incircle separation.

There is at most one additional center in each of at most four
sectors, hence at most four additional units besides the four
named units. A fifth near-origin unit, were it present, is already
an additional center and contradicts the radius conclusion of
Section 3; the theorem does not assume that exactly four units
meet the small disk.

All actual squares and all possible orientations enter the count.
The proof includes closed D_(1/60), all equality configurations at
the containing radius, physical contact limits, zero stress and
arbitrary force data. It changes no positive graph and requires no
circle-loaded body at all. The resulting capacity at most eight is
therefore a valid whole nine-square obstruction.

No Lean compilation, CI, remote action, central-ledger modification
or claim about a complete coarse-cell attachment cover is part of
this independent review.
