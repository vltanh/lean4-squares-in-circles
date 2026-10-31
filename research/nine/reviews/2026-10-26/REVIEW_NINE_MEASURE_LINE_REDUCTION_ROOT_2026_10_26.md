# Root review: two fixed charges replace the entire inner-line subdivision

Date: October26,2026.

**Verdict: PASS for NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md
and NINE_RADIUS_TWO_MEASURE_LINE_TWO_POINT_CHECK.py.** This is a full
analytic-domain and exact-arithmetic review. It does not change the
accepted global checker automatically; integration and its exact
remaining-cover accounting are separate. No Lean or CI was run.

## 1. Exact circle charges and the origin boundary

I reconstructed the charge for S(a)=[a-1,a]x[-1/2,1/2].
The radius1/10 circle is entirely within the horizontal band, and
its upper x bound is inactive, giving acos(10(a-1))/pi.
For r>=1, the negative circle branch has x<=-sqrt(3)/2 and
is outside the square. The positive branch exceeds the lower bound,
so its charge is [asin(1/(2r))-acos(min(a/r,1))]_+/pi.
The radius27/20 term vanishes throughout9/10<=a<=11/10.

The origin is strictly interior exactly for a<1. Tangency points
of the circle measures have measure zero; the origin atom does not.
The left scalar's continuous extension at a=1 is used only to locate
its minimum; the actual a=1 square is included in the atom-free right
branch. Thus no atom is accidentally credited to a boundary square.

## 2. The complete left and right minima

On9/10<a<1, deleting only the nonnegative radius11/10 term leaves
the stated scalar L. Its derivative has exactly the sign of

    H(a)=3858^2*(a-9/10)*(11/10-a)-714^2*(1-a^2).

Both terms before positive squaring are positive. Direct differentiation
gives H'(a)=2*(3858^2-(3858^2-714^2)*a)>=2*714^2>0.
The endpoint signs are opposite, so L has one global minimum.
I verified the two rational signs at927/1000 and928/1000 and their
exact values from the source. Its unique minimum lies strictly inside
that one fixed enclosure.

On1<=a<=11/10, the radius1 term is constant, the radius11/10
term is active, and the atom is absent. Differentiation has exactly
the sign of

    J(a)=2424^2*(a-9/10)-714^2*(a+11/10).

It is strictly increasing and has the exact rational zero
324943/298110, strictly between the endpoints. Consequently this
point is the global minimum of the continuous closed right branch.
This derivative proof covers the entire domain; no sampling or
critical-root assumption is used.

## 3. The exact common-rectangle checks

The coordinate scale is B=83886080 and angular scale is2^56.
The left box is the outward enclosure of[927/1000,928/1000];
the right box is the outward enclosure of the exact rational minimum.
Both b coordinates are1/2. The open rectangle
(a_high-1,a_low)x(-1/2,1/2) is contained in every square of its
box. The first origin atom is strictly interior; the second is absent.
The first check includes only the radius1/10 and1 terms, exactly
as required for L, and does not recover the discarded11/10 charge.

I inspected the standalone checker. Its integer atan/asin/acos and
pi primitives reproduce the already independently reviewed outward
rounding, with floor/ceiling directions preserved. Its quadrant
intersection bounds take a lower upper endpoint and an upper lower
endpoint, then the positive part; therefore each is a lower bound
for the entire common rectangle's arc, not a representative square.
The mass comparison uses the upper pi enclosure in the denominator.

The standalone exact run passed. It verifies the derivative endpoint
signs, rational critical point identity, both origin statuses and the
two strict integer margins1153182092959159440 and2475502032000671400.
No floating-point arithmetic enters either bound.

## 4. Replacement scope

The accepted vertical-translation theorem extends this complete line
bound to exactly the original lower-b rectangle domain. Hence these
two fixed charged rectangles may replace all95 adaptive line leaves,
retiring93 current charge obligations. The corner, middle and outer
regions keep their original obligations until separately reduced.

With those unchanged regions, the complete measure proof would use
115 charge checks and the same6 empty-domain tests. This source is
not by itself a replacement for the complete global checker or a
certificate-free global proof. Its fixed enclosures are explicitly
counted. All nine physical units and every orientation/contact pattern
remain in the global theorem's original scope.

