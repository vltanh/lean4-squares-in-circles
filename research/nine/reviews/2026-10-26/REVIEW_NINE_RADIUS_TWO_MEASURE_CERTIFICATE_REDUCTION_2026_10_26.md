# Independent review of the uniform nine-square radius-two measure theorem

Date: October 26, 2026.

**Verdict: PASS for the full geometric theorem and exact finite checker.**

Reviewed sources:

- NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md;
- NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py.

This was an independent reconstruction of the continuous geometry,
open-interior measure convention, integer enclosures, recursive cover and
physical scope. Merely reproducing the saved checker was not the basis
of acceptance. A second arithmetic evaluator, using a different arcsine
reduction, also checked every accepted leaf; its construction and result
are recorded in Section7 below.

No Lean compilation, CI, workflow dispatch or remote write was performed.
The proof is an exact finite certificate with analytic reductions; it is
not a table-free or Lean-checked theorem.

## 1. The measure contradiction retains all nine original units

The four normalized angular measures and the origin atom are nonnegative,
and their integer weights sum exactly to8997. Thus their common measure
has total8997/1000<9. It is essential that the lower charge is proved for
the open interior of each square: nine pairwise disjoint open interiors
are disjoint measurable sets, so their masses add without double counting.

The source handles this correctly. A straight square side meets each
positive-radius measure circle in at most two points, so changing closed
side endpoints to open endpoints has zero angular measure. The origin
atom is treated separately and is never credited when the origin lies
on a square boundary. In particular there is no illicit boundary-atom
sharing among several squares.

Rotations, reflections and interchange of the actual own axes leave the
measure invariant. They put every actual square into

    [a-1,a] x [b-1,b],  1/2<=b<=a,  a^2+b^2<=4.

The last condition is exact: in each coordinate the upper endpoint is
the one with greatest absolute value. This covers arbitrary orientations,
interior units and all physical circle-contact masks. No force graph or
equilibrium selection appears in this normalization.

## 2. Independent verification of all analytic reductions

For a<=9/10, the small circle of radius1/10 lies in the square except
for finitely many possible tangent boundary points, and the origin is
strictly interior. Its two contributions total1006/1000, as claimed.

For 9/10<=a<=11/10 and 1/2<=b<=9/10, the vertical translation
argument is valid on the whole rectangle. The origin contribution
depends only on whether a<1 and is unchanged by b, including a=1.
The entire vertical extent of the small circle is present in every
square, so its contribution is likewise unchanged. At each larger
radius and every relevant |y|<=9/10, the negative x branch is below
a-1, whereas the positive branch automatically exceeds a-1. The exact
remaining density is

    (r^2-y^2)^(-1/2) 1_{sqrt(r^2-y^2)<a}.

It is even and nondecreasing with |y|. Translating the vertical interval
from [-1/2,1/2] to [b-1,b] removes and adds equal lengths, with every
added absolute coordinate at least1/2 and every removed one at most1/2.
This proves the claimed nondecrease simultaneously for all three large
circles. No differentiability at the indicator's transition is needed.

For the middle strip 11/10<=a<=3/2, 1/2<=b<=1, the upper x bound
is inactive at radii1 and11/10. The lower bound A=a-1 belongs to
[1/10,1/2]. Since t=sqrt(r^2-A^2)>1/2, the source's exact arc formula
has the correct lower endpoint b-1 and upper endpoint min(b,t).
Its derivative changes from nonnegative to negative at t, so the
minimum occurs at b=1/2 or b=1. Both endpoint comparisons to
2asin(1/(2r)) are valid, including t=1 and r=1. The positive rational
reserves in the sine comparison and weighted two-circle charge were
independently checked:

    5/11-[47/100-(47/100)^3/6+(47/100)^5/120]
      =21887804923/13200000000000,

    3858/6000+(2424/1000)(47/100)(7/22)-1
      =189/34375.

For a>=27/20, every measure circle has x upper bound already inactive.
Increasing the comparison value a to sqrt(4-b^2) removes circle points
through its lower x bound and adds none. Both origin contributions are
zero. This establishes the required lower comparison on the full outer
domain, without moving any member of a packing. The original ordering
implies b<=sqrt(2), and the comparison point still satisfies a>=b.

These reductions exhaust the normalized domain with exactly the five
initial certificate roots. The diagonal restriction b<=a and disk
restriction a^2+b^2<=4 are retained in the two rectangles. The line
domain is split at a=1, and the outer domain retains b=sqrt(2).

## 3. Common rectangles and exact angular lower bounds

For every parameter box, the common open rectangle

    (a_h-1,a_l) x (b_h-1,b_l)

is contained in every actual open square represented by that box.
This remains true at every closed parameter endpoint. Its upper
coordinates are positive in all five domains, so the origin atom is
present exactly when a_h<1 and b_h<1. The code's Boolean is therefore
correct; it never credits the weak a_h=1 or b_h=1 case.

I reconstructed the quadrant formula directly from x=r cos(theta),
y=r sin(theta), 0<=theta<=pi/2. After clipping the coordinate/radius
ratios to [0,1], its lower endpoint is
max(acos(x_h/r),asin(y_l/r)) and its upper endpoint is
min(acos(x_l/r),asin(y_h/r)). If an entire coordinate range lies
beyond the circle, the resulting positive-part length is zero. The
four reflected quadrant rectangles cover the original rectangle;
their possible axis overlaps have zero angular measure.

The checker takes a lower bound for the upper angular endpoint and
an upper bound for the lower endpoint before applying the positive
part. Since positive part is increasing, this is a valid lower arc
bound for every point of the parameter box. Negative intermediate
acos lower enclosures near a clipped endpoint are harmless; they
can only reduce that lower arc estimate.

## 4. Independent audit of every integer primitive

All scales, coordinate endpoints, weights and subsequent arithmetic
are integers. No float enters an acceptance or empty-box decision.

The helper up(n,d) is an exact ceiling for positive d, including a
negative numerator. The square/power bounds in atan_small preserve
nonnegative interval order under multiplication. Its sixteen terms
end with a negative term. The integrated geometric-series identity
leaves a nonnegative remainder at most x^33/33, exactly the term
added to the upper enclosure. Thus both signed alternating sums
are rounded outward correctly.

The floor/ceiling inputs to atan_base_fraction bracket its exact
rational argument. Machin's identity has the correct signs in the
pi interval:16 times the lower atan(1/5) bound minus4 times the
upper atan(1/239) bound is a lower pi bound, and conversely for
the upper bound. The tangent computation and its (0,pi/2) branch
justify the identity independently of the numerical enclosure.

For atan_fixed above1/2, the transformed argument (1-x)/(1+x)
lies in [0,1/3), so the small-argument routine applies. Subtracting
its upper bound from a lower pi/4 bound and its lower bound from
an upper pi/4 bound has the correct direction.

For asin_fraction, the rounded square of the upper argument yields
a lower bound for 1-t^2; the rounded square of the lower argument
yields an upper bound. Taking isqrt for the former and isqrt+1
for the latter gives the stated outward square-root bounds. The
half-angle quotient t/(1+sqrt(1-t^2)) uses the upper denominator
for its lower bound and the lower denominator for its upper bound.
Clamping the latter to1 is safe because the true quotient is at
most1. Monotonicity and the identity asin(t)=2atan(quotient) then
give both angle bounds. The t=0 and t=1 cases are explicit and
correct. The acos routine again subtracts interval bounds in the
proper reversed order.

For an accepted box the integer test is

    sum_r(weight_r L_r)>=(1000-292 I) 2 PI_HI.

Dividing by1000*2*pi*Q and using PI_HI/Q>=pi proves that the
circle contributions are at least1-292 I/1000. Adding exactly
the origin atom proves mass>=1. Using the upper pi bound here
is the conservative and correct normalization.

## 5. The finite cover is exhaustive, including all weak endpoints

All five root coordinates are represented exactly at the chosen
denominator B. Every rectangular split produces two closed children
whose union is their parent, even when an integer midpoint is not
the real midpoint. The outer branch splits only its b interval,
and recomputes an outward enclosure of sqrt(4-b^2) on each child.

The strict tests b_l>a_h and a_l^2+b_l^2>4 discard only rectangles
with no admissible point. The strict outer test b_l^2>2 discards
only intervals wholly beyond sqrt(2). Equality is retained in every
test. A straddling outer interval is safe: its upper b endpoint is
at most3/2, so both square roots remain real, and its enlarged a
interval encloses the valid subcurve. It need not itself consist
entirely of ordered admissible squares to furnish a lower charge.

The nonprogressing-split assertion would reject a failed refinement;
it is not a path that silently accepts an unresolved leaf. The saved
run terminates with every retained leaf charged and every other leaf
proved empty. The leaf-count identity is a consistency check; actual
coverage follows from the recursive closed-child construction.

## 6. Reproduced exact result

Running the saved source with standard Python reproduced all values
in the manuscript:

| Domain | Charged leaves | Empty leaves | Splits |
| --- | ---: | ---: | ---: |
| Both line roots |95|0|93|
| Corner rectangle |14|3|16|
| Middle rectangle |2|0|1|
| Outer curve |97|3|99|
| Total |208|6|209|

Maximum depth is12. The minimum accepted integer charge margin is
4023192202688832>0. The pi numerators are
226375608064909912 and226375608064910268 over2^56. The ordered
leaf digest is

    d86a26a628643d32387e0ba9800dcfc1830335f7828d0335bcd9c2172767b0c5

The digest is only a reproducibility marker. The accepted proof rests
on the interval and coverage arguments above.

## 7. Separate arithmetic reconstruction

As an additional independent audit, I implemented a second evaluator,
saved as NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py. It imports
neither the original verifier nor any of its arithmetic or rectangle-charge
routines. It uses scale2^80,
40-term exact rational Machin bounds, and the distinct reduction

    asin(t)=4atan(q/(1+sqrt(1+q^2))),
    q=t/(1+sqrt(1-t^2)).

The final atan argument is at most sqrt(2)-1<1/2. A32-term
alternating expansion with its next positive remainder then supplies
outward intervals. Exact rational-radicand square-root enclosures
were used in both half-angle steps. The independent40-term rational
pi interval lies strictly inside the author's saved pi interval.

The helper's423-symbol explicit forest is an alternative encoding of
the same208 charged leaves,6 empty leaves and209 splits. It independently
checks every split and every strict empty-domain condition, consumes
the complete forest with no omitted or unused branch, and reconstructs
the same ordered leaf digest. This imports no acceptance decision from
the original checker. I independently recomputed the lower charge of
every accepted common rectangle with this second evaluator.
All208 charged leaves again had strictly
positive margins. At scale2^80=1208925819614629174706176, the
smallest independent integer margin was

    67497964636653435442356 > 0.

The empty/split count was again6/209. This check is additional
arithmetic corroboration; the mathematical audit of the original
checker in Sections3--5 already justifies its acceptance semantics.
The saved independent checker audits the same single measure witness
and exact same finite cover. It does not create an additional set of
certificate obligations or a second measure packet.

## 8. Accepted scope and the exact remaining all-unique C6 join

The uniform geometric conclusion is accepted:

    every packing of nine unit squares has containing radius R>2.

It applies to all nine unchanged squares, with arbitrary orientations
and any contact or circle-weight pattern. It does not use an n=8
bound, a force graph or a choice of original means.

Section8 of the already independently accepted
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md proves R<2 on
the entire remaining all-unique chi=(1,1,0) outgoing-share0 C6
orbit. It uses the actual full channel equations only through their
true closure and virial consequences, preserves the actual mean
parameter and every transmitter slider, and has no coordinate-box
or completion-allocation premise. Its original physical scope
retains all nine units and all three extras.

Therefore an actual nine-unit realization of that orbit would have
R<2 and would, in particular, consist of nine interior-disjoint units
inside the same radius-two disk. The accepted measure theorem
contradicts this. This is a complete whole-orbit completion exclusion,
including every previously retained allocation at once. It does not
need the new pocket-2 capacity-one theorem or the final central/cap
coupling argument. No extra unit is removed to apply the measure.

The exact new arithmetic cost is208 whole-domain charge checks and
6 exact empty-domain tests after the analytic reductions. The earlier
four coefficient packets remain replaced analytically; this new
uniform geometric certificate is separate and should be counted
explicitly. Neither a certificate-free repository nor a Lean theorem
has been proved here. The stronger target R^2>=1105/256, its equality
classification, other physical graph/mask families and the complete
formalization remain separate obligations.
