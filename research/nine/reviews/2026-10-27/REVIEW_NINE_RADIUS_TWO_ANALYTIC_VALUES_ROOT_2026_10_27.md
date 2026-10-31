# Integration-owner full review of the radius-two analytic fixed values

Date: October 27, 2026.
Reviewer: root, independently of the manuscript's author.
Current comparison: PR11 at
`50c0cd616eb494ade100f055ad518cdbd33c7275`.

## 1. Verdict and exact source scope

**PASS for the complete analytic replacement and same-nine-square
join.** I read the entire new source, all five current original
analytic/global sources below, and reconstructed the exact arithmetic
from the written tables. The proof does not rely on a successful run
of an old inverse-angle checker or on its stored margins.

New source:
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`.
SHA-256:
`9a4656cc90ab81200847c8b6958fc6e089fc4b807b401705663304be4f782c4b`.

| Complete current source read | Git blob at the comparison head |
| --- | --- |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | 453091c80f23e0e1630f3351f139c7f50418c03d |
| NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md | ecf79060dee88a377a248f27fdb182cd10c11f12 |
| NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md | 278924e9cde3087e52b67bdad6ccdb2cfd53c917 |
| NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md | eb92e320d141bc00dd1aa2d30d9759e7e3c43a3e |
| NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md | 30e2cd8f1a576bc60d608acef8f2c24fc9504cd0 |

The second independent final-source review is recorded separately
before integration. No ledger or remote file was changed for this
review.

## 2. The exact targets and complete original domain

The same radial nonnegative measure has total mass 8997/1000, with
weights 292,714,3858,2424,1709 over 1000 on the origin and the four
stated circles. The original actual-square normalization is exactly
1/2<=b<=a and a^2+b^2<=4. It makes no force, contact or boundary-mask
assumption.

The left line submeasure has one minimum a0 in (927/1000,928/1000),
as proved by the strictly increasing derivative-sign polynomial H.
The right line measure has its exact minimum 324943/298110, as
proved by the increasing linear derivative-sign expression J.
I checked the positive squaring, endpoint signs and exact rational
critical-point identity in the current source. The actual atom is
present only in the left interval a<1. Its scalar extension to a=1
does not supply an atom to the actual endpoint; the closed right
interval handles that square without an atom.

The complete outer circle-face cover in the current source has the
three exact transitions b0,b1,b2 and the stated capped/strip
formulas. I read its derivations, monotonicity and whole-interval
convexity proof. The initial range is bounded by M(1/2), the final
range by M(sqrt(2)), and the middle has M''>1/30. Its tangent
b*=13/12 is strictly inside that middle interval. The replacement
therefore needs precisely the five mass targets and one derivative
target stated in its Section 1, without an additional sampled
minimum or a parameter-box hypothesis.

## 3. Shared Taylor and pi arguments

All Taylor arguments are in [0,13/10]. The alternating series terms
decrease from their first term onward, so C10<=cos<=C8 and
S11<=sin<=S9 hold with the stated signs on the whole interval.
Every fixed comparison lies in the strictly monotone principal
inverse-angle branch. A row that bounds cosine from above supplies
an upper acos bound; a row that bounds sine from above supplies
a lower asin bound. The other row types correctly reverse those
inverse inequalities.

The lower pi bound follows from the exact current Machin identity
and the signed four-term atan lower sum, subtracting the simple
upper bound 1/239 for the other atan. Its exact excess above
314159/100000 is 21011/12547500000. The upper pi bound follows
from the positive integral in the source. Direct division has
quotient x^6-4x^5+5x^4-4x^2+4 and remainder -4, so its integral
is exactly 22/7-pi.

The uniform small-angle bound is also correctly oriented. Squaring
the positive derivative comparison gives
t(5-21t-9t^2)/25>0 for 0<t<=1/144. Integration from zero proves
asin(x)<=x+x^3/5, and x^2/5<=1/720<1/500 gives the strict linear
upper bound. This is one whole-interval result for all three
subtracted tangent angles.

## 4. Five direct mass reserves

At the left minimum, 10(a0-1)<-18/25 and a0>927/1000 give the two
inverse-angle comparisons in the source. Their constant terms sum
to 1649/1000. The subtracted weighted numerator is positive, so
the lower pi bound gives the conservative lower mass estimate.

At the right minimum the two exact rational angle arguments are
26833/29811 and 324943/327921. The three written Taylor comparisons
bound its positive weighted numerator from below. The upper pi
bound is the conservative denominator in this case.

For outer b=1/2, the exact intervals are twice the stated acos or
asin terms, and the normalizing denominator consequently becomes
1000 pi. For b=13/12, the current capped/capped/strip branches
give exactly the three differences displayed in the replacement.
The radical upper bound for a and the uniform small-angle estimate
give their correct lower differences, all positive. For the
diagonal a=b=sqrt(2), each original interval has length
pi/2-2 asin((sqrt(2)-1)/r), giving the constant 7991/4000.
Its subtracted numerator requires the lower pi bound.

I reconstructed all thirteen rows of the written Taylor table
with exact Fraction arithmetic, using the displayed polynomials
and rational x,y, and verified each claimed integer lower reserve
for 10^9 times its difference. I also independently checked all
three positive-square radical upper reserves and the five complete
mass sums. The exact resulting reserves are:

| Actual target | Exact positive reserve |
| --- | --- |
| Left line minimum above 1 | 785291/314159000 |
| Right line minimum above 1 | 575589/110000000 |
| Outer b=1/2 above 201/200 | 539069/110000000 |
| Outer b=13/12 above 201/200 | 207622367/65340000000 |
| Actual diagonal above 201/200 | 847269/1256636000 |

These arguments evaluate the exact minima/points analytically. They
do not replace equal diagonal coordinates by independent rounded
parameters or use a stored common-rectangle charge.

## 5. Full derivative target and continuous outer join

Every radical in the derivative table is positive. I reconstructed
the radicands and checked all fourteen squared endpoint reserves.
For t1,t2 the lower radicand uses the upper a bound and the upper
radicand uses the lower a bound, as required by their common actual
dependence on a. No independently adjustable radicals are assumed.

For each G term, the lower positive quotient uses upper positive
denominators and its subtracted reciprocal uses the lower v bound;
the upper endpoint reverses those choices. For H the two reciprocal
choices likewise have the stated directions. All six endpoint
fractions and all six positive rational endpoint reserves in the
written table agree exactly with an independent reconstruction.

Multiplication by the unchanged positive weights gives

    -19917/500 < T < -1629/200 < 0,
    M'(13/12)=T/(2000 pi).

The lower endpoint exceeds -40 by 83/500. Thus pi>3 proves
the required strict absolute derivative bound 1/150. This is the
same derivative of the actual original middle branch.

Combining it with M(b*)>201/200 and the original M''>1/30 gives
the stated quadratic lower bound on both sides of b*. Completing
its square gives the exact lower value 3013/3000. Both outer
branch endpoints and all clipping transitions remain included by
the actual open-circle continuity. None involves an origin atom.

## 6. Complete two-dimensional and nine-unit assembly

I checked the six-region cover against the current global and
rectangle sources. The original even-density translation really
compares the values of one measure and preserves the origin
contribution, including a=1. The outward comparison is monotone
because every circle's upper x face is already inactive. Neither
comparison moves a packing unit.

The four corner cases and two middle cases are unchanged and
cover their full necessary order b<=a. Their atom-free boundary
rules, open-rectangle inclusions and signed analytic reserves remain
as stated. In particular no origin atom is assigned to a square
just because its parameters are a limit of atom-containing squares.
The direct small-square and two-circle-strip arguments cover the
other two original regions. The split at a=9/10, a=11/10,
a=27/20, b=9/10 and b=1 is exhaustive and includes its boundaries.

Thus every actual unit inside D2 has open-interior mass at least one.
The nine actual open interiors are disjoint, so additivity contradicts
total mass 8997/1000. This proves R>2 for the same nine squares,
with no condition on orientation, force graph or physical contacts.
It is not an assertion about an isolated smaller core.

## 7. Dependency accounting and limitations

After independent final acceptance and source integration, the
five whole-box inverse-angle mass-checker dependencies and the
fixed derivative-checker dependency are replaced by the displayed
analytic proof. The historical 208-charge and five-charge checkers
remain valid alternative proofs and are not additional current
requirements.

Finite arithmetic remains: thirteen new written Taylor comparisons,
the seven radical intervals and derivative fractions, the five
rational sums, and the already accepted fourteen rectangle Taylor
comparisons and other analytic comparisons. This review does not
rename those facts as absent arithmetic. It establishes that no
high-precision inverse-angle evaluator or stored charge margin is
needed by this current proof route.

The exact arithmetic used during this review verifies the identities
printed in the proof; execution of that audit is not a proof premise.
No adaptive pose cover, sample, numerical root isolation, new graph
gate, force deletion, altered contact mean, Lean compilation, CI,
workflow or remote mutation was used. The sharp unrestricted
1105/256 theorem, original equality classification and older global
canonicalization/prerequisite obligations remain open.
