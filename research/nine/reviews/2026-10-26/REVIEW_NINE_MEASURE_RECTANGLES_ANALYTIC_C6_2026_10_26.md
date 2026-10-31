# Independent review: analytic charges on the complete corner and middle domains

Date: October 26, 2026.

Reviewer: C6 completion agent, independent of the source and helper author.

**Verdict: PASS.** I read the entire source
`NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md`, checked
its join to the original normalized domain cover, and independently
reconstructed all face-order arguments, measure comparisons, atom
boundaries and rational mass reserves. The source proves strictly
more than unit mass throughout both stated domains. It replaces all
14 corner and two middle charge leaves and all three corner empty
tests. It adds no interval charge certificate.

## 1. Exhaustive domain and origin-atom audit

The two domains in (3), with the actual order \(b\le a\), are precisely
the physical portions of the corresponding residual rectangles in
Section 3.5 of `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md`. Their
inequalities can be used directly; no empty portions need to be
subdivided and discarded.

The four corner cases are exhaustive, including the overlaps at
\(a=1\), \(b=1\), and \(a=21/20\). The two middle cases retain
\(b=6/5\) and use \(b\le a\) where the common square requires it.
Each displayed open common rectangle is genuinely contained in every
actual open square of its stated case. Equality at one of the actual
faces does not invalidate an open-rectangle inclusion.

The only credited origin atom occurs when \(a<1\) and \(b\le a<1\),
so both actual lower coordinates are strictly negative and the origin
is strictly interior. It is credited to the actual square separately
from its common positive-quadrant rectangle. No limiting atom is
used at \(a=1\) or \(b=1\). All other cases ignore the atom entirely.
Edges on the circle measures carry no angular mass, as required.

## 2. Complete corner-region geometry

For the first three cases I checked each circle's positive angular
interval directly from the common rectangle. In particular:

- The small-circle contributions are a quarter circle in (7) and
  exactly a sixth circle in (11).
- The radius-1 and radius-11/10 upper-face intersections give exactly
  the stated arc lengths; every lower face claimed inactive is so.
- The negative inverse-sine term in (10) uses \(\pi>3\) in the
  correct direction, while its positive term uses \(\pi<22/7\).

I checked Section 2.4 separately, because it compares the complete
large-circle mass rather than using one common rectangle.

For radius one, the lower x face permits exactly (14). The function
increases before \(b=t\) and decreases afterward, so its minimum
is one of its two endpoint values. The comparison
\(\cos(2\arcsin(1/10))=49/50>9/10\) proves that the \(b=9/10\)
endpoint is the smaller one. The relevant angles lie in the stated
monotonicity interval; no reversed inverse-function inequality occurs.

For each larger circle, the lower x face is inactive on the complete
vertical interval \([-1/10,1]\). The density (15) is exactly the
positive-x branch's angular density, including the upper-x indicator.
It is even and nondecreasing in absolute height. Translating
\([b-1,b]\) upward for \(9/10\le b\le1\) removes heights with
absolute value at most \(1/10\) and adds heights at least \(9/10\).
Thus the integral cannot decrease. This argument includes the
negative-y branch when the upper x face admits it; none is silently
dropped. At fixed \(b=9/10\), increasing a merely opens the upper
x face, since the lower face remains inactive on all three circles.
This proves the full comparison (13).

At the comparison square \((21/20,9/10)\), I checked every arc in
(16). The two larger circles have no negative-y intersection because
their upper-x threshold exceeds \(1/10\). Their positive arcs have
the stated endpoint order. The radius-one arc includes its actual
negative-y contribution. Therefore the lower bound (17) applies
throughout the entire fourth corner case.

## 3. Complete middle-region geometry and signs

Both common rectangles are correctly included. I independently
checked the face-order comparisons in (19): the radius-11/10 upper
y face precedes the lower x face, and the radius-27/20 lower faces
are inactive while its two upper faces leave a positive arc.

For the second common square, both smaller circles have inactive
upper faces. The radius-27/20 lower faces are inactive because
\(625/729<1\), and its two upper faces leave a positive arc.
This verifies every formula in (22).

The combined non-pi numerator in the first middle case is positive,
so its division by \(2\pi\) is bounded below with \(7/44\).
In the second case it is negative, so the correct lower bound uses
\(\pi>3\). I checked both signs before applying those bounds.

## 4. Exact arithmetic audit

The signed Taylor bounds in (5) are valid throughout the entire
displayed interval: the alternating terms decrease, and all test
angles lie below \(\pi/2\). I independently rebuilt all nine lower
and all five upper inverse-sine comparisons using fresh rational
arithmetic. Each reserve is strictly positive and agrees with the
displayed value.

I then reconstructed the six mass bounds directly from the arc
formulas and their inverse-sine inequalities, without importing the
helper's expression list. Their reserves above one are exactly:

| Whole region | Exact reserve |
| --- | ---: |
| Corner, actual atom interior | \(11613/2200000\) |
| Corner, both lower coordinates nonnegative | \(5761/90000\) |
| Corner, \(1\le a\le21/20\), \(b\le1\) | \(14681/4400000\) |
| Corner, \(21/20\le a\le11/10\), \(b\le1\) | \(2423/550000\) |
| Middle, \(1\le b\le6/5\) | \(19681/550000\) |
| Middle, \(6/5\le b\le a\) | \(2897/75000\) |

I also read and successfully executed
`NINE_RADIUS_TWO_MEASURE_RECTANGLES_RATIONAL_IDENTITIES.py`.
It reproduces these displayed rational identities and face-order
comparisons; it does not compute a new measure interval or perform
a parameter search. The whole-region arguments above supply the
coverage.

## 5. Scope and integration consequence

Both residual physical parameter domains have open-interior mass
strictly greater than one. Together with the separately reviewed
line and outer-curve reductions, the same global nine-square measure
theorem requires only five fixed mass evaluations: two line and three
outer values. The one fixed outer derivative enclosure is retained.
There are no empty-domain tests or adaptive parameter subdivisions
in that integrated reduction.

The five fixed mass evaluations were already independently checked
at \(2^{80}\) in this reviewer's separate line and outer reviews.
Thus this source removes the final 16 whole-box charges, for a total
reduction of 203 from the original 208 charge checks. The theorem
still retains its explicitly stated fixed numerical certificate.

The measure, all original orientations, all nine physical squares
and every contact/circle-weight pattern remain unchanged. This
scalar improvement does not by itself tick any new graph gate.
No Lean compilation or CI was run.
