# The global radius-two measure proof reduces to five fixed charges

Date: October 26, 2026.

**Current dependency update, October 27:**
NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md now proves all five
actual mass targets and the derivative target directly. Its full root
and separate independent reviews are joined in
ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md. The complete geometry
and continuous-domain assembly below are unchanged. Its fixed values
now use that analytic source; the five common-rectangle enclosures,
checker entry points and counts below record the accepted October 26
stage and remain historical alternatives. Explicit finite Taylor,
radical and rational arithmetic remains in the current proof.

**Status: accepted complete assembly and standalone integrated checkers**
after full reviews in REVIEW_NINE_MEASURE_FIVE_POINT_ASSEMBLY_ROOT_2026_10_26.md
and REVIEW_NINE_MEASURE_FIVE_POINT_ASSEMBLY_C6_2026_10_26.md.
All three analytic replacements have root and separate C6 full-source
reviews. Both integrated exact entry points pass on the same five
fixed mass obligations. The original208-charge checker and its
independent alternative remain unchanged as historical proofs.

The integrated exact entry point is
NINE_RADIUS_TWO_MEASURE_FIVE_CHARGE_CHECK.py. The separate
NINE_RADIUS_TWO_MEASURE_FIVE_CHARGE_INDEPENDENT_CHECK.py independently
evaluates exactly the same five fixed mass charges with a different
inverse-trigonometric construction and higher integer precision.
Neither imports the old verifier or any other repository file.

## 1. Unchanged geometric theorem and measure

For every unit square \(S\) contained in the closed disk \(D_2\), prove
\(\mu(\operatorname{int}S)\ge1\), where
\[
 \mu=\frac1{1000}\left(
 292\delta_0+714\lambda_{1/10}+3858\lambda_1
       +2424\lambda_{11/10}+1709\lambda_{27/20}\right).
\tag{1}
\]
Here \(\lambda_r\) is normalized angular measure on the circle of
radius \(r\) about the original disk center. This same nonnegative
measure has total mass \(8997/1000<9\). For nine squares with disjoint
open interiors, additivity would give total mass at least nine,
a contradiction. Thus their containing radius is strictly greater
than two.

The normalization from Section 2 of
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md is unchanged. Rotation,
reflection and interchange of actual own axes yield exactly
\[
 S(a,b)=[a-1,a]\times[b-1,b],\qquad
                 1/2\le b\le a,\quad a^2+b^2\le4.
\tag{2}
\]
The farthest vertex is \((a,b)\), so the last condition is precisely
disk containment. The radial measure is invariant under all those
coordinate choices. No assumed contact, force, circle mask or
individual circle weight enters this normalization or the argument.

## 2. Complete continuous coverage

The following table assigns every actual normalized square a proved
whole-domain charge bound. At shared boundaries either adjacent
proof applies; no origin atom is obtained merely by continuity.

| Actual parameter region | Continuous proof and current obligations |
| --- | --- |
| \(a\le9/10\) | Original Section 3.1: the actual interior contains the origin and the small circle up to finitely many tangent points, giving \((292+714)/1000>1\). |
| \(9/10\le a\le11/10,\ b\le9/10\) | Original Section 3.2: the even angular-density translation reduces the whole region to \(b=1/2\). The line analytic reduction proves that entire line from two fixed charge enclosures, with \(a=1\) handled on the atom-free side. |
| \(9/10\le b\le a\le11/10\) | The rectangle analytic reduction, Section 2: four direct analytic cases cover the entire corner triangle, including all atom boundaries. No interval charge remains. |
| \(11/10\le a\le27/20,\ b\le1\) | Original Section 3.3, whose proved domain extends to \(a\le3/2\): the two-circle lower bound exceeds one by \(189/34375\). |
| \(11/10\le a\le27/20,\ 1\le b\le a\) | The rectangle analytic reduction, Section 3: two direct common-rectangle bounds give reserves \(19681/550000\) and \(2897/75000\). No interval charge remains. |
| \(a\ge27/20\) | Original Section 3.4: increasing the comparison parameter to \(a_*=\sqrt{4-b^2}\) cannot increase any circle charge. The whole resulting curve \(1/2\le b\le\sqrt2\) is proved by the outer analytic reduction, using three fixed charges and one fixed derivative enclosure. |

For explicit exhaustiveness, first use the first or last row when
\(a\le9/10\) or \(a\ge27/20\). In the remaining interval, if
\(a\le11/10\), split at \(b=9/10\); if \(a\ge11/10\), split at
\(b=1\). These are exactly the other four rows.

The original vertical translation and outer comparison compare values
of the single measure; they do not move any packing square. The
outer endpoint still has \(b\le\sqrt2\) by \(b\le a\) and disk
containment. Both comparisons retain closed endpoint parameters and
the actual open-interior convention.

## 3. The three analytic replacement sources

The exact current replacements are:

- NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md.
  Exact derivative signs reduce the two sides of the line to two
  fixed critical enclosures. The first is charged with its actual
  interior origin atom, the second without an atom. This replaces
  the former 95 line leaves by two fixed charges.

- NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md.
  A complete circle-face branch cover, uniform convexity of every
  capped circle arc, and one strong-convexity tangent bound reduce
  the entire boundary curve to \(b=1/2\), \(b=13/12\) and
  \(a=b=\sqrt2\). Each fixed charge exceeds \(201/200\).
  A single rational derivative enclosure at \(b=13/12\), together
  with \(M''>1/30\), proves the intervening interval exceeds
  \(3013/3000\). The initial and final ranges reduce to the endpoint
  charges. This replaces 97 charged and three empty leaves by
  three fixed charges and one fixed derivative enclosure.

- NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md.
  Six whole-region inclusions or monotonicity comparisons give
  direct rational mass reserves. All 14 inverse-sine Taylor
  comparisons and all six final rational reserves are displayed.
  This replaces 14 corner charges, two middle charges and three
  empty tests by analytic inequalities.

The inverse-angle enclosure theory from original Sections 4--5
is unchanged: common open rectangles lie inside the exact squares,
quadrant circle arcs use correctly directed inverse-angle intervals,
and the pi and inverse-angle estimates are established by signed
atan remainders and half-angle identities. Those primitives now
evaluate only the five fixed common rectangles below.

## 4. Exact five-charge witness

Let
\[
                  B=83886080,\qquad Q=2^{56}.
\]
Every coordinate in the following table is an integer numerator over
\(B\). A parameter enclosure supplies the common rectangle
\((a_h-1,a_l)\times(b_h-1,b_l)\), exactly as in the original proof.

| Charge | \(a_l\) | \(a_h\) | \(b_l\) | \(b_h\) | Target mass |
| --- | ---: | ---: | ---: | ---: | ---: |
| Left line minimum | 77762396 | 77846283 | 41943040 | 41943040 | \(1\) |
| Right line minimum | 91436699 | 91436700 | 41943040 | 41943040 | \(1\) |
| Outer \(b=1/2\) | 162444695 | 162444696 | 41943040 | 41943040 | \(201/200\) |
| Outer \(b=13/12\) | 141028166 | 141028167 | 90876586 | 90876587 | \(201/200\) |
| Outer diagonal | 118632832 | 118632833 | 118632832 | 118632833 | \(201/200\) |

The left line charge uses only radii \(1/10,1\) and the actual
origin atom. The right line charge uses radii \(1/10,1,11/10\),
without an atom. Each outer charge uses the three large circles and
no atom. Extra circle contributions are nonnegative and omitted.

At scale \(Q\), with the same conservative upper pi normalization,
the five strict integer charge margins in table order are
\[
 \begin{gathered}
 1153182092959159440,\qquad2475502032000671400,\\
 2486115696770948576,\qquad1716983502928824028,\qquad
 336341375099883104.
 \end{gathered}
\tag{3}
\]
The integrated checker additionally reconstructs the fixed outer
derivative enclosure, the line critical-point identities, all
displayed rectangle Taylor and mass reserves, and the original
strip reserve. It uses no floating-point arithmetic, adaptive
subdivision, empty test, numerical optimization or unproved root.

The independent checker uses exact rational Machin bounds with
40 terms, two half-angle reductions, and 32 alternating atan terms
at scale \(2^{80}\). On the same five boxes with the same selected
circle contributions and targets, it obtains strict margins
\[
 \begin{gathered}
 19347185060999821130904660,\quad
 41532032299372156640399944,\\
 41710100045798634478003694,\quad
 28806203097097727099813416,\quad
 5642871899810464564262128.
 \end{gathered}
\tag{4}
\]
It also independently encloses the original pi interval. This is an
alternative audit of the same witness, not five additional proof
obligations or a second certificate.

## 5. Historical five-point count and retained limits

At the October 26 checkpoint, the global-measure dependencies consisted of
five fixed whole-box mass checks, one fixed derivative enclosure,
and the explicitly displayed analytic Taylor/rational comparisons.
There are zero adaptive splits and zero empty-domain tests.
The reduction replaces 208 mass charges by five, removing 203 such
obligations. It does not claim that the entire theorem is free of
finite arithmetic or that every arithmetic assertion is one of the
five charge checks.

NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py and
NINE_RADIUS_TWO_MEASURE_INDEPENDENT_CHECK.py remain unchanged as
historical alternative proofs of the same witness. They are not
required as 208 additional current charge obligations once this
five-charge assembly is accepted.

The conclusion remains exactly the uniform geometric bound \(R>2\).
Its accepted join with the whole-core \(R<2\) theorem closes the
original all-unique/all-side C6 gate in
SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md without changing
the original nine squares or their individual weights. This
certificate reduction changes no additional graph gate. The target
\(R^2\ge1105/256\), equality classification, remaining radial and
other geometric families, and Lean integration are separate
obligations. No Lean compilation or CI was run.

