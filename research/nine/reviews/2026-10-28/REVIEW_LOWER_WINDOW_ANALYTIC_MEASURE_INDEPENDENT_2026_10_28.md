# Independent review of the original W.3 lower-window join

**Verdict: PASS.** The new join discharges the existing original fine
obligation `W.3` using a complete same-nine hand proof of `R>2`, with
no assumed lower-radius window and no eight-square import. The gate
effect is exactly **one fine closure and zero coarse closures**. It
does not prove the sharp target or its equality classification.

## 1. Exact source and operative dependency versions

I independently read the complete new source
`LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md`, SHA256
`3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90`.
I then read the full operative parts of all six mathematical modules
in its current dependency graph, including each explicit analytic
dependency update:

| Module | Exact SHA256 | Operative parts independently read |
| --- | --- | --- |
| `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` | `4c9e708945938c3f9df575e76f7573903d6b5a0ce4eccb5bcea760353a47458a` | Measure, normalization, complete geometric reductions, direct strip and exhaustive cover in Sections 1--3 |
| `NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md` | `714e2a092af516fad1450d2aeb38a6529418ef72070b5184d462a3f4b8a8f18d` | Complete line formulas, derivative signs and two exact minimum locations, Sections 1--3, with the current analytic target replacement |
| `NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md` | `8b749abf2792e022b2a3bb79ea275ebc02000707c864a4ae41f5b6410edeb780` | All four corner cases, two middle cases, fourteen signed Taylor comparisons and six mass sums, Sections 1--3 |
| `NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md` | `9258e4d00c0935a4deee1942159b88a7474e95169443d1ed966da3156a336eba` | Full actual face-transition cover, continuous monotonicity and convexity, initial/final branches and strong-convexity join, Sections 1--4 |
| `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md` | `9a4656cc90ab81200847c8b6958fc6e089fc4b807b401705663304be4f782c4b` | All thirteen signed Taylor targets, elementary pi bounds, both line minima, three outer values, radical derivative estimate and complete assembly |
| `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` | `c316fbce9320918ba88e46c4cd53b5c70c8ccdb2cc585171204f28385905929f` | Full physical normalized-domain assembly and the same-nine measure contradiction, Sections 1--3, with its current analytic dependency update |

All six hashes match the exact versions listed in the new join. These
are the analytic updated versions in the recovered publication tree,
not an earlier baseline version still requiring fixed-angle checkers.
The previous complete source-specific reviews and adoption records
remain the declared accepted dependency context. This review does not
purport to re-audit unrelated project gates.

## 2. The new W.3 implication has no hidden radius assumption

The new statement starts with arbitrary nonnegative `R`, nine actual
closed unit squares, their independently oriented actual frames, one
unchanged disk center, and pairwise disjoint open interiors. If
`R<=2`, the same physical units are contained in the same-centered
fixed disk `D_2`. This is disk inclusion, with no scaling, motion,
omitted unit or extracted smaller component.

The measure proof is about every individual unit in this fixed `D_2`.
Its original own-frame normalization is exactly
`S(a,b)=[a-1,a] x [b-1,b]`, `1/2<=b<=a`, `a^2+b^2<=4`.
This follows from the actual farthest corner, with no physical circle
contact assumption. The radial measure is unchanged by each individual
unit's coordinate normalization. Nothing puts the nine squares into
one common orientation.

The constants used in the normalized cover and its measure circles are
own-frame parameters or fixed measure radii. None is a hypothesis
`R>=79/40`, `R>=2`, or an imported packing lower bound. The operative
sources contain no stress, contact-graph, eight-square or lower-window
packing theorem on the path establishing the mass inequality.

## 3. Continuous coverage and all boundary conventions reconstructed

I checked the exhaustive six-region split directly from the normalized
domain. The initial region uses its actual interior origin atom and
small circle. The inner strip reduces by its even increasing angular
density to `b=1/2`, with the origin contribution unchanged and the
negative circle branch explicitly absent. The middle strip gives its
two-circle lower bound throughout the whole interval stated. The outer
comparison only reduces the value of the same measure when the lower
x face is moved outward to `a=sqrt(4-b^2)`; it is not a physical motion
of any packing square.

For the line, the two derivative signs have the stated polynomial and
linear numerators. The left numerator is strictly increasing and has
opposite endpoint signs, so the unique left minimum lies in its exact
`927/1000<a_0<928/1000` enclosure. The right minimum is the exact
rational `324943/298110`. The actual `a=1` square is assigned to the
atom-free right formula. The left scalar function's continuous
extension does not give an origin atom to that actual boundary square.

In the corner rectangle, I checked the four actual subdomains, their
open-rectangle inclusions and the mixed case's entire density
comparison. In the middle rectangle, the order `b<=a` supplies the two
common open rectangles and all three circle intervals. The signs of
the combined non-pi numerators determine the proper pi-bound direction;
the negative combined term correctly uses the lower pi bound. All
boundaries `a=1`, `b=1`, `a=21/20` and `b=6/5` are explicitly covered
without a limiting atom.

For the outer curve, I checked the exact upper and lower circle-face
transitions and the absence of lower clipping at the two larger radii.
The derivative identity for each capped circle gives decreasing arcs.
The second-derivative identity, including the complete quadratic lower
bound with positive discriminant reserve `1799/1600`, gives its
continuous strict convexity. The strip-circle derivative signs are
valid on their full used interval. The initial and final ranges reduce
to their real geometric endpoints, and the whole middle interval has
`M''>1/30`, with the exact tangent `b=13/12` in its interior.

The current analytic fixed-value source evaluates the actual two line
minima and the three actual outer targets, rather than requiring a
historical rounded rectangle charge. Its signed Taylor bounds have
the correct inverse-angle direction on the monotone branches. The
three small subtracted angles are bounded on one whole interval. Its
positive radical intervals and rational substitutions give the correct
lower/upper directions for each derivative term. Their weighted sum
lies between `-19917/500` and `-1629/200`, hence has absolute value
less than forty. With `pi>3`, this proves the stated derivative target.

The resulting uniform outer bound follows from the exact identity

\[
 \frac{201}{200}-\frac{|y|}{150}+\frac{y^2}{60}
 =\frac{3013}{3000}+\frac{(|y|-1/5)^2}{60}>1.
\]

Actual face-transition endpoints are included by the same formula or
continuity of angular measure. Only finitely many circle/edge points
are removed when using open square interiors, and those have zero
angular measure. The origin atom is always treated separately.

## 4. Exact arithmetic corroboration and acyclic dependency order

I independently recomputed all thirteen fixed-value Taylor comparisons
and all fourteen rectangle Taylor comparisons using exact rational
polynomials, with their printed positive directions and reserves. I
also independently recomputed the five new mass bounds, all six
rectangle mass reserves, the direct strip's sine and mass comparisons,
the Machin lower pi reserve, the outer convexity reserves, both weighted
derivative sums, the final completed square, the measure's total mass
and `2-79/40=1/40`.

The companion record is
`INDEPENDENT_LOWER_WINDOW_ANALYTIC_MEASURE_EXACT_RECORD_2026_10_28.json`.
It contains 49 exact identities/comparisons and all six exact input
hashes. This arithmetic corroborates the displayed hand inequalities;
it is not an inverse-angle evaluator or a new source of numerical
mass premises. No historical checker was executed.

I checked the explicit Machin identity in the new join: the two
tangent formulas give `tan(4 arctan(1/5)-arctan(1/239))=1`, and its
angle lies strictly between zero and `pi/2`. The elementary integral
gives `pi>2` independently to select that branch. The lower signed
atan sum and the positive polynomial-division integral then give
the printed lower and upper pi bounds. No packing theorem occurs here.

The active mathematical graph is acyclic: define the measure and
physical domain; prove geometric comparisons and continuous line,
rectangle and outer formulas; prove elementary Taylor/pi bounds;
evaluate the actual line and outer targets; assemble the full mass
inequality; apply additivity to all nine actual open interiors.
Mutual historical bibliographic references do not introduce a
mathematical dependency from one of these preliminary inequalities
back to the final packing contradiction.

## 5. Accepted original closure and retained limits

For every actual unit in `D_2`, the assembled theorem gives
`mu(int S)>=1`. The nine open interiors are disjoint measurable sets,
so their combined mass is at least nine. The same nonnegative measure
has total mass `8997/1000<9`, a contradiction. Therefore the original
nine-square packing has `R>2`. Since `2-79/40=1/40>0`, this proves
the original requested weak lower window, and in fact its strict form.

This accepts the exact original `W.3` closure. The older eight-square
import remains an alternative and is not needed on this route. The
replacement does not remove unrelated arithmetic, selection,
canonicalization, compactness or stress prerequisites of the project.
The finite displayed Taylor, radical and rational inequalities remain
part of this hand proof; no claim of an arithmetic-free theorem is
being made.

All nine physical units and their original circle are retained.
The theorem is not asserted for a smaller isolated component. The
target sharp radius and equality classification remain separate.
No original source bytes, fine label, shared ledger, remote state,
Lean file, compilation, CI or workflow was changed by this review.
