# Second-pass human-proof audit: J–N

Baseline production commit: `1dbbd4f106e9860752e9c0c612864196167df103`.
Research branch: `research/seven-human-analytic`, PR #8.
All deliverables are under `research/seven/`; production integration is separate.

## Completed mathematical replacements

| Item | Old numerical device | Replacement | Mathematical output |
| --- | --- | --- | --- |
| J | Interior test label 18/25, test-value/test-slope brackets | Stronger curvature, the actual diagonal endpoint, monotone circle-correlated comparison | `transitionF > 1/32000`; `diagonalValue > 1/640` |
| K | Tangent at 1/8 and six-digit radical/reciprocal brackets | Uniform curvature at most -1/8 and exact origin data | `arcEnvelope <= pi/6+353/648`; the same 801/1600 marker width |
| L | Five-decimal enclosures of J,a0,u0,rd and diagonalAngle | Circle/line monotonicity and two derived endpoint tests | Coarse geometry sufficient for all identified callers; `3/5<diagonalAngle<5/8` |
| M | Tuned shifted squares in state exclusions | Disk projection in direction (2,1), then constrained corner distances | The original three strict state bounds |
| N | Tight sqrt(3) enclosure at the initial boundary ratio | Exact comparison with the smallest geometric angle, pi/12 | `ratio(0)<tan(pi/12)`; an exact proof of the old 51/200 bound is also supplied |
| P | Need for an elementary pi bound in L | Rational tangent identity and two integral remainder estimates | `157/50<pi<377/120<22/7` |

K intentionally replaces the *internal* numerical envelope conclusion
5443/10000 by a sufficient 353/648 bound. It does not claim to prove the
former constant. L likewise replaces unnecessarily tight helper statements
with the coarse statements their mathematical callers need. Neither changes
the original packing, marker theorem, contact cases, radius, or column family.

## Dependency order and circularity audit

1. P supplies the elementary pi bounds. Standard trigonometric and real-algebra
   facts are assumed in the usual way.
2. M uses only the admissible disk, label definitions and those pi bounds.
3. L starts from the explicit circle/line intersection formulas, establishes
   the correct branch with coarse estimates, and then proves its own coarse
   geometry. It does not assume the old `transition_coarse` or tight bounds
   while proving their replacements.
4. K uses the exact envelope derivatives and a direct curvature comparison.
   It can establish the curvature as well as the envelope bound, so the separate
   earlier A proof is optional on this revised marker route.
5. J uses L's coarse geometry and the existing circle derivative identities.
   It proves endpoint data independently before invoking the tangent-parabola
   theorem. Neither `test_point` nor either target positivity theorem is used
   as a premise.
6. `diagonal_value_pos` follows from J by angle order. The independent upper
   domain bound for the inward-circular theorem comes from L, not from assuming
   that diagonal positivity or the inward-opposite theorem is already known.
7. N initializes the existing monotonicity proof using its geometric angle;
   B continues to supply the derivative-ratio inequality.
8. A–F/G and the untouched geometric fixed-gap/all-gaps/contact assembly retain
   their stated roles. E's side-tangent estimate uses L's coarse reserve.

This is a source-level mathematical dependency review. An elaborated Lean
constant-dependency audit is still required after implementation.

## Exact arithmetic cross-checks performed in this continuation

89 independently evaluated exact symbolic/rational assertions passed:

| Note | Number | Examples |
| --- | ---: | --- |
| K | 12 | Ratio factorization; critical point; origin data; completed parabola; all marker margins |
| M | 9 | Cauchy projection identity; label cutoff; constrained corner-distance identities |
| N | 3 | Geometric tangent comparison; optional old-helper identity; square difference |
| L | 26 | Branch selection; root comparisons; coarse coordinate/angle bounds; tangent reserve |
| J | 33 | Curvature constants; four partial derivative identities; corner substitution; sine/cosine comparisons; final reserve |
| P | 6 | Double-angle identities; tangent subtraction; both pi estimates and their ordering |

These are exact checks, not a mesh of real sample points. They corroborate the
written arguments; their success is not a mathematical premise. A finite
number of arithmetic checks does not by itself prove a continuous inequality:
the interval conclusions come from the monotonicity, curvature, and geometric
comparison arguments in the notes.

## What large rationals remain, and why

The goal is not to make every numerator small. It is to remove unexplained
quantitative choices and coefficient acceptance as the central argument.

* In J, `2351/3744` is the explicitly derived angle of a comparison corner,
  not an enclosure of an unknown angle. `59/37440` and `68647/1572480` are
  sums of displayed endpoint products. The simple margins actually consumed
  by the curvature argument are 1/640 and 7/160.
* In M, 2852/1125 and 1623/5600 are outputs of linear elimination; 69/6400
  is a corner's squared-radius excess. The directions/corners are explained
  before these quantities are evaluated.
* The older F note still displays the expanded degree-11 polynomial and a long
  fraction for its exact endpoint value. It no longer uses a Bernstein vector:
  its sign comes from a short bound on its derivative and that single endpoint.
  These expanded coefficients are not claimed to disappear.
* In the unchanged lower-marker estimate, `1331/256000=(11/40)^3/4` is a
  Taylor remainder. The support constant 2171/1200 has squared margin
  `247/480000` over `(145/144)(13/4)`. Substituting it yields the explicit
  marker reserve `7/768000` using only pi>157/50. This is a scalar disk-support
  calculation, not a hidden table.
* P's optional expanded remainder integers arise from two explicit arctangent
  truncations. The proof can be read using the factored expressions without
  displaying those expanded integers.

Thus the new route removes the audited five-/six-decimal *enclosure chains*,
not all large exact arithmetic. The old production constants remain physically
present until a maintainer integrates the replacements.

## Retained features that are mathematical, not numerical search

The four separating axes, transverse signs, active/capped labels, circle/line
junctions, capped triangle, and contact-cycle bookkeeping remain. So do the
small-gap/leftmost-minimum arguments. The marker perturbations `0,+/-1/3200`
are deductions from a positive arc-width reserve, not evidence from sampling.
The rational 2/5 overlap endpoint in G has an explicitly proved reserve.

No exhaustive angle-box subdivision, generated stress classification, or
external success premise is introduced in these replacements.

## Limits of completion

The identified humanization tasks A–F and J–N now have written mathematical
solutions and integration recipes. This is not a guarantee that every reader
will find every algebraic calculation short, nor a claim that the production
formalization already uses these arguments.

Not performed: implementation of the proposed Lean bodies, production changes,
Lean build, Comparator, axiom inspection, or independent kernel replay.
Those remain maintainer integration/verification tasks. All commits in this
continuation request CI skipping with `[skip ci]`.
