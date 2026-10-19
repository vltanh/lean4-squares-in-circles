# Independent review of the whole low/middle pair entry

**Result: PASS for the stated strict L/M entry `.9005`.** I rederived
the continuous case reductions, all target and source support choices,
and the polynomial enclosures, and independently reconstructed the
displayed finite arithmetic. The result uses the upstream exterior
gap and signed-axis reductions stated in the manuscript. It does not
assume the frame concentration that this table is intended to prove.

## Reviewed files

| File | SHA-256 |
|---|---|
| `LOW_MID_WHOLE_PAIR_HAND_PROOF.md` | `6ce5edf08836a572a9f18a3d52219d7c5228da87df1f1a9e550b24838113ea68` |
| `verify_low_mid_whole_pair_hand.js` | `e3281841f98ba3ffc8e54028fc2fc8049379b429c726a126cee94e9ffa950ca8` |
| `audit_low_mid_hand_polynomials.py` | `c4d3408d77c7748221a66360ce441850a2a9bec61f4e8cee05cb4b3663a4de88` |

The reviewed manuscript includes one small correction: the intermediate
bound `L-.98b <= .004b-.11b^2` is non-strict at `b=0`. Its final
uniform bound `<.00004` is still strict. No later estimate changes.

## Coordinates, angle ranges, and support algebra

The retained source margins follow from the own-frame centers
`(a,-sigma*b)` with the stated signs. Reflection followed by reversal
preserves the frame increment and corrected cost, sends the signs to
`(-tau,-sigma)`, and covers the retained target axes.

I independently checked the sign-specific angle lower bounds. The
shared L/M cut makes the angle difference nonnegative for L-to-M `++`
and M-to-L `--`, so their `.76` lower bounds are valid. All other
entries follow with the correct directions from the arctangent bounds.
In particular, every actual frame increment here is positive.

Both labels increase and are concave on their arcs. The endpoint
secant test for `M-lambda*b` has the correct direction: `lambda>=.8`
selects the upper endpoint and `.797` selects the lower. The convex
negative-source and primary-source support choices follow from the
stated derivative inequalities. The `.98` low-source bound follows
from a uniform negative second derivative, so it covers the interior
minimum that an endpoint-only test would miss.

For each axis and quadrant I rederived the two trigonometric
coefficients and the norm square in (8). The adverse target constant
for L has the correct sign. The affine source floor in row 4 uses an
upper bound on the source transverse coordinate and a lower bound on
its label; its multiplier exceeds `.8` throughout the entire row.
The primary source floors likewise use the adverse upper coordinate
and upper label bounds.

## Continuous cover

All eight ordered secondary sign cases are covered. The negative
target endpoint supports are justified either by concavity or by a
strictly positive derivative when their primary coefficient changes
sign. The amplitude bounds used for increasing scalar functions are
valid on both endpoints of the corresponding full type arc. The
slightly negative derivative bounds in Sections 3.3 and 3.5 are used
with the full interval length and leave the claimed strict reserve.

For the delicate M-positive/L-positive case, the initial SAT barrier
is valid on the whole interval through `.4`. The affine-multiplier
row covers `[.4,.79]`. On `[.79,.95]`, the source secant selects the
lower M endpoint and the target derivative selects the upper L
endpoint. These endpoints have exactly the same coordinates, as used
in the scalar formula. The derivative amplitude is below one, so
the value at `.79` bounds the entire interval. The tail joins it at
`.95` without a gap.

For M-negative/L-positive, the full-circle norm is nonzero, and its
rotating-norm identity is exact. The monotone quarter-norm bound and
the triangle bound in the second quadrant have the correct scope.
They make both scalar pieces strictly concave. The three endpoint
comparisons thus cover the whole interval, not sampled states.

For a primary axis, its hypothesis is independent of the source
sign, so proving the smaller negative-source cost covers both signs.
Each of the four primary barriers is a valid uniform bound for all
coordinates on the stated arcs. The positive trigonometric sums used
in those barriers are concave on the specified first-quadrant
intervals; their endpoint tests therefore have the correct direction.
The negative-target endpoint scalar in Section 4.3 is also concave.

The polynomial intervals straddling `pi/2` are harmless enlargements:
the first-quadrant formula is used only on its physical first-quadrant
part and the second-quadrant formula only on its corresponding part.
Their rational domains overlap across `pi/2`. The direct tails cover
all larger frame increments. No omitted sign or angle regime remains.

## Polynomial and exact arithmetic checks

The trigonometric replacements in (9) all have the right direction:
positive and negative sine coefficients use their respective lower
and upper Taylor polynomials, negative cosine coefficients use an
upper polynomial, and the norm-square terms use lower polynomials
when their coefficients are negative. These alternating remainder
bounds are valid through the largest endpoint `1.71`.

The expression being squared is separately positive on every row.
Thus `P=T^2-QV>0` implies the desired support inequality without a
sign ambiguity. There is no numerical root selection in this step.

The author's JavaScript replay passed all **305 strict comparisons**.
Its operations are exact integer fractions. The final status checks
every comparison, and no floating approximation accepts a bound.

The independent Python checker reads the coefficient lists and
positive-T floors from the manuscript and reconstructs all eight
polynomials from its formulas using `Fraction`. It directly computes
the Bernstein coefficients in the declared degrees. This separately
verifies all **146 displayed P coefficient bounds** and all **77
positive-T coefficient bounds**. It also reruns the JavaScript replay.
All checks passed.

In row 4 the polynomial's actual degree is 16, while the printed
Bernstein basis has degree 18. This is legitimate degree elevation;
the independent checker directly converts to degree 18 rather than
depending on the author's zero-padding convention. The smallest
printed coefficient bound in this row is `394/1000000`, which is
strictly positive and sufficient for the proof.

## Equality scope

Every feasible pair in this entry has corrected cost strictly greater
than `.9005`. There is no equality case in the rounded L/M bound.
This strict pair-table conclusion does not by itself classify the
equality family at the sharp packing radius; the latter remains an
independent global assembly and stationary-dual question.
