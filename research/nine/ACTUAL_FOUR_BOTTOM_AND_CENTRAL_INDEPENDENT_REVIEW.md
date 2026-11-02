# Independent review of the actual-four bottom caller and central lemmas

November 2, 2026. This is an independent assistant review of the original
physical geometry and exact arithmetic, not human or proof-kernel
verification. No Lean, Lake, or CI was run.

## Accepted scope

The following three complete hand arguments have been reviewed separately
from their authors:

1. `LOW_FLOOR_RIGHT_CENTRAL_AND_HIGH_RIGHT_SHOULDER_EXCLUSION.md`:
   the stated low-floor right central square is incompatible with the
   original left helper, right main inset, and high right shoulder.
2. `UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md`:
   two upper central originals whose horizontal center gap is at most
   one half force the higher square's whole floor above `2807/24000`.
3. `ACTUAL_FOUR_221_FULL_SIDE_BOTTOM_CLOSED_HAND_PROOF.md`:
   the complete strict-radius actual-cone-four occupancy `(2,2,1)` is
   excluded when the full-side main is lowest, together with its
   horizontal and vertical reflections.

The first two statements hold at closed `Q=1105/256`. The third is a
strict-radius caller using normalization and the resulting adjusted
endpoint span `D>2`. This review does not promote that caller to a
closed-Q exclusion or a whole fixed-mask closure.

## Low-floor right central exclusion

The review checked both left-helper alternatives: horizontal separation
and separation on the original central square's physical oblique axis.
The right-main inset forces an upward, left-pointing separator; the left
helper forces an upward, right-pointing separator in the oblique case.
Their component assignments are coupled through the same original
square frame. No independent axis choice is introduced between pairs.

The bounds `t<4/5` were checked in both alternatives. The lower bound
`a>=1-t/3` was verified on that complete interval. The resulting
horizontal center gap to the right shoulder is smaller than the sum of
the central halfwidth and the shoulder's fixed contained inset
halfwidth. Both vertical signs are also too small for coordinate
separation. The remaining signed projections onto both physical central
axes were checked, including the inward signs, the aligned endpoint,
and the diagonal limit. The two final Cauchy comparisons have positive
exact rational reserves.

Fresh execution of `verify_low_floor_right_central.py` passed all
printed positive rational comparisons. The verifier is an arithmetic
audit; geometric coverage is supplied by the foregoing signed-axis
argument and the companion manuscript.

## Upper central half-width replacement

The independent review checked the endpoint outward-quadrant corner,
monotonicity of the circular sum, and the strict diagonal resource. The
smallest printed squared reserve there is `1/180000`.

The physical proxy clearance was reconstructed from the coordinate axes
and both possible component orders of the original square's side axes.
The ordering condition is positive throughout every used inset-margin
range. This yields the uniform center-height lower bound in all three
horizontal intervals, including the two boundaries at `+/-1/60`.

Both quartic orientation bounds hold over the entire folded interval:
the first uses monotonicity followed by a uniform convex quadratic
minorant, and the second uses a global convex quadratic minorant. The
concave function `J` has the asserted uniform curvature bound, and its
anchor value and derivative bound give a complete maximum estimate.

Finally, the higher original unit is separated from the lower unit's
contained aligned square. The full physical clearance gives the stated
whole-floor formula. The zero-loss branch has a stronger floor than the
claimed threshold; the positive-loss branch yields exactly
`59/64-703/4000-151/240=2807/24000`.

Fresh execution of `verify_upper_central_half_width.py` passed the
independently reconstructed quartic identities and all scalar reserves.
Thus three upper central units always contain a pair to which this
theorem applies: their two adjacent horizontal gaps cannot both exceed
one half inside a strip of width `29/30`.

## Complete bottom-main occupancy caller

The normalization argument retains the original nine frames and all
physical pairs. Original side outsiders remain in their side bands.
A central outsider crossing into the already full side is excluded by
the established side capacity; crossing into the other side is routed
to the already accepted `(2,1,2)` theorem. Occupancy invariance is not
assumed at a moving central/side boundary.

The original two central units are each above both mains or below both.
Two below are impossible by the original unit-disk distance bound. The
right outsider's three alternatives are exhaustive:

- Below its main: the precise one-sided main-height theorem supplies
  `y2>-7/20`. The previous shared-frame floor proof needs only that lower
  bound, not a middle-marker upper bound or an extra right outsider.
- Above its main and below `3/5`: the accepted two-low-mains exclusion
  rules out a lower central unit. The low-side extraction applies on
  each central square's own horizontal half-plane.
- Above its main and at least `3/5`: the original high left and right
  shoulders are available. Two upper central units either include a
  nonpositive center handled by the left helper, or both have positive
  centers and are handled by the half-width theorem. With one upper and
  one lower central unit, the two-low-mains contrapositive gives
  `y2>-119/310`, and the low-floor right-central exclusion applies.

When both central units have high whole floors, the accepted upper-column
separation forces opposite horizontal signs. They remain distinct
original units when one supplies the central cap input and the other
supplies its right shoulder. In every alternative the widened cap
therefore applies to five distinct original units and yields `D<=2`,
contradicting the same normalized original endpoint span `D>2`.

Fresh execution of `verify_full_side_bottom_221_arithmetic.py` passed the
additional rational disk-distance and threshold comparisons.

## Coupled cone inset-loss lemma

`COUPLED_CONE_INSET_LOSS_HAND_PROOF.md` was also independently reviewed.
The own-half-plane physical clearance includes both chiralities and all
axes. The exact coupling identity

`k-g=-t^2/(sqrt(1+t^2)(1+t))`

retains the original unit's frame and its own inset. The low-slope
interval is excluded directly; on the remaining interval both sides of
the squared comparison are nonnegative. All 28 degree-six Bernstein
coefficients were freshly reconstructed by
`verify_coupled_cone_inset_loss.py`; all four printed minima are positive.
The final whole-floor reserve is exactly `13/4960` above one tenth.

Both stated cone callers follow from the original contained aligned
insets: a horizontal cone comparison and physical disjointness force
horizontal center gap at least the sum of their inset halfwidths.
No actual horizontal projection link is inferred for the original
physical squares.

## Accounting boundary

These are complete internal lemmas and an occupancy family. The fixed
registry still has the same 32 masks, with six accepted strict-radius
closures until a complete original-nine `000/11` assembly is accepted.
The 15 roadmap IDs and 7,915 positional-root IDs are unchanged. No new
positional-root closure, unrestricted lower-bound closure, or global
equality claim follows from this review alone.
