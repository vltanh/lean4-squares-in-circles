# Strict-radius application to the original 011/00 mask

This is a conditional application of an accepted theorem. It does not close
the 011/00 mask, change any D821 premise, or assert a result at closed Q.
The target is the original nine-square predicate with squared radius
q < Q = 1105/256. Every original frame, corner, physical pair and center
cone is retained. The exact long-mask bits are actual AB, strictly weak
BC, and strictly weak CD. Both short links EF and FG are actual.

Let X be either original H or original I. Suppose a certified caller state
proves all of the following:

- the canonical angle of D is nonnegative;
- y_G - y_D >= 0 and |x_G - x_D| < 1;
- x_B <= x_X <= x_D;
- |y_X-y_B| + |y_D-y_X| <= 3/5.

The selected originals A, B, X, D, E, F, G are seven distinct physical unit
squares. The unchanged actual AB, EF, and FG comparisons provide exactly
the three projection hypotheses of the accepted actual-AB two-link theorem.
Its remaining hypotheses are the four guards just listed. Consequently
q >= Q, contradicting the strict-radius target. C and the unused extra
remain physical in the original nine-square caller; this argument discards
none of their constraints and introduces no surrogate square.

The theorem's q >= Q conclusion does not assume actual BC, a weak CD bit,
or any other comparison involving C. The separate equality-blocker paragraph
for the previous 001/00 caller uses actual BC. That paragraph is not used
here. No conclusion is made about whether the 011/00 predicate can hold at
q = Q. In particular, neither existing closed-Q witnesses for other masks
nor any future 011/00 boundary witness would be contradicted by this adapter.

## Exact guard and target separation

The producer and independent checker reuse byte-identical quantitative guard
implementations from the accepted H/I substitution package. The adapter
changes only the application scope, from the previous 001/00 caller to the
explicit strict 011/00 target. Both require the external arguments
`mask='011/00'` and `radius_mode='strict'`; a closed-radius call is rejected.
The independent checker reconstructs the full printed literal and rejects
changes to the target, comparisons, guard values, or closed-Q claim.

This check validates the quantitative implication from the certified state.
It does not certify the state's geometric ancestry. A future full-mask
dispatcher must independently establish the unchanged all-nine strict
011/00 caller, replay the accepted theorem's exact scalar certificate, and
then bind the state and literal to this adapter. `ACCEPTED_DEPENDENCIES.json`
pins the accepted theorem and label-substitution dependencies. The inherited
scalar proof has 28 domains, 103 leaves and 12,875 rational Bernstein
coefficients; no new scalar search or scalar theorem is claimed here.

If these guards are not implied, this application returns an unproved guard.
A complete full-mask proof must retain and close every complementary domain.
Neither guard controls nor the present application provide original-cell or
whole-mask closure credit.
