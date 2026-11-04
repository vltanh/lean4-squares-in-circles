# Independent review of the positive-D two-link guard

The reviewed helper is `positive_d_row_guard.py`, SHA-256
`a5ee541508c4b284738182827f9c80935afd0c0cc45618de13e96a8b768c82cd`.
The separate exact evaluator `review_positive_d_row_guard.py` passes 499
rational checks. No original cell or mask is closed by this review.

The physical premise is Sections 1–4 of
`WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md`.
It applies to each retained extra X=H or X=I in the unchanged strict
original-nine 001/00 caller, with its normalized CD transverse gap at
least 2/3 and the accepted upward D/G separator consequence. The helper
requires a source-bound certified state from that caller; it does not
establish the caller or accept an arbitrary collection of intervals.

The scalar layout is nine alphas, nine signed betas, nine absolute betas,
and nine inset halfwidths. Hence local scalar coordinate 12 is beta_D.
Either a nonnegative D slope or a nonnegative signed beta_D proves the
same sign premise. Original unit-frame identities remain necessary.

For two center differences the helper intersects the coordinate interval
with the certified difference interval. Reversing a pair changes `[l,u]`
to `[-u,-l]`. Both orientations, both coordinates and both X choices were
checked separately. The four signed height forms are exactly
`s(y_X-y_B)+t(y_D-y_X)` for independently chosen signs s,t. Their maximum
is the total variation. Each interval evaluation is an upper bound on
its corresponding signed form, so the maximum of these four upper bounds
bounds the total variation. The two telescoping forms can also use the
certified B–D interval. The sum of the two independently bounded absolute
gaps is a second valid upper bound, and their minimum remains an upper
bound. This reasoning does not require all four interval extrema to be
simultaneously realizable.

The six closed complementary rows are `x_X<=x_B`, `x_D<=x_X` and the four
signed height forms at least 1/2. They cover every failure of the weak
horizontal-order and variation guard. Equality faces overlap; none is
dropped. If an order is equality while variation is at most 1/2, the
corresponding pair has center distance at most 1/2, contradicting its
original disjoint radius-one-half incircles. Thus the guard's weak order
implies the strict order required by the physical theorem.

The exact checker must still retain the unchanged positive-D caller,
reconstruct all conditional rows, verify every ancestor, and close every
complementary branch before accepting a parent. Testing one extra does
not permit dropping a complement based on the other extra. The latter
may instead supply an analytic terminal within a retained branch. The
source review and finite arithmetic are accepted with this conditional
scope; complete original coverage remains a separate obligation.
