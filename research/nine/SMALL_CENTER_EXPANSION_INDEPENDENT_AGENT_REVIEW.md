# Independent agent review of sufficiently small center expansion

November 2, 2026. The proposal was authored by `/root` and independently
reviewed by `/root/root_certificates`. This is an independent agent review,
not a human, kernel, Lean, or CI review.

## Reviewed claim

A strict original nine-square counterexample with largest squared corner
norm q<Q may be expanded by a common factor lambda>1 sufficiently close
to one, moving centers and retaining every physical frame, so that:

- all original corners remain strictly inside the Q-disk;
- every original pair of closed squares becomes strictly separated;
- all actual main comparisons and all cone comparisons persist;
- each designated strictly weak short comparison remains weak;
- every original central outsider remains central and every side outsider
  remains on its original side;
- the original endpoint span becomes strictly greater than two.

## Review

For each of the 36 original corners, its squared norm after expansion is
`|lambda*c_i+v_ij|^2`, a continuous function of lambda whose value at one
is at most q<Q. Finitely many strict margins give a common open interval
of admissible lambda around one.

For each original pair, choose one genuine separating normal n. Initially
`n.(c_j-c_i)>=H_i(n)+H_j(n)>=1`. Expansion multiplies the left side by
lambda and leaves the support sum unchanged. Every lambda>1 therefore
makes this separator strict. The finite family of these strict separators
gives disjoint closed original squares.

An actual horizontal main comparison has positive center gap and remains
actual under expansion. A cone comparison is homogeneous in the center
difference and is unchanged. For a designated weak short comparison,
`d_x<h_i+h_j` with d_x>0; requiring
`lambda<(h_i+h_j)/d_x` preserves that strict weak inequality. There are
only finitely many such comparisons and all these upper bounds exceed one.

For each central outsider with nonzero x-coordinate, requiring
`lambda<l/|x_i|` preserves `|lambda*x_i|<l`. A zero coordinate stays zero.
Again the finite upper bounds all exceed one. Existing side coordinates
with x>=l or x<=-l move farther into their same sides. Relative vertical
center order is preserved by multiplication by the same positive lambda.

Writing the original adjusted endpoint span as
`D0=x3-x0-h0-h3`, the actual four-chain gives
`D0>=2(h1+h2)>=2`. Hence
`Dlambda=lambda*D0+(lambda-1)(h0+h3)>D0>=2`.

Taking the minimum of the finite continuity, weak-edge, and central-strip
upper bounds leaves a nonempty choice interval with lambda>1. This proves
all claims simultaneously. No largest possible expansion is needed.

The reviewer checked
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md`: the complete
three-marker theorem in Sections 1--5 requires only containment in the
closed Q-disk and physical nonoverlap. The marker-order argument in
Section 7 uses closed-disjointness and the same geometric bounds. Neither
requires a corner to attain squared norm Q. Its Section 6 choice to expand
all the way to Q is therefore sufficient but unnecessary for these uses.

Consequently the small expansion supplies all actual hypotheses consumed
by the normalized occupancy callers while preserving the original weak
bits and column counts. This review makes no change to the stable root
inventory and no new independent whole-mask claim.
