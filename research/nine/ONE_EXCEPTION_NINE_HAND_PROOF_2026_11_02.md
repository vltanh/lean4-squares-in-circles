# Nine squares with at most one exceptional coordinate pair

November 2, 2026. Hand-proof synthesis. This manuscript uses the completed
geometric arguments linked below; no mathematical program, Lean, Lake,
or CI is part of the proof.

## 1. The theorem and its exact scope

**Theorem.** Let nine physical unit squares have pairwise disjoint open
interiors and be contained in a disk of radius R. Suppose there is an
orthonormal coordinate frame such that every pair except possibly one
has disjoint open x-projections or disjoint open y-projections. Then

\[
                         R^2\ge\frac{1105}{256}.
\]

Each physical square may have its own orientation. Contact between
boundaries is allowed. The exceptional pair is required to be physically
nonoverlapping, just like every other pair; only its coordinate-projection
separation is absent.

The theorem is a sharp lower bound for this entire class, since the known
attaining packing belongs to the smaller two-direction-separable class.
It does not assert that arbitrary nine-square packings admit such a frame,
nor does it classify all equality configurations in the present wider class.

## 2. Actual orders and a single completed comparison

Write \(Q=1105/256\). It suffices to analyze \(R^2=q\le Q\),
because q>Q already satisfies the conclusion. For a physical square S,
let \(h_S\in[1/2,1/\sqrt2]\) be its projection halfwidth on either
coordinate axis, and set \(g_S=1/(4h_S)\).

Write \(S<_xT\) for the actual comparison
\(x_T-x_S\ge h_S+h_T\), and similarly for y. The universal center
bound is \(|c_S|<91/60\). In particular an actual five-chain is
impossible in either direction.

If all pairs are already covered by the two coordinate orders, the complete
[two-direction theorem](TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md)
proves the result. Otherwise denote the unique genuine exceptional pair
by A,B. Their open projections overlap on both axes.

The [physical pair-span lemma](ONE_EXCEPTION_PAIR_SPAN_AND_SHARP_TERMINAL_2026_11_01.md)
uses the actual inscribed aligned squares of halfwidth g to give

\[
 \max(|x_B-x_A|,|y_B-y_A|)\ge g_A+g_B.
\]

Choose a coordinate direction satisfying this inequality, call it x,
and reflect it so that \(x_B-x_A\ge g_A+g_B\). This is the fat
direction of the pair. Add only the comparison A<B to the actual x-order.
The [augmentation proof](ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md)
shows that this relation is already transitive: every other comparison
remains an actual x-comparison. Together with the unchanged actual y-order,
the completed orders cover every pair and have height at most four.

The [width-five proof](ONE_EXCEPTION_RANK_AND_WIDTH_REDUCTIONS_2026_11_01.md)
settles every case in which either original actual order has an antichain
of size five. Thus the remaining original widths are at most four.

## 3. The exhaustive two-pattern reduction

If both completed heights are at most three, the augmented-grid argument
gives the strict bound

\[
 q\ge\frac{825+200\sqrt2}{256}>Q.
\]

Otherwise the [height-four reduction](ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md)
applies the nine-element consequence of Greene's partition theorem.
It extracts disjoint completed chains of lengths four and three in one
direction. If they are both actual, the existing physical 4+3-chain theorem
proves q≥Q. If the exceptional pair occupies the two internal positions
of the four-chain, the physical pair-span reserve gives the same endpoint
terminal, strictly even at Q.

All remaining configurations therefore have one of the following forms,
up to the stated common reflections and relabelings:

| Pattern | Chain containing the exception | Disjoint actual chain |
|---|---|---|
| I | A<B<_xC<_xD | L<_xM<_xR |
| II | A<B<_xC | M_0<_xM_1<_xM_2<_xM_3 |

Only A<B is nonactual. The other two physical squares remain in the disk
and retain every original pairwise constraint. No smaller subsystem is
substituted for the nine-square configuration.

## 4. Pattern II: complete five-outsider capacity

[PATTERN_II_NINE_SQUARE_CONTINUATION.md](PATTERN_II_NINE_SQUARE_CONTINUATION.md)
and [BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md](BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md)
prove the complete Pattern II lower bound. Its actual four-chain is
disjoint from both exceptional squares and runs in their fat direction.

The exact transverse budget for the four-chain endpoints is
\(|y_0|+|y_3|\le1/8\). Its five outsiders have \(|x|<13/12\),
and at most two lie in either side column outside \(|x|<29/60\).
The proof exhausts all possible numbers of middle outsiders. The ordinary
alternatives produce actual disjoint 4+3 chains. The exceptional alternatives
derive the floors needed for the new
[downward](DOWNWARD_THREE_SQUARE_CAP_HAND_PROOF.md) and
[upward](UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md) physical transfer caps.
Each such alternative contradicts a strict cap sum even at q=Q.

Thus Pattern II has no strict subcritical realization.

## 5. Pattern I: all original height possibilities

The initial localization gives, after reflection in y,

\[
 L<_yA,B,
 \qquad x_A<-\frac{59}{60}-g_A.
\]

The following branches are distinct and must all be treated; the presence
of an actual four-chain cannot be silently identified with Pattern II.

1. **An actual four-chain in the fat x-direction.**
   [PATTERN_I_ACTUAL_HEIGHT_FOUR_BRIDGE.md](PATTERN_I_ACTUAL_HEIGHT_FOUR_BRIDGE.md)
   proves that any such chain has endpoints A,D. The other actual
   three-chain L,M,R is disjoint from it, because an internal intersection
   would force an ordinary outsider beyond its proved strip. The physical
   4+3 terminal applies.

2. **An actual perpendicular y-four-chain, with actual x-height at most three.**
   [PATTERN_I_PERPENDICULAR_HEIGHT_FOUR_BRIDGE.md](PATTERN_I_PERPENDICULAR_HEIGHT_FOUR_BRIDGE.md)
   retains the original ranks, every member
   of that four-chain, and all nine units. Its endpoint bounds, far-endpoint
   uniqueness and signed cap caller settle this branch.

3. **Both original actual heights at most three.**
   The [transverse-grid proof](ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md)
   and [Pattern I rank continuation](PATTERN_I_NINE_SQUARE_CONTINUATION.md)
   exclude the distinct full grid and every duplicated-top diagram.
   The remaining ranks have an actual bottom three-chain, a middle weak
   four-chain with A,B at the same rank, and an actual top two-chain.
   [PATTERN_I_HEIGHT_THREE_COMPLETE_HAND_PROOF.md](PATTERN_I_HEIGHT_THREE_COMPLETE_HAND_PROOF.md)
   treats all three missing-top-cell positions.

The completed original-height-three argument uses the
[all-upward theorem](PATTERN_I_STEEP_UPWARD_HAND_PROOF.md),
[downward owner extension](PATTERN_I_DOWNWARD_OWNER_EXTENSION_HAND_PROOF.md),
[steep downward bounds](PATTERN_I_STEEP_DOWNWARD_HAND_PROOF.md), and the
owned-axis interval exclusion from the rank continuation. Each geometric
caller derives the exceptional pair's required vertical-span bound from
the other physical squares. No assumed alignment of rank rows is used.

These branches exhaust all original heights because actual five-chains
are impossible. Thus Pattern I also has no strict subcritical realization.
Together with Sections 2–4, this proves the theorem.

## 6. What this supplies to the unrestricted problem

**Corollary.** Any unrestricted packing with q<Q must have at least two
pairs with overlapping open projections on both coordinate axes in every
orthonormal frame.

Indeed a frame with at most one such pair would meet the theorem's
hypotheses. This is a necessary condition for an unrestricted counterexample,
not an existence assertion or an unrestricted impossibility proof.

The earlier exact equality example already shows why one cannot assume an
unconditional one- or two-exception cover at q≤Q. It has an actual sharp
4+3 terminal and requires at least three exceptional pairs for every pair
of projection directions. A complete unrestricted proof must therefore
derive an appropriate terminal or treat the remaining multiple-exception
geometry directly.

No entire original positional root is removed by this class theorem alone.
The published root ledger and the same fifteen roadmap IDs remain unchanged.
