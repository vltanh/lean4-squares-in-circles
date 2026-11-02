# Structural audit of the actual-four occupancy assembly

November 2, 2026. This is an exact finite coverage audit. The previously
remaining full-side-middle low-floor input now has its complete exact
replay and independent source audit, and its original-nine caller has
also passed independent review. The source arguments below therefore
supply the complete actual-four strict-radius assembly. Publication and
the fixed-ledger update remain the parent task. No Lean or CI.

## 1. Normalize before assigning columns and short-edge bits

Retain an actual horizontal main four-chain which is also a center-cone
chain, and a disjoint selected outsider horizontal cone three-chain. A
strict counterexample admits common expansion of all original centers,
retaining their frames, to the closed Q-disk. Original physical pair
separation, corner containment up to the first Q boundary, actual main
comparisons, and all cone comparisons survive. The adjusted original main
endpoint span becomes strictly greater than two.

The selected short links must be checked again after this expansion.
Actual projection comparisons survive expansion; strict weak comparisons
can become actual. There is no need to assume their bits are preserved.

If exactly one normalized short link is actual, the complete closed-Q
`000/01` or `000/10` theorem excludes the normalized configuration.
If both are actual, the selected short adjusted endpoint span B is at
least one. Adding the two universal physical pair caps gives

\[
 46D+(27/2)B\le211/2,
\]

which contradicts D>2 and B>=1. Thus the remaining normalized family has
both selected short links weak. This is exactly the short-edge premise
needed by the remaining middle-main seven-unit subsystem.

All columns and marker orders below refer to the normalized original
configuration. A separate claim that expansion preserves an earlier
central/side count is unnecessary.

## 2. The complete outsider count list

Use left side x<=-l, central |x|<l, right side x>=l, with l=29/60.
The side-capacity theorem gives at most two outsiders in each side.
There are five outsiders. Up to horizontal reflection the integer count
triples are exactly

\[
 (2,1,2),\quad(2,2,1),\quad(2,3,0),\quad
 (1,3,1),\quad(1,4,0),\quad(0,5,0).
\]

Indeed the central count is 1, 2, 3, 4, or 5; the remaining side total is
4, 3, 2, 1, or 0, and the cap of two leaves precisely the list above.
The two boundary lines belong to the side columns, so there is no
unassigned center or equality face.

## 3. Common routing and vertical alternatives

The common cone-three routing theorem places the selected middle P in
the central strip. After one vertical reflection it places P above both
inner mains, selected L above the left main, and selected R above the
right main. Every central outsider is either above both inner mains or
below both, with equality excluded by physical clearance. The selected
triple cannot be wholly central, since its horizontal span is at least
sqrt(2), greater than 2l.

If selected R is central, selected L is a genuine left-side outsider,
P is negative central, R is positive central, and the original L center
is above 27/40. The horizontally reflected assertion handles a central L.

The complete caller allocation is therefore:

| Normalized count | Exhaustive internal alternatives | Complete caller location |
|---|---|---|
| (2,1,2) | Full-side markers, up to both reflections: middle/middle, bottom/bottom, bottom/middle; opposite extremes impossible by the main cone | `ACTUAL_FOUR_FULL_SIDE_OCCUPANCY_CLOSED_HAND_PROOF.md` |
| (2,2,1) | Full-side main bottom, middle, or top | Bottom/top: `ACTUAL_FOUR_221_FULL_SIDE_BOTTOM_CLOSED_HAND_PROOF.md`; middle: `ACTUAL_FOUR_221_FULL_SIDE_MIDDLE_ASSEMBLY.md` and its complete seven-unit tables |
| (2,3,0) | Selected P,R central and upper; third central upper or lower; full-left main bottom or middle | `ACTUAL_FOUR_230_WHOLE_OCCUPANCY_CLOSED_HAND_PROOF.md` |
| (1,3,1) | One, two, or three upper central originals | One/three: `ACTUAL_FOUR_MANY_CENTRAL_EASY_CALLERS.md`; two: the two callers in Section 4 below |
| (1,4,0) | Selected P,R central and upper; total upper central count 2, 3, or 4 | Two/four: `ACTUAL_FOUR_MANY_CENTRAL_EASY_CALLERS.md`; three: `ACTUAL_FOUR_140_THREE_UPPER_ONE_LOWER_CLOSED_HAND_PROOF.md` |
| (0,5,0) | Selected triple would be wholly central | Direct cone-span contradiction |

For (2,3,0), the full-left main cannot be top because the selected L is
above it. For (2,2,1), the bottom/top theorem does not need a selected
short-chain order, so its vertical reflection remains applicable even
when the selected triple initially routes upward.

## 4. The last (1,3,1) height split has exactly two side-order families

Suppose exactly two central originals are upper and one is lower. At
least one side outsider is a selected endpoint, so at least one side
outsider lies above its own main. Both side outsiders cannot lie below
their mains.

If both lie above their mains, the complete caller is
`ACTUAL_FOUR_131_BOTH_SIDE_UPPER_CLOSED_HAND_PROOF.md`. It treats both
possible selected-chain endpoint placements, both-high side heights, and
exactly-one-low side heights. Two low side heights are excluded by the
original selected cone-chain span.

Otherwise, after horizontal reflection the left side outsider is above
its own main and the right one below. The latter cannot be selected, so
the selected right endpoint is central and the selected left endpoint is
the left side outsider. The complete caller is
`ACTUAL_FOUR_131_OPPOSITE_SIDES_CLOSURE.md`. Its two cone budgets keep
the same original P frame, and its final cap uses the original L,P,R.

These side orders are strict by physical same-side clearance. There is
no equality case or third side-order family.

## 5. Dependency direction and proof boundary

The normalized bit reduction uses only earlier actual-short-chain results.
The side capacity, common routing, main/endpoint geometry, and universal
physical pair cap precede all occupancy callers. The widened five-square
cap is a common terminal; it does not depend on any occupancy caller.
The new pair orientation tolls depend only on the original universal pair
support reduction and their own one-dimensional scalar covers, so using
them inside the middle-main seven-unit exclusion creates no cycle.

Within that seven-unit proof, the independently completed low-right
exclusion precedes its use in the low-floor exclusion. The latter's
2,821,264 strict leaves passed the separate exact C++ replay, and its
complete source, contractor, and coverage audit is recorded in
`MIDDLE_MAIN_LOW_FLOOR_CPP_INDEPENDENT_AUDIT.md`. The required original
lower-side main-height theorem has its separately replayed 74-row cover.
The complete original-nine caller review is
`FULL_SIDE_MIDDLE_221_INDEPENDENT_ASSEMBLY_REVIEW.md`.

Every entry of the finite list is now supplied by a complete source
argument. The normalized short-bit cases in Section 1 and the exhaustive
occupancy/height choices above therefore exclude a strict counterexample
with an actual cone four-chain and a disjoint outsider cone three-chain.
In particular they discharge the entire fixed `000/11` strict-radius
domain. The conclusion is a sharp strict-radius closure, not an assertion
that its closed-Q domain is empty.
