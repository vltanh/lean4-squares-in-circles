## Latest checkpoint and handoff

[New push-and-handoff](HANDOFF_A2_POST_89CC4C2_2026_11_01.md) ·
[Exact marked-chain hand ledger](UNRESTRICTED_MARKED_CHAIN_EDGE_LEDGER_HAND_PROOF.md).
The final global geometric caller is not yet proved. The reported
same-sign shoulder cap, middle-strip capacity and mixed-sign cases are
recorded as unverified continuation leads, not as a closed A.2 gate.

# n=9 — sharp nine-unit-square packing

**Global goal OPEN:** prove all nine independently oriented, interior-disjoint
unit squares inside a disk satisfy R²>=1105/256, then classify all equality
packings.

[Current proof status](PROGRESS.md) · [canonical roadmap](DEEP_GATED_ROADMAP.md)
· [current handoff](HANDOFF_A2_2026_11_01.md)

**Active gate: A.2.** Current method: hand proof, exact tables permitted;
mathematical scripts only for checking potential directions. No Lean/Lake/CI.

**New unrestricted structural results:** the
[November 2 continuation](UNRESTRICTED_STRUCTURAL_CONTINUATION_2026_11_02.md)
proves that selective completed coordinate orders have height at most four
for every physical packing. The new
[rotating-frame argument](UNRESTRICTED_ROTATING_FRAME_EXTRACTION_HAND_PROOF.md)
always supplies disjoint completed 4+3 chains in some orthonormal frame.
Added consecutive edges remain nonphysical; their remaining nine-square
geometry is still open.

The new [sharp three-square half-plane cap](THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md)
forces q>=Q whenever three whole squares lie beyond a line at distance 7/16
from the disk center, with arbitrary orientations. The
[unrestricted center cap](THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md)
also gives min(e.c_i)<21/20 for any three squares, and the
[actual-four-chain outsider strip](UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md)
now holds for every physical outsider without a coordinate-cover premise.
The [side-marker theorem](UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md)
further limits a strict counterexample to two outsiders in each side column.
The three-square half-plane terminal now also has its complete equality
family, including the free middle height. Global nine-square equality
remains open.

The entire [two-direction-separable class](TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md),
including all parallel-square packings, now has a complete sharp hand proof.
The [exact two-square cap](TWO_SQUARE_SHARP_CAP_HAND_PROOF.md) is a universal
sharp theorem, and the [two-strip terminal](TWO_STRIP_SEVEN_SQUARE_HAND_PROOF_2026_11_01.md)
needs no horizontal coordinate or separate anchor-height boxes.
The [boundary normalization](BOUNDARY_NORMALIZATION_WITH_SHARP_CAP_HAND_PROOF.md)
is a global strict-counterexample reduction incorporating the cap.

The entire [one-exception width-five branch](ONE_EXCEPTION_RANK_AND_WIDTH_REDUCTIONS_2026_11_01.md)
is also proved. The [augmented-grid proof](ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md)
and [height-four reduction](ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md)
reduce the remaining one-exception family to two weak endpoint patterns,
with all nine squares retained.

**Pattern II is now proved:** an actual four-chain disjoint from both
exceptional squares, in a fat direction of that pair, forces q>=Q. The
[four-chain budget and one-middle proof](PATTERN_II_NINE_SQUARE_CONTINUATION.md)
and [complete five-outsider capacity proof](BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md)
cover every placement. New [downward](DOWNWARD_THREE_SQUARE_CAP_HAND_PROOF.md)
and [upward](UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md) physical cap
inequalities close the exceptional alternatives strictly even at Q.

For Pattern I, the [transverse grid proof](ONE_EXCEPTION_TRANSVERSE_GRID_HAND_PROOF.md)
closes the hard full grid. When both original heights are three, the
[rank continuation](PATTERN_I_NINE_SQUARE_CONTINUATION.md) leaves only a
duplicated middle rank in a three/four/two arrangement. The
[common-lower cap](PATTERN_I_COMMON_LOWER_CAP_HAND_PROOF.md) closes a full
range of exceptional separating directions. The
[complete upward-sign theorem](PATTERN_I_STEEP_UPWARD_HAND_PROOF.md),
[downward extension](PATTERN_I_DOWNWARD_OWNER_EXTENSION_HAND_PROOF.md),
and [steep downward bounds](PATTERN_I_STEEP_DOWNWARD_HAND_PROOF.md) now
close the remaining direction cases. The
[height-three synthesis](PATTERN_I_HEIGHT_THREE_COMPLETE_HAND_PROOF.md)
and both [fat-direction](PATTERN_I_ACTUAL_HEIGHT_FOUR_BRIDGE.md) and
[perpendicular](PATTERN_I_PERPENDICULAR_HEIGHT_FOUR_BRIDGE.md) height-four
bridges complete Pattern I.

**The entire [one-exception class](ONE_EXCEPTION_NINE_HAND_PROOF_2026_11_02.md)
is therefore proved:** every nine-square packing with an orthogonal cover
missing at most one pair satisfies the sharp bound. The unrestricted theorem
still needs a global caller or a proof for the remaining multiple-exception
geometry.

An exact [eight-square obstruction](END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md)
shows why a smaller subsystem cannot settle those patterns. An exact
[nine-square equality example](GLOBAL_GEOMETRIC_CONTINUATION.md) requires
at least three exceptional pairs for every choice of two directions.

None supplies the remaining unrestricted coverage argument. The fixed
positional tally remains 5,838 excluded and 2,077 open out of 7,915 roots;
the earlier archive-only 312 additional exclusions remain separately recorded.

All new proof evidence is hand-derived. Two permitted numerical direction
experiments were exploratory only; no proof programs, Lean, Lake, or CI ran.

