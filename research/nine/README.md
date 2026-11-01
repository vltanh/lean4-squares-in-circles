# n=9 — sharp nine-unit-square packing

**Global goal OPEN:** prove all nine independently oriented, interior-disjoint
unit squares inside a disk satisfy R²>=1105/256, then classify all equality
packings.

[Current proof status](PROGRESS.md) · [canonical roadmap](DEEP_GATED_ROADMAP.md)
· [current handoff](HANDOFF_A2_2026_11_01.md)

**Active gate: A.2.** Current method: hand proof, exact tables permitted;
mathematical scripts only for checking potential directions. No Lean/Lake/CI.

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
with all nine squares retained. The full family remains open.

An exact [eight-square obstruction](END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md)
shows why a smaller subsystem cannot settle those patterns. An exact
[nine-square equality example](GLOBAL_GEOMETRIC_CONTINUATION.md) requires
at least three exceptional pairs for every choice of two directions.

None supplies the remaining unrestricted coverage argument. The fixed
positional tally remains 5,838 excluded and 2,077 open out of 7,915 roots;
the earlier archive-only 312 additional exclusions remain separately recorded.
