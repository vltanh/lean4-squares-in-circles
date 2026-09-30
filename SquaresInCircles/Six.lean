import SquaresInCircles.Six.Construction
import SquaresInCircles.Six.Normalization.StrongCardinal
import SquaresInCircles.Six.Stress.CandidateRadius
import SquaresInCircles.Six.Stress.CandidateCardinal
import SquaresInCircles.Six.Stress.StrictSupport
import SquaresInCircles.Six.Classification.CandidateGraph
import SquaresInCircles.Six.Goals

/-!
# Six-square formalization development entry point

The isolated development imports the normalization source chain, its N25+
cardinal E/N refinement, the candidate-radius central box and support, the
candidate-radius opposite-cardinal budgets, the strict-support implication,
and the complete fixed-stress D-edge classification. The latter starts from
actual pairwise disjointness, orients SAT axes by the fixed pins, and proves
that every normalized packing reaches the common candidate D-edge graph
W-secondary / S-secondary.

The remaining work is the candidate-graph scalar closure, the survivor and
Pattern-8 equality chains, equality reconstruction, and the unrestricted
lower-bound and uniqueness endpoints. A generic stress theorem cannot
substitute for those concrete pattern proofs.

Compilation and kernel acceptance remain separate from source completion.
Source bodies and independently replayed arithmetic are recorded in
`research/six/lean/CHECKLIST.md`, `research/six/lean/DOWNSTREAM_CHECKLIST.md`
and `UPLOAD_AUDIT.md`. This module remains separate from the public
`SquaresInCircles` root.
-/
