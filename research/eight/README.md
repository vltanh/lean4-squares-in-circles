# Eight unit squares in a circle

## Start here

The current table-free hand proof is
[the unrestricted eight-square theorem](formalization/HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md).
It proves the sharp radius, attainment, and the complete equality family
for the original centers through continuous geometric and scalar arguments.
Use [its dependency roadmap](formalization/TABLE_FREE_GEOMETRIC_HAND_ROADMAP.md)
and [current handoff](formalization/HANDOFF_2026_10_20.md) to follow this
completed route. The
[five-corner model](formalization/EIGHT_SQUARE_FIVE_CORNER_MODEL.md)
defines the radius by a geometric minimum without a numerical bracket.
The [equality model](formalization/EIGHT_SQUARE_GEOMETRIC_EQUALITY_MODEL.md)
uses five fixed squares, two contact-line sliders, and the actual central
angle. Its exact constant and equality family agree
with the earlier proof below; its mathematical chain does not import the
old numerical lookup tables.

The new [geometric Lean source draft](formalization/LEAN_GEOMETRIC_MODEL_DRAFT.md)
formalizes the model, its selection, the full equality family, and the
original-center assembly at the exact radius. The public eighth-case
definitions now use that model. The source is uncompiled and its concrete
global-entry implementation still uses the existing capture machinery;
the report separates this dependency from the table-free hand proof.

## Earlier tabular manuscript and provenance

The sharp-radius hand proof and the complete equality classification are
assembled in
[UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md).
That manuscript is the earlier consolidated tabular proof. Sections 1–12 join
the continuous geometric arguments to the necessary fixed rational tables
and include both directions of the equality classification. Section 13
records the complete gate ledger.

Every packing of eight closed unit squares with pairwise disjoint open
interiors, with arbitrary orientations and positions, has containing
radius at least \(R_*=\sqrt{q_*}\), and this radius is attained. The exact
constant is the unique admissible stationary zero defined in Section 1;
its proved bracket is

\[
3.91553413751747532652-2\cdot10^{-16}
<q_*<
3.91553413751747532652+10^{-16}.
\]

After an isometry and relabeling, five exterior anchors and the two
exterior orientation groups are fixed. Two exterior translation sliders
and the central square's two translations and rotation give the full
equality family. Section 12 supplies an explicit necessary and sufficient
domain for these five parameters and a full-dimensional box of
noncongruent packings. The uniqueness theorem concerns the stationary
root, rigid structure, and complete family; it does not assert one
isolated optimal packing.

**All mathematical gates in this hand-proof dependency chain are closed.
Lean formalization of this completed chain is a separate, staged task.**
The supplied proof is a long tabular hand proof: its fixed rational
polynomial tables are mathematical appendices. Source manifests and
successful checker executions record and reproduce that material; they
do not replace the continuous arguments.

## Reading and handoff

| Purpose | Document |
|---|---|
| Read the complete argument in proof order | [UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md) |
| See exactly what equality and uniqueness mean | [COMPLETE_EQUALITY_PARAMETER_DOMAIN.md](COMPLETE_EQUALITY_PARAMETER_DOMAIN.md) |
| Resume the work with its conventions, dependency boundaries, and reproduction commands | [HANDOFF.md](HANDOFF.md) |
| Implement the proof in Lean in bounded stages | [LEAN_FORMALIZATION_ROADMAP.md](LEAN_FORMALIZATION_ROADMAP.md) |
| Inspect the completed hand gates | [GATED_ROADMAP_2026_10_16.md](GATED_ROADMAP_2026_10_16.md) |
| Identify the exact reviewed mathematical sources | [UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json](UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json) |
| Read dated progress before the squash | [PROGRESS_HISTORY.md](PROGRESS_HISTORY.md) |
| Recover the complete original commit metadata | [PRE_SQUASH_COMMITS.json](PRE_SQUASH_COMMITS.json) |

Start with the main manuscript. Follow its appendix links at the first
lemma whose details you want to inspect. For formalization, read the
handoff and the stage roadmap before choosing a component.

## Proof dependency groups

The final manifest binds 84 direct source files and 15 completed component
manifests. The component manifests bind further tables, kernels, and
independent reviews. The following table is a reading map, not a reduced
list of files sufficient to reproduce the whole proof.

| Main sections | Mathematical role | Principal appendices or binding |
|---|---|---|
| 1 | Exact root, admissibility, family uniqueness, and sharp bracket | [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md); [HUMAN_SHARP_CEILING_BRACKET.md](HUMAN_SHARP_CEILING_BRACKET.md) |
| 2 | Central square and closed radius-\(1/12\) disk in its open interior | [HUMAN_GLOBAL_GEOMETRY_CLOSURE.md](HUMAN_GLOBAL_GEOMETRY_CLOSURE.md); [HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md](HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md) |
| 3–4 | Neighbor-cycle boundary reduction and fixed-witness radius transfer | [CYCLIC_RADIAL_BOUNDARY_REDUCTION.md](CYCLIC_RADIAL_BOUNDARY_REDUCTION.md); [HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md](HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md) |
| 5 | Four-type pair bounds and global frame concentration | [FOUR_TYPE_HAND_COVERAGE_INVENTORY.md](FOUR_TYPE_HAND_COVERAGE_INVENTORY.md); [HAND_EXTERIOR_FRAME_CONCENTRATION.md](HAND_EXTERIOR_FRAME_CONCENTRATION.md) |
| 6 | Seven quarter words and exclusion of six | [COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md](COMMON_QUARTER_TABLE_AND_FOUR_WORD_EXCLUSIONS.md); [SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md](SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md); [WRONG_0011011_WHOLE_WORD_HAND_PROOF.md](WRONG_0011011_WHOLE_WORD_HAND_PROOF.md) |
| 7–8 | Candidate tangent exclusions and the common scalar support kernel | [CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md](CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md); [AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md](AFFINE_ARC_ONE_ANGLE_HAND_KERNEL.md) |
| 9 | Complete mismatch chain \(13/50\to1/10\to3/200\to1/1000\) | [COARSE_MISMATCH_HAND_BUNDLE.md](COARSE_MISMATCH_HAND_BUNDLE.md); [MISMATCH_026_TO_01_HAND_BUNDLE.md](MISMATCH_026_TO_01_HAND_BUNDLE.md); [MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md](MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md); [MISMATCH_015_TO_001_HAND_BUNDLE.md](MISMATCH_015_TO_001_HAND_BUNDLE.md) |
| 10 | Separator owners, tilt, and the arbitrary-center sharp terminal | [HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md](HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md); [HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md](HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md) |
| 11–12 | Unrestricted lower bound, original-position rigidity, and full equality converse | [EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md](EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md); [COMPLETE_EQUALITY_PARAMETER_DOMAIN.md](COMPLETE_EQUALITY_PARAMETER_DOMAIN.md) |

## Current proof and retained research history

Use the main manuscript and its final manifest to select current proof
dependencies. Earlier exploration, failed approaches, narrower conditional
results, and superseded computer-assisted routes remain in this directory
as research history. A historical filename or positive status by itself
does not make a file an input to the final hand theorem.

Some frozen appendices retain earlier conditional wording or headings
about then-open obligations. The main manuscript discharges those former
inputs explicitly and records the policy in its assembly-status section.
The frozen files remain byte-for-byte unchanged so their review bindings
continue to identify the same material. In particular, the current proof
does not import the earlier adaptive central-core subdivision, older
four-type interval certificate, radial-necklace exclusions, or 123-box
capture.

Large fixed inputs are retained as ordered parts when required. Their
restore scripts verify the individual pieces and the reconstructed
complete hashes. Use the bundle instructions linked above, or the
commands in [HANDOFF.md](HANDOFF.md), before replaying those tables.

The [progress history](PROGRESS_HISTORY.md) and
[complete commit export](PRE_SQUASH_COMMITS.json) preserve all 650
pre-squash PR commit identifiers, parent relationships, messages, and
original author/committer timestamps. The squash supplies a single
reviewable PR commit while those records retain the dated progress history.
