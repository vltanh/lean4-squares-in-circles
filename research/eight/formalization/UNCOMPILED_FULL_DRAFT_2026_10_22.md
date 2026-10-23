# PR #10 — full uncompiled Lean hand-proof source

**Status:** complete **draft source** written and connected; **not compiled, not kernel-verified, not merged**. **Date:** October 22, 2026 (Chicago). **Branch:** \`formalize/eight-uncompiled-draft\`. **PR:** [#10](https://github.com/vltanh/lean4-squares-in-circles/pull/10).

This is the manifest for the complete source-level table-free proof of the unrestricted **n=8** unit-square-in-a-disk problem. It identifies the actual proof terms, imports and hand documents rather than pasting thousands of declarations into this report. The full Lean code is in the GitHub branch at the pinned revision below, and is also available in the normal GitHub archive of that revision.

**Pinned source snapshot:** [\`a80e002d61fdc9040cdd71924f710fecfe89c558\`](https://github.com/vltanh/lean4-squares-in-circles/tree/a80e002d61fdc9040cdd71924f710fecfe89c558).
**Full source archive:** [GitHub ZIP at the pinned revision](https://github.com/vltanh/lean4-squares-in-circles/archive/a80e002d61fdc9040cdd71924f710fecfe89c558.zip).
**Single Lean import for all final statements:**
\`\`\`lean
import SquaresInCircles.Eight.TableFree.UncompiledFullProof
\`\`\`

The new uncompiled [\`UncompiledFullProof.lean\`](../../SquaresInCircles/Eight/TableFree/UncompiledFullProof.lean) exposes all of the following **with source proof bodies** (no extra mathematical assumptions):

| Theorem | Statement / original-source meaning |
| --- | --- |
| \`TableFree.unrestricted_source_entry\` | An inhabitant of \`SharpSourceEntry\`; originally selected physical normal witnesses retained |
| \`TableFree.unrestricted_radius_lower_bound\` | Every packing into an arbitrary radius R at arbitrary center has \`FiveCorner.radius ≤ R\` |
| \`TableFree.unrestricted_squared_radius_lower_bound\` | At the original squared enclosing radius \`FiveCorner.radius^2 ≤ q\` |
| \`TableFree.unrestricted_sharp_attained\` | A packing exists at that radius |
| \`TableFree.unrestricted_equality_iff_parameters\` | Exact iff with five admissible parameters, both reflections and all weak contacts |
| \`TableFree.unrestricted_least_radius\` | Sharp radius is least among actually attainable radii |
| \`TableFree.unrestricted_equality_classified\` | Every sharp packing congruent, after relabeling, to a model |
| \`TableFree.unrestricted_equality_rigid\` | Explicit isometry and permutation preserving all square open/closed sets |
| \`TableFree.unrestricted_eight_complete\` | One unconditional conjunction of sharp lower bound, attainment, equality iff and least radius |

Here and throughout, a *proof body in a Lean file* is a drafted proof, **not** a successful elaboration or Lean kernel certification. The published result must not be described as formalized/verified until G9 is completed.

## 1. Canonical mathematical hand argument

- [Full geometric theorem, exact five-corner datum and five-parameter family](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md).
- [Global same-radius selected normal/primary owner theorem](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md).
- [Untouched original configuration, original selected-normal equality and radius pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md).
- [Current hierarchical proof closure and verification gates](TABLEFREE_EXECUTION_GATES_2026_10_22.md).
- [Original source-writing handoff](TABLEFREE_HANDOFF_CURRENT.md).

The hand argument is table-free **in the sense of eliminating the old affine owner-capture tables**. Some local exact inequality certificates and an independent generated equality-box certificate remain in the Lean library. This manifest makes no claim that all rational certificates have been eliminated.

## 2. Exact source pipeline, in dependency order

### G0 — sharp datum / stationary anchors / equality family

- \`SquaresInCircles/Eight/ExactFamily/Coordinates.lean\`, \`Stationary.lean\`, \`EqualityBox.lean\` — actual stationary coordinates and equality constraints.
- \`SquaresInCircles/Eight/GeometricModel/Basic.lean\`, \`FiveCornerSelection.lean\`, \`FiveCornerNominalTrial.lean\`, \`TwoHeightMinimum.lean\` — geometric five-anchor minimizer and radius.
- \`SquaresInCircles/Eight/GeometricModel/EqualityFamily.lean\`, \`EqualityCircle.lean\`, \`EqualityEquivalence.lean\` — admissible equality domain and converse.

### G1–G2 — original radius and quarter-word reduction

- \`SquaresInCircles/Eight/GlobalNormalization.lean\`, \`CycleActions.lean\`, \`GeometricModel/SharpBoundary.lean\` — original boundary representative and retained axes.
- \`SquaresInCircles/Eight/TableFree/FramePhysicalTransport.lean\` — physical normal/gap transport.
- \`SquaresInCircles/Eight/TableFree/QuarterDoubleExclusion.lean\`, \`ShortWordExclusion.lean\`, \`SecondWordExclusion.lean\`, \`QuarterWordSelection.lean\` — exhaustive wrong quarter-word exclusions and original candidate word.

### G3–G4 — true physical owner cases, same-q transports and terminal exclusion

- \`SquaresInCircles/Eight/TableFree/GlobalGASourceDomain.lean\` — original high-GA source with all seven actually retained witnesses.
- \`SquaresInCircles/Eight/TableFree/GlobalGANegativeANormalForm.lean\`, \`GlobalGACoreENormalForm.lean\` — same-radius necessary-cycle A/E reductions.
- \`SquaresInCircles/Eight/TableFree/GlobalGATransportTSecondary.lean\` — complete T transfer: actual BT2 or impossible positive BT3/TD0.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighBT2NegativeANormalForm.lean\` — A normalization without reconstituting a moved packing as original.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighBT2ReducedANegativeOuterE.lean\` and \`GlobalGAHighBT2ReducedANonnegativeOuterE.lean\` — both A total signs for original outer E.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighBT2CoreEFirst.lean\`, \`GlobalGAHighBT2CoreEFirstAllT.lean\` — E-first true-core case and full A/T sign partition, including joint negative.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighBT2Complete.lean\`: **\`high_GA_BT2_exclusion : HighGABT2Exclusion\`** — the top-level finite source contradiction.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighOwnerExit.lean\` — original GA physical normal allowed-owner reduction and source-to-sharp join.

All individual EH/DE, signed TD and original-frame certificates are imported through these source files. The 1,900+ \`TableFree\` Lean modules contain those lower-level exact inequalities, geometric signatures, transport statements and locality certificates. Their presence is not a substitute for G9 certification.

### G5–G7 — hard equality at *original* anchors, selected normals, source entry

- \`SquaresInCircles/Eight/TableFree/PairTerminalRecovery.lean\` — hard terminal / equality recovery.
- \`SquaresInCircles/Eight/TableFree/NormalizedSourceEntry.lean\` — original owner, stationary frame and retained selected-normal equality.
- \`SquaresInCircles/Eight/TableFree/SharpEntry.lean\` — precise \`SharpSourceEntry\` interface.
- \`SquaresInCircles/Eight/TableFree/GlobalGAHighSourceComplete.lean\`: **\`table_free_sharp_source_entry : SharpSourceEntry\`** and \`table_free_original_rigidity\`.

### G8 — unrestricted public theorem, equality, least-radius statement

- \`SquaresInCircles/Eight/GeometricModel/SharpAssembly.lean\` — source entry → original sharp rigidity and lower bound; the old compatibility capture was replaced.
- \`SquaresInCircles/Eight/GeometricModel/SharpEquality.lean\` — arbitrary center/labels and full equality classification.
- \`SquaresInCircles/Eight/GeometricModel/Theorem.lean\` — unrestricted radius bound, squared radius bound, precise admissible equality iff, rigidity, optimum and \`IsLeast\`.
- \`SquaresInCircles/Eight/TableFree/UncompiledFullProof.lean\` — single-import public theorem bundle from this source branch.
- \`SquaresInCircles.lean\` — the project-level \`optimal_radius\`, \`optimal_packings\`, \`optimal_packings_rigid\` surface imports \`Eight.GeometricModel.Theorem\`.

## 3. Draft trust boundary

The new original physical source proof **does not declare** \`HighGABT2Exclusion\` or \`SharpSourceEntry\` as axioms. It creates explicit proof bodies of both. It does not call \`Candidate.capture\` in the newly inspected main chain. However:

1. **No standard Lean/Mathlib compilation was attempted.** Every theorem above may still fail elaboration or contain type/namespace mismatches.
2. **The full transitive public import graph has not yet been exhaustively traversed.** The old \`Candidate.Capture.lean\` and \`Eight.Generated.AffineBudgets.lean\` still exist as *separate historical modules*. Source-level separation from them has been established only for inspected imports, not proven for all transitive modules.
3. **A generated equality certificate survives:** \`ExactFamily/Generated/EqualityBox.lean\`. It is distinct from the old affine owner-capture budget. Its standard-kernel trust and performance remain to be checked.
4. \`AxiomAudit.lean\` (at repository root) stages \`#print axioms\` commands for the complete source and final aggregate theorem. Those statements have not been executed.
5. The final squared-radius and original-center equality must be checked with all weak ties and source-vs-transported geometry; an uncompiled proof interface is not a mathematical verification.

## 4. G0–G9 acceptance ledger

| Gate | Current source status | Kernel status |
| --- | --- | --- |
| G0 stationary/equality parameter domain | Drafted, joined | Pending |
| G1 original-radius boundary | Drafted, joined | Pending |
| G2 seven quarter words | Drafted, joined | Pending |
| G3 original physical source/owner domain | Drafted, joined | Pending |
| G4 whole-domain high-GA/BT2 contradiction | Drafted, joined | Pending |
| G5 hard terminals and strict original anchor inequalities | Drafted, joined | Pending |
| G6 original initially selected normals/equality recovery | Drafted, joined | Pending |
| G7 unconditional \`SharpSourceEntry\` | Drafted, joined | Pending |
| G8 unrestricted bound/attainment/equality converse/rigidity | Drafted, joined; final aggregate entry added | Pending |
| G9 source/interface audit; Lean elaboration, kernel trust/dependencies | Source audit partial; kernel tasks deliberately deferred | **Not run** |

**Next authorized work without compiling:** manually inspect critical input/result signatures, find concrete stale theorem names or imported modules, check source-level weak tie completeness, and update this ledger with each proof correction. Do **not** trigger Lean/Lake/CI or claim formal verification.
