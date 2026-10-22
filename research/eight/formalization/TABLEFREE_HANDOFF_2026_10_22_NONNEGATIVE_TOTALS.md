# PR #10 — verified remote checkpoint and handoff (2026-10-22)

**Start here in a new session.** This is the latest dated source-drafting
checkpoint; use it together with
[`TABLE_FREE_FORMALIZATION_PROGRESS.md`](TABLE_FREE_FORMALIZATION_PROGRESS.md)
and the [G0–G9 acceptance ledger](TABLEFREE_LEAN_CLOSURE_ROADMAP_2026_10_21.md).
Older handoffs and stale PR-body summaries are historical, not completion claims.

## 1. Repository, push verification, and hard boundary

- **Repository:** `vltanh/lean4-squares-in-circles`
- **PR:** [#10](https://github.com/vltanh/lean4-squares-in-circles/pull/10)
  (open draft; base `research/eight-proof`).
- **Head branch:** `formalize/eight-uncompiled-draft`.
- **Verified remote checkpoint before this handoff update:**
  `f3fcdb9472969928e41d4f1adaa115bac7fb3d80`.
- GitHub's compare endpoint confirms **eight consecutive commits** from
  `2e2cc04efc3621ae9316662c09203d878d50b13c` to
  `c70532faae2c03d1013ac15ac35dc8c58b8bfacc`, comprising seven
  Lean files listed below and the predecessor handoff document.
  Each file was also independently fetched on the remote branch.
- Two subsequent source repairs were pushed and confirmed by the contents
  API: `c6ba42612667edca35f887e1a0c7536187f8f2f6`
  and `f3fcdb9472969928e41d4f1adaa115bac7fb3d80`.
- This verification establishes that all **known GitHub submissions from
  the preceding drafting session** are present. There is no local Git
  checkout available in this continuation, so this is **not** a claim about
  unknown, unsaved changes in another environment.
- **Proof status:** uncompiled Lean draft. **Not a completed table-free
  formalization, not elaborated and not kernel-checked.** Do not run Lean,
  lake, tests, CI, native-kernel substitutions, or a whole-source audit
  during the source-first drafting phase unless the user changes direction.
  Commit small increments with `[skip ci]`.

**Critical blocker:** the public n=8 proof still invokes
`GeometricModel.SharpAssembly.compatibility_source_entry`, which uses
`Candidate.capture` and generated dependencies. The unconditional
`TableFree.SharpSourceEntry` is **not proved**. A completed Markdown hand
argument or a finite local sector is not a substitute for that theorem.

## 2. What was actually drafted and pushed

### A. Selected nonnegative A and E totals, BT2, all TD choices

The source package starting at
`SquaresInCircles/Eight/TableFree/GlobalGANonnegativeTotalsData.lean`
includes four triangle/rectangle coefficient domains, twelve numerator
positivity certificates, radical/support inequalities, signed angle
concentration and original-force-sum comparisons. Its other files include
`GlobalGANonnegativeTotalsNegativeTD*.lean`, culminating in
`GlobalGANonnegativeTotalsNegativeTDSource.lean`.

Concrete **draft** exports (verify declaration arguments before calling):

- `GlobalGA.NonnegativeTotals.Source.actual_false`: nonnegative TD2 error.
- `GlobalGA.NonnegativeTotals.TD0.actual_false`: TD0 with either error sign.
- `GlobalGA.NonnegativeTotals.NegativeTD.Source.actual_false`: negative TD2 error.
- `GlobalGA.NonnegativeTotals.all_TD_false`: combines TD0 and both TD2 signs.
- `GlobalGA.NonnegativeTotals.frame_all_TD_false`: boundary-frame adapter.

The total constraints are on the **selected signed A/E primary pairs**,
not an assumption that each individual original angle is nonnegative.
All deductions are at the same original radius with weak physical owner
contacts. Source scripts are **not** a proof of their own elaboration.

### B. Mixed or both-negative A primary errors reduced to a single negative A

These **seven files are confirmed present** in
`SquaresInCircles/Eight/TableFree/`, in dependency order:

1. `GlobalGAMixedNegativeACaps.lean` — four exact upper/lower
   caps, including **upper constant `-1/2`**, on the unchanged G/B points.
2. `GlobalGAMixedNegativeACapSlopes.lean` — secant bounds,
   monotonicity and a common strictly positive gap-slope reserve.
3. `GlobalGAMixedNegativeAMotion.lean` — explicit `max`/`min`
   tangent paths for opposite-signed A errors.
4. `GlobalGANegativeANormalForm.lean` — same-state secondary-owner
   alternatives, nonnegative or single-negative terminal cases, and
   `NegativeANormalForm.Result`.
5. `GlobalGANegativeABothMotion.lean` — reflection of the actual
   `(B,A,G)` triple and the existing G5 negative-GA1 transport,
   for both negative A errors.
6. `GlobalGANegativeAReduction.lean` — original-neighbor
   reduction for the selected A owner pair.
7. `GlobalGANegativeACycle.lean` — `cycle_reduce`,
   nonincident feasibility, signed variation and strict spread on
   the replacement **necessary** cycle.

The governing hand proof is
[`HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md`](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md).
For negative GA3 and positive AB2 the A tangent is
`max(b,Lplus)`, ending at B's frame. For positive GA3 and negative AB2
it is `min(b,Uplus)`, ending at G's frame. When both are negative,
use the reflected G5 endpoint. The terminal aligned edge gains its
**actual** secondary witness; other points/frames and nonincident
weak inequalities are unchanged, and both variations do not increase.
The transported cycle need not be an original packing and must not be
subjected to unproved marker or global owner classification again.

**Two concrete fixes already committed:**

- `c6ba426`: `GlobalGANegativeANormalForm.lean` now directly imports
  `GlobalGAPairedECharge.lean` for `PairedE.selected`.
- `f3fcdb9`: `GlobalGAMixedNegativeAMotion.lean` no longer
  has the invalid, unused `min_le_iff.not.mpr` proof. The intended
  `le_min` bound remains.

**Remaining source reconciliation (not yet audited):** check the
`flat_core_negative_ga1_hg0_transport` application, reflected
`zeroFeasible` / `quarterFeasible` identities, and nested
`Result` / `CycleResult` interfaces against exact theorem signatures.
Do not infer correctness from the absence of `sorry` or `admit`.

## 3. Immediate next writing task — finish the negative-A matrix

The next real missing scalar coverage is a *single genuine negative
flat-core A primary with a nonnegative selected E total and TD2 with
positive error*. Transcribe and wire **both** existing hand proofs,
without changing their method:

1. [`HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md`](HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md)
   for `0 ≤ e ≤ s`. It uses the original negative-primary secant
   gain, signed E charge, exact half-angle estimate and two
   completed-square reserves, then compares to the reference
   negative-A stress.
2. [`HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md`](HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md)
   for `e ≥ s`. It uses concave `g_*`, small-total transfer,
   balanced signed concentration and four native TE/TC/RE/RC
   domains with twelve numerator families.

These ranges overlap at `e=s` and cover the entire nonnegative E
total when `s>0`. Preserve both actual A-owner alternatives:
negative GA3 / secondary AB0, and secondary GA2 / negative AB2,
including their respective strict tangent and angle cuts. Do not
replace the hand argument with a numerical mesh, generated
certificate, simpler special subclass, or an assumed scalar reserve.

Then connect these drafts to `NegativeANormalForm.cycle_reduce`,
`NonnegativeTotals.all_TD_false`, and the already-existing
paired-E negative/TD0 or nonpositive-TD2 sources where their **literal
hypotheses** match. The reduction's terminal A state is flat-core;
the original source geometry and original-owner admissibility must
still be justified separately when the final global theorem is built.
Only claim closure after a theorem dispatches all sign allocations
under the real original-cycle hypotheses.

## 4. Other global open work — do not mistake local cases for gates

In priority order after the immediate negative-A task:

- **G3/G4 signed residuals:** negative E total; paired negative
  core-E transports and short/long positive excess; joint negative A
  and core-E with positive TD2; DE3/EH1 alternatives. Use
  `HAND_G3_PAIRED_NEGATIVE_CORE_E_COMPLETE_TRANSPORT.md` and the
  `HAND_G3_CORE_E_*` / `HAND_G3_JOINT_NEGATIVE_A_CORE_E_*`
  documents as their exact mathematical sources.
- **Remaining BT owners:** positive BT3, including arbitrary TD0
  and nonnegative A/E totals, plus negative-A / negative-DE3 /
  negative-EH1 combinations. The sorted-D endpoint and two-angle
  hand proofs are **not** by themselves an original physical
  source theorem.
- **G2 word exclusion:** four zero-quarter outer representatives,
  four remaining mixed-quarter representatives, short-word gaps,
  and both original binary wrong-word aggregates.
- **G3 original owner classification:** finish global high-GA,
  BT and EH owner rigidity, all-high DE outer bridge, permitted
  owner ties and E radial/sign cases. Consult
  [`HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md`](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md).
  Do not assume an owner on the original cycle merely because a
  transport endpoint has that owner.
- **G4–G6 global closure:** join all G/T same-radius, both
  reflection and radial/sign alternatives to
  `UniversalHardSharp.hard_sharp` and
  `SourcePrimaryRecovery` / `OrderedSourceRecovery`,
  preserving the **unchanged original anchor centers** and their
  signed weak witnesses. The hard terminal is a drafted
  conditional theorem; proving its hypotheses is still essential.
- **G7/G8:** prove unconditional `SharpSourceEntry`; edit
  `SquaresInCircles/Eight/GeometricModel/SharpAssembly.lean`
  to remove `compatibility_source_entry` / `Candidate.capture`
  from the public dependency chain. Retain the original
  sharp-radius inequality, full five-parameter equality family
  and uniqueness of the least circle.
- **G9 (later):** only after a complete uncompiled source pass,
  static dependency/interface audit, then standard Lean/Mathlib
  kernel verification when separately authorized. Compilation
  performance is not the current objective.

**Gate state at this handoff:** G0 drafted, G1 drafted/integrated,
G2 partial, G3 partial, G4 partial, G5 hard terminal drafted,
G6 partial, G7 open, G8 geometric statement drafted but
compatibility-dependent, G9 deferred. No global gate is newly
marked closed by the seven A-reduction files.

## 5. How to continue efficiently and report truthfully

Read the **current GitHub PR head first**, followed by this file, the
live progress ledger, the G0–G9 roadmap and the named hand sources.
Write faithful uncompiled Lean transcriptions of remaining cases.
Commit/push each coherent source batch with `[skip ci]` and
verify the remote readback/head. Do not spend the drafting pass
optimizing algebra, refactoring old certificates or compiling.

For each case distinguish: hand lemma written; Lean body written;
connected to actual original witnesses; globally dispatched;
elaborated/kernel-checked. Only the first two occur automatically
when a local file is drafted. In particular, no shifted necessary
cycle, virtual comparison stress, unconstrained physical owner or
unproven anchor equality can be silently treated as original.

Before handing off again, update this dated handoff (or create
a later dated successor), `STATUS.md`, and the PR overview with the
verified last pushed SHA, each new original-cycle entry point,
and the **exact remaining unrestricted gaps**. Keep PR #10 draft
until the unconditional source theorem and permitted verification
are actually finished.
