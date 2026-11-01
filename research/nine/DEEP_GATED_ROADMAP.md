# n=9 — canonical roadmap v3: published checkpoints and sharp terminals

**Target:** q>=1105/256 for nine independently oriented, interior-disjoint unit
squares in a disk, all attaining configurations, then a complete hand/table proof.
**Status:** all three global deliverables OPEN. **Active: A.2.**
The same 15 registry entries and 7,915 canonical root IDs are retained.

| Deliverable | Status | Acceptance condition |
|---|---|---|
| A — global lower bound | OPEN | Every physical q<Q packing excluded |
| B — full equality classification | OPEN | Explicit necessary-and-sufficient families at q=Q |
| C — final hand/table manuscript | OPEN | Complete and independently checkable arguments for A and B |

## A — global lower bound

**A.0 — faithful model [SOURCE AVAILABLE].** The original unrestricted emitter
has nine independent frames, 36 corners and 36 weak pair separations. Its source
equivalence proof and attaining witness remain available. Final independent human
source audit is outstanding; no kernel verification is claimed.

**A.1 — global coverage [EXPLICIT COVER AVAILABLE].** Nineteen closed hexagons
cover the entire possible center disk. Their diameters are strictly below one,
so nine physical centers occupy distinct cells. There are 92,378 nine-cell
subsets and 7,915 canonical representatives under twelve actual disk symmetries.
Every root retains all continuous orientations and original physical predicates.

- **A.1a [SOURCE AVAILABLE]:** exact unrestricted representation and root emitter.
- **A.1b [PROVED SOURCE + ENUMERATION]:** explicit full root cover with fixed IDs.
- **A.1c [PROVED FOR THIS COVER]:** closed cells, overlapping boundaries, independent
  orientations, all weak contacts and degeneracies retained.

**A.2 — close every physical root [OPEN / ACTIVE].** The published coupled-
separator checkpoint supplies **5,838 excluded / 2,077 open** cases. It uses
247 additional cores, 401 proof nodes, 77 exhaustive splits and 8,777 propagation
rows, after retaining all previous square-pose and disk-support evidence. The
complete source and independent replay implementation are now in the branch.
The earlier local-only publication limitation is resolved for those sources.

Two distinct kinds of terminal are now available:

1. **Closed-Q exclusions:** the exact geometric graphs and the separate three-cell
   rational proof rule out entire specified domains even at q=Q.
2. **Sharp terminals retaining equality:** the neighborhood theorem and its wider
   vertical-slide extension prove q-Q>=V/256 plus positive anchor squares. They
   exclude q<Q while allowing genuine equality poses. The extension keeps the
   1/64 tilt bound and 1/8 horizontal/anchor tolerances, but permits internal
   middle-row vertical deviations [-1/8,11/16] and bottom-middle [-19/32,1/8].
   Its rational seven-row table and original-coordinate guard interface are supplied.

The new local theorem does NOT close an entire positional root by itself. The
missing global caller must cover all assignments by exclusions or by proved
sharp-terminal guards. Every split must preserve the original root linkage and
all boundary assignments. A failed or incomplete search never changes a root's
status. No completion percentage or uniform-ease claim is made.

**A.3 — complete global replay [OPEN].** The separate coupled verifier rebuilds
the full earlier dependency chain and all new graph edges/inferences. Its saved
complete partial-proof report is pinned by hashes. The new sharp verifier checks
two physical polynomial identities, four owner telescopes, 14 endpoint layers,
126 full six-tilt layers, equality controls and corruptions. The guarded emitter
is separately parsed and checked under common rotations/reflections, relabelings
and fixed cell assignments. These do not supply the still-missing global caller.
Final A.3 requires every original q<Q domain, not just all currently supplied
certificates. No separate human reviewer or Lean verification is claimed.

A closes only with the full physical exclusion and its soundness. The existing
exact attainer then establishes the sharp optimum.

### Methods are tools, not extra gate trees

The direct exact physical route remains primary. Structural/contact lemmas may
be imported only with a proved caller and compatible hypotheses. The unverified
two-direction draft is not used. No new mandatory stress proof or replacement
progress denominator is introduced. A method failure is not a theorem closure.

## B — complete equality classification

**B.1 [ROOT COVER SUPPLIED].** The same closed positional cover works at q=Q.
The known attaining root 7820 remains OPEN, as it must under closed-Q pruning.

**B.2 [OPEN].** Prove every equality configuration has one of the eventual
listed structures, with exact free-position/orientation ranges up to genuine
common symmetries and relabelings. The widened seven-square chart now has a
necessary local slide description; it is not asserted globally necessary.

**B.3 [OPEN].** Verify every listed global parameter family and prove no equality
packing is absent. The local converse for the seven-square chart does not classify
the additional two squares or replace this global obligation.

## C — complete hand/table proof

**C.1 [OPEN].** Local readable assets include the center-cover argument,
admissible-center support formula, coupled separator derivation, the ten-row
three-cell argument with a generated 1,600-row rational appendix, and the two
sharp neighborhood theorems with fourteen signed layers. The final manuscript
still requires the global caller, every remaining exclusion and all of B.

**C.2 [OPEN].** Independently audit all final geometric implications, exact
arithmetic and boundary cases. Separate implementations and finite regression
controls do not constitute a separate human reviewer. Lean, Lake and CI remain
deferred and are not extra active mathematical gates.

## Source reproduction

From `research/nine/computer_assisted/`:

```sh
python make_hex_cover.py
python make_square_pose_certificate.py
python make_disk_support_certificate.py
python make_coupled_separator_certificate.py
python verify_coupled_separator_certificate.py --negative-controls
python make_three_cell_table.py
python verify_three_cell_table.py --negative-controls
python render_three_cell_tables.py
python make_sharp_neighborhood_certificate.py
python verify_sharp_neighborhood_certificate.py --negative-controls
python make_wide_slide_certificate.py
python verify_wide_slide_certificate.py --negative-controls
python test_sharp_terminal_emitter.py
```

The graph implementations require NumPy with bounded integer arithmetic. The
small rational table and sharp-terminal checks require only the standard library.
The full generated forests/manifests/appendix are deterministic outputs, pinned
by the committed summaries and supplied in the conversation archives; they are
not asserted checked in as GitHub blobs. No exploratory graph cache is a trusted
input to the full verifier.

Current source publication: `d05959c` (original sharp chart), `d946146` (coupled
and three-cell checkpoint), `cd1ab86` (wider sharp chart and exact guard interface).
The authoritative machine-readable status is `gates/ACTIVE_ROADMAP.json`.
