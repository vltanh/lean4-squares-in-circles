# Independent review of the eight-square proof handoff

## Scope and review state

Review date: **2026-10-18 01:17:20 UTC** (2026-10-17 in America/Chicago).
The production-baseline and document review was refreshed at
**2026-10-18 01:40:49 UTC** after current main was identified.

This review concerns faithful consolidation, preservation of the research
history during the requested squash, and the interfaces that a future Lean
formalization must prove. It is not a new replay of the large arithmetic
tables or a claim that the Lean development is complete.

The historical closed-proof checkpoint before the cleanup is:

| Object | Identity |
|---|---|
| Research branch | `research/eight-proof` |
| Closed-proof head | `2dfee8a55617ebd4b96a57f5167603dda2f1e54d` |
| Closed-proof tree | `9a10bbf3e79a6d6dc81303bf70538ac6a9ab1ea6` |
| Main manuscript SHA-256 | `a69a1d897fad1c144fd1931a09bb1e464cbaed9054d273151d37645225e277fc` |
| Main manifest SHA-256 | `19f3992f5ade2de3b5962e920997277a98b95194f818739e6ee55ea42dfb7833` |

The original research chain began after base commit
`35c72e0aa740b17f012584e625bd13367c9726ff`. That is the
**pre-squash history boundary**, not the target parent for the refreshed
publication. A subsequent PR/base refresh supplied current main
`089a1cb83aeb40eea802375c1f35d3301fda06a3`, 34 commits beyond the
historical base. The publishing process is preparing a replacement
one-commit squash on that current base. This review does not treat an
earlier provisional squash as the final delivered result.

There are consequently two different preservation comparisons. The 985
original `research/eight/` files must retain their old-head identities.
Files outside that prefix must agree with the **current publication
base**, including its newer Common-module refactor. The 1,530 old-head
entries and 545 old-base entries in `PRE_SQUASH_TREE.json` remain a
historical record; they are not instructions to restore outdated
nonresearch files over current main. History metadata must distinguish
`pre_squash_base` from the chosen publication base.

The main manifest records 84 source files, 15 completed component
manifests, and no pending mathematical gates. I independently compared
the bytes of all 84 locally located sources with the sizes and SHA-256
values in that manifest, using its assembler's explicit lookup order.
Every comparison passed. This establishes source identity; it does not
replace the continuous proofs or their finite arithmetic.

The complete manuscript already consolidates the unrestricted theorem
and equality classification. A new reader entrypoint and handoff should
organize access to that manuscript and its appendices while keeping the
reviewed files unchanged. In particular, some frozen notes retain
historical pending-capture language, and the main Section 9 heading still
says “with its remaining obligation exposed.” Its body and completed
ledger discharge that obligation. The existing main assembly explicitly
explains this historical wording. A new entrypoint should direct readers
to the current dependency graph rather than changing hash-bound sources.

## 1. Evidence required for the requested squash

The following conditions define a safe, reviewable result. They are
publication acceptance conditions, not assertions that the operation
has already happened.

### Preserve the original progress record

1. Capture the current PR base identity, current research head, their
   merge base, and the complete set of commits that the PR is replacing.
   Record the actual parent list of every commit. A date-sorted log alone
   does not represent merge ancestry.
2. Save each original full commit SHA, tree SHA, parent SHA list, full
   message, author identity and author timestamp, and committer identity
   and committer timestamp. Retain the source's timestamp strings
   exactly. If a GitHub API response normalizes them to UTC, identify
   that representation honestly rather than claiming that the raw Git
   object's timezone offset was recovered. Derived UTC and
   America/Chicago display values may be added, but must not replace
   the source records.
3. State the history boundary and ordering explicitly. Distinguish
   ancestry/topological order from chronological display order, because
   author dates and committer dates can differ or be nonmonotone.
4. Create and verify a durable archival Git reference resolving to the
   unsquashed head before rewriting the PR branch. The JSON/Markdown
   history makes progress searchable, while the reference preserves the
   actual original Git objects and their complete trees.
5. Bind the exported history with a hash and record its original head,
   count, time range, and capture time. Save both a machine-readable
   export and a readable progress table. The squash's new timestamp must
   be presented separately from those historical timestamps.

### Preserve both proof content and newer base changes

6. Choose the squash parent deliberately. To display one commit against
   the current target branch, use its verified current head as parent
   and apply the authorized research changes to that base. Do not copy an
   older whole-repository tree over a newer base tree.
7. Before updating the branch, compare all 985 original files under
   `research/eight/` with the unsquashed head. The reviewed manuscript, data parts,
   restorers, kernels, compact arithmetic, independent reviews, and
   manifests should remain byte-identical unless a separately described
   intentional edit is required.
8. Compare the proposed result against its current publication-base
   parent outside `research/eight/`. There should be no changes there.
   Use current-main entries for this comparison, not the historical
   545-entry base inventory. This verifies that newer unrelated base
   changes survive and that this cleanup has not changed Lean source,
   build configuration, or CI.
9. Preserve the complete recursive file dependencies of the component
   manifests. The 84 direct main-manifest entries are not the entire
   transitive appendix set. Some large JSON inputs are deliberately
   reconstructed from committed byte parts; all those parts, their
   part-manifests, and the exact restoration scripts are needed.
10. Resolve local basename duplicates according to the frozen manifests
    and exact hashes. A stale file with the same name elsewhere in this
    workspace must not silently replace the published source.

### Publish and verify the concrete result

11. Use the old research head as an expected value for the branch update
    and fail on concurrent changes. Do not overwrite an unexpected new
    head. Verify the archival reference and exported history first.
12. Verify the published commit has exactly one parent, that the parent
    is the intended target-base commit, that the PR now reports one
    commit, and that its resulting tree is the reviewed proposed tree.
13. Verify the published history files, consolidated entrypoint, handoff,
    and formalization roadmap against their prepared bytes. Check their
    relative links in the flat `research/eight/` publication layout.
14. Record the old head, archive reference, current base, squash head,
    squash author/committer dates, and proof-preservation result in the
    final publication report. Do not fabricate a self-referential hash
    inside the commit whose identity it purports to record.

The user has authorized squashing and preserving commit times. These
conditions make that authorized operation concrete; they do not impose
an additional approval round.

## 2. Mathematical contracts the Lean roadmap must preserve

### Unrestricted packing and normalization

The final theorem must quantify over eight closed unit squares with
arbitrary centers and frames and pairwise disjoint **open** interiors.
Touching is allowed. Its containing circle has an arbitrary center.
Translation to the origin and normalization by isometries and relabeling
must be proved, not inserted into the initial packing definition.

The central square and the positive radius-`1/12` core are consequences
at squared radius `Q0 = 9789/2500`. They are not hypotheses of the
unrestricted theorem. Arc measure must include all connected components;
finite boundary intersections have zero angular measure. The central
existence equality case is used to derive the contradiction.

### Signed axes, boundary reduction, and radius transfer

The basic SAT interface has eight signed alternatives. The geometry
first excludes the four backward alternatives, leaving the four precise
forward margins in main equation (7.2). This exclusion must hold when
several axes are feasible simultaneously.

Choose one feasible signed witness per original neighboring pair once,
and carry those physical witnesses through the proof. Moving a center
to a circle/core boundary preserves the true square frames and selected
witnesses. It need not preserve that center's ray, canonical tangent,
or canonical quarter-turn choice. Later expansion along fixed rays
preserves all of those additional angular quantities.

The boundary model must retain every one of the `2^7 = 128` independent
outer/core assignments. Both pieces of the core curve, including their
shared endpoint, and all canonical sign/axis ties are covered. The
relaxed neighbor cycle need not satisfy nonneighbor separation; an
impossibility for the larger class suffices.

The three radius levels are logically distinct:

| Constant | Exact value | Role |
|---|---:|---|
| `qMinus` | `7831/2000` | Safe lower containing radius for the transfer |
| `Q1` | `1957767069/500000000` | Candidate capture tables |
| `Q0` | `9789/2500` | Central core, coarse frames and quarter words |

The inequality `qMinus < qStar < Q1 < Q0 < 4` is proved from the
selected stationary root. At each initially feasible signed axis,
outward expansion preserves feasibility. To apply a `Q0` boundary
theorem at `Q1`, temporarily expand to `Q0` and reuse the unchanged
angular quantities. To finish at a lower radius, recover the particular
earlier representative already known to be feasible. No general inward
feasibility theorem is available or needed.

### Finite classifications and table soundness

The four-type marker theorem uses a single marker choice per vertex,
including overlapping type endpoints, so its two occurrences telescope.
The same rule applies to all later arc markers. A vertex cannot choose
different marker labels independently on its two incident edges.

The seven quarter classes are obtained from real frame lifts, cyclic
angle sum, and integer quarter offsets. Finite enumeration proves the
classification only after those geometric constraints are established.
The reflection `i ↦ 5-i mod 7` fixes E and normalizes its tangent sign;
it must be represented with its accompanying role and frame changes.

The generic arithmetic theorem must prove why each supplied row implies
its analytic pair inequality. It must include rational interval bounds,
radical majorants, trigonometric remainder bounds, affine support on
both radial curves, and Bernstein positivity on the full closed interval.
The finite cover theorem must then quantify over every required original
axis, signed angle, source/target arc, and closed endpoint.

All positive row conditions and all nonnegative premise conditions must
be distinguished correctly. A successful closed cover does not establish
the row inequalities. A successful row replay does not establish that
all required domains are covered. Both are necessary.

JSON parsing, input hashes, optimizer success, or an external `PASS`
report must never replace these Lean theorems. Supplied data may be
converted to finite Lean values by a generator, but the theorem must be
derived from a sound checker proved in Lean or from kernel-checkable
proof terms. A native-evaluation trust axiom is outside the intended
standard-axiom trust boundary.

### Exact order of the mismatch and owner implications

Use the original role order `(H,G,A,B,T,D,E)` and charged set
`I = {0,2,3,4,5}`. The total mismatch is
`S = ∑ i ∈ I, |d_i|`. The G→A and E→H mixed edges remain uncharged;
their individual differences can still range over `[-.7,.7]` when S
is small.

| Implication | Hypotheses that must not be strengthened prematurely |
|---|---|
| Tangent cuts | Both radial kinds and all four original forward axes |
| Initial `S < 13/50` | Full SAT; only the established G/T/E cuts |
| `13/50 → 1/10` | A/B still have both signs; all four original axes on every edge |
| Sign bootstrap | Applied only after `S ≤ 1/10` |
| `1/10 → 3/200` | Established sign ranges; all four original axes |
| Quarter-owner capture | Requires `S ≤ 3/200`; allows all mixed-axis choices |
| `3/200 → 1/1000` | Only the proved zero/quarter owners; all four axes on both mixed edges |
| Mixed-owner and tilt capture | Applied after `S ≤ 1/1000` |

The exact positive contraction reserves are part of the proof. They
close fixed thresholds rather than a limiting sequence of better
numerical bounds. The domain includes zero errors and every weak endpoint
needed when passing from a strict conclusion to a later weak premise.

The tilt proof fixes a common multiplier vector on each interval before
maximizing over its 21 signed-error/owner vertices. Independent multiplier
choices for those vertices would not prove the required maximum bound.
Both one-sided width slopes at cusps are included.

### Sharp terminal and equality for the original centers

The sharp terminal is an inequality for arbitrary admissible centers
under the proved frame and owner hypotheses. Its slider projection
bounds are automatic. It assumes no center closeness to the candidate,
no boundary equation for every original square, and no local slider
capture beyond the proved bounds.

Its conclusion retains all positive terms: the squared common tilt
error, the five weighted center-completion squares, and the positive
coefficient of S. These terms are needed for rigidity, not merely for
the scalar radius lower bound.

Equality first gives zero frame mismatch on the boundary representative.
These are statements about the unchanged original true frames. To fix
the original positions, apply the stationary dual again to the original
centers and the originally selected nonnegative separating gaps. The
reduction itself is not injective, so rigidity of its output alone does
not imply rigidity of the original packing.

The exact uniqueness statement is a unique admissible stationary root,
two exterior frame groups, five normalized fixed exterior anchors, and
the explicit necessary and sufficient five-parameter family. The two
exterior sliders and the central square's two translations plus rotation
are genuine freedoms. Formalize both directions of the family theorem
and a full injective box modulo isometries/relabeling. Do not replace
this with an assertion that an isolated optimal pose is unique.

The half-open central frame interval and strict core inequalities have
different purposes. Preserve the interval convention and the weak
exterior slider endpoints exactly; the final seven SAT inequalities
automatically exclude any impossible simultaneous endpoint cases.

## 3. Handoff acceptance

The new reader entrypoint should identify the frozen main manuscript as
the canonical hand theorem, list only its current proof dependency
route, and explain how to reach and restore the needed fixed tables.
Historical exploratory material may remain available with its status
clearly distinguished.

The formalization roadmap should provide named stages with explicit
input structures, theorem outputs, dependencies, and completion tests.
It should separate completed hand-proof status, unimplemented Lean
obligations, uncompiled drafts, and actual kernel-checked closure.
No Lean source or compilation is requested as part of this preparation.

The safest initial formalization work is to establish the unrestricted
packing/SAT interfaces and the generic exact-arithmetic soundness layer,
then test the representation on a small representative fixed table.
That pilot resolves proof-term size and trusted-evaluation issues before
the large frozen tables are converted. It must not invent a new search
procedure or change any frozen inequality.

This review's mathematical-interface findings are complete. Publication
conditions in Section 1 must be reported against the actual final Git
operation. The handoff-document review below concerns prepared source
files, not a remote branch update.

## 4. Review of the prepared handoff documents

The following final prepared files pass this review:

| File | Bytes | SHA-256 |
|---|---:|---|
| `README.md` | 7,231 | `b6a2f3cb5921a994b6b92de00c48e0697c320c2d85e0646bec558d16b1c9b809` |
| `HANDOFF.md` | 17,199 | `36198a938fa49196aec4998a4846d7b280207d3ae4279680055d82489f1395f9` |
| `LEAN_FORMALIZATION_ROADMAP.md` | 44,805 | `9ab0012845ca8c2ff2c3fcd77fe7b013003f9190acfaf5b76d485c63c78c410d` |

The README selects the unchanged canonical manuscript, maps Sections
1–12 to their required appendices, and identifies Section 13 as the
completed dependency ledger. It explains the retained historical wording
without changing any frozen proof source.

The handoff preserves the unrestricted theorem, exact root selection,
all radial and signed-axis cases, the radius-transfer order, automatic
slider terminal, original-position equality, and both directions of the
full five-parameter classification. Its restoration, replay, and audit
commands match the supplied script filenames and their inspected
interfaces. No large arithmetic replay was repeated for this editorial
review. A refreshed local link scan found no missing named destinations
in any of these three documents, including the two history files.
The schema-2 history and three-tree inventories receive their own
provenance audit, separate from this source/interface review. The
publishing process must still verify their final remote identities.

The roadmap supplies thirteen bounded formalization stages, F0–F12,
with theorem outputs, prerequisites and exit conditions. The ordered F7
and F8 subgates preserve the exact sign and axis dependencies. F9 now
states the precise open-core avoidance, `q ≤ Q0`, A/G frame and
canonical quarter-offset hypotheses of the arbitrary-center terminal.
F11 separates original-position necessity, the full parameter converse,
and noncongruence on the explicit box. F12 checks the actual public
theorems and their complete dependencies. A hash, external `PASS`, or
native-evaluation correctness axiom is never accepted as the missing
mathematical argument.

The reported toolchain and mathlib lock agree with the refreshed
`089a1cb` repository snapshot, whose supplied tree identity is
`af4976ff0b9f7b3cf471d44e9a41d4354cdaad54`. Its `Packing`,
`Congruent`, `Optimum`, and general two-square SAT interfaces were
inspected directly. The roadmap correctly points to
`SquaresInCircles.SAT.separating_axes` in `Common/SeparatingAxes.lean`,
coordinate transport in `Common/Charts.lean`, angular budgets in
`Common/Arcs.lean`, and normalization/reflection in `Common/Frames.lean`.
It does not propose importing the removed older module paths. It also
records the current module visibility and pinned-manifest conventions
without running their build or comparator commands. In particular, the roadmap
correctly identifies Euclidean `normSq` rather than the product norm,
preserves the existing rotation-based meaning of `Congruent`, includes
a reflected model family for the full isometry statement, reuses the
actual `CongruentOrDiagonal` and reflection-preservation facts, and uses
the family-valued `Optimum` interface. It also identifies the pure-definition
import dependency that must be settled before the public export is
extended. These are proposed implementation steps, not implemented
Lean declarations.

**Prepublication review result:** source identity and handoff/roadmap
interfaces pass. The actual history archive, archival Git reference,
single-commit branch update, final tree preservation and published links
remain the responsibility of the separate publication verification in
Section 1. This review does not assert that those remote operations have
already succeeded.
