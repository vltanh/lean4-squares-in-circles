# Handoff: eight-square hand proof and Lean formalization

## 1. State of the work

The completed result is the sharp radius for **eight arbitrarily rotated
unit squares**, together with attainment and a necessary and sufficient
classification of every equality packing up to isometry and relabeling.
The canonical consolidated manuscript is
[UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md).
All mathematical gates in its dependency chain are closed. Its source
binding is
[UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json](UNRESTRICTED_EIGHT_SQUARE_HAND_MANIFEST.json),
which records 84 direct files, 15 completed component manifests, and an
empty pending-mathematical-gate list.

The last completed hand-proof assembly before this cleanup was commit
`2dfee8a55617ebd4b96a57f5167603dda2f1e54d` on `research/eight-proof`,
in PR #9 of `vltanh/lean4-squares-in-circles`. The squash preserves the
mathematical source files and adds the navigation, history, and
formalization plan. The [human-readable progress history](PROGRESS_HISTORY.md)
and [complete original commit export](PRE_SQUASH_COMMITS.json) identify all
650 original PR commits and their original times; the date of the squash
is not the date at which all those mathematical results were obtained.

The **production and formalization baseline** is current main commit
`089a1cb83aeb40eea802375c1f35d3301fda06a3`, which is 34 commits after
the historical PR base `35c72e0aa740b17f012584e625bd13367c9726ff`.
Keep this distinct from the historical hand-proof snapshot `2dfee8a`.
Take production Lean definitions and module interfaces from `089a1cb`;
take the frozen mathematical appendices from the completed hand-proof
snapshot. The final publication preserves the current base outside
`research/eight/` and the 985 original research files within that prefix.
The history records distinguish the historical base from the publication
base and retain the first squash as a separate packaging checkpoint.

The completed object is a **long tabular hand proof**. Continuous
geometric arguments reduce certain statements to supplied fixed rational
comparisons and one-variable polynomial tables with complete closed
covers. Exact replayers and independent reviews check those appendices.
The external programs, their successful exits, and the source manifests
are not additional geometric assumptions. There is no claim here that
the unrestricted eight-square theorem has been translated into Lean or
accepted by its kernel.

This handoff prepares that next task. It does not write or compile Lean,
run CI, or merge the PR. The stage contracts and acceptance gates are in
[LEAN_FORMALIZATION_ROADMAP.md](LEAN_FORMALIZATION_ROADMAP.md).

## 2. Exact theorem targets

Use squared radius \(q\). A packing consists of eight closed unit
squares with pairwise disjoint **open interiors**, contained in a closed
disk with arbitrary center. Translate the containing center to the origin;
boundary contacts remain allowed.

The formalized final package must contain all of the following results.

1. **Exact root selection.** There is one admissible simultaneous
   stationary zero \((q_*,u_*,t_*)\) of the radical/trigonometric system
   in main equations (1.1)–(1.3). The auxiliary variable \(v\) is the
   function determined on the stated positive-radical branch. The branch
   inequalities and stationary derivatives are part of this theorem.
2. **Unrestricted lower bound.** Every packing as above has
   \(R^2\ge q_*\).
3. **Attainment.** The explicit construction yields actual pairwise
   interior-disjoint squares in the radius-\(\sqrt{q_*}\) disk.
4. **Equality classification in both directions.** A packing attains
   \(q_*\) if and only if, after an isometry and relabeling, it belongs
   to the explicit five-parameter domain in main Section 12.
5. **Exact meaning of uniqueness.** The admissible stationary root,
   normalized five-anchor structure, and two exterior orientation groups
   are unique. A full five-dimensional box consists of noncongruent
   attaining packings, so isolated-pose uniqueness is false.

The decimal
\(3.91553413751747532652\) is the center of a proved rational
bracket, not the definition of \(q_*\). Keep the exact constants

\[
q_-=\frac{7831}{2000},\qquad
Q_1=\frac{1957767069}{500000000},\qquad
Q_0=\frac{9789}{2500},\qquad
q_-<q_*<Q_1<Q_0<4.
\]

The central-existence lemma uses the separate ceiling \(98/25\).
The positive-core, frame, and wrong-word results use \(Q_0\); the
candidate tables use \(Q_1\). Main Sections 1–4 specify the transfers.

## 3. Coordinates and interfaces to preserve

The seven cyclic exterior roles and quarter word are

\[
(H,G,A,B,T,D,E)=(0,1,2,3,4,5,6),\qquad
k=(0,1,0,1,0,1,1).
\]

The nominal quarter offsets relative to A's actual frame are
\((-1,-1,0,0,1,1,2)\). A canonical center has own-frame coordinates
\((a,-\sigma b)\), with \(a\ge b\ge0\), and signed tangent
\(u=\sigma b/a\). Each boundary state is independently core-boundary
or outer-boundary; no radial assignment is discarded.

For lifted frame errors \(d_i\), use exactly

\[
I=\{0,2,3,4,5\},\qquad S=\sum_{i\in I}|d_i|,
\qquad h(x)=\frac{|\sin x|+|\cos x|-1}{2}.
\]

The four original forward signed axes are numbered: 1, source \(+f\);
2, target \(+e\); 3, target \(+f\); 4, source \(-e\). Their explicit
margins are main equation (7.2). Preserve these original indices across
pair reversal; the charge belongs to the original cyclic edge.
The separating-axis theorem initially supplies eight signed alternatives.
The cap and backward-axis lemmas eliminate the other four before this
forward-axis model is used; every remaining feasible axis, including ties,
is covered.

The reflection normalization is \(i\mapsto5-i\pmod7\), which fixes
E, preserves the word, and permits \(u_E\le0\). After this choice, do
not introduce another reflection without proving how it acts on the
roles, frame lifts, tilt, and owner conventions.

The completed capture sequence is:

| Available input | New conclusion |
|---|---|
| Candidate word and E normalization | G lies in \((-4/5,-1/20)\) |
| G bounds | T lies in \((1/20,4/5)\) |
| G/T bounds | \(u_H>1/2\), \(u_D<-1/2\) |
| G/T bounds and E normalization | Coarse full-axis \(S<13/50\) |
| Coarse mismatch and tangent cuts; both A/B signs and all axes retained | \(S<1/10\) |
| Small mismatch | A/B signs and zero-quarter owners are available for later steps |
| \(S\le1/10\) and the stated next-table hypotheses | \(S<3/200\) |
| \(S\le3/200\) and the established sign/tangent domains | Other-quarter owners lie in \(\{3,4\}\) |
| Previous conclusions; all four mixed axes retained | \(S<1/1000\) |
| \(S\le1/1000\) | Mixed owners, tilt \(1/10<t<4/25\), and the arbitrary-center terminal |

The exact premises of each table, including whether a stronger available
cut is actually used, are in main Sections 7–10 and the corresponding
theorem file. This table summarizes dependency order rather than
replacing those premises.

The final cyclic owner sets are

\[
\{1,3\},\{1\},\{1,3\},\{3,4\},\{1,3\},\{3,4\},\{2\}.
\]

They exclude every forbidden feasible axis, including ties. This
all-axis conclusion is needed for the originally selected witness.

## 4. Interfaces most likely to cause a formalization error

### Original packing, relaxed neighbor cycle, and equality

Prove central existence and the positive core for the original packing,
while all pairwise nonoverlap conditions are present. Only afterward
retain the seven neighbor conditions. Nonneighbors may overlap in that
relaxed class; it is not an actual eight-square packing.

Before deformation, choose one genuinely feasible signed separating
witness on each original neighbor edge. Retain those choices. The first
boundary deformation preserves true frames, cyclic order, and the
selected witnesses. It need not preserve center rays or relative
tangents. The later radius expansion is a different operation and does
preserve rays and tangents.

Expansion proves feasibility of every initially feasible signed witness
as radius increases. The proof later recovers a particular lower-radius
cycle already known to be feasible. It never asserts arbitrary inward
monotonicity. At equality, it reapplies the stationary dual directly to
the original centers; equality of a deformed representative's centers
would not establish original-position rigidity.

### Shared labels, complete domains, and quantitative hypotheses

Choose one canonical sign, type, and arc label for each vertex, including
ties, and use that same label on both incident edges. The marker terms
telescope only with this shared choice. Cover every closed endpoint,
one-point interval, admissible sign, radial kind, and original axis.

Do not import a later sign or owner conclusion into an earlier table.
In particular, the \(13/50\to1/10\) table retains both A/B signs and
all four axes, and the \(3/200\to1/1000\) table retains all four axes
on each mixed edge. The latter table precedes mixed-owner and tilt
capture. A positive cyclic constant without the full pair theorem is not
a contraction proof.

For the signed-error tilt bound, the nonnegative edge-weight vector is
fixed before the error/owner disjunction. Its reduction to
\(1+5\cdot2\cdot2=21\) alternatives uses that common choice. Selecting
independent weights for the alternatives would change the proof.

### Root, terminal, and full equality

The exact family theorem establishes root existence and uniqueness within
the declared admissible branch. It does not initially assume that an
arbitrary packing belongs to that family. The unrestricted reduction and
terminal supply that structural implication.

The terminal retains arbitrary actual centers, a positive mismatch
reserve, the tilt square, and the five completed center squares. Its
slider projection bounds follow automatically. Do not replace this with
a local-center-neighborhood theorem or add an unproved slider-capture
hypothesis.

The equality family has free coordinates \((x,y,w,z,\eta)\), where
\(w=\tan(\theta/2)\) is the central orientation parameter, z is T's
height, and \(\eta\) is G's transverse coordinate. Retain the full
central quarter-turn interval, the two strict core inequalities, the two
slider ranges, and all seven central/exterior separating-axis maxima.
The full-dimensional box proves genuine freedom but is only a subset of
the complete necessary and sufficient domain.

The two independent whole-proof reviews explain these interfaces in
[UNRESTRICTED_EIGHT_HAND_DEPENDENCY_INDEPENDENT_AUDIT.md](UNRESTRICTED_EIGHT_HAND_DEPENDENCY_INDEPENDENT_AUDIT.md)
and
[UNRESTRICTED_EIGHT_ROOT_CORE_EQUALITY_INDEPENDENT_AUDIT.md](UNRESTRICTED_EIGHT_ROOT_CORE_EQUALITY_INDEPENDENT_AUDIT.md).

## 5. Reproducing the supplied arithmetic and assembly

Run these commands in the flat `research/eight` directory of the
repository checkout. The supplied Python checkers use Python 3; the exact
affine-row replayers invoke `node` and use integer/rational arithmetic.
They need no discovery optimizer. Some audit and assembly scripts rewrite
their deterministic reports, so use a disposable checkout when comparing
the supplied bytes with regenerated output.

First restore the ordered large inputs. These scripts check every part
and the reconstructed hash, and refuse to overwrite a differing input.

```sh
python3 restore_candidate_coarse_mismatch_hand_input.py
python3 restore_mismatch_026_to_01_hand_inputs.py
python3 restore_mismatch_015_to_001_hand_inputs.py
```

The final arithmetic interfaces and source assembly can then be checked:

```sh
python3 verify_unrestricted_eight_hand_interfaces.py
python3 assemble_unrestricted_eight_hand_proof.py
```

The first command checks displayed rational comparisons and finite word
steps. The second binds the exact reviewed sources and completed component
manifests; it does not re-expand every polynomial coefficient or prove a
continuous geometric lemma.

The four mismatch coefficient replays are:

```sh
python3 replay_candidate_coarse_mismatch_hand.py
python3 replay_mismatch_026_to_01_hand.py
python3 replay_mismatch_01_to_015_hand.py
python3 replay_mismatch_015_to_001_hand.py
```

Each uses a fixed supplied input, exact kernel, and compact records. The
replay checks the complete full-output hash, every compact polynomial
record, row counts, and the complete cover. Full outputs can be large;
the middle and final bundles document `--save-full` if they are needed.
A preparatory geometry-only report is not an accepted all-row replay.

The middle and final author/domain reviews are directly reproducible:

```sh
python3 audit_mismatch_026_to_01_hand_assembly.py
python3 audit_mismatch_026_to_01_independently.py
python3 audit_mismatch_015_to_001_hand_assembly.py
python3 audit_mismatch_015_to_001_independently.py
```

For the other components, follow the scripts and inputs bound by their
manifests. The complete-bundle notes are
[COARSE_MISMATCH_HAND_BUNDLE.md](COARSE_MISMATCH_HAND_BUNDLE.md),
[MISMATCH_026_TO_01_HAND_BUNDLE.md](MISMATCH_026_TO_01_HAND_BUNDLE.md), and
[MISMATCH_015_TO_001_HAND_BUNDLE.md](MISMATCH_015_TO_001_HAND_BUNDLE.md).
Keep every ordered part even when its reconstructed JSON is present in a
working directory. Preserve byte-exact inputs, including final newlines.

The frozen mathematical manifest is the selector for current dependencies.
Its 84 direct files are not the whole transitive file set: retain the
tables, parts, checkers, and reviews bound by every child manifest too.
Neither a document reading list nor this command list authorizes deletion
of those transitive sources.

## 6. Beginning Lean formalization

Follow [LEAN_FORMALIZATION_ROADMAP.md](LEAN_FORMALIZATION_ROADMAP.md).
Begin by inspecting the repository's existing geometric definitions and
completed earlier cases, fixing exact theorem interfaces and a module
dependency graph, and mapping every main-proof lemma to its source.
At this refreshed production baseline the pinned toolchain is
`leanprover/lean4:v4.35.0-rc3`, and the pinned mathlib revision is
`c55e6e786f49471c72fbddbec5415808896aec1e`. Preserve that baseline during
the initial interface inventory; an upgrade is a separate change.
The refreshed module map matters: the general separating-axis theorem is
`SquaresInCircles.SAT.separating_axes` in `Common/SeparatingAxes.lean`;
coordinate and chart transport is in `Common/Charts.lean`; angular-budget
infrastructure is in `Common/Arcs.lean`; and frame normalization and
diagonal reflection are in `Common/Frames.lean`. The existing `Packing`,
`normSq`, rotation-only `Congruent`, and `Optimum` meanings remain
in force. Use the roadmap's current module inventory instead of import
paths from the older proof snapshot.
Reuse a previous result only after checking that its units, open/closed
conventions, orientation quotient, and hypotheses match.

Formalize the generic scalar kernel once: rational polynomial evaluation,
Bernstein lower bounds, alternating trigonometric enclosures, radical
majorants, support reduction, and complete finite closed covers. Treat
the supplied table entries as data. Establish in Lean why accepted data
imply the geometric pair inequality; importing an external `PASS` or a
SHA-256 match as an axiom does not establish it.

The geometry/root/terminal work and the finite arithmetic infrastructure
can be assigned in parallel after their interfaces are fixed. Each stage
must state all hypotheses explicitly and expose the unresolved next-stage
contract without claiming the final theorem. Preserve arbitrary centers,
all orientations, and the equality converse through the module boundaries.

At the final stage, inspect the dependencies of the unrestricted lower
bound, attainment, and equality equivalence themselves. Every hand lemma
must have been discharged, including the real analytic and measure
arguments and the full fixed tables. Any compilation, CI, or axiom audit
should be reported as performed only when actually authorized and run.

The new roadmap and handoff are planning documents. They do not change
the meaning or proof status of the frozen mathematical sources, and they
do not themselves supply any Lean theorem.

## 7. Progress history and future checkpoints

The [complete history export](PRE_SQUASH_COMMITS.json) is the authoritative
record of the pre-squash PR commits, with a readable chronology in
[PROGRESS_HISTORY.md](PROGRESS_HISTORY.md). Preserve original author and committer timestamps
separately, along with full commit identifiers, parent identifiers, tree
identifiers, and messages. Original timestamps are recorded as provenance;
they are not retrospectively reconstructed from file modification times.
Use the history's ordering metadata for the commit graph and the original
timestamp strings for time displays.

For future formalization checkpoints, record the stage, theorem contract,
what was implemented, actual verification performed, remaining explicit
dependencies, and the resulting commit identifier and timestamp. Keep a
stage's completion time distinct from its first planning or implementation
commit. A later squash should append a new provenance record while
retaining this original history.
