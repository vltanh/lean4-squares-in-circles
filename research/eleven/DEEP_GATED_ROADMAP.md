# Eleven-square deep gated roadmap

**Scope:** unrestricted unit squares in a closed disk, including all weak
contacts and independent orientations. **Current phase:** hand mathematics;
no Lean. **Sharp radius and global equality classification:** OPEN.

Let q11 be the infimum of squared feasible radii. An exact feasible constant U
only gives q11 <= U. A proposed sharp constant Q becomes the target of a
separate universal lower-bound theorem. Do not substitute the public
`optimalRadius 11` placeholder, which is currently zero, for q11.

The current candidate target is Q=q_c, the unique root specified in
[the contact system](CANDIDATE_CONTACT_SYSTEM.md). Exact construction proves
q11<=q_c<49013/10000. Proving q11>=q_c is still the open global problem.
The larger rational U remains convenient for every coarse reduction below.
[The unconditional weighted-circle lower bound](arc_budget/UNIVERSAL_LOWER_BOUND.md)
now proves q11>9/2, so every minimizer lies in 9/2<q<=q_c.

## Status and closure rules

**H** means a hand argument with the stated quantifiers is written and
reviewed; it does not mean Lean verification. **C** flags a conditional
result; method/scope tags can combine as H/C or H/A. **A** is an exact
arithmetic certificate with a written soundness
argument and independent replay, also not kernel verification.
**OPEN** is a missing argument, **BLOCKED** an unmet predecessor, and
**DEFERRED** a later implementation phase. A parent closes only when all its
required children and its assembly implication close. Numerical evidence
cannot close an H gate. An arithmetic regression validates a formula or finite
enumeration only, not an unproved geometric reduction.

Every nonempty finite leaf must carry: its complete hypotheses and closed
parameter domain; the extraction map or parent cover theorem; separator
owner/sign/tie data; an exact exclusion or lower bound; its equality residue;
and a written proof reference. A leaf lacking a certificate stays in the
residual set. No assumption of parallel frames, a central square, a contact
cycle, connected stress on all eleven squares, or a unique equality pose is
allowed without a separate theorem.

## Current gate table

| Gate | Output | Status |
| --- | --- | --- |
| G0.1 | Pinned repository semantics and n=8 workflow audit | H |
| G0.2–G0.4 | Exact physical encoding, compact search domain, minimizer | H |
| G1.1 | Baseline q=5 and exact rational upper bound U=49013/10000 | H/A; independently replayed |
| G1.2.a | Pinned published candidate and its evidentiary scope | H |
| G1.2.b | Exact selected contact system, including the slider | H/C |
| G1.3 | Locally unique exact root and full feasible candidate family | A; independently reviewed |
| G1.4 | Candidate target q_c named; negative-control inventory | PARTIAL |
| G1.4.N1 | Exact family has no common separating coordinate frame | H/A |
| G2.1–G2.3 | Exhaustive raw finite owner/sign cover, degeneracies, normalization | H |
| G2.4.a | Unrestricted radial extraction: two core/ring counts and cyclic ring | H |
| G2.4.b–c | Reduced sharp terminal inventory inside these classes | OPEN |
| G3.C1–C2 | Necessary common-coordinate rank classification | H/C |
| G3.C3–C5 | Entire common-coordinate class excluded at q<=U | H/A; 6 cases, 32 nodes, 19 leaves |
| G3.O2 | Actual minimizer stress extraction, compact weights, small-component exclusion | H |
| G3.O2.S | Full-angle core has 5–11 bodies; contact stars and all four-body graphs excluded | H |
| G3.O3–O5 | Complete oblique contact classes and their physical completions | OPEN |
| G4.1 | Generic weak stress identity with equality consequences | H/C; supplied weights |
| G4.U | Unrestricted coarse lower bound q11>9/2 | H/A |
| G4.F | Fixed candidate frames plus fourteen separators: sharp bound and equality | H/A/C |
| G4.A | Full two-group-angle square with fourteen separators: sharp bound and equality | H/A/C; 507 rectangles |
| G4.L | Unrestricted local sharpness and complete local equality | H/A |
| G4.2–G4.5 | Remaining whole-domain certificates and global assembly | BLOCKED |
| G5 | Universal lower bound and attainment | BLOCKED |
| G6 | Complete necessary-and-sufficient equality family | BLOCKED |
| G7 | Independent full hand audit and proof handoff | BLOCKED |
| G8 | Lean translation and ordinary-kernel verification | DEFERRED |
| G9 | Public theorem, documentation, registry integration | DEFERRED |

## Dependency map

```text
G0 semantics/compactness ── G1 feasible candidates
          │                    │
          └────── G2 raw cover + radius window
                         │
                 G2.4 reduced geometric cover
                   ┌─────┴───────┐
             G3.C coordinate   G3.O oblique + completions
                   └─────┬───────┘
                     G4 all terminal bounds
                         │
                G5 lower bound + attainment
                         │
                G6 original equality + converse
                         │
                G7 independent hand audit
                         │
                G8 Lean ── G9 integration
```

G3.C may progress as a useful conditional branch while G2.4 is open. Its
completion never closes G3.O or G5 by itself. A universal invariant may
replace terminal enumeration, but it must cover all raw signatures and all
physical completions, and the dependency map must record that replacement.

## G0 Physical model and global existence

**G0.2–G0.4 closed:** [finite separator cover](FINITE_SEPARATOR_COVER.md),
Sections 1–5, proves exact physical equivalence, center bounds, closed
normalization and compact attainment. The exact upper bound supplies
nonemptiness. No previous n=9 theorem is used.

- **G0.1 H:** pin the definitions and study n=8's actual proof, not only its
  PR summary. Evidence: [source audit](N8_METHOD_AND_SOURCES.md).
- **G0.2:** write corners using centers c_i and frames u_i,v_i; prove full
  square containment iff the four corner inequalities hold. Derive the
  farthest-corner formula and true own-axis separating alternatives.
- **G0.3:** translate the disk center to zero, fix one frame by rotation,
  bound centers and frame coordinates on q<=U; retain reflections separately
  for the final repository congruence statement.
- **G0.4:** prove compactness using a finite union of closed separation
  conditions and produce a minimizer. Keep compact overlapping charts if a
  half-open orientation convention would break compactness.
- **Exit:** every physical packing in the window maps to the exact model,
  every model point is a physical packing, and minimization is attained.

## G1 Exact witnesses and target selection

**G1.2.b and G1.3 closed for the selected family:**
[the contact system](CANDIDATE_CONTACT_SYSTEM.md) specifies q_c exactly by
two radical equations and an isolating rational rectangle. A contraction
certificate proves existence and uniqueness there; ten vertex equalities,
fourteen pair equalities, two slider inequalities, and exact interval bounds
for the remaining 34 vertices and 39 pairs prove full packing feasibility.
[Independent review](CONTACT_ROOT_REVIEW.md) checks the domains, derivative
enclosures, Banach argument, contact algebra and all residual pairs. This
does not by itself prove optimality. The later G4.L theorem proves local
optimality; global optimality and global equality remain open.

**G1.4 target:** use Q=q_c as the candidate sharp target, with q_c in
4.901206412408144+[-10^-9,10^-9]. Global sharpness is explicitly G5.

**G1.4.N1 closed negative:** [no common separating frame](NO_COMMON_SEPARATING_FRAME.md)
proves the exact candidate family forces two nonorthogonal separator normals.
It therefore belongs to the oblique branch O. Rigid motions and relabeling
cannot make the common-coordinate branch exhaustive. Other proposed
normalizations must receive their own proof or negative control.

- **G1.1:** give an elementary exact eleven-square construction; audit all
  44 corners and 55 pair separations. Use its radius as the initial upper
  bound without asserting sharpness.
  **Closed:** [exact upper bound](EXACT_UPPER_BOUND.md) gives the elementary
  q=5 witness and a tighter rational witness at U=49013/10000. Its 11 frames,
  44 corners and 55 separator witnesses passed exact rational replay and an
  independent projection-interval check. The positive margins certify a
  feasible packing, not sharpness or equality at U.
- **G1.2.a:** pin the published candidate source and distinguish credited
  discovery, decimal radius, diagram, and exact coordinates.
  **Closed:** Friedman source commit `fdd8504` credits Kovacic, May 2006,
  and prints 2.21386+. It supplies a layout and decimal, not exact optimality.
- **G1.2.b:** reconstruct its contact equations, orientations, and genuine
  free parameters. A reconstruction must be checked against physical SAT.
- **G1.3.a:** solve the candidate equations exactly or specify algebraic
  roots with rational isolating intervals and uniqueness on their domain.
- **G1.3.b:** prove feasibility and boundary attainment exactly, including
  inactive pairs. A stationary point is not even an upper bound until this
  check succeeds.
- **G1.4:** choose a candidate Q only after G1.3; retain alternatives if
  equal or better witnesses appear. Build negative controls for every
  proposed rigidity or extraction shortcut.
- **Exit:** exact construction at Q. Global optimality remains G5.

## G2 Exhaustive finite cases

**G2.1–G2.3 closed:** [finite separator cover](FINITE_SEPARATOR_COVER.md),
Sections 1–4, gives 8^55 tagged closed quadratic cells. Sorting orientations
in a closed first-quadrant chart removes absolute-value sign ambiguity;
multiple valid pair owners stay in overlapping cells. This counts syntactic
cells, not realizable geometric classes.

**G2.4.a closed:** [the refined core/ring theorem](CORE_RING_TWO_CASES.md) gives
two exhaustive count rows: (3,8) and (4,7), at threshold 41/40. Auxiliary-circle arcs prove a genuine
cyclic ring; all core squares are strictly circle-unloaded. The six-core
case is excluded: its forced origin-containing square is pinned near zero,
and five neighboring centers cannot occupy four narrow regions.
A [weighted three-circle argument](arc_budget/WEIGHTED_ARC_EXCLUSION.md)
now excludes every case with at least five core centers. Its complete
continuous pose covers have 4790 nodes and 2037 accepted arc leaves;
independent arithmetic replay uses a different inverse-trigonometric
reduction and precision. The proof retains every orientation
and all 55 physical pairs, including ring nonneighbors. These are geometric
classes, not yet sharp terminals: G2.4.b–c remain open.

- **G2.1.a:** one of eight signed own axes per unordered pair gives a raw
  finite cover; prove both directions and retain all 55 pairs.
- **G2.1.b:** eliminate absolute values by sign cells or by all vertex
  support inequalities; record explicit polynomial degree and variable
  conventions. Cover zero dot products and multiple valid owners.
- **G2.2.a:** define a deterministic tie policy for bookkeeping or retain an
  overlapping closed cover. Do not require strict generic position.
- **G2.2.b:** justify any relabeling, quarter-turn, reflection, or cyclic
  quotient. Reflection reductions must restore both equality families.
- **G2.3:** prove the raw finite cover theorem on the compact G0 window.
  Distinguish syntactic count, realizable signatures, and certified leaves.
- **G2.4.a:** derive geometric restrictions valid for every packing in the
  window: projection chain lengths, central occupancy, loaded boundary
  structures, or other justified invariants.
- **G2.4.b:** partition using explicit predicates and prove every residual
  case is assigned. No picture-derived row/cycle assumption is admissible.
- **G2.4.c:** supply a finite reduced inventory with exact domains, an
  extraction proof, and a reproducible count or an analytic count proof.
- **Exit:** a useful complete cover, including degenerate and oblique cases.
  The raw 8^55 cover alone closes G2.3, not G2.4.

## G3 Classify geometry before closing leaves

### G3.C A common separating coordinate frame

**Entire G3.C closed at q<=U:** [the shrinking theorem](COORDINATE_SHRINKING_REDUCTION.md)
reduces every common-coordinate packing to axis-aligned squares in the same
disk. [The complete exclusion](AXIS_ALIGNED_EXCLUSION.md) covers all
axis-aligned packings with six fixed-cell cases and excludes every case by
exact interval arguments (32 nodes, 19 leaves), independently replayed.
Thus none of the old 1105 rank masks has a physical realization in this
radius window. There are no common-coordinate equality cases at q_c.

The old rank injection, corner exclusions and mask inventory remain as proved
intermediate reductions. [The case ledger](TERMINAL_CASES.md) records their
closure by the stronger theorem and the remaining unrestricted oblique work.

This is an added hypothesis: every pair's projection intervals separate on
one of two common perpendicular axes. Squares may still be independently
oriented. Prove separately whether such a frame exists in a proposed class.

- **C1:** chain-length bounds and injective pairs of longest-chain ranks.
- **C2:** enumerate rank-grid dimensions, occupancy masks, row/column
  profiles, and empty-rank exclusions. Record masks as necessary data only.
- **C3:** for each admissible profile derive sharp endpoint/width/support
  inequalities or subdivide into precisely defined geometric terminals.
- **C4:** close every coordinate terminal and preserve its equality cases.
- **C5:** assemble the conditional theorem; do not export its hypothesis
  into the unrestricted statement.

### G3.O No common separating coordinate frame

**O2 closed:** [minimizer stress extraction](SPARSE_MINIMIZER_STRESS.md)
proves normalized multipliers from a strict feasible first-order direction.
It gives at most 23 fixed-frame terms or, separately, 33 full-angle support
vertex atoms. All positive pairs are actual contacts. A connected positive
component has 4 to 11 squares, at least two circle-loaded bodies, no unloaded
leaf, and at most two internal squares in a straight transmission path.
[The elementary center bound](CENTER_SHELL_BOUND.md) excludes the
three-body component. All normalized multipliers are bounded, permitting
closed semialgebraic charts with physical contact witnesses.
[Independent review](SPARSE_STRESS_REVIEW.md) checks these claims.
The [small graph theorems](CLOSED_STRESS_GRAPH_FAMILIES.md) now exclude
spanning physical contact stars of any size and all four-body full-angle
cores. The [leaf-neighbor theorem](LEAF_NEIGHBOR_UNLOADED.md) uses angular
stationarity to make a stress leaf's neighbor strictly circle-unloaded; it
closes the previously missing loaded-internal four-path case. Thus the
full-angle component has 5–11 bodies, while a separately extracted
fixed-frame component retains the 4–11 bound.
[Independent review](SMALL_GRAPH_REVIEW.md) checks the graph classification
and both separator-owner cases.

A stress component is different from the radial core: it can include both
core and ring squares. Every omitted physical square remains quantified.
Sparsity and angular stationarity do not solve the contact classes.

- **O1:** preserve actual pair-owned oblique axes from G2.
- **O2:** if using minimizer stresses, prove constraint regularity, nonnegative
  multipliers, and exact dual identities before asserting sparse support.
- **O3:** distinguish translational stress, torque balance, the contact-point
  incidence graph, and the body graph. Planarity of one does not imply the
  others; a conic sparsity count is not a geometric classification.
- **O4:** classify cores together with every placement of the remaining
  physical squares. Include disconnected contacts, unloaded squares,
  multiply owned contacts, and zero multipliers.
- **O5:** prove each resulting graph/domain appears in the reduced inventory.
  If this cannot be done, keep an explicit residual class instead of adding
  disconnected conditional families indefinitely.
- **Exit:** every actual oblique packing/minimizer is covered by a terminal
  retaining all eleven squares or a proved completion constraint.

## G4 Whole-domain terminal certificates

**G4.1 generic identity closed:** Section 6 of
[the separator note](FINITE_SEPARATOR_COVER.md) gives the exact weak bound
for any supplied nonnegative weights, including the zero-circle-weight
condition and equality consequences. The [candidate stress](FIXED_ORIENTATION_STRESS.md) now supplies positive
weights giving the sharp bound for the fixed candidate frames and fourteen
specified separators, including full equality reconstruction. The
[local theorem](LOCAL_OPTIMALITY.md) retains both parallel-contact owners
and proves unrestricted local sharpness and equality. Both have an
[independent audit](CANDIDATE_STRESS_REVIEW.md). They close G4.F and G4.L.
The [full grouped-angle theorem](FULL_GROUP_ANGLE_CLASS.md) also closes G4.A:
arbitrary centers and both angles in the full closed first-quadrant square
satisfy the sharp bound under the fourteen selected separators. Its 507
closed rectangles include 355 strict dual tiles, 151 strict domain discards,
and one quantitatively solved neighborhood. Equality is exactly the known
slider family. [Independent review](FULL_ANGLE_COVER_REVIEW.md) audits the
assembly and both angle orders. Global capture or certificates for every
distant class remain open.

For each leaf T, prove Packing + T implies q>=Q, or show it impossible for
q<=Q. Fix frames only inside a conditional argument; then prove the bound
uniformly over their entire admitted angle domain.

- **G4.1:** derive transparent weighted support or completed-square identities.
- **G4.2:** prove nonnegativity of weights and denominator signs on the full
  domain, including boundary faces and coincident active constraints.
- **G4.3:** use exact root isolation or interval certificates only with a
  written soundness argument; a program's PASS is not the hand proof.
- **G4.4:** record all equality conditions, including coefficients that can
  vanish and therefore fail to force rigidity.
- **G4.5:** verify that the certified union equals the G2.4 inventory; list
  any remaining cases explicitly. One unresolved feasible leaf blocks G5.

## G5 Sharp radius

- **G5.1:** assemble a universal implication Packing_11 -> q>=Q, or exclude
  a global minimizer with q<Q using G0.4 and the complete terminal cover.
- **G5.2:** combine with G1 exact attainment and translate to radius sqrt(Q)
  with the nonnegative-radius condition.
- **G5.3:** check the statement contains no row, frame, graph, small-box, or
  numerical-success hypothesis. This is the unrestricted hand theorem.

## G6 All equality packings

- **G6.1:** apply the equality identities to original centers and frames.
- **G6.2:** recover every rigid component and every independent sliding,
  translation, and angular freedom; include cases with zero multipliers.
- **G6.3:** specify exact parameter domains with all pairwise nonoverlap and
  containment restrictions; prove their sufficiency as well as necessity.
- **G6.4:** account for relabelings, frame quarter turns, reflections and
  intersections between parameter charts. Do not assume an isolated pose.
- **G6.5:** compare with the construction and all retained negative controls.

## G7 Hand-proof handoff

- **G7.1:** independent audit of semantics, extraction, complete coverage,
  each analytic inequality, boundary cases, and original equality recovery.
- **G7.2:** reconcile theorem statements, dependency DAG, finite inventory,
  current gate table, progress history, and PR body.
- **G7.3:** create a source manifest with hashes and exact replay commands;
  distinguish mathematical proofs from regressions and exploratory files.
- **Exit:** a self-contained unrestricted hand proof ready to translate.

## G8 and G9 Later completion gates

**G8 is deferred under the current instruction not to write Lean.** Later
implementation should mirror proved interfaces, translate full-domain
certificates, compile with the pinned toolchain, audit axioms/import closure,
and independently check the final lower-bound and equality statements.
Source drafted, source joined, and kernel verified are separate statuses.

**G9** updates the public radius/model cases, theorem range, challenge,
documentation and registry only after verified n=11 proofs exist. Run the
repository's prescribed build, sanity, axiom and comparator checks there.

## Execution discipline

Close small mathematical gates in dependency order and commit each coherent
checkpoint with `[skip ci]`. Keep changes under `research/eleven/` during this
phase. Before a closure commit, review the exact quantifiers and all weak
ties; after it, record its SHA/time in the next ledger checkpoint. Keep the
PR draft while the unrestricted proof is open. Do not run Lean or promote
research claims into public theorem status.
