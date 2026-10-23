# Eleven-square deep gated roadmap

**Scope:** unrestricted unit squares in a closed disk, including all weak
contacts and independent orientations. **Current phase:** hand mathematics;
no Lean. **Sharp radius and global equality classification:** OPEN.

Let q11 be the infimum of squared feasible radii. An exact feasible constant U
only gives q11 <= U. A proposed sharp constant Q becomes the target of a
separate universal lower-bound theorem. Do not substitute the public
`optimalRadius 11` placeholder, which is currently zero, for q11.

## Status and closure rules

**H** means a hand argument with the stated quantifiers is written and
reviewed; it does not mean Lean verification. **C** is a conditional hand
result. **OPEN** is a missing argument, **BLOCKED** an unmet predecessor, and
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
| G1.1 | Baseline q=5 and exact rational upper bound U=49013/10000 | H; exact arithmetic independently replayed |
| G1.2.a | Pinned published candidate and its evidentiary scope | H |
| G1.2.b–G1.4 | Exact record reconstruction and target isolation | OPEN |
| G2.1–G2.3 | Exhaustive raw finite owner/sign cover, degeneracies, normalization | H |
| G2.4 | Useful geometric reduction and exhaustive small terminal inventory | OPEN |
| G3.C1–C2 | Necessary common-coordinate rank classification | H |
| G3.C3 | Double-four-chain terminal excluded; 1105 residual masks | PARTIAL |
| G3.C4–C5 | Close and assemble all common-coordinate cases | OPEN |
| G3.O | Unrestricted oblique/core-plus-completion classification | OPEN |
| G4.1 | Generic weak stress identity with equality consequences | H; conditional on supplied weights |
| G4.2–G4.5 | Sharp whole-domain terminal certificates and full assembly | BLOCKED |
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
cells, not realizable geometric classes. G2.4 remains OPEN.

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

**Closed initial classification:** [coordinate rank cases](COORDINATE_RANK_CASES.md)
proves the rank injection and reduces 4296 masks to 1105. A square cannot
have ranks (4,4), and the first row and column cannot both be full.
Two disjoint parallel four-chains force q>=5, excluding
both rectangular grids and masks with two full rows or columns at q<=U<5.
The exact residual masks are in `RANK_MASKS.json`; they are necessary data,
not assertions of geometric feasibility. Every surviving geometric domain
remains an open sharp-bound obligation.

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
condition and equality consequences. No weights giving the sharp n=11
bound uniformly have been supplied; all sharp terminal obligations remain.

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
