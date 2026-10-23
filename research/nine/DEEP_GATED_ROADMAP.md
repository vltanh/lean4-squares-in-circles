# n=9: deep gated roadmap to a complete unrestricted proof

**Version:** 2026-10-22 research continuation.  
**Branch:** `research/nine-tablefree-hand`; **PR:** #11 (draft).
**Status:** mathematics OPEN. This document is a *proof dependency contract*, not a promise that the remaining conjecture is true or presently solvable. In particular **no global sharp lower bound, complete global equality classification, Lean build, or kernel verification has been delivered**.

## A. Exact target and acceptance standard

Write
\[
Q:=1105/256,\qquad R_*:=\sqrt{1105}/16.
\]
The construction in [HAND_PROOF.md](HAND_PROOF.md) gives \(R_9\le R_*\).
The missing *unrestricted* assertion is

> **G4 / T9.** For every \(S:\mathrm{Fin}\,9\to\mathrm{UnitSquare}\), disk center \(o\) and \(R\ge0\), the original project predicate \(\mathrm{Packing}(S,o,R)\) implies \(R^2\ge Q\).

The separate equality theorem must classify **all** packings at \(R_*\) up to the existing \(\mathrm{Congruent}\) convention. It must not force nine parallel squares: the rigorous rotated upper-pair witness [NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md) contradicts such a claim.

### Status vocabulary

- **CLOSED (hand):** a written mathematical implication with all hypotheses stated, all cases covered, and no computation-as-oracle. It is **not** Lean-verified without a separate build.
- **CLOSED (negative):** a precise proposed reduction has been **disproved** by an exact counterexample; no downstream lemma may silently use it.
- **PARTIAL:** a proper, explicitly characterized subfamily is solved; no claim of global coverage.
- **OPEN:** no valid proof or exhaustive reduction yet.
- **BLOCKED:** logically requires an earlier OPEN item.
- **REJECTED:** a candidate statement is mathematically false. Retain the witness and design a different route.

A deep subgate is introduced **only when there is a mathematical invariant that divides the whole parent gate into a finite, fully quantified collection**. Do not create an endless tree of tighter rational boxes or tiny angle windows. Close a gate only after checking it against all known negative controls.

### Master critical path

```text
G0 Exact model, witness, negative controls           CLOSED (hand)
  |
G1 Exact terminal stress machinery                   CLOSED (hand)
  |    T1 long/short paired four-anchor
  |    T2 independently rotated 4+3
  |    T3 four-corner 3×3 grid
  |    T4 graph weak dual
  |
  +--> G2.C common-coordinate-separable branch       PARTIAL
  |       C0-C3 rank and four-chain extraction       CLOSED
  |       C4.1 shadow and inner-pair domination      CLOSED
  |       C4.2 zigzag branch                         CLOSED
  |       C4.3a signed 4+3-chain terminal            CLOSED
  |       C4.3b three-center-band grid terminal     CLOSED
  |       C4.3c five-complement x-chain ≤ 2          OPEN  <-- FIRST
  |       C4.4 whole C theorem                      BLOCKED
  |
  +--> G2.O oblique separators                       PARTIAL
  |       O0 exact no-global-frame counterexample    CLOSED (negative)
  |       O1 exact SAT formulation                   CLOSED
  |       O2 fixed-owner center-eliminating dual     CLOSED (hand)
  |       O3 finite meaningful owner-graph quotient  OPEN  <-- SECOND
  |       O4 orientation-uniform stresses/obstacles  OPEN
  |       O5 full oblique coverage                   BLOCKED
  |
  +--> G2.X exhaustiveness from original Packing     OPEN
           |
           +--> G4 unrestricted radius bound         BLOCKED
                    |
                    +--> G5 equality necessity       BLOCKED
                    +--> G5 equality converse        PARTIAL
                               |
                               +--> G6 hand audit     BLOCKED
                                       |
                                       +--> G7 Lean    NOT STARTED
                                               |
                                               +--> G8 public integration
```

**Note:** G2.C and G2.O overlap if their frame is changed; choose a frame when applying a branch. The *global dichotomy* “some common frame works / none works” is logically exhaustive, but a known equality packing is in the second branch. Never assert coordinate separability for all nine squares. The origin interior/boundary/exterior trichotomy (G2.P) is a cross-cutting optional organizing lemma, not an assumption of a central square.

---

## G0 — Exact semantics and negative controls [CLOSED, hand; audit later]

### G0.1 — Physical model

- **G0.1.1** Exact rotated unit-square support \(H_S(z)=\tfrac12(|z\cdot u_S|+|z\cdot v_S|)\).
- **G0.1.2** Disk containment equivalent to
  \(\|c_S\|^2+1/2+|c_S\cdot u_S|+|c_S\cdot v_S|\le q\).
- **G0.1.3** Pairwise disjoint open interiors equivalent to **one** true separating edge-normal axis from either square (SAT), with endpoints and equality handled.
- **G0.1.4** Any such pair has center distance \(\ge1\) (disjoint inscribed open radius-1/2 disks).
- **Exit:** precise lemmas directly matching `Geometry.lean` with no strict/closed-set confusion.

### G0.2 — Exact record construction

- **G0.2.1** 2–4–3 aligned construction gives \(q=Q\).
- **G0.2.2** A second exact equality candidate has two tilted upper squares, with oblique mutual separator.
- **G0.2.3** Verify every corner and pair separation as **exact** inequalities, not a picture.
- **Exit:** unrestricted upper bound plus precise equality witnesses (not global optimality).

### G0.3 — Rejected global normalizations

- **G0.3.1 CLOSED (negative):** an n=8-style unique central open square is false at n=9 equality.
- **G0.3.2 CLOSED (negative):** all nine squares need not share an orientation.
- **G0.3.3 CLOSED (negative):** a single common orthogonal pair of projection separators for *every* pair is false, even at the record radius.
- **G0.3.4 CLOSED (negative):** center radius + coordinate \(\ell^\infty\) spacing alone are too weak (see [CENTER_RELAXATION_COUNTEREXAMPLE.md](CENTER_RELAXATION_COUNTEREXAMPLE.md)).
- **G0.3.5 CLOSED (negative, hand):** even **nine axis-aligned** squares at (q=Q) may have **no horizontal stratification in any rotated frame**; [NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md) proves this using forced frame alignment and a chain of small height gaps.
- **Exit:** all proposed global reductions must be tested against these counterexamples before promotion.

---

## G1 — Short analytic terminal certificates [CLOSED, hand; independent audit later]

### G1.T1 — Long/short four-anchor stress

- **T1.1** Two long-span endpoints \(M_L,M_R\) satisfy
  \(x_{M_R}-x_{M_L}\ge2+h_{M_L}+h_{M_R}\).
- **T1.2** Two short-span endpoints \(B_L,B_R\) satisfy
  \(x_{B_R}-x_{B_L}\ge1+h_{B_L}+h_{B_R}\).
- **T1.3** Vertical separator condition:
  (a) common above/below seam, or
  (b) pairwise vertical gaps, possibly independently signed, under the signed tangent formulation.
- **T1.4** Exact tangent weights 23 and 9 give \(q\ge Q\); all orientations allowed. Equality pins the four corresponding boundary squares in each sign branch.
- **Sources:** [FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md), [PAIRED_FOUR_ANCHOR_STRESS.md](PAIRED_FOUR_ANCHOR_STRESS.md), [SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md).
- **Exit:** quantified implication only; does **not** assert every packing has these four anchors.

### G1.T2 — Orientation-stable 4+3 projection-row stress

- **T2.1** Exact one-square orientation penalty, valid across all tilt angles.
- **T2.2** Sharp arbitrary-rotation cap-row inequality, with two tangent vectors.
- **T2.3** 4-over-3 seam crossing at \(s=-7/16\), giving \(q\ge Q\).
- **T2.4** Equality is axis-aligned on the seven anchors; two extra squares need not align.
- **Source:** [ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md).

### G1.T3 — Four-corner 3×3 grid terminal

- **T3.1** Four horizontal/vertical span inequalities with one-unit reserves.
- **T3.2** Four diagonal tangent supports give \(q\ge9/2>Q\).
- **T3.3** Equality of this *conditional* theorem only at the rigid 3×3 outer corners.
- **Source:** [GRID_FOUR_CORNER_STRESS.md](GRID_FOUR_CORNER_STRESS.md).

### G1.T4 — Separator graph weak dual

- **T4.1** Fix square frames and choose one genuine SAT owner/axis for each selected pair.
- **T4.2** Disk corner constraints are convex in centers; chosen separator inequalities are linear.
- **T4.3** For chosen nonnegative multipliers, eliminate all center variables by a one-dimensional completed-square identity, obtaining explicit orientation-dependent lower bound.
- **T4.4** Allow zero circle-contact weights only if the corresponding net separator force vanishes.
- **Source:** [SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md).
- **Exit:** a valid **method**, not a sharp universal \(Q\)-certificate.

---

## G2.C — Coordinate-separable nine-square branch [PARTIAL]

Fix one orthonormal frame and suppose **each** pair is separated in at least one of its two coordinate projections. The square frames remain independent.

### G2.C0 — Rank and projection capacity [CLOSED]

- **C0.1** Define strict partial orders \(\prec_x,\prec_y\) from disjoint open projection intervals; check boundary equality.
- **C0.2** Associate longest-chain ranks \((r_x,r_y)\) to each of nine squares.
- **C0.3** Prove the rank-pair injection \(9\le ab\), where \(a,b\) are the longest horizontal and vertical chain sizes.
- **C0.4** Show five projection-separated unit squares cannot fit for \(q\le Q\); thus \(a,b\le4\).
- **C0.5** If \(a,b\le3\), the ranks occupy a complete 3×3 rectangle and imply G1.T3; contradiction.
- **Exit:** at least one chain of four, in one of the two frame directions.
- **Source:** [ORTHOGONAL_RANK_DICHOTOMY.md](ORTHOGONAL_RANK_DICHOTOMY.md).

### G2.C1 — Four-chain global shadow [CLOSED]

Choose a four-horizontal-projection chain \(M_1,\ldots,M_4\).

- **C1.1** Four intervals have total length \(\ge4\), while disk projection length \(2R<17/4\); all complementary gaps total \(<1/4\).
- **C1.2** Any fifth square has projected interval length \(\ge1\), so it meets at least one chain interval.
- **C1.3** Its incidence indices form a nonempty consecutive block of at most three.
- **C1.4** Stronger oblique-safe lemma: neither singleton \(\{1\}\) nor singleton \(\{4\}\) occurs; every extra square meets \(M_2\) or \(M_3\) in projection.
- **Exit:** 7 meaningful shadow-incidence blocks (not 7^5 cases to enumerate).
- **Sources:** [FOUR_CHAIN_SHADOW_BARRIER.md](FOUR_CHAIN_SHADOW_BARRIER.md), [INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md).

### G2.C2 — Remove large-zigzag chain geometry [CLOSED]

- **C2.1** Deduce uniform center-radius \(<61/40\) from the exact corner functional.
- **C2.2** Four-chain x centers lie in four disjoint narrow bands around \(-3/2,-1/2,1/2,3/2\).
- **C2.3** An inner-to-inner center height gap \(\ge2\) is the only possible large zigzag.
- **C2.4** In the coordinate-separable branch, prove top/bottom cap and three-region capacity bounds for **all five** other centers.
- **C2.5** Saturating those capacities contradicts pairwise coordinate separation. No remaining 4×3 zigzag leaf.
- **Exit:** four-chain vertical center diameter \(<2\) for the C branch.
- **Sources:** [FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md](FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md), [ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md).

### G2.C3 — Finish coherent-side patterns [PARTIAL; primary open branch]

- **C3.1 CLOSED:** If five extra squares contain a **disjoint horizontal projection chain of three**, apply [SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md) (endpoint interlocking + signed vertical stress). This closes the entire disjoint 4+3-chain branch.
- **C3.2 CLOSED:** If the nine squares form three projection chains of three in the prescribed upper/middle/lower center bands, apply [THREE_BAND_GRID_OBSTRUCTION.md](THREE_BAND_GRID_OBSTRUCTION.md).
- **C3.3 OPEN:** Complement \(E\) of five squares has horizontal projection-chain number \(\le2\). This is the **only residual C branch**.
  - **C3.3.a CLOSED (combinatorial):** By the interval-order chain/antichain theorem, partition \(E\) into at most **two** horizontally overlapping antichains; coordinate separability forces each antichain into a vertically projection-disjoint chain. One of these two stacks has at least three squares.
  - **C3.3.b OPEN (geometry):** Prove an exact disk/corner/support capacity restriction on every such two-stack complement **relative to the already fixed four-chain**, retaining orientation-dependent widths and all equality poses. **Test a perpendicular-frame 4+3-chain extraction first:** the exact equality witness proves such a switch can be necessary. Do not claim that a crossed four-chain by itself is impossible: [CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md](CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md) gives eight exact physical squares with two disjoint perpendicular four-chains at squared radius (17/4<Q).
  - **C3.3.c OPEN (end-to-end):** For **both** cardinality patterns (4,1) and (3,2), prove an exhaustive disjunction: (a) perpendicular **signed 4+3** chains, (b) another proved stress, or (c) impossibility at (q\le Q). The (3,2) branch is demonstrably **attained at equality**; exclude only unsupported subbranches, not the whole parent. Establish the equality zero-set for all surviving branches.
  - **C3.3.d CLOSED (negative, exact physical packing):** [TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md) constructs **nine genuine axis-aligned unit squares at exactly (q=Q)**, with a horizontal four-chain and a five-square complement of x-chain length precisely two. Therefore any assertion that the entire residual complement is *impossible at (q\le Q)* is FALSE. This witness has **disjoint perpendicular 4+3 chains**, so a frame-switch terminal stress explains equality. The correct goal is a **sharp lower bound with equality coverage**, not a blanket exclusion.
- **Exit for C3.3:** One quantified theorem (mathrm{Packing}_9\wedge q\le Q\wedgemathrm{CoordinateSeparable}\wedge a=4\wedge a(E)\le2\Rightarrow q=Q), with the known rational equality witness **included** in the resulting classification. A theorem ruling out this complete parent class would contradict the committed construction.
- **Do not:** expand into hundreds of layer/height configurations or solve one of infinitely many narrowed subclasses.

### G2.C4 — Assemble the entire coordinate-separable theorem [BLOCKED on C3.3]

- **C4.1** Choose a four-chain by C0.
- **C4.2** Rule out large zigzag by C2.
- **C4.3** If \(a(E)\ge3\), apply C3.1; otherwise apply the completed C3.3.
- **C4.4** Collect equality rigidities; do not infer that all nine frames coincide.
- **Exit:** no remaining coordinate-separable packing with \(q<Q\); every \(q=Q\) packing in this class has an explicit normal form or a fully specified finite union of normal forms.

---

## G2.O — Oblique-separator/global graph branch [PARTIAL; dominant open difficulty]

A fixed common orthogonal frame **need not** separate all pairs. This is true at equality, not merely at a pathological nearby configuration.

### G2.O0 — Validate that the branch is necessary [CLOSED (negative)]

- **O0.1** Exact tilted upper-square witness at \(q=Q\).
- **O0.2** Adjacent contacting aligned anchors force any globally separating perpendicular frame to be the anchor frame (up to signs/swaps).
- **O0.3** In that frame the two tilted upper squares overlap in **both** projection axes but are physically disjoint on their own oblique edge axis.
- **Exit:** never promote C4 to all packings via global frame selection.

### G2.O1 — The exact native SAT graph [CLOSED as framework]

- **O1.1** For each of 36 unordered pairs, choose a *genuine* separating normal among the two axes of each square, together with its directed sign.
- **O1.2** Keep equality/contact pairs (several separator choices may be valid); no generic-position assumption.
- **O1.3** Factor invariance under square relabeling, global rotation and the quarter-turn equality of square records/point sets.
- **Exit:** a finite combinatorial syntax encoding all original unrestricted packings, *without yet* claiming it yields few geometrically distinct cases.

### G2.O2 — Convex center elimination [CLOSED as framework]

- **O2.1** For each fixed owner graph and fixed side frames, encode exact center feasibility as convex inequalities.
- **O2.2** Establish weak dual with explicit node force vectors and nonnegative edge stresses.
- **O2.3** Remove center variables by exact scalar minimization; document zero-contact-weight force balance.
- **O2.4** Verify graph dual certificates are legitimate lower bounds (not necessarily strong-duality equalities).
- **Exit:** every future candidate stress reduces to finite orientation inequalities, with no center search as a proof premise.
- **Source:** [SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md).

### G2.O3 — Compress owner graphs *structurally* [OPEN]

- **O3.1 (graph invariant):** Find a planar/cyclic/interval or angular ordering for *arbitrary* nine squares and prove it from physical nonoverlap and containment; center-on-boundary configurations must be included.
- **O3.2 (stress-skeleton extraction):** Show every owner graph at \(q\le Q\) has either:
  (a) a small, balanced **positive-stress subgraph** supporting a \(Q\) lower bound;
  (b) a named exceptional graph family with an independent direct obstruction; or
  (c) an exact counterexample to the proposed classification.
- **O3.3 (finite coverage):** Prove the proposed graph families are **exhaustive up to symmetry and graph-reduction rules**. Merely counting a finite \(8^{36}\) SAT search does not pass.
- **O3.4 (no false anchored prerequisite):** If a graph lacks four long/short anchors, do not assert they can be created by deformation without proving nonoverlap and disk containment throughout.
- **Exit:** a short theorem \(\mathrm{Packing}_9(q\le Q)\Rightarrow\bigvee_{j=1}^k \mathrm{GraphClass}_j\), every \(\mathrm{GraphClass}_j\) defined geometrically, with a genuinely human-sized fixed \(k\). **This is the largest conceptual gap.**

### G2.O4 — Uniform orientation stresses [OPEN; requires O3 class inventory]

For each surviving graph class \(G_j\):
- **O4.1** Derive an explicit nonnegative edge/node multiplier assignment using graph balances (prefer support on at most a few boundary squares).
- **O4.2** Prove the dual lower bound \(\ge Q\) **for all allowed square orientations**, by geometry or a short algebraic SOS/convexity inequality—not a fine angular box mesh.
- **O4.3** If a graph class is infeasible at \(q\le Q\), give a short exact geometric contradiction rather than a numerical “optimizer failed.”
- **O4.4** Record the complete equality set of the dual conditions, including zero multipliers and all free non-anchor frames.
- **Exit:** every \(G_j\) has a mathematically checked sharp obstruction or is rigorously eliminated.

### G2.O5 — Global oblique closure [BLOCKED on O3/O4]

- **O5.1** Combine O3's exhaustive graph disjunction and O4's terminal inequalities.
- **O5.2** Ensure the coordinate-separable graph classes need not be handled twice; C4 may serve as one terminal.
- **O5.3** Verify the exact known oblique record witnesses are retained at \(q=Q\).
- **Exit:** unrestricted **sharp** lower bound, including equality contact patterns, from original \(\mathrm{Packing}\) only.

---

## G2.P — Disk-center incidence (cross-check and fallback) [OPEN as a proof route]

Every disk-center point lies in exactly one of:
- **P.I:** the open interior of exactly one square;
- **P.B:** no open interior, but the boundary of one or more squares;
- **P.E:** outside all nine closed squares.

### P.I subgates
- **P.I.1** Obtain a center-containing-square geometry bound **at \(Q>4\)**, not by importing n=8's \(q<4\) central-core lemma.
- **P.I.2** Establish a global exterior-square arc/support budget.
- **P.I.3** End at a T1–T3 stress or a new exact exclusion.
### P.B subgates
- **P.B.1** Treat zero-distance boundaries, including central seams/corners, without genericity.
- **P.B.2** Extract boundary supporting rays without asserting the unique record contact pattern.
- **P.B.3** Cover rotated free squares and invoke valid terminal stress.
### P.E subgates
- **P.E.1** Bound radial intersection arcs of squares that avoid the center.
- **P.E.2** Convert arc coverage into a rigorous global cyclic-order constraint.
- **P.E.3** Prove a terminal obstruction or route into O3 graphs.

**Status:** all P.I/P.B/P.E terminal implications OPEN. They are **not three extra independent gates that must each be proved** if O5 already handles everything; they are a fallback route to O3's global classification. Stop pursuing a P-branch if it merely classifies one small subclass of infinitely many cases.

---

## G2.X and G4 — Unrestricted radius theorem [BLOCKED]

### G2.X.1 — Coverage theorem
Write a theorem whose hypotheses are **only** the original Packing predicate and \(q\le Q\), whose conclusion is a proved terminal stress hypothesis or a proven impossible alternative. All freely oriented squares and all disk-center incidences must be covered.

### G2.X.2 — Strict-bound and boundary audit
Check \(q<Q\) and \(q=Q\) separately where necessary. A strict result for \(q<Q\) suffices for the lower bound but not the equality classification.

### G4.1 — Existence
Use G0.2's explicit exact nine-square construction to show the set of feasible squared radii contains \(Q\).

### G4.2 — Lower bound
Use G2.X and G1/G2.O stresses to exclude \(q<Q\) without stronger normalization assumptions.

### G4.3 — Statement match
Transfer from squared radius to radius \(R_*\ge0\) and match the `Optimum` / public `Packing` definitions.

**Exit:** theorem T9 is written as a complete readable hand proof, independent of execution of any certificate program.

---

## G5 — All equality packings [PARTIAL; global necessity BLOCKED]

### G5.0 — Proven conditional families [CLOSED, hand]
- **G5.0.1** [STRATIFIED_EQUALITY_FAMILY.md](STRATIFIED_EQUALITY_FAMILY.md) gives explicit three slider heights and two freely oriented upper squares, with exact disk/support inequalities.
- **G5.0.2** Exact nonstratified record witness proves the stratified family is not globally complete.
- **G5.0.3 CLOSED (conditional):** [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md) classifies **all** equality packings whose seven squares form two projection-separated 4+3 chains with corresponding endpoints vertically separated. Seven anchors become axis-aligned, three heights obey four exact separator inequalities, and two arbitrary freely rotated squares obey 15 actual-SAT pair tests. It contains the new nonstratified two-stack equality witness.
- **G5.0.4** Four-anchor stress equality pins the stressed boundary squares, but does not establish that *every* unrestricted packing has this skeleton.

### G5.1 — Equality skeleton necessity [OPEN]
- **G5.1.1** For every \(q=Q\) packing, apply G2.X's *equality* branches.
- **G5.1.2** Prove which stress constraints are necessarily saturated (no hidden assumptions that non-stressed squares are fixed).
- **G5.1.3** Classify different sign/reflection/owner-graph equality skeletons; merge genuinely equivalent descriptions.

### G5.2 — Free-parameter domain [OPEN]
- **G5.2.1** Store rigid anchors, exact slider variables and all nonanchor square frames/centers; permit oblique-only free-square separators.
- **G5.2.2** Replace the original 36 pairwise Packing checks with a modest explicit domain of corner containment and actual SAT projections relative to fixed anchors/free squares.
- **G5.2.3** Prove every parameter choice yields physical disjointness and disk containment (sufficiency).
- **G5.2.4** Prove every equality configuration appears in the parameter domain (necessity).

### G5.3 — Symmetry quotient [OPEN]
- **G5.3.1** Distinguish rotations/relabelings from reflections according to the actual `Congruent` predicate.
- **G5.3.2** Avoid claiming isolated uniqueness in the presence of nontrivial slider/rotation parameters.
- **Exit:** a necessary-and-sufficient equality model set for all n=9 optimal packings.

---

## G6 — Independent, table-free hand audit [BLOCKED on G4/G5]

- **G6.1** Consolidate the proof as one ordered manuscript, not a pile of independently solved conditionals.
- **G6.2** Audit every analytic inequality, algebraic factorization, sign, corner support and endpoint equality with a second derivation.
- **G6.3** Audit SAT logical disjunctions and the graph-case exhaustiveness proof independently.
- **G6.4** Verify all negative controls and equality witnesses.
- **G6.5** Record exact theorem-to-source dependencies, unresolved assumptions and source commits. No bound or “numerical experiment” is silently used as an axiom.
- **Exit:** a human reviewer can follow the full unrestricted theorem without executing any program.

## G7 — Lean kernel proof, Palomar standard [NOT STARTED]

- **G7.1** Introduce exact \(Q\), candidate radius and model/equality parameter types; no changes to the unrestricted square semantics.
- **G7.2** Formalize square support, exact corner-containment and separating-axis criteria.
- **G7.3** Formalize small terminal stress inequalities and equality zero-set lemmas.
- **G7.4** Formalize the *actual* global G2.X structural theorem, no unexplained axioms or overstrong normalization hypotheses.
- **G7.5** Prove sharp lower bound + attainment; prove full equality necessity/converse.
- **G7.6** Compile through standard Lean kernel/Mathlib workflow; inspect axioms, imports, transitive dependencies and a clean independent replay.
- **Exit:** kernel-checked public theorem with no `sorry`, `admit`, bespoke external proof oracle, native-kernel shortcuts, or unvalidated generated tables.

## G8 — Repo integration and handoff [NOT STARTED]

- **G8.1** Integrate n=9 into public optimal radius/packing registry and `Optimum` instances.
- **G8.2** Update `Challenge.lean` mirror, README, proof textbook, equality illustration and registry records.
- **G8.3** Verify no regression in n=1–8.
- **G8.4** Commit sources with timestamps and a consolidated handoff/coverage manifest; merge/close draft PR only after verification.
- **Exit:** full reproducible result, not just a proposed manuscript.

---

## B. Immediate execution queue (do not skip open gates)

**First research attack: G2.C3.3 (five-square two-stack complement).**

1. **Completed falsification:** an exact rational nine-square packing at (q=Q) lies in C3.3; it switches to two disjoint **vertical** projection chains of four and three. Never attempt to exclude the entire C3.3 branch including equality.
2. **Next:** prove a *frame-switch or other sharp stress* disjunction for the full (4,1) and (3,2) complement cardinality classes using actual square projection widths and circle corner supports.
3. **Counterexample control:** an exact eight-square cross already has disjoint horizontal and vertical four-chains; these chains alone are not forbidden. What the ninth square forces is essential.
4. **Closure:** prove (q\ge Q) uniformly, including exact classification of equality zero sets. Avoid angle meshes and accumulating single-pose exclusions.

**Second attack: G2.O3 graph invariant.**

1. Start with actual SAT owner normals; do not assume a global frame or central square.
2. Seek a cyclic/planar/interval graph invariant forcing a short positive-stress subgraph, allowing free-square oblique edges to have zero contact weights.
3. Falsify candidate graph classification against the known equality witnesses, *especially* the no-global-frame pair.
4. Only after graph coverage is proved, apply G1.T4 weak dual and search for orientation-uniform symbolic stresses.

### Decision points / pivot triggers

- If G2.C3.3 does not admit a whole-class obstruction using actual square widths, **pivot to G2.O3**; do not keep weakening a true terminal theorem into infinitely many special cases.
- If graph enumeration grows explosively, switch to a *geometric* invariant (radial/angular budget or a balanced separator force principle), not a finer SAT enumeration.
- If an exact 9-square packing with \(q<Q\) is found, the **target is false**; verify it by exact corner and SAT calculations and revise every downstream gate.
- Every completion claim must name its global quantifiers, its exact added assumptions (if any), and whether hand, Lean, or independently audited.

### Ledger at this commit

| Gate | Current state | Immediate blocker |
|---|---|---|
| G0 | CLOSED hand | Independent audit later |
| G1 | CLOSED hand (conditional terminals) | Global applicability |
| G2.C0–C2 | CLOSED hand | — |
| G2.C3.1–C3.2 | CLOSED hand | — |
| **G2.C3.3** | **OPEN; equality counterexample verified** | Frame-switch or other sharp all-two-stack bound |
| G2.C4 | BLOCKED | G2.C3.3 |
| G2.O0–O2 | CLOSED (negative/framework) | — |
| **G2.O3** | **OPEN** | Global structural graph coverage |
| **G2.O4–O5** | **OPEN/BLOCKED** | G2.O3 + uniform stresses |
| G2.X/G4 | BLOCKED | Coordinate/oblique closure |
| G5.0 | CLOSED hand (stratified and signed 4+3 conditional families) | — |
| G5.1–G5.3 | OPEN/BLOCKED | Equality global necessity |
| G6 | BLOCKED | G4/G5 |
| G7/G8 | NOT STARTED | G6 |

**Total progress must be assessed by how many *unrestricted* input configurations are now covered, not by how many narrow conditional lemmas are proved.**
