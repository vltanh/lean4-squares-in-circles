# n=9 — gated roadmap to a Palomar-portable Lean proof

**Status: execution roadmap, not a proof.** Prepared 2026-10-30 from PR #11 commit e14efe5bb9e5f9ddb9489bfe474664b11040fbbe. Canonical original inventory: **37/58 coarse cells closed; 2373/2513 fine gates checked**. No original checkbox changes are made by this roadmap. The unrestricted nine-square bound, all equality packings, the downstream G4.2.c selection audit, and n=9 Lean verification remain **OPEN**.

## 0. Non-negotiable deliverable and trust boundary

Prove for **nine actual, independently oriented, interior-disjoint unit squares in one closed disk**, in the repository's existing exact definition of Packing:

- **Lower bound:** every Packing S o R with S : Fin 9 → UnitSquare satisfies 1105/256 ≤ R².
- **Attainment:** construct a concrete nine-unit packing at R = sqrt(1105/256) with its complete pointwise containment and pairwise interior-disjointness proved.
- **Equality:** explicitly characterize ALL radius-optimal nine-unit packings, including possible continuous/sliding degrees of freedom, relabelling, rotation and reflection conventions. Do not posit uniqueness or a family without proof.
- **Correct statement surface:** expose the result in a small, independently auditable n=9 Challenge, with the same definitions and theorem types in the Solution; preserve the already registered n≤8 source/Challenge/Comparator intact.
- **Trust:** a finished proof is a Lean proof term that the pinned Lean kernel, fresh kernel replay and independent NanoDa kernel accept, with at most the standard axioms propext, Classical.choice, Quot.sound. No custom axiom, sorryAx, Lean.ofReduceBool, native_decide, untrusted external certificate oracle, or patched kernel.
- **Performance:** a finite, modular, human-auditable certificate suite rather than a million-line expansion; compile, export, and replay on the pinned toolchain and a fresh environment. It is insufficient merely to run a Python verifier, accept a proof manuscript, or compile a theorem stated under an unproved global reduction hypothesis.

A positive-stress **component of size six/seven/eight/nine** is NOT the number of squares packed; every configuration always has **nine physical squares**. An exclusion that requires selected stress, a true degree, physical circle masks or a canonical secondary minimizer must receive those hypotheses from the same global construction.

### Palomar acceptance checklist

- [ ] Independent n=9 Challenge (Mathlib/Lean allowed imports only) is short, uses the module system, and states precisely the unrestricted packing theorem plus the equality claim.
- [ ] Corresponding n=9 Solution imports the actual development and proves the matched declarations; separate comparator-nine configuration identifies exactly those declarations and the three permitted axioms.
- [ ] Every submitted Lean source begins with the required module header and stays below 10,000 lines; n=9 Challenge is below 1,000 lines and 100 KiB.
- [ ] Pinned lean-toolchain, Mathlib revision, lake-manifest.json, metadata and license are consistent; existing registered n≤8 entry is not silently changed.
- [ ] Axiom audit lists exactly the allowed standard axioms (or a subset) for both top-level theorems and critical certificate checkers. Avoid Lean.ofReduceBool via native_decide.
- [ ] Lake build, independent fresh Lean kernel replay, Comparator statement/solution comparison, full export and NanoDa replay all pass on one immutable pushed commit, with performance and source hashes recorded.
- [ ] Palomar formalization metadata accurately records AI/tool assistance, source provenance, limitations, independent mathematical review and **actual** machine-verification results; submission uses a full immutable SHA, not a branch name.

The repository already has n≤8 as a working precedent: README.md, Challenge.lean, SquaresInCircles/Geometry.lean, comparator.json, AxiomAudit.lean, formalization.yaml, and pinned Lake files. The n=9 Challenge should not import solution-only local code, and an existing n≤8 comparator success must not be cited as an n=9 success.

## 1. Dependency DAG and definition of a gate

Mathematical path:

    M0 (scope and candidate) --> M1 (common selected physical stress)
           --> M2 (finite planar/graph classification) --> M3 (all 58 original cells)
           --> M4 (sharp strict bound and radius endpoint) --> M5 (equality)

Formal path, starting concurrently rather than after all hand proofs:

    L0 (statement/geometry bridge) --> L1 (physical stress) --> L2 (graph cover)
    L0 --> L3 (exact-certificate checker)
    L1+L2+L3+M3 --> L4 (case proofs/assembled lower bound)
    L4+M5 --> L5 (attainment/equality)
    L4+L5 --> L6 (axiom/Comparator/NanoDa release)

Two distinct statuses MUST be recorded per mathematical item: (a) complete at original hand-proof scope, and (b) imported and kernel-checked in Lean. A separate status distinguishes (c) compared and independently replayed. This file's gates are **engineering/research milestones**, not new members of the canonical 2,513 fine-ID ledger.

### M0 — statement and exact model contract

- [ ] M0.1 Freeze target Q = (1105 : ℝ)/256, radius sqrt Q, exact nine-unit Packing predicate, and allowable congruence/equality symmetries.
- [ ] M0.2 Give an explicit feasible equality witness and prove it satisfies every containment/nonoverlap condition; never derive attainment from a mere lower bound.
- [ ] M0.3 Establish the strict contradiction window R² < Q, including the inherited lower-radius entry used by case lemmas, by an actually proved theorem about all nine squares.
- [ ] M0.4 Specify equality families only after the sharp chain exposes all equality conditions; keep q<Q exclusions separate from q=Q necessity.

### M1 — one compatible physical selection and stress reduction (global gate G4.2.c)

This is a **blocking mathematical gate** even though the existing later physical-stress manuscripts construct a common certificate at their stated scopes. Complete downstream compatibility and all caller dependencies still need audit/formal proof.

- [ ] M1.1 Compactness/existence of the intended radius-then-secondary-Phi minimizer, or a replacement optimization with explicitly proved equivalent hypotheses. Record the allowed continuous motions.
- [ ] M1.2 Construct one simultaneous nonnegative physical force-and-torque certificate at that same minimizer; encode individual corner forces, positive pair edges, all possible zero weights, physical shared-side means, and true full degrees.
- [ ] M1.3 Prove geometric contact/support and normal conventions, including singleton owners, shared length, weak endpoints and alternative physical mask cases. A corner with zero multiplier remains a physical corner.
- [ ] M1.4 Prove noncrossing/planarity and a single positive component with the **same** certificate; classify exterior physical squares separately from positive-graph vertices.
- [ ] M1.5 Prove simultaneous feasibility of all finite generic normal exclusions **before** extracting multipliers. Resolve G4.2.c's remaining downstream nonidentity, true-degree, graph/mask and caller audit; no post-extraction reselection.
- [ ] M1.6 Obtain a kernel-checkable global implication: every hypothetical counterexample to Q yields an original allowed case, with no extra premise beyond Packing and R²<Q.

### M2 — finite structural classification (one reusable kernel-checked table)

- [ ] M2.1 Define finite planar embedded positive graphs, block/articulation partitions, genuine leaves, root forests, load masks, selected ports and physical boundary masks as finite data plus geometric validity predicates.
- [ ] M2.2 Kernel-check graph enumeration, rotation/reflection orbit normalization, stabilizers, planarity and load constraints. The external Python enumerator is a generator/diagnostic ONLY.
- [ ] M2.3 Derive the original 58 coarse-case cover and all relevant fine alternatives as an exhaustiveness theorem; keep its original labels stable. Prove the reduction from actual selected packing to the finite data object.
- [ ] M2.4 Make every graph table row a proof obligation for the FULL original star, three or more actual completing squares as appropriate, and all continuous contact/mean/mask parameters.
- [ ] M2.5 Prove or import as kernel-checked general lemmas: two-positive-cut unloaded module classification, length/force-work bound, circle arc budgets, side-pocket capacity, genuine root/leaf capacity and motion-to-cap with weak endpoint treatment.
- [ ] M2.6 Distinguish entire simple-cycle results from an embedded marked cycle within a chorded block. A deleted edge must not silently delete an original force or turn a higher-degree vertex into a true-degree-two transmitter.

### M3.6 — CLOSE THE LAST SIX-BODY COARSE PARENT C1.6.b0 FIRST

**Current actual table input:** SIX_BODY_TABLE_FIRST_DRAFT_2026_10_30.md and scripts/n9_six_body_table.py. Five interior-pentagon graph parents have complete earlier hand closures but require Lean proofs. Exterior hexagon has nine chord-graph classes and **40** necessary graph/load orbits BEFORE two bare-cycle geometric exits; hence **38** table representatives after those exits (12 with three loads, 20 with four, 6 with five). The conservative table currently names **11** whole hand-closed rows, **two definitively open D02 rows**, and **25 UNRECONCILED** rows (which must not be called new open cases). The six five-load orbit closures already have named complete manuscripts.

- [ ] M3.6.0 Reconcile all 38 table rows with original existing checked/unchecked fine IDs and exact original-domain proof files. The 25 UNRECONCILED labels are evidence-status gaps, not 25 mathematical failures; do not change canonical checkboxes merely by matching a filename.
- [ ] M3.6.1 Reconfirm the five entire interior-pentagon graph parents and their closure dependencies, then formalize a single graph-family elimination instead of rereviewing each historical manuscript.
- [ ] M3.6.2 Formalize the nine exterior-hexagon chord classes, actual dihedral stabilizers, exact 38-orbit post-exit cover and face graph. Prove every orbit application transports the complete physical/force data.
- [ ] M3.6.3 Reuse the established shared geometric screens: bounded triangle capacity 0; bounded quadrilateral with at least three physical-boundary units capacity 0 in its radius window; direct loaded/loaded exterior pocket capacity 0. These are NECESSARY screens, not a free exterior-completion contradiction.
- [ ] M3.6.4 Close the four currently singled-out all-bounded-faces-empty completion rows: graph 03/load 0134, graph 02+03+35/load 1245, graph 02+04+24/load 135 and load 0135. Prove the JOINT capacity of the actual exterior pockets for all three physical completing squares and all zero-weight physical contacts.
- [ ] M3.6.5 **D02.L135 (unloaded N):** exhaust the Type II far-A-vertex side branch, Type II A-only side branch, and the two physical-two-corner V inner-face charts, including zero individual coefficients. Parallel V, physical-unique Type III, physical-unique Type I and both Type II diagonals have existing hand exits at their stated scopes.
- [ ] M3.6.6 **D02.L1345 (loaded N):** retain N's entire positive force and torque. Exhaust physical-unique Type I S/M1/M2/G (and reflections), remaining Type II side/owner branches, and physical-two V inner-face charts. NEVER use the unloaded transmitter equation on N.
- [ ] M3.6.7 Use the new necessary exact Type II both-unique inequality (T) and elimination equation (E) as a prototype certificate search. They are **filters**, not an established contradiction; retain the hub cubic, two circle equations, individual torques, singular matrix cases, positive denominators and full means.
- [ ] M3.6.8 Cover every other unreconciled exterior graph/load orbit with either an already complete original-domain source or an explicit newly verified exact inequality/physical completion certificate.
- [ ] M3.6.9 Produce ONE final literal six-body original-domain union theorem: all 38 exterior representatives and the five already-closed pentagon parents eliminated with three actual completing units. Only then check original C1.6.b0 and its genuinely completed fine gates; n=9 remains open.

**Research priority:** draft a complete D02 or joint-pocket certificate rather than review another isolated geometric inequality. A partially evaluated interval grid is not a proof. Full independent mathematical review happens at the complete original-row or union level, followed by kernel verification.

### M3.7 — seven-vertex positive components: 4 open coarse parents

- [ ] M3.7.1 C1.7.b0: finish one-/zero-RR no-long short C7, including the original U/T near-central constraints, all central and exterior completing-square contacts, shared means and two-physical-circle masks. The two-RR no-long family and sharp long-run family already have complete scoped hand exits.
- [ ] M3.7.2 C1.5.b2 and C1.6.b1: reuse five-/six-block root and two-exit module lemmas, but keep all actual positive chords/branch loads, two physical extras, and original forests.
- [ ] M3.7.3 C2.35.b0: prove complete two-block articulation pressure and both actual positive stars; a two-terminal network with more than two exits does NOT satisfy the two-exit theorem.
- [ ] M3.7.4 One original-domain join per coarse parent with all physical masks and both extra squares. No finite cycle result is applied after removing an unlicensed chord.

### M3.8 — eight-vertex positive components: 6 open coarse parents

- [ ] M3.8.1 One-block families: C1.6.b2, C1.7.b1, C1.8.b0. Apply the loaded-ear/branching extension of the arc and network inequalities; simple marked C8 exclusion does not exclude a chorded C8 block.
- [ ] M3.8.2 Two-block families: C2.35.b1, C2.36.b0, C2.45.b0. Prove original articulation-full-star separation and joint capacity including the ninth unit.
- [ ] M3.8.3 Assemble complete physical and polynomial case tables at each original parent scope; classify every zero stress/physical-contact option.

### M3.9 — nine-vertex positive components: 10 open coarse parents

- [ ] M3.9.1 One-block families: C1.6.b3, C1.7.b2, C1.8.b1, C1.9.b0. In C1.6.b3, the connected-private partition3 is hand-excluded; only disconnected clear-Q Types I/II remain, with their larger middle stars, optional chords and full loads. Do not reapply an exact B3 theorem to a larger original star.
- [ ] M3.9.2 Larger chorded/branching blocks: transfer true-degree and occupied-arc lemmas without incorrectly equating a chorded block with an entire simple cycle.
- [ ] M3.9.3 Two-block families: C2.35.b2, C2.36.b1, C2.37.b0, C2.45.b1, C2.46.b0, C2.55.b0. Finish generalized articulation pressure and complete multi-exit module analysis with all nine units in the component.
- [ ] M3.9.4 Complete all ten original parent joins, including every physical circle mask and equality possibility. The sharp seven-cycle four-anchor result alone is not a nine-square equality classification.

### M4 — unrestricted sharp inequality and equality

- [ ] M4.1 Chain M1 global extraction + M2 exhaustive original classification + all original M3.6–M3.9 exits to show there is **no** packing with R²<Q, with the inherited lower-radius entry justified.
- [ ] M4.2 Prove closed bound Q≤R² for all R≥0, including R²=Q as a legitimate endpoint; do not claim a strict-radius exclusion also excludes equality.
- [ ] M4.3 Prove a fully explicit nine-square equality witness (all 36 nonoverlap pairs and all relevant corners, or one quantified uniform proof).
- [ ] M4.4 Recover equality necessity from each *non-strict* inequality in the sharp chain and exhaust surviving geometry, not just four boundary anchor coordinates. State exactly the allowed continuous families, symmetries and reflections.
- [ ] M4.5 Prove equality sufficiency: each named family is a Packing at Q and each optimal Packing is congruent to some member.

## 2. Lean implementation path: proof terms, not an external oracle

### L0 — independent n=9 statement and existing geometry bridge

- [ ] L0.1 Add a separate NineChallenge.lean that repeats only the minimal existing Mathlib-based definitions needed by the statements, with the same definitional meaning as SquaresInCircles/Geometry.lean. Do not import the Solution module or unapproved local definitions into Challenge.
- [ ] L0.2 Expose in the Solution a theorem schematically of the form

      Nine.radius_sq_ge (S : Fin 9 → UnitSquare) (o : Point) (R : ℝ)
        (h : Packing S o R) : (1105 : ℝ)/256 ≤ R^2

  plus attained optimality and equality/classification theorems once their *actual* models are mathematically known. This is a declaration target, NOT compiled Lean code.
- [ ] L0.3 Add a separate comparator-nine.json and n=9 Solution module. Leave existing Challenge.lean/comparator.json for n≤8 untouched, including its stated n≤8 quantifier bound.
- [ ] L0.4 Use the same normSq, sub, openSquare, closedSquare, inDisk, Packing, and Congruent semantics; explicitly audit reflected models when Congruent itself allows rotations and relabelling but not reflections.

### L1 — physical geometry and global stress

- [ ] L1.1 Kernel-prove the square/frame arithmetic, support points, exact disk corner containment and algebraic separation characterization used by all manuscripts.
- [ ] L1.2 Formalize the compact minimizer, canonical secondary functional, allowed motions and contact supporting normals without custom axioms.
- [ ] L1.3 Formalize physical force/torque stationarity, nonnegative corner loads, shared-side application intervals, total-circle-load vs physical-boundary distinction.
- [ ] L1.4 Prove planar/common-certificate construction and G4.2.c simultaneous selection/caller theorem with exact original true degrees and masks.
- [ ] L1.5 Prove the kernel-checked reduction from an unrestricted nine-unit counterexample to one of the 58 original symbolic cases.

### L2 — graph/table enumeration and physical join

- [ ] L2.1 Represent six square indices as Fin 6, full packing indices as Fin 9, finite chord graphs/load sets and exact dihedral actions. Use a verified finite cover theorem, not a magic list produced by Python.
- [ ] L2.2 Prove the 40 necessary exterior-hexagon orbits and the two geometric bare-cycle exits; derive the 38-case current table with original-ID mapping.
- [ ] L2.3 Prove the physical face/pocket localization bridge: a whole extra is in a real region after allowing weak contact, not only in a combinatorial face name.
- [ ] L2.4 Formalize full graph/load/owner/mask/side-width refinements and merge covered orbits under exact relabelling.
- [ ] L2.5 Reuse one branch/cycle/articulation combinatorial lemma across component sizes 6–9.

### L3 — small reusable real-algebraic certificate checker

A Python/CAS script may **discover** witness coefficients, cover boxes and elimination identities. The Lean theorem must verify every finite step using exact rational arithmetic and standard proof terms; a script's assertion, float sampling, timeout or log is never a premise.

- [ ] L3.1 Define a normalized exact leaf: source original-case ID; full real-algebraic constraints; rational coordinate box; sign/equality target; witness polynomial identity or Bernstein/Farkas/SOS certificate; explicit assumptions and exclusions.
- [ ] L3.2 Formalize a **soundness theorem**: verified positive rational Bernstein coefficients imply the target polynomial is nonnegative on the exact closed box, or a verified algebraic identity plus assumed inequalities yields a contradiction. Use only Lean terms and mathematical identities.
- [ ] L3.3 Formalize exact box splitting and coverage of all original closed parameter domains, including equality faces and shared-mean endpoints. Check denominator positivity *before* field_simp; encode square roots by positive auxiliary variables and squared equations; trigonometry by algebraic half-angle variables with exact sign bounds.
- [ ] L3.4 Reduce repeated coefficients to shared DAG nodes and a few reusable small source lemmas, not generated millions of proof lines. Certifier may output rational data, but its validation must be kernel-replayed.
- [ ] L3.5 Put each certificate family in a small independent Lean module with a real, stated theorem and no hidden globally assumed compactness or selection hypotheses.
- [ ] L3.6 Check proof-term sizes, elaboration and replay cost as gates. If a full interval cover explodes, return to a human inequality eliminating a whole parameter or choose an SOS/linear-combination certificate; *do not* trade trust for speed.
- [ ] L3.7 Proof-test equality/boundary cases separately when strict certificates do not cover them. Make the certificate library self-contained enough for a second independent kernel.

Permitted tactics such as ring, norm_num, positivity, linarith, nlinarith and ordinary decide are *proof generators* whose output is kernel checked. No native_decide, unsafe escape hatch, external process result cast to a theorem, custom axiom, or imported black-box infeasibility answer.

### L4 — proof modules ordered by geometry, then case size

- [ ] L4.1 Build reusable modules for original physical support/arc/circle and all nine actual units.
- [ ] L4.2 Translate the reconciled six-body table, the complete D02 feature exhaustions and exact certificates, and prove the C1.6.b0 elimination statement in Lean.
- [ ] L4.3 Formalize original completed six-body parents and all established 3–5-component reductions rather than importing them as hypotheses.
- [ ] L4.4 Formalize the complete seven-body, eight-body and nine-body original parents, reusing L1–L3 lemmas. Check every parent independently by import/build.
- [ ] L4.5 Assemble the complete 58-case upper-level proof into one unrestricted theorem with no case-table gaps.

### L5 — construction/equality and portable release

- [ ] L5.1 Implement the explicit nine-unit optimal models only once equality geometry is determined; prove each model feasible.
- [ ] L5.2 Prove the converse equality statement and any needed reflection/combinatorial-family equivalences.
- [ ] L5.3 Run full build, #print axioms audit for critical and exported declarations, and fresh leanchecker replay.
- [ ] L5.4 Run the pinned Comparator against the independent n=9 Challenge, export every required dependency, and replay through NanoDa; examine complete machine results rather than assuming the build implies cross-kernel portability.
- [ ] L5.5 Audit the resulting public statement, exact total radius, equality classification, tool/AI provenance and metadata; publish immutable full-SHA and an updated reproducibility handoff. Only then mark the n=9 formalization completed.

## 3. Concrete repository layout (proposed, not yet created)

    NineChallenge.lean
    NineSolution.lean
    comparator-nine.json
    SquaresInCircles/Nine/
      Geometry.lean
      Stress.lean
      Selection.lean
      GraphCover.lean
      Capacity.lean
      Cert/Soundness.lean
      Cert/Data/*.lean
      SixBody.lean
      SevenBody.lean
      EightBody.lean
      NineBody.lean
      LowerBound.lean
      Equality.lean
    research/nine/
      SIX_BODY_TABLE_FIRST_DRAFT_2026_10_30.md
      PALOMAR_PORTABLE_LEAN_GATED_ROADMAP_2026_10_30.md
      HANDOFF_PR11_PALOMAR_LEAN_2026_10_30.md

Paths are a module plan, not an assertion that these files are present. Prefer a few sizable geometric lemmas to thousands of duplicated original-case proof scripts; enforce the current Palomar module and source-size restrictions.

## 4. Execution discipline and accounting

1. **Proof-first mathematical loop:** pick one complete original load orbit or a generic theorem that eliminates several; draft exact contradiction and all original boundary cases; only then perform one complete independent review and adopt it. Allow tentative calculations and explicit failed boxes in clearly marked research files.
2. **Formalize in parallel:** statement and general certificate checker can be built before C1.6.b0 is closed. Start kernel-checking the finite table and high-reuse physical geometry now; do not defer Lean until all 21 parents are proved by hand.
3. **No fake progress:** keep original 58 coarse IDs and 2,513 fine IDs immutable. A conditional feature, a proof manuscript, a generated polynomial, or a file hash is not a checked original gate; a math hand-closure is not a Lean theorem.
4. **Record metrics:** for each original case record graph/load ID, exact proof scope, continuous residual, data/certificate path, mathematical status, Lean build status, allowed axiom audit and independent replay status. Every closed gate links to a literal theorem and proof source.
5. **Do not let review eat research:** place discovery, proof construction and case completion ahead of review polishing. Review a complete row/union or reusable checker once; reuse it by exact theorem application. Never waive the final kernel/Comparator/NanoDa checks.
6. **No unsupported promises:** the remaining 21 parent cases are not necessarily equal difficulty. Progress in six-body exact certificates and articulation theory may transfer, but a finite combinatorial table alone does not bound the necessary continuous geometry.

## 5. Immediate next work package

- Reconcile the **25 status-UNRECONCILED** rows in the exact six-body table against the canonical fine ledger, without changing the original flags by guesswork.
- Target **D02.L135 Type II side** first with a rational semi-algebraic exact certificate; use inequality (T), elimination (E) and the full original endpoint/radius/torque constraints. Then tackle D02.L1345 without losing the loaded N force, and the four joint exterior-pocket cases.
- At the same time draft NineChallenge and the standalone verified graph-table enumerator + one small positivity/splitting soundness theorem in Lean. Do not wait to formalize the entire eight thousand-page research corpus.
- Build to the first **kernel-checked actual six-body orbit** and a complete-original-row proof next. Reassess certificate size and pivot to a stronger geometric reduction if certificate growth becomes prohibitive.

**Do not mark this roadmap complete** until all mathematical M0–M4 and Lean L0–L5 release gates have real compiled evidence. The latest source at input e14efe5b contains **no new fine/coarse closure**; this file creates none.
