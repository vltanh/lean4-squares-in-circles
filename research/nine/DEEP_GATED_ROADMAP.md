# n=9: fixed-domain roadmap

November 1, 2026, America/Chicago. Supersedes the expanding active research queue; preserves the same 15 roadmap IDs, all 7,915 positional root IDs, and every existing proof source.

**Target:** every nine-square packing has q>=Q=1105/256; then classify every equality packing and assemble a complete hand/table manuscript. **All three global deliverables remain OPEN. Active gate: A.2.**

[Exact closure contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md) · [Current status](PROGRESS.md) · [Machine registry](gates/ACTIVE_ROADMAP.json)

## The unchanged gates and their actual acceptance conditions

| ID | Status | Acceptance condition |
|---|---|---|
| A | OPEN | Complete unrestricted q<Q exclusion with justified inputs and assembly |
| A.0 | SOURCE AVAILABLE | Faithful physical model and attaining witness, with their geometric equivalence audited |
| A.1 | EXPLICIT COVER AVAILABLE | Every strict counterexample is covered, without an assertion that continuous domains are easy |
| A.1a | SOURCE AVAILABLE | All nine independent frames, 36 corners, and 36 weak pair separations retained |
| A.1b | SOURCE PROOF + HISTORICAL ENUMERATION | Original positional cover and its stable IDs retained; source chain extraction supplies the hand-mask cover |
| A.1c | PROVED FOR HEX COVER | Closed cell boundaries, weak contacts, and all orientation endpoints retained |
| A.2 | OPEN / ACTIVE | Complete whole-domain hand proofs or a universal terminal-extraction proof covering every strict counterexample |
| A.3 | OPEN | Audit the complete global proof and its dependency/coverage assembly, including every q<Q arbitrarily close to Q |
| B | OPEN | Necessary-and-sufficient unrestricted equality families |
| B.1 | EQUALITY ROOT COVER SUPPLIED | Every q=Q configuration remains in the closed cover |
| B.2 | OPEN | Prove all equality structures and parameter ranges up to actual common symmetries and relabeling |
| B.3 | OPEN | Verify the converse for every proposed global equality parameter family |
| C | OPEN | Complete human-checkable unrestricted bound and equality proof |
| C.1 | OPEN | One assembled manuscript with the full cover, complete terminal callers, and equality argument |
| C.2 | OPEN | Independent audit of final arithmetic, geometric implications, and boundary cases |

No gate is newly closed by this reset. Lean, Lake, and CI remain deferred; no computational replay is part of the current execution plan.

## A.2 has one fixed frontier, not a growing tree

The active hand-proof frontier is exactly the existing 32 masks in
[gates/A2_MASK_FRONTIER.json](gates/A2_MASK_FRONTIER.json). Their quantified physical domains and coverage proof are in Sections 2-5 of the contract. `000/00` and `010/00` have inherited complete proofs; 30 masks remain OPEN. These are continuous domains, not a finite list of sampled geometries.

The original root ledger is separate: 5,838 closed-Q exclusions and 2,077 OPEN roots. These counts are inherited from the published summary, not recomputed. Root 7820 contains equality and must never be labeled a closed-Q exclusion. Strict-radius discharges and closed-Q exclusions must have distinct records.

A complete fixed-root hand/table proof is an alternative route. It must name the stable root and its full predicate. A conditional chart within a root does not discharge that root. Global rotations or center expansions require a root-transfer argument when used in this route.

## Immediate proof target

**Whole `000/01`, with `000/10` by reversal.**

Prove the nine-square lower bound with an actual four-chain and a disjoint cone three-chain whose first link is actual and second weak. The remaining two squares and every cross-pair remain unrestricted physical data. This is not the global one-exception hypothesis.

The most useful common proof would also settle `000/11`, namely the entire actual-four-chain nine-square family. That is a broader possible conclusion, not another gate. No claim of equal difficulty or of a guaranteed small proof is made.

Other masks wait in the same fixed table. New owner signs, floor thresholds, first-birth positions, or orientation intervals are not added to the active queue. Existing corresponding lemmas may be used only with proved hypotheses.

## What counts as progress

A mathematical closure checkpoint contains a complete proof for at least one fixed full mask, a complete strict-radius proof for named original roots, or a valid global terminal-extraction theorem. Necessary internal lemmas and exact tables are allowed inside that proof.

Every internal split must cover its parent, including its complement and boundary faces. Every leaf must close or invoke a proved terminal whose hypotheses have been derived. Dependencies must be acyclic or explicitly well-founded. Splitting alone earns no closure.

A new conditional inequality, recovered source, tighter numerical threshold, or additional case distinction is not a closed gate. An unfinished attempt is recorded as OPEN/BLOCKED with its obstruction; it is not converted into new mandatory children. Corrections and source-maintenance commits must report zero new mathematical closures unless they include an actual complete proof.

## What this roadmap does not promise

A decreasing count of unresolved fixed rows is an accounting invariant for accepted correct closures. It is not a proof-discovery algorithm and does not guarantee that the next row can be solved. Finite coverage, compactness, and a list of masks do not establish a uniform subdivision bound. The former proliferation of cases is stopped administratively; mathematical convergence still requires the missing whole-domain arguments.

The current hand sources are a library, not an extra roadmap. Their pre-reset catalogue and detailed history remain at
[ea4ff8b](https://github.com/vltanh/lean4-squares-in-circles/blob/ea4ff8bad97a58e2b8633ab69f549acb5352e573/research/nine/DEEP_GATED_ROADMAP.md).
