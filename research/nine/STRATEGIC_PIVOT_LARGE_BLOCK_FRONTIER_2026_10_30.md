# PR #11 — strategic reset: large cyclic blocks before six-body polishing

**Prepared:** October 30, 2026 UTC. **Status:** research strategy and exact ledger observation, NOT an adopted new exclusion or a proof of n=9. Input mathematical checkpoint: `1bead7f5e377753f4b5ddda68eb02fc5b3bc304c`; preceding published handoff: [HANDOFF_PR11_2026_10_30_PUSH_CURRENT.md](HANDOFF_PR11_2026_10_30_PUSH_CURRENT.md).

## Decision

Stop treating completion of the last six-body parent as the critical path. A six-body closure would leave **21** coarse rows open, including **10 nine-body** rows. Prioritize a quantitative full-nine-square theorem organized by **large biconnected cyclic blocks**, using the seven-body equality-like core as the sharpness test. Do not replace this with a renamed set of 22 local case proofs.

This memo changes research priority, NOT the original gates, assumptions or identities:
- **2373/2513** original fine obligations checked, **140 open**.
- **36/58** original coarse cells closed, **22 open**.
- Sharp unrestricted `R^2 >= 1105/256`, equality classification, full G4.2.c downstream common-selection audit, and Lean integration are OPEN.

## 1. Exact combinatorial observation from the original ledger

Inspection of the unchanged 58-cell table in [CYCLIC_CELL_LEDGER.md](CYCLIC_CELL_LEDGER.md) yields the following exhaustive partition of its **22 currently open** coarse rows:

| Component size | Single cyclic block (C1) | Two cyclic blocks (C2) | Total |
| --- | --- | --- | ---: |
| 6 | C1.6.b0 | — | 1 |
| 7 | C1.5.b2, C1.6.b1, C1.7.b0 | C2.35.b0 | 4 |
| 8 | C1.5.b3, C1.6.b2, C1.7.b1, C1.8.b0 | C2.35.b1, C2.36.b0, C2.45.b0 | 7 |
| 9 | C1.6.b3, C1.7.b2, C1.8.b1, C1.9.b0 | C2.35.b2, C2.36.b1, C2.37.b0, C2.45.b1, C2.46.b0, C2.55.b0 | 10 |
| **Total** | **12** | **10** | **22** |

**Ledger consequence:** every open row contains at least one **biconnected cyclic block with five or more vertices**. There is no open C1.3/C1.4, C2.33/C2.34/C2.44, or three-/four-block row. This is a finite bookkeeping fact, NOT an unconditional theorem about all geometric minimizers until the original root inventory's exhaustiveness and the global selection/prerequisite audit are established.

A purely “long cycle” theorem is insufficient: a 2-connected graph with >=5 vertices can have no simple cycle of length >=5 (e.g. K2,3, or a multiear book of short cycles). The desired generality is **block order >=5**, including interior vertices, short-cycle ears and chorded blocks, not just a bare C5-C9 rim.

## 2. Why the current approach does not scale

1. The newly proved arbitrary-degree support-band, closed-cone and loaded-chain theorems are useful, but the score has not moved from 2373/2513 or 36/58 across the recent sequence. Reduction of a *feature* is not closure of its whole original cell.
2. A positive stressed component with six or seven bodies leaves three or two **real remaining squares**. Their physical placement is often the essential sharp constraint; deleting or forgetting them changes the theorem.
3. [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md) provides a planar **translational** certificate with outer-face circle loads; it does NOT license replacing the full **torque-balanced physical contact** certificate by its uncrossing. Any combined proof must explicitly establish a compatible selection or work with separate certificates.
4. The record construction in [SPARSE_MINIMIZER_STRESS.md](SPARSE_MINIMIZER_STRESS.md) has a seven-square cyclic stressed core with two additional physical squares, at exactly `Q=1105/256`. Therefore an unconditional claim that all large cyclic blocks are impossible at `q<=Q` is false. A sharp argument must use `q<Q` or retain equality configurations.

The unfinished far-side and A-only Type II L135 side rows, loaded N in L1345, and the other D02 configurations are **still open**. Their previous accepted inequalities remain valid at their exact stated scopes; no unreviewed unique-C draft is promoted.

## 3. Primary approach: large-block geometry and completion capacity

**Research goal (unproved):** isolate a *short, graph-order-independent* geometric inequality, with a sharp radius threshold, that applies to an actual cyclic block of size >=5 **and all nine actual squares**. The already-closed small-block cases then leave only this single geometric principle plus an explicit G4.2.c audit. This goal is almost as strong as the theorem under the existing reduction, so merely restating it is not progress; progress requires a genuinely checkable intermediate bound.

### Gate LB0 — calibrate against the equality witness, not D02 alone

Use `C1.7.b0` (seven-body cyclic block plus two physical completing squares) as the **first target**, because the record construction supplies an exact sharpness test. State a necessary geometric **capacity inequality** in terms of the whole block's actual supports and the two remaining squares. It must:
- apply to freely tilted squares, physical zero-weight circle corners, shared-side means and every original load;
- imply a contradiction for `q<Q` rather than incorrectly excluding the record at `q=Q`;
- cover the record's seven-core geometry with equality or explain its strict slack;
- avoid presuming that the two completing squares are stressed or have any prescribed orientations.

Deliverable: one explicit inequality with quantified domain and a complete continuous proof; if it only handles a named pose or an individual load mask, it is a diagnostic, not LB0 closure.

### Gate LB1 — extract a size-independent geometric budget

Test a **two-radius/annular angular-occupation** approach, using actual physical squares and their possible empty arcs, with an inner-region packing count. The basic pointwise disjointness `sum occupied angular lengths <= 2*pi` is valid but *by itself too weak*; a viable argument must link two radii, boundary-root spacing, the central capacity and the free completing squares, and deliver a strict reserve below `Q`. The existing small-root arc/cap theorems may provide this coupling.

A second candidate is a **support-width/directional corridor budget** for a near-diametral chain, building on the exact new preliminary hand lemma
[UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_2026_10_30.md](UNIFORM_FOUR_SQUARE_AXIAL_CHAIN_NEAR_DIAMETER_2026_10_30.md).
That lemma is a genuine all-size geometric estimate, but applies only when **three consecutive actual tight contacts share one signed normal**. It does not cover every large block; its usefulness must be measured by actual callers, not by its elegant statement.

Falsification tests: apply the same candidate to `C1.7.b0`, `C1.6.b0` and `C1.9.b0`, preserving all nine physical squares. The exact record packing must pass the weak form at `q=Q`. If no common numerical/structural invariant survives at least two of those cells, do not spend another cycle reducing a single D02 polynomial.

### Gate LB2 — induct over biconnected blocks, not component size

Express a large block by a cycle and successive open ears. Separate (i) unloaded degree-two actual transmitter paths, (ii) genuine loaded branches, (iii) new hubs of true positive degree >=3. Suppress only actual unloaded degree-two vertices, with their exact projected support widths and their bodies still counted. Prove an **ear-extension inequality** that preserves or increases the LB1 obstruction when a block grows or acquires external attachments.

Do NOT assume every large block contains C5; do NOT pretend contraction preserves torque or all physical contacts. If an ear is loaded, it retains its own complete force, moment and circle equations. If an extension inequality fails on a legitimate example, record the counterexample and narrow the premise; never count the family as closed.

Concrete transfer tests: `C1.5.b2 -> C1.5.b3`, `C1.7.b0 -> C1.7.b1/b2`, and `C1.8.b0 -> C1.9.b0`. The arrows are **tests**, not proved monotonic implications.

### Gate LB3 — independently handle two-block pressure

There are **10** open two-block rows. Test a single **joint exterior-root / annular capacity** obstruction on `C2.35.b0` and `C2.55.b0` first; one has two completing squares and the other has none. A theorem only for one block or only for a bare long cycle cannot close these. Full shared articulation, all actual connecting squares and individual physical circle masks must remain.

### Gate LB4 — audit, sharp inequality and equality

Only after LB0-LB3 cover **all** listed original rows: assemble the exact original 58-cell joins, independently audit G4.2.c for nonidentity, chosen normal/force consistency and true degree, prove `R^2>=Q` for all nine-square packings, and classify the full equality domain in both directions. Equality is not discharged by excluding `q<Q`; the model's inactive two squares and possible sliding degrees of freedom must be treated explicitly.

## 4. Independent exact-algebra fallback, with no stress assumptions

All nine-square configurations can also be encoded **directly** without contact-graph classification. This is a rigorously equivalent finite semialgebraic feasibility question, not a claim that general quantifier elimination is computationally tractable.

For `i=1,...,9`, let `c_i=(x_i,y_i)`, `u_i=(a_i,b_i)`, `v_i=(-b_i,a_i)`, with `a_i^2+b_i^2=1`. The four physical corners are `c_i+(epsilon*u_i+eta*v_i)/2` for signs `epsilon,eta in {-1,+1}`.

- **Disk:** each of the 36 corner norms squared is **strictly** below `Q=1105/256`.
- **Disjoint interiors:** for each of the 36 pairs `i<j`, at least one of `d in {u_i,v_i,u_j,v_j}` satisfies the *weak* separating-axis inequality
```text
|d · (c_j-c_i)| >=
    (|d·u_i|+|d·v_i|+|d·u_j|+|d·v_j|)/2 .
```
  This is the standard exact separating-axis equivalence for two rectangles; equality permits actual boundary contact. Signs and absolute values can be eliminated by finite polynomial sign splits. A common rigid rotation can normalize `u_1=(1,0)`.

The strict system is satisfiable **iff** nine interior-disjoint unit squares fit in a disk of squared radius **strictly less than Q** (take the maximum of all 36 vertex radii for the reverse implication). An exact UNSAT certificate would prove the sharp lower bound at once, regardless of the 22 stress cells; an equality classification would require a separate analysis of the weak `<=Q` system. At its full 9-body dimension this is likely too large for a naive CAD/SOS implementation. Use this exact encoding to **check proposed global inequalities or low-dimensional exceptions**, not to claim a computation that has not been performed.

## 5. Research discipline and stop conditions

- **Priority:** LB0 (seven-body equality-calibrated capacity) -> LB1 (global budget) -> LB2/LB3 (single-/two-block transfer) -> LB4 (audit). Keep the six-body D02 side calculations as a benchmark and revisit them only if a result transfers to another component size or closes an entire original parent.
- **Promote a new general lemma only after** its complete source, precise actual-contact premise, full force/moment requirements if any, all physical endpoints, and a separate independent current-source review. Explicitly distinguish a bare general lemma from its caller-specific complete joins.
- **Measure progress** by original coarse rows actually closed and by a documented common invariant proved for at least two distinct component sizes. Do not create new bookkeeping flags or inflate percentages by subdividing cases.
- **Pivot criterion:** if the proposed annular or ear inequality cannot handle the exact seven-body record without false strictness, or fails to yield a common reduction on two of the three named single-block benchmarks, stop local polynomial sharpening and pursue the exact semialgebraic verification track.
- **Preserve:** original nine physical units, true loads/degrees, selected normals, complete positive contact stars, full actual application means, every circle mask and allowed individual zero weight. No claim of common rotational and planar stress until separately proved.
- **Current commit:** strategy documentation and one elementary candidate hand lemma only. No fine or coarse flags updated; no new radius certificate, Lean build, CI run or merge.

This reset is intended to reduce **structural complexity**, not merely to rename the unclosed \(n=9\) theorem as a “large-block lemma.”