# n=9 — current proof roadmap and gate status

**Status at the 2026-10-22 PR #11 commit review:** the
unrestricted \(n=9\) lower bound and complete unrestricted equality
classification are **OPEN**. The upper-bound construction is exact.
Mathematical conditional-branch lemmas are hand proofs, not Lean
kernel-checked theorems. No n=9 Lean build or CI is claimed.

## Canonical documents

1. **[DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md)** — *authoritative
   detailed plan*, including G0–G8, subgates/subsubgates, dependencies,
   quantified closure criteria and falsification rules.
2. **[G2_SUBGATES.md](G2_SUBGATES.md)** — *authoritative current
   mathematical branch ledger*, including which C4/O gates have
   hand proofs and which remain open.
3. **[README.md](README.md)** — source index, handoff and proof
   reading order.

This short file is the entry point. The initial long roadmap was
superseded by the deep roadmap; its previous versions remain in
the branch's Git history. When statuses change, update the **deep
roadmap and G2 ledger together**, then this summary and PR #11.

## Target

For nine freely oriented closed unit squares with pairwise disjoint
open interiors inside a disk centered anywhere, prove
\[
R^2\ge Q:=1105/256,\qquad R_9=\sqrt{Q}=\sqrt{1105}/16,
\]
and classify **all** equality packings under the repository's exact
rotation/relabeling congruence. The explicit 2–4–3 construction
shows only that \(R_9\le\sqrt Q\); the converse is open.

## Live gate ledger

| Gate | Mathematical contract | Status |
|---|---|---|
| G0 | Exact construction, corner/SAT geometry, negative tests | CLOSED hand / negative controls |
| G1 | Arbitrarily rotated four-anchor, 4+3, grid and signed stresses; fixed-owner weak dual | CLOSED hand **conditional on terminal hypotheses** |
| G2.C0–C2 | Common-frame rank injection, four-chain shadow and whole large-zigzag exclusion | CLOSED hand |
| G2.C3.1–C3.2 | Signed matched 4+3 and three-band grid terminal | CLOSED hand |
| G2.C3.3.a | Exact (4,1)/(3,2) two-stack classification | CLOSED hand |
| G2.C3.3.b | Complete (4,1) complement exclusion by central-quadrant cover | CLOSED hand |
| G2.C3.3.c | Complete (3,2) complement via elementary five-element matching and perpendicular 4+3 stress | **CLOSED hand** |
| **G2.C4** | **Sharp n=9 bound for every common-coordinate-separable packing, independent orientations** | **CLOSED hand** |
| G2.O0–O2 | Exact oblique equality witness, actual SAT owners and fixed-owner convex weak dual | CLOSED negative/framework |
| **G2.O3** | Exhaustive geometric owner-graph classes for *unrestricted* square orientations | **OPEN — principal global blocker** |
| **G2.O4–O5** | Uniform orientation stresses and full oblique coverage | OPEN / BLOCKED on O3 |
| G2.X / G4 | Sharp theorem from original unrestricted Packing alone | BLOCKED on oblique structural closure |
| G5.0 | Stratified, signed matched-chain and common-coordinate **conditional** equality families | CLOSED hand within named classes |
| G5.1–G5.3 | Complete necessity/converse for *all* unrestricted equality packings | OPEN / BLOCKED |
| G6 | Independent table-free manuscript audit | BLOCKED |
| G7–G8 | Lean/Palomar-standard kernel proof and public integration | NOT STARTED |

**Critical distinction:** G2.C is now **mathematically complete as a
hand proof** but G2.O cannot be omitted. At least one exact
record-radius packing is **not** coordinate-separable in any single
global orthonormal frame. The unrestricted \(n=9\) conjecture
therefore remains OPEN; no Lean or independent audit is claimed.

## Reconciliation of the recent commits

The PR #11 research head before this reconciliation was
[c0e26c3](https://github.com/vltanh/lean4-squares-in-circles/commit/c0e26c3616413746adc66d9de619b7db23ff4d28),
committed 2026-10-23 02:29 UTC (2026-10-22 Chicago time).
Review of the preceding research commits establishes:

- **[TWO_COLUMN_COMPLEMENT_REDUCTION.md](TWO_COLUMN_COMPLEMENT_REDUCTION.md)**
  is a *proved* reduction, not an open combinatorial task. The five
  complementary squares have **exactly** two vertical rank stacks
  of sizes (4,1) or (3,2). A vertical triple's middle center obeys
  \(|y|<21/40\), forcing an inner horizontal-chain square to have
  \(|y|>19/40\).
- **[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md)**
  is a genuine record-radius nine-square packing with a horizontal
  four-chain and a five-square complement of horizontal chain number
  two. Therefore **reject** attempts to eliminate the entire
  residual class at \(q\le Q\); a sharp terminal theorem must
  retain its equality poses. The witness also has disjoint **vertical
  4+3** chains, demonstrating a useful frame switch.
- **[SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md)**
  gives a necessary-and-sufficient **conditional** equality
  parametrization for signed 4+3-chain terminal hypotheses:
  four pinned boundary squares, three slider heights, two
  independently oriented additional squares, and exact SAT checks.
  It is **not** yet the global equality theorem.
- **[NONSTRATIFIED_PARALLEL_NINE.md](NONSTRATIFIED_PARALLEL_NINE.md)**
  proves even an all-axis-aligned record-radius packing need not
  admit horizontal stratification in *any* frame. Thus
  stratification is an invalid global equality normal form.
- **[CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md](CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md)**
  constructs eight squares with perpendicular four-chains at
  \(q=17/4<Q\). Excluding crossed chains without using the ninth
  square is another **rejected** shortcut.
- **[SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md)**
  removes center coordinates after orientations and true SAT
  separator owners are fixed. It does *not* close graph coverage
  or establish a uniform sharp radius inequality.

The completed coordinate-separable large-zigzag exclusion in
[ZIGZAG_BRANCH_CLOSED.md](ZIGZAG_BRANCH_CLOSED.md) remains
CLOSED; do not describe its 4×3 rank subcase as pending.
The oblique-safe [INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md)
remains a completed lemma *conditional on the existence of a
four-projection chain*, not a proof such a chain always exists.

## Next exact mathematical deliverables

**Completed: G2.C3.3 and G2.C4 (entire common-frame branch).**
[FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md](FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md)
eliminates the (4,1) case.
[COORDINATE_SEPARABLE_NINE_COMPLETE.md](COORDINATE_SEPARABLE_NINE_COMPLETE.md)
eliminates (q<Q) in every (3,2) case via a five-element
poset matching and a perpendicular signed 4+3 terminal. Together
with the earlier rank/grid/zigzag theorems, this is a complete
**hand proof** of the sharp radius for the common-coordinate class.
Do not reopen this branch for minor parameter tightening.

**Now first: G2.O3–O5 (unrestricted oblique coverage).** Prove a
geometrically meaningful, human-sized exhaustive class reduction
for actual square-edge-normal separating axes. Use the convex weak
dual to certify each class uniformly over all allowed orientations.
A list of SAT assignments without a compression/coverage theorem
does **not** close O3.

**Then: G2.X/G4 and G5.** Only after the oblique route closes,
assemble the unrestricted lower bound and recover every equality
packing, including nonstratified and oblique-only variants.

**Finally: G6–G8.** Independent mathematical audit, Lean formalization
using only standard kernel proof checking, and public integration.
Do not change the status to completed because no `sorry` appears
in an uncompiled Lean draft.

## Proof-completion discipline

A gate closes only after its original quantified statement is
proved, with exact equality and boundary cases, or an explicit
counterexample forces it to be marked REJECTED and reformulated.
Count progress by **full structural classes covered**, not by
individual numerical cases. Preserve commit timestamps in the
handoff and keep PR #11 draft until the unrestricted theorem and
formal verification are actually complete.
