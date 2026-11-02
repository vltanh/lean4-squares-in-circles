# A.2 push-and-handoff after the rotating-frame checkpoint

Date: 2026-11-01 (America/Chicago; GitHub UTC date may read November 2).
Branch: research/nine-tablefree-hand, PR #11.
Prior proved checkpoint: 89cc4c2df52f8c61f7dc2709c9c91e8414ace3a9.

## Status and acceptance boundary

**Unrestricted A.2 OPEN.** The nine-square bound R²>=1105/256 is *not*
proved for all independently rotated squares. Global equality B.2/B.3,
full replay A.3, and final manuscript C.1/C.2 also remain open.
No Lean, Lake, CI, or mathematical proof program was run during this
handoff. No new whole-root exclusion is established. The existing
15 gate IDs, all 7,915 canonical root IDs, and the published root ledger
5,838 excluded / 2,077 OPEN remain unchanged. The archive-only 312
additional exclusions are *not* transferred into that ledger.
The genuine equality-witness root 7820 must remain open at closed Q.

This handoff distinguishes:
(1) complete mathematical derivations already committed;
(2) the newly supplied elementary marked-edge ledger; and
(3) post-checkpoint research leads for which a self-contained proof file
has not yet been recovered. Leads in group (3) are **not** accepted
certificates or closed gates.

## A. What is fully written and available on the branch

1. Complete sharp lower bound when an orthonormal coordinate cover
   misses at most one physical pair:
   ONE_EXCEPTION_NINE_HAND_PROOF_2026_11_02.md.
2. Complete two-direction projection-cover lower bound and equality
   *within that class*:
   TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md.
3. Exact physical two-square weighted support cap, whose sum proves
   the lower bound from two vertex-disjoint **actual** projection
   chains of lengths four and three:
   PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md.
4. Unconditional selective completed coordinate orders of height at
   most four, and the rotating-frame proof that **some** orthonormal
   frame always contains disjoint completed 4+3 chains:
   UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md and
   UNRESTRICTED_ROTATING_FRAME_EXTRACTION_HAND_PROOF.md.
   Consecutive completed links may be weak/nonphysical.
5. Unrestricted actual-four-chain outsider strip |x|<13/12,
   endpoint reserve |y_0|+|y_3|+(37/50)(h_0+h_3-1)<=1/8,
   and at most two outsiders per side column when q<Q:
   UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md,
   UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md.
6. Sharp three-whole-square half-plane terminal for
   e·x>=7/16, with its *three-square-only* equality family, plus
   universal three-center cap min_i(e·c_i)<21/20:
   THREE_SQUARE_SHARP_HALFPLANE_CAP_HAND_PROOF.md and
   THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md.
7. The exact sharp two-square directional cap, two-strip terminal,
   and boundary strict-radius normalization remain on the branch.

New in **this handoff**:
UNRESTRICTED_MARKED_CHAIN_EDGE_LEDGER_HAND_PROOF.md prints and proves
\[
 g_S+g_T\le d_x<h_S+h_T,\qquad |d_y|\le d_x<h_S+h_T
\]
for every weak completed x-link, and proves that all nonconsecutive
within-chain comparisons are physical. There are at most 32 symbolic
five-link masks, all-actual already settled, plus nine possible
(L,C,R) outsider occupancies for an actual four-chain. Neither ledger
is a list of independently solved continuous cases.

## B. Exact status of post-89cc4c2 explorations

These were discussed during the subsequent hand analysis but *were
not preserved as complete source proofs*. They are explicitly recorded
as reconstruction leads, not as proved stand-alone lemmas.

| Lead | Reported direction | Missing for acceptance |
|---|---|---|
| Side-column marker ordering | Vertical section-marker order constrains center-height order; a possible gap greater than 97/100 relative to an inner main square | State the precise physical section/center hypotheses and prove both chirality and weak-contact cases |
| Adjacent-main-square projection barrier | Restrict how an arbitrarily tilted outsider straddles the tops of adjacent inner mains | Reconstruct full geometric inequality with all four side-normal ownership/sign cases |
| Two-square central-strip cap | Limit how two physical outsiders jointly occupy the central strip | Exact threshold, hypotheses, and a complete support or marker derivation were not saved |
| Two-sided inner-main budget | When an inner main has appropriately placed outsiders above and below, a candidate bound |y_M|<7/20 emerged | Specify what “above and below” means for oblique physical pairs; prove the budget without silently assuming y-projection separation |
| Three-upper-outsider reduction | With both inner-main budgets, the proposed branch forces at least three whole outsiders beyond y=1/10 (after reflection) | Derive a *whole-square* lower-edge bound, not merely a center-height bound; exhaustive distribution/case proof |
| Same-sign joint shoulder cap | Central plus left/right shoulder with matched actual vertical separations and suitably bounded same-sign slopes appears to force Q sharply | State every matched endpoint and slope hypothesis, derive the common central-square support with one shared orientation, show both signs and all endpoints |
| Mixed-sign shoulders and oblique endpoint pairs | No complete transfer argument | Full independent physical signed-normal case analysis |
| Remaining weak-four links | Global completed4+3 extraction proved, physical conversion not proved | Complete geometric nine-body caller keeping all 36 physical pairs and the two unselected squares |

**Do not import these reported claims as theorems**. In particular,
a proposed claim about three *center heights* in an upper strip has
tilted-square negative controls; the whole-square distinction matters.
A seven- or eight-body analogue of the full nine-body end-exception
terminal has an exact subcritical obstruction. The nine-square
attainer with at least three exceptional pairs for every frame
refutes a universal small-exception-frame assumption at closed Q.

## C. The concrete remaining A.2 gates (work packages, not new canonical IDs)

**A2-F1 — actual-four physical case: fully documented.**
Take an actual horizontal four-chain M0<M1<M2<M3 and all five physical
outsiders. Using the proved strip and side-capacity bounds, exhaust
the nine possible (L,C,R) occupancy triples printed in
UNRESTRICTED_MARKED_CHAIN_EDGE_LEDGER_HAND_PROOF.md.
Do not substitute side marker membership for physical y-separation.
The target for each occupancy is an actual disjoint 4+3 chain, three
whole units in a forbidden 7/16 cap, a proved sharp support terminal,
or a fully derived contradiction. Treat both exceptional normal signs,
all owners, physical contacts and boundary ties.

**A2-F2 — finish the shoulder/central capacity theorem.**
Try to reconstruct and prove the joint-support same-sign argument first:
exactly one orientation of the central physical square must be used
in both support inequalities. Then handle mixed signs, oblique
shoulder-to-endpoint separations, and configurations where the
central outsider has no coordinate projection separation from either
inner main. The assertions in B are research leads until all their
hypotheses and scalar reserves are printed.

**A2-W — completed-four case with weak consecutive links.**
For any frame extracted by the unconditional rotation theorem, keep
the 4+3 chain, the two other physical squares, and mark its up to five
consecutive links according to the new exact edge ledger. Prove all
nonzero weak-link masks impossible at q<Q or force an actual
sharp terminal. Do not confuse “one weak selected link” with “one
exceptional pair in the entire nine-square configuration.”

**A2-G — global join and boundary audit.**
Every q<Q packing has such an extracted completed 4+3 configuration,
but the completion frame depends on the packing. Once A2-F1/F2/W
are complete, connect the universal extraction to a proved terminal.
Handle arbitrary orientations, all original physical pair constraints,
weak contacts, both reflected signs, and a strict-counterexample
normalization only in its allowed global domain.

There is no justified uniformly easy finite number of analytic
subcases, and no completion percentage. The 32 weak masks and nine
actual-four occupancies are *structural indexing*, not an exhaustive
validated finite certificate of continuous poses.

## D. Quality checks and handoff instructions

- Preserve source/proof/obstruction status exactly; do not mark A.2 done
  from a conditional cap.
- For a proposed new sharp inequality record exact hypotheses,
  signed separating-axis ownership, every support term and triangle/
  rectangle minimization, rational endpoint checks, and equality behavior.
- If an eventual theorem covers complete original root domains, record
  their stable IDs and replayable exact derivations before raising 5,838.
- The 312 earlier archive-only exclusions stay separate until their
  complete reproducible source, manifest, certificate and report are
  GitHub-published and checked.
- No Lean compilation or CI under the current hand-only instruction;
  tables are permissible, external numerical scripts only for checking
  candidate directions, never as proof evidence.

**Next action:** reconstruct the unarchived shoulder cap with its exact
signed premises and hand scalar inequalities, prove the missing
mixed-sign/oblique cases, and then apply it to the nine occupancy
groups. In parallel, reduce the weak-edge masks using the unconditional
completion theorem and the physical nine-body pair-span constraints.

## E. Canonical status

| Item | Status |
|---|---|
| A.2 unrestricted exclusion | OPEN |
| A.3 full replay | OPEN |
| B.2/B.3 full nine-square equality | OPEN |
| C.1/C.2 final manuscript/audit | OPEN |
| Published original roots | 7,915 total / 5,838 excluded / 2,077 OPEN |
| Separate archive-only claims | 312 extra exclusions, not published here |
| Active method | Hand proof; tables allowed; no Lean/Lake/CI |

This is a **source handoff**, not a claim to have completed the
unrestricted nine-square theorem.