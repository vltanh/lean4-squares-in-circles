# n=9 — canonical proof roadmap (replacement v3)

**The unrestricted sharp theorem and complete equality classification are OPEN.**
Target: nine interior-disjoint, independently oriented closed unit squares in one disk have squared radius at least **1105/256**, and classify every attaining packing.

## What counts as progress

There are exactly **three theorem deliverables**: **A** lower bound, **B** complete equality classification, **C** human-checkable proof with exact tables. A theorem gate closes only when its full quantifiers and geometric scope are proved and checked. Experiments, conditional subfamilies, solver setup, and decisions to switch methods are *research activities*, not theorem closures.

The exact general nine-square model and one exact seven-row pilot are already available. They are **inputs**, not progress toward a complete unrestricted proof by themselves.

| Deliverable | Current status | Only acceptance test |
| --- | --- | --- |
| A. Global bound | **OPEN** | A complete sound proof excludes every physical packing at every squared radius q < 1105/256 |
| B. Equality | **OPEN** | Every physical q=1105/256 packing belongs to an explicitly characterized family, and every family member is feasible |
| C. Hand/table proof | **OPEN** | A self-contained manuscript reproduces A and B with human-checkable inequalities or exact finite tables |

## A — prove the lower bound

**A.0 — Faithful model [SOURCE AVAILABLE; audit required].** The unrestricted emitter represents all nine center/frame poses, 36 corners and 36 pair separations, including touching/parallel cases. The source proof of equivalence, exact q elimination and legal global rotation is in `computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md`. Independently audit before using it as the final theorem's foundation.

**A.1 — Global coverage [OPEN; mathematical bottleneck].** Give either (i) a complete finite certificate partition of the **actual unrestricted** counterexample formula, or (ii) a fully proved global geometric reduction to such a partition. Existing eight-directed-axis pair disjunctions give a syntactically finite Boolean cover, **not** a tractable solved partition. Every arbitrary orientation, contact degeneracy, equality face and disconnected configuration must remain covered. No unproved two-direction frame or stress selection is allowed.

  * **A.1a — sound representation [SOURCE AVAILABLE]:** all original physical constraints exactly, with a bijective or equisatisfiable global normalization.
  * **A.1b — exhaustive manageable cover [OPEN]:** produce explicit finite root/child/leaf definitions plus a proof that their union contains every potential counterexample. This is not known to have a practical size.
  * **A.1c — boundary and overlap accounting [OPEN]:** certify all zero, touching, repeated-normal and singular split faces; no generic-position assumptions.

**A.2 — Close the resulting finite obligations [OPEN].** Every leaf of A.1b needs a rigorous contradiction valid for all its real assignments: exact rational/algebraic interval arithmetic, a verified polynomial identity, or a fully proved hand inequality. A solver's bare UNSAT, a floating tolerance, and a fixed q=Q-epsilon computation do not count. Record a number of remaining leaves **only after** the partition is explicitly generated; leaf statuses are `PROVED` or `OPEN`, never silently discarded.

**A.3 — Independent global replay [OPEN].** An independently written verifier checks every node's implication/coverage and each terminal certificate, rejects unknown leaves, and proves that accepted output implies the impossibility of **all** q<Q physical packings. The uniform strict boundary as q approaches Q is included.

**A is closed iff A.0–A.3 establish the unrestricted lower bound.** The known q=Q attaining packing is already a source-checked input, so it then establishes the sharp optimum (subject to independent audit).

### Operational method, not an extra gate

**Primary attempt:** exact semialgebraic/computer-assisted proof using `emit_unrestricted_nine.py`, first with sharp q elimination, exact necessary bounds and certified branch compression. A proof-producing solver or interval/SOS checker must give a replayable certificate. **Fallback:** existing force/contact/graph lemmas, but only after proving a **single globally valid selection** and exhaustively covering the remaining physical cases. These are alternative mechanisms for A, not parallel gate trees. Switching tools is not a theorem completion. Local positive results do not count as A.2 progress until the A.1 cover has a proven caller.

The **two-direction theorem draft is not certified**. Its proposed Greene-grid step and support inequalities need an independent proof. Even if repaired, it covers only a special class and cannot by itself close A.1.

## B — characterize all equality packings

**B.1 — Complete equality-domain cover [OPEN].** Start again from the original **closed** q=Q physical formula. A strict q<Q contradiction alone is insufficient; preserve all tangent, zero-slack and oblique configurations.

**B.2 — Necessary normal forms and parameters [OPEN].** Prove every equality packing, up to global Euclidean isometries and relabeling, has one of explicitly listed structures. Give exact ranges for all center displacements, square rotations, free slides and endpoint choices. Do not assert that the seven-row pilot's equality core is globally necessary.

**B.3 — Constructive converse [OPEN].** Verify each listed parameter family satisfies all original corner and pair nonoverlap inequalities and exhausts the equality set. Then B closes.

## C — write the hand proof with tables

**C.1 — Human reconstruction [OPEN].** Provide the proof of the full A.1 cover, the exact inequalities for A.2 terminals, and B's necessity and sufficiency. Compact rational tables are permitted. If the global certificate is too large to display, supply a short explicit table schema, full attached table and an independent replay algorithm; do not claim an unreadable black-box solver output is a hand proof.

**C.2 — Audit [OPEN].** Recalculate table bounds independently and check all implications and degeneracies. Deliver one readable paper-level theorem and equality proof. Lean/CI is **deferred**, not counted as an open mathematical gate.

## One current task and one honest stop rule

**Active: A.1b — construct a provably exhaustive, usable partition of unrestricted counterexamples.** A.1c follows with it. Then A.2 and A.3, then B and C. No percentage of A or case fraction exists until a certificate cover has been generated and validated. Existing special cases may suggest a reduction but do not themselves reduce the remaining total.

If a direct exact approach fails, record its concrete limitation and pivot to a complete structural approach *within A.1*; do not close a theorem gate by declaring a method unsuccessful.

## Existing source assets (not new gates)

- `computer_assisted/emit_unrestricted_nine.py`: unrestricted 9-pose quadratic QF_NRA model.
- `computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md`: geometric model proof, source-tested sharp seven-body row certificate.
- `computer_assisted/row43_certificate.json` and independent checker: complete **conditional** parallel four-over-three row profile.
- `PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`: broader conditional physical 4+3 chain theorem.
- `computer_assisted/TWO_DIRECTION_SEPARABLE_NINE_SUMMARY.md`: **draft only** after explicit audit caveat.
- Older graph/stress research files are **supporting material**, not concurrent canonical progress counters.

Use `gates/ACTIVE_ROADMAP.json` as the machine-readable status. The superseded D/C/S/T/Q/E/H letters in old manuscripts are historical references, not a second active checklist.
