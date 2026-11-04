# Continuation across the 14 remaining reversal classes

This is a read-only work plan, with no new exclusion or proof credit. Its
snapshot is PR #11 commit 925e1112814a0758889cafa5c975c27414b86570. The current
mask ledger has 8 strict-radius closures and 24 OPEN masks. The separate
001/00 register has 231 immutable original cells: 221 closed and 10 OPEN.
The D821 native proof and literal table have passed, but its final cold
replay and publication were pending at this snapshot. Component proofs,
including the published A1 checkpoint, do not close their containing cell.

The current 24 OPEN masks form **14 reversal classes**. After a complete
strict-radius 001/00 proof and its exact reversal are accepted, **13 classes
and 22 raw masks** remain. These are counts of fixed predicates, not an
estimate of remaining work. The contract and mask ledger contain some
historical original-cell counts; the current 221/10 count comes only from
the fixed original-cell register. The source inventory and metadata check
are in PLAN_BINDINGS.json and PLAN_METADATA_CHECK.json.

## Keep the target unchanged

For every full-mask caller, retain nine independent physical unit-square
frames, all 36 original corners, all 36 physical pair conditions and all
five designated center-cone comparisons. Every corner must have squared
norm strictly less than Q = 1105/256; physical contact is allowed. On each
designated edge, bit 0 means horizontal gap at least the physical support
sum, and bit 1 means a strictly smaller gap. Projection equality belongs
to bit 0, while cone equality remains allowed. H and I remain physical
even when a terminal theorem uses only a subset of originals.

The accepted reversal simultaneously reverses both chains and negates
both witness basis vectors. It maps abc/de to cba/ed and preserves every
original physical constraint. Reversing only the short bits is not this
operation. Different exact masks have no assumed implication: in
particular, a proof of 001/00 does not prove 011/00, and a short bit of 1
does not supply the corresponding actual EFG projection link. An optional
global routing proof must prove its new witness and all terminal premises.

## Exact class map and available starting points

“Boundary” below means an already checked nine-square witness at exactly
Q, never a strict-subcritical witness. “New short-row argument” may instead
be a proved physical relabeling or global extraction; it is not permission
to replace a weak designated edge by an actual one.

| Representative | Reversed partner | Starting point or remaining obstacle |
|---|---|---|
| 001/00 | 100/00 | Finish the unchanged 231-cell register, assemble the full strict predicate, then apply reversal. |
| 001/01 | 100/10 | EF actual, FG weak: full-nine bounds and a new short-row argument. |
| 001/10 | 100/01 | EF weak, FG actual: a distinct full caller; new short-row argument. |
| 001/11 | 100/11 | Both short links weak; new short-row argument or proved routing. |
| **011/00** | **110/00** | **Next principal target:** accepted strict actual-AB terminal and complete guard complements. |
| 011/01 | 110/10 | EF actual, FG weak; the strict actual-AB adapter does not supply the missing short link. |
| 011/10 | 110/01 | EF weak, FG actual; retain this distinct caller and every complement. |
| 011/11 | 110/11 | Both short links weak; full-nine analysis and a new short-row argument. |
| 101/00 | itself | Accepted original-four-row terminal is available under its opposite-sign and height guards. |
| 101/01 | 101/10 | One short link weak; new short-row argument or proved routing. |
| 101/11 | itself | **Boundary**; both short links weak. A strict boundary argument or valid routing is essential. |
| 111/00 | itself | **Boundary**, even with all five cone and bit margins strict; use sharp strict-radius reasoning. |
| 111/01 | 111/10 | **Boundary on both masks**; one short link weak and a sharp strict boundary obligation remains. |
| 111/11 | itself | **Boundary**; both short links weak and a sharp strict boundary obligation remains. |

## First full-mask continuation: 011/00

Build a fresh exact caller for the original strict 011/00 predicate.
The published conditional actual-AB application uses either original
X = H or X = I. Its quantitative guards are:

- the canonical angle of D is nonnegative;
- yG >= yD and abs(xG - xD) < 1;
- xB <= xX <= xD;
- abs(yX - yB) + abs(yD - yX) <= 3/5.

The exact mask supplies actual AB, EF and FG. Under these guards the
accepted theorem gives q >= Q, contradicting the strict target. Actual
BC is not a premise of this strict application. Its older 001/00
closed-Q equality blocker must not be imported. Actual use requires a
fresh, source-bound replay of the accepted scalar proof: 28 domains,
103 leaves and 12,875 rational coefficients, plus independently proved
strict 011/00 ancestry and the literal guard.

Every guard failure remains in the full caller. In particular, D821's
reduced five-domain complement is specific to its proved parent guards;
it is not automatically a full 011/00 cover. The previously accepted
opposite-endpoint original ABCD row is another optional terminal for any
short-00 caller with opposite endpoint signs and total ABCD height
variation at most 23/100. Its complete escape cover has eight signed
height halfspaces and two same-sign conjunctions. The optional
near-horizontal 011/00 replacement-row cover has 144 domains. Neither
cover excludes its members without their complete proofs.

## Computer-assisted route and stopping conditions

1. After the current original cells close, emit the exact full strict
   nine-square caller with emit_fixed_mask.py. Its API accepts each exact
   mask; run_full_mask.py is a historical hardcoded 000/01 trial, not a
   batch driver. Bounded SMT or optimization trials are discovery only.
2. Reuse accepted universal corner, four-product corner, owned-pair Gram
   and owner-free support rows through a new independently checked
   caller adapter. Do not reuse D821's fixed-path ancestry as a full-mask
   premise. Preserve every alternative and every shared equality face.
3. Use sharp terminals where a positive-reserve closed-Q contradiction
   cannot hold. Complete each caller-to-terminal cover, with finite
   acyclic bindings for reused consequences, before claiming closure.
4. Require the whole exact replay, physical hand derivation, literal
   terminal table and cold portable replay; then transfer the complete
   strict theorem by the specified reversal. Commit reviewable completed
   results without promoting partial trees or changing the fixed masks.

The selected-seven controls realize all 24 OPEN masks with squared
corner norms strictly below 17/4 < Q: 14 representatives and 882 exact
rational checks. They prohibit an unconditional exclusion of the A-G
subsystem; they are not nine-square counterexamples. The separate full-nine
closed-Q controls cover 101/11 and all four 111/de masks. Retain their
published exact witnesses when checking proposed global relaxations.
An exclusion only below Q minus a fixed positive margin cannot settle
any of the requested strict predicates.

The inherited 001/00 baseline coverage uses strict-radius arguments.
Even if every original cell closes, its assembled 001/00 and 100/00
claim remains strict-radius unless a separate complete closed-Q proof is
supplied. No numerical solve, ledger edit, new mandatory subdivision or
proof installation is performed by this plan.
