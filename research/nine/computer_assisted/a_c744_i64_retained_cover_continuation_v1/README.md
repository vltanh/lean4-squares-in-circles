# A-c744: exact continuation of the complete retained cover

The complete retained 165-node cover now has 118 excluded leaves and 14 OPEN
leaves. The new exclusions are leaves 155, 158 and 160. All 165 consumer records
and all complete covers were independently replayed; the observed process
exited zero. There were 112 rounds, 28,533 deductions and 48,549 printed rows.
The fresh component scalar replay checked 28 domains, 103 leaves and 12,875
Bernstein coefficients. No numerical optimizer or new split was used.

The original component-3 domain remains the old closed 3/5 domain. Every
original initial state, every old round and every 4/8/2 alternative is retained.
The original-wide 16/25 endpoint family supplies 1,664 positive weighted uses.
The old source/complement proofs and the separately published 813-deduction
source are explicitly reused by identity, rather than claimed as freshly run.

The compact archive in `delta/` holds all 17 changed payloads, the complete new
manifest, source files, full fresh report, inherited full report and observed
execution evidence. `readable_evidence/TREE_ASSEMBLY.json` maps all 148 omitted
unchanged payloads to the published A1 base packet. The archive has 45 regular
members and preserves 16,153,258 uncompressed bytes. Root fresh extraction and
the exact-member/prefix/base-alias audit passed. The two earlier byte-audit
harness errors and their corrected v3 source are retained as preparation
history; neither error was a mathematical replay failure.

For extraction, use the preserved `a165_delta_transport_v1.py` and inventory;
then the archived `materialize_tree.py` combines the delta with the identified
published A1 base. Native dependency aliases are still required for arithmetic
replay. This is not a claim of a cold standalone proof.

`separate_first_height_use/` records one subsequent exact deduction at leaf
154. Half of the accepted 16/25 height row and half of each current negative-yB
and negative-yD endpoint row improve yI's lower bound by 71693/524288, with
zero residual. The independent unchanged core accepts it and rejects five
damaged records. This separate one-leaf deduction has not replaced the cover.

The whole original and mask remain OPEN. The fixed totals remain 222/231
originals and 8/32 masks CLOSED. No Lean, Lake, compilation or CI was run.
