# A-c744 handoff at user stop

The whole original positive-c744bc031d40ee64 remains OPEN. No original-cell or
mask credit was earned. No Lean, Lake, compilation, or CI ran. Numerical work
has stopped and there are no remaining A worker processes.

The published base is commit a41572b,
`a2_00100_a_c744_167_physical_checkpoint_20261105`: 167 nodes, 124 excluded
leaves, nine OPEN leaves. Its entire original-to-leaf consumer was freshly
replayed (28,709 deductions, 49,707 checked premises), independently reviewed,
and materialized from its thin archive. Historical source proofs were reused
explicitly. Remaining base leaves: 144,148,151,154,156,157,159,161,164.

This handoff preserves several independently checked alternative complete
subcovers of base leaves 144 and 151. Counts below must not be added together.

| Complete subcover | Nodes | Excluded leaves | OPEN leaves | Exact report |
| --- | ---: | ---: | ---: | --- |
| 144 after selected SAT bounds | 41 | 33 | 3 | SELECTED_BOUND144_EXACT_REPLAY.json |
| 144 after final angle continuation | 61 | 35 | 11 | ANGLE_FINISH144_EXACT_REPLAY.json |
| 151 bounded I/G/angle cover | 63 | 9 | 23 | ANGLE151_FULL_COVER_EXACT_REPLAY.json |
| 151 B/H owner cover | 9 | 6 | 2 | BH151_FULL_COVER_EXACT_REPLAY.json |
| 151 B/H then D/G owner covers | 25 | 18 | 4 | DG151_FULL_COVER_EXACT_REPLAY.json |

The latest concrete 151 frontier is the 25-node B/H–D/G cover. Its OPEN nodes
12,16,20,24 correspond respectively to the two surviving negative vertical
B/H owner alternatives crossed with the two positive vertical D/G owners.
All horizontal D/G alternatives and all other B/H alternatives exclude.
The four OPEN records retain 54,55,57,53 additional physical bound deductions.
The full 25-node graph and every record have passed exact replay from the
published A167 leaf-151 certified state. The actual numerical counter stopped
at 1,211 calls, within its 1,500-call bound. No next tactic was started.

The 144 tactic stopped at exactly 1,500 actual HiGHS.run calls. A preceding
small pilot had no retrospective low-level call count; this is disclosed in
its preserved counter metadata. At the stop, the complete 61-node cover has
11 OPEN alternatives. An earlier 41-node version has three broader OPEN
leaves (24,28,32). Its surviving normalized numerical frame points violate
D/G/H corner caps; those points are relaxation diagnostics, not physical
counterexamples. Generic splitting was stopped without a whole-leaf closure.

The bounded 151 angle tactic stopped at 63 nodes and 875 actual HiGHS.run
calls. Its node 53 is the first checked weighted use of the conditional 7/10
I-height row. Only I's certified slope interval [-1/2,1/2] discharges this
guard. The independent attachment reuses the accepted original-wide 16/25
proof's completed components 0,1,2,4 and D/G guards. A fresh scalar replay
checks 28 domains, 127 leaves and 15,875 exact Bernstein coefficients. Four
negative guard controls reject an out-of-range I, substitution of B's bound,
and the wrong original. The complete 63-node cover preserves the negative
outer I interval; no unguarded 7/10 promotion occurs. The other eight terminal
certificates in that cover use only existing physical rows.

For continuation, retain every sibling and each unchanged A167 ancestor. The
four 151 B/H–D/G states are a more informative starting point than its broad
angle-only frontier. A remaining geometric obstruction is separation from the
nearby originals C,H,I,F under the selected B/H and D/G owners; no complete
remaining-complement plan or new lemma has been proved. Other seven A167
survivors were not changed after publication.

The archive is native exact evidence, not a cold standalone proof. Restore the
published A167 and its existing A1/base/I64/correlation dependencies first.
`COPY_PROVENANCE.json` gives exact native aliases for this packet. The two
readers `replay_subtree.py` (physical rows) and `replay151.py` (also guarded
height rows) take TREE OUTPUT arguments and verify the complete subcover
against the A167 source leaf and source full-prefix receipt. The guarded
height decoder and all its frozen proof sources are included under
`guarded_height`. No discovery module or optimizer is imported by the readers.
