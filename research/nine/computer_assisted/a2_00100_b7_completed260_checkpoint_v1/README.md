# B7: portable checkpoint of completed domain 260

**The original remains OPEN. This checkpoint grants zero original-cell and
zero whole-mask credit.** The live fixed register at publication has
223/231 CLOSED and 8 OPEN.

The unchanged original is `negative-7c60be8b07a358e9`. Native and fresh portable
exact replay both check its entire 813-node physical cover: 442 excluded
terminal cases and six OPEN cases. Inside it, saved domain 260 is fully
excluded by a 425-node cover with 213 excluded leaves. All nine physical
unit squares, original corners and pairs, marked conditions, strict CD,
original frames and shared closed faces are retained.

The completed component contains both closed sides of `y_I-y_H=0` and the
full positive-half continuation. Its physical attachment and independent
source/coverage review are included. The six outside obligations are
original-tree nodes 3, 4, 142, 154, 156 and 264. Later continuations are not
implicitly part of this frozen snapshot.

## Recovery and exact replay

Concatenate the parts in the order listed in `ARCHIVE_PARTS.json`. Check
every part hash and then the complete archive SHA256
`8caaaa49a1ec7527896fe6733a3722fb1bd0cfec5be61b33a90802d50bbb5346` before extraction. The archive has
33,772,300 bytes and 1,231
verified regular members. Its top directory is `b7_completed260_open_packet_v2`.

Place it beside the published `b16a_I32_complete_H_checkpoint` prior named
in `PUBLISHED_PRIOR.json` (prior archive SHA256
`c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`). From their common directory run:

```sh
python3 -B -S b7_completed260_open_packet_v2/code/replay_registered_b_relative_support_packet.py \
  --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is `PASS_PORTABLE_OPEN_PROTOTYPE`, with
`complete=false`, `whole_original_proved=false` and six OPEN leaves.
The portable checker forbids old-workspace proof reads, independently
reconstructs exact arithmetic and complete covers, and rehashes all inputs.
The transport adds only 751 verified aliases to already frozen bytes; the
original proof and checker files are unchanged.

## Reusable boundary sources

The sibling `a2_00100_original_boundary_guard_helpers_v1` folder preserves
the sharp and deep boundary guards with their frozen theorem sources.
Its fresh local-only source replay checks three sharp criteria and 144
deep identities. This source package itself has zero original-terminal
uses and zero credit. Concrete C27 central subdomains use the existing
sharp AHID terminal; no deep-cylinder use is inferred from preparing it.

The claim remains strict `q < 1105/256`. No closed-Q global theorem,
equality classification, original or whole-mask closure is asserted.
No Lean, Lake, compilation or CI was run.
