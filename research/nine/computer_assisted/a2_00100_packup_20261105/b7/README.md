# B7 verified prefix and bounded diagnostics handoff

The latest fully replayed B7 cover is `component156_one`: 1011 nodes, 543 excluded terminal domains, 43 OPEN terminal domains. Its only changed node is 871, with one new round containing 160 exact bound deductions. Every original complement and the seven previously completed components 4, 260, 814, 816, 818, 820, 993 remain. B7 itself remains OPEN; this handoff gives zero original or mask credit.

`inputs.tar.xz` is a content-addressed thin delta. `INPUTS.json` binds each original native path either to a retained new blob or to a byte-identical member of the already published B7 packet or B16 prior. Both published archives are dependencies, not duplicated here. `ARCHIVE_PARTS.json` and `PUBLISHED_PRIOR.json` provide exact archive and part identities; the checkpoint is published at commit `38b47f293ba6dec51f2abf7d6c2738d427742059` under `research/nine/computer_assisted/a2_00100_b7_completed_components1011_checkpoint_v1`. The prior directory is named in `MANIFEST.json`.

The exact report and receipt for the 160-deduction prefix are retained byte-for-byte, together with the published-baseline fresh replay report, numerical drivers, source bindings and logs. The accepted full replay was performed before packaging. Packaging and restoration verify bytes and coverage identities; they do not claim another cold full exact replay.

The three other complete graph files are search diagnostics, not newly accepted proof trees. Their new node payloads are retained too, so no candidate bytes are lost:

- `component156_sat256`: 136 new nodes, 1500 underlying LP calls, 1147 nodes total, 618 candidate exclusions and 87 OPEN leaves. No original target closed.
- `component813_ci16`: 16 new nodes, 309 underlying LP calls, all 16 new domains OPEN; 1027 nodes total, 543 candidate exclusions and 57 OPEN leaves.
- `component156_angles96`: 96 new nodes, 1467 persisted underlying LP calls, 1107 nodes total, 552 candidate exclusions and 82 OPEN leaves. The two selected original residuals still contain 41 OPEN domains; normalized frame defects migrate between different squares.

The finite next plan is explicitly **not started** because the user requested handoff: in `component156_sat256`, retain the full prior cover and target only node1013's two OPEN alternatives1051 and1055. Try a complete angle cover, at most32 new children and600 persisted underlying LP calls, with zero bound rounds. Node1013 and those two alternatives are not certified complete. An exact replay of the candidate SAT cover and any successful new attachment is required before acceptance.

To check this delta against already extracted published inputs:

```sh
python -B -S restore_thin_handoff.py --packet /path/to/b7_selected1011_open_packet_v1 --prior /path/to/b16a_I32_complete_H_checkpoint --verify-only
```

To restore all retained variants and source aliases into a fresh dedicated directory, replace `--verify-only` with `--destination /path/to/new/b7_handoff`. The helper preserves all frozen source bytes and prints the full exact replay command. It generates a relocation wrapper for the existing independent replay entry point; no numerical search starts during restoration.
