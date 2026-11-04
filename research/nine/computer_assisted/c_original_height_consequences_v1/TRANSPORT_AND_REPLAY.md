# Final C portable transport and exact replay

The immutable mathematical delta is `delta_v7`. Its assembled input manifest is SHA256 `06115f494173bc344821932525d7a8522df8ea2ed80b400f735f3b68d4a1b58b`; its thin release manifest is `297eee1bae8caa4b2dd85d0af9544586773c6fa0cb8e4508629b9481f0f80e30`.

The final launcher is `replay_portable_c_height_packet_v3.py`, SHA256 `d7d9b17da9091cb7920e5964618303c93ae2689a8528381091b35f3ee4c2cb28`. The final builder is `build_compact_c_height_packet_v7.py`, and the materializer remains unchanged. Use Python 3.12 with assertions enabled and both `-B` and `-S`. The tested path joins rely on Python 3.12 behavior.

## Immutable inputs and exact path identities

The remote delta contains 172 new mathematical files, totaling 143,575,284 bytes. Materialization reuses all 1,380 published A payload members and 456 Cb882 members. Every overlap preserves the already-selected C hash; conflicting hashes are rejected. The complete assembled inventory contains 2,015 files and 687,782,645 bytes. Unused base members are inventory-only, not proof premises.

All mathematical source and certificate bytes remain unchanged. The filesystem facade transports exact inventoried absolute filenames and directories. The JSON facade transports only complete string values equal to those aliases, and dictionary keys only for explicit file aliases. It preserves unknown and embedded paths, rational coefficients, endpoints, indices, frame labels and predicates. The map is injective and rejects key collisions. Raw read_bytes and SHA256 checks are unchanged.

## Read-only packet and generated reports

Every isolated child installs the same guard. Both logical paths and resolved targets are checked. All packet writes and mutations are forbidden, all packet reads must be inventoried, and reads through output symlinks must remain within fresh output. Unbound workspace reads and numerical imports are rejected. Bytecode probes are routed into output, with writes disabled.

The unchanged archived checkers write diagnostic reports under their own `new_reviews`, `diagonal_replay_reports` and `replay_reports` directories. The launcher routes the seven known output subtrees into fresh output through 21 explicit directory/file aliases. Each entire subtree is proved disjoint from every frozen input, and output aliases do not overlap input aliases. Both direct Path constructions and HERE / folder / filename joins were exercised. Unknown raw packet writes remain forbidden.

The archived strict read guards remain unchanged. The assembled packet and output are under `/tmp`; the outer guard independently blocks all unbound workspace reads in every child. Subprocess commands must use the same Python executable with both `-B` and `-S` and an inventoried script, and re-enter this launcher.

## Final exact result

`fresh_replay/PORTABLE_RECEIPT.json` has status `PASS_FRESH_PORTABLE_C_HEIGHT_CONSEQUENCES_AND_SHARED_BOUNDS` and SHA256 `0ec2356ee2becd7b1b56c80929f7dab6dfcf7ae272b85ce990a6e454e621fe8d`. The fresh run took 330.58 seconds and rehashed all inputs at completion.

It freshly replayed C887 branch7 and Cb882 branches4/7 with the frozen older source checkers. The unsplit C887 root passed six rounds, 416 deductions and 858 printed rows, including two weighted uses of the height consequence. The 91-node first-use cover passed 57 rounds, 8,780 deductions and 39,146 printed rows, including fourteen weighted shared-root bounds and 783 four-product corner rows. Its 73 leaf domains remain explicitly OPEN; the publication does not claim either original is excluded.

Final transport controls passed eleven positive checks and twelve rejected access/mutation cases. Separate output-join controls passed 49 positive checks and seven rejected raw packet writes. All saved PASS reports are records of these fresh executions, never replacements for source replay.

The package proves three necessary whole-original height inequalities and 414 original-variable bounds for C887. It awards zero original-cell or mask credits. The live A1 and C887 numerical searches remain separate from these frozen inputs.
