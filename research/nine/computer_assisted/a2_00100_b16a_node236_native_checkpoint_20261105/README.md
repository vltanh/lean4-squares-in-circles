# B16 node236 complete conditional exclusion

The whole physical region identified by native adaptive SAT node236 is excluded. The unchanged independent rational tree checker returned `PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE`: 11 nodes, five complete angle unions, six excluded terminal regions, zero OPEN regions, no new bound rounds, and 335 local printed rows. Its full initial path is retained in `EXACT_REPLAY.json`, with all 21 path entries and the 18-step exact ancestry certificate.

This is a conditional subregion of original `negative-16a2fc93c8d133f0`, inside the merged closed I21/I22 rectangle. It additionally fixes inherited proxy/angle branches and the physical H/I, B/I, and A/H SAT alternatives printed in `SOURCE_NODE236.json`. This packet does not close node206, the entire merged I21/I22 region, original B16, or any mask. The other fourteen original I rectangles retain their existing proofs; this packet does not re-partition them. Original-cell and mask credit are both zero.

The complete refinement uses exact slope cuts: G at −1/2; on its lower half I at −1/2; on I lower, H at −9/16; on I upper, C at −5/16; on the surviving C upper half, H at −9/16. Both closed halves are retained at every split. The six terminal contradictions have positive exact rational reserves reconstructed from accepted physical rows. Numerical points only chose cut locations. No stronger terminal premise or chosen central-pair assumption is used.

`INPUTS.json` maps every retained absolute native input path to a content-addressed blob in `inputs.tar.xz`. The archive is read back and every member digest checked when packaged. It includes all checker-retained source, certificate, geometric-premise and ancestry bytes, plus the packaging script. This is a native input bundle, not a standalone cold-portable replay claim. Restore it only through a separately reviewed native restoration process.

Native replay command after the listed paths exist:

```sh
python -B -S /workspace/scratch/f9f48fcfb253/b_work/verify_b_accepted_center_disk_tree_v1.py /workspace/lean4-squares-in-circles/research/nine/.runs/b16_geometry/complete_node236_tree/manifest.json /tmp/b16_node236_replay.json --packet /workspace/scratch/f9f48fcfb253/b_work/b16a_I32_complete_H_checkpoint --cap-proof-dir /workspace/scratch/f9f48fcfb253/b_work/recovery_20261105/extracted_b340/unpacked/b340_complete_original_package/accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1
```

Discovery used 189 counted native LP calls after the first two uninstrumented phase searches. No bound rounds were run; these numerical counts are not proof premises. Fresh independent manuscript/attachment review is pending when this bundle is produced.
