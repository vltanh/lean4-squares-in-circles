# Stopped-work recovery bundle

All searches stopped at the user's request. This bundle grants zero original
or mask credit. See the [main handoff](../../HANDOFF_2026_11_05_PACKUP_AND_NEXT_TASKS.md)
for remaining tasks and acceptance requirements. Alternative covers overlap;
their counts are not additive.

| Directory | Retained scope | Acceptance status |
| --- | --- | --- |
| `a_c744` | Complete subcovers of A167 leaves144/151; latest151 has25 nodes,18 excluded,4 OPEN | Fresh exact subcover replays; original OPEN |
| `b16_stopped192` |281 nodes,133 excluded,77 OPEN | Fresh exact partial replay; separate manuscript review not claimed |
| `b7` |Strengthened871 prefix and three diagnostic deltas | Accepted prefix replay; diagnostic exclusions remain candidates |
| `b462` |Whole-original145 snapshot and separate complete93 proof | Exact replays pass;91/93 non-author reviews and93 merge pending |
| `cb882_discovery` |Stopped306-record continuation of148 | Candidates only; new full-tree arithmetic replay pending |
| `c191_candidate` |Signed-height upper3/8 variant,32 roots/34 boxes | Producer checks only; independent proof/guard/terminal pending |
| `reviews` |Completed common-decoder review and review handoff | Scope stated in each report |

The separately published [B16 region188](../a2_00100_b16a_node188_native_checkpoint_20261105/PUBLICATION.md)
and [Cb882177 input](../a2_00100_cb882_signed_177_completed_input_v1/README.md)
are reviewed complete components. None closes an original.

For the three native packets `b16_stopped192`, `b462`, `cb882_discovery`, run:

```sh
python -B -S verify_native_packet.py SUBDIRECTORY
```

Add `--restore` to install missing exact native paths; conflicting existing
bytes are rejected. This verifies transport, not arithmetic. Published
ancestral proof archives remain dependencies; these maps do not claim to
enumerate every file opened transitively. The A/B7 thin archives retain their
own extraction maps and published-base dependencies.

For B7, first extract `b7/b7_verified_prefix_handoff_v1.tar.xz` to a fresh
directory, then run its restoration helper there. The copied README/JSON/Python
sidecars here are for inspection; the outer archive also contains the required
thin input archive. Do not run the helper on the sidecars alone.

The Cb882 candidate's latest native manifest is
`research/nine/.runs/root_cb882_continue/cd148_finish_five/MANIFEST.json`:
306 processed records,159 candidate exclusions,17 pending and11 stopped
domains. Four new pending cases328/330/365/366 remain below218; all original
complements remain. The latest candidate has not received full arithmetic
replay. Its archive includes the frozen138-node base, fresh baseline report,
all discovery stages, exact source maps and budget records. The last two
angle allocations each stopped at1500 actual native calls; earlier attempts
are separately recorded.

No Lean, Lake, compilation or CI was run. Accepted historical inputs remain
unchanged. `FILES_SHA256.json` records all files in this bundle at publication.
