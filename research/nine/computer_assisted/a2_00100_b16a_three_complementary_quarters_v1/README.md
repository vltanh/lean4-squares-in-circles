# Three complete complementary B16a original quarters

**I20, I31 and I33 are completely excluded. B16a remains OPEN.**
These proofs restore reproducible complementary pieces of the existing
sixteen-rectangle original cover. They add zero original-cell or mask closures.
The remaining B16a domain is the whole merged I21/I22 rectangle under the
unchanged original path and all original physical predicates.

Read `HAND_PROOF.md` for the complete original-domain attachment and physical
argument, `COMPLETE_TERMINAL_TABLE.md` for all 23 leaves, and
`ROOT_HAND_TABLE_REVIEW.md` for the independent cover and literal arithmetic
review, including twelve explicit short interval contradictions.

The complete three-quarter proof has 31 nodes, six complete inset unions,
two complete closed angle unions, 19 retained rounds, 2,919 rational deductions,
6,943 printed rows and zero OPEN leaves. Its fresh portable replay retains
360 new packet inputs and 507 hash-pinned accepted prior inputs. All nine
original frames, 36 corners, 36 pairs, five cones, strict-radius scope and
exact mask predicates remain present. No Lean, Lake or CI was run.

## Availability of the other complementary pieces

At this publication, six earlier whole-quarter proofs and these three new
proofs are preserved in published source packets. Five further quarters
I00/I01/I02/I03/I30 have already been reconstructed and replayed locally;
their source-complete supplemental publication is being prepared. Thus the
local reconstructed inventory has fourteen exclusions, while this release
alone brings the published reproducible inventory to nine. The older
historical count is not used in place of missing source bytes. All sixteen
whole-quarter proofs remain required by the unchanged original assembly.

## Reproduce the exact proof

Verify the part hash against `ARCHIVE_PARTS.json`. The sole part is already
the complete xz archive; extract it to obtain `b16a_complementary_package_v2`.
Reassemble and extract the already published B16a I32 prior identified by
`PUBLISHED_PRIOR.json` as the sibling directory `prior`. Its archive SHA256 is
`c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`.
From the extracted new packet, run:

```sh
python -B -S code/replay_b16a_complementary_packet.py --prior ../prior --output ../fresh_replay
```

The result must be `PASS_PORTABLE_THREE_COMPLETE_ORIGINAL_B16A_QUARTERS`,
with `whole_original_proved=false`. The exact checker reconstructs all whole
quarter attachments and complete trees. It accepts no saved PASS as arithmetic.

The separate root literal audit can be repeated with only this publication
script and the extracted new packet:

```sh
python -B -S audit_b16a_complete_quarter_tables.py --packet /path/to/b16a_complementary_package_v2 --output /path/to/root_table_audit.json
```

This second command checks the finite cover and all displayed terminal sums;
it relies on the full portable proof for the preceding row-validity and bound
induction and does not replace that proof. The archive itself contains every
literal certificate and all required unchanged checker sources.
