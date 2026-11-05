# C887: fresh independent replay of whole-original starting bounds

The source packet in commit 4efd616976b22fb3dd1802a0314deba461753099
(`c887_fresh_original_starting_state_v1`) has now passed root source/physical
review and a fresh independent exact replay. This folder preserves all seven
fresh output files, including the original-prefix and accepted-height child
reports, full whole-state report, raw logs and observed execution receipt.

The fresh proof reconstructs the original C887 prefix and its accepted height
consequences, then six root rounds with 624 deductions and 1,288 printed rows.
All eight physical D/G alternatives start from the same parent. Four are
excluded and four survive. Their coordinatewise hull supplies necessary bounds
on all 207 original slope, center, frame, pair-difference and diagonal intervals;
165 intervals strictly improve the earlier target. The parent's original ID,
path and choices are restored, and no child SAT auxiliary crosses the union.

The missing older strong-box archive supplies no premise. The earlier target
is used only as a weaker statement, with exact containment checked separately.
The source bytes and all 557 native inputs were checked before and after the
fresh replay; the certified hull matches the published hull exactly. The fresh
process exited zero. The accepted general cone, rotating center cone and
incircle families are reconstructed independently; no tangent row is used.

`root_review/replay_external_c887_fresh_bounds_v1.py` preserves the native
command and full input binding. The already-published source archive and its
explicit native dependency aliases are still needed. No cold standalone
replay is claimed. A peer's read-only source/hull audit and its corrected
metadata-only preparation harness are also preserved.

These are whole-original necessary bounds, not an exclusion. C887 and its
mask remain OPEN. Totals remain 222/231 originals and 8/32 masks CLOSED.
No numerical optimizer, Lean, Lake, compilation or CI was run.
