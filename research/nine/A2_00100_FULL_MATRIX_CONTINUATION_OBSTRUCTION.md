# Complete full-matrix check of the remaining 178 original cells

This is a negative discovery result, not an additional proof closure.
The accepted checkpoint remains **53 of the original 231 cells closed,
178 open**, within the still-open original-nine `001/00` mask.
No new mask, positional root, or roadmap gate closes here.

After freezing that checkpoint, every remaining original cell was tested
once with the full version-14 linear relaxation. This retained all 128
exact rational corner-support directions and all primitive corner-support
rows that the sparse discovery accelerator omits. The original nine
frames, original caller hypotheses, shared variables, chosen physical
separators and all inherited necessary rows were unchanged. No upper/upper
guard, new threshold, new geometric premise, or subdivision was introduced.

## Complete bounded result

| Item | Result |
|---|---:|
| Original cells attempted | 178 of 178 |
| Additional entire original cells closed | 0 |
| Cell timeouts | 0 |
| Rejected candidate certificates | 0 |
| Cells returning a relaxed center proposal | 178 |
| Original cells still open | 178 |

The run completed in approximately 83 seconds. Numerical LP proposals
are neither exact feasible packings nor proof certificates. The claim
here is only that this complete stronger direct pass found no further
contradiction. Its source and output are `computer_assisted/dense_original_cell_pass.py`
and `computer_assisted/dense_original_cell_report.json`. The hash inventory is
`computer_assisted/dense_original_cell_manifest.json`. To rerun this discovery
pass, extract the accepted checkpoint archive beside the script so its
`whole_cell_payload` directory is present. SciPy and NumPy are required for
discovery; exact certificate replays use the frozen standard-library verifier.

## What remains unresolved

The unresolved full-domain question includes the simultaneous placement
of both unselected original squares. The selected-seven obstruction proves
that some omitted-original information is necessary; it does not prove that
each omitted original is individually indispensable. Strengthening circle-support directions alone
did not resolve any surviving whole cell. Inspected normalized deep-cell
proposals violate several original physical separation conditions; they
do not provide counterexamples. Broad angle/center intervals still allow
relaxed bilinear products and different unresolved physical separator
choices. The existence of an LP proposal therefore leaves the nonlinear
original-nine question unanswered.

The independent all-seven obstruction supplied by the global worker is
more decisive about scope: for each of the 24 open masks there are seven
physical selected originals at `q <= 17/4 < 1105/256`. Thus no argument
using only those selected seven, without a necessary consequence of the
two other originals, can close any remaining whole mask. In particular,
`111/00` is not an easy seven-original escape route.

The next justified alternatives are a complete all-nine placement/capacity
argument on this fixed domain, or a separate full-nine mask such as
`101/00`, where both weak outer ends can be used together. There is no
evidence here that `101/00` is easier, and its seven-original relaxation is
also feasible. The incomplete upper/upper guarded intersection experiment
and rotated-chain escape experiment remain research; neither is added to
the immutable 53-cell proof package or counted as a whole original-cell
closure.

No Lean, Lake, or CI was run.
