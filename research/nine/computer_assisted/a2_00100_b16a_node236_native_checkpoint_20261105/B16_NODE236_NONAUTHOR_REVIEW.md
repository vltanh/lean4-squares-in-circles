# Non-author review of B16 conditional node 236

Review date: 2026-11-05. Result:
**PASS_COMPLETE_CONDITIONAL_COMPONENT_NONAUTHOR_REVIEW**.

The exact region represented by frozen native node 236 is completely
excluded. Its refinement has eleven nodes, five complete closed slope unions
and six excluded leaves, with no OPEN leaf. I found no mathematical,
attachment, coverage or byte-binding defect in this stated result.

This is a conditional component of original `negative-16a2fc93c8d133f0`
inside the merged I21/I22 rectangle. It does not close node 206, that merged
rectangle, the original or a mask. **Original-cell and mask credit are zero.**
This review was performed by an agent that did not author the component.

## Exact reviewed objects

The native packet is
`research/nine/.runs/b16_continue/node236_native_package/`.

| File | SHA256 |
| --- | --- |
| `MANIFEST.json` | `2faded180cd56365ee0b0723856f960cd00460dbf6a91ce5813b272ae58efc42` |
| `README.md` | `2dfa25e585b066374a6d24ec8159b6f665e274a7d08c3b9d5cf8938e5d5f2c9d` |
| `TREE_MANIFEST.json` | `28ff378d53a57bf25fea1b43faf2a2fd07307b33927cb45cd2fdcbe53861233a` |
| `ANCESTRY_PREFIX.json` | `e5a858f51e41475902275b97743a7aed29218ec6df287524b8b1dc6658cc422e` |
| `SOURCE_NODE236.json` | `e57a38ef886af1f6667da5a65ab9279e6f1e7abcc133005ad663a1600293b94b` |
| `EXACT_REPLAY.json` | `a3fec7f6661e4c5f536986528eaac4652fba0dc6991de918ada4365f023ad4e5` |
| `INPUTS.json` | `6e08800bc5d0fd6e479d8a43b19e02857d9dfd51eff152771ee5508ab9a8a1d7` |
| `inputs.tar.xz` | `7c5e9ff2a308804adf05351ed635fd48bbe1d45356572cfc26be6fb9ecff0026` |
| `package_node236.py` | `ce7aabcde06bb349e714e5ac404939706f882560fa925e4a3add8ef98069367c` |

The tree manifest and ancestry are literal copies of
`research/nine/.runs/b16_geometry/complete_node236_tree/manifest.json`
and `node236_ancestry_prefix.json`. The full report has the first tree
manifest's hash as its certificate identity and explicitly says
`PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE`, `complete=true`,
`whole_original_proved=false` and
`entire_registered_original_domain_retained=false`.

## Attachment and inherited physical scope

The ancestry begins at `B16A_MERGED_I21_I22_RESTRICTION.json`, SHA256
`142b74254b59e00267298ea59fa27bef68b392a220f9509aa4a88221f514d5cc`, under
`/workspace/scratch/f9f48fcfb253/b_work/`. This is the same accepted closed
rectangle used by the earlier reviewed B16 checkpoints:
`x_I in [-163627/2097152,2457813/4194304]`,
`y_I in [-91/120,91/120]`, with all original physical premises and strict
`q < 1105/256`. No equality conclusion is supplied.

There are eighteen ancestry records and 21 entries in the resulting initial
path. I independently reconstructed each selected restriction from the prior
record's certified final state and checked exact equality with the next
record's initial state. The permitted restrictions append only the stated
proxy, original physical SAT or closed slope selection. All other state is
retained. The original nine squares, corner/pair premises, marked cones and
links, and strict weak CD are inherited unchanged.

The first fifteen records, at native indices
`0,4,7,9,11,14,15,16,17,18,65,67,69,71,73`, are literally identical to the
previously reviewed 203-node checkpoint. I checked that checkpoint's manifest
hash, every payload hash and the earlier review-report hash before reusing
its arithmetic. Node 188 retains its exact old initial state and appends two
certified bound rounds. The remaining ancestry records are 206 and 236.
I freshly replayed those three changed records: two rounds, 350 deductions
and 1,923 printed-row occurrences. The unchanged merged-parent and fifteen
old record computations were not repeated.

The final three physical SAT restrictions are H/I with owner H, axis 0,
positive sign; B/I with owner B, axis 1, positive sign; and A/H with owner A,
axis 0, positive sign. These are explicitly conditional cases, not assumptions
asserted for every packing. Their state, together with the earlier proxy and
slope restrictions, is exactly the saved node 236 state. The saved node's
bytes match its entry in the frozen source manifest, SHA256
`0a33b8c35e839a93ab534c858ab7d43b8dbb51d9fc9aa9917ef4bd07fa5100da`.
The last ancestry final state is exactly the complete subtree's root state.

The frozen source manifest still marks sibling 242 OPEN. The continuing
discovery run may modify its live files; this review attaches to the frozen
node and source snapshot, and makes no claim about later live search states.
In particular, closing 236 alone provides no closure of its parent 206.

## Complete closed refinement

The five exact splits are:

| Internal node | Original slope | Cut | Both child nodes |
| --- | --- | --- | --- |
| 0 | G | `-1/2` | 1, 2 |
| 1 | I | `-1/2` | 3, 4 |
| 3 | H | `-9/16` | 5, 6 |
| 4 | C | `-5/16` | 7, 8 |
| 8 | H | `-9/16` | 9, 10 |

My structural walk checks that every cut is strictly inside its parent
interval, reconstructs both closed halves, checks all other state literally,
visits each indexed node exactly once and verifies all payload and
parent/depth/choice bindings. Internal closure follows only after both
children close. Thus the six terminal domains cover the entire conditional
root, including every shared cut face. No further bound round is used inside
the eleven-node refinement.

All six leaves, at indices 2, 5, 6, 7, 9 and 10, close by positive exact
rational reserve. Their respective printed-row counts are
56, 61, 56, 52, 58 and 52, totaling 335. I separately recomputed every positive
integer-over-2^40 weight, coefficient sum, RHS, absolute-variable residual
bound and strictly positive reserve using Fraction arithmetic. The full
rational reserves are recorded in the review JSON.

I also freshly executed the existing independent physical row checker for
all eleven records. Every printed necessary premise is reconstructed and
every variable bound is checked. The resulting inequality `c*z <= b` is
inconsistent with `c*z >= -sum(M_j*abs(c_j))` because
`-b-sum(M_j*abs(c_j)) > 0`. The rows use already accepted physical families;
no additional central-pair or geometric classification assumption is introduced.
Numerical points and defect values only selected rational cuts and are not
used to validate exclusions.

The exact engine checks frame, support, corner, separating, product and other
accepted necessary rows through its existing independent decoders. This
review reuses their accepted physical derivations rather than claiming a new
implementation or proof of each family. The new conditional replay rechecks
48 adapter-retained pins; the larger complete report/source inventory is
also independently rehashed. No NumPy, SciPy or HiGHS module is imported by
the review run.

## Native transport and manuscript scope

I rehashed every outer-manifest file and every indexed native source. The
4,832,040-byte archive has 286 unique blobs representing 295 native paths.
Every compressed member was read: each is a regular `sources/<sha256>` file
of the declared length and digest, with no missing, duplicate or extra member.
Every source pin in the full exact replay report was also rehashed. The
review JSON records 304 exact identities including the nine outer packet
files and all indexed native sources.

The README accurately distinguishes the complete conditional component from
the remaining merged region and original. It correctly describes the five
cuts, six terminal contradictions and numerical discovery boundary. Its
statement that review was pending was accurate when these exact bytes were
produced; this separate report supplies the later scoped review.

The archive is a native recovery bundle. This review does not assert that its
checker-retained inventory enumerates every file opened transitively by
ancestral loaders, and it does not test a fresh isolated restoration. Earlier
accepted proof packages remain dependencies. No standalone cold replay,
human/kernel verification or whole-proof audit is claimed. No Lean, Lake,
compilation or CI was run. The original/mask register remains 224/231 and
8/32 CLOSED.

## Reproduction

The review command, with the exact native paths restored, is:

```sh
python -B -S research/nine/.runs/review_continue/review_b16_node236.py
```

It imports `review_b16_checkpoints.py`, SHA256
`fb78dac04f3b9177f97a5d78e731b3d0ffb683c63f23b54ea1e2d89587d5b5c8`,
and reuses `B16_CHECKPOINTS_NONAUTHOR_REVIEW.json`, SHA256
`0cf2119730030a434e6b10ba720ff1da48eb21bb1024b04a63b03f191827e79a`.
The companion structured result and raw log record all new record audits and
literal reserves. This command is native-only, not a cold-install command.

Review script SHA256:
`e576d9f98995067c21b45a072a1fd15f9d8df6ba1284cf4db1a134e297dc2215`.
`B16_NODE236_NONAUTHOR_REVIEW.json` SHA256:
`1bbd9598e953e501c31dac2d0c5be8e4591c30b6c6bf245651425b59587f7478`.
`b16_node236_review.log` SHA256:
`ee89a82735897bed855f3573e2135c1a02351e5324ae8faadf985ca04c433542`.
The final audit run took about eleven seconds.
