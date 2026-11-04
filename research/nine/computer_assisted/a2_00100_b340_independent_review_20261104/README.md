# Independent replay and physical review of accepted B340

The complete original `negative-34029ea8b047982f` was published in
`ec6b94cb69ef994fcaf44961de7005faaca8a84c` while this independent review was
in progress. That commit advances 220/231 to 221/231. This supplement
accepts the same proof, preserves its immutable packet, and adds **zero**
further original cells or masks. The live counts remain **221 CLOSED /
10 OPEN** and **8 masks CLOSED / 24 OPEN**.

[Accepted whole-original proof](../../A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md) ·
[Complete source packet](../a2_00100_b340_complete_original/ORIGINAL_PROOF.json) ·
[Fresh exact receipt](ROOT_PORTABLE_RECEIPT.json) ·
[Physical hand/table review](PHYSICAL_REVIEW.md) ·
[Complete parent-cover review](WHOLE_PARENT_COVER_REVIEW.json)

## Fresh arithmetic and complete original coverage

A new isolated replay reconstructs every bound, terminal and complete cover
in the 403-node tree. All 279 leaves close. The same 47 four-way inset
unions, ten eight-way physical separating unions and 67 two-way closed
slope unions retain every original domain and shared boundary face.

The replay checks 400 bound rounds, 67,336 exact rational deductions and
203,189 printed-row occurrences, including 4,173 terminal rows. It rehashes
all 726 packet inputs and 507 pinned prior inputs before and after the run,
forbids reads from the previous workspace and imports no numerical solver.
Its receipt reports `PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`
in 715.848507849 seconds. `REPLAY_COMPARISON.json` checks agreement with the
published proof on every mathematical tree, leaf, bound-audit and physical
row-count field; different local source-path aliases do not change any
of those fields.

The separate whole-parent audit reconstructs the immutable registered
definition and compares all 231 ID/sign/index/path tuples. It checks every
node hash, exact state inheritance, complete sibling set and closed slope
face, visiting every node exactly once. It permits a current CLOSED status
when rerun after acceptance, while retaining the frozen pre-acceptance OPEN
snapshot. The original, mask and all physical caller predicates are unchanged.

## Independent physical and literal checks

`PHYSICAL_REVIEW.md` gives direct continuous derivations of the four-product
original-corner rows, frame and projection Gram rows, disk supports and
the rational residual-payment rule. Its separate source program imports
neither the producer nor the mathematical checker. It independently checks:

| Check | Occurrences |
|---|---:|
| Original-corner disk supporting rows | 77,352 |
| Physical frame Gram rows | 4,482 |
| Four-product corner rows in bound rounds | 14,386 |
| Grouped corner rows in bound rounds | 7,458 |
| Projection Gram rows in bound rounds | 2,905 |
| Affine terminal sums with every coefficient residual paid | 181 |
| Terminal-table rows matched to literal leaves | 279 |

The remaining interval-dependent terminal rows are reconstructed with their
independently propagated intervals in the full exact replay. The physical
identities hold on every closed interval and degenerate face. The four
independent product-plane choices are simultaneously valid inequalities,
not an incomplete geometric split. Gram parameters need no numerical
eigenvalue or positive-semidefiniteness assertion.

All 181 affine terminal reserves are independently recomputed and positive.
The smallest, at node 306, is

\[
\frac{151733336600989615520443323263491089484860283}
{10676154221601432410482833817168273548178505072640}
>\frac1{100000}.
\]

The other 98 leaves have exact original center/angle/frame contradictions.
No sharp or full-angle conditional row terminal is used. Every coefficient
and rational multiplier remains in the accepted archive; the complete
Markdown terminal table indexes those literal records.

## Archive identity and reproduction

`ROOT_ARCHIVE_AUDIT.json` independently checks all seven ordered parts and
all 730 members of the 53,274,488-byte accepted archive, SHA256
`b4b3db56da2b3ac7a006d8c8e1060d07e4ab0103070fdce88c7611c74744569f`.
This transport audit is distinct from arithmetic replay. The accepted
archive is not duplicated or changed by this supplement.

Follow the extraction and full-replay command in the accepted proof. With
the extracted packet and prior present, the additional structural audit is:

```sh
python3 -B audit_b340_whole_parent_cover.py \
  --packet /path/to/b340_complete_original_package \
  --prior /path/to/b16a_I32_complete_H_checkpoint \
  --output /path/to/new_cover_review.json
```

The optional `--register` argument checks the current status register;
without it the pinned pre-acceptance snapshot is used. The physical-literal
audit takes `--packet` and `--output` paths. Both review sources and their
bound reports are preserved here.

All nine original squares, 36 corners, 36 physical pairs, five cones and
exact marked predicates remain in the proof for the original strict-radius
scope. There are no new mandatory gates, original-cell IDs, masks or
positional-root IDs. No Lean, Lake or CI was run. This is independent
computer/agent review; no proof-kernel or human verification is claimed.
