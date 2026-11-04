# A c744: portable OPEN checkpoint

This checkpoint preserves exact, independently replayed work inside the unchanged
original `positive-c744bc031d40ee64` of mask `001/00`. The original remains OPEN.
It adds zero original-cell, mask, positional-root, or roadmap credit. The stable
ledgers remain 220/231 closed originals and 8/32 closed masks.

The original path is
`[["angle",3,1],["angle_cut",[0,"0"],0],["inward_row_escape",[7,8],[4]]]`.
All nine physical squares, all 36 corners, all 36 physical pair conditions, all
five marked center cones, the actual AB/BC/EF/FG links, and the strict weak CD
link are retained. The radius-square bound is `1105/256`.

## Complete declaration and necessary inequalities

The accepted actual-AB two-link theorem and its closed complement declaration
give five complete alternative domains. Complement 0 is now excluded by a
complete 41-node physical tree with 31 excluded leaves, ten complete four-way
proxy covers, 1,154 exact deductions and 1,385 printed row occurrences.
Complements 2 and 4 are excluded directly by the independently checked original
parent bounds. Complements 1 and 3 remain OPEN.

These completed exclusions give three necessary inequalities on the entire
unchanged original domain:

- `x_B - x_I <= 0`;
- `y_B - y_D <= 3/5`;
- `y_B + y_D - 2*y_I <= 3/5`.

They are weak closed negations of excluded closed alternatives. Retaining an
excluded equality face enlarges the necessary domain harmlessly. Only those
three inequalities are transported. No branch-specific SAT choice, auxiliary
value, child interval, or producer endpoint becomes an original-domain premise.
The independent consumer first replays the complete original declaration and
the source exclusions with older checkers that cannot use these consequences;
the dependency is therefore acyclic. The complete derivation is preserved as
`A_C744_COMPLEMENT_CONSEQUENCES_HAND_PROOF.md` in the frozen packet payload.

## What the fresh portable replay establishes

| Component | Tree nodes | Excluded leaves | Explicit OPEN leaves | Scope |
|---|---:|---:|---:|---|
| 0 | 41 | 31 | 0 | Complete complement |
| 1 | 49 | 0 | 38 | Selected partial path cover |
| 3 | 165 | 115 | 17 | Partial complete-domain cover |

The component-3 replay checks 26,869 deductions and 46,885 printed row
occurrences. Its first four-product use contains 387 such occurrences, together
with 3,146 older grouped unit-frame corner rows and 12,406 ordinary corner-disk
rows. A row occurrence is not a new domain or a closure. The component-1 sample
is deliberately smaller than the continuing live search; it carries no claim
that its still-open alternatives have been excluded.

For one original corner, the four-product rows expand its actual squared norm
as `x^2+y^2+1/2+eps*alpha*x+tau*alpha*y+eps*beta*y-tau*beta*x`.
Each signed bilinear product has either of its two valid endpoint lower planes
on the current independently proved rectangle. The sixteen combinations are
simultaneously valid inequalities, not sixteen disjoint alternatives. The
residual is the sum of two center-tangent squares, four nonnegative rectangle
products and the original physical disk slack. The earlier committed
`four_product_corner_rows_v1` hand proof and independent reconstructor are
retained byte for byte in the payload. Every used row is reconstructed at the
current independently propagated state.

The completed portable run checked 1,384 immutable inputs totaling
468,599,561 bytes and 1,488 explicit filename/directory aliases. Every exact
child runs through the same restricted launcher. Old-workspace reads, unlisted
packet reads, frozen writes, numerical imports and unapproved subprocesses are
rejected. All mathematical source bytes, predicates, intervals, coefficients
and multipliers remain unchanged. The two valid and eight rejected transport
controls are included. The root separately reviewed the complete launcher and
physical attachment mechanism. The execution receipt records the fresh
independent arithmetic; publication adds an archive-wide byte audit, not a
claim to a second full arithmetic replay.

## Reproduce

Concatenate the archive parts in `ARCHIVE_MANIFEST.json` order, verify its
SHA256, and extract the xz tar. From the extracted directory run:

```bash
python -B -S packet/replay_portable_a_c744_packet.py --packet packet --output ../fresh_a_c744_open_replay
```

Use a new output directory. The replay checks hashes before and after each
isolated exact child and writes `PORTABLE_RECEIPT.json` only after success.
It needs Python's standard library and does not run a numerical optimizer.
`RELEASE_MANIFEST.json` inventories every archive file except itself; the outer
archive manifest pins that release manifest and every compressed part.

No Lean, Lake, or CI was run. This is a durable OPEN research checkpoint.
The live continuation must still close both remaining complete components,
pass the unchanged whole-original assembler, and pass a fresh portable complete
replay before any original-cell credit can be awarded. The PR remains draft.
