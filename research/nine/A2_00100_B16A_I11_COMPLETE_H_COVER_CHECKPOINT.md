# Exact complete H cover of the B16a I11 rectangle

This packet proves that the fixed I11 rectangle of the original cell
`negative-16a2fc93c8d133f0` contains no physical configuration. It covers all
eight H rectangles, including every touching face. It closes one conditional
I rectangle and awards **zero original-cell and zero mask closure credit**.
The other I rectangles remain separate obligations.

## Unchanged original caller

The original path is literally

```json
[["angle",3,0],["angle_cut",[0,"0"],0],["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[3]]]
```

The frozen whole-original prefix has SHA256
`69ddd2dcc5383c3259187588a890ddadb4a6545e8bdcc11e653bdfb8bb6b3886`.
Its independent replay reconstructs the original path, all nine physical unit
squares and their independent frames, and the inherited pair constraints.
It verifies the earlier 30 coordinate deductions and then all 199 deductions
in five rounds, using 582 printed rows. The original strict C–D predicate is
retained. No point surrogate replaces a physical square.

Let the independently proved whole-prefix center intervals be the parent
boxes. I11 is the second closed quarter in each coordinate of I. Its exact
rectangle is

\[
x_I\in[-3112321/4194304,-163627/2097152],\qquad
y_I\in[-91/120,0].
\]

The original H parent box is

\[
x_H\in[-1474347/1048576,17/64],\qquad
y_H\in[-120173/655360,311927/262144].
\]

For an interval \([a,b]\), its closed part \(k\) out of \(n\) parts is
\([a+(b-a)k/n,a+(b-a)(k+1)/n]\). Split H's first interval into two parts and
its second into four. The eight Cartesian products cover the entire H box.
Adjacent products share their boundary; no equality face is discarded.
Every other original bound remains in force in every product.

## Complete table

The table uses H indices after the common I indices `(1,1)`. Every displayed
positive bound is a rational lower bound on the exact residual-paid reserve
stored in `COVER_TABLE.json` and the replay report.

| H part | Independently checked terminal | Local bound rounds | Reserve at least |
|---|---|---:|---:|
| `(0,0)` | All four original H–I inset separation options are impossible | 0 | Interval terminal |
| `(0,1)` | Direct nonnegative weighted affine contradiction | 0 | `2353/250000` |
| `(0,2)` | Nonnegative weighted affine contradiction after induction | 1 | `548463/500000` |
| `(0,3)` | Direct nonnegative weighted affine contradiction | 0 | `298431/250000` |
| `(1,0)` | All four original H–I inset separation options are impossible | 0 | Interval terminal |
| `(1,1)` | Nonnegative weighted affine contradiction from the initial physical tile | 0 | `23039/1000000` |
| `(1,2)` | Nonnegative weighted affine contradiction after induction | 2 | `4771/1000000` |
| `(1,3)` | Direct nonnegative weighted affine contradiction | 0 | `551487/500000` |

The three induction records contain 421 exact deductions and 620 checked row
occurrences, including 40 terminal rows. The direct affine leaves use 34
terminal rows. The two direct interval leaves use the accepted physical
center/inset propagator and require its exact original-pair terminal.

## Why each affine terminal proves exclusion

Every used row is independently rebuilt from the same physical caller and the
already proved bounds. A stored nonnegative weight combines rows of the form
\(a_r\cdot z\le b_r\). The checker computes the combined coefficient vector
\(c\) and right side \(d\) over the rationals. If the independently justified
absolute bounds are \(|z_k|\le M_k\), the exact positive reserve is

\[
-d-\sum_k M_k|c_k|>0.
\]

Indeed, every physical point would satisfy both
\(c\cdot z\le d\) and \(c\cdot z\ge-\sum_kM_k|c_k|\), which this strict
inequality makes impossible. Residual coefficients are paid explicitly; the
proof does not assume floating-point cancellation. Inductive bounds use the
same exact weighted-sum calculation, followed by independently justified
frame and interval intersections.

The local printed premises include four occurrences of the accepted physical
three-square center-energy inequality
\(\sum_{i<j}\|c_i-c_j\|^2\ge7/2\) for three original physical unit squares.
There are three distinct printed definitions:
`three_square_center_energy_0_1_7_000` occurs once,
`three_square_center_energy_0_7_8_000` occurs once, and
`three_square_center_energy_1_2_8_000` occurs twice. The interval secants are
upper bounds on the corresponding squared differences, so substitution into
the lower energy bound gives valid affine necessary inequalities.

The full accepted three-square proof and coefficient audit are frozen under
`ancestry/three_square_energy_proof`. The master freshly replays its two exact
geometric evaluators, 128 angular triangles and 1,877 coefficient identities
before checking these leaves. The existing physical point/incircle, support,
frame and inset rules are reconstructed by the frozen independent original
checker. The local selected rows have zero occurrences of the four-center
or area-moment additions; their unchanged hand sources remain in the
ancestry inventory.

## Attachment and provenance

`verify_b16a_I11_complete_H_cover.py` first replays the unchanged original
prefix. It then invokes the accepted affine and H-cover checkers on all eight
direct screen records. Exactly five are terminals. For each of the other
three addresses, it freshly invokes the accepted exact induction checker,
requires a complete physical terminal, and matches the original ID, literal
path, original-prefix hash, I rectangle and H rectangle. The resulting set of
addresses must be exactly `{(1,1,hx,hy): hx in {0,1}, hy in {0,1,2,3}}`.

The direct numerical attempt at H `(1,1)` recorded an optimizer warning.
Its raw record remains intact and contributes no proof or necessary state.
The selected zero-round exact induction certificate reconstructs that same
closed rectangle directly from the original prefix. `STOPPING_RECORD.json`
preserves the numerical stop; the exact acceptance above uses its separately
replayed rational certificate.

The master checks the actual origins and hashes of the imported independent
modules. All 151 frozen inputs are checked before and after assembly, and a
strict read audit keeps proof reads inside the packet. The common prefix is
the same hash in every component. The numerical producer and optimizer are
not imported by terminal replay.

## Replay and scope

From this directory run:

```bash
python -B -u verify_b16a_I11_complete_H_cover.py
```

The completed author replay is `B16A_I11_COMPLETE_H_REPLAY.json`, SHA256
`1f25175fe32e5df0e36e059ada6eeb6f1d4bbd3c94430a28164fbab50007509c`.
The exact component master is SHA256
`9eb1c7325a7926d626c0014549badf54271b36d82e9395f5055731b88b25d4d3`.
The 151-input core inventory is SHA256
`0041434b888284901ca7f4b36f9827b3af00474cb9084534501279b6dd127505`.
The complete table is SHA256
`70b83f306fbe3b444477cd42cd909d0595f1f8234e140938b431a469ccc31580`.

The conclusion is exclusion of **this whole fixed I11 rectangle**. A complete
original-cell proof must additionally cover every other I rectangle from the
same original-prefix box. This checkpoint changes no original-cell or mask
denominator or closure count.

## Committed portable evidence and fresh root replay

[Archive parts and exact inventory](computer_assisted/a2_00100_b16a_I11_complete_H_manifest.json) ·
[Fresh root exact replay](computer_assisted/a2_00100_b16a_I11_complete_H_root_replay.json) ·
[All-member archive check](computer_assisted/a2_00100_b16a_I11_root_archive_check.json).

Concatenate the two declared archive parts in order, extract the xz tar,
and run `python -B -S verify_b16a_I11_complete_H_cover.py` from
`b16a_I11_complete_fixed_rectangle_checkpoint`. The packet contains 159
frozen assembly inputs and separate review, source and replay records.
The root freshly replayed the complete assembly, checked its hand table,
and verified all 174 archive members against the embedded 173-file inventory.
No archive member is an external link.

The 421 local deductions use 580 premise rows. There are 74 terminal rows:
40 at the end of the bounded inductions and 34 direct rows. The reported
620 bound rows include the 40 bounded terminal rows; they must not be added
again as premise rows. All eight exact closed H rectangles are excluded.
This closes the entire fixed I11 rectangle, with all contacts retained.

The B16a original, the current mask and all global denominators remain
unchanged. No whole-original, mask, positional-root or roadmap credit is
inferred from this checkpoint. No Lean, Lake or CI was run.
