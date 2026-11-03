# Three complete A originals from fixed grids and physical interval terminals

## Statement

The entire original cells `positive-d9e959003493b8f1`,
`positive-8e41311b61c89e61`, and `positive-5edcabd77ec2e38b` are empty.
Each proof retains all nine independent physical unit squares, their
original frames, all original corner and pair constraints, and every
predicate of the original path. Every closed equality face is included.

The shared method is a fixed 8 by 8 cover of the ninth original's center
rectangle. Most tiles have exact static weighted or original geometric
contradictions. The remaining tiles have explicit contradictions between
proved whole-parent pair bounds and necessary physical pair bounds on
the entire tile. No further subdivisions or weighted bound rounds are
needed to finish these three grids.

These are three complete original-cell closures. They do not establish
the whole A family, the whole A2/00100 mask, or the remaining masks.

## 1. Exact original domains and proved parent states

The three literal paths are preserved in the source-bound certificates,
and the independent checker verifies each original identifier against
its path. They share the following initial four predicates:

```text
angle(3,1)
angle_cut(0,0,0)
inward_row_escape(7,8,[6])
position_cut(11,1/2,0)
```

The remaining path suffixes are:

| Original suffix | Complete remaining suffix |
| --- | --- |
| `5edcabd77ec2e38b` | `f_side_escape(5,7,[4])` |
| `8e41311b61c89e61` | `f_side_escape(5,7,[6]); f_side_escape(5,8,[6]); lower_escape(2,7,[0])` |
| `d9e959003493b8f1` | `f_side_escape(5,7,[6]); f_side_escape(5,8,[6]); lower_escape(2,7,[1]); lower_escape(2,8,[1]); positive_row_escape(1,7,[2])` |

The whole-parent inductions establish the positions, physical scalar
variables, frame intervals, and pair-difference bounds used below. Every
coordinate-prefix deduction, physical row, guard, rational weighted
bound, and physical frame refinement is independently replayed.

| Original suffix | Earlier coordinate deductions | Parent rounds | New parent deductions | Parent printed rows |
| --- | ---: | ---: | ---: | ---: |
| `d9e959003493b8f1` | 31 | 5 | 457 | 1,178 |
| `8e41311b61c89e61` | 33 | 5 | 653 | 1,201 |
| `5edcabd77ec2e38b` | 32 | 8 | 411 | 1,136 |

The existing eight-round 5ed parent certificate is reused unchanged.
The new d9 and 8e inductions each stop after their declared five rounds.
The parent states alone remain open; their arrays are proved premises
for the complete grid arguments, not standalone contradiction claims.

## 2. One closed rational grid for each whole parent

The exact whole-parent I-center rectangles are:

| Original suffix | I horizontal interval `[a,b]` | I vertical interval `[c,d]` |
| --- | --- | --- |
| `d9e959003493b8f1` | `[-1/1048576, 5/4]` | `[72697/1048576, 776793/524288]` |
| `8e41311b61c89e61` | `[-198559/1048576, 482849/524288]` | `[146687/1048576, 773945/524288]` |
| `5edcabd77ec2e38b` | `[-111163/1048576, 5/4]` | `[-387839/1048576, 1548825/1048576]` |

For `0 <= p,q < 8`, define

\[
T_{8p+q}=
\left[a+\frac{p(b-a)}8,a+\frac{(p+1)(b-a)}8\right]
\times
\left[c+\frac{q(d-c)}8,c+\frac{(q+1)(d-c)}8\right].
\]

All 64 tiles are closed, and adjacent endpoints are exactly equal
rational numbers. Thus the grid covers the entire proved parent
rectangle, including its boundary and every shared tile face. All other
original variables keep their entire proved parent domains.

The grid is fixed before its tests. Each tile receives at most one static
exact dual test and no new bound rounds. The final proof uses:

| Original suffix | Positive-reserve tiles | Original interval/inset tiles | Explicit physical difference tiles | Total |
| --- | ---: | ---: | ---: | ---: |
| `d9e959003493b8f1` | 25 | 35 | 4 | 64 |
| `8e41311b61c89e61` | 30 | 30 | 4 | 64 |
| `5edcabd77ec2e38b` | 16 | 45 | 3 | 64 |

The weighted contradictions follow the exact nonnegative-combination
principle in
[the three-B fixed-center assembly](A2_00100_THREE_B_FIXED_CENTER_COVER_CLOSURE.md).
Each physical row is rebuilt from its named rule and the proved guard
intervals; each original interval/inset terminal is independently
reconstructed. An inset-pair exclusion checks all four permitted
original inset separation options on that entire tile.

## 3. The explicit physical interval terminals

Fix a tile. Begin with the independently verified whole-parent state
and intersect only I's two center intervals with the tile. Reconstruct
the effective original angle bounds, propagate the original physical
center constraints, and compute the resulting necessary pair-difference
bounds. The original parent pair bounds remain valid on the tile.

If the parent gives `w <= U` while physical propagation gives `w >= L`
with `L-U > 0`, the entire tile is impossible. This is an exact interval
contradiction; it does not require a separating-axis choice, a sampled
center, or a new optimization step.

The following table supplies one such witness for each remaining tile.
Grouped tile indices have exactly the same displayed witness. The
supplementary tables include every reconstructed empty-intersection
witness, and the independent checker verifies them all.

| Original suffix | Tile indices | Pair difference `w` | Parent upper bound `U` | Physical lower bound `L` | Positive gap `L-U` |
| --- | --- | --- | --- | --- | --- |
| `d9e959003493b8f1` | `49,57` | `y_G-y_D` | `172055/131072` | `93523406158693/70368744177664` | `1152081394533/70368744177664` |
| `d9e959003493b8f1` | `50,58` | `y_G-y_D` | `172055/131072` | `94277474909029/70368744177664` | `1906150144869/70368744177664` |
| `8e41311b61c89e61` | `53,54` | `x_G-x_F` | `1448455/1048576` | `99136928414565/70368744177664` | `1932758809445/70368744177664` |
| `8e41311b61c89e61` | `57` | `x_I-x_G` | `-445293/1048576` | `-97295651693663/281474976710656` | `22236777814945/281474976710656` |
| `8e41311b61c89e61` | `58` | `x_I-x_G` | `-445293/1048576` | `-47661287707597/281474976710656` | `71871141801011/281474976710656` |
| `5edcabd77ec2e38b` | `36` | `x_G-x_F` | `1445277/1048576` | `198864559097113/140737488355328` | `4882763826457/140737488355328` |
| `5edcabd77ec2e38b` | `51,59` | `y_G-y_D` | `172055/131072` | `23816798273143/17592186044416` | `723967082103/17592186044416` |

Every gap is a positive rational number with the displayed exact
identity. These witnesses account for all 11 remaining fixed tiles.
The physical propagation retains the full original square geometry;
the pair expressions are necessary differences between original
centers, not distances between auxiliary proxy points.

The discovery grid had marked these tiles open because its generic row
constructor encountered the empty parent/physical intersection before
constructing a dual. That diagnostic exception itself supplies no
proof. The explicit intervals above, derived again from the physical
premises, supply the proof. The original tile files are preserved
unchanged; their supplementary interval tables are separate records.

## 4. Independent full-grid replay

The new immutable checker `verify_fixed_i_static_parent.py` imports no
grid producer, supplementary-table producer, optimizer, or point-search
routine. It first obtains the exact proved parent state through the
canonical independent parent replay. It then recomputes all 64 rational
tile rectangles and checks every tile file, index, center restriction,
original identifier, and shared face.

For each ordinary static tile, it reconstructs the physical rows and
checks the exact weighted contradiction, or reconstructs the original
geometric terminal. For each supplemented tile, it independently
recomputes the effective angles, propagated centers, every original
pair difference, and every empty intersection with the parent bounds.
The recorded witness list must equal that newly derived list exactly.

The supplemental tile indices must be exactly the original grid's
pending indices. Missing tiles, additional unsupported terminal kinds,
unproved parent arrays, and incomplete coverage are rejected. Every
source, parent certificate, grid manifest, and supplemental record is
bound by its recorded SHA-256 digest. Portable replay resolves the
original source paths through the packet's explicit source map.

All three fresh independent replays returned
`PASS_COMPLETE_ORIGINAL_PARENT`. Their complete finite arguments use
96 earlier coordinate deductions and 1,521 new whole-parent deductions.
The parent inductions have 3,515 printed rows, and the static grids have
383 printed rows, for 3,898 in all. The final cover has 192 complete
terminal domains and no additional bound rounds or subdivisions.

The general center-cover argument is independent of which original is
chosen as target: restricting any one original center to a complete
closed cover is a valid case split. This particular checker and these
three records select I, at position indices 16 and 17. A proof that
selects H must use H's indices 14 and 15 and retain the original path's
ordering predicates; it cannot relabel H and I without justification.

No Lean, Lake, or CI execution is used or claimed. The result is the
complete physical hand/table argument, the exact finite certificates,
and their independently implemented replay.
