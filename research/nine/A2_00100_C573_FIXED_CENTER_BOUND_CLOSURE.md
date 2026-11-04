# Complete original C573: sixteen exact I-center rectangles

November 4, 2026. This complete original-cell proof advances the same
231-cell register from **206 CLOSED / 25 OPEN to 207 CLOSED / 24 OPEN**.
The remaining original families are **A4, B10, C7, D3**. The full-mask
ledger remains **8 CLOSED / 24 OPEN**. Mask `001/00`, its reversal
`100/00`, A.2, the unrestricted bound and global equality remain OPEN.

[Source-bound packet and root fresh replay](computer_assisted/a2_00100_c_573_bound_manifest.json) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Physical caller and coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

The separate independent checks and the complete original-cell assembly
passed. The root then repeated the whole proof from a relocated frozen
packet. All source hashes remained unchanged. This is independent exact
rational arithmetic and a complete written physical argument; no human
or proof-kernel verification is claimed. No Lean, Lake or CI was run.

The unchanged original cell `negative-573078fc944ce553` is empty. The proof covers its entire certified I-center rectangle by sixteen closed quarter products and proves a contradiction on every member. It closes one original cell of the `001/00` frontier. It does not by itself close that mask.

## 1. Original physical caller and exact ancestry

The full original path is

```json
[["angle",3,0],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[7]],["alternate_four_escape",[1,8],[5]]]
```

All nine original unit squares A through I, their independent physical frames, all 36 corner-containment conditions, and all 36 pairwise nonoverlap conditions remain in this caller. The original actual links, center cones, strictly weak C–D predicate, sign intervals, and every primary and predecessor inequality of the two alternate-four escapes remain in force. The proof neither relabels the squares nor replaces an original with an interior tile.

The original v3 bound prefix has SHA-256

```text
884d0851746b3ba7f21dafc0e817e3d94d6c285c38ab2af0619846ccd7e5741e
```

Its independent replay checks 32 earlier coordinate deductions and five subsequent rounds containing 453 exact bound deductions and 1,210 printed rows. The diagonal-format wrapper has SHA-256

```text
57103fb7cf0e69795de18a4b7275ed93bdfb45949828d6188592942acc6b6e61
```

The wrapper has zero rounds. Its final original state is checked to be exactly the independently replayed v3 state, and its additional diagonal dictionary is empty. It creates no extra hypothesis or bound. Thereafter, diagonal intervals are derived from the same certified Cartesian pair differences and retained through each exact bound round.

The master `verify_all.py` checks this original identifier and full path against the immutable 231-cell input registry. Every direct and bound certificate must have the same wrapper hash. Each tile rectangle is independently recomputed from that same original state; equal tile indices alone are insufficient.

## 2. A complete closed cover

The certified rectangle for the original center I is

\[
[l_x,u_x]\times[l_y,u_y]
=\left[\frac{44173}{131072},\frac54\right]
\times\left[-\frac{45001}{524288},\frac{1493687}{1048576}\right].
\]

For either coordinate interval `[l,u]`, define

\[
J_j(l,u)=\left[l+\frac j4(u-l),\;l+\frac{j+1}{4}(u-l)\right],
\qquad j=0,1,2,3.
\]

The sixteen members are `I ∈ J_i(l_x,u_x) × J_j(l_y,u_y)` for every pair `(i,j)∈{0,1,2,3}²`. Their union is the entire original rectangle, including every outer and shared face. All other originals retain their full certified intervals. No H subdivision or additional geometric case is used.

The complete terminal table is below. A reserve lower bound means the exact rational reserve is strictly greater than the displayed value. Every full reserve, input hash, interval label, and frame witness appears in `COVER_TABLE.json` and the immutable certificate records.

| I quarter | Terminal | Local rounds | New bound deductions | Bound-premise rows | Terminal rows | Reserve lower bound |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| (0,0) | Direct affine contradiction | 0 | 0 | 0 | 2 | 1/2 |
| (0,1) | Affine contradiction after bounds | 1 | 308 | 331 | 38 | 1/64 |
| (0,2) | Affine contradiction after bounds | 1 | 314 | 323 | 29 | 1/64 |
| (0,3) | Direct affine contradiction | 0 | 0 | 0 | 9 | 1/16 |
| (1,0) | Direct affine contradiction | 0 | 0 | 0 | 2 | 1/2 |
| (1,1) | Empty original C-frame interval | 1 | 373 | 201 | 0 | Exact frame gap below |
| (1,2) | Affine contradiction after bounds | 1 | 362 | 289 | 3 | 1 |
| (1,3) | Affine contradiction after bounds | 1 | 272 | 375 | 30 | 1/256 |
| (2,0) | Direct affine contradiction | 0 | 0 | 0 | 25 | 1/64 |
| (2,1) | Direct affine contradiction | 0 | 0 | 0 | 3 | 1 |
| (2,2) | All four original G–I inset alternatives impossible | 0 | 0 | 0 | 0 | Exact interval |
| (2,3) | Affine contradiction after bounds | 1 | 358 | 295 | 3 | 1/32 |
| (3,0) | Direct affine contradiction | 0 | 0 | 0 | 3 | 1/32 |
| (3,1) | Direct affine contradiction | 0 | 0 | 0 | 3 | 1/16 |
| (3,2) | All four original G–I inset alternatives impossible | 0 | 0 | 0 | 0 | Exact interval |
| (3,3) | Empty propagated original center interval | 0 | 0 | 0 | 0 | Exact interval |
| **Total** | **16 complete members** | **6** | **1,987** | **1,814** | **150** | **All 12 reserves > 1/256** |

Thus seven members have direct affine contradictions, three have direct interval contradictions, five have affine contradictions after one bound round, and one has an exact original-frame contradiction after one bound round. The local proof checks 1,964 printed row occurrences in total, consisting of the 1,814 bound-premise rows and the 150 terminal rows.

## 3. Exact physical rows and bound induction

Every row concerns the same 54 physical variables: 18 original center coordinates, nine alpha components, nine signed beta components, nine absolute-beta components, and nine original inset halfwidths. The independent row reconstructors check the original frame, corner, support, inset, actual-link, center-cone, pair-separation, capacity, and certified-difference rules, including their current interval guards. The correlated rows retain the certified intervals for both `dx+dy` and `dx-dy`.

One additional planar row used in the I(2,3) bound round is the four-center energy secant for the distinct originals F,G,H,I. The accepted planar theorem gives

\[
\sum_{i<j\in\{F,G,H,I\}}\|c_j-c_i\|^2\ge8.
\]

For any certified Cartesian difference interval `l≤d≤u`, the identity `(d-l)(u-d)≥0` gives `d²≤(l+u)d-lu`. Applying this to all twelve coordinate differences yields the exact affine row named `four_center_energy_5_6_7_8_000000`. Its coefficients are independently rebuilt from the old-state bounds.

For each bound proposal, let the checked physical rows be `a_r·z≤b_r`, and let `|z_k|≤M_k` be the explicit certified absolute bounds. With nonnegative rational multipliers `w_r`, write

\[
a=\sum_r w_r a_r,\qquad b=\sum_r w_r b_r.
\]

For a requested affine objective `c·z`, the same physical configuration must satisfy

\[
c\cdot z\le b+\sum_k M_k|a_k-c_k|.
\]

The checker recomputes this expression exactly, verifies the outward rational-grid rounding, and intersects the resulting necessary bound with the old interval. Every proposal in a round uses only that round's original row collection. Physical frame inferences are then checked before forming the next state. This is an acyclic deduction on the same complete rectangle, not an additional subdivision.

For each of the twelve affine terminals, the exact weighted sum has

\[
\eta=-b-\sum_k M_k|a_k|>0.
\]

The row sum would give `a·z≤b`, whereas the absolute bounds give `a·z≥b+η`, a contradiction. Every printed multiplier, physical coefficient, absolute bound, residual allowance, and reserve is checked in rational arithmetic. The twelve reserves all exceed `1/256`.

## 4. The exact original C-frame contradiction in I(1,1)

The checker first verifies all 373 weighted bound deductions and all nine frame-inference identities in the final round. The derived signed slope interval for the original C is

\[
-\frac{14760312003073}{281474976710656}
\le t_C\le
\frac{10818453394967}{35184372088832}.
\]

The canonical physical frame has `alpha_C=1/sqrt(1+t_C²)>0`. The exact analytic interval reconstruction therefore gives

\[
\alpha_C\ge\frac{269044004737661}{281474976710656}.
\]

The lower root bound is itself valid by the exact check `L²(1+T²)≤1`, where `L` is the displayed lower bound and `T` is the larger absolute slope endpoint. But the independently proved affine bounds also give

\[
\alpha_C\le\frac{494585}{524288}.
\]

These two bounds are inconsistent, with positive exact gap

\[
\frac{269044004737661}{281474976710656}
-\frac{494585}{524288}
=\frac{3515704726141}{281474976710656}>0.
\]

The discovery record exits before installing a new post-round frame state. The independent checker verifies that early-exit convention and derives the contradiction directly from the final weighted bounds and the reconstructed physical frame. It never uses the stale final fields as a newly proved state.

## 5. Whole-original assembly

The master enumerates all sixteen quarter pairs and requires an accepted exact contradiction for each. It checks the common original path and common source-prefix hash, recomputes every rectangle, preserves the fixed original labels and strict C–D caller, and rejects missing or duplicate members. The optional partial mode lists every missing rectangle explicitly and grants zero original credit; this completed run has no remainder.

The complete portable runtime report `COMPLETE_REPLAY.json` returns `PASS_COMPLETE_ORIGINAL_PARENT`. It records all sixteen terminals, all 1,987 local deductions, the exact frame witness, the full original ancestry replay, source hashes, and the local import audit. Its strict context resolves historical names only to frozen packet files and rejects external workspace imports or reads. The mathematical replay uses independent exact physical arithmetic; numerical solver results and discovery row counts are not proof premises.

The entire original rectangle is covered, and every physical configuration in every member is contradictory. Therefore the unchanged original cell `negative-573078fc944ce553` is empty. No Lean, Lake, CI, or whole-mask result is claimed.

The final master also compares every table member, source hash, exact reserve,
local induction total and C-frame witness against its fresh arithmetic replay.
The preceding assembly-review input is retained unchanged under `review_inputs`;
its report hash is explicitly checked before the table is accepted.


## Reconstruct the committed packet

From `research/nine/computer_assisted`, run:

```sh
printf '%s  %s\n' 7f589ddd158926bd4b974bd93cdae6e804ac0f638ff30e03ce7f0b3600daad23 a2_00100_c_573_bound_checkpoint.tar.gz | sha256sum -c -
tar -xzf a2_00100_c_573_bound_checkpoint.tar.gz
cd c_573_bound_package
python -B -S verify_all.py
```
