# Independent physical audit of the D a497 complete center cover

## Claim and caller

The proposed exclusion concerns exactly the fixed original cell
`positive-a4979e5f2a7e8734`, with unchanged original path

```json
[["angle",3,1],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[6]]]
```

This is a cell of the existing `001/00` cover. Its caller retains all nine
original physical unit squares, their nine independently oriented frames,
all 36 corner conditions, and all 36 pairwise nonoverlap conditions. In
particular, H and I remain physical squares. The center restrictions below
are exhaustive internal proof cases, not extra hypotheses of the mask.

The radius parameter is the original `q < Q = 1105/256`. Every corner row
used by this proof is valid after weakening its strict bound to the closed
bound `Q`; consequently no fixed distance below Q, positive clearance, or
numerical tolerance is assumed. This audit does not assign a closed-Q
status to the whole mask: any stronger conclusion would also have to check
all hypotheses of the inherited original-cell reduction at closed Q.

The independent ancestor replay starts from the published original caller
and rechecks its bound deductions, arc-union deductions, and diagonal
deductions. The resulting intervals are proved necessary properties of
the same configuration. They are not accepted from a numerical optimizer.
The frozen prefix SHA-256 is
`7b440e17f9370432b0aa2bf3612b2b6280186603685f86514bf5897c57f2e4e3`.

## Complete finite cover, with equality faces

Write `[a,b]` for either certified coordinate interval of I. The four
intervals

\[
[a+(b-a)r/4,\ a+(b-a)(r+1)/4],\qquad r=0,1,2,3,
\]

cover `[a,b]` exactly, including every endpoint. Taking the Cartesian
product gives the 16 fixed I tiles. Eleven have independently verified
affine or explicit interval contradictions. The other five are each
covered by the two equal closed intervals of H's x coordinate and the
four equal closed intervals of H's y coordinate. These 40 HI tiles cover
the remaining five I tiles. Shared faces are deliberately retained.

The independent affine/interval replay closes 32 of these 40 HI tiles.
Its exact remainder is

```text
(0,2,0,0)  (0,3,0,0)  (0,3,1,0)  (0,3,1,1)
(1,3,0,0)  (1,3,1,0)  (1,3,1,1)  (1,3,1,2)
```

Each tuple lists `(I_x tile, I_y tile, H_x tile, H_y tile)`, with division
counts `(4,4,2,4)`. These are exactly the eight complete tiles accepted
by the independent rational quadratic replay. Thus the assembled cover
has **51 terminal domains: 11 coarse I terminals and 40 HI terminals**.
There is no uncited complement, open endpoint, or residual infinite tree.

## Meaning of the quadratic certificates

The 54 original real variables are the 18 center coordinates and the 36
frame/inset variables. The frame coordinates, their absolute components,
and the inset quantities all describe these same nine squares. The
quadratic lift has **1,539 coordinates in total**: 54 degree-one variables
and 1,485 products `z_i z_j` with `0 <= i <= j < 54`. No independent
physical object is introduced by a lifted coordinate. A hypothetical
physical packing gives one simultaneous assignment to all these values.

Every used row is independently reconstructed as a polynomial inequality
in these original variables. The reconstruction checks the exact physical
tile, frame and corner identities, interval-product and secant bounds,
pair constraints, and any additional named geometric theorem used.
For an RLT row, its affine antecedent is first independently rebuilt and
proved in this same tile; multiplication is then by a variable's
nonnegative distance from one of its certified interval endpoints.

Every used PSD-discovered row has the explicit rational form

\[
-\left(r_0+\sum_{i=0}^{53}r_i z_i\right)^2\le 0.
\]

Its coefficients are expanded exactly. No numerical eigenvalue, solver
status, approximate positive semidefinite matrix, normalization, or
floating-point feasibility decision is a proof premise. A numerical
method only proposed the rational coefficients and positive weights.

If the checked rows are `a_j . w <= b_j`, their printed positive rational
weights give `c . w <= b`. Independently certified absolute bounds
`|w_k| <= M_k` give `c . w >= -sum_k |c_k| M_k`. The checker computes

\[
\rho=-b-\sum_k |c_k|M_k>0
\]

with exact fractions. The two inequalities then imply `0 <= -rho`, a
contradiction. This explicitly pays for every residual coefficient; it
does not require cancellation that holds only to numerical precision.

## Replay evidence and scope

`verify_affine_cover.py` independently checks the 43 affine/interval
terminal domains, their 186 printed rows, and the exact eight-tile
remainder. Its report is `AFFINE_COVER_REPLAY.json`.

`verify_active_psd_tiles.py` independently checks all eight remaining
complete physical tiles. `D_A497_PSD_TILE_REPLAY.json` records **5,074 used
terminal rows, 178 affine RLT antecedents, and 66 used negative rational
squares**. All eight exact reserves are positive; their approximate
display range is `0.0007313266` through `0.0139458174`. The exact fractions,
weighted right sides, residual corrections, and input hashes are in the
report and source certificates. The replay imports independent physical
checkers and the Python standard library; it does not import a numerical
optimizer or the discovery row generators. No Lean, Lake, or CI was run.

Matching the affine remainder to these eight PSD tile keys and checking
their common original path proves the **entire unchanged original cell**
impossible. The two partial checker reports intentionally assign zero
original-cell closure credit on their own. The complete assembly is
entitled to one original-cell closure, after its source binding and exact
cover checks succeed. This result alone closes no whole mask and changes
none of the fixed mask definitions or denominators.
