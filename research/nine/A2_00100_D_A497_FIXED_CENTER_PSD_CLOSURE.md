# Complete D a497 original-cell exclusion by a fixed center cover

[Source-bound packet and replay](computer_assisted/a2_00100_d_a497_psd_manifest.json) · [Independent physical audit](A2_00100_D_A497_PHYSICAL_AUDIT.md) · [Fixed register](gates/A2_00100_FIXED_FRONTIER.json)

November 4, 2026. Input PR head: `4ac78a7e5bba09544e162568d876f09f82afb0d1`.

## 1. The unchanged theorem and caller

The original fixed cell `positive-a4979e5f2a7e8734` is impossible. This is one
complete original predicate in the existing `001/00` mask, not a new mask or a
claim about the other original cells. Its immutable path is

```json
[["angle",3,1],["angle_cut",[0,"0"],1],["alternate_four_escape",[1,7],[6]]]
```

The path is conjoined with the full original caller in
`A2_COVERAGE_AND_CLOSURE_CONTRACT.md`: nine independent physical unit-square
frames, all 36 corner conditions and all 36 physical pairs, the five marked
center-cone comparisons, actual AB, BC, EF and FG, and strictly weak CD.
The radius satisfies every `q<Q=1105/256`. The accepted low-gap exclusion and
reflection give `y_D-y_C>2/3`; only the two extras are ordered by `x_H<=x_I`.
The path selects nonnegative canonical slopes for D and A and the already
registered alternate-four escape indexed 6 for B,H. The frozen path decoder
supplies its complete guarded inequalities. No physical original is removed.

The inherited exact induction is replayed from this original path, through
the coordinate and frame bounds, whole-parent arc union and four correlated
diagonal rounds. All these implications preserve the entire original cell.
They give the following closed outer intervals for the two extra centers:

| Coordinate | Lower endpoint | Upper endpoint |
|---|---:|---:|
| x_H | 44173/131072 | 352255/524288 |
| y_H | -225497/1048576 | 759573/1048576 |
| x_I | 44173/131072 | 5/4 |
| y_I | -59865/131072 | 416230958895369/281474976710656 |

All other inherited scalar, Cartesian-difference and correlated-diagonal
intervals remain in force. Their large rational endpoints are in the immutable
ancestor certificate. They are derived bounds, never added hypotheses.

## 2. One complete finite cover

For any closed interval `[a,b]` define its m equal closed pieces by

`J_m(k)=[a+(b-a)k/m, a+(b-a)(k+1)/m]`, for `0<=k<m`.

The pieces cover `[a,b]`, including both endpoints and every shared face.
Cover the two I coordinates with four pieces each, indexed `(i,j)` with
`0<=i,j<4`. Eleven complete I rectangles terminate immediately. For each
of the other five, use the same fixed H partition: two x-pieces and four
y-pieces, indexed `(h,k)`. No adaptive refinement is used in this proof.

In the table, `L` is a complete affine rational-sum terminal, `E` a complete
exact interval terminal, and `H` routes to the complete eight-piece H cover.

| I x-index | I y-index 0 | I y-index 1 | I y-index 2 | I y-index 3 |
|---:|:---:|:---:|:---:|:---:|
| 0 | L | L | H | H |
| 1 | L | L | L | H |
| 2 | L | H | E | L |
| 3 | H | L | E | E |

Every routed H cover is complete. Its entries below are ordered
`(h,k)=(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)`.
`S` denotes an exact quadratic rational-sum terminal using negative squares.

| Parent I rectangle | Eight H terminals in the stated order |
|---|---|
| (0,2) | S, L, E, E, L, L, E, E |
| (0,3) | S, L, L, L, S, S, L, L |
| (1,3) | S, L, L, L, S, S, S, L |
| (2,1) | E, E, E, E, E, E, E, E |
| (3,0) | E, E, E, E, E, E, E, E |

There are exactly 51 terminal domains: 23 E, 20 L and eight S. The replay
checks this union from the original intervals and matches the eight missing
affine domains exactly to the eight independently proved S domains. There
are no omitted complements, assumed positive clearances or discarded faces.

## 3. Exact interval and affine terminals

For each E terminal, accepted original-center interval propagation either
produces an empty interval, excludes all four axis-separation alternatives
for a pair of original contained insets, or derives a Cartesian difference
interval disjoint from an inherited certified interval. The checker repeats
the exact rational implication, including the compared pair and coordinate.
An exception or a failed numerical solve is never accepted as a terminal.

For each L terminal, the packet prints the physical inequalities used and
nonnegative rational weights. If `a_r·z<=b_r` are those inequalities and
`|z_i|<=M_i` are certified bounds, the checker computes

`a=sum(lambda_r a_r)`, `b=sum(lambda_r b_r)`, and
`rho=-b-sum(M_i |a_i|)>0`.

Any physical point would imply both `a·z<=b` and
`a·z>=-sum(M_i|a_i|)>b`, a contradiction. The 20 L sums use 186 printed
rows altogether. Every row and its interval guard is independently rebuilt;
one used new affine row is the unconditional four-original planar energy law.
That law, its proof and its exact secant expansion are supplied with the packet.

## 4. Quadratic terminals are rational identities on the originals

Use the same 54 real original variables: 18 center coordinates, nine alpha
frame coordinates, nine signed beta coordinates, nine absolute beta values
and nine inset halfwidths. For a physical configuration, adjoin each product
`z_i z_j`, `i<=j`, giving 1,539 coordinates in all. This is an exact embedding;
the extra symbols do not replace the original independent frames.

The necessary rows are original physical affine inequalities, unit-frame and
absolute-value identities, original corner and pair inequalities, valid
interval products, and RLT products of a proved affine inequality with a
nonnegative coordinate slack. The checker rebuilds each used RLT antecedent
in its own tile before multiplying. All-nine radial/cardinality rows and the
unconditional planar four-original energy law are used only with their
proved hypotheses. The area-inertia and owned-axis rows present in discovery
are not used by these eight final sums.

Every used PSD cut is explicitly

`-(q_0 + sum(q_i z_i))^2 <= 0`

for a printed rational vector q. Expanding this polynomial requires rational
arithmetic only. A numerical eigenvector merely suggested q; no floating-point
eigenvalue or assertion that a numerical matrix is positive semidefinite is
a premise of the proof.

The final weighted sum uses exactly the same residual payment as Section 3,
now with certified `|z_i z_j|<=M_i M_j`. Every coefficient, weight, right-hand
side and positive reserve is recomputed with exact fractions. All eight
reserves exceed 1/2000. The decimal values below locate the certificates;
their exact rational values are printed in the packet and checked by replay.

| I indices | H indices | Used terminal rows | Exact reserve, decimal display |
|---|---|---:|---:|
| (0,2) | (0,0) | 32 | 0.0115460778 |
| (0,3) | (0,0) | 1,535 | 0.0011637145 |
| (0,3) | (1,0) | 163 | 0.0028211009 |
| (0,3) | (1,1) | 137 | 0.0044631862 |
| (1,3) | (0,0) | 1,527 | 0.0007313266 |
| (1,3) | (1,0) | 117 | 0.0037992343 |
| (1,3) | (1,1) | 1,531 | 0.0013174384 |
| (1,3) | (1,2) | 32 | 0.0139458174 |

The eight S proofs use 5,074 printed rows, 178 checked RLT antecedents and
66 used explicit negative rational squares, counted across certificates.
The independent checker imports no discovery producer or optimizer.

## 5. Assembly, persistence and exact scope

Every hypothetical point of the unchanged original predicate reaches one
of the 16 I rectangles. Eleven are impossible. Each of the other five
reaches one of its eight H rectangles, all of which are impossible by the
checked E, L or S terminal. Therefore the complete original predicate is
impossible. The argument retains weak contact and applies to every q<Q.

The packet separately records raw numerical discovery, exact candidate
identities, independent reconstruction, source-byte bindings and the final
cover assembly. `replay.py` verifies frozen bytes, replays the complete
ancestor, rejects unbound external workspace reads and produces a fresh
`PASS_COMPLETE_ORIGINAL_PARENT` report. No human or kernel verification is
claimed. No Lean compilation, Lake or CI is run.

This closes exactly one previously OPEN original cell. The same 231-cell
register advances from 197/34 to 198/33. Family D decreases from four to
three OPEN originals; A5, B17 and C8 are unchanged at this checkpoint.
`001/00`, `100/00`, A.2, the unrestricted bound and global equality remain
OPEN. The full-mask ledger stays 8 CLOSED / 24 OPEN, the 7,915 positional
root IDs and their historical statuses stay unchanged, and no roadmap gate
is closed by this one-cell theorem.
