# A rational neighborhood of the six-body candidate admits no additional square

**Status:** complete conditional hand proof with a printed finite rational
cover; two full mathematical reviews passed on 2026-10-29. Independent
exact reconstruction by half-plane line intersections checks every table
entry. This does not close LSLSLD or assert
that its numerical candidate is an exact physical stress.

Consider any packing of unit squares in a centered disk with
`R^2<=17/4`. Suppose it contains six distinct squares whose centers belong
to the six regions below. There is no restriction on their orientations.

**Theorem.** Such a packing contains exactly these six squares: no
additional interior-disjoint unit square can be inserted.

This supplies a completion obstruction for a whole neighborhood of the
[exploratory one-D/two-S core](ONE_DIAGONAL_TWO_SIDE_COMPONENT_CANDIDATE.md),
including the displayed ranges of transverse S placements. It does not
reduce every core of that signature to this neighborhood.

## 1. The rational center regions

All decimal endpoints in this table are exact terminating rationals.
Each of A,B,C,D ranges over one closed box. Each S region is the convex
hull of its two displayed closed boxes.

| Region | Box or convex hull of two boxes |
| --- | --- |
| A | `[-1.30,-1.29] x [-.45,-.44]` |
| B | `[1.11,1.12] x [-.74,-.73]` |
| C | `[-.03,-.02] x [1.33,1.34]` |
| D | `[-.10,-.09] x [-.63,-.62]` |
| S_A | hull of `[-.56,-.55] x [.48,.49]` and `[-.99,-.98] x [.73,.74]` |
| S_B | hull of `[.83,.84] x [.44,.45]` and `[.56,.57] x [.30,.31]` |

The exact vertices are also listed in
[six_body_center_cover.json](six_body_center_cover.json). The numerical
candidate's A,B,C,D centers lie strictly in their boxes. Its S_A centers
for slide parameter in `[1/2,1]` and S_B centers for slide parameter in
`[0,3/10]` lie in the respective convex hulls, as a numerical observation.
The theorem itself assumes center-region membership directly; it does
not use that numerical observation as a premise.

## 2. Every possible additional center lies in a fixed polygon

For a unit square centered at c in the radius-R disk, the universal
center bound is

```text
|c|<=sqrt(R^2-1/4)-1/2<=3/2.
```

One direct proof is that its farthest squared vertex radius is at least
`|c|^2+|c|+1/2`: the sum of the absolute center projections on its two
unit side directions is at least |c|. Rearranging gives the displayed
bound.

Let P be the intersection of these 32 closed half-planes:

```text
|x|, |y| <= 3/2,
|x+y|, |x-y| <= 15/7,
|2x+y|, |2x-y|, |x+2y|, |x-2y| <= 17/5,
|3x+y|, |3x-y|, |x+3y|, |x-3y| <= 19/4,
|4x+y|, |4x-y|, |x+4y|, |x-4y| <= 31/5.
```

The disk `|c|<=3/2` lies in P. By Cauchy's inequality, the required
squared comparisons are respectively

```text
9/4=9/4,
225/49>9/2,
289/25>45/4,
361/16>45/2,
961/25>153/4.
```

Thus every possible additional square center belongs to P.

## 3. A finite convex cover places it too near an existing center

Start from the square `[-3/2,3/2]^2`. At each subdivision, quarter a box
by its horizontal and vertical midlines. Label the four children
`0=southwest`, `1=southeast`, `2=northwest`, `3=northeast`. A path such
as `001310` specifies its dyadic box exactly.

The 64 rows in Section 4 are the leaves of a full four-way subdivision.
Intersect each box with P. Four intersections are empty. For every other
row, the assigned center region has this property:

> For every vertex z of the clipped box and every listed vertex c of
> the assigned center region, `|z-c|^2` is at most the printed rational
> bound, strictly below one.

These are finite rational inequalities. The clipped-box vertices are
obtained by intersecting rational lines; the region vertices are given
in Section 1. The printed value is the largest such squared distance
for that row. The
[exact checker](check_six_body_center_cover.py) reconstructs the cells,
checks complete subdivision coverage, clips with rational arithmetic,
and verifies every printed value. It does not use optimization or
floating-point arithmetic.

For a fixed center-region vertex c, convexity of squared distance extends
its bound to the whole clipped box. For a fixed point z of that box,
convexity in c then extends the same bound to the whole center region.
Consequently every point of P is at distance strictly below one from the
actual center of at least one of the six specified squares. The largest
printed bound is

```text
10193149/10240000<1.
```

Two interior-disjoint unit squares have center distance at least one,
because their open inscribed disks have radius 1/2. An additional
square's center would belong to P and have distance below one from an
existing center, a contradiction. This proves the theorem.

## 4. The complete rational cover table

An empty row means its box has empty intersection with P. Every bound
below is exact. The table is a local completion certificate, not an
additional entry in the main 21-family ledger.

<!-- SIX_BODY_CENTER_COVER_TABLE -->

| Dyadic path | Center region | Maximum squared distance |
| --- | --- | --- |
| `000` | EMPTY | — |
| `0010` | EMPTY | — |
| `0011` | D | `30361/32000` |
| `0012` | A | `2811337/3920000` |
| `00130` | A | `2331181/2560000` |
| `001310` | A | `10193149/10240000` |
| `001311` | D | `1974681/2048000` |
| `001312` | A | `1196533/1280000` |
| `001313` | D | `1877/2048` |
| `00132` | A | `260677/320000` |
| `00133` | A | `581729/640000` |
| `002` | A | `357253/980000` |
| `003` | A | `30869/40000` |
| `01` | D | `7461/8000` |
| `02` | A | `101/200` |
| `03` | D | `333/400` |
| `100` | D | `591961/640000` |
| `10100` | D | `2807597/2880000` |
| `10101` | B | `2620949/2880000` |
| `10102` | D | `301333/320000` |
| `10103` | B | `282061/320000` |
| `1011` | B | `542981/720000` |
| `1012` | B | `143093/160000` |
| `1013` | B | `52009/80000` |
| `102` | D | `9613/20000` |
| `103` | B | `14221/20000` |
| `11` | B | `19637/40000` |
| `120` | D | `5813/20000` |
| `121` | B | `2753/4000` |
| `122` | D | `24901/40000` |
| `123` | S_B | `17937/20000` |
| `13` | B | `6997/10000` |
| `200` | A | `569/800` |
| `201` | S_A | `1513/2500` |
| `202` | S_A | `534089/640000` |
| `203` | S_A | `16141/40000` |
| `210` | S_A | `37033/40000` |
| `2110` | D | `4797/6400` |
| `2111` | D | `108529/160000` |
| `2112` | S_A | `75941/80000` |
| `21130` | D | `21501/25600` |
| `21131` | D | `537841/640000` |
| `211320` | D | `94977/102400` |
| `211321` | D | `47133/51200` |
| `211322` | S_A | `1140581/1280000` |
| `211323` | S_A | `2490637/2560000` |
| `21133` | S_B | `288117/320000` |
| `212` | S_A | `10229/20000` |
| `2130` | S_A | `124357/160000` |
| `2131` | C | `30697/32000` |
| `2132` | S_A | `54041/80000` |
| `2133` | C | `10121/16000` |
| `22` | S_A | `30161/40000` |
| `23` | C | `881/1000` |
| `30` | S_B | `9081/10000` |
| `31` | S_B | `9797/10000` |
| `32` | C | `1913/2000` |
| `330` | S_B | `872453/980000` |
| `331` | S_B | `817853/980000` |
| `3320` | C | `31433/32000` |
| `3321` | S_B | `3771737/3920000` |
| `3322` | C | `20761/32000` |
| `3323` | EMPTY | — |
| `333` | EMPTY | — |
