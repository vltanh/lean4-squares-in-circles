# A subcritical eight-square obstruction to the weak end-chain terminal

November 1, 2026. Exact hand verification of the construction supplied by
the root agent. No scripts, optimization, Lean, or CI were used.

## Result and scope

Eight physical unit squares can satisfy all of the following **strictly
below** `Q=1105/256`:

* A genuine exceptional pair A,B has overlapping x and y projections.
* Its x direction is fat: `x_B-x_A+h_A+h_B>2` and
  `x_B-x_A>=g_A+g_B`, with `g_i=1/(4h_i)`.
* A,B,C,D form an x-ordered four-list with only A--B lacking an actual
  x-projection separation; B,C,D and A,C,D are actual three-chains.
* A disjoint actual three-chain L,M,R exists.
* L overlaps both A and B in x projection and lies vertically below both.
* Every pair other than A,B has an actual coordinate separation.
* An eighth physical square, additional to the weak four-list and the
  disjoint three-chain, also satisfies all original conditions.

Thus neither these seven-square hypotheses nor their combination with
one arbitrary additional physical square implies the sharp lower bound.
Any valid closure of the remaining nine-square branch must use the ninth
actual square or further hypotheses. This is not a
counterexample to the nine-square conjecture or its one-exception subclass.

## 1. Explicit poses

Give A and B the common orthonormal frame

    u=(99,-20)/101,  v=(20,99)/101,
    h_A=h_B=119/202,  g_A=g_B=101/238,

and centers

    A=(-73/50,7/20),   B=(-61/100,6/5).

The other six squares are axis-aligned, with centers

    C=(4839/10100,1/10), D=(14939/10100,1/10),
    L=(-1,-9/10), M=(0,-9/10), R=(1,-9/10).
    F=(3/5,6/5).

The unit-frame identity is `99^2+20^2=101^2`.

## 2. Physical nonoverlap and exact weak-chain data

The exceptional center difference is `(17/20,17/20)`. Its v projection is

    (17/20)(119/101)=2023/2020=1+3/2020.

The two squares each have width one in v, so their open interiors are
strictly separated. In each coordinate their projection overlap is

    119/101-17/20=663/2020>0.

The x fat-span reserve and the inscribed-pair gap reserve are

    17/20+119/101-2=57/2020>0,
    17/20-101/119=3/2380>0.

The actual B--C x gap is

    4839/10100+61/100=110/101=h_B+1/2,

and C--D has x gap exactly one. A is strictly x-separated from C and D.
Thus B,C,D and A,C,D are actual x-three-chains, and A,B,C,D has the
stated weak end-pair structure. L,M,R is another actual x-three-chain.

Every other pair is coordinate-separated:

| Pair family | Actual separation |
|---|---|
| A,L | y gap `5/4>110/101` |
| A,M and A,R | x gap at least `73/50>110/101` |
| B against L,M,R | y gap `21/10>110/101` |
| C,D against L,M,R | y gap exactly `1` |

L has x-center gaps `23/50` and `39/100` from A and B, respectively,
both strictly less than `110/101`. Hence it overlaps both projections
in x while lying strictly below both in y. All twenty-one physical pair
comparisons are covered by the actual chains, the table, and the oblique
A--B separator.

The eighth square F is also coordinate-separated from every member of
that seven-square core:

| Pair family | Actual separation |
|---|---|
| F,B | x gap `121/100>110/101` |
| F,A | x gap `103/50>110/101` |
| F against C,D | y gap `11/10>1` |
| F against L,M,R | y gap `21/10>1` |

Thus all twenty-eight pairs in the eight-square packing are checked,
and A,B remain the only coordinate-exceptional pair.

## 3. Both actual projection heights are exactly three

The following are partitions of all eight squares into three antichains
of the actual projection orders:

| Order | First antichain | Second antichain | Third antichain |
|---|---|---|---|
| x | `{A,L,B}` | `{M,C,F}` | `{R,D}` |
| y | `{L,M,R}` | `{A,C,D}` | `{B,F}` |

Each indicated block has a point common to the **open** projection
intervals of all its members. For x, one may use respectively `-1`,
`1/4`, and `5/4`. For y, one may use `-9/10`, `1/10`, and `6/5`.
Thus each block is genuinely an antichain, including the boundary cases
elsewhere in the packing. Every chain meets each block at most once,
so both actual heights are at most three.

B,C,D is an actual x-three-chain. L,C,B is an actual y-three-chain:
its successive center gaps are `1` and `11/10`, the latter greater
than `110/101`. Both heights are therefore exactly three.

The construction consequently satisfies the height-at-most-three
hypotheses of the rank-boundary branch as well as the one-exception
cover. Its essential missing hypothesis is the ninth actual unit.

## 4. Exact subcritical circle

For a square with center c and frame u,v, the maximum squared corner
norm is `|c|^2+1/2+|c.u|+|c.v|`. Direct substitution gives

| Square | Maximum squared corner norm |
|---|---:|
| A | `4351541/1010000` |
| B | `4245121/1010000` |
| D | `(19989/10100)^2+9/25 < 10701/2500` |
| C | strictly less than D's value |
| L,R | `421/100` |
| M | `221/100` |
| F | `(11/10)^2+(17/10)^2=41/10` |

For a direct check of the two oblique entries:

    |c_A|^2=22541/10000,
    c_A.u=-7577/5050, c_A.v=109/2020;

    |c_B|^2=18121/10000,
    c_B.u=-8439/10100, c_B.v=533/505.

The D bound uses `19989/10100<99/50`. Every other displayed value is
strictly below A's. For example

    10701/2500 = 4323204/1010000 < 4351541/1010000,
    421/100   = 4252100/1010000 < 4351541/1010000.

Consequently the whole packing fits in squared radius

    q0=4351541/1010000,

with exact strict margin

    Q-q0=128469/16160000>0.

Convexity of the disk turns the four-corner checks into full square
containment. The weak end-chain terminal therefore fails on actual
physical geometry, not just on a relaxed algebraic assignment. The
eight-square extension further shows that even one of the two bodies
outside the weak four-list and the three-chain does not suffice by itself.
The ninth body, or additional proved nine-body consequences, is essential
to a valid closure of the remaining problem.
