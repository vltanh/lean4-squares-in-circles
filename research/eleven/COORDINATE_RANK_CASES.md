# Eleven-square coordinate rank cases

**Current status:** all 1105 masks in this note are now excluded in q<=U
by [coordinate shrinking](COORDINATE_SHRINKING_REDUCTION.md) followed by
[the six-case axis exclusion](AXIS_ALIGNED_EXCLUSION.md). The enumeration
below remains a valid intermediate classification, not an open gate.

This note classifies necessary finite data for packings whose pairs all
separate on one of two common perpendicular axes. This is an **additional
hypothesis**; the unrestricted oblique branch remains open. Individual squares
may rotate independently. In the certified window q<=U=49013/10000<5, the
initial 4296 rank masks reduce to **1105 residual 4 by 4 masks**. Their impossibility is supplied by the stronger theorem linked above.

## 1. Projection orders and exact rank extraction

Fix the common axes x,y. Let I_i^x and I_i^y be the closed projection
intervals of square i, and let h_i^x,h_i^y be their half-widths. For a unit
square, in any common frame,

    h_i^x = h_i^y = (|c_i|+|s_i|)/2 >= 1/2.

Define i<_x j when the right endpoint of I_i^x is at most the left endpoint
of I_j^x. Define <_y similarly. Each is a strict transitive order because
all intervals have positive width. The common-frame hypothesis says that for
any distinct i,j, they are comparable in at least one of these two orders.
Touching projections are allowed throughout.

Let r_x(i) be the maximum number of vertices in an x-chain ending at i, and
let r_y(i) be the analogous rank. If i<_x j then r_x(i)<r_x(j), and similarly
for y. Consequently the map i -> (r_x(i),r_y(i)) is injective: equal rank
pairs would make two squares incomparable in both orders.

No projection chain has five members. Its projection intervals would have
total length at least five, whereas all lie in a disk projection of length
2sqrt(q)<=2sqrt(U)<5. Write a=max r_x and b=max r_y. Then

    11 <= a*b,    1<=a,b<=4,

so (a,b) is (3,4), (4,3), or (4,4). Every rank from 1 to a and from 1 to b
occurs: along a maximal chain, an omitted predecessor rank would contradict
maximality (equivalently ranks satisfy one plus maximal predecessor rank).
Thus the image consists of eleven occupied cells with no empty row/column.

Squares with equal x-rank form a y-chain: they cannot be x-comparable and
so must be y-comparable. Equal y-rank squares form an x-chain. This fact,
not a visual grid assumption, connects the masks to actual projection chains.

## 2. Initial finite inventory

The 3 by 4 and 4 by 3 masks each have twelve possibilities, since exactly
one cell is missing. For 4 by 4, choose eleven of sixteen cells. There are
C(16,11)=4368 choices; an empty specified row leaves C(12,11)=12 choices,
as does an empty specified column. No choice can have both an empty row and
an empty column: their union would require seven missing cells, but there
are only five. Hence the count is

    4368 - 4*12 - 4*12 = 4272,

giving 12+12+4272=4296 labeled masks. No geometric realizability is asserted.
The unordered row-count profiles in the square grid are
(4,4,2,1), (4,3,3,1), (4,3,2,2), and (3,3,3,2).

## 3. A forbidden rank corner

No square has rank pair (4,4) when q<=5. To see this, an x-chain of length
four ending at i has three predecessors of width at least one. Its leftmost
projection endpoint is at least -R, so the center of i obeys

    p_ix >= -R + 3 + h_i^x >= 7/2-R.

The y-chain ending at i gives p_iy>=7/2-R too. Since R<=sqrt(5)<9/4,
both center coordinates exceed 5/4. Thus ||p_i||²>25/8.

But the unconditional center bound in [the separator cover](FINITE_SEPARATOR_COVER.md)
gives ||p_i||<=C(5)=(sqrt(19)-1)/2<17/10, hence
||p_i||²<289/100<25/8, a contradiction.

After forbidding (4,4), the square-grid count is

    C(15,11) - 2*(C(12,11)+3*C(11,11)) = 1335.

Here an empty fourth row includes the already omitted corner and leaves
twelve cells; any other empty row leaves eleven. Columns give the same
count, and simultaneous empty row/column events are still impossible.
Including both rectangular grids gives 1359 masks at this stage.

The directed longest-chain ranks matter. Reflecting an axis replaces ranks
by co-ranks, which need not equal a+1-r_x. No dihedral quotient of this
rank inventory is used without a proof of its action on actual orders.

There is a second forbidden corner pattern: the first row and the first
column cannot both be full. Their shared square at (1,1) starts an x-chain
of length four along column 1 and a y-chain of length four along row 1.
Reversing the endpoint estimate above gives both center coordinates at most
R-7/2<-5/4, again contradicting ||p||²<289/100. This is a geometric proof
for the actual chains, not a reflection of longest-chain ranks.

## 4. Two disjoint four-chains force squared radius at least five

**Conditional terminal theorem.** If a common-coordinate-separable packing
contains two vertex-disjoint four-square chains in the same projection
direction, then q>=5. The other squares and all individual orientations are
arbitrary.

It suffices to prove the theorem for q<=5. Call the common chain direction y.
By the center bound all center heights lie in [-C(q),C(q)], with
2C(q)<=sqrt(19)-1<4. In either four-chain consecutive centers differ in
height by at least one. Its bottom height lies in [-C(q),C(q)-3]; its top
height lies in [-C(q)+3,C(q)]. Thus the two bottom centers differ vertically
by less than one, and so do the two top centers. Their y projection interiors
overlap. The common-frame hypothesis forces x separation between the two
bottom squares, and separately between the two top squares. The left-to-right
orders of the two pairs may differ; no uncrossed-chain assumption is used.

For the two bottom and two top endpoints choose w_i=(epsilon_i,2 eta_i),
where epsilon_i is -1/+1 according to that pair's x order, and eta_i is
-1 on the bottom and +1 on the top. Let h_i(w) be the square support
half-width in direction w. Disk containment gives

    w_i dot p_i + h_i(w_i) <= sqrt(5q).

Sum these four inequalities. The two x separations contribute the endpoint
x half-widths. Twice each y-chain span contributes twice its endpoint
y half-widths and four times each interior y half-width. Consequently

    4sqrt(5q) >= sum_endpoints [h_i^x + 2h_i^y + h_i(w_i)]
                  + 4 sum_four_interiors h_i^y.                 (T)

For every oriented unit square and each w=(+-1,+-2),

    h^x + 2h^y + h(w) >= 3.                                    (P)

Here is an all-angle proof. Reflections and coordinate interchange allow
c>=s>=0, c²+s²=1. They may interchange the coefficients 1 and 2 in w,
but the minimum of its support over signs/interchange is unchanged. With
h=(c+s)/2, the minimum of 3h+h(w) equals

    3c+s       if s<=c/2,
    2c+3s      if s>=c/2.

In the first interval (3c+s)²-9=2s(3c-4s)>=0, with equality only at s=0.
In the second (2c+3s)²-9=c(12s-5c)>0. This proves (P) and shows that
equality requires alignment with the common coordinate frame.

Each interior half-width is at least 1/2. In (T) the endpoint sum is at
least twelve and the interior sum at least eight. Thus 4sqrt(5q)>=20 and
q>=5, as claimed. At equality all eight squares align; no claim that other
squares are rigid follows. The constant five is sharp for this conditional
theorem, attained by an axis-aligned 2 by 4 rectangle.

## 5. Closed finite classes and explicit residual cases

Since U<5, the two-four-chain theorem excludes both rectangular rank grids:
eleven cells in a 3 by 4 grid have two full rows, and transposition handles
4 by 3. In the 4 by 4 grid it excludes every mask with two full rows or
two full columns. The surviving row profiles are (4,3,3,1), (4,3,2,2),
and (3,3,3,2); columns obey the same condition.

| Dimensions | All nonempty rank masks | Omit (4,4) | Exclude two full rows/columns | Exclude shared start corner |
| --- | ---: | ---: | ---: | ---: |
| 3 by 4 | 12 | 12 | 0 | 0 |
| 4 by 3 | 12 | 12 | 0 | 0 |
| 4 by 4 | 4272 | 1335 | 1155 | 1105 |
| Total | 4296 | 1359 | 1155 | 1105 |

The shared-start exclusion removes another 50 masks. The remaining 1105
masks have row-profile counts 225, 460, and 420 in the order above.
They are explicitly listed as integer bitmasks in
[RANK_MASKS.json](RANK_MASKS.json). Bit 4(r-1)+(s-1) records occupancy of
rank pair (r,s). No symmetry quotient is taken.

Regenerate or compare the exact enumeration:

```sh
python3 classify_rank_masks.py --check RANK_MASKS.json
python3 classify_rank_masks.py --write RANK_MASKS.json
```

The script enumerates finite subsets and applies the predicates proved above.
It does not establish which surviving masks are physically feasible, supply
a sharp lower bound for them, or classify arbitrary oblique packings.

**Gate status:** G3.C1–C5 are now closed in the candidate window by the
stronger axis reduction and exclusion. The unrestricted G3.O branch and
G5–G6 remain open. This finite inventory is preserved for proof provenance.
