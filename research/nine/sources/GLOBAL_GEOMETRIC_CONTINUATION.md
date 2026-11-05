# A sharp physical packing that needs at least three exceptional pairs in every two-direction cover

November 1, 2026. Exact hand construction and proof. No mathematical scripts,
enumeration, Lean compilation, or CI were used.

## 1. Result and why it matters for the global caller

Put `Q=1105/256`. There is a packing of nine interior-disjoint unit squares
in the closed Q-disk such that, **for every choice of two fixed projection
directions, at least three pairs have overlapping open projections in both
directions**. The directions need not be perpendicular.

For the ordinary horizontal/vertical directions, exactly three pairs are
exceptional. Thus the minimum possible number of exceptional pairs is
exactly three.

Consequently neither a one-exception nor a two-exception two-direction
cover can be asserted for every unrestricted packing at `q<=Q`. This
obstruction applies to equality and therefore to any proposed closed-Q
global normalization. It does **not** disprove a hypothetical theorem
restricted to `q<Q`; the construction below attains Q and retains an
actual four-plus-three projection-chain terminal. Nor does it refute
a disjunction allowing either that terminal or a small-exception cover.

## 2. Nine explicit square poses

The seven aligned squares have centers

| Label | Center |
|---|---|
| M0 | `(-3/2,1/16)` |
| M1 | `(-1/2,1/5)` |
| M2 | `(1/2,1/16)` |
| M3 | `(3/2,1/16)` |
| B0 | `(-1,-15/16)` |
| B1 | `(0,-15/16)` |
| B2 | `(1,-15/16)` |

All seven have frame `(1,0),(0,1)`. Relative to the usual attaining core,
only M1 has been raised.

Add two squares F and G with the same orthonormal frame

    u=(99/101,20/101),  v=(-20/101,99/101),

and centers

    c_F=(-5/8,103/80),   c_G=(19/40,103/80).

The unit-frame identity is `99^2+20^2=101^2`. Their common horizontal
and vertical halfwidth is

    h=119/202.

## 3. Exact circle containment

The standard six anchors other than M1 retain their usual Q containment.
In particular M0,M3,B0,B2 have actual corners of squared norm Q.
The raised M1 has farthest squared corner norm

    1+(7/10)^2=149/100<Q.

For any square with center c and frame u,v, its farthest squared corner
norm is

    |c|^2+1/2+|c.u|+|c.v|.

For the two new squares, direct substitution gives

| Square | `|c|^2` | `c.u` | `c.v` | Farthest squared corner norm |
|---|---:|---:|---:|---:|
| F | `13109/6400` | `-2890/8080` | `11197/8080` | `Q-3989/161600` |
| G | `12053/6400` | `5822/8080` | `9437/8080` | `Q-7213/161600` |

For a direct common-denominator check, the two maxima are
`2774169/646400` and `2761273/646400`, while
`Q=2790125/646400`. Both reserves are strictly positive.

Thus every vertex, and by convexity every square, lies in the closed
Q-disk. The four retained outer anchors attain Q.

## 4. Exact physical nonoverlap of all pairs

The seven aligned anchors have disjoint interiors. Within each horizontal
chain their x-center gaps are at least one. Raising M1 preserves those
horizontal separations; its vertical center gap above each nearby B square
is `1/5+15/16=91/80>1`. All remaining anchor comparisons are unchanged.

The lowest y coordinate of F and G is

    103/80-119/202=5643/8080.

Every aligned anchor other than M1 has top height at most `9/16`.
The strict clearance is

    5643/8080-9/16=549/4040>0.

Hence F and G are vertically separated from all six of those anchors.
It remains to check their pairs with M1 and with one another.

M1 is the rectangle `[-1,0] x [-3/10,7/10]`. Its maximum v projection
is attained at `(-1,7/10)` and equals `893/1010`. The minimum v
projection of F is `11197/8080-1/2`. Their clearance is exactly

    (11197/8080-1/2)-893/1010=13/8080>0.

Thus the actual oblique axis v strictly separates F from M1.

M1's maximum u projection is attained at `(0,7/10)` and equals `14/101`.
The minimum u projection of G is `5822/8080-1/2`. Their clearance is

    (5822/8080-1/2)-14/101=331/4040>0.

Thus the actual oblique axis u strictly separates G from M1.

Finally `c_G-c_F=(11/10,0)`. Projection on their common u-axis has
center gap

    (11/10)(99/101)=1089/1010=1+79/1010.

Both squares have width one on u, so they are strictly separated.
This checks every physical pair, including all weak anchor contacts.

## 5. Exactly three exceptions in the original coordinate directions

All pairs among the seven anchors are separated along a coordinate, and F,G are
vertically separated from the six unchanged anchors, as just checked.
The following three pairs overlap in both original coordinate projections:

    {F,M1}, {G,M1}, {F,G}.

For each new square versus M1, the vertical center gap is `87/80`,
whereas the sum of halfwidths is `h+1/2=110/101`. The overlap margin is

    110/101-87/80=13/8080>0.

Their horizontal center gaps are respectively `1/8` and `39/40`, both
strictly smaller than `110/101`. Thus neither coordinate separates
either pair.

For F,G the horizontal center gap is `11/10`, while the total projection
width is `2h=119/101`. The horizontal overlap is

    119/101-11/10=79/1010>0,

and their vertical projections have identical centers. This proves that
there are exactly three exceptions in the original frame.

## 6. Every pair of directions leaves at least three exceptions

Directions are treated as unoriented, since reversing a projection axis
does not change separation. Let e,f be any two unit directions.

### 6.1. Three anchor pairs force a horizontal direction

The three pairs

    {B0,B1}, {B1,B2}, {M2,M3}

consist of aligned squares with center difference `(1,0)`. For a unit
projection direction `(a,b)`, their projected center gap is `|a|` and
their sum of halfwidths is `|a|+|b|`. Separation therefore requires
`b=0`: their **only** separating direction is horizontal.

If neither e nor f is horizontal, all three pairs are exceptional.
Otherwise relabel directions so e is horizontal.

### 6.2. Two anchor pairs force a vertical direction

The two matched pairs

    {M0,B0}, {M3,B2}

have center differences `(1/2,-1)` and `(-1/2,-1)`, respectively,
and all four squares are aligned. A separating direction `(a,b)` would
require

    |(+/-1/2)a-b| >= |a|+|b|.

The left side is at most `|a|/2+|b|`, so necessarily `a=0`. Their
**only** separating direction is vertical.

If f is vertical, Section 5 gives exactly three exceptions. If f is not
vertical, both matched pairs are exceptional. We now show a third pair
must also remain exceptional.

### 6.3. The remaining direction cannot separate the whole three-square cluster

Every pair among M1,F,G overlaps in horizontal projection, by Section 5.
If f separated all three pairs, their three projection intervals would
have pairwise disjoint open interiors. They could therefore be ordered
as a three-square projection chain. Every unit square has projection
width at least one, so its extreme center projections would differ by
at least two. In particular some two cluster centers would have
Euclidean distance at least two.

But all three centers lie in a rectangle of width `11/10` and height
`87/80`. Its squared diameter is

    (11/10)^2+(87/80)^2=15313/6400<4.

Every cluster center distance is strictly smaller than two. Thus f
cannot separate all three pairs. At least one cluster pair is exceptional
for both e and f, in addition to the two matched anchor pairs.

All direction cases are exhausted. Every pair of directions leaves at
least three exceptional pairs, and the original coordinate directions
attain that count.

## 7. Precise global consequence

This is an obstruction to an **unconditional closed-Q small-exception
cover theorem**, not to the sharp radius conjecture. The construction
still has the actual x-four-chain M0,M1,M2,M3 and the disjoint x-three-chain
B0,B1,B2, so the existing physical four-plus-three theorem explains its
sharp lower bound without any small-exception cover.

A possible future global reduction must therefore be stated as either:

* a theorem restricted to strict subcritical packings `q<Q`; or
* a genuine disjunction allowing the proved physical terminals as well
  as whatever residual direction-cover class is established.

Neither of those missing global implications is proved here. No canonical
root is closed, no original root count is changed, and no global equality
classification is claimed by this example.
