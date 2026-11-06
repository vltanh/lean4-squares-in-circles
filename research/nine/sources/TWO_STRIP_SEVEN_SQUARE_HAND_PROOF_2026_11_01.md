# A.2 hand theorem: two strips force the sharp seven-square core

> Retained mathematical source. Reproduction commands, checker reports and implementation notes below refer to the [archived version](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/TWO_STRIP_SEVEN_SQUARE_HAND_PROOF_2026_11_01.md); the current task is the [pen-and-paper roadmap](../PROOF_PLAN.md).

This is a hand continuation of the seven-square argument in
[research/nine/computer_assisted/WIDE_SLIDE_SHARP_TERMINAL.md](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/computer_assisted/WIDE_SLIDE_SHARP_TERMINAL.md) at commit
`6ee96ea0b74add3d3b57c4e8ffa9843db17b9f1b`. No program, Lean compilation, CI,
enumeration, or numerical optimization is used in the proof below.

The improvement is that **every horizontal coordinate guard and every
separate anchor-height guard can be removed**. Circle containment and the
two strip occupancies imply the separator-axis choices. The anchor
displacements need not be bounded because the weighted identity retains
their positive quadratic costs.

This remains a conditional theorem. It does not prove that every packing
of nine squares admits these two strips and the stated relative-frame bound.
It closes no original positional root without a caller.

## 1. Theorem

Put `Q=1105/256` and `b=1/64`. Consider seven interior-disjoint closed unit
squares in a disk centered at the origin of squared radius `q`.
In one common orthonormal frame suppose that:

* Four centers lie in the closed strip `-1/16 <= y <= 3/4`.
* Three other centers satisfy `y <= -13/16`.
* Sort the four centers by x and name them `M0,M1,M2,M3`; sort the three by x
  and name them `B0,B1,B2`. Every square has a frame
  `u_i=(a_i,t_i), v_i=(-t_i,a_i)`, where `a_i>=0`, `a_i^2+t_i^2=1`, and
  `|t_i|<=1/64`. The common frame is the physical frame of `M0`, so
  `a_0=1,t_0=0`.

Then `q>=Q`. Two additional squares can have arbitrary physical poses.

At `q=Q` all seven squares are parallel. Their four outer centers are

    M0=(-3/2,1/16),  M3=(3/2,1/16),
    B0=(-1,-15/16),  B2=(1,-15/16).

The other centers are precisely

    M1=(-1/2,1/16+s1), M2=(1/2,1/16+s2), B1=(0,-15/16+r),

where

    0<=s1,s2<=11/16,
    (23-sqrt(1041))/16 <= r <= min(1/8,s1,s2).

Conversely every such choice gives a seven-square packing in the stated
strips at radius squared `Q`. These are seven-square equality parameters;
any eighth and ninth squares must still satisfy all their physical constraints.

## 2. Universal center bound and the bottom-strip x bound

Only `q<=Q` needs consideration. For a contained unit square with center c
and orthonormal frame u,v, maximizing over its four corners gives

    q >= |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Since

    (91/60)^2+91/60+1/2-Q = 31/57600 > 0,

every center satisfies `|c|<91/60`. Also `a_i>=1-b=63/64`, because
`a_i=sqrt(1-t_i^2)>=1-|t_i|`.

For a bottom-strip square choose a corner pointing outward in the x
direction and downward in y. Its absolute x coordinate is at least
`|x|+(a-|t|)/2`, and its negative y coordinate is at least
`-y+(a-|t|)/2`. Here `(a-|t|)/2>=31/64` and `-y>=13/16`.
Consequently, if `|x|>=73/64`, that corner has norm squared at least

    (104/64)^2+(83/64)^2
      = 17705/4096 = Q+25/4096 > Q.

Thus every bottom-strip center satisfies `|x|<73/64`.

The bottom-strip height is bounded below automatically by `y>-91/60`.
In particular its height span is less than `23/32`, since

    91/60-13/16 = 169/240 < 23/32.

The four-center strip has height span at most `13/16`.

## 3. Every sorted chain uses a positive horizontal separator

For two allowed frames write `d=|t_j-t_i|`. The exact total support
halfwidth of the two squares on an axis belonging to either square is

    (1+u_i.u_j+|det(u_i,u_j)|)/2 >= 1+(15/32)d.       (1)

For completeness, `|a_i-a_j|<=2bd`; hence
`|det(u_i,u_j)| >= (1-b-2b^2)d >= (1-2b)d`, while
`u_i.u_j = 1-((a_i-a_j)^2+d^2)/2 >= 1-2bd`.
Their sum proves (1), with `c=15/32`.

Consider consecutive squares in either list sorted by x, so `Delta x>=0`.
The global center bound gives `Delta x<91/30`. On either owned v-axis,

    |v_owner.(Delta x,Delta y)| <= b Delta x+|Delta y|.

This is strictly below `1651/1920<1` in the M list and below
`1471/1920<1` in the B list. Thus no v-axis can separate the pair.
On an owned u-axis the projection is at least `-b|Delta y|>-1`.
Since a separating projection has absolute value at least one, a
u-axis separator must have positive projection. The separating-axis theorem
therefore supplies an actual owner o at one of the two endpoints with

    Delta x >= 1+c|t_j-t_i|-t_o Delta y.              (2)

In particular consecutive horizontal gaps satisfy

    Delta x_M >= 1-13/1024 = 1011/1024,
    Delta x_B >= 1-23/2048 = 2025/2048.              (3)

The gaps are positive, so ties in the initial x ordering are impossible.
No contact equality or common separator direction was assumed.

## 4. The outer cross-pairs automatically use vertical separators

Use index 4 for B0 and index 6 for B2. From the total chain spans in (3),
the M center bound, and the sharper B x bound,

    x_M0 < 91/60-3033/1024,
    x_B0 < 73/64-2025/1024 = -857/1024.

Combining both upper and lower bounds gives

    4679/15360 < x_B0-x_M0 < 10441/15360 < 3/4.

Reflection gives the identical inequality for `x_M3-x_B2`.
For each cross-pair directed from B to M,

    3/4 <= Delta y < 3/4+91/60 = 34/15,
    |Delta x| < 3/4.

An owned u-axis projection has absolute value less than

    3/4+(1/64)(34/15) = 377/480 < 1.

An owned v-axis projection is positive, being at least
`(63/64)(3/4)-(1/64)(3/4)=93/128`.
Thus the actual separating owner satisfies

    Delta y >= 1+c|t_M-t_B|+t_owner Delta x.         (4)

These are exactly the two cross-pair inequalities needed by the sharp
weighted proof. Neither the anchor y neighborhoods nor any x neighborhoods
have been assumed.

## 5. Telescope in the full strips

Write all centers as deviations from the base positions:

    M_i=(-3/2+i+dx_i, 1/16+z_i),             i=0,1,2,3,
    B_j=(-1+j+dx_(4+j), -15/16+z_(4+j)),     j=0,1,2.

There is **no bound on any dx_i** and no additional bound on an anchor z_i.
The strip conditions and the automatic center bound give

    -1/8 <= z_i <= 11/16          for i=0,1,2,3,
    -19/32 < z_i <= 1/8          for i=4,5,6.

The second lower bound follows with reserve `7/480` from
`-91/60+15/16 = -19/32+7/480`.

For any chain with all z in `[L,U]`, let `m=(L+U)/2`, `h=(U-L)/2`.
For either actual owner of an edge the term `-t_owner(z_j-z_i)` equals

    t_i z_i-t_j z_j + m(t_j-t_i)
      +(z_k-m)(t_j-t_i),

where k is the other endpoint. The last term is at least
`-h|t_j-t_i|`. Summing (2) gives

    span-number_of_edges
      >= (c-h)V_chain+t_start z_start-t_end z_end
         +m(t_end-t_start).                           (5)

For M use `(m,h)=(9/32,13/32)`; for B use
`(m,h)=(-15/64,23/64)`. Define

    V_M=|t1|+|t2-t1|+|t3-t2|,
    V_B=|t5-t4|+|t6-t5|,
    V_C=|t4|+|t3-t6|,     V=V_M+V_B+V_C.

For the two cross-pairs let l be the left actual owner tilt, either 0 or t4,
and r the right actual owner tilt, either t3 or t6. Sum (4), retain l,r in
the displacement terms, and bound only their constant terms by max/min:

    (y0-y4-1)+(y3-y6-1)
      >= (c-1/4)V_C-t4/4+(t3+t6)/4
         +l(dx0-dx4)+r(dx3-dx6).                      (6)

All owner cases are included in (5) and (6).

## 6. Why unrestricted anchor displacements cause no difficulty

Use the four corners with frame signs `(-,+),(+,+),(-,-),(+,-)` at anchors
`0,3,4,6`, respectively. Give them weights

    w0=w3=23/64,   w4=w6=9/64.

Put `W_M=23/16`, `W_B=27/64`, `k=207/512`, and
`L_i=s_i x_i+v_i y_i`, `J_i=-v_i x_i+s_i y_i` for these signs.
Weighted corner containment and direct expansion give

    q-Q >= W_M(x3-x0-3)+W_B(x6-x4-2)
          +k[(y0-y4-1)+(y3-y6-1)]
          +sum_A w_i(dx_i^2+z_i^2)
          +sum_A w_i[(a_i-1)L_i+t_i J_i].             (7)

This polynomial identity holds for arbitrary real anchor displacements.
After substitution of (5) and (6), their linear displacement terms have
the following coefficients, writing `w=23/64`, `v=9/64`:

| Anchor | dx coefficient | z coefficient |
|---|---|---|
| 0 | `k l` | `0` |
| 3 | `w(a3-1-t3)+k r` | `w(a3-1-3t3)` |
| 4 | `v(1-a4+t4)-k l` | `v(1-a4+2t4)` |
| 6 | `v(a6-1+t6)-k r` | `v(1-a6-2t6)` |

For any real vector d, coefficient vector L', and positive weight w,

    w|d|^2+L'.d >= (w/2)|d|^2-|L'|^2/(2w).          (8)

Thus no bound on d is needed. With `1-a_i<=b|t_i|`,
`|l|<=|t4|`, and `|r|<=|t3|+|t6|`, the negative quadratic tilt costs in
(8) and the base-corner terms are bounded by

    C3 t3^2+C4 t4^2+C6 t6^2,

where

    C3=2623909/524288,
    C4=484929/262144,
    C6=1647099/524288.

For direct verification put `P=w(1+b)+k`, `H=v(1+b)+k`. These constants are

    C3 = [2P^2+w^2(3+b)^2]/(2w)+k^2/v+25w/16,
    C4 = k^2/(2w)+[H^2+v^2(2+b)^2]/(2v)+31v/16,
    C6 = k^2/w+[2H^2+v^2(2+b)^2]/(2v)+31v/16.

These estimates depend on tilts and the fixed base coordinates, not on
anchor displacement ranges. This is the precise reason the former anchor
boxes are unnecessary.

## 7. Fourteen hand-checkable signed layers

The recentered base linear tilt terms are
`-(23/2048)t3+(45/4096)(t6-t4)`.
Subtract `V/256` from the bound (7), minimize
`V_M>=|t3|` and `V_B>=|t6-t4|`, and use `t_i^2<=b|t_i|`.
It suffices to check `F(X,Y,Z)>=0`, with `X=t3,Y=t4,Z=t6`, where

    2^25 F = 259675|X|-376832X+1866622|Y|
             +1417216|Z-Y|+368640(Z-Y)
             +2836480|X-Z|-1647099|Z|.                (9)

The integer expression makes every entry of the following table checkable
by addition and subtraction alone.

| Nonzero coordinates S | `2^25 F(1_S)` | `2^25 F(-1_S)` |
|---|---:|---:|
| X | 2,719,323 | 3,472,987 |
| Y | 2,915,198 | 3,652,478 |
| X,Y | 5,634,521 | 7,125,465 |
| Z | 2,975,237 | 2,237,957 |
| X,Z | 21,600 | 37,984 |
| Y,Z | 3,056,003 | 3,056,003 |
| X,Y,Z | 102,366 | 856,030 |

For example the smallest positive-layer value is
`259675-376832+1417216+368640-1647099=21600`.

To see that these fourteen directions cover every real triple, decompose
each positive coordinate into positive indicator level layers and each
negative coordinate into negative indicator level layers. Each `|x|`,
each `|x-y|`, and each linear term is exactly the corresponding nonnegative
weighted sum of its layer values. This works also across opposite signs;
zero coordinates and repeated levels give layers of zero length. Hence F
is a nonnegative weighted sum of the displayed positive integers.

Combining (7)--(9) proves, whenever `q<=Q`,

    q-Q >= V/256 + (1/2) sum_A w_i(dx_i^2+z_i^2).       (10)

It follows that `q<Q` is impossible and `q=Q` forces `V=0` and zero anchor
displacements. The variation graph is connected to `t0=0`, so every frame
is parallel. The exact endpoint spans then force every x gap to be one.

## 8. Equality and the remaining caller

The outer B squares horizontally overlap the respective inner M squares,
so the latter must have `s1,s2>=0`. The bottom-middle square horizontally
overlaps both, giving `r<=s1,s2`; reversed vertical order is impossible in
the strips. Its upper strip bound is `r<=1/8`. Its lowest corner gives

    1/4+(-23/16+r)^2 <= Q,

and hence `r>=(23-sqrt(1041))/16`. These are exactly the parameters in
Section 1. Conversely they suffice: all other pairs separate horizontally,
the needed vertical inequalities hold, the inner M corner norms are at
most `41/16<Q`, and the bottom-middle corner bound is exactly the displayed
one. The four fixed anchors attain Q.

**Remaining global obligation.** Prove that every physical counterexample
admits this strip arrangement and relative-frame bound in one M0 frame,
or rule out every counterexample failing those hypotheses. A conditional
strip theorem alone does not discharge A.2, classify all nine-square
equality packings, or remove any entire original root.
