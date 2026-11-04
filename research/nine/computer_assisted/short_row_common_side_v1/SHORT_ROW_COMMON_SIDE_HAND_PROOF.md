# The actual short row is on one side of a nearly horizontal four-row

November 4, 2026. Complete rational cover, independently reconstructed
exact replay, and hand derivation. This is a conditional structural lemma,
not an original-cell or whole-mask exclusion. No Lean, Lake or CI.

## Statement

Retain seven distinct physical original unit squares `A,H,I,D,E,F,G`,
with pairwise disjoint open interiors in a disk of squared radius at most
`Q=1105/256`. Assume

\[
x_A\le x_H\le x_I\le x_D,\qquad
 |y_H-y_A|+|y_I-y_H|+|y_D-y_I|\le23/100.
\]

Assume `EF` and `FG` are actual horizontal projection links **and retain
the original center-cone comparisons**:

\[
x_F-x_E\ge h_E+h_F,\quad x_G-x_F\ge h_F+h_G,
\qquad |y_F-y_E|\le x_F-x_E,quad |y_G-y_F|\le x_G-x_F.
\]

Then all three centers `E,F,G` are strictly above every center in
`A,H,I,D`, or all three are strictly below every center in that row.
The frames of all seven originals remain independent and unrestricted.

The center-cone comparisons are existing hypotheses of every original
four-plus-three mask. They must not be omitted when this lemma is reused.
The same original nine-square caller retains its two other squares,
all 36 physical pairs and every marked mask bit.

## 1. Universal center and difference bounds

A unit square with center `c`, orthonormal axes `u,v`, and four corners
inside the `Q` disk satisfies

\[
 Q\ge |c|^2+\tfrac12+|c\cdot u|+|c\cdot v|
      \ge |c|^2+|c|+\tfrac12.
\]

At `r=91/60`, the last expression exceeds `Q` by exactly `31/57600`.
Thus every center has norm strictly less than `r`; the proof below safely
uses the closed bound `|c|<=r`. Pairwise disjoint open incircles imply
`|c_i-c_j|>=1`, including contact.

Put `U=23/100`. For an adjacent row gap `(d,w)`, horizontal order and
unit center separation imply `d>=sqrt(1-w^2)`, with `|w|<=U`. Since
`(97/100)^2+U^2<1`,

\[
 d\ge1-\frac{23}{197}|w|.
\]

Indeed `1-sqrt(1-w^2)=w^2/(1+sqrt(1-w^2))<=23|w|/197`.
Summing all three adjacent gaps gives
`x_D-x_A>=3-529/19700`. Summing the appropriate two gives the analogous
`2-529/19700` lower bound. Each single gap is at least `97/100`.
Together with the closed center-radius bound, these imply

| Center | Closed horizontal interval |
|---|---|
| A | `[-91/60,-29/20]` |
| H | `[-11/20,-9/20]` |
| I | `[9/20,11/20]` |
| D | `[29/20,91/60]` |

For the outer-endpoint comparison, the unused positive rational margin
is `383/59100`. Actual short-row links imply horizontal gaps at least
one because every unit-square projection halfwidth is at least one half.
Therefore

| Center | Closed horizontal interval |
|---|---|
| E | `[-91/60,-29/60]` |
| F | `[-31/60,31/60]` |
| G | `[29/60,91/60]` |

## 2. Each short-row center has a definite side

For every horizontal coordinate in `[-r,r]`, one of the four actual row
center coordinates is within `11/20`: the largest possible neighboring
gap from the table is `11/10`, and the two endpoint overhangs are at most
`1/15`. If another center had height between the row's minimum and
maximum heights, its squared distance from that nearest row center would
be at most

\[
 (11/20)^2+(23/100)^2=1777/5000<1,
\]

contradicting the original incircles. Thus each of E,F,G is strictly
above all four row centers or strictly below all four.

If their three sides are mixed, an adjacent pair switches side. Horizontal
reflection with simultaneous reversal of both original lists moves a
switch on FG to EF. Vertical reflection, if necessary, makes E below and
F above. These transformations preserve every hypothesis, the radius,
and the complete original physical configuration. There are exactly two
remaining closed patterns: G below or G above. Both are covered below.

## 3. Exact inequalities on a horizontal box

The cover splits only the three E/F/G horizontal intervals. At every node,
intersect them with the unchanged necessary inequalities
`x_F>=x_E+1`, `x_G>=x_F+1`. Each split is into both closed halves of one
resulting interval. Interval intersection discards no physical point;
shared faces remain in both children.

For each center with horizontal interval `[l,u]`, put
`m=0` if the interval contains zero, and otherwise
`m=min(|l|,|u|)`. The circle gives

\[
 |y|\le\sqrt{r^2-m^2}.
\]

For a row center i and short-row center P, let
`D=max(|l_P-u_i|,|u_P-l_i|)`. If `D<1`, unit center separation and the
known side of P give a signed vertical gap at least `sqrt(1-D^2)`.
For `D>=1`, keep the signed gap zero. The remaining inequalities are
`|y_i-y_j|<=U` for all row-center pairs and the two short center cones,
whose horizontal upper bounds come from the current box.

Every square root is enclosed by a rational with denominator `10^6`:
round circle upper bounds upward and separation lower bounds downward.
The inequalities are justified by exact integer square comparisons.

All resulting inequalities have form `y_j-y_i<=b`, with an extra node
representing the constant zero. A terminal certificate lists a directed
cycle. Adding its inequalities cancels every height variable and gives
`0<=B<0`, an exact contradiction.

## 4. Complete finite cover and independent replay

`SHORT_ROW_COMMON_SIDE_COVER.json` contains both full closed root trees.
No frontier remains.

| G side after normalization | Terminal leaves |
|---|---:|
| Below | 13 |
| Above | 25 |
| Total | 38 |

The maximum depth is 9. The independent replay checks all 38 cycles,
comprising 156 listed inequalities; its least positive contradiction
reserve is exactly `7667/3000000`. It reconstructs every interval,
all propagation, all root enclosures, all inequalities and every cycle.
It imports no producer code and uses integer bisection instead of the
producer's integer-square-root routine.

The checker also verifies that every internal node has precisely both
closed children and that every leaf is an exact contradiction. The
rational cover plus the preceding physical reduction proves the stated
common-side lemma throughout the continuous original domain.

## 5. Corollary: signs of the endpoint-pair separators

No additional square center can have `x>=29/20`: it would be within
squared distance at most

\[
 (1/15)^2+4\bigl((91/60)^2-(29/20)^2\bigr)=179/225<1
\]

of D. Similarly every additional center has `x>-29/20`, using A.
Combining this with the two actual short gaps gives

\[
 -29/20<x_E<-11/20,\qquad
 11/20<x_G<29/20.
\]

Hence `0<x_E-x_A<29/30<1` and
`0<x_D-x_G<29/30<1`. If EFG is below the four-row, a physical separating
normal from A toward E, or from D toward G, must have strictly negative
vertical component: a nonnegative component would make its center
projection at most the horizontal difference, below one, whereas the
sum of the two incircle supports is one. If EFG is above, both separator
vertical components are strictly positive.

This keeps the genuine original separator owners. It supplies the joint
vertical-side condition missing from two independently reflected endpoint
pair caps; it does not itself assert a stronger tilted cap or row terminal.
