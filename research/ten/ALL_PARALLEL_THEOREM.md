# Ten parallel squares: sharp radius and complete equality family

**Status: complete hand proof for a common square orientation.** The centers
are arbitrary: no row, column, grid, or stratification hypothesis is imposed.
The proof below is self-contained and uses no optimization result or numerical
case enumeration. It has not been formalized or checked by the Lean kernel.
Independently rotated squares remain outside this theorem.

## The theorem

Let ten unit squares with a common edge orientation and pairwise disjoint
interiors lie in a disk of radius `R`. Then

\[
                         R^2\ge Q:=\frac92.
\]

Equality holds precisely for the following family, up to an isometry of the
plane and relabeling. Set

\[
                   h=\frac{\sqrt{17}-1}{2}.
\]

There are four squares centered at `(±1,±1)`. The remaining centers are

\[
 (-\ell,0),\quad (r,0),\quad (0,z_1),(0,z_2),(0,z_3),(0,z_4),
\]

where

\[
 1\le\ell,r\le h,\qquad
 -h\le z_1,\qquad z_{i+1}-z_i\ge1\ (i=1,2,3),\qquad z_4\le h.
 \tag{E}
\]

Thus the least radius within the entire parallel class is `3/sqrt(2)`, and
the six-parameter construction family is exhaustive within that class.

Translate the disk center to the origin and rotate the common edge axes to
horizontal and vertical. For a square center `p=(x,y)`, write

\[
 F(p)=(|x|+\tfrac12)^2+(|y|+\tfrac12)^2.
\]

Containment is exactly `F(p)≤q`, where `q=R²`. Distinct centers satisfy

\[
                |x_i-x_j|\ge1\quad\hbox{or}\quad |y_i-y_j|\ge1.
 \tag{S}
\]

Boundary contacts are allowed throughout. We need only consider `q≤Q`:
for `q>Q` the lower bound is immediate.

## 1. Exact bounds around a four-chain

A horizontal chain is a sequence whose consecutive x-coordinate gaps are
at least one. Vertical chains are defined similarly.

Every center satisfies

\[
                        |x|,|y|<\frac{25}{16}.                \tag{1}
\]

Indeed, if `|x|≥25/16`, then

\[
 F(p)\ge(\tfrac{33}{16})^2+\tfrac14
       =\frac{1153}{256}>\frac{1152}{256}=Q.
\]

There is no horizontal or vertical chain of five, because its endpoint
coordinate gap would be at least four, whereas (1) gives a gap below `25/8`.

Let `M1,M2,M3,M4` be a horizontal four-chain. Its x-coordinates belong,
respectively, to

\[
 (-\tfrac{25}{16},-\tfrac{23}{16}),\quad
 (-\tfrac9{16},-\tfrac7{16}),\quad
 (\tfrac7{16},\tfrac9{16}),\quad
 (\tfrac{23}{16},\tfrac{25}{16}).                            \tag{2}
\]

Its two outer centers satisfy

\[
                       |y_{M_1}|,|y_{M_4}|<\frac38.          \tag{3}
\]

Otherwise their containment bound would exceed

\[
 (\tfrac{31}{16})^2+(\tfrac78)^2
    =\frac{1157}{256}>Q.
\]

Every center `P` other than these two outer centers satisfies

\[
                              |x_P|<\frac75.                \tag{4}
\]

For if `x_P≥7/5`, containment implies `|y_P|<1/2`, since
`(19/10)²+1=461/100>Q`. Its x-distance from `M4` is below
`max(25/16−7/5,25/16−23/16)=13/80`, and its y-distance is
below `1/2+3/8=7/8`. This contradicts (S). The left side is symmetric.
All these facts have vertical counterparts.

Two disjoint horizontal four-chains are impossible. Their left endpoints
would have x-distance below `1/8` and y-distance below `3/4`, contradicting
(S). The same holds vertically.

## 2. Horizontal and vertical four-chains cannot coexist among ten squares

Suppose there are a horizontal four-chain `M` and a vertical four-chain `V`.
Their four outer centers are all distinct. An outer center of `M` cannot
belong to `V`: every center of `V` has `|y|>7/16` by the vertical version of
(2), whereas (3) gives `|y|<3/8` for an outer center of `M`. The symmetric
argument handles the outer centers of `V`. Thus any common centers are
middle centers, and the chains intersect in zero, one, or two squares.

All their middle centers lie in the open box

\[
                       B=(-\tfrac9{16},\tfrac9{16})^2.       \tag{5}
\]

For example, `M2` horizontally overlaps both outer centers of `V`, since
`9/16+3/8=15/16<1`. Also `|y_M2|<23/16`: the contrary, together with
`|x_M2|>7/16`, would give

\[
 F(M_2)>(\tfrac{15}{16})^2+(\tfrac{31}{16})^2
       =\frac{1186}{256}>Q.
\]

So `M2` lies vertically between the two outer centers of `V`. Separation
from them forces `−9/16<y_M2<9/16`. The other middle centers follow by
symmetry.

Every center other than the four outer centers lies in

\[
                          C=(-\tfrac75,\tfrac75)^2,          \tag{6}
\]

by applying (4) in both directions.

### No common middle center

The four distinct middle centers lie in `B`. A quadrant of `B` has both
coordinate widths below one, so (S) allows at most one center in each
quadrant. Assign coordinate axes to the nonnegative side; four centers
therefore occupy all four quadrants.

Comparison with the middle center of opposite y-sign and the same x-sign
forces `|y|>7/16`; comparison across x forces `|x|>7/16`. Thus all four
middle centers satisfy

\[
                   \frac7{16}<|x|,|y|<\frac9{16}.             \tag{7}
\]

Any additional center in `C` has a middle center with the same two signs.
Both coordinate differences are strictly below

\[
                 \max(\tfrac9{16},\tfrac75-\tfrac7{16})
                       =\frac{77}{80}<1,
\]

contradicting (S). There are at most eight centers in this case.

### Exactly one common middle center

Reflect axes if needed so that the common center `A` is the left middle
center of `M` and the lower middle center of `V`. Then

\[
                  -\tfrac9{16}<x_A,y_A<-\tfrac7{16}.
\]

Call the other middle center of `M` `D`, and that of `V` `T`. We know
`7/16<x_D<9/16`, `7/16<y_T<9/16`, and both lie in `B`.
Separation of `D,T` forces either

\[
                x_D-x_T\ge1\quad\hbox{or}\quad y_T-y_D\ge1.
\]

The reverse inequalities are impossible in `B`. Exchanging x and y if
necessary, take the first alternative. Then

\[
 -\tfrac9{16}<x_A,x_T<-\tfrac7{16},\qquad
 -\tfrac9{16}<y_A<-\tfrac7{16}<\tfrac7{16}<y_T<\tfrac9{16}.
\]

Any other nonouter center `P` must have `x_P>7/16`. If `x_P≤7/16`, (6)
would make it horizontally overlap both `A,T`. To avoid them vertically,
it would have to lie below `A` by at least one, above `T` by at least one,
or in the gap between them at distance at least one from each. The first
two possibilities require `|y_P|>23/16>7/5`; the third requires
`y_T−y_A≥2`, although that gap is below `9/8`. All are impossible.

Thus, apart from the four outer centers and `A,T`, all centers are in the
strip `7/16<x<7/5`, whose width is `77/80<1`. They must be pairwise
vertically separated. Since their y-coordinates lie in an interval of
length `14/5<3`, there are at most three, including `D`. Hence there are
at most `4+2+3=9` centers in this case.

### Exactly two common middle centers

These two centers have opposite x-signs and opposite y-signs, because they
are both middle pairs. Reflect an axis if needed so they are a southwest
center `A` and a northeast center `D`, both satisfying (7).

Any other nonouter center `P` cannot have the same coordinate signs as
`A` or `D`, because (6) and (7) would make both coordinate differences
below `77/80`. Suppose it is in the northwest quadrant. It horizontally
overlaps `A`, so `y_P≥y_A+1>7/16`. It vertically overlaps `D`, so
`x_P≤x_D−1<−7/16`. Hence it lies in

\[
                   (-\tfrac75,-\tfrac7{16})
                    \times(\tfrac7{16},\tfrac75).
\]

Both side lengths are `77/80<1`, so this rectangle holds at most one
center. The southeast rectangle likewise holds at most one. Points on an
axis satisfy the same conclusions when the nonnegative side is chosen;
in particular they do not create another possibility. There are at most
`4+2+1+1=8` centers in this case.

These three cases prove that ten centers cannot have four-chains in both
directions, even at `q=Q`.

## 3. A chain decomposition forces a 4+3+3 pattern

By Section 2, at least one direction has no four-chain. Exchange axes so
that there is no vertical four-chain.

Any four centers with pairwise horizontal distances below one would have
pairwise vertical distances at least one by (S), giving a vertical
four-chain. Consequently every horizontal antichain has at most three
centers.

Partition all centers into at most three horizontal chains as follows.
Process centers in nondecreasing x-order. Append each center to a chain
whose last x-coordinate is at least one smaller, if such a chain exists;
otherwise start a new chain. If a fourth chain were ever needed, the three
existing last centers and the new center would all have x-coordinates in
an interval of length strictly below one. They would form a forbidden
four-element horizontal antichain. Thus at most three chains suffice.

Each chain has length at most four by (1), and two disjoint four-chains
are impossible by Section 1. Ten centers in at most three such chains
must therefore have chain lengths exactly `4,3,3`.

## 4. The 4+3+3 terminal and its equality anchors

Let `M` be the four-chain, and let `L1,L2,L3` and `U1,U2,U3` be the two
three-chains. All six centers of the three-chains satisfy (4). Since each
three-chain has endpoint x-gap at least two, its left endpoint has
`x<−3/5` and its right endpoint has `x>3/5`.

The two left endpoints `L1,U1` horizontally overlap each other and `M1`:
their x-coordinates lie in `(-7/5,−3/5)`, and the largest possible gap to
`M1` is below `25/16−3/5=77/80<1`. Therefore the three centers are
pairwise vertically separated.

Both short-chain left endpoints have `|y|<23/16`. Indeed their absolute
x-coordinate exceeds `3/5>7/16`, so the `1186/256` calculation in Section
2 applies. Since `|y_M1|<3/8`, `M1` must be vertically between the other
two centers: if it were lowest or highest, the opposite extreme would
have absolute y-coordinate greater than `2−3/8=13/8>23/16`.
Consequently

\[
                         |y_{L1}-y_{U1}|\ge2.
\]

The same argument at `M4` gives `|y_L3−y_U3|≥2`. The four short-chain
endpoints therefore satisfy

\[
 x_{L3}-x_{L1}\ge2,\quad x_{U3}-x_{U1}\ge2,\quad
 |y_{L1}-y_{U1}|\ge2,\quad |y_{L3}-y_{U3}|\ge2.              \tag{8}
\]

For real numbers `a,b` with `|a−b|≥2`,

\[
 (|a|+\tfrac12)^2+(|b|+\tfrac12)^2
 =a^2+b^2+|a|+|b|+\tfrac12\ge\frac92.                      \tag{9}
\]

Here `a²+b²≥(a−b)²/2≥2` and `|a|+|b|≥|a−b|≥2`.
Equality holds only when `{a,b}={−1,1}`.

Apply (9) to the two horizontal pairs and the two vertical pairs of (8).
Every coordinate term of the four endpoint containment functions occurs
once, so

\[
 4q\ \ge\ F(L1)+F(L3)+F(U1)+F(U3)\ \ge\ 4\cdot\frac92.
\]

This proves `q≥9/2`. If `q=9/2`, equality holds in all four uses of (9).
The left endpoints have x-coordinate `−1`, the right endpoints have
x-coordinate `1`, and each left or right pair has y-coordinates `−1,1`.
Thus the packing contains exactly the four anchor centers

\[
                            (\pm1,\pm1).                    \tag{10}
\]

No choice of the diagonal pairing of these four centers affects (10).

## 5. Complete equality classification within the parallel class

Assume `q=Q` and use the anchors (10). Every remaining center satisfies
`|x|,|y|≤h<2`. If both coordinates were nonzero, the anchor with the same
two coordinate signs would differ by strictly less than one in each
coordinate. This contradicts (S). Hence each of the six additional
centers is on a coordinate axis. Conversely an axis center with absolute
nonzero coordinate at most `h` lies in the disk.

The origin cannot be among these six centers. If it were, all others on
the axes would have absolute nonzero coordinate at least one. Each of the
four half-axis intervals `[1,h]`, of length below one, could contain at
most one center; with the origin this gives at most five additional
centers, whereas six are required.

There are at most four centers on either axis, since `2h<4`. Moreover,
three centers on an axis force one to have absolute coordinate below one:
otherwise each of its two intervals `[-h,-1]`, `[1,h]` would contain at
most one. Three centers on each axis would therefore give two centers,
one on each axis, whose two coordinate differences are both below one.
This is impossible. Thus the axis counts are `4,2` or `2,4`.

Exchange axes so that the vertical axis has four centers, ordered as
`z1<z2<z3<z4`. Their containment and separation conditions are exactly
those for the `z` parameters in (E). In particular,

\[
                       |z_2|,|z_3|\le h-1<1.
\]

Each horizontal-axis center must therefore have absolute x-coordinate
at least one. There is at most one on each side, because `h−1<1`.
They are precisely `(-ell,0)` and `(r,0)` with `1≤ell,r≤h`.
This proves necessity of (E).

Conversely, every parameter choice in (E) gives a packing. The four
anchors have `F=Q`. Every additional axis center has `F≤Q`, because
`(h+1/2)²+1/4=Q`. The four vertical centers are separated by their unit
gaps. Each is horizontally separated from both horizontal centers and
from each anchor. Each horizontal center is vertically separated from
the anchors on its own side, horizontally separated from the opposite
anchors, and horizontally separated from the other horizontal center.
Thus all interiors are disjoint.

This completes the sharp radius and equality theorem for all parallel
unit-square packings of size ten.

## Scope of the remaining problem

The theorem makes no restriction on the centers but does require a common
square orientation. The general `Packing` predicate permits independently
rotated squares. Its disk-containment and separation conditions do not
imply `F≤q` and (S) in a single frame, so the proof does not establish the
unrestricted n=10 theorem. The construction proves the unrestricted upper
bound; the unrestricted lower bound and global equality extraction remain
open.
