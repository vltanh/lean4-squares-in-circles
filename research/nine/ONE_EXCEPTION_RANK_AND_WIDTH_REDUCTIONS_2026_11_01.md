# One exceptional pair: proved rank and width reductions

November 1, 2026. Hand arguments only. **The full one-exception class remains
OPEN.** This note records proved reductions, not a replacement roadmap or a
claim that the surviving geometric domains have been exhausted.

## Setting and dependencies

Let nine actual unit squares lie in a disk with squared radius
\(q\le Q=1105/256\). Fix an orthonormal coordinate frame such that every
pair except \(E_1,E_2\) has disjoint open projections in x or y. Assume the
exception is genuine: its projections overlap in their interiors in both
coordinates. Write \(h_S\ge1/2\) for a square's common x/y halfwidth.

The x and y projection orders are the actual orders

\[
 S<_xT\iff x_T-x_S\ge h_S+h_T,
 \qquad S<_yT\iff y_T-y_S\ge h_S+h_T.
\]

Every center satisfies \(|c_S|<r_0=61/40\), as shown in
`TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md`. Each order
therefore has height at most four. Each has width at most five: a six-element
x-antichain would contain the exceptional pair and four other squares;
the four others and either exceptional square would give a five-element
y-chain, a contradiction. Interchange coordinates for the other width.

The named inputs below are:

* the actual four-perimeter-chain grid bound \(q\ge9/2\) and Greene's
  nine-element extraction lemma, both proved or precisely stated in the
  two-direction manuscript;
* the physical pair-span inequality and sharp endpoint-span terminal in
  `ONE_EXCEPTION_PAIR_SPAN_AND_SHARP_TERMINAL_2026_11_01.md`.

In particular, for any physical pair,

\[
 \max(|\Delta x|,|\Delta y|)+h_1+h_2\ge2,
\]

strictly for a genuine exceptional pair. This follows by inscribing in
each square the aligned square of halfwidth \(1/(4h_i)\). The terminal
needs only four distinct actual endpoints with spans

\[
 x_R-x_L\ge2+h_L+h_R,\qquad
 x_D-x_C\ge1+h_C+h_D.
\tag{T}
\]

It then gives \(q\ge Q\). If either displayed span is strict, the endpoint
cap inequalities exclude even \(q=Q\). No unproved comparison is inferred
solely from different rank values.

## 1. When both projection heights are at most three

Give each square its pair \((r_x,r_y)\) of longest-chain ranks. A comparison
strictly increases its corresponding rank. Therefore only \(E_1,E_2\)
can share a rank pair: any other two squares are comparable in at least
one actual order. Thus there are either nine distinct pairs, filling
\(\{1,2,3\}^2\), or eight occupied rank cells with the exceptional pair
duplicated in one cell and exactly one other cell missing.

In a fixed row, any two squares other than the exceptional pair are
x-comparable: their equal y-ranks prevent y-comparability. The direction
of their x-comparison agrees with increasing x-rank. The analogous
statement holds for a fixed column. These are the only row/column
comparisons used here.

### 1a. Nine distinct rank pairs: intact perimeter cases

The four perimeter three-chains, and hence \(q\ge9/2>Q\), are present in
either of the following cases:

* the two exceptional rank pairs differ in both coordinates;
* they share the middle row or the middle column.

In the first case no row or column contains both exceptional squares.
In the second, none of the four perimeter lines contains both. Every
pair used on each perimeter line is therefore an actual comparison.

If the exceptional pair shares a boundary row, it cannot occupy columns
1 and 3: the square in column 2 would be x-after the first and x-before
the second, making the exceptional pair x-comparable by transitivity.
The corresponding assertion holds for a boundary column. Thus the only
distinct-rank cases not covered here have the exceptional pair in
**adjacent cells on one perimeter edge**.

### 1b. A duplicated cell and a missing central cell

If the missing cell is \((2,2)\), choose one exceptional square to
represent its duplicated cell and discard the other for this argument.
All eight perimeter cells are now represented by distinct squares. Each
perimeter line consists of three actually comparable squares, since no
chosen pair is the exceptional pair. Again \(q\ge9/2>Q\).

### 1c. A duplicated central cell and a missing corner

Suppose the exceptional pair both have rank \((2,2)\), and the missing
cell is a corner. Both the middle row and the middle column are complete.
The pair-span inequality gives at least one of

\[
 |\Delta x_E|+h_{E_1}+h_{E_2}>2,
 \qquad |\Delta y_E|+h_{E_1}+h_{E_2}>2.
\]

Suppose the first holds; the second is the coordinate-interchanged case.
Let \(L,R\) be the squares in middle-row cells \((1,2),(3,2)\). They
satisfy all four actual comparisons

\[
 L<_xE_1,\quad L<_xE_2,\quad E_1<_xR,\quad E_2<_xR.
\]

The x-projection union of the exceptional pair has width at least
\(|\Delta x_E|+h_{E_1}+h_{E_2}>2\). Since the right edge of \(L\)
lies before both exceptional left edges and the left edge of \(R\)
lies after both exceptional right edges,

\[
 x_R-x_L>2+h_L+h_R.
\]

This argument uses the actual minimum left edge and maximum right edge;
it does not assume their order is the order of the exceptional centers.
The boundary row opposite the missing corner is complete and supplies a
disjoint actual x-three-chain, hence the short span in (T). The terminal
excludes \(q\le Q\). No bound on the exceptional vertical gap is needed.

The remaining duplicated-rank patterns are explicitly: a noncentral
duplicated cell with a missing boundary cell, or a central duplicated
cell with a missing edge-middle cell. This list excludes the proved
cases 1b and 1c; it does not assert the remaining patterns are feasible.

## 2. The entire width-five branch satisfies the sharp lower bound

Suppose the x-order has width five. Its five-element antichain contains
\(E_1,E_2\); the other three y-intervals form three single-square blocks
before or after the overlapping exceptional interval block. The pair-span
note proves that the exceptional block is internal. After reflecting y,
the four ordered blocks can be written

\[
 D,\quad C,\quad \{E_1,E_2\},\quad U.
\]

The actual chains \(D<_yC<_yE_i<_yU\), and the center-radius bound, give

\[
 2-r_0<y_{E_i}<r_0-1,
 \qquad |y_{E_2}-y_{E_1}|<2r_0-3=\frac1{20}.
\tag{1}
\]

Before reflection the signs may be negative; in all cases
\(|y_{E_i}|>2-r_0=19/40\). Physical disjointness also gives
\(|c_{E_2}-c_{E_1}|\ge1\), so

\[
 |x_{E_2}-x_{E_1}|>\frac{39}{40}. \tag{2}
\]

For example \((39/40)^2+(1/20)^2=1525/1600<1\), which proves (2)
directly. A y-antichain of size five would force the coordinate-interchanged
version of (1), namely \(|\Delta x_E|<1/20\), contradicting (2).
Consequently the y-order has width at most four and height exactly four.

Apply Greene's extraction lemma to the y-order. Two actual y-chains of
sizes four and three give the sharp theorem immediately. In the other
alternative it gives disjoint y-antichains \(A,B\) of sizes four and
three. If the exceptional pair is split between them, or not jointly
present, both are actual x-chains and again give the theorem.

Suppose the pair belongs to the four-antichain \(A\). Its x-projections
form three ordered blocks: two singles and the overlapping exceptional
block. The exceptional block cannot be an end block. For example, if it
comes after both singles, its lesser x-center exceeds \(2-r_0=19/40\).
By (2), the greater exceeds \(58/40\). Its y-coordinate has absolute
value greater than \(19/40\), so its squared norm exceeds

\[
 \frac{58^2+19^2}{1600}=\frac{3725}{1600}
 >\frac{3721}{1600}=r_0^2,
\]

a contradiction. Reflection handles the other end.

Thus \(A\) has actual outside comparisons
\(L<_xE_i<_xR\). By (1), the nearby-height pair-span corollary gives
horizontal exceptional-union width strictly greater than two. The
three-antichain \(B\) is an actual x-three-chain. This gives (T), with
strict long span, and excludes even equality.

It remains to treat a Greene antichain pair of sizes four and three in
which the exceptional pair lies in the three-antichain. The four-antichain
is an actual x-four-chain; call its endpoints \(M_L,M_R\). They satisfy

\[
 -r_0<x_{M_L}<-\frac{59}{40},\qquad
 \frac{59}{40}<x_{M_R}<r_0,\qquad
 |y_{M_L}|,|y_{M_R}|<\frac25.
\tag{3}
\]

The horizontal assertions follow from the four-chain center span of at
least three. The vertical assertions follow from
\((59/40)^2+(2/5)^2>r_0^2\).

By (1) and (3), the y-coordinate gap between either exceptional square
and either long-chain endpoint is less than

\[
 \frac{21}{40}+\frac25=\frac{37}{40}<1.
\]

Those pairs are not exceptional, so all must separate in x. The center
disk excludes placing any exceptional square outside the long endpoints:
a further unit center gap beyond \(59/40\) would exceed \(r_0\).
Consequently both exceptional centers satisfy

\[
 -\frac{21}{40}<x_{E_i}<\frac{21}{40}. \tag{4}
\]

Let \(T\) be the other square in the three-antichain. It is x-separated
from both exceptional squares. Since their x-intervals overlap, its
x-interval lies wholly before or wholly after their interval union.
Reflect x so it lies before. By (2) and (4), the exceptional square with
the smaller x-center has center less than
\(21/40-39/40=-18/40\). Therefore

\[
 -r_0<x_T<-\frac{58}{40},\qquad |y_T|<\frac12,
\]

where the last bound follows from
\((58/40)^2+(1/2)^2>r_0^2\). Comparing with \(M_L\), we now have

\[
 |x_T-x_{M_L}|<\frac3{40}<1,\qquad
 |y_T-y_{M_L}|<\frac12+\frac25=\frac9{10}<1.
\]

Thus \(T,M_L\) cannot separate along either coordinate, contradicting
the one-exception premise. The reflected case is identical. This closes
the damaged three-antichain branch without assuming its missing short span.

**Conclusion.** Every one-exception nine-square packing for which either
projection order has width five satisfies \(q\ge Q\). The direct
four-plus-three-chain alternative may retain equality; the damaged
antichain alternatives above are excluded throughout \(q\le Q\).
No full equality classification for this width-five class is asserted.

## 3. What remains for the full one-exception theorem

The proved reductions above leave these precisely scoped obligations:

1. With both heights at most three: the adjacent-exception perimeter-edge
   patterns and the duplicated/missing boundary patterns listed in Section 1.
2. With both widths at most four and at least one height four: Greene gives
   an actual four-plus-three chain terminal, or disjoint opposite-order
   antichains of sizes four and three. The latter is already closed if it
   does not contain the exceptional pair in a single part. If it does,
   the required physical long or short span must still be proved; the
   width-five small-gap estimate is unavailable in this branch.

The width-five branch has no remaining lower-bound obligation after
Section 2. Its complete equality classification is a separate question.

These reductions neither close the full one-exception class nor imply
that unrestricted nine-square packings possess such a cover. They add
no gate IDs, alter no original root status, and make no global optimality
or equality-classification claim.
