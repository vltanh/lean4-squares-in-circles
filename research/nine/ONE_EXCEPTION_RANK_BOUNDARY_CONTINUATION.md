# One exceptional pair: augmented-grid closure and the remaining end-pair terminal

November 1, 2026. Hand proof continuation. No scripts, Lean or CI.
The full one-exception theorem remains open; the precise remaining
end-pair issue is isolated below.

Throughout, \(Q=1105/256\), every square is physical and contained in a
disk of radius \(R\le\sqrt Q\), and a fixed orthonormal frame separates
all pairs except a genuine exceptional pair \(E_1,E_2\). Write \(h_S\)
for the common x/y projection halfwidth of square \(S\), and put
\(g_S=1/(4h_S)\). Thus \(1/2\le h_S\le1/\sqrt2\).

## 1. A one-corner support loss still exceeds the sharp target

For any square and any diagonal sign vector \(P=(\pm1,\pm1)\),

\[
 2h_S+H_S(P)\ge2,
 \qquad h_S+g_S+H_S(P)\ge\frac5{2\sqrt2}. \tag{1}
\]

The first inequality is the orientation bound in the two-direction hand
proof. Here is a complete derivation of the second. Let \(a\ge b\ge0\)
be the absolute physical side-axis components, with \(a^2+b^2=1\).
For either diagonal sign, \(H_S(P)=a\). Put \(p=a+b\in[1,\sqrt2]\).
Then

\[
 h_S+g_S+H_S(P)
 =p+\frac1{2p}+\frac12\sqrt{2-p^2}=:F(p).
\]

On \(1<p<\sqrt2\),

\[
 F''(p)=\frac1{p^3}-\frac1{(2-p^2)^{3/2}}\le0,
\]

because \(p\ge1\ge\sqrt{2-p^2}\). Thus \(F\) is concave on the
closed interval by continuity, and its minimum is attained at an endpoint.
The endpoint values are \(F(1)=2\) and
\(F(\sqrt2)=5/(2\sqrt2)\), proving (1).

Suppose four distinct actual endpoint squares, named \(TL,TR,BL,BR\),
satisfy a sum of perimeter-span inequalities of the form

\[
 (x_{TR}-x_{TL})+(x_{BR}-x_{BL})
 +(y_{TR}-y_{BR})+(y_{TL}-y_{BL})
 \ge4+\sum_{S\ne TL}2h_S+h_{TL}+g_{TL}. \tag{2}
\]

The exceptional reduced coefficient may be at any of the four corners;
the displayed choice is a naming convention. Disk support gives
\(P\cdot c_S+H_S(P)\le\sqrt2R\) for each corresponding outward
diagonal vector. Summing the four support inequalities and using (1)-(2),

\[
 4\sqrt2R\ge10+\frac5{2\sqrt2},
 \qquad
 R\ge\frac{20\sqrt2+5}{16}.
\]

Consequently

\[
 \boxed{R^2\ge\frac{825+200\sqrt2}{256}
       >\frac{1105}{256}.} \tag{3}
\]

The final comparison is exact: \(\sqrt2>7/5\). This terminal tolerates
one full-to-inscribed-halfwidth replacement at a corner and still excludes
the entire closed \(Q\)-disk domain.

## 2. Completing the cover with aligned inner rectangles

The physical square \(S\) contains an aligned square of halfwidth
\(g_S\), with its open interior inside the physical square's interior.
Indeed the absolute physical frame components sum to \(2h_S\), so an
aligned displacement of coordinate size at most \(g_S\) has each
physical frame coordinate at most \(2h_Sg_S=1/2\).

The two inscribed aligned squares for \(E_1,E_2\) have disjoint open
interiors. Hence

\[
 |\Delta x_E|\ge g_{E_1}+g_{E_2}
 \quad\hbox{or}\quad
 |\Delta y_E|\ge g_{E_1}+g_{E_2}.
\]

Choose one such direction and call it x. Replace the exceptional pair's
x-halfwidths by \(g_{E_i}\), keeping their y-halfwidths \(h_{E_i}\).
For each other square use both halfwidths \(h_S\). These are auxiliary
aligned rectangles; they are not asserted to be physical squares or to
lie in the disk.

Every pair of these rectangles separates along x or y. Every former
coordinate separation is retained when the x-halfwidths decrease, and
the exceptional pair now separates in x. The y-order is exactly the
original physical y-projection order. Let the x-proxy halfwidths be
\(\sigma_S\), equal to \(g_S\) on the exceptional pair and \(h_S\)
otherwise.

Both proxy orders have height at most four. A y-five-chain is already
impossible. In an x-five-chain the endpoint center gap is at least
\(2+\sqrt2\): start from five halfwidths \(1/2\), and allow at most
two internal halfwidths to decrease to \(1/(2\sqrt2)\). Placing a small
halfwidth at an endpoint instead decreases the span less. Since
\(2+\sqrt2>61/20\), this contradicts the center-radius bound
\(|c|<61/40\).

### Only one new comparison is needed

Label the exceptional squares so \(x_B>x_A\), and put
\(D=x_B-x_A\ge g_A+g_B\). Add **only** the comparison \(A<B\) to
the original x-order. This is already transitive: no other new comparison
is required. If \(S<_xA\), then

\[
 x_B-x_S\ge D+h_A+h_S
 \ge (g_A+h_A)+g_B+h_S
 \ge1+g_B+h_S>h_B+h_S,
\]

so \(S<_xB\) was an actual comparison. Similarly \(B<_xT\) implies
\(A<_xT\) was already actual. These are all possible transitivity checks
involving the one added relation. It creates no cycle because the pair
was originally incomparable.

Call the resulting order \(P^+\). Together with the unchanged actual
y-order it covers every pair. It is a suborder of the x-proxy order, so
its height is at most four. Its sole nonphysical x-comparison is \(A<B\).

## 3. The complete three-by-three augmented-grid branch is excluded

Suppose both augmented heights are at most three. The full augmented cover makes
the nine longest-chain rank pairs distinct, so they fill all nine cells
of \(\{1,2,3\}^2\).

Every fixed x-rank column is an actual y-three-chain: the y-order was
never changed. In every fixed y-rank row, all pairs other than
\(E_1,E_2\) are **actual** x-comparisons. Indeed their equal y-ranks
exclude an actual y-comparison, and the original one-exception cover then
forces x-separation. The order of such a comparison agrees with the augmented
x-ranks.

If the exceptional pair belongs to different rows, or both belong to
the middle row, the four perimeter three-chains are all actual. The
ordinary grid argument gives \(q\ge9/2>Q\).

Otherwise the exceptional pair shares a boundary row. It cannot occupy
the two outer cells of that row: the middle square would give two actual
x-comparisons joining the pair, contradicting the genuine exception by
transitivity. Thus it occupies adjacent cells on that boundary row.
Reflect coordinates so the row is top and the pair occupies columns 1
and 2. Call the first exceptional square \(E\), the second \(F\), and
the third top-row square \(TR\). The augmented ranks give

\[
 x_F-x_E\ge g_E+g_F,
 \qquad x_{TR}-x_F\ge h_F+h_{TR},
\]

where the second comparison is actual, as just proved. Since
\(g_F+h_F\ge1\), their sum gives

\[
 x_{TR}-x_E\ge1+g_E+h_{TR}. \tag{4}
\]

Take \(TL=E\) and the actual bottom corner squares \(BL,BR\).
The other three perimeter spans are unchanged:

\[
 x_{BR}-x_{BL}\ge1+h_{BL}+h_{BR},
\]
\[
 y_E-y_{BL}\ge1+h_E+h_{BL},\qquad
 y_{TR}-y_{BR}\ge1+h_{TR}+h_{BR}.
\]

Together with (4), they are precisely (2). The weakened-corner support
terminal (3) excludes this last case. Hence **every three-by-three
augmented-grid assignment is impossible at \(q\le Q\)**, with every
exceptional position and every weak boundary covered.

### An additional full original-grid closure using spans of lengths 4, 3, 3, 2

The same support terminal also closes one transverse end-pair case directly
from all nine actual rank cells. Suppose the original rank pairs are all
distinct and the exceptional pair occupies the left-column cells
\(A=(1,2)\), \(B=(1,3)\). Name the remaining rank cells

\[
 L=(1,1),\ M=(2,1),\ R=(3,1),\quad
 C=(2,2),\ D=(3,2),\quad T=(2,3),\ G=(3,3).
\]

Assume the pair is fat in the transverse x direction, ordered with its
edge-middle square farther outward:

\[
 x_B-x_A\ge g_A+g_B. \tag{5}
\]

All comparisons within a row are actual: the only exceptional pair is in
a column. Hence \(B<_xT<_xG\) and \(L<_xM<_xR\). All comparisons within
the right column are actual, giving \(R<_yD<_yG\); also \(L<_yA\)
is actual. Combining (5) with the top row, and using \(g_B+h_B\ge1\),
gives the long span

\[
 x_G-x_A\ge2+g_A+h_G.
\]

The other three selected spans are

\[
 x_R-x_L\ge1+h_L+h_R,\qquad
 y_G-y_R\ge1+h_R+h_G,\qquad
 y_A-y_L\ge h_A+h_L.
\]

Their constant terms sum to \(2+1+1+0=4\). With the four actual endpoint
squares named \(TL=A,TR=G,BL=L,BR=R\), their sum is exactly (2), with
the sole reduced coefficient \(h_A+g_A\). Therefore (3) excludes this
entire closed-\(Q\) case. The four endpoints need not have the same
top/bottom heights; the proof uses precisely the displayed comparisons.

Reflections and interchange of the coordinates give the corresponding
statement for any corner/adjacent-edge exceptional pair when the
edge-middle member is farther outward in the transverse fat direction.
The opposite transverse ordering is not covered by this argument.

## 4. Consequence for the former height-at-most-three frontier

Now assume both original physical projection heights are at most three,
as in the remaining rank-boundary branch of
`ONE_EXCEPTION_RANK_AND_WIDTH_REDUCTIONS_2026_11_01.md`.

After choosing the augmented x-order as above, its y-height is still at
most three. Section 3 excludes augmented x-height at most three. Therefore
any surviving assignment has augmented x-height four and x-width at most
three, since an x-antichain is a y-chain under the complete augmented cover.

Greene's theorem then produces two disjoint augmented x-chains of lengths
four and three. To see the numerical step exactly, if the maximum union
of two chains had size at most six, Greene's partition would have first
part four, second part at most two, and at most three positive parts.
Its total would be at most eight, contradicting nine elements.

The four-chain must contain \(A,B\): otherwise every comparison in it is
actual, contrary to the original x-height bound of three. The pair must
be consecutive in that chain, since an intervening square would make
\(A<B\) an actual comparison by transitivity of the original order.
The disjoint three-chain is therefore entirely actual.

If the exceptional pair is internal in the four-chain, its two outside
comparisons are actual, and

\[
 D+h_A+h_B\ge (g_A+h_A)+(g_B+h_B)\ge2
\]

supplies the long endpoint span. Together with the actual three-chain's
short span, this is the already proved physical sharp terminal. For a
genuine exceptional pair the long span is strict, excluding equality too.

Thus the former adjacent-boundary and duplicated/missing rank patterns
are all routed into **one remaining end-pair terminal**. Up to reflecting
x, there are actual comparisons

\[
 L<_xC<_xA,\qquad L<_xC<_xB,
 \qquad x_B-x_A\ge g_A+g_B,
\]

and a disjoint actual three-chain \(D<_xF<_xG\). The exceptional pair
occupies the end of the augmented four-chain \(L,C,A,B\). The original
rank diagrams no longer need separate geometric exclusions.

### Remaining mathematical obligation

For this end-pair arrangement, the available chain sum gives only

\[
 x_B-x_L\ge2+h_L+g_B,
\]

whereas the existing sharp terminal requires \(2+h_L+h_B\). The missing
amount \(h_B-g_B\) is nonnegative and cannot be silently discarded. The
precise remaining task is to derive the full endpoint span or an equally
strong physical terminal, using all original one-exception separations
and the remaining two squares. The full one-exception
theorem and unrestricted global caller therefore remain open. No original
root count, gate ID or equality classification is changed by this reduction.

The necessity of those remaining bodies is substantive. The exact
construction in
[`END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md`](END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md)
places **eight** physical squares strictly below \(Q\), with only one
coordinate-exceptional pair, both actual projection heights equal to three,
the same weak four-list, a disjoint actual three-chain, and one additional
square. Thus neither the seven-square core nor that core plus one arbitrary
extra square is a valid sharp terminal. A completion-capacity argument must
use the ninth square or an additional consequence proved from all nine.

[`ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md`](ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md)
joins the same augmented-order method to the original height-four branch.
Together these continuations replace the older separate rank/width frontiers
by two physical endpoint patterns: a weak end-pair in the four-list with an
actual three-chain, or an actual four-chain with a weak end-pair in the
three-list. The original height-at-most-three branch treated here can only
produce the first pattern.

### A further nine-body partition restriction

For the remaining lower-bound obligation in this original height-at-most-three
branch, we may take both widths at most four: width five enters the already
proved sharp terminal. An order of height at most two and width at most four
has at most eight elements, by partitioning into its rank levels. Thus both
actual heights here are exactly three. Greene's partition for either actual
projection order has largest part three, at most four parts, and total nine.
Its only possibilities are

\[
 (3,3,3),\qquad (3,3,2,1),\qquad (3,2,2,2).
\]

The last is impossible. Its conjugate is \((4,4,1)\), so two disjoint
antichains have total size eight and must each have size four. At most one
of them contains both exceptional squares. The other is an actual
four-chain in the perpendicular projection order, contrary to that order's
height bound of three. Consequently each actual projection order has
Greene partition either \((3,3,3)\) or \((3,3,2,1)\).

In particular, each actual order has two disjoint three-chains. This is an
additional restriction using all nine bodies, not an assertion that a
single chain partition realizes every Greene maximum simultaneously.
