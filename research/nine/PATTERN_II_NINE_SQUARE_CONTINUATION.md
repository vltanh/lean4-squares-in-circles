# Pattern II: a sharp endpoint budget and the five-square complement

November 1, 2026. Hand proof continuation. No scripts, Lean, or CI.

This note works with an actual horizontal four-chain and all five other
squares. It proves a sharp endpoint budget, the side-column capacities,
and the complete one-central-outsider case. Together with the complete
middle-outsider cases in `BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md`
and the two three-square cap proofs cited below, these supply the
Pattern II closure. Every invocation retains all nine physical squares.

## 1. Setup

Put \(Q=1105/256\) and \(\rho=91/60\). Nine physical unit squares
have pairwise disjoint open interiors and lie in the disk \(q\le Q\).
Every pair except \(A,B\) has a coordinate projection separation.
The exceptional pair belongs to the five squares outside an actual chain

\[
 M_0<_xM_1<_xM_2<_xM_3.
\]

For each square write \(h\in[1/2,1/\sqrt2]\) for its common x/y
projection halfwidth, and put

\[
 g=\frac1{4h},\qquad k=\sqrt{\frac12-h^2}.
\]

The x-axis is a fat direction of the exceptional pair:

\[
 |x_B-x_A|\ge g_A+g_B\ge\frac1{\sqrt2}. \tag{1}
\]

We use the center bound \(|c|<\rho\), the exact four-plus-three
endpoint terminal, and the elementary four-chain bounds from
`ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md`. In particular,

\[
 \begin{array}{c|c}
 i&x_{M_i}\ \hline
 0&(-91/60,-89/60)\\
 1&(-31/60,-29/60)\\
 2&(29/60,31/60)\\
 3&(89/60,91/60)
 \end{array} \tag{2}
\]

and the endpoint halfwidths satisfy \(h_0,h_3<8/15\). We may stop
with the sharp lower bound whenever three outsiders form an actual
x-chain, since that chain is disjoint from the displayed four-chain.

## 2. An orientation-sensitive corner bound

For a square with center \((x,y)\), put \(X=|x|\), \(Y=|y|\).
Its four vertices have coordinate offsets, up to reflections,
\((h,k),(-k,h),(-h,-k),(k,-h)\). Thus there is an outward-quadrant
vertex with offsets either \((h,k)\) or \((k,h)\). Consequently

\[
 q\ge\min\{(X+h)^2+(Y+k)^2,
              (X+k)^2+(Y+h)^2\}. \tag{3}
\]

If \(X\ge Y\), the smaller displayed expression is the second, so

\[
 q\ge(X+k)^2+(Y+h)^2. \tag{4}
\]

Both expressions in (3) increase separately in nonnegative X and Y.
Therefore one may replace X,Y by any nonnegative lower bounds before
taking their minimum. This observation avoids assuming that a physical
square's farthest-corner norm is monotone under a change of center
coordinates with its orientation held fixed.

## 3. The actual four-chain has a sharp total transverse budget

**Theorem.** The two endpoints of every actual horizontal four-chain in
the closed Q-disk satisfy

\[
 \boxed{|y_{M_0}|+|y_{M_3}|\le\frac18.} \tag{5}
\]

Equality requires \(q=Q\), all four main halfwidths equal to \(1/2\),
all three actual x-gaps equal to one, and

\[
 x_{M_0}=-\frac32,\quad x_{M_3}=\frac32,
 \quad |y_{M_0}|=|y_{M_3}|=\frac1{16}.
\]

*Proof.* Write \(X_i=|x_{M_i}|\), \(Y_i=|y_{M_i}|\) for the two
endpoints. The previously proved individual bounds
\(X_i>89/60\), \(Y_i<1/5\) justify (4). Hence

\[
 (X_i+k_i)^2+(Y_i+h_i)^2\le q.
\]

The actual chain gives
\(X_0+X_3\ge2+h_0+h_3\). The triangle inequality in the plane,
applied to the two vectors \((X_i+k_i,Y_i+h_i)\), therefore gives,
with \(S=Y_0+Y_3\),

\[
 4q\ge
 (2+h_0+k_0+h_3+k_3)^2+(S+h_0+h_3)^2. \tag{6}
\]

Suppose \(S\ge1/8\). On \(1/2\le h_i\le8/15\), we have
\(k_i>23/50\), \(h_i+k_i\le1\), and

\[
 0\le\frac{h_i}{k_i}-1<\frac{11}{69}.
\]

For fixed S the derivative of the right side of (6) with respect to
either endpoint halfwidth is at least

\[
 -8\frac{11}{69}+2\left(\frac18+1\right)
 =\frac{269}{276}>0.
\]

It is therefore minimized at \(h_0=h_3=1/2\). Formula (6) implies

\[
 4Q\ge16+(S+1)^2\ge16+\left(\frac98\right)^2=4Q.
\]

This proves (5). Equality forces both endpoint halfwidths to be \(1/2\)
and equality in every displayed inequality. Equality in the planar
triangle inequality and in the two endpoint norm bounds makes the
vectors equal to \((2,9/16)\), giving the stated endpoint coordinates.
Equality in the chain span forces both internal halfwidths to be
\(1/2\) and every x-gap to equal one. QED.

The same result holds after interchanging the two axes. In particular,
every endpoint of an actual vertical four-chain has \(|x|\le1/8\).

## 4. All five outsiders lie in a strictly narrower vertical strip

**Lemma.** Every outsider F satisfies

\[
 \boxed{|x_F|<\frac{13}{12}.} \tag{7}
\]

*Proof.* Suppose, for example, \(x_F\le-13/12\). Both F and
\(M_0\) have x-centers in \((-\rho,-13/12]\), so their center
gap is less than \(\rho-13/12=13/30<1\). Their x-projections
overlap. This pair is not exceptional, so it is y-separated. By (5),

\[
 |y_F|\ge h_F+h_0-|y_0|\ge h_F+\frac38.
\]

Apply (3) with lower bounds \(X=13/12\), \(Y=h+3/8\). Since
\(13/12>1/\sqrt2+3/8\), the second expression is smaller, and

\[
 q\ge F(h):=\left(\frac{13}{12}+k\right)^2
                +\left(2h+\frac38\right)^2.
\]

For \(1/2<h<1/\sqrt2\),

\[
 F''(h)=6-\frac{13/12}{k^3}<0,
\]

because \(k\le1/2\). Thus F is concave, and its minimum on the
closed interval occurs at an endpoint. Those values are

\[
 F(1/2)=\frac{2533}{576}>Q,
\]
\[
 F(1/\sqrt2)=\frac{1909}{576}+\frac{3\sqrt2}{4}
 >\frac{1909}{576}+\frac{21}{20}>Q.
\]

Here \(\sqrt2>7/5\) gives the last rational comparison. This is
a contradiction. Reflection proves the right-hand bound. QED.

## 5. Three columns for the five outsiders

Partition the outsiders into

\[
 \mathcal L=\{F:x_F\le-29/60\},\qquad
 \mathcal C=\{F:|x_F|<29/60\},\qquad
 \mathcal R=\{F:x_F\ge29/60\}.
\]

Every two centers in \(\mathcal L\) have x-gap less than
\(13/12-29/60=3/5\), and the same is true in \(\mathcal R\).
By (1), neither side column contains both exceptional squares.
Furthermore every square in \(\mathcal L\) overlaps \(M_1\)
horizontally, and every square in \(\mathcal R\) overlaps \(M_2\)
horizontally: (2) and (7) bound the relevant gaps by less than one.

Consequently \(\mathcal L\cup\{M_1\}\) is an actual y-chain,
and \(\mathcal R\cup\{M_2\}\) is an actual y-chain. A four-chain
entirely in either side column would have both endpoints at
\(|x|\ge29/60>1/8\), contradicting (5) with the axes interchanged.
Therefore

\[
 \boxed{|\mathcal L|\le2,\quad |\mathcal R|\le2,
        \quad |\mathcal C|\ge1.} \tag{8}
\]

Every central outsider overlaps both \(M_1,M_2\) horizontally,
because its x-gap from either is strictly less than
\(29/60+31/60=1\). Thus every central outsider is y-separated from
both inner main squares. Any two central outsiders have x-gap less
than \(29/30<1\), so they too are y-separated unless they are
the exceptional pair.

## 6. The case of one central outsider

Suppose \(\mathcal C=\{F\}\). Then there are exactly two outsiders
in each side column.

If F has actual y-comparisons with all three members of the left
column's chain \(\mathcal L\cup\{M_1\}\), those four squares
form an actual y-four-chain. At least one of its endpoints belongs to
the left column, where \(|x|\ge29/60\), contradicting (5).
Thus either F has an exceptional pair with one left outsider, or F is
actually x-separated from a left outsider. The corresponding assertion
holds on the right. F cannot be x-separated from \(M_1\) or \(M_2\),
as observed above.

If F is not exceptional, it is therefore x-separated from one outsider
on each side, giving an actual x-three-chain disjoint from the main
four-chain. The sharp terminal applies.

In any remaining one-central instance, F is exceptional with an outsider
on one side. Reflect x if needed and rename this pair \(A\in\mathcal L\),
\(B=F\). B must have an actual x-separation from a right outsider C,
so \(B<_xC\). By (7),

\[
 x_B<\frac{13}{12}-h_B-h_C\le\frac1{12}.
\]

The fat pair gap gives

\[
 x_A\le x_B-g_A-g_B
 <\frac1{12}-\frac1{\sqrt2}<-\frac{31}{60}. \tag{9}
\]

In particular A cannot lie to the right of \(M_0\) in actual x-order:
that comparison would require
\(x_A>x_{M_0}+h_0+h_A>h_A-61/60\ge-31/60\).
Nor can A lie to its left, since that would extend the main chain to
length five. Therefore A overlaps \(M_0\) horizontally, and

\[
 |y_A|\ge h_A+\frac38\ge\frac78. \tag{10}
\]

The left actual y-three-chain consists of A, the other left outsider U,
and \(M_1\). A cannot occupy its middle position: a middle member
of any actual three-chain has y-center in \((-31/60,31/60)\), whereas
(10) puts it outside this interval. Thus A is one of the two ends.
Since B overlaps A vertically but is y-separated from U and \(M_1\),
B lies on the same side of both those squares as A. Up to reflecting y,
the remaining one-central case has the concrete arrangement

\[
 \{U,M_1\}\text{ form an actual y-two-chain below both }A,B,
 \qquad A<B<_xC,
\]

with \(x_A<-31/60\), \(|y_A|\ge h_A+3/8\), and
\(x_B<1/12\). The actual four-chain and the other right outsider
remain present. The two cap theorems below exclude this final exceptional
end-block case.

## 7. Closing the exceptional one-central end block

Retain the notation at the end of Section 6, and reflect y so that A,B
are both above the other two members of the left actual y-three-chain.
The side-square edge theorem in Section 6 of
`BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md` says that every contained
square with \(|x|\ge29/60\) has top edge \(y+h>-5/6\).
Apply this to the bottom member S of the left chain. The two actual
gaps from S through its middle member T to A, or to B, give

\[
 y_A-h_A\ge y_S+h_S+2h_T>\frac16,
 \qquad
 y_B-h_B>\frac16. \tag{11}
\]

By (9), A horizontally overlaps \(M_0\). Since A is the upper endpoint
of an actual three-chain, \(y_A>h_A-1/60\ge29/60\); thus the
ordinary A--\(M_0\) pair must be separated with A above \(M_0\).
The endpoint budget gives

\[
 y_A-h_A\ge y_{M_0}+h_{M_0}\ge\frac38. \tag{12}
\]

We can choose the right separator C in Section 6 to be the **top member
of the actual right y-three-chain**, and it is then above \(M_3\).
Here are the complete comparisons. Since B is the upper endpoint of an
actual three-chain, \(y_B>h_B-1/60\). B is actually y-comparable with
\(M_2\). If \(M_2\) were above B, it would have
\(y_{M_2}>h_{M_2}+59/60\ge89/60\), contradicting
\(|x_{M_2}|>29/60\) and \(|c_{M_2}|<91/60\), because
\(29^2+89^2>91^2\). Hence \(M_2<_yB\).

If \(M_2\) were the top member of its side three-chain, B would extend
that whole chain to an actual y-four-chain with a forbidden side endpoint.
Thus its top member C is an outsider. The comparison \(B<_yC\) would
give \(y_C>h_C+59/60\ge89/60\), again violating the side-center
bound. The comparison \(C<_yB\) would extend the whole right chain to
an actual y-four-chain with a forbidden side endpoint. Therefore B,C
must actually x-separate, and their column positions give \(B<_xC\).

Since \(x_B>-29/60\),

\[
 x_C\ge x_B+h_B+h_C>\frac{31}{60}.
\]

Together with \(x_C<13/12\) and (2), this makes C horizontally
overlap \(M_3\). Its being the upper endpoint of its side three-chain
gives \(y_C>h_C-1/60\ge29/60\). Hence the ordinary pair is separated
with C above \(M_3\).

### The two possible physical separator signs

The separating-axis theorem supplies a signed unit normal n for the
physical A,B pair such that

\[
 n\cdot(c_B-c_A)\ge H_A(n)+H_B(n)\ge1.
\]

Its x-component is positive. Indeed, by (11), both squares have bottom
edge above \(1/8\), while both top edges are at most \(r=\sqrt Q\).
Thus

\[
 |y_B-y_A|\le r-h_A-h_B-\frac18
 \le r-\frac98<1.
\]

Since \(x_B>x_A\), a normal with nonpositive x-component could not
have the displayed separation projection at least one. A horizontal
normal would make A,B actually x-separated, contrary to the genuine
exception. Thus exactly one of the following two cases holds.

- If n points right/down, (11) supplies the floor for the complete
  theorem in `DOWNWARD_THREE_SQUARE_CAP_HAND_PROOF.md`.
- If n points right/up, (12) supplies the guarded lower edge for the
  complete theorem in `UPWARD_THREE_SQUARE_CAP_ORIENTATION_PROOF.md`.

Both theorems give the same strict transfer cap, with
\(a=46,b=27/2,T=211/4\):

\[
 a(-x_{M_0}-h_{M_0})+b(1-x_B-h_B)<T. \tag{13}
\]

The reflected physical matched cap for \(M_3,C\) gives

\[
 a(x_{M_3}-h_{M_3})+b(x_C-h_C)\le T.
\]

But their sum is at least

\[
 a(x_{M_3}-x_{M_0}-h_{M_0}-h_{M_3})
 +b(1+x_C-x_B-h_B-h_C)
 \ge2a+b=2T,
\]

by the actual four-chain and \(B<_xC\). This contradicts (13).
The exceptional one-central end block is therefore impossible even in
the closed Q-disk.

## 8. Pattern II closure and its scope

The side capacities give at least one central outsider. Section 7 closes
the exceptional one-central case; the ordinary one-central case already
provides an actual disjoint three-chain. The complementary note
`BROAD_NINE_SQUARE_GEOMETRIC_CONTINUATION.md` treats the other counts:
four or five central outsiders are impossible; every three-central case
provides an actual three-chain; and the two-central cases either provide
an actual four-plus-three terminal or route to the same strict transfer
cap with an explicitly proved floor.

Consequently, under the hypotheses of Section 1, the containing disk
has \(q\ge Q\). This closes Pattern II of
`ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md`: an actual horizontal
four-chain disjoint from the exceptional pair, in a fat direction of
that pair, cannot participate in a subcritical nine-square packing.

This is a full nine-square capacity theorem for the stated family.
It does not replace the physical hypotheses by seven- or eight-square
surrogates. It does not by itself close the other weak-four-chain
Pattern I, nor the unrestricted global caller. No new unrestricted
equality classification or canonical root count is asserted here.
