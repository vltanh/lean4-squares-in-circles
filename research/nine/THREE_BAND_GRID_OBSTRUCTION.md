# n=9: complete three-by-three center-band obstruction (independent rotations)

**Status (2026-10-22): exact hand theorem, conditional only on an explicit
three-band projection structure.** This closes the 3+3+3 center-band
terminal branch of G2.C4.3. The proof does **not** assume equal
orientations or equal heights within a band, nor does it enumerate
position or angle subintervals. It does **not** prove that every
nine-square packing admits this band decomposition.

## 1. Statement

Let nine independently oriented unit squares fit in a disk of squared
radius \(q\le q_*:=1105/256\). Fix an orthonormal coordinate frame in
which **every pair** of squares is separated along at least one of the
two coordinate projections. Suppose the nine squares partition into
three groups of three, each with pairwise disjoint open horizontal
projections, and the center heights satisfy

\[
 y_T\ge\tfrac12 \quad (T\text{ in top group}),\qquad
 -\tfrac12<y_C<\tfrac12 \quad (C\text{ in middle group}),\qquad
 y_B\le-\tfrac12 \quad (B\text{ in bottom group}).\tag{1}
\]

**Theorem:** Under these hypotheses \(q\ge9/2\), hence no such packing
can have \(q\le1105/256<9/2\).

This is sharper than the conjectural n=9 obstruction because the
three-row grid is geometrically inefficient.

## 2. Coarse center and extreme-rank bounds

As established in FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md, every center obeys
\[
                 |c|<\rho:=61/40.\tag{2}
\]
A center in either outer group satisfies \(|y|\ge1/2\), so
\[
 |x|<\alpha:=29/20,\tag{3}
\]
because \(\alpha^2+1/4=941/400>3721/1600=\rho^2\).

If three square projections in one horizontal group are disjoint,
the left-to-right center gaps are at least one. Therefore, their
leftmost and rightmost center coordinates lie in

\[
\begin{array}{c|cc}
 &x_L &x_R\\
\text{top or bottom}&(-\alpha,\alpha-2)&(2-\alpha,\alpha)\\
\text{middle}&(-\rho,\rho-2)&(2-\rho,\rho).
\end{array}\tag{4}
\]
These ranges follow from the center bounds and two consecutive
horizontal gaps of at least one.

The key exact inequality is
\[
                \rho+\alpha-2
                    =61/40+58/40-80/40=39/40<1.
\tag{5}
\]
It implies that the x center coordinates of **any two leftmost
squares** from different bands differ by less than one, and the
same holds for **any two rightmost squares**.

## 3. Forced vertical endpoint chains

Let \(T_L,C_L,B_L\) denote the three leftmost squares of their
respective bands; similarly \(T_R,C_R,B_R\) for the rightmost.

By (4)--(5), the open horizontal projections of each corresponding
pair \(T_L,C_L\), \(C_L,B_L\) overlap, since each square's horizontal
halfwidth is at least \(1/2\). The same is true of the rightmost
pairs.

The common-frame coordinate-separability hypothesis therefore
forces **vertical projection separation** for each such pair.
Their height order is dictated by (1). Consequently,
\[
 \begin{aligned}
 y_{T_L}-y_{C_L}&\ge h_{T_L}+h_{C_L},\\
 y_{C_L}-y_{B_L}&\ge h_{C_L}+h_{B_L},
 \end{aligned}
\]
and hence
\[
          y_{T_L}-y_{B_L}
             \ge h_{T_L}+h_{B_L}+2h_{C_L}
             \ge h_{T_L}+h_{B_L}+1.
\tag{6}
\]
The same holds with L replaced by R.

Moreover, the three horizontally separated squares in the top
group give
\[
           x_{T_R}-x_{T_L}
                  \ge1+h_{T_L}+h_{T_R},
\tag{7}
\]
and the bottom group gives
\[
           x_{B_R}-x_{B_L}
                  \ge1+h_{B_L}+h_{B_R}.
\tag{8}
\]

Thus the four outer squares \(T_L,T_R,B_L,B_R\) meet all four
span hypotheses of GRID_FOUR_CORNER_STRESS.md, including the
one-square reserves in the vertical spans furnished by (6).

## 4. Conclusion

The arbitrary-rotation four-corner grid stress theorem gives
\[
                         q\ge9/2>1105/256,
\]
contradicting \(q\le q_*\). This finishes the proof. \(\square\)

**What is and is not closed:** A full 3+3+3 band geometry, even with
staggered heights and independent orientations, is now excluded by
a universal four-corner certificate. This does not establish that
an arbitrary nine-square packing can be split into the three
horizontal-projection chains in (1). In particular, centers in a
band of vertical extent greater than one need not be mutually
horizontally projection-separated, even if the physical squares
do not overlap.

The remaining coherent-side task is the **structural existence**
of an appropriate 4+3 paired certificate, a 3+3+3 band grid,
or an independently proved obstruction for the configurations
that evade both templates. Avoid using this conditional theorem
as an unstated normalization.
