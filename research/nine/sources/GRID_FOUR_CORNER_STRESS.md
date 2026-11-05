# n=9: the four-corner grid stress theorem

**Status: proved geometric hand theorem; independent square rotations allowed.**
This is a *second* structural terminal inequality, complementary to
[FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md). It excludes a four-corner
"3×3-grid skeleton" at the conjectural n=9 squared radius
\(q_*=1105/256\), without assumptions on the other five squares.
It is **not** a proof that arbitrary nine-square packings have
such a skeleton.

## 1. Precise hypothesis

Fix any orthonormal coordinate frame \(e,f\), and let the centers of
four independently oriented unit squares be
\[
 c_{TL}=(x_{TL},y_{TL}),\quad
 c_{TR}=(x_{TR},y_{TR}),\quad
 c_{BL}=(x_{BL},y_{BL}),\quad
 c_{BR}=(x_{BR},y_{BR}).
\]
The halfwidth of square \(S\) along either coordinate axis is
\[
 h_S=\tfrac12\bigl(|\cos\theta_S|+|\sin\theta_S|\bigr)
 \ge\tfrac12.
\]
No two angles are assumed equal. Write
\(H_S(P)=(|P\cdot u_S|+|P\cdot v_S|)/2\) for the
(square) support function about its center.

Suppose the four corner squares have the following **outer spans**:
\[
\begin{aligned}
 x_{TR}-x_{TL}&\ge1+h_{TR}+h_{TL}, &(X_T)\\
 x_{BR}-x_{BL}&\ge1+h_{BR}+h_{BL}, &(X_B)\\
 y_{TL}-y_{BL}&\ge1+h_{TL}+h_{BL}, &(Y_L)\\
 y_{TR}-y_{BR}&\ge1+h_{TR}+h_{BR}. &(Y_R)
\end{aligned}\tag{1}
\]

Each span contains a *one-unit reserve* in addition to the two
corner halfwidths. For a conventional 3×3 arrangement, the four
other edge squares can certify the four reserves by consecutive
projection separations. But for the theorem we do **not** assume
the existence, placement, orientation or feasibility of any
intervening square: inequalities (1) are its entire hypothesis.

## 2. The exact square-orientation penalty

**Lemma 2.1.** Let \(h_S\) be the coordinate halfwidth of a freely
rotated unit square and let \(P=(\pm A,\pm A)\), where \(A>0\).
Then
\[
                 2Ah_S+H_S(P)\ge2A. \tag{2}
\]
Equality holds if and only if the sides of the square are
parallel to the chosen coordinate frame (up to a right-angle turn).

*Proof.* Up to the square's quarter-turn symmetry put
\[
 a=\max(|\cos\theta|,|\sin\theta|),\qquad
 b=\min(|\cos\theta|,|\sin\theta|).
\]
Thus \(1\ge a\ge b\ge0\), \(a^2+b^2=1\), and
\(h_S=(a+b)/2\).
For **all four sign combinations** of \(P\),
\[
 H_S(P)=A\max(a,b)=Aa.
\]
Consequently
\[
 2Ah_S+H_S(P)=A(2a+b).
\]
Since \(1-a=b^2/(1+a)\),
\[
 2a+b-2
   =\frac{b(1+a-2b)}{1+a}\ge0.
\]
Indeed \(1+a-2b=(1-b)+(a-b)\ge0\).
If \(b>0\), then \(b<1\), hence the inequality
is strict. If \(b=0\), then \(a=1\) and it is an
equality. \(\square\)

This is an exact two-line algebraic factorization, with no
trigonometric approximations or angle subdivision.

## 3. Four-corner theorem

**Theorem 3.1 (sharp grid-skeleton stress).**
Suppose four independently oriented unit squares lie in
the same closed disk of squared radius \(q\), and their
centers/halfwidths satisfy all four spans (1).
Then
\[
                       \boxed{q\ge\frac92}. \tag{3}
\]
In particular, this pattern is **impossible** for
\(q\le q_*=1105/256\), since \(9/2>1105/256\).

*Proof.* Translate the disk center to the origin.
Set \(A=3/2\). Assign one test point to each square:
\[
\begin{aligned}
 P_{TL}&=(-A,A),&P_{TR}&=(A,A),\\
 P_{BL}&=(-A,-A),&P_{BR}&=(A,-A).
\end{aligned}
\]
All four have squared norm \(2A^2=9/2\).

For every square \(S\) inside the disk, maximizing
the linear functional \(P\cdot v\) over its vertices and
using the elementary identity
\[
 2P\cdot v
    =\|P\|^2+\|v\|^2-\|P-v\|^2
    \le\|P\|^2+q
\]
gives
\[
 P\cdot c_S+H_S(P)\le\tfrac12(q+\|P\|^2).
\]
Apply this to the four squares with their four assigned
test points, and add:
\[
 2q+9
 \ \ge\ \sum_{S} (P_S\cdot c_S+H_S(P_S)). \tag{4}
\]

The signed center-coordinate sum is exactly
\[
\begin{aligned}
 \sum_S P_S\cdot c_S
   =A[&(x_{TR}-x_{TL})+(x_{BR}-x_{BL})\\
      +&(y_{TL}-y_{BL})+(y_{TR}-y_{BR})].
\end{aligned}
\]
By (1), the bracket is at least \(4+2\sum_S h_S\).
Hence (4), together with Lemma 2.1, gives
\[
\begin{aligned}
 2q+9
 &\ge4A+\sum_S\bigl(2Ah_S+H_S(P_S)\bigr)\\
 &\ge4A+4(2A)=12A=18.
\end{aligned}
\]
Therefore \(2q\ge9\), proving (3). \(\square\)

**Corollary 3.2 (equality rigidity).** If (1) holds
and \(q=9/2\), then all four square orientations
are aligned with the chosen axes, every inequality
in (1) is an equality, and their centers are
\[
 TL=(-1,1),\quad TR=(1,1),\quad
 BL=(-1,-1),\quad BR=(1,-1).
 \tag{5}
\]
In particular all four extreme outer corners
are exactly the test points \((\pm3/2,\pm3/2)\).

*Proof.* Equality in the sum of four nonnegative
slacks forces equality in Lemma 2.1 at every
square, and in the four tangent inequalities.
Each supporting vertex must then coincide with
its test point \(P_S\), since equality in the
Euclidean tangent identity requires \(v=P_S\).
With axis alignment, the corresponding centers
are exactly (5). The four spans are consequently
saturated. \(\square\)

## 4. How to use this in the unrestricted G2 classification

There are now **two** mathematically different
four-square terminal inequalities:

- **Long/short pair pattern,**
  [FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md):
  long horizontal span, short horizontal span,
  and complete vertical separation of the pairs
  force \(q\ge1105/256\).
- **Four-corner grid pattern,** Theorem 3.1:
  two large horizontal spans (top/bottom) and
  two large vertical spans (left/right), each
  with a one-square reserve, force
  \(q\ge9/2>1105/256\).

The second pattern is **not** a small optimization
of the first: it has a different dual/stress graph
and excludes the competing three-by-three
arrangement in an angle-uniform way.

**Still OPEN:** derive, from unrestricted
\(\mathrm{Packing}_9\) with \(q\le q_*\),
a genuinely exhaustive geometric disjunction
of one of these two patterns (or a short list of
further named, proved terminal alternatives).
Theorem 3.1 itself does not force grid spans:
five intervening squares have to certify them
by correct **actual** separating axes, not
by assuming row/column membership.

## 5. Verification boundary

Every step is a support-function identity,
four elementary center-span inequalities, or
an exact unit-circle factorization. No numerical
optimizer, state-grid table, Lean source or
kernel/CI verification is used in this proof.
Independent global G2 coverage and the
unrestricted n=9 theorem remain open.
