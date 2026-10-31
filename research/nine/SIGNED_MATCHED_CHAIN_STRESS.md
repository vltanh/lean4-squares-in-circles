# n=9: exact two-chain terminal with mixed vertical signs

**Status (2026-10-22): complete table-free hand proof of a new
whole-branch terminal theorem for common-coordinate-separable packings.**
It covers **all** vertical ordering patterns (same or opposite signs) of
the corresponding endpoints of two disjoint horizontal projection
chains, one of length four and one of length three. All seven squares
may rotate independently. It replaces the stronger same-sign/outer-band
hypotheses of PAIRED_FOUR_ANCHOR_STRESS.md.

**Scope:** a fixed orthogonal frame must separate every pair along
one of its two coordinate projections. That premise is false for
arbitrary packings (NO_GLOBAL_ORTHOGONAL_FRAME.md). The remaining
G2.C4.3 task is to extract a three-chain from the five squares outside
a given four-chain or exclude the entire residual class. This theorem
does **not** yet solve that extraction.

## 1. Sign-flexible four-anchor stress

Write \(Q=1105/256\). Suppose four independently oriented unit
squares \(M_L,M_R,B_L,B_R\) fit a disk of squared radius q.
Let h_i be their equal coordinate projection halfwidths
(relative to some fixed perpendicular frame). Assume

\[
 \begin{aligned}
 x_{M_R}-x_{M_L}&\ge2+h_{M_L}+h_{M_R},\\
 x_{B_R}-x_{B_L}&\ge1+h_{B_L}+h_{B_R}.
 \end{aligned}\tag{1}
\]

Suppose that for **each** \(k=L,R\) there is a sign
\(\sigma_k\in\{-1,1\}\) such that
\[
       \sigma_k(y_{M_k}-y_{B_k})
              \ge h_{M_k}+h_{B_k}. \tag{2}
\]

No relation is required between \(\sigma_L\) and \(\sigma_R\).
They may be the same (both M endpoints above or below B)
or opposite (a crossed arrangement).

**Theorem 1.1 (signed matched-anchor stress).** Under (1)--(2),
\[
                               \boxed{q\ge Q}. \tag{3}
\]

*Proof.* For each k use the tangent test vectors
\[
\begin{array}{c|c}
 M_L&(-2,\ \sigma_L\,9/16)\\
 M_R&( 2,\ \sigma_R\,9/16)\\
 B_L&(-3/2,\ -\sigma_L\,23/16)\\
 B_R&( 3/2,\ -\sigma_R\,23/16).
\end{array}\tag{4}
\]
Each vector has squared norm Q. The Euclidean tangent identity
for every square inside the disk gives
\[
      P_i\cdot c_i+H_i(P_i)\le(q+Q)/2,
      \quad H_i(P)=\tfrac12(|P\cdot u_i|+|P\cdot v_i|).
      \tag{5}
\]

Multiply the two M inequalities by 23 each and the two B
inequalities by 9 each. Their total right-hand side
is \(32(q+Q)\). The signed center terms on the left combine into
\[
 46(x_{M_R}-x_{M_L})
 +\frac{27}{2}(x_{B_R}-x_{B_L})
 +\frac{207}{16}
 \sum_{k=L,R}\sigma_k(y_{M_k}-y_{B_k}).
\tag{6}
\]
The vertical terms have the desired same coefficient because
\(23\cdot9/16=9\cdot23/16=207/16\).

Use (1)--(2). The weighted sum is at least
\[
 92+\frac{27}{2}
 +\sum_{k=L,R}
  \left[
   \frac{943}{16}h_{M_k}+23H_{M_k}(P_{M_k})
   +\frac{423}{16}h_{B_k}+9H_{B_k}(P_{B_k})
  \right].
\tag{7}
\]

For any freely rotated unit square, any choices of signs,
and \(0\le p\le A\), the exact orientation penalty
in ORIENTATION_STABLE_SEVEN_ANCHOR.md says
\[
          (A+p)h_i+H_i((\pm A,\pm p))\ge A+p.
          \tag{8}
\]
Apply it with \((A,p)=(2,9/16)\) and
\((A,p)=(3/2,23/16)\) to each M and B respectively.
The expression (7) is at least
\[
 92+\frac{27}{2}
  +2\frac{943}{16}+2\frac{423}{16}
 =\frac{1105}{4}=64Q.
\]
Thus \(32(q+Q)\ge64Q\), proving (3).
The signs play no role in the final arithmetic. \(\square\)

**Equality:** Every penalty and tangent inequality must be sharp.
Thus all four squares are axis aligned and, writing the chosen signs,
\[
\begin{aligned}
 M_L&=(-3/2,\ \sigma_L/16),&
 M_R&=(3/2,\ \sigma_R/16),\\
 B_L&=(-1,\ -15\sigma_L/16),&
 B_R&=(1,\ -15\sigma_R/16).
\end{aligned}\tag{9}
\]
This is an implication for these four anchors, **not** a
claim that all sign patterns extend to full equality packings.

## 2. Universal interlocking of two horizontal projection chains

**Lemma 2.1 (endpoint projection interlocking).**
Suppose seven of nine freely oriented unit squares lie in the
disk \(q\le Q\), with disjoint interiors, and form two
disjoint horizontal projection-separated chains
\[
             M_L,M_2,M_3,M_R,\qquad
             B_L,B_2,B_R
\]
in left-to-right order. Then the horizontal **open**
projections of \(M_L\) and \(B_L\) overlap.
Likewise the horizontal open projections of
\(M_R\) and \(B_R\) overlap.

*Proof.* Every square center has Euclidean norm
\[
                    |c|<\rho:=61/40.
\tag{10}
\]
This follows from the exact disk-corner formula
\(q\ge |c|^2+1/2+|c|\), evaluated at \(\rho\).

For the four-square chain, successive horizontal
center gaps are at least one, so
\[
 -\rho<x_{M_L}<-59/40,\qquad
 59/40<x_{M_R}<\rho.
\tag{11}
\]
The corresponding outer center heights obey
\[
                  |y_{M_L}|,|y_{M_R}|<2/5.
\tag{12}
\]
Indeed \((59/40)^2+(2/5)^2>\rho^2\).

Suppose the open horizontal projections of M_L,B_L
do not overlap. B_L cannot lie entirely to the left:
that would force
\[
  x_{B_L}\le x_{M_L}-h_{B_L}-h_{M_L}
          \le x_{M_L}-1<-99/40<-\rho.
\]
So B_L lies to the **right**, with
\[
              x_{B_L}\ge x_{M_L}+1>-21/40.
\tag{13}
\]
The chain B has two consecutive center gaps
each at least one, hence
\[
              x_{B_R}\ge x_{B_L}+2>59/40.
\]
Since also \(x_{B_R}<\rho\), both B_R and M_R
have x-coordinates in \((59/40,61/40)\).
By the same center-radius argument as (12),
both have \(|y|<2/5\). Their squared center
distance is strictly less than
\[
                 (1/20)^2+(4/5)^2=257/400<1.
\tag{14}
\]
But any two distinct disjoint-interior unit squares
contain open inscribed disks of radius 1/2, so
their centers must have distance at least one.
This contradicts (14). Thus the leftmost
endpoint projections overlap.

Reflect x and interchange left/right to get
the rightmost case. \(\square\)

This lemma uses **actual physical nonoverlap** to
derive a pairwise center-distance contradiction.
It does not assume the other five square orientations
or contact patterns are aligned.

## 3. A terminal theorem for any 4+3 pair of chains

**Theorem 3.1 (common-coordinate-separable 4+3 chains).**
Suppose nine independently oriented unit squares
fit in a circle of squared radius \(q\le Q\), and
a single perpendicular coordinate frame separates
each pair along at least one of its two coordinate
projections.

If seven of the squares can be partitioned into
two disjoint horizontally projection-separated
chains of sizes four and three, then
\[
                        q=Q.
\tag{15}
\]
At equality, the four outer anchors belong to
one of the signed configurations (9).

*Proof.* The two chains give the horizontal
span inequalities (1), since the intermediate
square projection widths are at least one.
Lemma 2.1 forces the horizontal projections
of corresponding left and right endpoints
to overlap. The coordinate-separability
assumption then forces their **vertical**
projections to be disjoint, in *some* order.
For each endpoint pair choose \(\sigma_k\)
recording which square is above the other.
This is exactly (2). Theorem 1.1 gives
\(q\ge Q\), hence equality under \(q\le Q\).
The equality anchors follow from (9).
\(\square\)

This theorem makes **no assumption** that
the two chains have equal heights, form globally
ordered horizontal layers, or have same-sign
vertical endpoints. The vertical signs are
handled by the stress automatically.

## 4. Precise remaining C4.3 question

Given a common-coordinate-separable nine-square
packing at \(q\le Q\), the rank-grid theorem
first supplies a horizontal (or reflected vertical)
projection-disjoint chain of four squares.
The large-zigzag branch has already been
excluded by ZIGZAG_BRANCH_CLOSED.md.

**The exact remaining combinatorial branch is:**
can the five squares outside this four-chain
lack a horizontally projection-disjoint triple?
If not, Theorem 3.1 closes the entire
coordinate-separable case at once. If yes,
derive a different sharp stress or prove this
entire 5-square complement class impossible
at \(q\le Q\).

This is **not** a proof that the triple must
exist. In particular, finite poset ranks
alone allow five squares whose longest x-chain
has size two and y-chain has size three.

For arbitrary oblique separators, the endpoint
interlocking lemma (2.1) still holds, and the
signed stress (1.1) still holds, but the step
from **overlapping horizontal projections**
to **vertically separated square projections**
is unavailable without the common-coordinate
separability premise. This is the separate
G2.O2/O3 obstacle.

## 5. Verification boundary

Every argument is a two-sign orientation penalty,
four exact rational tangent vectors, the disk
center-radius bound, a four-versus-three endpoint
order, and the inscribed disk distance lemma.
There is no large positional or angle table.
No n=9 Lean compilation, kernel audit, or
global optimality claim is made.
