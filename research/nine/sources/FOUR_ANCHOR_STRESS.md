# n=9: four-anchor stress theorem (independent orientations)

**Status: complete exact hand proof.**
This is a stronger terminal theorem than the seven-anchor
result [ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md).
The sharp disk bound can be certified using **only four
designated squares**, two long-span anchors and two short-span
anchors, provided their projection spans satisfy two exact
inequalities and the two anchor pairs are vertically ordered.
The other five squares need not be horizontally or vertically
layered for this certificate to apply.

## 1. Extremal-pair cap lemma

Fix an orthonormal coordinate frame \((e,f)\) and write
\(c_S=(x_S,y_S)\). Every unit square has equal coordinate
projection halfwidth
\[
 h_S=\tfrac12(|e\cdot u_S|+|e\cdot v_S|)
     =\tfrac12(|f\cdot u_S|+|f\cdot v_S|)\ge\tfrac12.
\]
For a vector z let
\(H_S(z)=(|z\cdot u_S|+|z\cdot v_S|)/2\).

**Lemma 1.1 (two-anchor cap stress).**
Let \(A>0\), \(0\le p=s+1\le A\), and let
two independently rotated squares \(S_L,S_R\) fit
inside a disk centered at zero with squared radius \(q\).
Assume
\[
\begin{aligned}
 x_R-x_L&\ge (2A-2)+h_L+h_R,\\
 y_L-h_L&\ge s,\qquad y_R-h_R\ge s.
\end{aligned}\tag{1}
\]
Then
\[
                         q\ge A^2+p^2. \tag{2}
\]
If \(p>0\) and equality holds, both squares are aligned
with the coordinate frame and their outermost upper
corners are exactly \((-A,p),(A,p)\), respectively.

*Proof.* The one-square orientation-penalty lemma
[ORIENTATION_STABLE_SEVEN_ANCHOR.md](ORIENTATION_STABLE_SEVEN_ANCHOR.md),
Lemma 2.1, states
\[
 (A+p)h_i+H_i((\pm A,p))\ge A+p. \tag{3}
\]
The tangent identity
\[
 2P\cdot v=\|P\|^2+\|v\|^2-\|P-v\|^2
\]
for a square vertex \(v\) in the disk gives
\[
 P\cdot c_i+H_i(P)\le
              \tfrac12(q+\|P\|^2)
\]
for either \(P=(\pm A,p)\). Apply it to
\((S_L,P_-)\) and \((S_R,P_+)\) and add.
The resulting lower bound is
\[
\begin{aligned}
 q+A^2+p^2
 &\ge A(x_R-x_L)+p(y_R+y_L)
      +H_R(P_+)+H_L(P_-)\\
 &\ge A(2A-2)+2ps
      +\sum_{i=L,R}[(A+p)h_i+H_i(P_i)]\\
 &\ge A(2A-2)+2ps+2(A+p)\\
 &=2A^2+2p^2.
\end{aligned}
\]
Cancel \(A^2+p^2\) to obtain (2).
When equality holds, (3) is sharp, so
both orientations are axis aligned.
Equality in the tangent identity forces the
supporting vertex of each square to equal
the respective tangent point \((\pm A,p)\).
\(\square\)

**Lemma 1.2 (reflected cap).** If the two
squares in (1) instead lie below ceiling \(y=s\),
and \(0\le1-s\le A\), then
\[
 q\ge A^2+(1-s)^2. \tag{4}
\]
Equality forces the corresponding two
lower extreme corners to be
\((-A,s-1)\) and \((A,s-1)\).

*Proof.* Reflect y and apply Lemma 1.1. \(\square\)

**Important:** Neither lemma refers to any intermediate
square between the two endpoint anchors. For a horizontally
projection-disjoint row of m squares, its two extreme
squares satisfy (1) with \(A=m/2\), but the lemma's
hypotheses are strictly weaker.

## 2. The sharp four-anchor certificate

**Theorem 2.1 (sharp four-square long/short stress).**
Suppose four independently oriented unit squares
\(M_L,M_R,B_L,B_R\) fit in a disk of squared
radius \(q\). In some common orthonormal frame
write \(h_{M_L},h_{M_R},h_{B_L},h_{B_R}\)
for their coordinate projection halfwidths.
Assume exactly these three geometric conditions:

1. **Long horizontal span:**
   \[
     x_{M_R}-x_{M_L}\ge
               2+h_{M_L}+h_{M_R}. \tag{5}
   \]
2. **Short horizontal span:**
   \[
     x_{B_R}-x_{B_L}\ge
               1+h_{B_L}+h_{B_R}. \tag{6}
   \]
3. **Complete vertical anchor separation:**
   \[
     \min_{m=M_L,M_R}(y_m-h_m)\ge
     \max_{b=B_L,B_R}(y_b+h_b). \tag{7}
   \]

Then
\[
                  \boxed{q\ge1105/256.} \tag{8}
\]

No assumption is made about any other squares, their
positions, frames, or whether their projections overlap
the four anchors.

*Proof.* Choose \(s\) equal to the right side
of (7). Then the M-anchors are above floor s and
the B-anchors are below ceiling s.

If \(s\le-1/2\), use Lemma 1.2 with
\(A=3/2\), applied to the B pair with
the weaker ceiling \(-1/2\):
\[
 q\ge9/4+(3/2)^2=9/2>1105/256.
\]
If \(s\ge1/2\), use Lemma 1.1 with
\(A=2\), applied to the M pair with
the weaker floor \(1/2\):
\[
 q\ge4+(3/2)^2=25/4>1105/256.
\]
For \(-1/2<s<1/2\), the parameters
\(p_M=s+1\in(1/2,3/2)\le2\) and
\(p_B=1-s\in(1/2,3/2)\le3/2\) are
in the valid ranges. Therefore
\[
 q\ge4+(s+1)^2,\qquad
 q\ge9/4+(1-s)^2.
\]
The first bound increases and the second
decreases with s in this interval. Their
intersection occurs at \(s=-7/16\)
and both equal \(1105/256\).
Thus (8) holds. \(\square\)

**Corollary 2.2 (four pinned equality anchors).**
If the three hypotheses (5)--(7) hold and
\(q=1105/256\), then \(s=-7/16\)
and all four squares are axis aligned in
the chosen frame, with centers
\[
\begin{aligned}
 M_L&=(-3/2,\ 1/16),&
 M_R&=( 3/2,\ 1/16),\\
 B_L&=(-1,\ -15/16),&
 B_R&=( 1,\ -15/16).
\end{aligned} \tag{9}
\]

*Proof.* At the only possible equality seam,
both cap-pair bounds are equalities. Lemmas 1.1
and 1.2 identify both extreme supporting corners,
and equality in the one-square orientation penalty
forces their axes to be aligned. Their centers are
obtained by shifting the corners inward by
\((1/2,1/2)\) in the appropriate signs. \(\square\)

## 3. Why this is a materially better G2 target

The original G1 proof assumed *seven*
independently oriented squares could be partitioned
into projection-disjoint rows of four and three,
with complete separation between entire rows.
That hypothesis implies (5)--(7), but the
converse need not hold.

Here **only four** boundary squares are involved:
we seek one horizontally widely separated pair,
a second pair with a smaller but still definite
horizontal span, and their mutual vertical
support ordering.

In an actual 4+3 layered arrangement,
the remaining three squares between the anchors
certify (5)--(6) by adding their horizontal
projection widths, each at least 1.
However these intervening squares need not
be identified or aligned to apply Theorem 2.1
once the two spans are established by *any*
sound geometric argument.

This opens a more focused global-extraction goal:

> **G2-four-anchor target (OPEN):** Prove that every
> nine-square packing with \(q\le q_*\) admits a
> frame and four anchors satisfying (5)--(7),
> or falls into an explicit finite collection of
> nonstratified exceptions with separately proved
> sharp lower bounds.

No universal extraction of the four anchors
is asserted here. The four-anchor theorem
is a terminal analytic implication, not yet
an unrestricted nine-square theorem.

## 4. Verification boundary

The entire proof is the elementary one-square
penalty, two Euclidean tangent identities,
and two intersecting quadratic bounds in s.
No numerical search or certificate is part of
the proof. No Lean compilation, kernel audit,
or equality-family completion is claimed.
