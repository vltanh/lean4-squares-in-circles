# n=9: sharp paired four-anchor dual stress, without a common separating seam

**Status (2026-10-22): complete elementary hand proof.** This improves
[FOUR_ANCHOR_STRESS.md](FOUR_ANCHOR_STRESS.md) by removing its assumption
that *both* upper endpoints lie above *both* lower endpoints. Instead it
requires only one **sum of vertical-center gaps**; matching left/right
vertical separations are sufficient. All four squares may rotate
independently. No numerical optimization, angle subdivision or generated
table enters the proof.

The result does **not** imply that every arbitrary nine-square packing
contains the required anchors. Its role is a stronger terminal certificate
for G2.C4.3 and G2.O2.

## 1. Definitions

Fix a perpendicular coordinate frame and disk center 0. For a unit
square S with center c=(x,y), orthonormal side axes u,v, write

\[
 h_S=\frac{|u_x|+|v_x|}{2}
     =\frac{|u_y|+|v_y|}{2}\ge\frac12,\qquad
 H_S(P)=\frac{|P\cdot u|+|P\cdot v|}{2}.
\]

For any containing disk of squared radius q and any P,
\[
             P\cdot c+H_S(P)\le\frac{q+|P|^2}{2}.
             \tag{1}
\]
Indeed, maximize \(P\cdot z\) over the square's vertices and use
\(2P\cdot z=|P|^2+|z|^2-|P-z|^2\).

We use the already hand-proved square orientation penalty
(ORIENTATION_STABLE_SEVEN_ANCHOR.md, Lemma 2.1): when \(A\ge p\ge0\),
\[
             (A+p)h_S+H_S((\pm A,\pm p))\ge A+p.
             \tag{2}
\]
The reflected sign cases are identical. For \(p>0\), equality forces
the square's sides to be parallel to the coordinate frame.

## 2. Sparse four-square stress with aggregate vertical order

**Theorem 2.1 (paired four-anchor stress).** Suppose four independently
oriented unit squares \(M_L,M_R,B_L,B_R\) fit inside a disk of squared
radius q. Denote their centers by \((x_i,y_i)\) and their common
horizontal/vertical coordinate halfwidths by \(h_i\). Assume:

\[
\begin{split}
 x_{M_R}-x_{M_L}&\ge2+h_{M_L}+h_{M_R},\\
 x_{B_R}-x_{B_L}&\ge1+h_{B_L}+h_{B_R},\\
 (y_{M_L}+y_{M_R})-(y_{B_L}+y_{B_R})
   &\ge h_{M_L}+h_{M_R}+h_{B_L}+h_{B_R}.
\end{split}\tag{3}
\]

Then
\[
                        \boxed{q\ge q_*=\frac{1105}{256}}.
                        \tag{4}
\]

The third hypothesis is **strictly weaker** than the old all-above-
all-below condition. In particular, it follows if the projections of
\(M_L,B_L\) are vertically separated in the given upper/lower order,
and likewise for \(M_R,B_R\), without requiring vertical separation
of the cross pairs.

*Proof.* Set the four exact boundary tangent points
\[
\begin{array}{c|c}
M_L&(-2,9/16)\\
M_R&(2,9/16)\\
B_L&(-3/2,-23/16)\\
B_R&(3/2,-23/16).
\end{array}
\tag{5}
\]
Each has squared norm \(q_* =1105/256\).

Apply (1) to the four squares and their respective points, with
positive weights 23 on each M-square and 9 on each B-square. The
sum of all four right-hand sides is
\[
   \frac{2(23)+2(9)}2(q+q_*)=32(q+q_*).
\tag{6}
\]
Their weighted center contributions are
\[
 46(x_{M_R}-x_{M_L})
 +\frac{27}{2}(x_{B_R}-x_{B_L})
 +\frac{207}{16}
      (y_{M_L}+y_{M_R}-y_{B_L}-y_{B_R}),
\tag{7}
\]
since \(23(9/16)=9(23/16)=207/16\).

Substitute all three hypotheses (3). The sum (7) is at least
\[
       46\cdot2+\frac{27}{2}
       +\frac{943}{16}(h_{M_L}+h_{M_R})
       +\frac{423}{16}(h_{B_L}+h_{B_R}).
\tag{8}
\]
The weighted square support terms can be combined with the h terms,
since
\[
 \frac{943}{16}=23(2+9/16),\qquad
 \frac{423}{16}=9(3/2+23/16).
\]
Applying the orientation penalty (2) to each of the four squares,
the entire weighted tangent sum is at least
\[
 92+\frac{27}{2}
  +2\frac{943}{16}+2\frac{423}{16}
 =\frac{1105}{4}=64q_*.
 \tag{9}
\]
Together (6) and (9) give
\[
                32(q+q_*)\ge64q_*,
\]
hence \(q\ge q_*\). \(\square\)

**Corollary 2.2 (rigidity).** If q=q* in Theorem 2.1, then the
four anchor squares have axes parallel to the chosen frame, and
their centers are exactly
\[
 M_L=(-3/2,1/16),\quad M_R=(3/2,1/16),\quad
 B_L=(-1,-15/16),\quad B_R=(1,-15/16).
\tag{10}
\]

*Proof.* All weights are positive, so equality in the chain
(1)--(9) forces every individual tangent inequality and every
orientation penalty to be an equality. By (2) all four squares are
axis aligned. Equality in (1), which used
\(2P\cdot z=|P|^2+|z|^2-|P-z|^2\), forces their supporting vertices
to equal the four points (5). Moving half a side in both
coordinates gives (10). \(\square\)

Reflecting the vertical direction yields the corresponding theorem
with B above M.

## 3. A global-frame chain terminal with no layer assumption

**Lemma 3.1 (three endpoint squares in an outer center band).**
Let nine freely oriented unit squares lie in the disk \(q\le q_*\)
and be pairwise separated by horizontal or vertical projections
in one chosen frame. Suppose there are:

1. A horizontal projection-disjoint chain of four squares M.
2. A horizontal projection-disjoint chain of three **different**
   squares B, whose *leftmost and rightmost center heights* are
   both at most \(-1/2\).

Then \(q=q_*\) and the four end squares are pinned as in
Corollary 2.2.

*Proof.* Every square center c satisfies
\[
 |c|<\rho:=61/40
\]
by the exact far-corner containment bound
\(|c|^2+1/2+|c|\le q_*\). The outer center x-coordinates of a
four-square horizontal chain obey
\[
 -61/40<x_{M_L}<-59/40,\qquad
 59/40<x_{M_R}<61/40,
\tag{11}
\]
and their heights satisfy \(|y_{M_L}|,|y_{M_R}|<2/5\).
The chain itself supplies the first inequality in (3) by summing
its three consecutive projection gaps, since the two intervening
projection widths are each at least one.

For each extremal B-square, \(|y_B|\ge1/2\) gives
\[
 |x_B|<29/20;
\]
indeed \((29/20)^2+(1/2)^2>(61/40)^2\).
Ordering the three B-squares and using two horizontal center gaps
at least one gives
\[
 -29/20<x_{B_L}<-11/20,\qquad
 11/20<x_{B_R}<29/20.
\tag{12}
\]
The three-square chain supplies the second horizontal span
inequality in (3).

By (11)--(12), the x center differences in both corresponding
endpoint pairs satisfy
\[
 |x_{M_L}-x_{B_L}|<39/40<1,\qquad
 |x_{M_R}-x_{B_R}|<39/40<1.
\tag{13}
\]
Since all coordinate projection halfwidths are at least 1/2,
each corresponding pair has overlapping open horizontal
projections. Coordinate-separability then forces separation
of its vertical projection intervals. The M endpoints have
height greater than \(-2/5\), whereas the B endpoints have
height at most \(-1/2\), so the separation is in the order
M above B:
\[
 y_{M_L}-y_{B_L}\ge h_{M_L}+h_{B_L},\qquad
 y_{M_R}-y_{B_R}\ge h_{M_R}+h_{B_R}.
\]
Adding gives exactly the third inequality in (3). Theorem 2.1
gives \(q\ge q_*\), hence equality under the hypothesis
\(q\le q_*\) and rigidity. \(\square\)

Reflection covers a three-square chain whose outer endpoint
center heights are both at least \(1/2\).

**Important:** B's middle square may have any allowable height.
Neither M nor B needs to be a full horizontal layer. No
all-cross-pairs vertical separation is used. Consequently this
is a genuine new terminal branch for G2.C4.3.

## 4. Exact remaining coverage gap

For a coordinate-separable nine-square packing with a four-chain,
G2.C4.3 is now reduced further: prove that one can find a disjoint
horizontal three-chain whose two endpoint center heights are
both in the outer upper band \(y\ge1/2\) or outer lower band
\(y\le-1/2\), **or** derive a different finite sharp terminal
inequality for all configurations where no such three-chain exists.
The existence of such a three-chain is **not yet proved** by
the four-chain shadow lemma, and the counterexample tests should
precede claiming it.

For genuinely oblique separators, Lemma 3.1 does not apply,
because a pair whose horizontal projections overlap may
be separated on an oblique own-square axis instead of the
vertical axis. Theorem 2.1 itself does apply with no common-frame
separability, once its explicit aggregate vertical inequality
is verified by other geometric means.

No Lean compilation or independent end-to-end theorem audit
is claimed.
