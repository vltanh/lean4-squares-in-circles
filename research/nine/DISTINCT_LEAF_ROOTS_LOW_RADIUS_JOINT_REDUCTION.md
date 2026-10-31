# Two distinct leaf roots: a joint reduction to the upper radius interval

**Status: complete hand reduction; independent root review passed.**
See REVIEW_DISTINCT_LEAF_ROOTS_LOW_JOINT_2026_10_25.md.
Keep the common physical certificate, all actual positive forces,
selected normals, side means and all original physical units. Put
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad r=R-\sqrt2.
\]
The principal reduction concerns the strict lower interval
\[
                      d<1,\qquad R^2<17/4.
 \tag{1}
\]
It retains the equality \(R^2=17/4\) in the remaining upper interval.
No new gate is introduced, and no full-window parent is closed by
this reduction alone.

## 1. The full normal form for two distinct genuine leaf roots

Let two distinct physical units \(A,H\) each have a genuine positive
leaf. Their positive degrees may be arbitrary.

A D-leaf root contains \(O\) in its open interior. An S-leaf root
contains \(O\) when \(d<1\), by the actual inward unit segment
from its radial support point \(de\). Consequently neither root
can have a D leaf: the other square has interior points arbitrarily
close to its point \(O\), which would overlap the open neighborhood
of \(O\) in the D root.

For an S root tilted relative to its genuine leaf direction, the
full root chart is
\[
 de+[0,1](-a,-b)+[0,1](-b,a),
 \qquad a,b>0,\quad a^2+b^2=1,
\]
up to reflection. The origin has own coordinates \(da,db\),
both strictly between zero and one when \(d<1\). Thus a tilted
root would also contain \(O\) in its open interior, impossible.

Both roots are therefore aligned S roots. In the radial direction
their interval is \([d-1,d]\), and \(O\) is strictly interior
to that interval. To avoid interior overlap at \(O\), each root
has \(O\) on a transverse side, in the relative interior of that
side. Their open tangent half-planes at \(O\) must be disjoint,
so the half-planes are opposite and their boundary lines coincide.

The leaf directions are consequently parallel or antiparallel.
They cannot be equal, since the same direction and radius determine
the same genuine radial S leaf. After rotation and reflection,
the exact physical roots and leaf forces are
\[
 \begin{aligned}
 A&=[d-1,d]\times[0,1],&
 H&=[-d,1-d]\times[-1,0],\\
 F_{L_A}&=\lambda e_x,&
 F_{L_H}&=-\mu e_x,\qquad\lambda,\mu>0.
 \end{aligned}
 \tag{2}
\]
Every other original root force remains present. This is a geometric
normal form, not a reduction of either root's positive degree.

## 2. No circle-touching square can touch both roots

**Theorem 2.1.** In the normal form (2), no physical circle-touching
unit square \(X\) can touch both \(A,H\), even with zero stress
at either contact or zero total circle weight on \(X\).

The common radius window gives \(d>9/10\) and \(r>1/2\).
Set \(a=1-d\), so \(0<a<1/10\). Every point of a
circle-touching square has norm at least \(r\): subtract its
distance, at most \(\sqrt2\), from a circle corner.

Suppose \(p\in X\cap A\) and \(q\in X\cap H\). Then
\[
 |p|,|q|>1/2,\quad p_y\ge0,\quad q_y\le0,\quad
 p_x\ge-a,\quad q_x\le a.
 \tag{3}
\]
If \(p_x\ge0\), then
\[
 p\cdot q\le p_xq_x\le a|p|
                  <\frac15|p|\,|q|.
\]
If \(p_x<0\), use \(|p_x|\le a\) instead to get
\[
 p\cdot q\le p_xq_x\le a|q|
                  <\frac15|p|\,|q|.
\]
Thus the angle between the two nonzero vectors is greater than
\(\arccos(1/5)>\pi/3\).

But CIRCLE_CONTACT_ANGULAR_ORDER.md, Lemma 4.1, proves that the
entire angular shadow of every physical circle-touching unit in
the window has length strictly less than \(\pi/3\).
Both \(p,q\) belong to \(X\), a contradiction. This proves the
theorem without any force equation at \(X\).

## 3. A leaf root in this interval has no unloaded degree-two neighbor

This elementary part of the existing normal-channel estimate is useful
independently of the two-root normal form.

Let \(A\) be any genuine leaf root with \(d<1\). Then \(O\in A\).
Suppose \(U\) is a true unloaded degree-two neighbor of \(A\), with
other positive neighbor \(C\). The actual channel has unit direction
\(n\), reserve \(w\ge1\), and support value \(\alpha\), with
\[
 A\subseteq\{n\cdot x\le\alpha\},\qquad
 C\subseteq\{n\cdot x\ge\alpha+w\}.
\]
The origin premise gives \(\alpha\ge0\). The center bound
\(|c_C|\le d+1/2\), and halfwidth at least \(1/2\), give
\[
                  \alpha+w\le d<1.
\]
This contradicts \(w\ge1\). The proof needs no force or degree
premise at \(A,C\), and retains the actual channel means.

## 4. Two antipodal radial leaves cannot balance a boundary contact pair

The following implication holds throughout the full radius window,
without the root normal form (2).

**Lemma 4.1.** Let \(B,C\) be two physically touching
circle-touching units with positive actual circle resultants
\(F_B,F_C\). Let \(L\) be any other physical circle-touching unit
whose center direction is \(e\). Then
\[
                     F_B+F_C\notin\mathbb R_{>0}e.
 \tag{4}
\]

To prove it, use the center-order bounds of
CIRCLE_CONTACT_ANGULAR_ORDER.md, Lemmas 2.1 and 3.1, and the
all-mask resultant-direction bound assembled in Section 1 of
BOUNDARY_THREE_PATH_RESULTANT_CONE.md:

- Any two circle-touching center directions differ by more than
  \(\pi/5\).
- A physical boundary contact has an empty minor center-angle arc
  of length less than \(2\pi/5\).
- Every actual positive circle resultant differs from its own
  center direction by less than \(\pi/12\), including either
  zero individual weight in a physical two-corner mask.

Choose compatible lifts \(\alpha_B<\alpha_C\) for the contacting
centers and \(\beta_B,\beta_C\) for their actual resultant
directions. Then
\[
 0<\beta_C-\beta_B
       <\frac{2\pi}{5}+\frac{\pi}{6}
       =\frac{17\pi}{30}<\pi.
 \tag{5}
\]
The lower strict inequality follows from
\(\pi/5-\pi/6=\pi/30>0\).
Their positive sum is nonzero and has direction strictly between
\(\beta_B,\beta_C\).

If that direction were \(e\), choose the center-direction lift
\(\alpha_L\in(\beta_B,\beta_C)\) of the physical boundary unit \(L\).
It must lie strictly between \(\alpha_B,\alpha_C\). Indeed if
\(\alpha_L\le\alpha_B\), then
\[
 0\le\alpha_B-\alpha_L<\pi/12,
\]
contradicting the center-angle separation \(>\pi/5\). The
case \(\alpha_L\ge\alpha_C\) is identical. An intermediate
circle-touching center contradicts the empty minor arc of the
physical \(BC\) contact. This proves (4).

**Corollary 4.2.** A positive component cannot have exactly four
positively loaded bodies consisting of two genuine radial leaves
in antipodal directions and a physically touching pair \(B,C\).

Its genuine component force sum would give
\[
        F_B+F_C=-(\lambda-\mu)e.
\]
If \(\lambda=\mu\), this contradicts the nonzero pair sum in
(5). Otherwise it is a positive multiple of the center direction
of one of the two original radial leaves, contrary to Lemma 4.1.
No leaf or pair force was suppressed to obtain the component sum.

## 5. All distinct-root layouts of C1.4.b2 have the same upper remainder

Use the exact labels and full positive-load cover in
FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md. The component is still
the original six bodies, with all three additional physical
squares retained.

| Original layout | Original block loads | Uniform exclusion at \(d<1\) |
| --- | --- | --- |
| C4 \(A-B-C-D-A\), leaves at adjacent \(A,B\) | \(C\), with reflected \(D\) included | \(D\) is a true unloaded degree-two neighbor of the genuine leaf root \(A\); Section 3 excludes it. |
| The same adjacent-root C4 | \(CD\) | The two actual leaf directions are antipodal by (2), and \(C,D\) are the only other loaded units and physically touch. Corollary 4.2 applies. |
| C4 leaves at opposite \(A,C\) | \(BD\) | Either \(B\) or \(D\) is a circle-touching common neighbor of both roots, forbidden by Theorem 2.1. |
| Diamond, leaves at both hubs \(H,K\) | \(BC\) | Each loaded page tip is a physical common neighbor of both roots, forbidden by Theorem 2.1. |
| Diamond, leaves at both tips \(B,C\) | \(HK\) | Either loaded hub is a physical common neighbor of both roots, forbidden by Theorem 2.1. |
| Diamond, leaves at hub \(H\) and tip \(B\) | \(KC\) | The actual loaded hub \(K\) is a common neighbor of the two roots, forbidden by Theorem 2.1. |

Thus all five distinct-root attachment layouts, with all six original
block-load orbits, reduce simultaneously to
\[
                         \boxed{17/4\le R^2\le1105/256}.
 \tag{6}
\]
For mixed S/D assignments, the prior root-interior theorem already
makes the lower endpoint strict. All D/D assignments were already
excluded throughout the window.

The existing S/S leaf-family IDs affected by this reduction are
M6.B4L2.C4.ADJACENT.LC.SS,
M6.B4L2.C4.ADJACENT.LCD.SS,
M6.B4L2.C4.OPPOSITE.LBD.SS,
M6.B4L2.DIAMOND.TWO_HUBS.LBC.SS,
M6.B4L2.DIAMOND.TWO_TIPS.LHK.SS, and
M6.B4L2.DIAMOND.HUB_TIP.LKC.SS.
Their entire upper intervals and the equality \(R^2=17/4\) remain
under the same original IDs. This source alone changes none to
closed and does not create LOWER/HIGH subgate IDs.

The separately accepted full-window
BOUNDARY_EDGE_OUTER_FACE_AND_DIAMOND_EXCLUSION.md supersedes the
two-tip diamond row. It is not used anywhere in this proof.

## 6. Precise remaining join

The same-root C4 and diamond pressure theorems close the two common-root
attachments independently of this reduction. The separate
SIDE_S_ARM_ADJACENT_C4_EXCLUSION.md closes the complete side-normal
S-arm/adjacent-load gate. Neither fact closes a distinct-root upper
domain or either entire bridge-arm parent.

A common-neighbor exclusion cannot simply be extended to arbitrary
two near-origin leaf roots at \(d>1\): the completed distinct-S-leaf
triangle wall core supplies an actual positive five-body example
in that interval. A valid upper-interval join must retain the second
common boundary neighbor, the extra connected triangle tip, or the
actual unloaded-transmitter/bypass geometry from the relevant row.
The wall-core capacity theorem cannot be imported after replacing
two actual loads by one fictitious square.

All arguments here are uniform geometric or force-sum implications.
No scalar coefficient table, numerical pose search, Lean compilation
or CI is used.

