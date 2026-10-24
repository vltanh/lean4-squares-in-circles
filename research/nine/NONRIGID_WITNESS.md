# n=9: an exact non-parallel attaining construction

**Purpose.** The nine-square record at radius
\(R_*=\sqrt{1105}/16\) is *not* confined to configurations
where all nine squares share a frame. This matters when designing
the unrestricted hand proof: forcing a common frame for *every*
square would give a false equality classification.

## The seven fixed anchors

Keep the following seven axis-parallel squares, each of side one:

\[
\begin{array}{c|c}
x&y\\ \hline
-3/2,-1/2,1/2,3/2&1/16\\
-1,0,1&-15/16.
\end{array}
\]

As shown in [HAND_PROOF.md](HAND_PROOF.md), the four-square group
and three-square group have pairwise disjoint interiors, and their
largest corner squared norm is \(q_*=1105/256\).

## Two further squares, one genuinely rotated

Put the remaining two square centers at
\[
   p=(-3/5,19/16),\qquad p'=(3/5,19/16).
\]
At \(p\), use orthonormal unit axes
\[
 u=(99/101,20/101),\qquad
 v=(-20/101,99/101),
\]
so \(99^2+20^2=101^2\). This is a genuine, non-right-angle
rotation relative to the seven anchors. At \(p'\), use the usual
axis-parallel square.

The horizontal projection of the rotated square has width
\((99+20)/101=119/101\). The other upper square has width 1.
The difference of the two centers' horizontal coordinates is
\(6/5\), and
\[
 \frac65-\left(\frac{119}{202}+\frac12\right)
    =\frac{56}{505}>0. \tag{1}
\]
Thus the two upper squares are horizontally separated.

The lowest point of the rotated square has vertical coordinate
\(19/16-119/202\). The seven anchors are all at or below
\(1/16+1/2=9/16\). The clearance is
\[
 \frac{19}{16}-\frac{119}{202}-\frac9{16}
   =\frac{29}{808}>0. \tag{2}
\]
The axis-parallel upper square has still greater clearance.
Hence the two upper squares are also separated from all seven
anchors.

For a square with center \(c=(x,y)\) and unit axes \(u,v\),
the farthest squared distance among its four corners is
\[
 |c|^2+\frac12+|c\cdot u|+|c\cdot v|. \tag{3}
\]
Direct exact substitution gives, for the rotated upper square,
\[
 \max_{\text{corners}}\!|p\pm u/2\pm v/2|^2
       =\frac{2524789}{646400},\qquad
 q_*-\frac{2524789}{646400}
       =\frac{33167}{80800}>0. \tag{4}
\]
For the axis-parallel upper square,
\[
 \max_{\text{corners}}\!|p'\pm(1/2,1/2)|^2
       =\frac{25969}{6400},\qquad
 q_*-\frac{25969}{6400}
       =\frac{207}{800}>0. \tag{5}
\]
All four vertices in each upper square therefore lie strictly
inside the record circle. Convexity of the disk then gives
containment of the entire square.

**Conclusion.** These nine squares form a packing at squared
radius exactly \(q_*\); four pinned anchor corners still attain
the boundary. But one square is turned relative to the other
eight. The two added squares have strictly positive separation
and disk-containment slack, so small changes of their positions
and rotations also preserve a packing. No numerical optimization
or computer-generated certificate is used in this argument.

**Caution:** this proves that multiple distinct *record-radius
packings* exist. It does **not** prove the record radius globally
optimal; the unrestricted lower bound remains open.
