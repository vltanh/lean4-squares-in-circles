# Universal full-unit midpoint horizontal chords in offset caps h>=7/24

Research continuation, 2026-10-12. This establishes an
**exact arbitrary-frame slice ordering** for pairs of whole
squares in the 2+2 near-cap branch, including all centers
and all orientations. It is a geometric ingredient, not a
claim that a same-sign pair or any remaining n=8
status class is impossible.

## Theorem (one square, entire frame/position continuum)

Let a unit square S of arbitrary orientation lie
wholly in a disk \(D_R\) centered at zero and
in the outward half-plane
\[
\{y\ge h\},\quad R^2\le9789/2500,\quad h\ge7/24.
\]
Set the **shared horizontal midpoint slice**
\[
Y=(R+h)/2.
\]
Then \(y=Y\) meets the **open interior** of S
in an open horizontal chord interval of length
\[
\boxed{\ell\ge1.}
\]
Equality is possible only when S has an axis-parallel
frame (then \(\ell=1\)); **every genuinely rotated
frame has \(\ell>1\)**.

The conclusion does not rely on the square
touching either the circle or the cap boundary.

## Proof from the exact true-square chord

Let \(m=(R-h)/2\). The radius hypothesis
gives \(R<99/50\), and hence
\[
m<(99/50-7/24)/2=1013/1200<1.
\]
Reduce the unsigned square orientation modulo
right-angle rotations/reflections to
\(0\le\theta\le\pi/4\). Set
\[
c=\cos\theta,\quad s=\sin\theta,\quad
L=c+s\in[1,\sqrt2],\quad
cs=(L^2-1)/2.
\]

The **full y projection** of the square
has length L and is contained in the strip
\([h,R]\). Its center y coordinate thus
satisfies
\[
h+L/2\le p_y\le R-L/2.
\]
Consequently, at the midpoint \(Y\),
\[
|Y-p_y|\le m-L/2<L/2,
\]
the final strict inequality because \(L\ge1>m\).
So \(y=Y\) meets the open square interior.

At zero tilt, the horizontal chord length is
exactly one. For \(s>0\), intersecting
the square's four true sides with the
horizontal line gives the exact piecewise formula
\[
\ell=
\begin{cases}
1/c,& |Y-p_y|\le(c-s)/2,\\
\displaystyle\frac{L/2-|Y-p_y|}{cs},
  & (c-s)/2<|Y-p_y|<L/2.
\end{cases}
\]
On the plateau branch, \(\ell=1/c>1\).

On a sloping flank, the midpoint-strip estimate
gives
\[
\ell\ge\frac{L-m}{cs}
=\frac{2(L-m)}{L^2-1}.
\]
For fixed \(m<1\), the final rational
function is **strictly decreasing** in
\(1<L\le\sqrt2\): its derivative is
\[
-\frac{2[(L-m)^2+(1-m^2)]}{(L^2-1)^2}<0.
\]
It therefore has minimum at \(L=\sqrt2\),
and
\[
\ell\ge2(\sqrt2-m)
>2(7/5-1013/1200)
=667/600>1.
\]
We used only the exact square inequality
\(\sqrt2>7/5\).
This proves the theorem, including the
strictness for every non-axis-parallel frame.
QED.

## Pair corollary: a mandatory actual horizontal order

If **two distinct** pairwise interior-disjoint unit
squares both lie in the same offset cap
\(y\ge h\ge7/24\) within the same disk,
the **same** horizontal line \(y=Y\)
cuts both open square interiors in intervals
of length at least one. These two open
intervals must be disjoint.

Thus the pair has a **true left-to-right
chord order on this exact common slice**,
without any common frame or chosen square
contact. If one square is rotated, the
sum of chord lengths is strictly greater
than two. This does **not** by itself imply
their **whole horizontal projections** are
disjoint: oblique squares may be separated
at the slice yet their projections overlap.

For the remaining exclusive S2/k=4
nearer-U cap, whose offset lies in
\((7/24,97/200)\), this common-chord
order is available in **all three** cells
of [HUMAN_S2_K4_THREE_CELL_QUEUE.md](HUMAN_S2_K4_THREE_CELL_QUEUE.md),
regardless of their inner/outer and
transverse sign pattern. It is a promising
ingredient for an exact two-square cap
separation argument, **not a proof that
any of A, B, or C is empty**.

The global lower bound \(R_8\ge\widehat R\),
other S2 branches, D0 corner exceptions,
D1/D2 and Lean handoff remain OPEN.
