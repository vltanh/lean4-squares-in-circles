# One common translation bounds the whole tilted double-axis long pocket by two

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_TILTED_TERMINAL_AND_DOUBLE_AXIS_LONG_C6_RECOVERY_2026_10_26.md.

Keep the original tilted double-axis family \(m=f_2,n=f_1\),
the genuine S leaf L, true degrees, all actual normals and positive
forces, both linked original root means, both individual physical
radial weights at C, all B masks and U,V sliders, and all nine units.

Use S_LEAF_C5_TILTED_DOUBLE_AXIS_B_FEATURE_REDUCTION.md. Its full
three-row cover gives, with \(v=\sqrt\delta\),
\[
\begin{gathered}
0<v<1/\sqrt{60}<1/4,\quad d=1+v^2,\quad
a=(1-v^2)/d,\quad b=2v/d,\\
A=[-v^2,1-v^2]\times[2v-1,2v],\quad
C=[-d-1,-d]\times[-1/2,1/2],\\
p_{AU}=(-v^2,T),\quad p_{CU}=(-d,T),\qquad
v<T\le2v.
\end{gathered}
\tag{1}
\]
The strict lower bound on T was proved from the original means,
not chosen in this theorem. The endpoint \(T=2v\), with both root
means zero, is included.

**Theorem.** At most two of the three actual physical extras can
occupy the original long exterior region bounded by the C--U--A--L
path. In particular all three cannot occupy it, even with arbitrary
independent orientations and repeated occupancy.

## 1. The actual crosscut and the single comparison frame

In the root frame of (1), the actual leaf has radial direction
\(n_L=(a,b)\), transverse direction \(j_L=(-b,a)\), and inner
midpoint
\[
p_0=d n_L=(1-v^2,2v).
\]
Its upper outer circle point is
\[
z_L=(d+1)n_L+\frac12j_L,
\]
and the upper outer C circle point is
\[
z_C=(-d-1,1/2).
\]
Use the occupied crosscut, in this order:
\[
\begin{split}
z_C&\longrightarrow(-d,1/2)
\longrightarrow(-d,T)
\longrightarrow(-v^2,T)\\
&\longrightarrow(-v^2,2v)
\longrightarrow p_0
\longrightarrow p_0+j_L/2
\longrightarrow z_L.
\end{split}
\tag{2}
\]
Each segment lies in the indicated original closed body: C, its
actual inner face, the actual reserve-one U channel, the left and
upper sides of A, and the inner face and upper side of L. The
root-side segment may have zero length at \(T=2v\); it is simply
deleted without changing either actual mean.

The path is simple after deleting that zero segment. Its interior
segments occupy the actual consecutive bodies and meet at the
displayed original applications; the coordinate orders in (1)
also show directly that they do not cross. In particular
\(T\le2v<13/50<1/2\), the U segment ends at the left root side,
and the leaf-side segments lie above the root after leaving p0.

Define the fixed orthonormal basis and one translation
\[
e=(1,v)/\sqrt d,\qquad j=(-v,1)/\sqrt d,\qquad
P_*=(-v^2,v)=v\sqrt d\,j.
\tag{3}
\]
Every tested extra is translated by this same \(P_*\) and expressed
in this same basis. No physical packing or individual mean is moved
independently.

The two outer endpoints have equal positive j projection. Their
minor circle arc through the positive j axis is therefore the
selected upper arc. No other B circle point is on it: the complete
B feature cover has every B point at root height at most
\(-H<-37/50\) and horizontal coordinate greater than -1, so its
j projection is negative, using \(v<13/100\). The latter fixed
comparison follows from \(1/60<(13/100)^2\), whose reserve is
\(7/30000\). The other L,C circle corners also have negative
j projection, since
\[
(d+1)v-\frac12<(121/60)(13/100)-\frac12<0.
\]
Thus (2) and this minor arc give the actual outer crosscut for the
long region. The actual free pocket lies inside its bounded Jordan
side; other contacts may subdivide that side but do not enlarge it.

## 2. Every point of the whole region is above the comparison axis

The translated j heights of the relevant crosscut vertices are
\[
\begin{array}{c|c}
\text{actual vertex}&j\cdot(z-P_*)\\ \hline
z_C,z_L&(v+1/2)/\sqrt d\\
(-d,1/2),p_0+j_L/2&1/(2\sqrt d)\\
(-d,T)&T/\sqrt d\\
(-v^2,T)&(T-v)/\sqrt d\\
(-v^2,2v)&v/\sqrt d\\
p_0&0 .
\end{array}
\tag{4}
\]
All are nonnegative, and the actual U mean gives the strict
\(T-v>0\). The j projection along the selected minor arc is
minimized at its endpoints, so it is also positive after
translation. Half-plane convexity now contains the complete
crosscut, arc and their bounded side in the upper half-plane.
Every whole translated extra therefore satisfies \(y\ge0\).

This is a whole-region conclusion from actual occupied barriers.
It does not assume that an extra stays in a sector merely because
its center is there.

## 3. The actual radial terminals imply avoidance of two canonical terminals

Put
\[
c=1/\sqrt d,\qquad s=v/\sqrt d.
\]
In the coordinates (3), the two entire unchanged terminals become
\[
\begin{split}
L-P_*&=[1,2](c,s)+[-1/2-v,1/2-v](-s,c),\\
C-P_*&=[1,2](-c,s)+[-1/2-v,1/2-v](s,c).
\end{split}
\tag{5}
\]
For example \(n_L\cdot P_*=v^2\), so its inner radial coordinate
is \(d-v^2=1\), while \(j_L\cdot P_*=v\). The C calculation is
its reflection. Thus (5) keeps the full actual transverse shifts.

The physical outer-face screen in RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1, applies at the original radius as well: the exact center
bound is \(d+1/2\), and the actual radial outer face is at d+1.
The same chord and unshareable-circle-vertex argument gives radial
projection strictly less than d+1 for every point of any other
physical unit. After the single translation,
\[
\max_{E-P_*}(c,s)\cdot z<2,\qquad
\max_{E-P_*}(-c,s)\cdot z<2.
\tag{6}
\]
The argument uses the actual terminal geometry and no equality of
its two circle weights.

The entire upper unit and exact shifted terminal in (5)--(6)
satisfy UNIT_TILTED_RADIAL_TERMINAL_SCREEN.md. It follows that every
translated extra avoids the open interior of
\([1,2]\times[-1/2,1/2]\). Reflection gives avoidance of
\([-2,-1]\times[-1/2,1/2]\). This is a comparison theorem for whole
units; it does not assert a pointwise containment between the two
terminal shapes.

## 4. The complete region is strictly inside squared radius 17/4

Both actual outer endpoints have the same translated squared norm:
\[
|z_L-P_*|^2=|z_C-P_*|^2
=4+(v-1/2)^2
=\frac{17}{4}-(v-v^2)<\frac{17}{4}.
\tag{7}
\]
Since \(P_*\) is a positive multiple of j and the j projection
on the selected minor arc is minimized at the endpoints, the
identity
\[
|z-P_*|^2=R^2+|P_*|^2-2P_*\cdot z
\]
bounds every point of that arc by (7).

The inner upper terminal vertices have squared norm
\(1+(v-1/2)^2\) after translation. The other crosscut vertices
satisfy, directly in the original root frame,
\[
\begin{split}
|(-d,T)-P_*|^2&=1+(T-v)^2\le1+v^2,\\
|(-v^2,T)-P_*|^2&=(T-v)^2\le v^2,\\
|(-v^2,2v)-P_*|^2&=v^2,\\
|p_0-P_*|^2&=1+v^2.
\end{split}
\tag{8}
\]
All are strictly below 17/4. By convexity, every segment of the
actual crosscut lies in the same open disk. Its compact boundary,
and hence its complete bounded side, lies strictly inside that
disk. Thus every whole translated extra obeys
\[
E-P_*\subset\operatorname{int}D_{\sqrt{17}/2}.
\tag{9}
\]

## 5. Full repeated-occupancy conclusion

The one common translation and rotation preserve all square
shapes and pairwise interior-disjointness. Sections 2--4 place
any three extras in the same upper half-disk of squared radius
17/4, avoiding the two opposite canonical terminals.
HALF_POCKET_TRIPLE_RIGIDITY.md forces every such triple to be its
canonical triple, which has outer-circle vertices. This contradicts
the strict whole-region inclusion (9).

Consequently \(n_{\rm long}\le2\) throughout the entire original
double-axis family, including both root mean endpoints and all B
masks and sliders. This is a physical completion bound, not a
six-body core contradiction. The central, leaf-side and return
pockets keep their separate capacity obligations until assembled.

