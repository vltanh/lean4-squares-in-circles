# Adjacent S leaves: the complete four-parallel-frame interface

Status: complete original-domain interface proof, awaiting independent review.
The earlier attempted write did not survive the workspace rollback; this is
the first verified saved version.

Use the original high-radius adjacent-C4 domain
`ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md`.
The positive edges are
\[
 AB,BC,CD,DA,AL,BM,
\]
with true degrees \(A3,B3,C2,D2,L1,M1\). The genuine leaves \(L,M\) are
S leaves; \(C,D\) are physically boundary, each with one physical circle
corner. All nine physical squares remain present. Put
\[
 Q_*=1105/256,\quad d=\sqrt{R^2-1/4}-1=1+\varepsilon,
 \quad0<\varepsilon<1/60.
\]

**Theorem.** This entire domain is impossible if the actual frames of all
four cycle squares \(A,B,C,D\) are parallel. The original means on every
shared side are arbitrary. No two-by-two grid is assumed.

Choose the actual \(AB\) normal east. Then
\[
 A_x=[h-1,h],\qquad B_x=[h,h+1],\qquad |h|\le\varepsilon.
\]
Reflect vertically so that the original common positive cycle moment is
\(\tau>0\). If the actual \(AB\) mean is \((h,p)\), then \(p<0\).
Both statements are the unchanged common-domain conclusions. In this
parallel-frame setting an actual owned-axis positive contact has a segment
of positive length: a point-only contact has the strictly interior selected
point normal, not an endpoint own-axis normal.

## 1. Horizontal genuine leaves are impossible, without an owner-selection assumption

Suppose first that the genuine leaf at \(A\) is horizontal. It cannot point
east because that support is \(h\le\varepsilon<d\). Thus it points west,
\[
 h=-\varepsilon,\qquad A_x=[-d,-\varepsilon],
\]
and \(A\)'s vertical interval contains zero. Its full true three-force
equation makes \(AD\) horizontal.

If \(AD\) points west, the actual parallel square \(D\) has horizontal
interval \([-d-1,-d]\). Writing its vertical center as \(y_D\), containment
and \(R^2=(d+1)^2+1/4\) give
\[
 (d+1)^2+(|y_D|+1/2)^2\le R^2,
\]
so \(y_D=0\). This would make \(D\) identical with the genuine leaf \(L\).
Therefore \(AD\) points east. Now \(B,D\) have the same horizontal interval
\(I=[-\varepsilon,1-\varepsilon]\).

Let \((-\varepsilon,q)\) be the actual \(AD\) mean and let the two positive
magnitudes be \(\mu,\nu\). The full original moment equation at \(A\) is
\(\mu p+\nu q=0\), so \(q>0\). Since \(p<0<q\) and the actual vertical
intervals of \(B,D\) have disjoint interiors, \(D\) is above \(B\):
\[
 B_{\rm top}\le D_{\rm bottom}.
\]
The genuine near point \(\varepsilon e_M\in B\) gives
\(B_{\rm top}\ge-\varepsilon\), hence
\(D_{\rm bottom}\ge-\varepsilon\). Its farthest actual corner is therefore
\((1-\varepsilon,D_{\rm bottom}+1)\). Because \(D\) is physically boundary,
\[
 (D_{\rm bottom}+1)^2
 =R^2-(1-\varepsilon)^2=13/4+6\varepsilon>(9/5)^2,
\]
and thus \(D_{\rm bottom}>4/5\).

The positive-length \(AB,AD\) side contacts imply
\[
 A_{\rm bottom}<B_{\rm top}\le D_{\rm bottom}<A_{\rm top}.
\]
Consequently the vertical gap from \(B\) to \(D\) has length strictly less
than one. Consider the real parallel unit \(C\), which touches both.
If its horizontal interior overlaps the interior of \(I\), disjointness
requires its entire unit vertical interval to lie in that gap and to touch
both endpoints; the gap would have length one, a contradiction.
Otherwise its horizontal interval must be either
\([-d,-\varepsilon]\) or \([1-\varepsilon,2-\varepsilon]\).
In the first case its vertical interval connects \(B\) to \(D\), while
\(A\) contains an open neighborhood of the intervening gap. This overlaps
the interior of \(A\). The same conclusion holds when the gap is zero:
\(A\) contains that height in its vertical interior, and \(C\) has a
nonempty interval on at least one of its sides.
In the second case any actual \(CD\) point has height
\(y\ge D_{\rm bottom}>4/5\). The actual point
\((2-\varepsilon,y)\in C\) then has squared norm
\[
 >(119/60)^2+(4/5)^2=16465/3600>Q_*.
\]
This excludes a horizontal leaf at \(A\).

Reflecting horizontally and interchanging \(A,B\) and \(C,D\) gives the
same argument for a horizontal leaf at \(B\). This reflection/relabeling
preserves the positive-cycle convention. No extra cycle force has been
discarded in either case.

## 2. All four cycle normals are actual own axes

The two nonleaf forces at each of \(A,B\) are now nonparallel, because the
genuine leaf has a nonzero vertical component. The true loaded \(C2,D2\)
pairs are nonparallel by the genuine two-force concurrence theorem, each
having the other as a boundary neighbor. Apply
`ADJACENT_S_LEAF_C4_ALL_NONPARALLEL_PAIRS_SIDE_OWNER_SELECTION.md`.
It makes every original cycle contact side-owned at at least one endpoint,
using a compatible finite choice before extraction. In the present parallel
frames, all four selected normals are therefore common frame axes.

The nonparallel pairs at \(A,B\) force \(AD,BC\) vertical. The nonparallel
pairs at \(C,D\) then force \(CD\) horizontal. Every such physical contact
has positive side length, by the initial strict point-normal selection.
The horizontal components of the full root equations say that \(A\)'s
genuine leaf points left and \(B\)'s genuine leaf points right. Thus their
actual inner support points are left and right vertices, respectively.
Write
\[
 X=1-h,\quad Y=1+h,\quad
 v^2=d^2-X^2,\quad w^2=d^2-Y^2.
\]
Here
\[
 0<v,w<4/15,\qquad X,Y>59/60,\qquad v^2-w^2=4h. \tag{1}
\]
Their vertical signs are not yet chosen.

## 3. The actual side layout and the signs of the two leaves

If \(A\)'s leaf is lower left, its square is vertically
\([-v,1-v]\), and the positive \(AD\) force points north, putting \(D\)
above it. If its leaf is upper left, the reflected statement puts \(D\)
below it. The same holds for \(B,C\). Opposite vertical signs of the two
leaves would put one of \(C,D\) wholly above \(11/15\) and the other wholly
below \(-11/15\); they could not touch. The signs are equal.

The actual horizontal contact of \(C,D\) cannot have \(C\) on the left.
Indeed, writing \(C_x=[k-1,k]\), \(D_x=[k,k+1]\), the positive-length
vertical \(AD\) contact would require \(k<h\), whereas the positive-length
vertical \(BC\) contact would require \(k>h\).
Thus \(D\) is on the left and the original \(C\)-to-\(D\) normal is west.
If both genuine leaves were upper vertices, all actual \(CD\) points would
have negative height, and
\(\det(P_{CD},-e_x)<0\), contrary to \(\tau>0\).
Both leaves are therefore lower vertices.

The complete physical layout is now
\[
\begin{array}{ll}
 A=[h-1,h]\times[-v,1-v],& B=[h,h+1]\times[-w,1-w],\\
 D=[k-1,k]\times[1-v,2-v],& C=[k,k+1]\times[1-w,2-w].
\end{array}                                                   \tag{2}
\]
The horizontal offset \(k\), the side means, and both lower depths are
still the original ones; no symmetry has been imposed.

## 4. The unchanged full equations force a two-by-two grid

The actual upper-right corner of \(C\) and upper-left corner of \(D\)
have heights greater than \(26/15\). Since
\((6/5)^2+(26/15)^2=40/9>Q_*\), containment gives
\(|k+1|,|k-1|<6/5\), hence \(|k|<1/5\).
In (2) the unique farthest corners are consequently
\[
 Z_C=(1+k,2-w),\qquad Z_D=(k-1,2-v).
\]
Both are actual circle corners. Subtracting their squared norms and using
(1) yields
\[
 k=h-(v-w).                                            \tag{3}
\]

Keep the original positive magnitudes: \(\mu\) on \(AB\),
\(\nu_A\) on \(AD\), \(\nu_B\) on \(BC\), and \(\kappa\) on \(CD\).
The full \(A3,B3\) force equations, including the actual genuine leaves,
give
\[
 \frac{\nu_A}{\mu}=\frac v{1-h},\qquad
 \frac{\nu_B}{\mu}=\frac w{1+h}.                       \tag{4}
\]
The full loaded \(D2,C2\) force equations, using their actual circle
corners, give
\[
 \frac{\nu_A}{\kappa}=\frac{2-v}{1-k},\qquad
 \frac{\nu_B}{\kappa}=\frac{2-w}{1+k}.                 \tag{5}
\]
All four equations concern the same original magnitudes. No degree-three
or zero-external-moment surrogate is used.

If \(h>0\), (1) gives \(v>w\), so (4) implies \(\nu_A>\nu_B\).
But
\[
 v-w=\frac{4h}{v+w}>h,
\]
and (3) gives \(k<0\). Equation (5) then implies
\(\nu_A<\nu_B\), a contradiction. For \(h<0\) all these comparisons
reverse, again contradicting each other. Thus
\[
 h=0,\qquad v=w,\qquad k=0.
\]
The four actual squares tile
\([-1,1]\times[-v,2-v]\), and the actual genuine S leaves have inner
support points \((-1,-v)\) and \((1,-v)\).

## 5. The original three-square completion is impossible

Apply the complete force-free theorem
`TWO_BY_TWO_CORE_ADJACENT_RADIAL_LEAVES_COMPLETE_CAPACITY.md` to these six
actual squares. Its hypotheses are precisely a physical two-by-two block,
two genuine radial S leaves at the endpoints of one exterior side, and
containment under \(Q_*\). It permits at most two further unit squares,
of arbitrary orientations and with arbitrary contacts. The original domain
has three further physical squares. This contradiction closes the whole
four-parallel-frame interface.

The proof leaves the branches with a tilted \(C\) or \(D\) separate.
It does not claim that the six-body core equations alone are inconsistent:
their surviving grid is excluded by its same-nine physical completion.
