# Two parallel roots with lower radial leaves leave room for at most four other units

Status: complete force-free physical capacity theorem, awaiting independent
review. No orientation or stress is prescribed for any completion square.

Put
\[
 Q=1105/256,\quad\rho=9/8,\quad\delta=2\pi/9,
 \quad d=1+\varepsilon,\quad0<\varepsilon<1/60,
 \quad R^2=(d+1)^2+1/4\le Q.
\]
Suppose four actual contained, interior-disjoint unit squares are as follows:
\[
\begin{split}
 A&=[h-1,h]\times[-v,1-v],
 &X=1-h,&\quad X^2+v^2=d^2,\\
 B&=[h,h+1]\times[-w,1-w],
 &Y=1+h,&\quad Y^2+w^2=d^2,
\end{split}                                                   \tag{1}
\]
where \(|h|\le\varepsilon\), and their two actual radial S leaves are
at the lower outer support points \((-X,-v)\), \((Y,-w)\).
Assume
\[
 v>1/8,\qquad w>1/8.                                  \tag{2}
\]
Then at most four further unit squares can be added inside the same circle,
at arbitrary orientations and with arbitrary physical contacts. In
particular these four actual squares cannot belong to a nine-unit packing.
There is no graph-degree, selected-normal, force or circle-weight premise.

We use the complete theorem
`FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md`: every actual
contained unit at distance strictly greater than \(1/8\) from the origin
has one connected open radius-\(\rho\) arc longer than \(\delta\),
containing its actual radial-center point.

## 1. Every further actual unit has the required strict clearance

From (1),
\[
 X,Y>59/60,\qquad X,Y<61/60,\qquad
 0<v,w<4/15,
\]
because \(v^2,w^2\le4\varepsilon<1/15\). Write
\(m=\min(v,w)>1/8\). The union of the two actual root squares contains
the complete rectangle
\[
 [-X,Y]\times[-m,1-\max(v,w)],
\]
and therefore contains the whole closed origin disk of radius \(m\).
Any further actual square \(E\), disjoint in open interior from both
roots, has \(\operatorname{dist}(O,E)\ge m\). To include boundary points
in this assertion, a point of \(E\) inside the open radius-\(m\) disk
would have actual interior points of \(E\) arbitrarily close to it.
Their neighborhood meets the interior of at least one of the two root
tiles, even on their common side, contradicting disjointness.

Thus every further unit has clearance strictly greater than \(1/8\).
Its complete open radius-\(\rho\) intersection is consequently one arc
longer than \(\delta\). Distinct further squares give disjoint arcs.
Each such open arc also avoids the closed intersections of all four
given squares: an interior point of one square cannot lie on the boundary
of another actual square without a neighboring open-interior overlap.

## 2. The exact actual root arcs

Define
\[
 \theta_A=\arccos(X/\rho),\quad
 \eta_A=\arcsin((1-v)/\rho),
\]
and define \(\theta_B,\eta_B\) with \(Y,w\) in place of \(X,v\).
The entire closed radius-\(\rho\) intersection of \(A\) is
\[
 [\pi-\eta_A,\pi-\theta_A],
\]
and that of \(B\) is
\[
 [\theta_B,\eta_B].                                  \tag{3}
\]
Here angles are taken counterclockwise from the positive horizontal axis.

To check that (3) loses no physical feature, a radius-\(\rho\) point
in either root cannot have negative y, since
\[
 (61/60)^2+(4/15)^2<\rho^2.
\]
Nor can an A point have nonnegative x, or a B point nonpositive x:
the corresponding squared norm is at most \(\varepsilon^2+1<\rho^2\).
In the stated quadrants the shallow inner vertical sides are inactive,
since even at y=1 the circle has \(|x|\ge\sqrt{\rho^2-1}>1/2\).
The outer vertical and upper horizontal sides therefore give exactly
the endpoints in (3). Each interval has positive length because
\[
 X^2+(1-v)^2=d^2+1-2v>22/15>\rho^2,
\]
and likewise for \(B\).

The useful strict bounds are
\[
 0<\theta_A,\theta_B<\pi/6,
 \qquad \pi/6<\eta_A,\eta_B<\pi/2.                  \tag{4}
\]
Indeed \(X/\rho,Y/\rho>118/135>\sqrt3/2\), with squared integer
reserve \(4\cdot118^2-3\cdot135^2=1021\), while
\((1-v)/\rho,(1-w)/\rho>88/135>1/2\).

## 3. The exact actual radial-leaf arcs

Put
\[
 \phi_A=\arctan(v/X),\quad\phi_B=\arctan(w/Y),
 \qquad\alpha=\arccos(d/\rho).
\]
The genuine leaf directions are \(\pi+\phi_A\) and \(2\pi-\phi_B\).
Adding the two radius identities in (1) gives
\[
 d^2=1+h^2+(v^2+w^2)/2>65/64.
\]
Therefore \(\sqrt{\rho^2-d^2}<1/2\). On the radius-\(\rho\) circle
the inner side of either actual S leaf is the active condition; its
outer side is farther out and its two transverse sides are strictly
inactive throughout this interval. Its complete closed arc is exactly
the interval of half-width \(\alpha\) about its genuine direction.
This uses the full actual leaf square, not merely a chosen occupied
subarc.

Furthermore
\[
 0<\phi_A,\phi_B<\alpha<\pi/6.                        \tag{5}
\]
The last comparison follows from \(d/\rho>8/9>\sqrt3/2\).
For the middle comparison,
\(\rho X,\rho Y>177/160>d^2\); the rational difference from
\((61/60)^2\) is \(523/7200\). Thus
\(X/d,Y/d>d/\rho\), and comparison of their cosines proves (5).

## 4. Every actual complementary gap has capacity at most two

The four closed actual arcs from (3) and Section 3 have their physical
circular order. Their complement has at most four gaps; a zero-length
gap causes no difficulty. Their lengths are
\[
\begin{array}{ll}
 G_{\rm right}=\theta_B+\phi_B-\alpha,&
 G_{\rm left}=\theta_A+\phi_A-\alpha,\\
 G_{\rm top}=\pi-\eta_A-\eta_B,&
 G_{\rm bottom}=\pi-\phi_A-\phi_B-2\alpha.
\end{array}                                                   \tag{6}
\]
Actual disjointness supplies their nonnegative ordering; the estimates
below also cover an absent gap. By (4)--(5),
\[
 G_{\rm right},G_{\rm left}<\pi/6<\delta,
 \qquad G_{\rm top}<2\pi/3=3\delta.                  \tag{7}
\]

For the bottom gap, each sum \(\phi_A+\alpha\),
\(\phi_B+\alpha\) is strictly greater than \(\pi/6\).
Here is a uniform exact verification. The bounds in (2) give
\[
 \frac vd,\frac wd>\frac{15}{122},\qquad
 \sqrt{\rho^2-d^2}>12/25,
\]
where the last squared reserve is
\(81/64-(61/60)^2-(12/25)^2=581/360000>0\).
Consequently
\[
\begin{split}
 \cos(\phi_A+\alpha)
 &=\frac X\rho-
   \frac vd\frac{\sqrt{\rho^2-d^2}}\rho\\
 &<\frac{122}{135}-\frac{16}{305}
   =\frac{1402}{1647}<\frac67<\frac{\sqrt3}{2}.
\end{split}
\]
The comparison with \(6/7\) has reserve \(68/11529\), and
\((6/7)^2<3/4\). The same calculation applies to \(\phi_B\).
The sums lie in \((0,\pi/2)\) by (5), so the cosine comparison gives
the claimed angular bound. Therefore
\[
 G_{\rm bottom}<2\pi/3=3\delta.                       \tag{8}
\]

Every further unit has one complete connected open arc longer than
\(\delta\), by Section 1. It must lie in one actual gap of (6), since
it avoids the four closed occupied arcs. The two side gaps in (7) hold
none. Each of the top and bottom gaps in (7)--(8) holds at most two:
three disjoint arcs of length strictly greater than \(\delta\) would
already exceed its full length. Thus there are at most four further
actual units.

## 5. Exact adjacent-C4 consequence and limits

In the strict/strict domain of
`ADJACENT_S_LEAF_C4_PARALLEL_ROOT_LEAF_REDUCTION.md`, this theorem excludes
the complete original domain \(\min(v,w)>1/8\), with arbitrary original
\(C,D\) orientations, contact owners, means and forces. The original
packing has five further units beyond \(A,B,L,M\), not four. No
equation at \(C\) or \(D\), or even their physical mutual edge, is used.

The theorem makes no assertion at \(\min(v,w)\le1/8\), or in the
horizontal genuine-leaf endpoint charts. Those scopes remain separate.
It uses no numerical pose, force deletion, fictitious graph degree,
compilation, remote action or shared-metadata edit.
