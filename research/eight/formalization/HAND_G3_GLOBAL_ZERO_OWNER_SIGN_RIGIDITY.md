# Each original zero owner forces its adjacent transverse sign globally

## 1. The theorem

Assume the G0--G2 boundary-neighbor geometry at squared radius
\(5/2\le q\le Q=9789/2500\), with the common real frame spread less than
\(7/10\). Each center is on its true-core boundary or its actual
outer q boundary. On a zero-quarter edge, write the signed own-frame centers
as \((a,-y)\), \((A,-Y)\), and its actual frame increment as d.
Then
\[
\boxed{
\begin{aligned}
\text{original axis 0 feasible}&\ \Longrightarrow\ y>0,\\
\text{original axis 2 feasible}&\ \Longrightarrow\ Y<0.
\end{aligned}}
\tag{1}
\]
In particular, if both original transverse axes are feasible, both
strict signs hold. The result includes weak SAT contacts, tied owners,
and zero transverse coordinates.

This is a global restriction. It assumes no bound on S, no tangent
cut, no sign normalization on E, and no quarter or mixed owner
restriction. The earlier global zero-primary theorem may be used
separately to say that the only remaining original zero owners are
0 and 2. This note does not assert that both signs follow from just
one of those two owners.

The local quantitative statement is that a putative axis 0 witness
with \(y\le0\) forces
\[
d+\ell_s-\ell_t+\frac9{50}h(|d|)>1,
\qquad h(x)=\frac{\sin x+\cos x-1}{2},
\tag{2}
\]
using the unchanged common G1 marker. The six-edge return path then
contradicts the total angular budget.

## 2. Bounds from the unchanged common marker

Work first on the G0 boundary cycle at Q, with unsigned coordinates
\((a,b)\) and sign \(\sigma\), so \(y=\sigma b\).
The common marker is \(\ell=\sigma F(a,b)\), with the exact C/L/M/H
formulas in
[the global DE proof](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md),
Section 2. That section and the whole-chart proof in
[the zero-primary exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
give
\[
F\ge\frac45b,\qquad
b\le\frac12\ \Longrightarrow\ F\le\frac{111}{100}b.
\tag{3}
\]
These hold on both radial kinds, at the core side/corner junction,
and for either selected marker at an outer-chart junction.
Choose that marker once per vertex and retain it on both incident
edges.

The geometric bounds needed below are
\[
|(a,b)|<U:=\frac{283}{200},\quad
0\le b<\frac9{10},\quad a+b<\frac95,\quad
(a+1/2)^2+(b+1/2)^2\le Q.
\tag{4}
\]
They also hold at original contained centers. On \(0\le x\le7/10\),
\[
\cos x\ge\frac34,\qquad
0\le\sin x\le\frac{13}{20},\qquad
\cos x>\sin x,\qquad
\sqrt Q<\frac{1979}{1000}.
\tag{5}
\]

The original zero-axis projections, with
\(W(d)=(1+\cos d+|\sin d|)/2\), are
\[
P_0=y+A\sin d-Y\cos d,\qquad
P_2=a\sin d+y\cos d-Y.
\tag{6}
\]
Only their original weak inequalities \(P_i\ge W\) will be used.

## 3. A bad source sign forces one positive long increment

Retain an original axis 0 witness and suppose \(y=-b\le0\).
If \(d\le0\), then \(A\sin d\le0\), and
\[
P_0=-b+A\sin d-Y\cos d\le |Y|<9/10<W.
\]
Hence \(d>0\). If \(Y\ge0\), (4)--(5) instead give
\[
P_0\le A\sin d<U\frac{13}{20}
=\frac{3679}{4000}<1\le W,
\]
again impossible. Thus \(Y=-B<0\), and the retained inequality is
\[
-b+A\sin d+B\cos d\ge W.
\tag{7}
\]
In particular
\[
b\le A\sin d+B\cos d-W
   \le |(A,B)|-1<U-1<\frac12.
\tag{8}
\]
Consequently the source marker obeys the upper bound in (3).

Feasibility also forces
\[
\boxed{\frac{29}{100}<d<\frac7{10}.}
\tag{9}
\]
To see this, put \(s=\sin d\), \(c=\cos d\). Since \(A\ge B\)
and \(c>s\),
\[
As+Bc\le\frac{A+B}{2}(s+c)<\frac9{10}(s+c).
\]
Combining this with (7) and \(b\ge0\) yields \(s+c>5/4\).
The function \(\sin d+\cos d\) increases on \([0,7/10]\).
At \(z=29/100\), its alternating Taylor upper bound gives
\[
\begin{aligned}
\sin z+\cos z
&\le1+z-\frac{z^2}{2}-\frac{z^3}{6}
                       +\frac{z^4}{24}+\frac{z^5}{120}\\
&=\frac54-\frac{2321216117}{400000000000}<\frac54.
\end{aligned}
\]
This proves (9) on the whole continuous domain.

## 4. One circle support and one concavity argument

Set \(\lambda=111/100\), \(m=4/5\), and \(\beta=9/50\).
The two signs in (7) mean
\(\ell_s=-F_s\), \(\ell_t=-F_t\). Equations (3), (7), and (8)
give
\[
\begin{aligned}
d+\ell_s-\ell_t+\beta h(d)
&\ge d-\lambda b+mB+\beta h(d)\\
&\ge d+\lambda W+\beta h(d)
                  -\lambda sA-(\lambda c-m)B.
\end{aligned}
\tag{10}
\]
Apply the actual target corner disk from (4) to the force
\((\lambda s,\lambda c-m)\). Its squared norm is
\[
\lambda^2s^2+(\lambda c-m)^2
 =K-Mc,\qquad K=\frac{18721}{10000},\quad M=\frac{222}{125}.
\]
Thus (10) is at least the single scalar
\[
f(d)=d+\frac{13}{200}
       +\frac65(\sin d+\cos d)
       -R\sqrt{K-M\cos d},\qquad R=\sqrt Q.
\tag{11}
\]
There is no radial contact assumption in this circle support.

The function f is strictly concave on \([29/100,7/10]\).
Indeed \(K-M=961/10000>0\), and, for
\(v(d)=\sqrt{K-M\cos d}\),
\[
v''(d)=
\frac{M\bigl(2K\cos d-M(1+\cos^2d)\bigr)}
     {4(K-M\cos d)^{3/2}}>0.
\tag{12}
\]
The numerator factor is increasing as a function of \(c=\cos d\)
on \([3/4,1]\), since \(K>Mc\). Its lower value is
\[
2K\frac34-M\left(1+\frac9{16}\right)
=\frac{663}{20000}>0.
\]
Therefore
\(f''=-(6/5)(\sin d+\cos d)-Rv''<0\).
It remains to check just the two endpoints of this one interval.

At \(d=29/100\), Taylor bounds give
\[
c\ge\frac{191}{200},\qquad s\ge\frac{57}{200},\qquad
\sqrt{K-Mc}<\frac{21}{50}.
\]
The first two reserves are \(59/20000\) and \(5611/6000000\).
The squared-root reserve is
\[
(21/50)^2-K+M(191/200)=\frac{19}{50000}>0.
\]
Using \(R<1979/1000\) in (11),
\[
f(29/100)>
\frac{29}{100}+\frac{13}{200}
+\frac65\left(\frac{191}{200}+\frac{57}{200}\right)
-\frac{1979}{1000}\frac{21}{50}
=1+\frac{591}{50000}>1.
\tag{13}
\]

At \(d=7/10\), the cubic sine lower bound and sixth-degree cosine
lower bound give
\[
c\ge\frac{19}{25},\qquad s\ge\frac{16}{25},\qquad
\sqrt{K-Mc}<\frac{723}{1000}.
\]
The respective trigonometric reserves are
\(3485351/720000000\) and \(17/6000\). The root reserve is
\[
(723/1000)^2-K+M(19/25)=\frac{389}{1000000}>0.
\]
Consequently
\[
f(7/10)>
\frac7{10}+\frac{13}{200}
+\frac65\left(\frac{19}{25}+\frac{16}{25}\right)
-\frac{1979}{1000}\frac{723}{1000}
=1+\frac{14183}{1000000}>1.
\tag{14}
\]
Concavity places the minimum at an endpoint, so (13)--(14) prove
f greater than one throughout (9). This proves (2).

## 5. Transfer the local result to the other original owner

Suppose original axis 2 is feasible with \(Y\ge0\).
In the local calculation exchange the two unsigned states and negate
both transverse signs, while keeping d unchanged:
\[
(a,y),(A,Y)\longmapsto(A,-Y),(a,-y).
\tag{15}
\]
The new source has nonpositive signed transverse coordinate. Its
axis 0 projection is exactly the old axis 2 projection:
\[
-Y+a\sin d+y\cos d=P_2.
\]
The local marker difference is also unchanged:
\[
(-\ell_t)-(-\ell_s)=\ell_s-\ell_t.
\]
The physical gap is unchanged as well, since the signed arctangents
are exchanged and negated. Thus the proof in Sections 3--4 gives
the same boosted bound (2) for the original edge.

This is an identity applied to the retained original inequality; no
alternative owner has been chosen and no new global cycle is needed.

## 6. The common G1 return path excludes either bad sign

For either putative bad sign, use its boosted bound (2) on that
original edge and the actual G1 inequalities on the other six:
\[
\phi_j+\ell_j-\ell_{j+1}-\beta h(|d_j|)>
\frac{8833}{10000}.
\]
The common real frame interval gives
\[
\sum_{j\ne i}h(|d_j|)\ge h(|d_i|).
\]
This follows by applying the metric h of distance along the six-edge
return path: h is increasing and concave with \(h(0)=0\), exactly
as in
[the zero-primary proof](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md),
Section 6. The common marker cancels upon summation, leaving
\[
1+6\frac{8833}{10000}<2\pi.
\]
But
\[
1+6\frac{8833}{10000}-\frac{710}{113}
=\frac{9387}{565000}>0,\qquad 2\pi<\frac{710}{113}.
\]
The contradiction proves both statements in (1).

For a boundary cycle at q<Q, retain the putative offending witness
and apply the unconditional fixed-ray expansion in Section 2 of
[the fixed-ceiling transfer theorem](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md).
It expands each outer center to its Q boundary and fixes each core
center. Every previously feasible signed axis, frame, quarter
increment and signed center ray is preserved, hence so is the
offending weak transverse sign. Choose the common G1 marker on
the resulting Q-boundary cycle and apply the argument above.
For an original packing the recession-direction boundary construction
comes first; these sign conclusions apply to the resulting boundary
states, without a claim that the first construction preserves rays.

The only new scalar calculation is the concavity of (11) on one
entire interval and the two displayed rational endpoint comparisons.
No state cover, angle mesh, generated certificate, Lean compilation,
or CI is part of this proof.
