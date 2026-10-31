# The entire radial S-leaf triangle-plus-leaf branch is impossible

**Status: complete exact hand argument; two separate hand audits passed.**
In the declared radius window

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
                                                               \tag{1}
\]

a positive physical stress component cannot have body graph consisting
of a triangle and one pendant edge when its pendant body is a radial
side-normal leaf of type S. The argument includes every tilted
articulation, every aligned articulation height, and all endpoint and
circle-load degeneracies. It excludes the four-body stressed core
itself, independently of all remaining physical squares.

The radial diagonal-leaf branch D is separate. Thus this theorem does
not by itself close the whole coarse cell C1.3.b1 or the unrestricted
nine-square problem. No Lean compilation or CI is claimed.

## 1. The four-body component and its exact S-leaf geometry

Write the triangle bodies as \(A,B,C\), with the pendant body \(L\)
joined to \(A\). All four graph edges have positive aggregate physical
contact weights and genuine shared application points. Every body and
every remaining physical square is a closed unit square with disjoint
open interiors in the origin-centered disk of radius \(R\).

The bridge and leaf results in `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`
give, after a rotation,

\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 L=[d,d+1]\times[-\tfrac12,\tfrac12],\qquad
 p=(d,0)\in A\cap L.                                    \tag{2}
\]

The bridge normal from \(A\) to \(L\) is \(e_1=(1,0)\), so
\(p\) is a rightmost support point of \(A\). The two positive
circle atoms on \(L\) have equal weights and lie at
\((d+1,\pm1/2)\). If \(\lambda_L>0\) is their total weight, the
circle-load vector of \(L\) is

\[
                         m_L=\lambda_L(d+1)e_1.          \tag{3}
\]

The articulation \(A\) is physically circle-clear by the central
endpoint theorem for a radial bridge. Both \(B\) and \(C\) carry
positive circle weight. For completeness, if one of them were
unloaded, its two positive contact forces would be equal and opposite.
It would transmit them between opposite support faces. The other two
triangle bodies would then lie on opposite sides of a projection gap
equal to that square's strictly positive width, and could not touch
each other. This contradicts the third triangle edge. This is the
same degree-two transmission argument used in
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`.

It is essential to keep the full aligned articulation family. If
\(A\) is aligned with the coordinate axes, then

\[
 A=[d-1,d]\times[t-\tfrac12,t+\tfrac12],\qquad
                         -\tfrac12\le t\le\tfrac12.      \tag{4}
\]

If it is not aligned, \(p\) is its unique rightmost vertex.
After reflection across the horizontal axis if necessary, its inward
side vectors from \(p\) can be written

\[
 (-a,-b),\quad(-b,a),\qquad
       a\ge b>0,\quad a^2+b^2=1.                         \tag{5}
\]

Its vertices are therefore

\[
 (d,0),\quad(d-a,-b),\quad(d-b,a),\quad(d-a-b,a-b).       \tag{6}
\]

For the aligned case make the same horizontal reflection to arrange
\(t\ge0\). These reflections preserve the S leaf, the containing
circle, and every physical force-and-torque equation. Both full cases
now have the following two common properties:

\[
 p\in A,\qquad |x-p|\le\sqrt2\quad(x\in A),             \tag{7}
\]

\[
                    x_1+x_2\ge d-\frac32\quad(x\in A).   \tag{8}
\]

For (4), the minimum in (8) is \(d+t-3/2\). For (6), the
four coordinate sums are \(d,d-a-b,d+a-b,d-2b\). Their
minimum is \(d-a-b\ge d-\sqrt2>d-3/2\). Thus (8)
does not assume that the origin belongs to \(A\), nor any restriction
on its aligned height beyond (4).

## 2. Two exact radius estimates

The lower endpoint in (1) implies

\[
                           d>\frac{91}{100}.             \tag{9}
\]

Indeed,

\[
 \left(\frac{79}{40}\right)^2-\frac14
       -\left(\frac{191}{100}\right)^2
                         =\frac{101}{40000}>0.
\]

Two further strict estimates will be used:

\[
       R^2+d^2+2Rd\frac7{\sqrt{58}}>8,                  \tag{10}
\]

\[
                    R\frac{10}{\sqrt{58}}+d>\frac72.     \tag{11}
\]

To prove (10), first note that \(7/\sqrt{58}>11/12\), since
\(84^2=7056>121\cdot58=7018\). All factors are positive,
so (1) and (9) give

\[
\begin{aligned}
 R^2+d^2+2Rd\frac7{\sqrt{58}}-8
 &>\left(\frac{79}{40}\right)^2
   +\left(\frac{91}{100}\right)^2
   +2\frac{79}{40}\frac{91}{100}\frac{11}{12}-8\\
 &=\frac{1421}{60000}>0.
\end{aligned}                                                   \tag{12}
\]

For (11), use \(\sqrt{58}<61/8\), because
\(58\cdot64=3712<3721=61^2\). Then

\[
 R\frac{10}{\sqrt{58}}+d
 >\frac{79}{40}\frac{80}{61}+\frac{91}{100}
 =\frac72+\frac1{6100}>\frac72.                         \tag{13}
\]

Only the declared lower radius bound has been used in this section.

## 3. A closed 90-degree circle arc is inaccessible to every neighbor of A

Let \(\vartheta\in(0,\pi/4)\) be determined by

\[
 \cos\vartheta=\frac7{\sqrt{58}},\qquad
 \sin\vartheta=\frac3{\sqrt{58}}.                       \tag{14}
\]

Consider the closed circle arc \(\mathcal I\) with angular interval

\[
                 [\pi-\vartheta,\;3\pi/2-\vartheta].    \tag{15}
\]

Its endpoint directions are \((-7,3)/\sqrt{58}\) and
\((-3,-7)/\sqrt{58}\). Its length is exactly \(\pi/2\),
and the negative horizontal direction lies strictly inside it.

**Lemma 3.1.** If a unit square \(T\) physically touches \(A\),
no point of \(T\) on the containing circle belongs to
\(\mathcal I\).

*Proof.* Choose a genuine shared point \(r\in A\cap T\),
and suppose that \(z\in T\), \(|z|=R\), belongs to the
arc. Split (15) into two closed subarcs, retaining their common
endpoint.

On the central subarc

\[
                       \arg z\in[\pi-\vartheta,\pi+\vartheta],
\]

we have \(z_1\le-7R/\sqrt{58}\). Therefore (10) gives

\[
 |z-p|^2=R^2+d^2-2dz_1
       \ge R^2+d^2+2Rd\frac7{\sqrt{58}}>8.
\]

On the other hand, the two unit-square diameters and (7) give
\(|z-p|\le|z-r|+|r-p|\le2\sqrt2\), a contradiction.

On the lower subarc

\[
                  \arg z\in[\pi+\vartheta,3\pi/2-\vartheta],
\]

write \(z=-R(\cos\gamma,\sin\gamma)\), where
\(\vartheta\le\gamma\le\pi/2-\vartheta\). The elementary
identity \(\cos\gamma+\sin\gamma
=\sqrt2\cos(\gamma-\pi/4)\) gives

\[
                \cos\gamma+\sin\gamma\ge\frac{10}{\sqrt{58}}.
\]

By (8) and (11),

\[
\begin{aligned}
 (r-z)\mathbin{\cdot}(1,1)
 &\ge d-\frac32+R\frac{10}{\sqrt{58}}\\
 &>2.
\end{aligned}
\]

Cauchy--Schwarz therefore gives \(|r-z|>\sqrt2\), again
contradicting that \(r,z\) lie in the same unit square \(T\).
Both subarcs are excluded, including all their endpoints. \(\square\)

This lemma applies to every physical neighbor of \(A\), independent
of whether a chosen contact or circle atom has positive weight.

## 4. The two triangle loads cannot balance the S leaf

Let \(\mathcal Z\) consist of all circle vertices of \(B\) and
\(C\) that carry positive circle weight. There are finitely many,
and every associated weight is strictly positive. Any two vectors
\(z,w\in\mathcal Z\) have

\[
                              z\mathbin{\cdot}w>0.       \tag{16}
\]

For vertices in different bodies this is the touching-boundary
acuteness theorem `ACUTE_LOADED_CONTACT_GRAPH.md`, since \(B\)
and \(C\) physically touch and the lower radius in (1) satisfies
\(R^2>2+\sqrt3\). For vertices in one body,
\(|z-w|\le\sqrt2\) and \(|z|=|w|=R\), so
\(z\cdot w=R^2-|z-w|^2/2\ge R^2-1>0\). Thus (16)
also covers two-circle-corner bodies and every positive-weight split.

Summing the four body force equations cancels all physical pair
forces at their common contact points. Because \(A\) has no circle
weight, (3) yields

\[
           M:=\sum_{z\in\mathcal Z}\lambda_z z
              =m_B+m_C=-\lambda_L(d+1)e_1.              \tag{17}
\]

For every \(z\in\mathcal Z\), (16) gives
\(z\cdot M>0\). Since the right side of (17) is a nonzero
negative horizontal vector, it follows that \(z_1<0\).
All these circle directions therefore lie in the open left
semicircle \((\pi/2,3\pi/2)\).

Every such vertex belongs to a square touching \(A\), so Lemma 3.1
excludes (15). Consequently each positive circle vertex has direction
in one of the two open intervals

\[
 (\pi/2,\pi-\vartheta)
 \quad\text{or}\quad
 (3\pi/2-\vartheta,3\pi/2).                            \tag{18}
\]

The first interval has positive vertical coordinate and the second
negative vertical coordinate. The vertical component of (17) is zero,
so both intervals must contain a positively weighted vertex. Choose
one from each. Their angular separation is strictly between
\(\pi/2\) and \(\pi\), because the two endpoints separating the
intervals differ by exactly \(\pi/2\). Their dot product is
therefore negative, contradicting (16).

**Theorem 4.1.** The entire radial S-leaf branch of a positive
triangle-plus-leaf component is impossible throughout (1). This
includes the aligned family \(|t|\le1/2\), both reflected tilted
families, vertex/side and shared-side degeneracies, and arbitrary
positive circle-corner weights on the other two loaded bodies.

The proof uses the exact bridge/leaf geometry and the full component
force balance. No nonbridge force was assumed radial, no common frame
was imposed on \(B,C\) or on the remaining squares, and no additional
square was discarded in a capacity argument: the stressed four-body
core itself cannot occur.

## 5. Remaining obligation in C1.3.b1

After this theorem, only the radial D-leaf branch remains for the
four-body triangle-plus-leaf coarse cell. Its articulation and two
loaded neighbors must still be handled with every permitted physical
contact type and every remaining square. The present forbidden-arc
estimate depends on the S-leaf radius \(d\) in (2); it is not asserted
for a D leaf, whose contact radius is \(R-\sqrt2\).
