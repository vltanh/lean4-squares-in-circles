# Tilted root-side direct contact: a whole long-pocket comparison at large mean

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_TILTED_LARGE_MEAN_LONG_RECOVERY_BLOCK_2026_10_26.md. This manuscript was absent after restoration. The
argument below is rederived from the unchanged actual geometry; no earlier
PASS is assigned to this present text.

Retain the original S-leaf C5 component A--B--V--C--U--A with genuine leaf L
at the true degree-three root A, all nine physical squares, every original
force, normal, application mean, radial weight and both transmitter sliders.
This source treats the tilted root, actual direct normal \(m=f_2\), and
strict channel \(t>0\). Its first theorem covers the entire original
direct-mean range \(Z\ge1/4\). Section 8 records an exact geometric
criterion on the complementary range, without asserting it always holds.

## 1. Original chart and the actual bounded outer region

Use S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md and
S_LEAF_C5_TILTED_DIRECT_AND_CHANNEL_HALFPLANES.md. Their unchanged chart is
\[
\begin{gathered}
d=1+\delta,\quad0<\delta<1/60,\quad
R^2=(d+1)^2+1/4\le1105/256,\\
p_0=(d,0),\quad L=[d,d+1]\times[-1/2,1/2],\\
f_1=(-a,-b),\quad f_2=(-b,a),\quad
a^2+b^2=1,\quad a>59/61,\quad0<b<16/61,\\
A=p_0+[0,1]f_1+[0,1]f_2,\qquad P=p_{AU}=p_0+f_1,\\
n=x f_1-t f_2,\quad f=t f_1+x f_2,\quad
x,t>0,\quad x^2+t^2=1,\\
C=[d,d+1]n+[-1/2,1/2]f,\qquad
P+n=dn-Tf,\quad0<T<13/50.
\end{gathered}
\tag{1}
\]
Both actual global components of n are negative. The original root-side
mean and its full unchanged relation are
\[
p_{AB}=p_0+Zf_1+f_2,\qquad
Z=\frac{at}{bx+at}\in(0,1).
\tag{2}
\]
Thus \(Z\ge1/4\) is exactly \(3at\ge bx\). No mean is replaced.

Set \(e_0=-f_1=(a,b)\), \(A_0=db\), \(E_0=da-1\).
In the orthonormal frame \(e_0,f_2\),
\[
P=E_0e_0-A_0f_2,\quad
n=-xe_0-tf_2,\quad f=-te_0+xf_2,
\]
and the original radial-channel equation gives
\[
\delta=-E_0x+A_0t,\qquad
T=A_0x+E_0t,\qquad Tx=db-\delta t.
\tag{3}
\]

The actual occupied lower crosscut, in its original order, is
\[
\begin{split}
z_C=(d+1)n-f/2,\quad dn-f/2,\quad
dn-Tf=P+n,\quad P,\quad p_0,\\
(d,-1/2),\quad z_L=(d+1,-1/2).
\end{split}
\tag{4}
\]
Its consecutive segments lie in C, U, A and L. In particular \(P\to p_0\)
is the actual root side; no direct-contact mean is substituted for it.
The original contact embedding puts the actual C--L outer pocket inside
the bounded side \(\Omega\) of this path and its southern outer circle
arc. B lies on the other side of A's actual direct supporting line,
so it cannot change the selected C--L side. Additional contacts can
subdivide this containing side and cannot enlarge it.

For clarity, write \(a=\cos\phi,b=\sin\phi\) and
\(x=\cos\psi,t=\sin\psi\). The strict west/down direction gives
\(0<\theta:=\phi+\psi<\pi/2\).
With \(\gamma=\arctan(1/[2(d+1)])\), the selected circle arc has angles
\[
\pi+\theta+\gamma\ \le\vartheta\le\ 2\pi-\gamma.
\tag{5}
\]
It has length less than \(\pi\) and lies wholly below the horizontal axis.

Every point of \(\Omega\) satisfies
\[
f_2\cdot(z-P)\le0,\qquad f\cdot(z-P)\le0.
\tag{6}
\]
Here the path vertices can be checked directly: \(p_0-P=e_0\),
\(f\cdot(p_0-P)=-t\), \(f_2\cdot n=-t\), and the C inner-face
segment adds a nonpositive multiple of f since \(T<1/2\).
The leaf's lower and outward segments also decrease both projections.
Neither normal direction occurs in the southern arc (5); its projection
maximum is at an endpoint. Hence the arc and the whole bounded side
satisfy (6). Equivalently, the purely geometric identity
\(d(bx+at)-T=t>0\) proves the required strict leaf-side f projection.
No force magnitude is used in this half-plane calculation.

## 2. One common translation and its uniform bounds

Define
\[
\varepsilon=
\max\left\{0,\,Tx-t+\frac{1-x}{2}\right\}
=\max\left\{0,\,db-dt+\frac{1-x}{2}\right\},
\qquad P'=P+\varepsilon f_2.
\tag{7}
\]
This is one common translation for every extra. Since
\((1-x)/2=t^2/[2(1+x)]<t/2\), always
\[
0\le\varepsilon\le db<4/15.
\tag{8}
\]
If \(\varepsilon>0\), then \(t<1/3\). Indeed
\(F(t)=t-(1-\sqrt{1-t^2})/2\) is concave on \([1/3,1]\);
its two endpoint values exceed \(4/15\). At \(1/3\), this uses
\(\sqrt2>13/10\), with squared reserve \(31/100\).
But (7) would require \(F(t)<db<4/15\).

Now assume the whole large-mean condition \(3at\ge bx\).
Put
\[
t_0=\frac b{\sqrt{9a^2+b^2}},\qquad
b/3\le t_0\le b/(3a).
\]
Then \(t\ge t_0\). On the only relevant positive-\(\varepsilon\) interval
\(t<1/3\), the expression inside the maximum in (7) decreases with t.
Using \(1-\sqrt{1-t_0^2}\le t_0^2\) gives
\[
\varepsilon\le\frac23db+\frac{b^2}{18a^2}
<b\left(\frac{61}{90}+\frac{976}{62658}\right)
<\frac7{10}b<\frac15.
\tag{9}
\]
The last coefficient comparison has exact reserve \(347/52215\).
The zero-\(\varepsilon\) case satisfies (9) directly.

## 3. Both exact outer endpoint reserves are positive

Put \(R_0=\sqrt{17}/2\). Direct expansion in the actual orthonormal
frames gives
\[
\begin{split}
R_0^2-|z_L-P'|^2
&=2(1-a)+b-(a+2b)\varepsilon-\varepsilon^2
=:\mathcal L,\\
R_0^2-|z_C-P'|^2
&=T-T^2-[\,4t+(1-2T)x\,]\varepsilon-\varepsilon^2
=:\mathcal C.
\end{split}
\tag{10}
\]
For the C identity, \(z_C-P=2n+(T-1/2)f\) and
\(f_2=-tn+xf\). Thus no unused root equation or numerical
approximation enters either expansion.

Write \(\kappa=1-a\), so \(b^2=\kappa(1+a)\).
Equation (9) gives
\[
\begin{split}
\mathcal L
&>2\kappa+b(1-7a/10)-\frac{189}{100}b^2\\
&\ge\frac3{10}b-\frac{89}{50}\kappa\\
&>b\left(\frac3{10}-\frac{89\cdot61}{50\cdot120}b\right)
>\frac{47}{750}b>0.
\end{split}
\tag{11}
\]
Here \(1+a>120/61\) and \(b<16/61\).

If \(\varepsilon=0\), then \(\mathcal C=T(1-T)>0\).
Otherwise put \(w=T-1/2\). Substitution of
\(\varepsilon=wx-t+1/2\) into (10), using \(x^2+t^2=1\), gives
the exact factorization
\[
\mathcal C=t\{(3-w^2)t-1-4wx\}.
\tag{12}
\]
The same original large-mean condition gives
\[
T=dbx+(da-1)t\le(4da-1)t<\frac{46}{15}t.
\]
Since \(0<T<13/50\), \(t<1/3\), and \(1+x>3/2\), the brace in (12)
is greater than
\[
\begin{split}
\frac{11}{4}t+1-4T-\frac{2t^2}{1+x}
&>1-\frac{571}{184}T-\frac4{27}\\
&>1-\frac{571}{184}\frac{13}{50}-\frac4{27}
=\frac{11179}{248400}>0.
\end{split}
\tag{13}
\]
Thus both actual endpoint reserves are strictly positive on the
entire original \(Z\ge1/4\) interval, including \(Z=1/4\).

## 4. The whole containing region enters the strict smaller disk

Under (9), the global vertical component of the translation center is
\[
(P')_y=-b+a\varepsilon<0.
\]
The opposite vector \(-P'\) is above the horizontal axis, outside the
southern arc (5). The linear projection \(P'\cdot z\) therefore has
its minimum on that arc at an endpoint. Since \(|z|=R\), (10)--(13)
put the whole arc strictly in the disk centered at P' of radius \(R_0\).

The remaining path vertices also lie strictly in that disk.
The P, \(P+n\), and \(p_0\) distances are at most
\[
\varepsilon,\qquad 1+\varepsilon,\qquad \sqrt{1+\varepsilon^2},
\]
respectively, all less than \(R_0\). Each C or L inner-face endpoint
has smaller squared distance than its corresponding outer endpoint:
the actual positive radial coordinates differ by one. Convexity puts
every segment of (4) in the strict disk.

The bounded side is contained in the convex hull of its compact
boundary, so the whole \(\Omega\) lies in the strict disk.
Every entire extra E in this original pocket consequently satisfies
\[
E-P'\subset\operatorname{int}D_{R_0},\qquad
f_2\cdot(E-P')\le-\varepsilon,\qquad
f\cdot(E-P')\le-\varepsilon x.
\tag{14}
\]
All extras use the same rigid translation; their mutual disjointness
and orientations remain.

## 5. Exact outer-face screen for each physical radial terminal

The outer-face argument of RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1, applies at the present d as follows.
Every unit-square center has norm at most \(d+1/2\), since
\[
R^2\ge |c_E|^2+|c_E|+1/2,\qquad
R^2=(d+1/2)^2+(d+1/2)+1/2.
\]
If a disjoint unit had a point beyond the actual radial outer face
\(n_0\cdot z=d+1\), the segment from its center would cross that
face inside its transverse interval \((-1/2,1/2)\), entering the
radial terminal interior. Equality away from the two outer vertices
has the same contradiction. Two disjoint contained unit squares
cannot share an outer circle point: their inward right-angle tangent
cones would otherwise require a positive tangent edge in the disk.

Thus every actual extra disjoint from L,C has, at every point,
\[
e_x\cdot z<d+1,\qquad n\cdot z<d+1.
\tag{15}
\]
This uses the physical terminals, with no hypothesis on their
individual circle-weight split.

## 6. The same translated extra avoids both canonical terminals

Work in the frame \(e_0,f_2\), and define the comparison terminals
\[
S_+=[1,2]e_0+[-1/2,1/2]f_2,\qquad S_-=-S_+.
\]

Suppose an interior point of the fixed translated extra \(E-P'\)
lies in \(S_+^\circ\), with coordinates \((X,Y)\).
Then \(1<X<2\), \(|Y|<1/2\), and \(Y\le-\varepsilon\) by (14).
The corresponding original point, relative to \(p_0\), has global
coordinates
\[
a(X-1)-b(Y+\varepsilon),\qquad
b(X-1)+a(Y+\varepsilon).
\]
The first is positive; the second lies strictly between \(-1/2\)
and \(1/2\), since \(Y+\varepsilon\le0\), \(a\le1\), and \(b<1/2\).
Equation (15) makes the first coordinate less than one.
The original point would lie in \(L^\circ\), a contradiction.

For a hypothetical intersection with \(S_-^\circ\), use its coordinates
\((X_C,Y_C)\) in the actual frame n,f. Membership in \(S_-^\circ\) gives
\[
xX_C+tY_C>1,\qquad
-\frac12<-tX_C+xY_C<\frac12.
\]
Equation (14) gives \(Y_C\le-\varepsilon x\), so
\[
X_C>\frac1x+\varepsilon t>1+\varepsilon t.
\tag{16}
\]
The lower transverse inequality, followed by (16), gives
\[
Y_C>\frac{t+\varepsilon t^2-1/2}{x}
\ge T-\varepsilon x-\frac12,
\tag{17}
\]
where the last comparison is precisely
\(\varepsilon\ge Tx-t+(1-x)/2\), as in (7).
The upper transverse bound follows directly from
\(Y_C\le-\varepsilon x<T-\varepsilon x+1/2\).
In these translated coordinates the actual C is
\[
[1+\varepsilon t,2+\varepsilon t]n+
[T-\varepsilon x-1/2,T-\varepsilon x+1/2]f.
\]
Equation (15) supplies \(X_C<2+\varepsilon t\).
Thus the original point would lie in \(C^\circ\), again impossible.

This comparison does not move a terminal or an extra separately.
It proves that the same translated extras avoid both canonical
comparison terminals.

## 7. Whole long-pocket capacity

Reflect the \(f_2\) coordinate in (14). Every translated extra is a
whole unit in the closed upper half-plane, strictly inside \(D_{R_0}\),
and avoids the two opposite canonical radial terminals.
If three such extras existed, HALF_POCKET_TRIPLE_RIGIDITY.md,
Theorem HALF.3, would make them the exact canonical triple.
That triple has actual vertices on \(\partial D_{R_0}\), contrary
to the strict containment in (14).

Therefore the entire original long pocket has
\[
\boxed{n_{CL}\le2\qquad\text{for all original }Z\ge1/4.}
\]
All actual root means, physical C weights and U,V sliders are retained.
The theorem is a whole-pocket capacity bound, not a sampled core
calculation or a replacement packing.

## 8. Exact full-parameter criterion outside the large-mean range

For any original \(0<Z<1\), keep exactly the epsilon (7) and the two
polynomials \(\mathcal L,\mathcal C\) in (10).
If
\[
\mathcal L>0,\qquad\mathcal C>0,
\tag{18}
\]
the same complete comparison proves \(n_{CL}\le2\).
No assertion is made that (18) holds throughout \(Z<1/4\).

For completeness, the whole-disk step still works without (9).
Bounds (8) give \(\varepsilon<4/15\), so all three nonterminal
vertex distances used in Section 4 remain less than \(R_0\).
Also \((P')_y<0\) on this complete epsilon domain.
It is immediate if \(\varepsilon=0\).
Otherwise \(t<1/3\) and \(x>9/10\), as proved in Section 2.
From \(\delta=-E_0x+dbt>0\), one obtains
\[
\begin{split}
(P')_y
&=bE_0-ad t+\frac a2(1-x)\\
&<t\left(\frac{db^2}{x}-ad+\frac{at}{2(1+x)}\right)<0.
\end{split}
\]
Indeed the first positive term is less than \(1/10\), the last less
than \(1/6\), and \(ad>9/10\). Thus the southern-arc projection argument
remains valid. The screens in Sections 5--6 used only (7)--(8) and
the exact half-planes, not the large-mean restriction.

This criterion preserves all original continuous parameters. It
introduces no interval packet, numerical sign, force deletion or
new normal, and does not close any exterior allocation until (18)
has been proved on its actual stated domain.

