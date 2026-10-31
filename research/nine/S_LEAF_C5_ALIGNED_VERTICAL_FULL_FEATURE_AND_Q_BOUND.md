# Complete aligned vertical B feature cover and a common concurrence interval

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_ALIGNED_VERTICAL_FEATURE_AND_CENTRAL_CERTIFICATE_REDUCTION_RECOVERY_2026_10_26.md. This is not an attestation
that the missing older feature source has been restored identically.

Keep the original S-leaf C5 component A--B--V--C--U--A, genuine radial leaf L,
true root degree three, true degrees two at B,C,U,V, all actual forces,
normals, means, individual physical corner weights, sliders and all nine
squares. This source treats the entire aligned root with its original
vertical direct normal \(m=(0,-1)\).

## 1. Original full chart and loaded properness

The accepted aligned far-endpoint theorem gives
\[
\begin{gathered}
d=1+\delta,\quad0<\delta<1/60,\quad R^2=(d+1)^2+1/4\le1105/256,\\
A=[\delta,d]\times[-b,a],\quad a+b=1,\quad
0<a<11/60,\quad b>49/60,\\
n=(-c,s),\quad f=(-s,-c),\quad c,s>0,\quad c^2+s^2=1,\\
q_A=(q,0),\quad0<q\le d,\quad
a=qs,\quad\delta=q(1-c),\quad a^2=2\delta q-\delta^2,\\
F=p_{AB}=(q,-b),\quad P=p_{AU}=(\delta,a),\quad
P+n=dn-af,\\
C=[d,d+1]n+[-1/2,1/2]f,\quad
Q=p_{CV}=dn+f/2,\quad G=p_{BV}=Q+g,\\
g=-\alpha n+\beta f=(u,-v),\quad
\alpha,\beta>0,\quad \alpha^2+\beta^2=u^2+v^2=1.
\end{gathered}
\tag{1}
\]
The return signs are those of the original common moment in the radial
side-channel cover; no return endpoint is selected anew.

The B pair cannot be parallel. The local classification and boundary-channel
exit in SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md, Sections 1 and 2.2,
apply to its actual reserve-one connection to the physical boundary C.
This local use does not assign simple-cycle degree to A.
Thus the true degree-two proper-concurrence lemma applies to B.
Its concurrence lies on the original vertical line \(X=q>0\) and is
a positive multiple of the original circle resultant. The actual return
force therefore has \(u>0\); also \(v=\alpha s+\beta c>0\).

There are exactly two actual direct features: a horizontal top face of B,
with its full mean, or a strict top vertex. The following sections exhaust
both and prove the common final interval
\[
\boxed{\frac15<q<\frac34.}
\tag{2}
\]

## 2. Entire horizontal-top mean feature

If B owns the vertical direct axis, write
\[
B=[K-1,K]\times[-b-1,-b],\qquad F=(q,-b).
\tag{3}
\]
The positive circle resultant has positive horizontal component.
The actual unique circle corner is consequently \((K,-b-1)\), with
\(K>1/2\). A physical radial axis-aligned B would have its inner top
face at \(-d\), requiring \(b=d>1\), or would have its top face at
a positive height; these are impossible. Thus this entire feature is
physical unique.

Since \(u,v>0\), the actual return support is the strict upper-left vertex
\[
G=(K-1,-b),\qquad
u=K-1+dc+s/2,\quad v=b+ds-c/2.
\tag{4}
\]
Put \(\zeta=q+1-K\in[0,1]\), its actual top-face mean coordinate.
Both proper descriptions of the original concurrence give
\[
q(b+1)=K\left(b+\zeta\frac vu\right).
\tag{5}
\]
In particular
\[
q>\frac{b}{2(b+1)}>\frac{49}{218}>\frac15.
\tag{6}
\]
Since \(q>49/218>5\delta/2\), equation (1) gives \(a>2\delta\), and
\[
dc+s/2>c+s/2=1+\frac{a/2-\delta}{q}>1.
\]
Thus \(K<u<1\), and \(\zeta>q>0\). Writing \(r=v/u\), the exact
rearrangement of (5) is
\[
\zeta K(1-r)=(1-\zeta)(b+1-K)\ge0,
\]
so \(0<r\le1\). This includes both \(\zeta=1\) and \(u=v\).

If \(q\ge3/4\), then \(c=1-\delta/q>44/45\), hence
\(K=u+1-dc-s/2<u+1/45\).
Using (5), \(\zeta\le1\), \(b<1\), and \(r\le1\), one gets
\[
\frac qK\le\frac{b+r}{b+1}\le\frac{1+r}{2}.
\]
Consequently
\[
q<\frac{u+v}{2}+\frac{1+r}{90}
\le\frac1{\sqrt2}+\frac1{45}
<\frac{17}{24}+\frac1{45}
=\frac{263}{360}<\frac34.
\tag{7}
\]
The assumed closed tail is impossible. This proves (2) on the whole
horizontal-top feature, keeping the original mean endpoints.

## 3. Strict top vertex: complete return and circle cover

Write its actual sides as
\[
e=(k,-l),\quad w=(-l,-k),\quad
k,l>0,\quad k^2+l^2=1,\qquad B=F+[0,1]e+[0,1]w.
\tag{8}
\]
An equality endpoint of k or l belongs to the preceding actual axis
feature and is not discarded.

Since \(g\cdot e=uk+vl>0\), the full return support is F, the side
\(F+[0,1]w\), or \(F+w\). Put
\[
X=q+dc+s/2,\qquad Y=b+ds-c/2>b-1/2>6/25.
\tag{9}
\]
The direct F is inside the circle, since \(|F|^2\le d^2+1<R^2\).
The left adjacent corner F+w cannot be a circle point: adding e
strictly increases its squared norm by \(2(qk+bl)+1>0\).
The only unique circle alternatives are therefore F+e and F+e+w.
For a physical radial B, an outward axis w would give
\(F=dw-e/2\) with negative horizontal coordinate. Its only possible
radial mask is the right face:
\[
F=de-w/2,\qquad\text{actual circle corners }F+e,\ F+e+w.
\tag{10}
\]
Both individual radial weights remain.

The coincident return \(G=F\) is impossible. Proper concurrence would
make F a positive multiple of its circle resultant. For \(z=F+e\)
this gives \(F\cdot w=0\), putting z+w outside the disk. For
\(z=F+e+w\), it gives
\[
|F|=R-\sqrt2<217/320<37/50<b\le|F|.
\]
For the radial face (10), it would require the resultant parameter
\(\omega=-(d+1)/(2d)<-1/2\) in
\((d+1)e+\omega w\), whereas the complete original nonnegative
weight interval is \(|\omega|\le1/2\).

The remaining actual return is
\[
G=F+\zeta w,\quad0<\zeta\le1,\qquad
u=X-\zeta l,\quad v=Y+\zeta k.
\tag{11}
\]
For \(g\cdot w<0\), it is strict and \(\zeta=1\). Otherwise
\(g=e\), and \(\zeta\) is the unchanged original owned-side mean.

## 4. The whole unique opposite-circle feature is impossible

Suppose \(z=F+e+w\). Put \(A_*=z\cdot e>1/2\),
\(B_*=z\cdot w>1/2\), and \(q_B=\tau z\), \(\tau>0\).
The original proper lines give
\[
q_B=F+\sigma(0,-1)=F+\sigma(le+kw),\quad\sigma\ge0,
\qquad q_B=G+\frac{\zeta l}{u}g.
\]
The w coordinate first gives \(\tau\le1\). Equality would force
\(\zeta=1,g=e,k=l\), while (11) gives \(l=Y+k>k\).
Hence
\[
\tau<1,\quad k>l,\qquad
(1-\tau)(A_*-B_*)=\sigma(k-l)\ge0,\quad A_*\ge B_*.
\tag{12}
\]
No prior inside-B concurrence premise is used.

For a strict return, \(v=Y+k<1\) gives \(k<1/2+a<19/25\).
Together with \(k>l\), it implies \(k>7/10\), \(l>16/25\).
The actual circle corner would have vertical magnitude
\[
b+k+l>37/50+7/10+16/25=52/25>133/64>R,
\]
a contradiction.

For an owned return \(g=e\), its actual C-frame components satisfy
\(\alpha=ck+sl>k\), \(\beta=cl-sk\le l\).
The first strict comparison follows from
\(\beta>0\Rightarrow s/c<l/k\) and
\(\alpha-k=s(l-ks/(1+c))>0\).
Since \(G=Q+e\), the actual circle coordinate is
\[
A_*=2-d\alpha+\beta/2
<2-k+l/2\le2-\frac1{2\sqrt2}<\frac53.
\]
On \(A_*\ge B_*\), the function
\[
f(A,S)=(A-1)^2+(\sqrt{S-A^2}-1)^2
\]
is nondecreasing in A. Increasing A to 5/3 and then S to
\(15541/3600\) stays in \(S-A^2\ge53/36>1\), where its S
derivative is positive. Thus
\[
|F|^2=f(A_*,R^2)<\frac{73}{144}<(37/50)^2<b^2\le|F|^2.
\tag{13}
\]
The fixed comparisons and derivative signs are also explicitly proved
in the freshly reconstructed all-mean tilted top-feature source;
the present equations verify their independent aligned premises.
This excludes every owned opposite mean, including its endpoint.

## 5. The right circle face forces a strict actual return

The only remaining physical masks are the unique \(z=F+e\) and
the radial face (10). Comparison with z+w gives
\[
ql-bk\ge\frac12,\qquad q>\frac12.
\tag{14}
\]
It is strict in the unique mask; the weak radial equality suffices.
Thus
\[
c>29/30>19/20,\qquad s<3/10.
\tag{15}
\]
If the actual return were owned, \(g=e\) and (11) would require
\(X=k+\zeta l\le\sqrt2\), while
\(X>q+c>22/15>\sqrt2\), with squared reserve \(34/225\).
Therefore the whole remaining return is
\[
\boxed{G=F+w,\qquad ul>vk.}
\tag{16}
\]
No genuine owner endpoint has been relabelled; its entire actual
interval was excluded first.

The right circle's e coordinate is at most d+1, since its absolute
transverse coordinate is at least one half. Consequently
\[
q^2+b^2=R^2-2z\cdot e+1\ge d^2+1/4.
\tag{17}
\]
Again the physical radial equality and all its weights remain.

For the unique mask, the complete present chart (1),(8),(16)
is exactly the original-domain premise of
S_LEAF_C5_VERTICAL_UNIQUE_TOP_VERTEX_CONCURRENCE_BOUND.md.
Its freshly rederived physical residual identity proves \(q<3/4\).
The remaining radial mask is handled separately below.

## 6. A short whole-mask radial bound

Represent the plane by complex numbers in the original global frame.
The two actual radial inner vertices are
\[
Q=(d+i/2)n,\qquad G=(d-i/2)e.
\]
Their common norm is \(\sqrt{d^2+1/4}\), and their actual distance
is one. The elementary two-circle chord identity therefore gives
\[
\frac en=1\quad\hbox{or}\quad
\frac en=\left(\frac{d+i/2}{d-i/2}\right)^2.
\tag{18}
\]
The first alternative makes the two entire radial squares B,C coincide,
contrary to their physical interior-disjointness. Keep the second.

Put \(\theta=4\arctan(1/(2d))\), \(C_0=-\cos\theta>0\),
\(S_0=\sin\theta>0\). Define
\[
Q_0=dC_0+\frac12S_0,\qquad B_0=dS_0-\frac12C_0.
\]
The actual coordinates of F then give, with no weight equation,
\[
q=cQ_0-sB_0,\qquad b=cB_0+sQ_0,\qquad
s(q+Q_0)=1-cB_0.
\tag{19}
\]
For complete exact bounds, write \(y=d^2\), so \(1<y<21/20\).
Direct half-angle expansion gives
\[
Q_0=\frac{d(-16y^2+40y-5)}{(4y+1)^2},\qquad
B_0=\frac{40y^2-20y+1/2}{(4y+1)^2}.
\tag{20}
\]
They are positive on this interval. Differentiating Q0 with respect to d
gives numerator
\(-64y^3-240y^2+180y-5\) over \((4y+1)^3\).
The numerator is negative at y=1 and strictly decreases for y≥1.
Differentiating B0 with respect to y gives
\((160y-24)/(4y+1)^3>0\). Hence
\[
0<Q_0<19/25<4/5,\qquad B_0>41/50>4/5.
\]
Finally
\[
\frac78(4y+1)^2-(40y^2-20y+1/2)
=-26y^2+27y+3/8>\frac3{50}>0,
\]
because it decreases on \([1,21/20]\) and equals 3/50 at 21/20.
Thus \(B_0<7/8\).

Since \(q\le d<61/60\), (19) now gives
\[
s(q+Q_0)=1-cB_0>1/8,\qquad
q+Q_0<61/60+4/5=109/60<15/8,
\]
so \(s>1/15\). Substituting in the first equation (19) proves
\[
q<\frac45-\frac1{15}\frac45=\frac{56}{75}<\frac34.
\tag{21}
\]
Every individual radial weight, including zero endpoints, was retained.

## 7. Exact recovered cover and scope

The full aligned vertical family has exactly these original rows:

| Actual direct feature of B | Physical circle feature | Actual return |
|---|---|---|
| Horizontal top side, full genuine mean | Unique lower-right corner | Strict upper-left vertex |
| Strict top vertex | Unique right-adjacent corner | Strict left-adjacent vertex |
| Strict top vertex | Physical radial right face | Strict left-adjacent vertex |

All satisfy (2). In the last two rows, (14)--(17) hold on the whole
original domain. Their means and radial weights were neither discarded
nor replaced by another contact label. The unique q-tail theorem is
used only in its exact original unique chart.

This result supplies physical prerequisites for central and exterior
capacity theorems. It does not itself exclude a completion or tick the
original S gate. No numerical core search, angular grid, force deletion
or new computational certificate is a premise.

