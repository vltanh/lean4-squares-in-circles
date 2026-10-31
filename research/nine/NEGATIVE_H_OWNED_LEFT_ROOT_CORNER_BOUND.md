# A negative left endpoint keeps the entire root inside the adjacent-corner radius

**Status: complete whole-domain hand bound; author, root and separate independent full saved-source, direct-prerequisite, exact-algebra and original-offset audits passed. This source supplies a geometric exclusion, not the entire remaining left-return assembly.**

Work throughout \(q_0=6241/1600\le q=R^2\le1105/256\). A is physically unique with true positive degree two, K is its actual physically boundary neighbor, \(c_H\cdot z_A<0\), HA is an H-owned singleton, and A's actual outgoing normal toward K is its left inner-side axis. Assume \(a>3/2\) in the original ordered frame. Keep every original H offset and application mean, all H/K forces and physical masks, and every other physical square.

**Theorem.** Every point of the actual H satisfies

\[
|z|^2<\frac{10609}{10000}
       <d_R^2+\frac14,
\qquad d_R=\sqrt{q-\frac14}-1.
\tag{1}
\]

Consequently H cannot contain any vertex of a contained unit that is adjacent to one of that unit's physical circle corners. No equation at H or K is used.

## 1. Full original frame and uniform scalar bounds

Use the degree-independent frame from Section 1 of NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md:

\[
z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,\quad
P=(x,b-1),\quad x=a-1,
\]

\[
n=(u,v),\quad 0<u\le v,\quad j=Jn=(-v,u),\quad
H(r)=P+[-1,0]n+[-(1-r),r]j,\quad 0<r<1.
\tag{2}
\]

Here r is the original offset. The actual left support is \((x,\beta)\), with \(0<\beta\le b\). The orientation-uniform support bound gives
\(\beta\ge\sqrt{q-x^2}-1\), hence \(a-b\le1\).
The same comparisons as Section 1 of NEGATIVE_H_OWNED_SHARED_LEFT_MIDDLE_EXCLUSION.md use only this inequality and give

\[
\frac12<x<\frac9{10},\qquad b>\frac45.
\tag{3}
\]

For completeness, \(a\le b+1\). If \(b\le4/5\), then
\(q=a^2+b^2\le97/25<q_0\). If \(x\ge9/10\), then \(b\ge x\) and
\(q\ge(x+1)^2+x^2\ge221/50>1105/256\).

NEGATIVE_H_OWNED_LEFT_NORMAL_RATIO_BOUND.md applies to every original left mean and gives

\[
\rho=u/v>5/6,\qquad
\frac5{\sqrt{61}}<u\le\frac1{\sqrt2},\qquad
\frac1{\sqrt2}\le v<\frac6{\sqrt{61}}.
\tag{4}
\]

We first sharpen the upper bound on b:

\[
b<\frac{13}{10}.
\tag{5}
\]

The full H-offset pressure bound and (4) give

\[
c_H\cdot z_A>
 a^2+b^2-a-b-\frac{11a+b}{2\sqrt{61}}.
\tag{6}
\]

The support expression decreases with \(\rho\ge5/6\), because \(a<2<11b\). The right side of (6) strictly increases with both a and b on \(a\ge3/2,b\ge13/10\). Its value at the lower corner is

\[
\frac{57}{50}-\frac{89}{10\sqrt{61}}>0;
\]

the exact last comparison is \(61\cdot57^2-445^2=164>0\). Thus \(b\ge13/10\) contradicts the actual negative pressure, proving (5).

## 2. All four vertices at the enlarged offset r=1 are short

Put \(\sigma=1/\sqrt2\). The four vertices of the comparison square H(1) are

\[
P,\quad P-n,\quad P+j,\quad P-n+j.
\]

This comparison does not move the actual H or assert that H(1) is another packing. It only bounds an endpoint of the original one-dimensional offset formula.

By (3), (5), \(|P|^2<9/10\). Also (4) gives
\(u>16/25\), \(v<77/100\), and \(v-u<13/100\). Hence

\[
|P-n|^2<\left(\frac{13}{50}\right)^2
            +\left(\frac{97}{100}\right)^2
=\frac{2017}{2000}<\frac{53}{50}.
\tag{7}
\]

For P+j, its second coordinate is positive and less than \(3/10+u\). At fixed u, the largest possible \((x-v)^2\) on \(1/2\le x\le9/10\) occurs at an endpoint. For either endpoint x, the expression

\[
(x-v)^2+(3/10+u)^2
=x^2+109/100-2x\sqrt{1-u^2}+(3/5)u
\]

strictly increases with u. At \(u=\sigma\), its two values are

\[
67/50-(2/5)\sigma,\qquad19/10-(6/5)\sigma,
\]

both less than \(53/50\), since \(\sigma>7/10\). Therefore
\(|P+j|^2<53/50\).

Finally the first coordinate of P-n+j is negative, with absolute value less than
\(\sqrt2-1/2<32/35\). Its second coordinate has absolute value less than \(33/100\). Thus

\[
|P-n+j|^2<\frac{1024}{1225}+\frac{1089}{10000}
=\frac{462961}{490000}<\frac{53}{50}.
\tag{8}
\]

All points of H(1) consequently have squared norm less than \(53/50\), by convexity of squared norm on the square.

## 3. The zero-pressure comparison center has norm less than 8/25

Write

\[
N=P\cdot n-1/2,\qquad J(r)=P\cdot j+r-1/2,
\]

so the actual center has H-axis coordinates \((N,J(r))\). Also set

\[
Z_n=au+bv>0,\qquad Z_j=-av+bu<0.
\]

The exact negative pressure says

\[
J(r)>J_*:=\frac{N Z_n}{-Z_j}.
\tag{9}
\]

If \(N\ge0\), then \(J(r)>0\). For fixed N the maximum squared vertex norm,
\((|N|+1/2)^2+(|J(r)|+1/2)^2\), increases with this positive J. Since \(r<1\), Section 2 already bounds every actual H vertex.

Suppose \(N<0\). Let \(c_*\) be the center with H-axis coordinates \((N,J_*)\). It satisfies \(c_*\cdot z_A=0\). Its norm t is exactly

\[
\frac tR=
\frac{\tfrac12\sqrt{1+\rho^2}-(a-1)\rho-b+1}{a-b\rho}.
\tag{10}
\]

The denominator is positive. At fixed a,b, the derivative of the quotient in (10) has the sign of

\[
\frac{a\rho+b}{2\sqrt{1+\rho^2}}-q+a+b
\le R/2-q+\sqrt2R<0,
\]

because \(R\ge79/40>1/2+\sqrt2\). Thus (4) bounds (10) above by

\[
F(q,a)=\frac{C-5a-6b}{6a-5b},\qquad C=11+\frac{\sqrt{61}}2.
\tag{11}
\]

At fixed q, with \(b=\sqrt{q-a^2}\),

\[
F_a=\frac{61q-C(5a+6b)}{b(6a-5b)^2}>0.
\tag{12}
\]

Indeed \(5a+6b\le\sqrt{61}R\), while \(R\sqrt{61}>3081/200>15>C\). Since \(a-b\le1\), the largest comparison a occurs at \(a=b+1\). Along that boundary,

\[
R^2=2b^2+2b+1,\qquad
R F=\sqrt{2b^2+2b+1}\,\frac{T-11b}{b+6},
\quad T=6+\frac{\sqrt{61}}2<10.
\tag{13}
\]

The function in (13) strictly decreases for \(b>0\). After multiplication of its derivative by positive factors, its numerator is

\[
-22b^3-275b^2+(11T-198)b+5T-66<0.
\tag{14}
\]

Thus its maximum comparison is at \(R=79/40\), where the corresponding b_0 satisfies
\(2b_0^2+2b_0+1=q_0\). One has \(b_0>803/1000\), since the exact squared-radius reserve is \(5007/1000000\). Also \(\sqrt{61}<391/50\), so \(T<991/100\). Equations (10)--(14) yield

\[
t<\frac{79}{40}\frac{1077}{6803}
=\frac{85083}{272120}<\frac8{25}.
\tag{15}
\]

The final rational reserve is \(9977/1360600>0\). Every vertex of the comparison square centered at c_* consequently has norm less than

\[
8/25+1/\sqrt2<8/25+71/100=103/100.
\tag{16}
\]

## 4. Convexity retains every original offset and excludes adjacent circle vertices

When \(N<0\), (9) and \(r<1\) put the original center on the segment between c_* and the center of H(1). The four corresponding vertices vary affinely along that same segment. Convexity of squared norm, together with Sections 2--3, therefore gives

\[
|z|^2<10609/10000
\]

at every original H vertex, and then at every point of the actual H. This includes every original strict offset and uses only enlarged scalar comparison positions.

The original radius window gives \(d_R>91/100\). Therefore

\[
d_R^2+1/4>10781/10000>10609/10000,
\]

proving (1).

For the stated consequence, express a physical circle corner of any contained unit in its outward side frame as \((A_C,B_C)\). Comparing adjacent corners gives \(A_C,B_C\ge1/2\), hence \(A_C,B_C\le\sqrt{q-1/4}\). Either vertex adjacent to this circle corner has squared norm at least

\[
q-2\sqrt{q-1/4}+1=d_R^2+1/4.
\]

No such vertex can belong to H by (1). This statement includes physical radial units and individual zero circle weights; it is purely geometric.

In the remaining ABC left-singleton, B-owned f-axis branch, the short actual BC point W forces a unique singleton C to have W opposite its circle corner. Its H-owned near return at W+q_Cedge is adjacent to that circle corner. The present bound excludes that whole return immediately, without an equation at H, a changed HC point or a chosen offset. The C-owned side-return cases and any shared-BC family retain their own complete obligations; this source does not silently replace them by vertex contacts. No physical motion, new normal selection, sampled pose premise, Lean compilation or CI is used.
