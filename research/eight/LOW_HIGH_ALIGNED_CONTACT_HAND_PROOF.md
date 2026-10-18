# A hand bound for the low/high aligned outer contacts

This note proves two continuous contact inequalities using explicit rational
comparisons. It uses neither a subdivision certificate nor a numerical
minimizer. It does **not** claim the complete four-type pair theorem.

## Constants and the two outer arcs

Put

\[
 Q=\frac{9789}{2500},\qquad
 c=\sqrt{Q/2}-\frac12,\qquad
 a_0=\sqrt{Q-1/4}-\frac12,
\]

and use the following rational coefficients:

\[
 \mu=\frac{403875}{10^6},\quad q=\frac{1089065}{10^6},\quad
 k=\frac{569472}{10^6},\quad v=\frac{390886}{10^6}.
\tag{1}
\]

Every outer state is on

\[
 (a+1/2)^2+(b+1/2)^2=Q,\qquad a\ge b\ge0.
\]

The low arc \(L\) has \(0\le b/a\le1/4\); the high arc \(H\)
has \(3/7\le b/a\le1\). Define

\[
 \ell_L(a,b)=\mu(a-a_0)+qb,
\qquad
 \ell_H(a,b)=\frac\pi4-k(a-c)+v(b-c).
\tag{2}
\]

For reference, write

\[
 a(b)=\sqrt{Q-(b+1/2)^2}-\frac12,
 \qquad r(b)=\frac{b+1/2}{a(b)+1/2}.
\]

Then

\[
 a'=-r,\qquad r'=\frac{Q}{(a+1/2)^3},\qquad
 \ell_L'=q-\mu r>0,\qquad \ell_H'=v+kr>0.
\tag{3}
\]

The last inequalities follow already from \(0\le r\le1\).
Let \(b_L\) and \(b_H\) be the transverse coordinates of the cuts
\(b/a=1/4\) and \(b/a=3/7\), respectively. Direct substitution in
the circle equation gives the useful coarse bounds

\[
 \frac3{10}<b_L<\frac{13}{40},\qquad
 \frac12<b_H<\frac{103}{200},\qquad
 \frac{89}{100}<c<\frac9{10}.
\tag{4}
\]

For example, \(17b_L^2+5b_L+1/2=Q\), and substituting \(13/40\)
exceeds \(Q\) by \(201/40000\). Similarly,
\((58/9)b_H^2+(10/3)b_H+1/2=Q\), and substituting \(103/200\)
exceeds \(Q\) by \(1853/180000\).

## The endpoint value

Set \(b_0=1-c\). The sharper square comparisons

\[
 \frac{1399214}{10^6}<\sqrt{Q/2}<\frac{1399215}{10^6},
\qquad
 \sqrt{Q-(b_0+1/2)^2}>\frac{1885379}{10^6},
\qquad
 \sqrt{Q-1/4}<\frac{1914576}{10^6}
\tag{5}
\]

follow by squaring positive quantities. In the second comparison use
\(b_0+1/2<600786/10^6\). The four positive square differences are,
in the displayed order,

\[
 \frac{45551}{250000000000},\quad
 \frac{104649}{40000000000},\quad
 \frac{2208563}{10^{12}},\quad
 \frac{4921}{3906250000}.
\]

Consequently

\[
 \frac{3185}{10000}<r(b_0)<\frac{31866}{100000}.
\tag{6}
\]

For the upper bound,
\((31866/100000)(1885379/10^6)-600786/10^6
=443607/50000000000>0\).
For the lower bound use \(b_0+1/2>600785/10^6\) and
\(a(b_0)+1/2<1886/1000\); the latter square comparison has positive
slack, and \((3185/10000)(1886/1000)<600785/10^6\).

The elementary Machin lower bound

\[
 \pi>
 16\left(\frac15-\frac1{3\cdot5^3}+
 \frac1{5\cdot5^5}-\frac1{7\cdot5^7}\right)-\frac4{239}
 =\frac{1231847548}{392109375}>
 \frac{314159}{100000}
\tag{7}
\]

is obtained from the alternating arctangent series and
\(\pi=16\arctan(1/5)-4\arctan(1/239)\).
This last identity follows by the tangent addition formula, whose
result is \(\tan(4\arctan(1/5)-\arctan(1/239))=1\), with the
angle in \((0,\pi/2)\).

At \((A,B)=(c,c)\), the high label equals \(\pi/4\). Thus (5)--(7)
give

\[
\begin{split}
 F_0&:=\ell_L(a(b_0),b_0)+\frac\pi4\\
 &>\frac{314159}{400000}
 -\mu\frac{29197}{10^6}
 +q\frac{100785}{10^6}\\
 &=\frac{17667339553}{20000000000}
 =0.88336697765.
\end{split}
\tag{8}
\]

Moreover, with \(d_0=q-v-k-\mu r(b_0)\), (6) gives

\[
 \frac{3277}{400000000}<d_0<\frac1{10000}.
\tag{9}
\]

The lower numerator in (9) is exact. For the upper comparison the
remaining slack is \(87/3200000\).

## Parallel contact: opposite signed states

Suppose the relative frame angle is zero, the source has positive signed
tangent and the target negative signed tangent, and separation is on
source \(+f\). For a low and a high state in either order, separation
is exactly

\[
 b+B\ge1,
\]

and the corrected cost is \(\ell_L(a,b)+\ell_H(A,B)\). Both labels
increase with their transverse coordinate. Since \(b_L+b_H<1\),
decreasing transverse coordinates until contact stays within the type
arcs and does not increase cost. On contact write

\[
 F(b)=\ell_L(a(b),b)+\ell_H(a(1-b),1-b),
 \qquad b_0\le b\le b_L.
\]

All these target points are in \(H\): \(1-b\ge27/40>b_H\).
Differentiation gives

\[
 F''(b)=
 -\frac{\mu Q}{[Q-(b+1/2)^2]^{3/2}}
 +\frac{kQ}{[Q-(3/2-b)^2]^{3/2}}>
 \frac14.
\tag{10}
\]

Here \(b\le13/40\) gives the first square root greater than
\(179/100\), while \(b\le13/40\) gives the second square root
less than \(8/5\). Using \(39/10<Q<98/25\),
\(\mu<101/250\), and \(k>569/1000\), the lower bound in (10)
minus \(1/4\) is at least

\[
 \frac{(569/1000)(39/10)}{(8/5)^3}
 -\frac{(101/250)(98/25)}{(179/100)^3}-\frac14
 =\frac{3675503589}{234919485440}>0.
\]

At the left endpoint \(F(b_0)=F_0\) and \(F'(b_0)=d_0>0\).
Thus \(F\) increases throughout its domain, proving

\[
 \boxed{\ell_L+\ell_H\ge F_0>\frac{8833}{10000}.}
\tag{11}
\]

## Quarter contact: low source, high target, both positive signs

Now let the relative frame angle be \(\pi/2\), with both signed
tangents positive and separation on source \(+f\). Separation and
cost become

\[
 A+b\ge1,\qquad C=\frac\pi2+\ell_L(a,b)-\ell_H(A,B).
\]

As a function of \(A\) along the high arc,

\[
 \frac{d}{dA}(-\ell_H)=k+v\frac{A+1/2}{B+1/2}>0.
\]

For fixed \(b\), the smallest feasible \(A\) is therefore
\(\max(c,1-b)\). If \(b\ge b_0\), the choice is \(A=B=c\),
and (3) gives \(C\ge F_0\). If \(0\le b\le b_0\), the contact
is \(A=1-b\) and
\(B=\sqrt{Q-(3/2-b)^2}-1/2\); this is in the high arc, since
\(c\le A\le1\) and its ratio \(B/A\) is greater than \(3/7\).
The resulting cost \(G\) satisfies

\[
 G(b_0)=F_0,\qquad G'(b_0)=d_0,
\]

\[
 G''(b)=
 -\frac{\mu Q}{[Q-(b+1/2)^2]^{3/2}}
 +\frac{vQ}{[Q-(3/2-b)^2]^{3/2}}>\frac14.
\tag{12}
\]

Indeed \(b\le b_0<101/1000\) bounds the first square root below
by \(47/25\), and \(b\le b_0\) bounds the second above by
\(7/5\). The corresponding rational curvature reserve is

\[
 \frac{(39/100)(39/10)}{(7/5)^3}
 -\frac{(101/250)(98/25)}{(47/25)^3}-\frac14
 =\frac{18791925}{284890312}>0.
\]

Integrating (12), then completing the square, gives for every such \(b\)

\[
 G(b)\ge F_0+d_0(b-b_0)+\frac18(b-b_0)^2
 \ge F_0-2d_0^2>F_0-\frac1{50000000}.
\]

Combining with (8),

\[
 \boxed{C>
 \frac{17667339153}{20000000000}
 >\frac{8833}{10000}.}
\tag{13}
\]

Reversal followed by reflection gives the identical cost bound for the
corresponding reversed target-axis contact. The open strips around these
aligned contacts require the separate deformation arguments; they are
not inferred merely from continuity of (11) or (13).
