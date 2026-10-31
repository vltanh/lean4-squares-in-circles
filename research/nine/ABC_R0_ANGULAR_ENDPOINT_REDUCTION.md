# ABC R0: a table-free reduction of every angle to two scalar endpoints

Date: October 25, 2026.

**Status: accepted complete table-free scalar proof, after independent
full review in `REVIEW_ABC_R0_TABLE_FREE_2026_10_25.md`.** The positive
endpoint is proved in `ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md` and also
separately reviewed in
`REVIEW_ABC_R0_POSITIVE_ENDPOINT_ANALYTIC_2026_10_25.md`. This source targets the remaining
270-sign large-ratio packet in `ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md`.
It keeps the original scalar, force ratios and physical assembly.

## 1. The original scalar and the exact square identities

Use the unchanged notation

\[
 K=79/40,\qquad r=1/\sqrt2,\qquad x\ge1,\qquad -r\le d\le r,
 \qquad e=\sqrt{1-d^2},
\]

\[
 a=x^2+1-2dx,\qquad
 b=2x^2+1+2x(e-d),
\]

\[
 p=a+dx/2,\qquad
 q=b+\frac{dx(e+d)}{2e},\qquad
 h=\frac{8+16d}{25}.
\]

Here \(a,b,p,q\) are strictly positive on the complete domain. The
required scalar is

\[
 F(x,d)=K\frac p{\sqrt a}-\frac q{\sqrt b}-\frac x2+h>0.
 \tag{1}
\]

The already accepted source proves (1) for \(0\le x\le1\). We use
the exact identities, valid without restricting the sign of \(d\),

\[
 \frac{p^2}{a}=x^2+1-dx+\frac{d^2x^2}{4a},
\]

\[
 \frac{q^2}{b}=2x^2+1+(e+1/e-d)x
       +\frac{d^2x^2}{4b}(1+d/e)^2.
 \tag{2}
\]

## 2. One affine lower bound for the first square root term

Put \(L=x^2+1\) and \(t=dx/L\). Since \(x/L\le1/2\), the
entire domain satisfies \(-r/2\le t\le r/2\). Exactly,

\[
 \frac p{\sqrt a}=\sqrt L\,\phi(t),\qquad
 \phi(t)=\frac{1-3t/2}{\sqrt{1-2t}}.
\]

The derivatives needed for a cubic Taylor bound are

\[
 \phi(0)=1,\quad \phi'(0)=-1/2,\quad
 \phi''(0)=0,\quad \phi'''(0)=3/2,
\]

\[
 \phi''''(t)=\frac{(15/2)(2+3t)}{(1-2t)^{9/2}}>0
 \qquad(-r/2\le t\le r/2).
\]

Indeed \(1-2t>0\) and \(2+3t\ge2-3r/2>0\). Taylor's
fourth-order remainder is nonnegative for either sign of \(t\), so

\[
 \frac p{\sqrt a}\ge
 \sqrt L-\frac{dx}{2\sqrt L}
             +\frac{d^3x^3}{4L^{5/2}}.
 \tag{3}
\]

The entire cubic, including negative \(d\), has the affine lower bound

\[
 d^3-\frac{3d-r}{8}=(d-r/2)^2(d+r)\ge0.
 \tag{4}
\]

Thus the following expression is affine in the actual angle variable
\(d\) and is a valid lower bound throughout its full closed interval:

\[
 P_*(x,d)=\sqrt L-\frac{dx}{2\sqrt L}
                    +\frac{x^3(3d-r)}{32L^{5/2}}
 \le\frac p{\sqrt a}.
 \tag{5}
\]

No Taylor series is truncated without its whole-interval remainder sign.

## 3. One convex upper square root for the second term

For \(r\le e\le1\),

\[
 e+1/e-2=d^2\frac{1-e}{e(1+e)}
       \le(3\sqrt2-4)d^2.
 \tag{6}
\]

The factor \((1-e)/(e(1+e))\) decreases with \(e\), and its value
at \(r\) is \(3\sqrt2-4\). The inequality is exact at \(d=0\)
and at both \(d=\pm r\).

Also, on the entire interval \([-r,r]\), the function

\[
 U(d)=(1+d/e)^2
\]

is strictly convex, since

\[
 U''(d)=\frac{2(e^2+4d^2+3de)}{e^6}
       =\frac{2((e+3d/2)^2+7d^2/4)}{e^6}>0.
\]

Its endpoint values are \(U(-r)=0\) and \(U(r)=4\). The chord
bound for a convex function therefore gives

\[
 U(d)\le2(1+\sqrt2d).
 \tag{7}
\]

Since \(d^2\le1/2\), \(1+\sqrt2d\ge0\), and
\(b\ge2x^2+1\), (2), (6), and (7) imply

\[
 \frac{q^2}{b}\le B_*(x,d),
 \tag{8}
\]

where

\[
 c=\frac{x^2}{4(2x^2+1)},\qquad
 B_*=2x^2+2x+1-dx+(3\sqrt2-4)xd^2
                         +c(1+\sqrt2d).
 \tag{9}
\]

In particular \(q/\sqrt b\le\sqrt{B_*}\). This upper bound is
**exact at both angular endpoints**. At \(d=-r\), the original
\(e+d\) vanishes, while at \(d=r\), the original \(b=2x^2+1\).
Consequently

\[
 \sqrt{B_*(x,-r)}=\sqrt2x+1,
 \qquad
 \sqrt{B_*(x,r)}=
 \frac{2x^2+1+rx}{\sqrt{2x^2+1}}.
 \tag{10}
\]

For fixed \(x\ge1\), \(\sqrt{B_*}\) is strictly convex in \(d\).
To verify this globally, write \(B_*=B_0+B_1d+C d^2\), where

\[
 B_0=2x^2+2x+1+c\ge2x^2,\quad
 B_1=-x+\sqrt2c,\quad C=(3\sqrt2-4)x>x/5.
\]

Here \(0<c<1/8\), so \(|B_1|<x\). Hence

\[
 4CB_0-B_1^2>\frac85x^3-x^2>0.
\]

The usual derivative formula for the square root of a quadratic yields

\[
 \frac{\partial^2}{\partial d^2}\sqrt{B_*}
   =\frac{4CB_0-B_1^2}{4B_*^{3/2}}>0.
 \tag{11}
\]

All square roots and derivatives are defined throughout the closed
physical interval because (8) and \(q^2/b>0\) give \(B_*>0\).

## 4. The entire angular interval reduces to two explicit endpoints

Combining (5) and (8),

\[
 F(x,d)\ge G(x,d):=K P_*(x,d)-\sqrt{B_*(x,d)}-x/2+h.
 \tag{12}
\]

For fixed \(x\ge1\), \(G\) is concave in \(d\): both \(P_*\)
and \(h\) are affine, and (11) gives convexity of the subtracted square
root. Therefore

\[
 F(x,d)\ge\min\{M_-(x),M_+(x)\},
 \tag{13}
\]

with the complete endpoint expressions

\[
\begin{aligned}
 M_-(x)={}&K\left(\sqrt L+\frac{rx}{2\sqrt L}
                         -\frac{rx^3}{8L^{5/2}}\right)\\
 &-(\sqrt2+1/2)x-\frac{17+16r}{25},
\end{aligned}
\tag{14}
\]

\[
\begin{aligned}
 M_+(x)={}&K\left(\sqrt L-\frac{rx}{2\sqrt L}
                         +\frac{rx^3}{16L^{5/2}}\right)\\
 &-\frac{2x^2+1+rx}{\sqrt{2x^2+1}}
 -x/2+\frac{8+16r}{25}.
\end{aligned}
\tag{15}
\]

This reduces the entire angular domain to the two one-variable
inequalities (14)--(15). Section 5 and the positive-endpoint companion
prove them on all \(x\ge1\), including their unbounded tails.

## 5. The negative endpoint is positive for every x >= 1

### 5.1 The interval 1 <= x <= 3/2

Convexity of \(\sqrt{x^2+1}\), or the two-dimensional Cauchy
inequality, gives its tangent lower bound at \(x=3/2\):

\[
 \sqrt L\ge\frac{3x+2}{\sqrt{13}}.
\]

Also \(x/\sqrt L\ge r\). Finally, \(L\ge2x\) gives

\[
 \frac{x^3}{L^{5/2}}\le\frac{\sqrt x}{4\sqrt2}
 \le\frac{\sqrt3}{8}<\frac14.
\]

Thus (14) is bounded below by the affine expression

\[
 K\left(\frac{3x+2}{\sqrt{13}}+\frac14-\frac r{32}\right)
       -(\sqrt2+1/2)x-\frac{17+16r}{25}.
\]

Its slope is negative: \(K<2\), \(\sqrt{13}>7/2\), and
\(\sqrt2>7/5\) give
\(3K/\sqrt{13}<12/7<19/10<\sqrt2+1/2\).
Its minimum is consequently at \(x=3/2\). Using
\(\sqrt{13}>18/5\) and \(r<99/140\) there gives the strict bound

\[
\begin{aligned}
 M_-(x)
 &>K\left(\frac95+\frac14-\frac{99}{4480}\right)
       -\frac32\left(\frac{99}{70}+\frac12\right)
       -\frac{17+16(99/140)}{25}\\
 &=\frac{991}{896000}>\frac1{1000}>0.
\end{aligned}
\tag{16}
\]

### 5.2 The entire tail x >= 3/2

For \(t\ge0\), the Taylor remainder signs give

\[
 \sqrt{1+t}\ge1+t/2-t^2/8,\qquad
 (1+t)^{-1/2}\ge1-t/2.
\]

Apply these with \(t=1/x^2\), and use \(L^{5/2}\ge x^5\) in
the subtracted term of (14). Then

\[
 M_-(x)\ge \frac{P(x)}{8x^3},
 \tag{17}
\]

where the single quartic is

\[
\begin{aligned}
 P(x)={}&(59/5-8\sqrt2)x^4
       +(-136/25+139\sqrt2/100)x^3\\
       &+(79/10)x^2-(237\sqrt2/80)x-79/40.
\end{aligned}
\tag{18}
\]

This quartic is strictly increasing on \([3/2,\infty)\). Here is
a direct verification requiring no root table. In \(t=x-5/2\), write
its coefficients of \(t^4,t^3,t^2,t\) as

\[
\begin{aligned}
 A&=59/5-8\sqrt2,\\
 B&=2814/25-7861\sqrt2/100,\\
 C&=2048/5-11583\sqrt2/40,\\
 D&=675-4769\sqrt2/10.
\end{aligned}
\]

The elementary rational enclosure
\(140/99<\sqrt2<99/70\), whose squared integer reserves are two
and one, gives

\[
 0<A<1/2,\qquad B>4/3,\qquad
 0<C<1/10,\qquad D>1/2.
 \tag{19}
\]

For \(t\ge0\), every term of
\(P'=4At^3+3Bt^2+2Ct+D\) is nonnegative and \(D>0\).
For \(-1\le t\le0\), group the same derivative as

\[
 P'=t^2(3B+4At)+2Ct+D>2t^2+3/10>0.
\]

Finally

\[
 P(3/2)=\frac{22871-16101\sqrt2}{400}
       >\frac{6971}{28000}>\frac15.
 \tag{20}
\]

Equations (17)--(20) prove \(M_-(x)>0\) on the whole unbounded
tail. Together with (16), this completes the negative endpoint without
a computational sign certificate.

## 6. Positive endpoint and physical assembly

`ABC_R0_POSITIVE_ENDPOINT_ANALYTIC.md` proves (15) for every x>=1
by controlled Taylor comparisons and one short positive quintic
decomposition. The whole angular reduction, both endpoints, the
small-ratio join and original physical pressure assembly have passed
independent full review. The remaining270-sign packet is now superseded
by this table-free proof; its files remain historical provenance.

The final implication is unchanged: (13), positivity of both
endpoints, and the accepted small-ratio proof yield the original R0
scalar for every nonnegative x and every original angle. The original
proof then uses the same scalar at its two genuine force ratios, with
all root-degree, pressure-reserve, contact-owner and application-mean
arguments retained. This is a scalar proof replacement, not a new
physical reduction, contact selection or geometric gate.

No Lean compilation, CI or workflow dispatch has been used.
