# A uniform normal-ratio bound for every negative left contact

**Status: complete whole-domain hand scalar lemma; author, root and separate independent full saved-source, direct-prerequisite and exact-polynomial audits passed. This lemma alone closes no return or roadmap gate.**

Use the original negative H-owned endpoint frame throughout

\[
q_0=6241/1600\le q=R^2\le1105/256.
\]

A is physically unique and has true positive degree two, its actual neighbors are H and the physically boundary square K, \(c_H\cdot z_A<0\), and HA is an H-owned singleton. Suppose A's actual outgoing normal is its left inner-side axis and \(a>3/2\). All original means, H offsets, physical masks, individual circle weights and other H/K forces remain.

**Lemma.** The unchanged H-to-A normal \(n=(u,v)\) satisfies

\[
\frac56<\frac uv\le1.
\tag{1}
\]

No K force equation, tilt bound, physical HK edge or return assumption is used. The lemma applies to both singleton and genuinely shared left outgoing contacts, with every original mean.

## 1. Original scalar domain

Section 1 of NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md gives

\[
z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,\quad
\delta_A=1-\kappa\in[0,1/a),
\]

\[
n=\frac{(1-\delta_Aa,1-\delta_Ab)}
 {\sqrt{(1-\delta_Aa)^2+(1-\delta_Ab)^2}}.
\tag{2}
\]

The unchanged outgoing application is

\[
T=(x,\beta),\qquad x=a-1,\qquad \beta=(1-\delta_A)b.
\]

Here \(1/2<x<1\): the upper bound follows from
\(a^2<1105/256-9/25<4\). The orientation-uniform right-support lemma in Section 1 of NEGATIVE_H_OWNED_LEFT_AXIS_SMALL_COORDINATE_EXCLUSION.md applies to the actual K and gives

\[
\beta\ge Y_0-1,\qquad Y_0=\sqrt{q-x^2},\qquad 0<\beta\le b.
\tag{3}
\]

Put \(t=Y_0-b\). Then

\[
\frac12<t\le1,\qquad
0\le\delta_A\le\frac{1-t}{b},\qquad
 a=bt+\frac{1+t^2}{2}.
\tag{4}
\]

Indeed \(Y_0^2-b^2=2a-1>2\), while
\(Y_0<121/60\), \(b<23/16\) and \(121/60+23/16<4\), so \(t>1/2\). The upper bound follows from (3). The identity for a is the same circle identity expanded with \(Y_0=b+t\).

Consequently

\[
q=(1+t^2)\left\{\left(b+\frac t2\right)^2+\frac14\right\}.
\tag{5}
\]

## 2. One exact polynomial controls the entire original interval

Define

\[
D=6t^2-11t+6=6(t-11/12)^2+23/24>0,
\qquad N=3(1-t)(1+t^2)\ge0.
\]

We prove \(b>N/D\). The right side of (5) is strictly increasing in b for \(b\ge0\). At the comparison value \(b_*=N/D\),

\[
b_*+t/2=\frac{6-5t^2}{2D}.
\]

Thus \(q(b_*)<q_0\) is equivalent to

\[
P(t):=(4q_0-1-t^2)D^2-(1+t^2)(6-5t^2)^2>0.
\tag{6}
\]

For an exact whole-interval verification, put \(w=t-3/4\), so \(|w|\le1/4\). Direct expansion of (6) gives

\[
\begin{aligned}
P={}&\frac{193959}{102400}
-\frac{71829}{12800}w
+\frac{351561}{1280}w^2
-\frac{185859}{400}w^3\\
&+\frac{139201}{400}w^4
-\frac{285}{2}w^5-61w^6.
\end{aligned}
\tag{7}
\]

The constant is greater than \(3/2\), the absolute linear coefficient is less than 6, the quadratic coefficient is greater than 274, and the cubic, quintic and sextic absolute coefficients are at most 465, 143 and 61. The quartic coefficient is positive. Since \(|w|\le1/4\),

\[
274-\frac{465}{4}-\frac{143}{64}-\frac{61}{256}>150.
\]

It follows directly, without subdividing the interval, that

\[
P(t)>\frac32-6|w|+150w^2
\ge\frac32-\frac{6^2}{4\cdot150}
=\frac{36}{25}>0.
\tag{8}
\]

Thus \(q(b_*)<q_0\le q(b)\), proving \(b>N/D\) on the whole original domain, including the enlarged endpoint \(t=1\).

## 3. The actual normal and retained scope

Since \(6a-5b>0\), (4) and the comparison just proved give

\[
\begin{aligned}
\delta_A(6a-5b)
&\le(1-t)\left\{6t-5+\frac{3(1+t^2)}b\right\}\\
&<1.
\end{aligned}
\tag{9}
\]

For \(t<1\), the strict inequality is precisely \(b>N/D\), because
\(1-(1-t)(6t-5)=D\). At \(t=1\), its left side is zero. Equation (2) now gives

\[
6u-5v
=\frac{1-\delta_A(6a-5b)}
 {\sqrt{(1-\delta_Aa)^2+(1-\delta_Ab)^2}}>0,
\]

which proves (1). The original normal was bounded, not replaced. All radius endpoints, actual left-side means and original H offsets remain; H and K retain their real positive degrees. No numerical pose, angle cover, new normal selection, Lean compilation or CI is used.
