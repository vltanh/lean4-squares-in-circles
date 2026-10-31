# A centered forty-degree inner arc in every circle-touching square

**Status: complete geometric lemma.** In the radius window

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\]

every unit square contained in the disk of radius \(R\) and touching
its boundary contains, in its **open interior**, the entire closed
arc

\[
\left\{\frac54e_\theta:
  |\theta-\arg C|\le\frac\pi9\right\},                 \tag{1}
\]

where \(C\) is its center and the angle difference uses the ordinary
interval about \(\arg C\). Consequently any two physical
circle-touching squares with disjoint open interiors have minor center
angular separation **strictly greater than \(2\pi/9\)**.

This is a geometric strengthening of
`CIRCLE_CONTACT_ANGULAR_ORDER.md`, not a completion theorem for a
cyclic packing.

## 1. Center and angle estimates

Write \(r=|C|\). Reflect and exchange the square axes so that the
center makes an angle \(\phi\in[0,\pi/4]\) with the first own axis.
Set

\[
s=\sin\phi,\qquad c=\cos\phi,\qquad
\rho=\frac54,\qquad\alpha=\frac\pi9.
\]

The circle-touching condition is

\[
r^2+r(s+c)+\frac12=R^2.
\]

Since \((s+c)^2\le2\),

\[
\left(r+\frac{s+c}{2}\right)^2
 =R^2-\frac12+\frac{(s+c)^2}{4}\le R^2,
\]

and therefore

\[
r\le R-\frac{s+c}{2}
 <\frac{133}{64}-\frac{s+c}{2}.                          \tag{2}
\]

The final strict comparison follows from
\(1105/256=17680/4096<17689/4096=(133/64)^2\).
Also, as in the center-annulus lemma of
`CIRCLE_CONTACT_ANGULAR_ORDER.md`,

\[
r\ge R-\frac1{\sqrt2}>\frac54=\rho.                     \tag{3}
\]

We use the exact elementary bounds

\[
\cos\alpha>\frac{15}{16},\qquad
\sin\alpha<\frac{11}{32}.                              \tag{4}
\]

For the first, \(4x^3-3x\) is increasing for \(x>1/2\),
its value at \(15/16\) is \(495/1024<1/2\), and its value at
\(\cos\alpha\) is \(\cos3\alpha=1/2\).
For the second, \(3x-4x^3\) is increasing on \([0,1/2]\),
its value at \(11/32\) is \(7117/8192\), and

\[
7117^2=50651689>50331648=\frac34\,8192^2.
\]

Thus that value exceeds \(\sin3\alpha=\sqrt3/2\), which
proves the second comparison.

## 2. Both own-coordinate deviations are smaller than one half

Let \(P=\rho e_\theta\) with
\(|\theta-\arg C|\le\alpha\). In coordinates parallel and
perpendicular to \(C\), its displacement from the square center is
\((-K,L')\), where

\[
0<K\le r-\rho\cos\alpha,
\qquad |L'|\le\rho\sin\alpha.
\]

By (2)--(4), we may bound these two quantities strictly above by

\[
K<\frac{29}{32}-\frac{s+c}{2},
\qquad |L'|<\frac{55}{128}.
\]

Consequently the two absolute own-coordinate deviations are smaller
than or equal to the corresponding bounds

\[
F_1=\frac{29}{32}s+\frac{55}{128}c-\frac{s^2+sc}{2},
\qquad
F_2=\frac{29}{32}c+\frac{55}{128}s-\frac{c^2+sc}{2}.
\]

The larger bound is \(F_1\), since

\[
F_1-F_2=(c-s)\left(\frac{s+c}{2}-\frac{61}{128}\right)
\ge0.                                                   \tag{5}
\]

Here \(c\ge s\) and \(s+c\ge1\). It remains to prove
\(F_1<1/2\).

For \(0\le s\le1/\sqrt2\),

\[
1-\frac35s^2\le c\le1-\frac12s^2.                     \tag{6}
\]

The upper inequality follows by squaring or concavity. For the lower,
the square of its nonnegative left side is at most \(1-s^2\),
because \(s^2\le1/2<5/9\).
Using the lower estimate in \(sc\) and the upper estimate in
\(-55c/64\) gives

\[
\begin{aligned}
1-2F_1
 &=1+s^2+sc-\frac{29}{16}s-\frac{55}{64}c\\
 &\ge P(s)
 :=\frac9{64}-\frac{13}{16}s
        +\frac{183}{128}s^2-\frac35s^3.
\end{aligned}                                           \tag{7}
\]

This cubic has a particularly short positive certificate. Put
\(z=s-3/8\). Since \(0\le s\le1/\sqrt2<3/4\),
we have \(|z|\le3/8\), and expansion gives

\[
P(s)=\frac{219}{40960}+\frac{17}{2560}z
       +\left(\frac{483}{640}-\frac35z\right)z^2.
\]

The quadratic coefficient is positive throughout that interval.
Therefore

\[
P(s)\ge\frac{219}{40960}-\frac{17}{2560}\frac38
      =\frac{117}{40960}>0.                              \tag{8}
\]

Equations (5)--(8) put both own-coordinate deviations strictly
between \(-1/2\) and \(1/2\), proving (1).

## 3. The pair consequence

Suppose two circle-touching center directions had minor separation
at most \(2\alpha\). The midpoint direction on that minor arc is
at distance at most \(\alpha\) from each center direction. By (1),
the point of radius \(\rho\) in that midpoint direction would lie
in both open squares. This contradicts physical nonoverlap.
Thus their minor separation is strictly greater than \(2\pi/9\).
\(\square\)
