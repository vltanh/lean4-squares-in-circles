# An unrestricted three-square directional cap at 21/20

November 2, 2026. Complete hand proof. The polynomial and every interval
bound below were derived by hand. No mathematical script, numerical
enumeration, Lean, Lake, or CI is a proof input.

Put

\[
 Q=\frac{1105}{256},\quad R=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad
 \eta=\frac{21}{20},\quad \kappa=\frac76,\quad
 \tau=\frac{499}{1000},\quad d=\kappa-\eta=\frac7{60}.
\]

## 1. The theorem and the retained slice argument

**Theorem.** Every physical unit square in the Q-disk with center
\((X,Y)\), where \(Y\ge21/20\), contains at least one of

\[
                       (-\tau,\kappa),
                       \qquad(\tau,\kappa)             \tag{1}
\]

in its interior. Thus any three interior-disjoint physical unit squares
satisfy, for every unit direction e,

\[
                          \min_{i=1,2,3}e\cdot c_i
                          <\frac{21}{20}.              \tag{2}
\]

No pairwise coordinate-separation assumption is made. The numerical
threshold is not asserted sharp.

For side-axis absolute components \(a\ge b\ge0\),
\(a^2+b^2=1\), put
\(h=(a+b)/2\), \(j=(a-b)/2\). The section at a vertical offset t
has length \(1/a\) for \(|t|\le j\), and
\((h-|t|)/(ab)\) for \(j\le|t|\le h\), when b>0. In particular
it has length at least one if \(|t|<h-ab\).

For the line at height κ, the offset below the center is bounded using
the uppermost vertex y+h≤R and

\[
 R<\frac{133}{64}<\frac{206}{99}<\sqrt2+\frac23.
\]

The first root comparison has squared reserve 9/4096. The middle
comparison has cross-product difference 17; the last uses
\(\sqrt2>140/99\), since 19602>19600. Also
\(2h-ab\ge\sqrt2-1/2\): writing z=a+b in \([1,\sqrt2]\),
the expression is z−(z²−1)/2, which decreases on that interval.
Consequently y−κ≤R−h−κ<h−ab when the center is above the line.
The offset above the center is at most

\[
 \kappa-\eta=\frac7{60}<\frac{\sqrt2-1}{2}\le h-ab.
\]

Thus this section is a closed interval of length at least one, and the
line passes strictly between the unit's extreme y-coordinates.

The last bound follows from
\(h-ab=(1+z-z^2)/2\ge(\sqrt2-1)/2\).
As the section length exceeds the marker spacing \(2\tau<1\), it is enough
to exclude a section lying entirely on or to the right of τ. Reflection
excludes the corresponding left case. One marker will then lie strictly
inside the section and hence inside the physical square.

## 2. The actual side inequality and its upward sign

Suppose that section has left endpoint at least τ. The line passes
strictly between the square's extreme y-coordinates, so a side giving
the left endpoint is not horizontal. Its inward normal points to the
right and is one of the square's actual side axes. Thus it supplies
\(n=(p,s)\), with
p>0 and \(p^2+s^2=1\), such that

\[
                       n\cdot c\ge\frac12+p\tau+s\kappa. \tag{3}
\]

The perpendicular side axis is \(m=(-s,p)\). For
\(\alpha=n\cdot c\), \(\beta=m\cdot c\), the exact maximal
corner norm is

\[
                         (|\alpha|+1/2)^2+(|\beta|+1/2)^2. \tag{4}
\]

All centers obey \(|c|<\rho\). This follows from
\(q\ge|c|^2+|c|+1/2\) and
\(\rho^2+\rho+1/2-Q=31/57600>0\).

Assume first s≥0, and put \(J=1/2+\tau p+\kappa s\).
The function \(\tau\sqrt{1-s^2}+\kappa s\) is concave. On
\([3/5,1]\) its minimum is therefore at an endpoint; adding 1/2,
the endpoint values are 1999/1250 and 5/3. Hence for s≥3/5,

\[
                         \alpha\ge J\ge\frac{1999}{1250}>\rho,
\]

which is impossible. For \(0\le s\le3/5\), we have p≥4/5>s,
α≥J>0, and

\[
 \beta=\frac{Y-s\alpha}{p}
 >\frac{\eta-(3/5)\rho}{p}=\frac7{50p}>0.             \tag{5}
\]

For fixed α, lowering Y to η decreases (4). At Y=η, half the derivative
of (4) with respect to α is

\[
                    \frac{\alpha-s\eta+(p^2-sp)/2}{p^2}>0
                    \qquad(\alpha\ge J),
\]

since \(J-s\eta=1/2+\tau p+ds>0\). Thus (4) is bounded below
by its value at \(Y=\eta,\alpha=J\). The corresponding horizontal
coordinate is

\[
                          X'=\tau+\frac{1/2+ds}{p}.    \tag{6}
\]

Set \(h=(p+s)/2\), \(j=(p-s)/2\). At that minimizing center,
the corner in (4) has coordinates \((X'+j,\eta+h)\). For a positive
lower bound v≤X', its squared norm is at least

\[
                 v^2+\eta^2+\frac12+(\eta+v)p+(\eta-v)s. \tag{7}
\]

Two simple ranges suffice:

| s range | Lower bounds used in (7) | Squared-norm lower bound | Reserve over Q |
|---|---|---:|---:|
| \([0,2/5]\) | \(X'>99/100,\ p>9/10\) | \(22093/5000\) | \(16351/160000\) |
| \([2/5,3/5]\) | \(X'>26/25,\ p\ge4/5\) | \(43561/10000\) | \(6351/160000\) |

In both rows η≥v, so the last term in (7) can be dropped. The first
row uses \(p\ge\sqrt{21}/5>9/10\) and
\(X'\ge\tau+1/2>99/100\). For the second,

\[
 X'\ge\tau+\frac12+\frac25d
 =\frac{3137}{3000}>\frac{26}{25}.
\]

The two reserves follow by putting the displayed bounds and Q over
denominator 160000. The entire nonnegative-sign case is excluded.

## 3. The downward sign and its large vertical component

Write now \(n=(p,-u)\), with p>0, u≥0, and \(p^2+u^2=1\).
Equation (3) and Y≥η give

\[
 X\ge\tau+\frac{1/2+u(Y-\kappa)}p
   \ge X_\eta(u):=\tau+\frac{1/2-du}{\sqrt{1-u^2}}.   \tag{8}
\]

For u≥18/25, the fraction in (8) increases: its derivative has
numerator u/2−d>0. Consequently

\[
 X\ge\tau+\frac{52}{5\sqrt{301}}
 >\tau+\frac{208}{347}>\frac{219}{200}.                \tag{9}
\]

Here \(\sqrt{301}<347/20\), with squared numerator comparison
\(120400<120409\), and
\(\tau+208/347-219/200=297/86750>0\). Therefore

\[
 |c|^2>\left(\frac{219}{200}\right)^2+
          \left(\frac{21}{20}\right)^2
 =\rho^2+\frac{449}{360000}>\rho^2,
\]

which is impossible.

It remains to consider \(0\le u\le18/25\). Put

\[
 h=\frac{p+u}{2},\quad j=\frac{p-u}{2}.
\]

One actual corner is \((X+h,Y+j)\). Both coordinates in the lower
bound \((X_\eta+h,\eta+j)\) are positive, so (8) gives

\[
                 q\ge (X_\eta(u)+h)^2+(\eta+j)^2.     \tag{10}
\]

This does not assume which own-frame coordinate determines the farthest
corner. A single actual corner is sufficient.

## 4. One explicit polynomial represents the remaining corner bound

Use the half-angle parameter

\[
 t=\frac{u}{1+p},\qquad
 p=\frac{1-t^2}{1+t^2},\quad u=\frac{2t}{1+t^2}.
\]

The remaining u range gives

\[
 0\le t\le\frac{18}{25+\sqrt{301}}<\frac37,           \tag{11}
\]

using \(\sqrt{301}>17\). Direct substitution yields

\[
 X_\eta=\frac{2997-700t+3t^2}{3000(1-t^2)}.
\]

Define

\[
 A(t)=4497+2300t-3700t^3+1503t^4,
\]

\[
 B(t)=4650-3000t-3000t^2+3000t^3-1650t^4.
\]

Then

\[
 X_\eta+h=\frac{A(t)}{3000(1-t^4)},
 \qquad \eta+j=\frac{B(t)}{3000(1-t^4)}.
\]

Thus the right side of (10), minus Q, is

\[
                \frac{P(t)}{36000000(1-t^4)^2},        \tag{12}
\]

where the following table specifies every coefficient of P:

| Degree | Coefficient |
|---:|---:|
| 0 | 11991411 |
| 1 | -28855200 |
| 2 | -54440000 |
| 3 | 50488800 |
| 4 | 199393178 |
| 5 | -4744800 |
| 6 | 130360000 |
| 7 | -84088800 |
| 8 | -135464589 |

For direct independent hand verification, the entire table is the single
identity

\[
             P(t)=4\bigl(A(t)^2+B(t)^2\bigr)
                   -155390625(1-t^4)^2.               \tag{13}
\]

No generated table or numerical sample is used: (13) and the next scalar
inequalities establish positivity on the whole interval (11).

## 5. A hand proof that P is positive on the whole interval

### 5.1. P decreases up to 3/10

For \(0\le t\le3/10\), drop the negative degree-four, degree-six,
and degree-seven terms of P'. Its positive terms satisfy

\[
\begin{aligned}
 151466400t^2+797572712t^3+782160000t^5
 &<\left(152000000\frac3{10}
       +798000000\frac9{100}
       +783000000\frac{81}{10000}\right)t\\
 &<124000000t
\end{aligned}
\]

for t>0; t=0 is immediate separately. Hence

\[
 P'(t)\le-28855200+15120000t
 \le-24319200<0.                                      \tag{14}
\]

So P(t)≥P(3/10) on this first interval.

### 5.2. Uniform strict convexity from 3/10 through 3/7

The exact second derivative is

\[
\begin{aligned}
 P''(t)={}&-108880000+302932800t+2392718136t^2
            -94896000t^3\\
          &+3910800000t^4-3531729600t^5-7586016984t^6.
\end{aligned}
\]

For \(0\le t\le3/7\), use

\[
 94896000t^3<41000000t^2,
\]

\[
 3531729600t^5\le1514000000t^4,
 \qquad7586016984t^6\le1394000000t^4.
\]

At t=0 the first displayed strict inequality is read as equality;
we use the resulting strict estimate below only for t≥3/10.
These comparisons follow respectively from

\[
 94896000\frac37<41000000,
 \quad3531729600\frac37<1514000000,
 \quad7586016984\frac9{49}<1394000000.
\]

The remaining degree-four coefficient is positive. It follows, throughout
\(3/10\le t\le3/7\), that

\[
\begin{aligned}
 P''(t)
 &>-109000000+300000000t+2350000000t^2\\
 &\ge192500000>180000000.                             \tag{15}
\end{aligned}
\]

### 5.3. One rational anchor and a quadratic lower bound

Direct evaluation of the printed polynomial gives

\[
 P(2/5)=\frac{130272735091}{390625}>300000,
\]

\[
 0<P'(2/5)=\frac{475586408864}{78125}<7000000.          \tag{16}
\]

These rational evaluations can also be checked from (13). Integrating
the uniform second-derivative bound (15), or completing the corresponding
quadratic, gives for every t in \([3/10,3/7]\)

\[
\begin{aligned}
 P(t)
 &\ge P(2/5)+P'(2/5)(t-2/5)+90000000(t-2/5)^2\\
 &>300000-\frac{7000000^2}{360000000}
   =\frac{1475000}{9}>0.                              \tag{17}
\end{aligned}
\]

In particular P(3/10)>0. Equation (14) now proves positivity on
\([0,3/10]\) as well. Thus P is positive everywhere in (11).

Equations (10)--(12) contradict q≤Q. This completes the entire downward
normal case.

## 6. Complete unrestricted consequences

No physical square centered at Y≥21/20 can have its height-κ section on
or beyond either marker. The section length is at least one, greater than
the marker spacing. Thus one marker is strictly interior, proving (1)--(2).

Two global consequences follow directly:

1. Every triangle of three physical centers meets the open central disk
   of radius 21/20, including collinear triples. Otherwise its closest
   point to the origin would have norm at least 21/20, and its radial
   direction would give all three center projections at least 21/20,
   contradicting (2).
2. In the exact normalized boundary-square frame, **at least seven of
   the eight other centers satisfy x<21/20**. The sharp x<H bound on
   all eight remains available simultaneously.

Here are the full details of the second statement. The proved global
boundary normalization in
[BOUNDARY_NORMALIZATION_WITH_SHARP_CAP_HAND_PROOF.md](BOUNDARY_NORMALIZATION_WITH_SHARP_CAP_HAND_PROOF.md) gives

\[
 u_0=(a,b),\quad v_0=(-b,a),\quad a\ge b>0,
 \quad a^2+b^2=1,\quad
 c_0=\left(R-\frac{a+b}{2},\frac{a-b}{2}\right).
\]

Its touching corner is (R,0). Put δ=R−κ. The coordinates of
\(Z_+=(\kappa,\tau)\) relative to its physical frame are

\[
 u_0\cdot(Z_+-c_0)=\frac12-\delta a+\tau b,
 \qquad v_0\cdot(Z_+-c_0)=-\frac12+\delta b+\tau a.
\]

We have 0<τ<δ<1. Since b≤a,
\(0<\delta a-\tau b<1\). On \(0\le b\le1/\sqrt2\),
\(\delta b+\tau\sqrt{1-b^2}\) increases, so

\[
 0<\delta b+\tau a\le\frac{\delta+\tau}{\sqrt2}<1.
\]

The last inequality uses
\(\delta+\tau< R-\kappa+1/2=R-2/3<\sqrt2\).
Thus Z+ is interior to the normalized boundary square.

Any other physical square must avoid Z+ even as a closed point; otherwise
its nearby interior points would overlap that boundary square's interior.
By the marker theorem rotated through a right angle, every other square
whose center has x≥21/20 must therefore contain
\(Z_-=(\kappa,-\tau)\) in its interior. There can be at most one such
square. This proves the stated seven-center guard.

The cap is an unconditional physical theorem with no orientation or
coordinate-cover premise. It supplies a new global guard, not a complete
unrestricted nine-square exclusion or equality classification.

