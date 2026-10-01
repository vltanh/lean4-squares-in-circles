# Appendix C. Six squares: the separators

[Contents](README.md) · [← Appendix B](appendix-b.md) · [Appendix D →](appendix-d.md)

This appendix proves the results of
[§9.6](09-six.md#96-the-separators-of-neighbours) on the separators of
neighbouring squares, in the order in which they depend on each other: the
secondary axes of two consecutive squares
([Lemma 9.37](09-six.md#lemma-937-secondary-axes), §C.1), the sign of the angle of
$W$ on its own axis
([Lemma 9.38](09-six.md#lemma-938-w-on-its-own-axis-turns-away-from-d), §C.2), the
angle of $D$ ([Proposition 9.39](09-six.md#proposition-939-the-angle-of-d), §C.3),
the transverse profiles
([Lemma 9.40](09-six.md#lemma-940-transverse-profiles), §C.4), the separation of
$D$ and $S$ along a secondary axis
([Proposition 9.41](09-six.md#proposition-941-d-and-s-along-a-secondary-axis),
§C.5), the walls ([Lemma 9.42](09-six.md#lemma-942-walls), §C.6) and the signs of
the own wings ([Lemma 9.43](09-six.md#lemma-943-signs-of-the-own-wings), §C.7).
Each proof uses only the results before it.

Three kinds of argument recur: separating inequalities, profiles and
stresses. A separation of two squares along an axis is a linear inequality
between their centres
([Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares)), and a
separation from the central square $C$ one between a centre and the centre of
$C$ ([Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square)).
Combined with the disk, such an inequality bounds a coordinate of a square by a
*profile*, a function of the angles. Where one inequality is not enough, a
*stress* ([Definition 9.23](09-six.md#definition-923-stress)) adds several of them
with weights, and the supports of the squares in the disk bound the works of
the forces ([Lemmas 9.24 to 9.26](09-six.md#lemma-924-balance)). The resulting
bounds are concave in each angle, so it remains to check them at the vertices
of a domain of the angles.

**Notation.** Throughout, a normalized packing
([Definition 9.34](09-six.md#definition-934-normalized-packing)) is fixed, with the
containing square $C = Q(c)$, $c = (c_x, c_y) \in [0, c_0]^2$, and the angles
$e$, $n$, $w$, $d$, $s$. We write

```math
W = Q_{\pi + w}(a_W, b_W), \qquad D = Q_{\pi + d}(a_D, b_D), \qquad S = Q_{3\pi/2 + s}(a_S, b_S)
```

for the charts in the ceiling of
[Proposition 9.22](09-six.md#proposition-922-labels), and $e^X_1$, $e^X_2$ for the
primary and secondary axes of a square $X$
([Definition 9.9](09-six.md#definition-99-squares-in-a-frame); Figure C.1). The
widths $\omega(\delta)$ and thresholds $\tau(\delta) = \frac12 + \omega(\delta)$
are those of Definition 9.9; for $0 \le \delta \le \frac\pi2$,

```math
\omega(\delta) = \tfrac12\left(\cos\delta + \sin\delta\right), \qquad \tau(\delta) = \tfrac12\left(1 + \cos\delta + \sin\delta\right),
```

and $\omega(\delta)$ does not change when $\delta$ is replaced by $-\delta$,
$\pi + \delta$ or $\frac\pi2 \pm \delta$
([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (2)). A unit vector $u(\theta)$
has the components $(\cos(\theta - t), \sin(\theta - t))$ in the frame of a
square of phase $t$.

![The model of six squares in its dashed circle of radius R6: the grey squares C, E, N and the coloured squares W (blue), D (purple, turned by 45 degrees) and S (green). At the centres of W, D and S the two axes of each frame are drawn as arrows: for W pointing left and down, for D down-left and down-right, for S down and right. Faint rays from the centre o mark the phases pi, 5 pi over 4 and 3 pi over 2. A blue dashed line runs along the lower side of W, touched by the top vertex of D, and a green dashed line along the left side of S, touched by the right vertex of D](figures/appendix-c/frames.svg)

*Figure C.1.* The model of [Theorem 9.1](09-six.md#theorem-91-six-squares), with the
frames of $W$, $D$ and $S$, of phases $\pi$, $\frac{5\pi}4$ and $\frac{3\pi}2$
(dotted rays). In a normalized packing these phases become $\pi + w$,
$\pi + d$ and $\frac{3\pi}2 + s$. The dashed lines are the two separations of
the model between the turned square $D$ and its neighbours: $W$ and $D$ along
$e^W_2$, and $D$ and $S$ along $e^S_2$, the *wings* of
[Definition 9.44](09-six.md#definition-944-wings).

**Facts from Chapter 9.** We use the following.

1. (Charts.) Each of the five charts has
   $\frac12 \le a \le \rho_0$, $|b| \le a$,
   $(a + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ and $a^2 + b^2 \le \rho_0^2$
   ([Lemma 9.10](09-six.md#lemma-910-charts-in-the-ceiling)), and moreover
   $a \ge a_0$, $|b| \le U_0$ and $|b| < \frac12$
   ([Lemma 9.16](09-six.md#lemma-916-the-core)); also
   $a + \frac{31}{100}(|b| + b^2) \le \rho_0$
   ([Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) (1)). These conditions
   involve $b$ only through $|b|$, so $(t, a, -b)$ is a chart in the ceiling
   whenever $(t, a, b)$ is.
2. (Angles.) $-\frac23 < w < \frac58$, $0 < d \le \frac\pi4$,
   $-\frac58 < s < \frac23$, and the phases increase in the order $W$, $D$, $S$:
   $w < d < \frac\pi2 + s$. $D$ is separated from $C$ along its own axis. As in
   Definition 9.34, $W$ is *on its matching side* if it is separated from $C$
   along the west side of $C$, and *on its own axis* otherwise, and then it is
   separated from $C$ along its own axis; likewise for $S$, with the south
   side. On its matching side, the angle of a square is less than $\frac25$ in
   absolute value ([Proposition 9.35](09-six.md#proposition-935-normalization),
   [Lemma 9.30](09-six.md#lemma-930-two-choices)).
3. (Constants.) By [Lemma 9.5](09-six.md#lemma-95-the-ceiling), $R_0 < 1.689$,
   $\rho_0 < \bar\rho = 1.11282 < 1.113$ and $c_0 < \bar c = 0.11282 < 0.113$, so
   that $\frac12 - c_0 > 0.38718 > 0.387$, $\frac12 + c_0 > 0.61$ and
   $\bar\rho = 1 + \bar c$; also $0.887 < a_0 < 0.888$ and $U_0 < 0.463$. We use
   $3.141592 < \pi < 3.141593$.

The one-variable tools of [Appendix A](appendix-a.md) are used throughout: the
Taylor bounds of [Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds), with
$\cos x \ge 1 - \frac{x^2}2$ for all $x$ and $x - \frac{x^3}6 \le \sin x \le x$
for $x \ge 0$; the brackets of
[Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets), whose values at the
angles we need are collected in Table C.1; and the concavity lemmas A.10 and
A.11 of [§A.4](appendix-a.md#a4-concave-functions-and-harmonics).

| $x$ | $\cos x$ | $\sin x$ |
| :-: | :-: | :-: |
| $\frac1{10}$ | $[0.99500, 0.99501]$ | $[0.09983, 0.09984]$ |
| $\frac25$ | $[0.92106, 0.92107]$ | $[0.38941, 0.38942]$ |
| $\frac12$ | $[0.87758, 0.87761]$ | $[0.47942, 0.47943]$ |
| $\frac23$ | $[0.78588, 0.78601]$ | $[0.61836, 0.61839]$ |
| $\frac9{10}$ | $[0.62159, 0.62234]$ | $[0.78332, 0.78343]$ |
| $\frac76$ | $[0.39313, 0.39664]$ | $[0.91943, 0.92002]$ |

*Table C.1.* Brackets of cosines and sines: the Taylor polynomials of degrees 6
and 4 for the cosine and of degrees 7 and 5 for the sine (Lemma A.8 with
$l = u = x$), rounded outward to five decimals.

## C.1 Proof of Lemma 9.37

We first write the separating inequalities of $W$, $D$ and $S$ in their
coordinates.

### Lemma C.1 (the margins of W, D and S)

Let $c = (c_x, c_y)$ and let $a$, $b$ be real numbers.

1. For $T = Q_{\pi + w}(a, b)$, the margins of $T$ against $C = Q(c)$ along its
   own axis and along the west side of $C$ are
   $m_{\mathrm{own}} = a + c_x\cos w + c_y\sin w - \tau(w)$ and
   $m_{\mathrm{west}} = c_x + a\cos w - b\sin w - \tau(w)$, and

   ```math
   m_{\mathrm{own}} - m_{\mathrm{west}} = (1 - \cos w)(a - c_x) + \sin w\,(b + c_y) .
   ```

2. For $T = Q_{3\pi/2 + s}(a, b)$, the margins along its own axis and along the
   south side of $C$ are $m_{\mathrm{own}} = a - c_x\sin s + c_y\cos s - \tau(s)$
   and $m_{\mathrm{south}} = c_y + a\cos s - b\sin s - \tau(s)$, and

   ```math
   m_{\mathrm{own}} - m_{\mathrm{south}} = (1 - \cos s)(a - c_y) + \sin s\,(b - c_x) .
   ```

3. In particular, for $0 \le x \le \frac\pi2$:

   ```math
   \begin{aligned}
   m_{\mathrm{own}}\left(Q_{\pi + x}(a, b)\right) &= a - \tfrac12 - \left(\tfrac12 - c_x\right)\cos x - \left(\tfrac12 - c_y\right)\sin x , \\
   m_{\mathrm{own}}\left(Q_{\pi - x}(a, b)\right) &= a - \tfrac12 - \left(\tfrac12 - c_x\right)\cos x - \left(\tfrac12 + c_y\right)\sin x , \\
   m_{\mathrm{west}}\left(Q_{\pi - x}(a, b)\right) &= a\cos x + b\sin x - \left(\tfrac12 - c_x\right) - \tfrac12\left(\cos x + \sin x\right) , \\
   m_{\mathrm{own}}\left(Q_{3\pi/2 + x}(a, b)\right) &= a - \tfrac12 - \left(\tfrac12 - c_y\right)\cos x - \left(\tfrac12 + c_x\right)\sin x , \\
   m_{\mathrm{south}}\left(Q_{3\pi/2 - x}(a, b)\right) &= a\cos x + b\sin x - \left(\tfrac12 - c_y\right) - \tfrac12\left(\cos x + \sin x\right) .
   \end{aligned}
   ```

*Proof.* In Definition 9.12 use $u(\pi + w) = (-\cos w, -\sin w)$,
$x_{\pi + w}(a, b) = -a\cos w + b\sin w$, $u(\frac{3\pi}2 + s) = (\sin s, -\cos s)$,
$y_{3\pi/2 + s}(a, b) = -a\cos s + b\sin s$, and $\tau(\pi + w) = \tau(w)$,
$\tau(\frac{3\pi}2 + s) = \tau(s)$. Subtracting gives the two differences. For
(3) put $w = \pm x$ or $s = \pm x$ and use
$\tau(\pm x) = \frac12 + \frac12(\cos x + \sin x)$. $\square$

*Lean:
[`Six.Normalization.centralMargin`](../../SquaresInCircles/Six/Normalization/Basic.lean#L284),
[`Six.Normalization.centralNormal`](../../SquaresInCircles/Six/Normalization/Basic.lean#L277),
[`Six.Normalization.own_sub_west_margin`](../../SquaresInCircles/Six/Normalization/Basic.lean#L296),
[`angularWidth_pi_add`](../../SquaresInCircles/Common/SeparatingAxes.lean#L261),
[`angularWidth_three_half_pi_add`](../../SquaresInCircles/Common/SeparatingAxes.lean#L270),
[`angularWidth_eq`](../../SquaresInCircles/Common/SeparatingAxes.lean#L253).*

The two differences correspond to each other under the reflection in the
diagonal, which exchanges $W$ and $S$ and $c_x$ and $c_y$, and replaces $w$ by
$-s$ and $b$ by $-b$.

### Lemma C.2 (the pairs W, D and D, S)

1. The phases of $W$ and $D$ differ by $q = d - w$, the threshold of the pair is
   $\tau(q)$, and

   ```math
   \left\langle e^W_2, c_D - c_W\right\rangle = a_D\sin q + b_D\cos q - b_W , \qquad
   \left\langle e^D_2, c_D - c_W\right\rangle = b_D + a_W\sin q - b_W\cos q .
   ```

2. The phases of $D$ and $S$ differ by $\frac\pi2 + s - d$, the threshold of the
   pair is $\tau(d - s)$, and

   ```math
   \left\langle e^D_2, c_S - c_D\right\rangle = a_S\cos(d - s) + b_S\sin(d - s) - b_D , \qquad
   \left\langle e^S_2, c_S - c_D\right\rangle = b_S + a_D\cos(d - s) - b_D\sin(d - s) .
   ```

*Proof.* These are the formulas of Lemma 9.11 for the phase gaps $d - w$ and
$\frac\pi2 + s - d$, with $\sin(\frac\pi2 + s - d) = \cos(d - s)$,
$\cos(\frac\pi2 + s - d) = \sin(d - s)$ and
$\tau(\frac\pi2 + s - d) = \tau(d - s)$. $\square$

*Lean:
[`pair_frameY_left`](../../SquaresInCircles/Common/SeparatingAxes.lean#L327),
[`pair_frameY_right`](../../SquaresInCircles/Common/SeparatingAxes.lean#L344),
[`oriented_pair_threshold`](../../SquaresInCircles/Common/SeparatingAxes.lean#L312),
[`Six.south_relative_width`](../../SquaresInCircles/Six/Separators/Walls.lean#L136).*

The heart of Lemma 9.37 is the following inequality between two projections of
the difference of two centres. When the phases of two squares $X$ and $Y$
differ by $q$, the inward primary axis $-e^X_1$ of the first square and the
secondary axis $e^Y_2$ of the second make the angle $\frac\pi2 - q$, and so do
$e^Y_1$ and $e^X_2$ (Figure C.2). Near $q = \frac\pi2$ the two axes of each
pair nearly agree, and for $q \le \frac{11}{10}$ the inward axis cannot
separate at all (Figure C.3).

![Two panels. (a) Two squares X (cyan) and Y (yellow) in the dashed circle of radius R0, with their phases marked by faint rays from the centre o that make the angle q; at the centre of each square the two axes of its frame are drawn as arrows, and a dotted line along the side of X facing Y separates the two squares. (b) The eight vectors plus and minus e1 and e2 of X and Y drawn from one point: e2 of X and e2 of Y bold black; minus e1 of X and e1 of Y orange, each a small angle away from one of the bold ones, the angles marked by small orange arcs; the other four grey, minus e2 of X and minus e2 of Y dashed](figures/appendix-c/eight.svg)

*Figure C.2.* Lemma 9.37 for two exterior squares $X = Q_t(a, b)$ and
$Y = Q_{t + q}(A, B)$ with $t = \pi + 0.4$ and the phase gap $q = 1.3$, at
$(a, b) = (1.02, -0.15)$ and $(A, B) = (1.02, 0.15)$. (a) The squares and their
frames; here they are separated along $e^X_2$ (dotted) and along $e^Y_2$.
(b) The eight vectors along which two squares can be separated, drawn from one
point. Part (2) of the lemma assumes that $-e^X_2$ and $-e^Y_2$ (grey, dashed)
do not separate, which the pins give for $W$, $D$ and for $D$, $S$; part (1)
excludes $e^X_1$ and $-e^Y_1$ (grey); and $-e^X_1$ and $e^Y_1$ (orange) make the
angle $\frac\pi2 - q$ with $e^Y_2$ and $e^X_2$ (bold), so that by Lemma C.3 a
separation along them is one along these secondary axes.

### Lemma C.3 (the dominance of the secondary axes)

Let $0 \le q \le \frac\pi2$, and let $a$, $b$, $A$, $B$ be real numbers with
$a \le \rho_0$, $A \ge a_0$, $|b| \le U_0$ and $|B| \le U_0$.

1. If $q \le \frac{11}{10}$, then $a - A\cos q + B\sin q < \tau(q)$.
2. If $a - A\cos q + B\sin q \ge \tau(q)$, then
   $B + a\sin q - b\cos q \ge \tau(q)$.

*Proof.* Here $\cos q, \sin q \ge 0$ and
$\tau(q) = \frac12 + \frac12(\cos q + \sin q)$.

(1) By Lemma A.7 (3) at $x = \frac{11}{10}$,

```math
\cos\tfrac{11}{10} \ge 1 - \tfrac{x^2}2 + \tfrac{x^4}{24} - \tfrac{x^6}{720} > 0.4535 > \tfrac9{20} ,
```

and the cosine decreases on $[0, \pi]$, so $\cos q \ge \frac9{20}$. With
$a \le \rho_0$, $A \ge a_0 = 2 - \rho_0$ and $B\sin q \le U_0\sin q$,

```math
\tau(q) - \left(a - A\cos q + B\sin q\right) \ge \tfrac12 - \rho_0 + \left(\tfrac52 - \rho_0\right)\cos q + \left(\tfrac12 - U_0\right)\sin q \ge \tfrac12 - \rho_0 + \tfrac9{20}\left(\tfrac52 - \rho_0\right) = \tfrac{13}8 - \tfrac{29}{20}\rho_0 ,
```

which is more than $1.625 - 1.45 \cdot 1.11282 > 0.0114$.

(2) By (1) we may assume $\frac{11}{10} < q \le \frac\pi2$. Put $k = \frac{13}{50}$.
The sine increases on $[0, \frac\pi2]$, so

```math
\sin q \ge \sin\tfrac{11}{10} \ge \tfrac{11}{10} - \tfrac16\left(\tfrac{11}{10}\right)^3 > 0.878 > \frac{1 - k^2}{1 + k^2} = 0.8733\ldots
```

Since $\cos^2 q = (1 - \sin q)(1 + \sin q)$,

```math
k^2\cos^2 q - (1 - \sin q)^2 = (1 - \sin q)\left((1 + k^2)\sin q - (1 - k^2)\right) \ge 0 ,
```

so $1 - \sin q \le k\cos q$, both sides being nonnegative. The difference of the
two projections is

```math
\left(B + a\sin q - b\cos q\right) - \left(a - A\cos q + B\sin q\right) = (A - b)\cos q - (a - B)(1 - \sin q) ,
```

and $A - b \ge a_0 - U_0 = 2 - \rho_0 - U_0$, $a - B \le \rho_0 + U_0$ and
$1 - \sin q \ge 0$. So the difference is at least

```math
\left(2 - \rho_0 - U_0\right)\cos q - \left(\rho_0 + U_0\right)k\cos q = \left(2 - \tfrac{63}{50}\left(\rho_0 + U_0\right)\right)\cos q \ge 0 ,
```

as $\frac{63}{50}(\rho_0 + U_0) < \frac{63}{50}(1.11282 + 0.463) < 1.986$. The
secondary projection is therefore at least the primary one, which is at least
$\tau(q)$. $\square$

*Lean:
[`Six.secondary_of_inward_primary`](../../SquaresInCircles/Six/Separators/Axes.lean#L115),
[`Six.nine_twentieths_le_cos`](../../SquaresInCircles/Six/Separators/Axes.lean#L86),
[`Six.one_sub_sin_le_cos`](../../SquaresInCircles/Six/Separators/Axes.lean#L96).*

![Graph over the phase gap q from 0 to pi over 2. An orange curve, the largest inward primary projection less the threshold, rises from about minus 0.77 at 0 and crosses zero at about q = 1.14, reaching about 0.58 at pi over 2. A blue curve, the least lead of the secondary projection over the inward primary one, rises from about minus 1.15 at 0, crosses zero near 1.05 and stays slightly above zero up to pi over 2, where it returns to zero. The band from 11/10 to pi over 2 is shaded](figures/appendix-c/dominance.svg)

*Figure C.3.* Lemma C.3. In orange, $p(q) - \tau(q)$, where
$p(q) = \rho_0 - a_0\cos q + U_0\sin q$ is the largest value of the inward
primary projection $a - A\cos q + B\sin q$ allowed by the hypotheses; it is
negative up to $q \approx 1.14$, so the inward axis separates only for larger
gaps. In blue, the least lead $\delta(q) = (a_0 - U_0)\cos q - (\rho_0 + U_0)(1 - \sin q)$
of the secondary projection over the inward primary one, nonnegative on
$[\frac{11}{10}, \frac\pi2]$ (shaded).

*Proof of Lemma 9.37.* Let $X = Q_t(a, b)$ and $Y = Q_{t'}(A, B)$ be two of the
five exterior squares, with $q = t' - t \in [0, \frac\pi2]$. By the facts above,
$a_0 \le a, A \le \rho_0$ and $|b|, |B| \le U_0$, and every centre lies within
$\rho_0$ of the origin.

(1) Since $c_X = a\,e^X_1 + b\,e^X_2$, we have $\langle e^X_1, c_X\rangle = a \ge a_0$
and $\langle e^X_1, c_Y\rangle \le |c_Y| \le \rho_0$, so

```math
\left\langle e^X_1, c_Y - c_X\right\rangle \le \rho_0 - a_0 = 2\rho_0 - 2 < \tfrac14 < \tau(q) ,
```

as $\tau(q) \ge 1$ (Lemma A.15 (2)). In the same way
$\langle -e^Y_1, c_Y - c_X\rangle = \langle e^Y_1, c_X\rangle - A \le \rho_0 - a_0 < \tau(q)$.

(2) By (1), the vectors other than $-e^X_2$ and $-e^Y_2$ along which $X$ and
$Y$ can be separated are $-e^X_1$, $e^X_2$, $e^Y_1$ and $e^Y_2$ (Figure C.2 (b)).
By Lemma 9.11,

```math
\left\langle -e^X_1, c_Y - c_X\right\rangle = a - A\cos q + B\sin q , \qquad \left\langle e^Y_2, c_Y - c_X\right\rangle = B + a\sin q - b\cos q ,
```

so by Lemma C.3 (2) a separation along $-e^X_1$ is one along $e^Y_2$. Likewise

```math
\left\langle e^Y_1, c_Y - c_X\right\rangle = A - a\cos q - b\sin q , \qquad \left\langle e^X_2, c_Y - c_X\right\rangle = -b + A\sin q + B\cos q ,
```

which are the two projections of Lemma C.3 for the numbers $A$, $-B$, $a$, $-b$
in place of $a$, $b$, $A$, $B$; so a separation along $e^Y_1$ is one along
$e^X_2$.

For $W$ and $D$ the phases differ by $d - w$, and
$0 < d - w < \frac\pi4 + \frac23 < \frac\pi2$.
By [Lemma 9.36](09-six.md#lemma-936-pins-orient-the-axes) (2), $W$ and $D$ are
separated along one of the eight vectors other than $-e^W_2$ and $-e^D_2$, hence,
by (2), along $e^W_2$ or $e^D_2$. If $s \le d$, the phases of $D$ and $S$ differ
by $\frac\pi2 + s - d \in (0, \frac\pi2]$, and by Lemma 9.36 (2) they are
separated along a vector other than $e^D_1$, $-e^D_2$ and $-e^S_2$; by (2), along
$e^D_2$ or $e^S_2$. $\square$

*Lean:
[`Six.normalized_outward_axes_excluded`](../../SquaresInCircles/Six/Separators/Axes.lean#L55),
[`Six.secondary_of_separating_axis`](../../SquaresInCircles/Six/Separators/Axes.lean#L147),
[`Six.westDiagonal_secondary`](../../SquaresInCircles/Six/Separators/Axes.lean#L189),
[`Six.south_secondary_choice_of_angle`](../../SquaresInCircles/Six/Separators/Axes.lean#L214),
[`Six.SouthSecondaryChoice`](../../SquaresInCircles/Six/Separators/Axes.lean#L207),
[`Six.frame_primary_le_rho0`](../../SquaresInCircles/Six/Separators/Axes.lean#L26),
[`Six.normalized_primary_lower`](../../SquaresInCircles/Six/Separators/Axes.lean#L45),
[`Six.normalized_center_radius`](../../SquaresInCircles/Six/Separators/Axes.lean#L37),
[`Six.pair_threshold_ge_half`](../../SquaresInCircles/Six/Separators/Axes.lean#L33).*

## C.2 Proof of Lemma 9.38

If $W$ is not separated from $C$ along the west side of $C$, it is separated
along its own axis. Suppose that its angle $w$ is not negative. If $w = 0$, the
two margins agree, which is impossible. If $w > 0$, $W$ is turned towards $D$,
and the two margins force it to sit low, in the way of $D$ (Figure C.4): its
transverse coordinate is bounded below (Lemma C.4). And $D$, on its own axis,
has a bounded transverse coordinate (Lemma C.5); the two bounds leave no room
for the separation of $W$ and $D$ along a secondary axis that Lemma 9.37
requires (Lemma C.6).

### Lemma C.4 (W on its own axis at a positive angle)

Let $0 < w \le \frac45$, and let $T = Q_{\pi + w}(a, b)$ satisfy
$m_{\mathrm{own}} \ge 0 > m_{\mathrm{west}}$ against $C = Q(c)$. Then

```math
b > -c_y - \tan\tfrac w2\,(a - c_x) .
```

*Proof.* By Lemma C.1 (1) and the identity
$1 - \cos w = \tan\frac w2\,\sin w$ of
[Lemma A.16](appendix-a.md#lemma-a16-half-angles) (2),

```math
0 < m_{\mathrm{own}} - m_{\mathrm{west}} = \sin w\left(\tan\tfrac w2\,(a - c_x) + b + c_y\right) ,
```

and $\sin w > 0$. $\square$

*Lean:
[`Six.own_west_transverse_lower`](../../SquaresInCircles/Six/Wings/WestSign.lean#L139).*

![Two panels, each with the grey central square C around the disk centre o, the dashed vertical line of the west side of C, a dashed blue line through a corner of C perpendicular to the own axis of W, and a dotted purple line through the lower left corner of C, beyond which D lies. W is drawn in outline where it touches the two dashed lines at that corner, and shaded where it has slid along the blue line, with an arrow. In panel (a), w = −0.3, the corner is the upper left one and W slides upwards, away from the purple pin of D below. In panel (b), w = 0.3, the corner is the lower left one and W slides downwards onto the pin of D, across the dotted purple line](figures/appendix-c/turn.svg)

*Figure C.4.* Lemma C.4, for $c = (c_0, c_0)$. A square $W$ at the angle $w$ that
touches both the line of the west side of $C$ and the line across which it is
separated along its own axis has a vertex at a corner of $C$ (outlined). To be
separated along its own axis but not along the west side, it must slide along
its own line past the west side (shaded): upwards, away from $D$, if $w < 0$
(a), and downwards, towards $D$ and its pin $p_D$, if $w > 0$ (b). The dotted
line is the line beyond which $D$ lies when it is separated from $C$ along its
own axis, drawn for $d = 0.65$.

### Lemma C.5 (the transverse coordinate of D)

Let $0 \le d \le \frac\pi4$, let $c_x, c_y \le c_0$, and let
$T = Q_{\pi + d}(a, b)$, for a chart in the ceiling, be separated from
$C = Q(c)$ along its own axis. Then

```math
|b| + \tfrac12\left(\cos d + \sin d\right) < \tfrac{97}{100} .
```

*Proof.* Put $v = \cos d + \sin d$; then $1 \le v \le \frac32$, since $v \ge 1$
by Lemma A.15 (2) and $v^2 = 1 + 2\sin d\cos d \le 2$. By Lemma C.1 (3),
$m_{\mathrm{own}} \ge 0$ gives, with $\cos d, \sin d \ge 0$ and $c_x, c_y < \bar c$,

```math
a \ge \tfrac12 + \left(\tfrac12 - c_x\right)\cos d + \left(\tfrac12 - c_y\right)\sin d \ge \tfrac12 + \alpha v , \qquad \alpha = \tfrac12 - \bar c = 0.38718 .
```

Suppose that $|b| \ge \frac{97}{100} - \frac v2$. Then $a + \frac12 \ge 1 + \alpha v$
and $|b| + \frac12 \ge \frac{147}{100} - \frac v2 > 0$, and writing $v = 1 + x$
with $0 \le x \le \frac12$,

```math
(1 + \alpha v)^2 + \left(\tfrac{147}{100} - \tfrac v2\right)^2 - Q_0 = 0.013988\ldots + 0.104176\ldots\,x + 0.399908\ldots\,x^2 > 0 ,
```

which contradicts $(a + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$. $\square$

*Lean:
[`Six.diagonal_transverse_profile`](../../SquaresInCircles/Six/Wings/WestSign.lean#L26).*

Figure C.12 (a) compares this bound (green) with the largest $|b|$ that the
disk allows.

### Lemma C.6 (two reserves)

Let $0 \le w \le d \le \frac\pi4$, $q = d - w$ and $k = \tan\frac w2$. Then

1. Against a separation along $e^W_2$:

   ```math
   \bar c + \bar\rho\left(\sin q + k\right) + \left(\tfrac{97}{100} - \tfrac12(\cos d + \sin d)\right)\cos q < \tau(q) ;
   ```

2. Against a separation along $e^D_2$:

   ```math
   \tfrac{97}{100} - \tfrac12(\cos d + \sin d) + \bar\rho\left(\sin q + k\cos q\right) + \bar c\cos q < \tau(q) .
   ```

*Proof.* As $d \le \frac\pi4 < \frac45$, Lemma A.16 applies to $d$ and to $w$, and
$0 \le q \le d$.

(1) The right side less the left side is

```math
\left(\tfrac12(\cos d + \sin d) - \tfrac{47}{100}\right)\cos q - \left(\bar\rho - \tfrac12\right)\sin q - \bar\rho k + \tfrac12 - \bar c .
```

By Lemma A.16 (1),
$\frac12(\cos d + \sin d) - \frac{47}{100} \ge \frac3{100} + \frac6{25}d \ge 0$,
and $\cos q \ge \cos d \ge 1 - \frac{d^2}2 \ge 0$. By Lemma A.16 (2),
$\bar\rho k \le \frac{11}{20}\bar\rho w \le (\bar\rho - \frac12)w$, as
$\frac{11}{20} \cdot 1.11282 = 0.612051 < 0.61282$; and $\sin q \le q$. So the
difference is at least

```math
\left(\tfrac3{100} + \tfrac6{25}d\right)\left(1 - \tfrac{d^2}2\right) - \left(\bar\rho - \tfrac12\right)(q + w) + \tfrac12 - \bar c = 0.41718 - 0.37282\,d - 0.015\,d^2 - 0.12\,d^3 ,
```

which decreases in $d \ge 0$ and is $0.047884$ at $d = \frac45$ (Figure C.5 (a)).

(2) By Lemma A.16 (3), $\sin q + k\cos q = \sin d - k\cos d$. With
$\bar\rho = 1 + \bar c$, the right side less the left side is the sum of

```math
\left(1 - \bar c\right)\cos d - \bar c\sin d - \tfrac{47}{100}
\qquad\text{and}\qquad
\left(\tfrac12 - \bar c\right)(\cos q - \cos d) + \tfrac12(\sin q - \sin d) + \bar\rho k\cos d ,
```

as one checks by expanding. For $0 \le d \le \frac45$,
$\cos d \ge 1 - \frac{d^2}2 \ge 1 - \frac25 d$ and $\sin d \le d$, so the first
term is at least $0.88718(1 - \frac25d) - 0.11282\,d - 0.47 = 0.41718 - 0.467692\,d \ge 0.043$.
For the second, Lemma A.16 (4) gives
$\cos q - \cos d \ge \frac{89}{200}(d^2 - q^2) = \frac{89}{200}w(d + q) \ge \frac{89}{200}wd$;
the mean value theorem gives $\sin d - \sin q \le d - q = w$; and Lemma A.16 (2)
gives $k \ge \frac w2$. So the second term is at least

```math
w\left(\tfrac{89}{200}\left(\tfrac12 - \bar c\right)d - \tfrac12 + \tfrac{\bar\rho}2\cos d\right) \ge w\left(0.172295\,d - 0.5 + 0.55641\left(1 - \tfrac25d\right)\right) = w\left(0.05641 - 0.050269\,d\right) \ge 0
```

for $d \le \frac45$ (Figure C.5 (b)). $\square$

*Lean:
[`Six.west_secondary_reserve`](../../SquaresInCircles/Six/Wings/WestSign.lean#L64),
[`Six.diagonal_secondary_reserve`](../../SquaresInCircles/Six/Wings/WestSign.lean#L93),
[`halfRatio_upper`](../../SquaresInCircles/Common/Trigonometry.lean#L680),
[`halfRatio_lower`](../../SquaresInCircles/Common/Trigonometry.lean#L650),
[`halfRatio_shift`](../../SquaresInCircles/Common/Trigonometry.lean#L709),
[`cosine_difference_lower`](../../SquaresInCircles/Common/Trigonometry.lean#L694),
[`small_polynomial_trig`](../../SquaresInCircles/Common/Trigonometry.lean#L621).*

![Two graphs over d from 0 to pi over 4. In each, a light blue band, whose lower edge is a blue curve labelled w = 0, falls from about 0.42 at d = 0 to between about 0.12 and 0.16 in (a) and between about 0.08 and 0.17 in (b) at pi over 4; a dashed orange curve below the band falls from 0.42 to 0.057 in (a) and to 0.050 in (b), where it ends in a marked dot](figures/appendix-c/reserves.svg)

*Figure C.5.* The reserves of Lemma C.6: the right side less the left side of
(1) in (a) and of (2) in (b), for $0 \le w \le d \le \frac\pi4$. For each $d$
they fill the shaded band as $w$ runs over $[0, d]$, and they are least at
$w = 0$ (blue). The bounds of the proof (dashed),
$0.41718 - 0.37282\,d - 0.015\,d^2 - 0.12\,d^3$ and $0.41718 - 0.467692\,d$,
stay below them and above $0.04$.

*Proof of Lemma 9.38.* By Lemma 9.30 (2), $W$ is separated from $C$ along its
own axis: $m_{\mathrm{own}}(W) \ge 0 > m_{\mathrm{west}}(W)$. Suppose that
$w \ge 0$. If $w = 0$, then $m_{\mathrm{own}}(W) = m_{\mathrm{west}}(W)$ by
Lemma C.1 (1), a contradiction. So $0 < w < d \le \frac\pi4$. Put $q = d - w$,
so that $0 < q \le \frac\pi4$, and $k = \tan\frac w2 \ge 0$.

By Lemma C.4, and as $c_x \ge 0$, $c_y \le \bar c$ and $a_W \le \rho_0 < \bar\rho$,

```math
-b_W < c_y + k\left(a_W - c_x\right) \le \bar c + \bar\rho k . \tag{C.1}
```

By Lemma C.5, applied to $D$, which is separated from $C$ along its own axis,
$b_D \le |b_D| < \frac{97}{100} - \frac12(\cos d + \sin d)$.

By Lemma 9.37, $W$ and $D$ are separated along $e^W_2$ or along $e^D_2$, with the
threshold $\tau(q)$ (Lemma C.2 (1)). Along $e^W_2$, with $a_D \le \bar\rho$,
$\sin q \ge 0$, $\cos q > 0$ and (C.1),

```math
a_D\sin q + b_D\cos q - b_W < \bar\rho\sin q + \left(\tfrac{97}{100} - \tfrac12(\cos d + \sin d)\right)\cos q + \bar c + \bar\rho k ,
```

which is less than $\tau(q)$ by Lemma C.6 (1). Along $e^D_2$, by the first
inequality of (C.1),

```math
b_D + a_W\sin q - b_W\cos q < \tfrac{97}{100} - \tfrac12(\cos d + \sin d) + a_W\left(\sin q + k\cos q\right) + \left(c_y - kc_x\right)\cos q ,
```

and $a_W(\sin q + k\cos q) \le \bar\rho(\sin q + k\cos q)$ and
$c_y - kc_x \le \bar c$, so this is less than $\tau(q)$ by Lemma C.6 (2). Both
separations fail, a contradiction; hence $w < 0$. $\square$

*Lean:
[`Six.own_west_negative`](../../SquaresInCircles/Six/Wings/WestSign.lean#L218),
[`Six.west_nonnegative_impossible`](../../SquaresInCircles/Six/Wings/WestSign.lean#L170),
[`Six.west_coarse_transverse`](../../SquaresInCircles/Six/Wings/WestSign.lean#L156),
[`Six.diagonal_transverse_profile`](../../SquaresInCircles/Six/Wings/WestSign.lean#L26).*

## C.3 Proof of Proposition 9.39

Suppose that $d \le \frac12$. We show that $W$, $C$ and $D$ cannot then be
separated as they must, by a stress on these three squares with three edges:
from $C$ to $W$, from $C$ to $D$, and from $W$ to $D$ along the secondary axis
that separates them. The weights depend on whether $W$ is on its own axis or on
the west side of $C$, and on which secondary axis separates $W$ and $D$.

**The slack of a stress.** For a stress on squares with centres $c_k$
([Definition 9.23](09-six.md#definition-923-stress)), we call

```math
\sigma = \sum_e \lambda_e\tau_e - \sum_k \left\langle F_k, c_k\right\rangle
```

its *slack*. If the squares are separated by the stress, then
$\sum_e \lambda_e\tau_e \le \sum_e \lambda_e\langle n_e, c_{U_j} - c_{U_i}\rangle$,
which equals $\sum_k \langle F_k, c_k\rangle$ by
[Lemma 9.24](09-six.md#lemma-924-balance) with $o$ the origin; so $\sigma \le 0$.
In each case below we show $\sigma > 0$, bounding the works
$\langle F_k, c_k\rangle$ above by the supports of the squares in the disk. The
work of a force with the components $U$, $V$ in the frame of $Q_t(a, b)$ is
$Ua + Vb$ ([Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk)), and
we use the supports in the following form.

### Lemma C.7 (supports with decimal constants)

Let $(t, a, b)$ be a chart in the ceiling and $U$, $V$, $L$ real numbers.

1. (The far vertex.) If $V \ge 0$, $L \ge 0$ and $U^2 + V^2 \le L^2$, then
   $Ua - Vb$ and $Ua + Vb$ are at most $1.689L - \frac12(U + V)$.
2. (The cap.) If $U, V \ge 0$ and $(\rho_0 + \frac12)V \le \frac12U$, then
   $Ua - Vb$ and $Ua + Vb$ are at most $1.113\,U$.
3. (The centre.) $Ua + Vb \le 1.113\sqrt{U^2 + V^2}$.
4. (The box.) If $c \in [0, c_0]^2$, $X, Y \ge 0$, $g_x \le X$ and $g_y \le Y$,
   then $g_xc_x + g_yc_y \le 0.113\,(X + Y)$.

*Proof.* This is [Lemma B.16](appendix-b.md#lemma-b16-further-supports) (1),
(2) and (4), stated as used here. As $(t, a, -b)$ is also a chart in the
ceiling, it suffices to bound $Ua - Vb$ in (1) and (2), which are the second
claims of Lemma B.16 (1) and (2); (3) is the first claim of Lemma B.16 (2),
and (4) is Lemma B.16 (4). $\square$

*Lean:
[`Six.vertex_linear_upper`](../../SquaresInCircles/Six/Supports.lean#L44),
[`Six.local_vertex_support`](../../SquaresInCircles/Six/Supports.lean#L28),
[`Six.cap_linear_upper`](../../SquaresInCircles/Six/Supports.lean#L101),
[`Six.chart_radial_work`](../../SquaresInCircles/Six/Supports.lean#L113),
[`Six.coarse_central_work`](../../SquaresInCircles/Six/Supports.lean#L253).*

### Lemma C.8 (three harmonics)

Let $K$, $A_v$, $B_v$, $A_d$, $B_d$, $A_q$, $B_q$ be real numbers with
$A_v \ge \frac1{10}$, $B_v \ge \frac16$, $A_d \ge \frac3{25}$,
$B_d \ge \frac3{25}$, $A_q \ge 0$ and $B_q \ge -\frac5{32}$, and put

```math
H(v, d) = K + A_v\cos v + B_v\sin v + A_d\cos d + B_d\sin d + A_q\cos(v + d) + B_q\sin(v + d) .
```

If $H$ is positive at the four corners of the rectangle
$[0, \frac23] \times [0, \frac12]$, it is positive on the whole rectangle.

*Proof.* Let $0 \le v \le \frac23$ and $0 \le d \le \frac12$. Then
$\cos v, \sin v \ge 0$, $\sin v \le \sin\frac23 \le 0.61839 < \frac58$,
$\cos d \ge 1 - \frac18 = \frac78$, $0 \le \sin d \le d \le \frac12$, and
$0 \le v + d \le \frac76 < \frac\pi2$, so that $\cos(v + d), \sin(v + d) \ge 0$.

For fixed $d$, expanding $\cos(v + d)$ and $\sin(v + d)$ shows that
$v \mapsto H(v, d)$ is a constant plus a first harmonic in $v$, whose harmonic
part is
$h_v = A_v\cos v + B_v\sin v + A_q\cos(v + d) + B_q\sin(v + d)$. Since
$\sin(v + d) = \sin v\cos d + \cos v\sin d \le \sin v + \frac12\cos v$,

```math
h_v \ge \tfrac1{10}\cos v + \tfrac16\sin v - \tfrac5{32}\left(\sin v + \tfrac12\cos v\right) = \tfrac7{320}\cos v + \tfrac1{96}\sin v \ge 0 .
```

So $v \mapsto H(v, d)$ is concave on $[0, \frac23]$ by
[Lemma A.11](appendix-a.md#lemma-a11-first-harmonics) (1). For fixed $v$, the
harmonic part in $d$ is
$h_d = A_d\cos d + B_d\sin d + A_q\cos(v + d) + B_q\sin(v + d)$, and
$\sin(v + d) \le \frac58\cos d + \sin d$, so

```math
h_d \ge \tfrac3{25}\cos d + \tfrac3{25}\sin d - \tfrac5{32}\left(\tfrac58\cos d + \sin d\right) \ge 0.0223\cos d - 0.0363\sin d \ge 0.0223\cdot\tfrac78 - 0.0363\cdot\tfrac12 > 0.001 ,
```

and $d \mapsto H(v, d)$ is concave on $[0, \frac12]$. Lemma A.10 (4) gives the
claim. $\square$

*Lean:
[`Six.threeHarmonics`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L26),
[`Six.threeHarmonics_positive`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L87),
[`Six.trig_sum_concave_of_nonnegative`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L32),
[`Six.compensated_v_curvature`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L52),
[`Six.compensated_d_curvature`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L68).*

### Proposition C.9 (W on its own axis)

If $W$ is on its own axis, that is, not separated from $C$ along the west side
of $C$, then $d > \frac12$.

*Proof.* Suppose that $d \le \frac12$. By Lemma 9.38, $w < 0$; put $v = -w$, so
that $0 < v < \frac23$ and $0 < d \le \frac12$, and $q = v + d$, the difference
of the phases of $W$ and $D$. By Lemma 9.37, $W$ and $D$ are separated along
$e^W_2$ or along $e^D_2$. Take the stress of Table C.2 (Figure C.6).

| edge | normal | threshold | weight, $W$–$D$ along $e^W_2$ | weight, $W$–$D$ along $e^D_2$ |
| :-: | :-: | :-: | :-: | :-: |
| $C \to W$ | $e^W_1$ | $\tau(v)$ | $\beta = \frac{44}{100}$ | $\beta = \frac{37}{100}$ |
| $C \to D$ | $e^D_1$ | $\tau(d)$ | $\alpha = \frac{31}{100}$ | $\alpha = \frac{42}{100}$ |
| $W \to D$ | $e^W_2$ or $e^D_2$ | $\tau(q)$ | $\mu = \frac{25}{100}$ | $\mu = \frac{21}{100}$ |

*Table C.2.* The stress at $D$ with $W$ on its own axis.

![Two panels with the grey central square C, the blue square W and the purple square D, inside a dashed arc of the circle of radius R0. In each panel W touches a dashed blue line through a corner of C, D touches a dashed purple line through another corner of C, and a dotted black line separates W and D: in (a) the line of the lower side of W, in (b) the line of the upper side of D. Orange arrows from the centres of W, D and C show the forces; those on W and D point roughly at their far vertices, which are marked in pink just outside the circle; the disk centre o lies in C](figures/appendix-c/own-stress.svg)

*Figure C.6.* The stress of Table C.2 at $v = d = 0.3$, with $C$ at the corner
$(c_0, c_0)$ of its box: (a) $W$ and $D$ along $e^W_2$, (b) along $e^D_2$. The
three separations of the stress hold with equality, the free transverse
coordinate being chosen to keep $W$ and $D$ as far inside as possible; still the
far vertices of $W$ and $D$ (pink) leave the disk of radius $R_0$. The forces
(orange, drawn at $1.25$ times their length) point roughly towards these
vertices.

The squares are separated by this stress: the first two edges are the
separations of $W$ and $D$ from $C$ along their own axes
(Definition 9.12), and the third is the separation of $W$ and $D$. The
weights add up to $\alpha + \beta + \mu = 1$. As $e^W_2 = u(t_W + \frac\pi2)$ has
the components $(\sin q, \cos q)$ in the frame of $D$, and $e^D_2$ has the
components $(-\sin q, \cos q)$ in the frame of $W$, the forces are, in the frames
of $W$ and $D$,

```math
\begin{aligned}
&\text{along } e^W_2: & F_W &= (\beta, -\mu), & F_D &= (\alpha + \mu\sin q, \mu\cos q), \\
&\text{along } e^D_2: & F_W &= (\beta + \mu\sin q, -\mu\cos q), & F_D &= (\alpha, \mu),
\end{aligned}
```

and in both cases

```math
F_C = -\beta e^W_1 - \alpha e^D_1 = \left(\beta\cos v + \alpha\cos d,\ \alpha\sin d - \beta\sin v\right) .
```

We call the *carrier* of the stress the square whose secondary axis is the
normal of the edge $W \to D$: $W$ along $e^W_2$, and $D$ along $e^D_2$. The
force on the carrier is constant in its frame, of length
$\sqrt{0.44^2 + 0.25^2} = \sqrt{0.2561} < L_0 = 0.5061$ along $e^W_2$ and
$\sqrt{0.42^2 + 0.21^2} = \sqrt{0.2205} < L_0 = 0.4696$ along $e^D_2$. The force
on the other square turns with $q$: its squared length is
$\lambda^2 + \mu^2 + 2\lambda\mu\sin q$, where $\lambda$ is the weight of the
central edge of the other square ($\alpha$ along $e^W_2$, $\beta$ along $e^D_2$).

*The slack in the angles.* All three angles $v$, $d$, $q$ lie in
$[0, \frac\pi2]$, so the threshold sum is

```math
\tfrac12 + \tfrac\beta2(\cos v + \sin v) + \tfrac\alpha2(\cos d + \sin d) + \tfrac\mu2(\cos q + \sin q) .
```

Writing the works as $Ua + Vb$ and collecting the terms, the slack is
$\sigma = H(v, d)$ in the notation of Lemma C.8, with

```math
\begin{aligned}
A_v &= \beta\left(\tfrac12 - c_x\right), & B_v &= \beta\left(\tfrac12 + c_y\right), & A_d &= \alpha\left(\tfrac12 - c_x\right), & B_d &= \alpha\left(\tfrac12 - c_y\right),
\end{aligned}
```

and, along $e^W_2$, $K = \frac12 - \beta a_W - \alpha a_D + \mu b_W$,
$A_q = \mu(\frac12 - b_D)$, $B_q = \mu(\frac12 - a_D)$; along $e^D_2$,
$K = \frac12 - \beta a_W - \alpha a_D - \mu b_D$, $A_q = \mu(\frac12 + b_W)$,
$B_q = \mu(\frac12 - a_W)$. The bounds of Lemma C.8 hold: with $\beta \ge 0.37$,
$\alpha \ge 0.31$ and $\frac12 - c_x, \frac12 - c_y > 0.38718$, we have
$A_v > 0.143 > \frac1{10}$, $B_v \ge 0.185 > \frac16$,
$A_d, B_d > 0.31 \cdot 0.38718 > 0.12 = \frac3{25}$; $A_q \ge 0$ as $|b| < \frac12$;
and $B_q \ge 0.25(\frac12 - 1.11282) > -0.1533 > -\frac5{32}$. So it suffices
to show that $\sigma > 0$ at the four corners.

*The corners.* At the corners $(v, d) = (0, 0)$, $(0, \frac12)$ and
$(\frac23, 0)$, where $q = 0$, $\frac12$ and $\frac23$, we bound the work of the
carrier by Lemma C.7 (1) with $L_0$, the work of the other square by Lemma C.7
(1) with a decimal $L \ge \sqrt{\lambda^2 + \mu^2 + 2\lambda\mu\sin q}$, and the
work on $C$ by Lemma C.7 (4) with $X = \beta\cos v + \alpha\cos d$ and
$Y = \max(\alpha\sin d - \beta\sin v, 0)$. The parts $-\frac12(U + V)$ of the
two bounds add up to $-\frac12(1 + \mu(\cos q + \sin q))$, and so

```math
\sigma \ge P - 1.689\left(L_0 + L\right) - 0.113\,(X + Y), \qquad P = 1 + \tfrac\beta2(\cos v + \sin v) + \tfrac\alpha2(\cos d + \sin d) + \mu(\cos q + \sin q) . \tag{C.2}
```

At the corner $(\frac23, \frac12)$, where $q = \frac76$, the force on the other
square, $(\lambda + \mu\sin q, \pm\mu\cos q)$, satisfies the slope condition of
the cap (Figure C.7): $(\rho_0 + \frac12)\mu\cos\frac76 < 2\mu \cdot 0.39664$,
which is $0.19832$ along $e^W_2$ and $0.16659$ along $e^D_2$, while
$\frac12(\lambda + \mu\sin\frac76) \ge 0.26992$, respectively $0.28153$. With
Lemma C.7 (2) for this force, and $\lambda_C$ the weight of the central edge of
the carrier,

```math
\sigma \ge P' - \left(1.689L_0 + 1.113\lambda\right) - 0.113\,(X + Y), \qquad P' = \tfrac12\left(1 + \lambda_C + \mu\right) + \tfrac\beta2(\cos v + \sin v) + \tfrac\alpha2(\cos d + \sin d) + \tfrac\mu2\cos q - 0.613\mu\sin q . \tag{C.3}
```

Table C.3 lists the bounds, computed with the brackets of Table C.1, each
cosine and sine replaced by the end of its bracket that makes $P$ or $P'$
smaller and $X + Y$ larger. The squared lengths
$\lambda^2 + \mu^2 + 2\lambda\mu\sin q$ are at most $0.1586$, $0.232912$ and
$0.254450$ along $e^W_2$, and $0.181$, $0.255503$ and $0.277098$ along $e^D_2$,
below the squares of the listed $L$.

| $W$–$D$ along | $(v, d)$ | $L$ | $P$ or $P'$ $\ge$ | work $\le$ | $0.113(X + Y) \le$ | $\sigma \ge$ |
| :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $e^W_2$ | $(0, 0)$ | $0.3983$ | $1.625$ | $1.527532$ | $0.08475$ | $0.012718$ |
| $e^W_2$ | $(0, \frac12)$ | $0.4827$ | $1.769585$ | $1.670084$ | $0.097258$ | $0.002243$ |
| $e^W_2$ | $(\frac23, 0)$ | $0.5046$ | $1.814992$ | $1.707073$ | $0.074111$ | $0.033808$ |
| $e^W_2$ | $(\frac23, \frac12)$ | cap | $1.272415$ | $1.199833$ | $0.069824$ | $0.002758$ |
| $e^D_2$ | $(0, 0)$ | $0.4255$ | $1.605$ | $1.511824$ | $0.08927$ | $0.003906$ |
| $e^D_2$ | $(0, \frac12)$ | $0.5056$ | $1.75494$ | $1.647113$ | $0.106216$ | $0.001611$ |
| $e^D_2$ | $(\frac23, 0)$ | $0.5265$ | $1.764674$ | $1.682413$ | $0.080324$ | $0.001937$ |
| $e^D_2$ | $(\frac23, \frac12)$ | cap | $1.282598$ | $1.204965$ | $0.074515$ | $0.003118$ |

*Table C.3.* The slack of the stress of Table C.2 at the corners of
$[0, \frac23] \times [0, \frac12]$, by (C.2), and by (C.3) at the corner
$(\frac23, \frac12)$; the work is $1.689(L_0 + L)$, respectively
$1.689L_0 + 1.113\lambda$.

![Two panels in the plane of the components U (horizontal) and V (vertical) of a force. In each, a blue arc shows the force on the other square as q runs from 0 to 7/6, with dots at q = 0, 1/2, 2/3 and 7/6: it starts at about (0.31, 0.25) in (a) and (0.37, 0.21) in (b) and turns down towards the U axis; the last dot lies in the shaded cone below a dashed line through the origin, labelled cap](figures/appendix-c/turning.svg)

*Figure C.7.* The force on the other square in the stress of Table C.2,
$(\lambda + \mu\sin q, \pm\mu\cos q)$ in its frame (drawn with the sign $+$),
as $q = v + d$ runs from $0$ to $\frac76$: (a) on $D$, with
$\lambda = \alpha = 0.31$ and $\mu = 0.25$, when $W$ and $D$ are separated along
$e^W_2$; (b) on $W$, with $\lambda = \beta = 0.37$ and $\mu = 0.21$, along
$e^D_2$. The force turns towards the primary axis as $q$ grows. At
$q = \frac76$, the corner $(\frac23, \frac12)$, it lies in the cone
$V \le U/(2\rho_0 + 1)$ of the cap bound (shaded); at the other corners its
length is at most the $L$ of Table C.3.

So $\sigma > 0$ at the four corners, hence on the whole rectangle by Lemma C.8,
in both cases; but $\sigma \le 0$, as the squares are separated by the stress.
This contradiction proves $d > \frac12$. $\square$

*Lean:
[`Six.own_west_diagonal_gt_half`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L437),
[`Six.DiagonalAngle.Own.impossible`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L416),
[`Six.DiagonalAngle.Own.slack`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L149),
[`Six.DiagonalAngle.Own.slack_formula`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L158),
[`Six.DiagonalAngle.Own.slack_nonpositive`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L371),
[`Six.DiagonalAngle.Own.slack_positive`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L336),
[`Six.DiagonalAngle.Own.corners`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L323),
[`Six.DiagonalAngle.Own.vertex_endpoint_lower`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L171),
[`Six.DiagonalAngle.Own.cap_endpoint_lower`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L203),
[`Six.DiagonalAngle.Own.alpha`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L131),
[`Six.DiagonalAngle.Own.beta`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L132),
[`Six.DiagonalAngle.Own.mu`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L133),
[`Six.DiagonalAngle.Own.westForce`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L140),
[`Six.DiagonalAngle.Own.diagonalForce`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L144),
[`Six.DiagonalAngle.Own.sourceNorm`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L238),
[`Six.DiagonalAngle.Own.normZero`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L239),
[`Six.DiagonalAngle.Own.normHalf`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L240),
[`Six.DiagonalAngle.Own.normFar`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L241),
[`Six.rotating_norm_sq`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L120).*

### Proposition C.10 (W on the west side of C)

If $W$ is separated from $C$ along the west side of $C$, then $d > \frac12$.

*Proof.* Suppose that $d \le \frac12$. Then $|w| < \frac25$ and $w < d$, and
$q = d - w$ lies in $[0, \frac9{10}]$. By Lemma 9.37, $W$ and $D$ are separated
along $e^W_2$ or along $e^D_2$. Take the stress of Table C.4 (Figure C.8).

| edge | normal | threshold | weight, $W$–$D$ along $e^W_2$ | weight, $W$–$D$ along $e^D_2$ |
| :-: | :-: | :-: | :-: | :-: |
| $C \to W$ | $(-1, 0)$ | $\tau(w)$ | $\beta = \frac{40}{100}$ | $\beta = \frac{30}{100}$ |
| $C \to D$ | $e^D_1$ | $\tau(d)$ | $\alpha = \frac{35}{100}$ | $\alpha = \frac{43}{100}$ |
| $W \to D$ | $e^W_2$ or $e^D_2$ | $\tau(q)$ | $\mu = \frac{25}{100}$ | $\mu = \frac{27}{100}$ |

*Table C.4.* The stress at $D$ with $W$ on the west side of $C$.

![Two panels like those of Figure C.6, now with W turned by −0.2 and touching the dashed vertical blue line of the west side of C; D touches the dashed purple line through the lower left corner of C, and a dotted line separates W and D, along the lower side of W in (a) and the upper side of D in (b). Orange arrows show the forces on W, D and C; the far vertices of W and D, marked in pink, lie just outside the dashed circle](figures/appendix-c/west-stress.svg)

*Figure C.8.* The stress of Table C.4 at $w = -0.2$ and $d = 0.35$, drawn as in
Figure C.6: (a) along $e^W_2$, (b) along $e^D_2$. With all three separations at
equality, the far vertices of $W$ and $D$ leave the disk.

The first edge is the separation of $W$ from $C$ along the west side,
$m_{\mathrm{west}} \ge 0$. The normal $(-1, 0) = u(\pi)$ has the components
$(\cos w, -\sin w)$ in the frame of $W$, so the forces are

```math
\begin{aligned}
&\text{along } e^W_2: & F_W &= (\beta\cos w,\ -\beta\sin w - \mu), & F_D &= (\alpha + \mu\sin q,\ \mu\cos q), \\
&\text{along } e^D_2: & F_W &= (\beta\cos w + \mu\sin q,\ -\beta\sin w - \mu\cos q), & F_D &= (\alpha, \mu),
\end{aligned}
```

and $F_C = (\beta + \alpha\cos d,\ \alpha\sin d)$. Their squared lengths are
$\beta^2 + \mu^2 + 2\beta\mu\sin w$ for $F_W$ and
$\alpha^2 + \mu^2 + 2\alpha\mu\sin q$ for $F_D$ along $e^W_2$; along $e^D_2$,
$|F_D|^2 = 0.2578 < 0.51^2$, and
$|F_W|^2 = \beta^2 + \mu^2 + 2\beta\mu\sin d$, since
$\sin w\cos q + \cos w\sin q = \sin d$. Each squared length is of the form
$y = p^2 + r^2 + 2pr\sin x$, and by Lemma A.14 its root is at most
$(y + y_0)/(2\sqrt{y_0})$, the tangent of the square root at a point $y_0 > 0$,
an affine function of $\sin x$. We take $y_0 = (\frac{12}{25})^2$ for $F_W$ and
$y_0 = \frac14$ for $F_D$ along $e^W_2$, and $y_0 = (\frac9{20})^2$ for $F_W$
along $e^D_2$.

*A lower bound in the angles.* The threshold sum is

```math
\tfrac12 + \tfrac\beta2(\cos w + |\sin w|) + \tfrac\alpha2(\cos d + \sin d) + \tfrac\mu2(\cos q + \sin q) .
```

We bound the works on $W$ and $D$ by Lemma C.7 (1), with these tangent
majorants of the lengths; this needs the second components of $F_W$ to be at
most $0$ and those of $F_D$ at least $0$. The latter is clear, and for $F_W$ it
holds as $\sin w > -\frac25$ and $\cos q \ge 1 - \frac{81}{200} > \frac12$:
$\beta\sin w + \mu > -0.16 + 0.25$ along $e^W_2$ and
$\beta\sin w + \mu\cos q > -0.12 + 0.135$ along $e^D_2$. The work on $C$ is at
most $0.113(\beta + \alpha\cos d + \alpha\sin d)$ by Lemma C.7 (4). In both cases
the parts $-\frac12(U + V)$ add up to
$-\frac12(\beta\cos w + \beta\sin w + \alpha + \mu + \mu\sin q + \mu\cos q)$, and
with $\frac12 + \frac12(\alpha + \mu) - 0.113\beta = 1 - 0.613\beta$ we obtain

```math
\sigma \ge g(w, d) = K + f_W(w) + f_D(d) + f_Q(d - w) ,
```

where, writing $[x]_+ = \max(x, 0)$,

```math
\begin{aligned}
&\text{along } e^W_2: & K &= 0.7548, & f_W(w) &= 0.4\cos w + 0.4\left[\sin w\right]_+ - 1.689\,\tfrac{0.4529 + 0.2\sin w}{0.96}, \\
& & f_D(d) &= 0.13545\left(\cos d + \sin d\right), & f_Q(q) &= 0.25\left(\cos q + \sin q\right) - 1.689\left(0.435 + 0.175\sin q\right), \\
&\text{along } e^D_2: & K &= -0.04529, & f_W(w) &= 0.3\cos w + 0.3\left[\sin w\right]_+, \\
& & f_D(d) &= 0.16641\left(\cos d + \sin d\right) - 1.689\,\tfrac{0.3654 + 0.162\sin d}{0.9}, & f_Q(q) &= 0.27\left(\cos q + \sin q\right) .
\end{aligned}
```

Here $K = 1 - 0.613\beta$, less $1.689 \cdot 0.51$ along $e^D_2$;
$f_D(d) = 0.387\alpha(\cos d + \sin d)$ less the work bound of $F_W$ along $e^D_2$;
and the fractions are the tangent majorants, for instance

```math
\frac{0.4^2 + 0.25^2 + 2 \cdot 0.4 \cdot 0.25\sin w + (12/25)^2}{2 \cdot 12/25} = \frac{0.4529 + 0.2\sin w}{0.96} .
```

*Concavity.* On each side of $w = 0$, each of $f_W$, $f_D$, $f_Q$ is a
constant plus a first harmonic, and its harmonic part is nonnegative on the
interval that matters. For $f_W$ on $[-\frac25, 0]$ and on $[0, \frac25]$, the
harmonic part $\beta\cos w + B\sin w$ has $\beta\cos w \ge 0.92\beta$ and
$|B\sin w| \le 0.4|B|$, with $|B| \le 0.351875$ along $e^W_2$ and $|B| \le 0.3$
along $e^D_2$, so it is at least $0.92 \cdot 0.4 - 0.4 \cdot 0.351875 > 0$ and
$0.92 \cdot 0.3 - 0.4 \cdot 0.3 > 0$. For $f_D$ on $[0, \frac12]$, along $e^D_2$
the harmonic part is $0.16641\cos d - 0.13761\sin d$, at least
$0.16641 \cdot \frac78 - 0.13761 \cdot \frac12 > 0$. For $f_Q$ on
$[0, \frac9{10}]$, along $e^W_2$ it is
$0.25\cos q - 0.045575\sin q \ge 0.25 \cdot 0.595 - 0.045575 \cdot 0.9 > 0$,
using $\cos q \ge 1 - \frac{0.81}2$ and $\sin q \le q$. The other harmonic
parts have nonnegative coefficients. By Lemma A.11 (1) and Lemma A.10 (3), $g$ is
concave in $w$ for fixed $d$, and in $d$ for fixed $w$, as long as $d - w$ stays
in $[0, \frac9{10}]$.

*The domain.* The angles lie in the domain $-\frac25 \le w \le \frac25$,
$0 \le d \le \frac12$, $w \le d$ (Figure C.10). On the rectangle $w \le 0$,
where $[\sin w]_+ = 0$, $g$ is positive by Lemma A.10 (4) once it is positive at
$(-\frac25, 0)$, $(-\frac25, \frac12)$, $(0, 0)$ and $(0, \frac12)$. On the part
$w \ge 0$, a trapezoid, $g$ is concave along the edge $d = w$, where $f_Q(0)$ is
constant, so it is positive there once it is positive at $(0, 0)$ and
$(\frac25, \frac25)$; it is concave in $w$ along the edge $d = \frac12$, so it is
positive there once it is positive at $(0, \frac12)$ and $(\frac25, \frac12)$;
and for each $w \in [0, \frac25]$ it is concave in $d$ on $[w, \frac12]$, so it
is positive on the trapezoid. The two formulas agree at $w = 0$. So it suffices
to check the six vertices (Figure C.9).

![Two panels in the plane of w (horizontal) and d (vertical), each with the domain of Proposition C.10, from w = −2/5 to 2/5 and d from 0 to 1/2 with w at most d, split by a dashed segment at w = 0, and level lines of the lower bound g, labelled 0.02 to 0.06. In (a) the values fall towards the top of the segment w = 0, where the least value, about 0.0046, is marked at the vertex (0, 1/2); in (b) they fall towards the top left vertex (−2/5, 1/2), where the least value, about 0.0047, is marked](figures/appendix-c/west-bound.svg)

*Figure C.9.* The lower bound $g$ of Proposition C.10 on its domain, with the
exact cosines and sines: (a) for $W$ and $D$ separated along $e^W_2$, (b) along
$e^D_2$, with level lines at $0.01, 0.02, \dots, 0.06$. On each side of $w = 0$
(dashed) it is concave in each angle, and its least value, about $0.0046$ in
(a) and $0.0047$ in (b), is taken at a vertex.

| along | $K$ | $f_W(-\frac25)$ | $f_W(0)$ | $f_W(\frac25)$ | $f_D(0)$ | $f_D(\frac25)$ | $f_D(\frac12)$ | $f_Q(0)$ | $f_Q(\frac1{10})$ | $f_Q(\frac25)$ | $f_Q(\frac12)$ | $f_Q(\frac9{10})$ |
| :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $e^W_2$ | $0.7548$ | $-0.291374$ | $-0.396821$ | $-0.409657$ | $0.13545$ | $0.177503$ | $0.183805$ | $-0.484715$ | $-0.490516$ | $-0.522198$ | $-0.537171$ | $-0.615023$ |
| $e^D_2$ | $-0.04529$ | $0.276318$ | $0.3$ | $0.393141$ | $-0.519324$ | $-0.586049$ | $-0.605671$ | $0.27$ | $0.295604$ | $0.353826$ | $0.36639$ | $0.379325$ |

*Table C.5.* Lower bounds of the terms of $g$ at the angles of the vertices,
computed with the brackets of Table C.1 (each cosine and sine at the end of its
bracket that makes the term smaller) and rounded down.

| vertex $(w, d)$ | $q = d - w$ | $g \ge$, along $e^W_2$ | $g \ge$, along $e^D_2$ |
| :-: | :-: | :-: | :-: |
| $(-\frac25, 0)$ | $\frac25$ | $0.076678$ | $0.06553$ |
| $(-\frac25, \frac12)$ | $\frac9{10}$ | $0.032208$ | $0.004682$ |
| $(0, 0)$ | $0$ | $0.008714$ | $0.005386$ |
| $(0, \frac12)$ | $\frac12$ | $0.004613$ | $0.015429$ |
| $(\frac25, \frac25)$ | $0$ | $0.037931$ | $0.031802$ |
| $(\frac25, \frac12)$ | $\frac1{10}$ | $0.038432$ | $0.037784$ |

*Table C.6.* The lower bound $g$ at the six vertices: the sums of the entries of
Table C.5.

So $g > 0$ on the domain, and $\sigma \ge g > 0$, while $\sigma \le 0$. This
contradiction proves $d > \frac12$. $\square$

*Lean:
[`Six.cardinal_west_diagonal_gt_half`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L389),
[`Six.DiagonalAngle.Side.impossible`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L369),
[`Six.DiagonalAngle.Side.slack`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L229),
[`Six.DiagonalAngle.Side.slack_nonpositive`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L320),
[`Six.DiagonalAngle.Side.gap_le_slack`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L266),
[`Six.DiagonalAngle.Side.gap`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L74),
[`Six.DiagonalAngle.Side.signedGap`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L70),
[`Six.DiagonalAngle.Side.constant`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L54),
[`Six.DiagonalAngle.Side.westTerm`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L57),
[`Six.DiagonalAngle.Side.diagonalTerm`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L61),
[`Six.DiagonalAngle.Side.relativeTerm`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L65),
[`Six.DiagonalAngle.Side.westTerm_concave`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L85),
[`Six.DiagonalAngle.Side.diagonalTerm_concave`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L97),
[`Six.DiagonalAngle.Side.relativeTerm_concave`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L107),
[`Six.DiagonalAngle.Side.positive_of_vertices`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L155),
[`Six.DiagonalAngle.Side.vertices`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L190),
[`Six.DiagonalAngle.Side.gap_positive`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L212),
[`Six.DiagonalAngle.Side.side_force_norm`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L236),
[`Six.DiagonalAngle.Side.rotating_force_norm`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L240),
[`Six.rotTangent`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L26),
[`Six.rotTangent_bound`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L35).*

![Two panels in the plane of w (horizontal) and d (vertical), each showing the window of the angles as a dashed rectangle from w = −2/3 to 5/8 and d = 0 to pi over 4, with the band d above 1/2 shaded green. Panel (a), W on its own axis: the orange rectangle w from −2/3 to 0, d from 0 to 1/2, with two numbers at each corner. Panel (b), W on the west side: the orange domain w from −2/5 to 2/5, d from 0 to 1/2, w at most d, split by a dotted segment at w = 0, with two numbers at each of its six vertices. A legend above says that the upper, blue number is for W and D separated along the secondary axis of W, and the lower, purple one along that of D](figures/appendix-c/domains.svg)

*Figure C.10.* The domains of the two stresses in the plane of $w$ and $d$, with
the lower bounds of the slack at their vertices, from Tables C.3 and C.6: the
upper value (blue) for $W$ and $D$ separated along $e^W_2$, the lower one
(purple) along $e^D_2$. Both domains lie below the band $d > \frac12$ that
remains.

*Proof of Proposition 9.39.* If $W$ is separated from $C$ along the west side
of $C$, Proposition C.10 gives $d > \frac12$; otherwise $W$ is on its own axis,
and Proposition C.9 does. $\square$

*Lean:
[`Six.normalized_diagonal_gt_half`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L422),
[`Six.own_west_diagonal_gt_half`](../../SquaresInCircles/Six/Separators/DiagonalAngleOwn.lean#L437),
[`Six.cardinal_west_diagonal_gt_half`](../../SquaresInCircles/Six/Separators/DiagonalAngle.lean#L389).*

## C.4 Proof of Lemma 9.40

A separation from $C$ bounds the radial coordinate of a square below by a
function of its angle, a *profile*; the disk then bounds its transverse
coordinate.

### Lemma C.11 (a profile bounds the transverse coordinate)

Let $(t, a, b)$ be a chart in the ceiling, and let $L$ and $T$ be real numbers
with $0 \le L \le a + \frac12$, $T + \frac12 \ge 0$ and
$L^2 + (T + \frac12)^2 > Q_0$. Then $|b| < T$.

*Proof.* If $|b| \ge T$, then $a + \frac12 \ge L \ge 0$ and
$|b| + \frac12 \ge T + \frac12 \ge 0$, so
$(a + \frac12)^2 + (|b| + \frac12)^2 \ge L^2 + (T + \frac12)^2 > Q_0$, which
contradicts the chart condition (Figure C.11). $\square$

*Lean:
[`Six.transverse_lt_of_profile`](../../SquaresInCircles/Six/Separators/Profiles.lean#L29).*

![The plane of a + 1/2 (horizontal, 1.3 to 1.7) against |b| + 1/2 (vertical, 0.5 to 0.8): the dashed circle of radius R0 and the region inside it, shaded, where the far corners of the charts lie. An orange vertical line at a + 1/2 = L, about 1.525, and a dashed orange horizontal line at |b| + 1/2 = T + 1/2 = 0.725 meet on the circle, at a purple dot labelled d = 1/2; the part of the region right of the vertical line, shaded orange, lies below the horizontal line. A short purple curve runs from that dot, just outside the circle, to a second dot labelled d = pi over 4](figures/appendix-c/profile-chart.svg)

*Figure C.11.* Lemma C.11 for $D$ at $d = \frac12$, as used in Lemma 9.40 (1), in
the plane of $(a + \frac12, |b| + \frac12)$, where the charts in the ceiling lie
inside the circle of radius $R_0$ (shaded). The separation of $D$ from $C$
gives $a + \frac12 \ge L = L(\frac12) \approx 1.525$, and the corner
$(L, T + \frac12)$, with $T = T(\frac12) = \frac9{40}$, lies just outside the
circle; so the part of the disk right of $a + \frac12 = L$ (orange) lies below
$|b| + \frac12 = T + \frac12$. As $d$ runs from $\frac12$ to $\frac\pi4$, the
corner $(L(d), T(d) + \frac12)$ moves along the purple curve, outside the circle
all the way, which is $E(d) > 0$ in the proof below.

*Proof of Lemma 9.40.* (1) By Proposition 9.39, $\frac12 < d \le \frac\pi4$. $D$
is separated from $C$ along its own axis, so by Lemma C.1 (3), with
$\frac12 - c_x, \frac12 - c_y > 0.387$ and $\cos d, \sin d \ge 0$,

```math
a_D + \tfrac12 \ge 1 + \left(\tfrac12 - c_x\right)\cos d + \left(\tfrac12 - c_y\right)\sin d \ge L(d) = 1 + 0.387\left(\cos d + \sin d\right) .
```

The function $\cos d + \sin d$ is nondecreasing on $[0, \frac\pi4]$
(Lemma A.15 (3)), so
$\cos d + \sin d \ge \cos\frac12 + \sin\frac12 \ge 0.87758 + 0.47942 = 1.357$,
and $a_D \ge \frac12 + 0.387 \cdot 1.357 > 1.0251 > \frac{41}{40}$.

For the transverse coordinate, put $T(d) = \frac{31}{100} - \frac{17}{100}d$, which
is positive on $[\frac12, \frac\pi4]$, and

```math
E(d) = L(d)^2 + \left(T(d) + \tfrac12\right)^2 - Q_0 = 1 + 0.387^2\left(1 + \sin 2d\right) + 0.774\left(\cos d + \sin d\right) + \left(0.81 - 0.17\,d\right)^2 - Q_0 ,
```

using $(\cos d + \sin d)^2 = 1 + \sin 2d$. Its second derivative is

```math
E''(d) = -0.774\left(\cos d + \sin d\right) - 4 \cdot 0.387^2\sin 2d + 2 \cdot 0.17^2 \le -0.774 + 0.0578 < 0
```

on $[\frac12, \frac\pi4]$, so $E$ is concave there (Lemma A.10 (1)). At the ends,
with $\cos\frac12 + \sin\frac12 \ge 1.357007$ (the Taylor polynomials of degrees
6 and 7), $\sqrt2 \ge 1.414$ and $\pi < 3.141593$,

```math
E\left(\tfrac12\right) \ge 1.525161^2 + 0.725^2 - Q_0 > 0.00056 , \qquad E\left(\tfrac\pi4\right) \ge 1.547218^2 + 0.676482^2 - Q_0 > 0.00033 .
```

So $E > 0$ on $[\frac12, \frac\pi4]$ (Lemma A.10 (2)), and Lemma C.11 with
$L = L(d)$ and $T = T(d)$ gives $|b_D| < \frac{31}{100} - \frac{17}{100}d$,
which is less than $\frac{31}{100} - \frac{17}{200} = \frac9{40}$ as $d > \frac12$
(Figure C.12 (a)).

(2) Let $W$ be separated from $C$ along the west side, with $w = -v$ and
$0 \le v \le \frac25$. By Lemma C.1 (3),
$a_W\cos v + b_W\sin v \ge \frac12 - c_x + \frac12(\cos v + \sin v)$, and since
$a_W \ge \frac12$ and $\cos v \le 1$,
$a_W = a_W\cos v + a_W(1 - \cos v) \ge a_W\cos v + \frac12(1 - \cos v)$. Hence

```math
a_W + \tfrac12 \ge \tfrac32 - c_x + \left(\tfrac12 - b_W\right)\sin v .
```

Suppose that $-b_W \ge \frac{47}{100} - \frac23v$. Then
$\frac12 - b_W \ge \frac{97}{100} - \frac4{15} > \frac7{10}$, and
$\sin v \ge v - \frac{v^3}6 \ge \frac9{10}v$ as $v^2 \le \frac4{25}$; so
$(\frac12 - b_W)\sin v \ge \frac{63}{100}v \ge \frac v2$, and as
$\frac32 - c_x > 1.387$, $a_W + \frac12 \ge L = 1.387 + \frac v2$. With
$T = \frac{47}{100} - \frac23v$,

```math
L^2 + \left(T + \tfrac12\right)^2 - Q_0 = 0.013489 + 0.0936\ldots\,v + 0.694\ldots\,v^2 > 0 ,
```

and Lemma C.11 gives $|b_W| < T$, contradicting $-b_W \ge T$. So
$-b_W < \frac{47}{100} - \frac23v$ (Figure C.12 (b)).

(3) Let $W$ be separated from $C$ along its own axis, with $w = -v$ and
$0 \le v \le \frac12$. By Lemma C.1 (3), with $c_y \ge 0$ and
$\frac12 - c_x > 0.387$,
$a_W \ge \frac12 + 0.387\cos v + \frac12\sin v$, and by the Taylor bounds

```math
a_W + \tfrac12 \ge P(v) = 1 + 0.387\left(1 - \tfrac{v^2}2\right) + \tfrac12\left(v - \tfrac{v^3}6\right) = 1.387 + \tfrac v2 - 0.1935\,v^2 - \tfrac{v^3}{12} ,
```

which is positive. Put $T = \frac{233}{500} - \frac{73}{100}v$, so that
$T + \frac12 = 0.966 - 0.73v > 0$, and

```math
G(v) = P(v)^2 + \left(0.966 - 0.73\,v\right)^2 - Q_0 = 0.005745 - 0.02336\,v + 0.246131\,v^2 - 0.424666\ldots v^3 - 0.045891\ldots v^4 + 0.03225\,v^5 + \tfrac{v^6}{144} .
```

For $0 \le v \le \frac14$, use $v^3 \le \frac{v^2}4$, $v^4 \le \frac{v^2}{16}$ and
drop the last two terms: $G(v) \ge 0.005745 - 0.02336\,v + 0.13709\,v^2$, a
quadratic with the negative discriminant
$0.02336^2 - 4 \cdot 0.13709 \cdot 0.005745 < -0.0026$, hence positive. For
$\frac14 \le v \le \frac12$, put $y = \frac12 - v \in [0, \frac14]$; expanding,

```math
G = 0.000762\ldots + 0.107294\ldots y - 0.412882\ldots y^2 + 0.418462\ldots y^3 + 0.060775\ldots y^4 - 0.053083\ldots y^5 + \tfrac{y^6}{144} ,
```

and with $y^2 \le \frac y4$, $y^5 \le \frac y{256}$ and the terms in $y^3$,
$y^4$, $y^6$ dropped,
$G \ge 0.00076 + (0.10729 - \frac{0.41289}4 - \frac{0.05309}{256})y > 0.00076 + 0.0038\,y > 0$.
So $G > 0$ on $[0, \frac12]$, and Lemma C.11 gives
$|b_W| < \frac{233}{500} - \frac{73}{100}v$ (Figure C.12 (c)). $\square$

*Lean:
[`Six.normalized_diagonal_profile`](../../SquaresInCircles/Six/Separators/Profiles.lean#L229),
[`Six.normalized_diagonal_transverse_affine`](../../SquaresInCircles/Six/Separators/Profiles.lean#L255),
[`Six.normalized_diagonal_transverse_small`](../../SquaresInCircles/Six/Separators/Profiles.lean#L260),
[`Six.own_front_profile`](../../SquaresInCircles/Six/Separators/Profiles.lean#L133),
[`Six.diagonalCircleExcess`](../../SquaresInCircles/Six/Separators/Profiles.lean#L146),
[`Six.diagonalCircleExcess_concave`](../../SquaresInCircles/Six/Separators/Profiles.lean#L156),
[`Six.cardinal_west_negative_transverse`](../../SquaresInCircles/Six/Separators/Profiles.lean#L51),
[`Six.leftProfile`](../../SquaresInCircles/Six/Separators/Profiles.lean#L40),
[`Six.left_circle_obstruction`](../../SquaresInCircles/Six/Separators/Profiles.lean#L44),
[`Six.own_west_transverse_small_angle`](../../SquaresInCircles/Six/Separators/Profiles.lean#L103),
[`Six.wingFrontCubic`](../../SquaresInCircles/Six/Separators/Profiles.lean#L81),
[`Six.own_wing_profile_circle`](../../SquaresInCircles/Six/Separators/Profiles.lean#L88),
[`Six.transverse_lt_of_profile`](../../SquaresInCircles/Six/Separators/Profiles.lean#L29).*

![Three graphs. (a) Over d from 0 to pi over 4, a blue curve, the largest transverse coordinate of D allowed by the disk, falls from about 0.46 to about 0.18; above it a dashed green curve, 0.97 minus (cos d + sin d)/2, and on 1/2 to pi over 4 a dashed orange line, 0.31 minus 0.17 d, which the blue curve nearly touches at both ends. (b) Over v from 0 to 2/5, the largest value of minus b for W on the west side falls from about 0.46 to zero near 0.375, below the dashed line 47/100 minus 2v/3. (c) Over v from 0 to 1/2, the largest |b| for W on its own axis falls from about 0.46 to about 0.10, just below the dashed line 233/500 minus 73v/100 throughout](figures/appendix-c/profiles.svg)

*Figure C.12.* The bounds of Lemma 9.40 (dashed) against the exact profiles
(blue): the largest transverse coordinate that the separation from $C$ and the
disk allow, for $C$ at the least favourable corner of its box. (a) $D$, with
the bound of Lemma C.5 (green) and that of Lemma 9.40 (1) (orange); (b) $W$ on
the west side; (c) $W$ on its own axis, where the bound from the Taylor
polynomials is drawn dotted and can hardly be told apart. The bounds of (a) and
(c) are nearly sharp.

## C.5 Proof of Proposition 9.41

If $s \le d$, Lemma 9.37 applies. If $s > d$, then $s > \frac12$ by
Proposition 9.39, so $S$ is not on the south side of $C$, where $|s| < \frac25$:
$S$ is on its own axis. Then the phases of $D$ and $S$ differ by more than
$\frac\pi2$, and Lemma 9.37 does not apply; instead, the separations of $D$ and
$S$ from $C$ push their centres so far out that the two secondary projections
together exceed twice the threshold.

### Lemma C.12 (the coupled reserve)

For $\frac12 \le d \le s \le \frac23$, put

```math
\varrho(d, s) = 0.387\cos(s - d) + \sin s\cos d - 0.613\cos d - \left(0.557 + \tfrac{s - d}3\right)\sin s .
```

Then $\varrho(d, s) > 0$.

*Proof.* For $\frac12 \le x \le \frac23$ we have
$\cos x \ge \cos\frac23 \ge 0.78588 > \frac79$ and
$\sin x \ge \sin\frac12 \ge 0.47942 > \frac9{20}$.

(a) Fix $s$. Expanding $\cos(s - d)$,

```math
\varrho(d, s) = A(s)\cos d + B(s)\sin d + \tfrac{\sin s}3\,d - \left(0.557 + \tfrac s3\right)\sin s ,
```

with $A(s) = 0.387\cos s + \sin s - 0.613 > 0.387 \cdot \frac79 + \frac9{20} - 0.613 > 0.138$
and $B(s) = 0.387\sin s \ge 0$. By Lemma A.11 (1) and Lemma A.10 (3),
$d \mapsto \varrho(d, s)$ is concave on $[\frac12, s]$, so it suffices that
$\varrho(\frac12, s) > 0$ and $\varrho(s, s) > 0$.

(b) The edge $d = \frac12$: expanding $\cos(s - \frac12)$,

```math
f(s) = \varrho\left(\tfrac12, s\right) = A_1\cos s + B_1\sin s - 0.613\cos\tfrac12 - \tfrac{s - 1/2}3\sin s ,
```

with $A_1 = 0.387\cos\frac12 \ge 0$ and
$B_1 = 0.387\sin\frac12 + \cos\frac12 - 0.557 \ge 0$. Its second derivative,

```math
f''(s) = -A_1\cos s - B_1\sin s - \tfrac23\cos s + \tfrac{s - 1/2}3\sin s \le -\tfrac23\cdot\tfrac79 + \tfrac1{18} < 0 ,
```

is negative on $[\frac12, \frac23]$, so $f$ is positive there once
$\varrho(\frac12, \frac12)$ and $\varrho(\frac12, \frac23)$ are.

(c) The edge $d = s$:
$g(s) = \varrho(s, s) = 0.387 + \frac12\sin 2s - 0.613\cos s - 0.557\sin s$, and
since $1 \le 2s \le \frac43 < \frac\pi2$ gives $\sin 2s \ge \sin 1 \ge \frac56$,

```math
g''(s) = -2\sin 2s + 0.613\cos s + 0.557\sin s \le -\tfrac53 + 0.613 + 0.557 < 0 .
```

So $g$ is positive on $[\frac12, \frac23]$ once $\varrho(\frac12, \frac12)$ and
$\varrho(\frac23, \frac23)$ are.

(d) The vertices: with the brackets of Table C.1, so that
$\sin\frac12\cos\frac12 \ge 0.47942 \cdot 0.87758$, and with
$\cos\frac16 \ge 1 - \frac1{72}$,

```math
\varrho\left(\tfrac12, \tfrac12\right) > 0.0027 , \qquad \varrho\left(\tfrac12, \tfrac23\right) > 0.0075 , \qquad \varrho\left(\tfrac23, \tfrac23\right) > 0.0466
```

(Figure C.13). $\square$

*Lean:
[`Six.coupledOwnReserve`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L25),
[`Six.coupled_own_reserve_positive`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L162),
[`Six.coupled_formula`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L32),
[`Six.coupled_concave_d`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L45),
[`Six.coupled_left_concave`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L70),
[`Six.coupled_diagonal_concave`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L111),
[`Six.coupled_vertices`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L140),
[`Six.coupled_trig`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L39).*

![A triangle in the plane of d (horizontal) and s (vertical), with vertices (1/2, 1/2), (1/2, 2/3) and (2/3, 2/3), shaded green and crossed by curved level lines of the reserve, labelled 0.005, 0.01, 0.02, 0.03 and 0.04 where they meet the dashed diagonal s = d. The values are written at the vertices: about 0.0027 at (1/2, 1/2), 0.0076 at (1/2, 2/3) and 0.047 at (2/3, 2/3)](figures/appendix-c/overtake.svg)

*Figure C.13.* The reserve $\varrho$ of Lemma C.12 on the triangle
$\frac12 \le d \le s \le \frac23$, with its level lines at $0.005$, $0.01$,
$0.02$, $0.03$ and $0.04$ and its values at the vertices. It is least at the
vertex $(\frac12, \frac12)$.

### Lemma C.13 (the radial sum of D and S)

Let $\frac12 \le d \le s \le \frac23$, let $c_y \le c_0$, and let
$D = Q_{\pi + d}(a, b)$ and $S = Q_{3\pi/2 + s}(A, B)$, for charts in the ceiling,
be separated from $C = Q(c)$ along their own axes. Then
$a + A > 2.17 + \frac{s - d}3$.

*Proof.* By Lemma C.1 (3), the two separations read

```math
a \ge \tfrac12 + \left(\tfrac12 - c_x\right)\cos d + \left(\tfrac12 - c_y\right)\sin d , \qquad A \ge \tfrac12 + \left(\tfrac12 - c_y\right)\cos s + \left(\tfrac12 + c_x\right)\sin s .
```

Multiply the first by $\sin s \ge 0$ and the second by $\cos d \ge 0$ and add:
the terms in $c_x$ cancel, and

```math
a\sin s + A\cos d \ge \tfrac12\left(\sin s + \cos d\right) + \sin s\cos d + \left(\tfrac12 - c_y\right)\cos(s - d) \ge \tfrac12\left(\sin s + \cos d\right) + \sin s\cos d + 0.387\cos(s - d) .
```

Now $\cos d \ge 1 - \frac{d^2}2 \ge \frac79 > \frac23 \ge s \ge \sin s$ and
$A \le \rho_0 < 1.113$, so
$a\sin s + A\cos d \le (a + A)\sin s + 1.113(\cos d - \sin s)$. If
$a + A \le 2.17 + \frac{s - d}3$, combining the two bounds gives

```math
0 \le \left(2.17 + \tfrac{s - d}3\right)\sin s + 1.113\left(\cos d - \sin s\right) - \tfrac12\left(\sin s + \cos d\right) - \sin s\cos d - 0.387\cos(s - d) = -\varrho(d, s) ,
```

which contradicts Lemma C.12. $\square$

*Lean:
[`Six.coupled_own_radial_sum`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L195).*

### Lemma C.14 (the secondary sum)

Let $(t, a, b)$ and $(t', A, B)$ be charts in the ceiling, let
$0 \le r \le \frac16$, and let $a + A > 2.17 + \frac r3$. Then

```math
\left(A\cos r - B\sin r - b\right) + \left(B + a\cos r + b\sin r\right) > 1 + \cos r + \sin r .
```

*Proof.* Every chart in the ceiling has $3a + |b| < 3.34$: by Cauchy–Schwarz,

```math
3\left(a + \tfrac12\right) + \left(|b| + \tfrac12\right) \le \sqrt{10}\sqrt{\left(a + \tfrac12\right)^2 + \left(|b| + \tfrac12\right)^2} \le \sqrt{10Q_0} < 5.34 ,
```

since $10Q_0 = 28.5118 < 5.34^2$. Put $T = a + A$, $U = |b| + |B|$ and
$\delta = T - U - 2$. Then $U < 6.68 - 3T$, so
$\delta > 4T - 8.68 > \frac43 r$; also $2.17 < T \le 2\rho_0 < \frac94$. The
left side is $T\cos r + (B - b)(1 - \sin r) \ge T\cos r - U(1 - \sin r)$, and
one checks the identity

```math
T\cos r - U(1 - \sin r) - (1 + \cos r + \sin r) = (T - 1)(\cos r - 1) + (T - 3)\sin r + \delta(1 - \sin r) .
```

Here $(T - 1)(\cos r - 1) \ge -\frac54 \cdot \frac{r^2}2$,
$(T - 3)\sin r \ge -0.83\sin r \ge -0.83\,r$, and
$\delta(1 - \sin r) > \frac43 r(1 - \sin r) \ge \frac43 r(1 - r)$, as
$0 \le \sin r \le r < 1$. So the right side exceeds

```math
-\tfrac58 r^2 - 0.83\,r + \tfrac43 r - \tfrac43 r^2 \ge r\left(\tfrac12 - 2r\right) \ge 0 .
```

$\square$

*Lean:
[`Six.overtaking_secondary_sum`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L249),
[`Six.chart_three_radial_support`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L180).*

*Proof of Proposition 9.41.* If $s \le d$, $D$ and $S$ are separated along
$e^D_2$ or $e^S_2$ by Lemma 9.37. Let $s > d$. As explained above, $S$ is then
separated from $C$ along its own axis, and $r = s - d$ satisfies
$0 < r < \frac23 - \frac12 = \frac16$. By Lemma C.13, with $d > \frac12$ and
$s < \frac23$, $a_D + a_S > 2.17 + \frac r3$. By Lemma C.2 (2), with
$\cos(d - s) = \cos r$ and $\sin(d - s) = -\sin r$,

```math
\left\langle e^D_2, c_S - c_D\right\rangle = a_S\cos r - b_S\sin r - b_D , \qquad \left\langle e^S_2, c_S - c_D\right\rangle = b_S + a_D\cos r + b_D\sin r ,
```

and the threshold is $\tau(r) = \frac12(1 + \cos r + \sin r)$. By Lemma C.14 the
two projections add up to more than $2\tau(r)$, so one of them exceeds
$\tau(r)$. $\square$

*Lean:
[`Six.south_secondary_choice`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L347),
[`Six.overtaking_own_secondary_choice`](../../SquaresInCircles/Six/Separators/SouthPair.lean#L294),
[`Six.south_secondary_choice_of_angle`](../../SquaresInCircles/Six/Separators/Axes.lean#L214),
[`Six.SouthSecondaryChoice`](../../SquaresInCircles/Six/Separators/Axes.lean#L207).*

## C.6 Proof of Lemma 9.42

Part (1) says that the secondary axis of $D$ separates $D$ from a neighbour only
if their phases differ by more than $\frac\pi4$: for smaller gaps a square
outside the core cannot reach far enough along it. Part (2) is a stress with
four edges of weight 1, in which the two forces on $D$ cancel.

### Lemma C.15 (the secondary projection outside the core)

Let $(t, a, b)$ be a chart in the ceiling with $a \ge a_0$, and let
$0 \le q \le \frac\pi4$. Then

```math
a\sin q - b\cos q \le a_0\sin q + U_0\cos q .
```

*Proof.* Put $l = \frac52 - \rho_0 = a_0 + \frac12 \le a + \frac12$ and
$B_0 = U_0 + \frac12 = \sqrt{Q_0 - l^2}$ (Definition 9.4): the point $(l, B_0)$
is where the line $x = l$ meets the circle of radius $R_0$ (Figure C.14). As
$\sin q \le \sin\frac\pi4 < \frac34$,
$R_0\sin q < 1.689 \cdot \frac34 < 1.27 < 1.387 < l$. So
[Lemma B.16](appendix-b.md#lemma-b16-further-supports) (3), applied to the
chart $(t, a, -b)$ with $s = \sin q$ and $\gamma = \cos q$, gives
$a\sin q - b\cos q \le (l - \frac12)\sin q + (B_0 - \frac12)\cos q$, which is
the claim. $\square$

*Lean:
[`Six.core_secondary_projection`](../../SquaresInCircles/Six/Separators/SmallAngle.lean#L25),
[`Six.circle_support_above_primary`](../../SquaresInCircles/Six/Supports.lean#L134),
[`Six.disk_corner_support`](../../SquaresInCircles/Six/Supports.lean#L85).*

![The plane of a + 1/2 against |b| + 1/2: the dashed circle of radius R0, the vertical line a + 1/2 = l with l = a0 + 1/2, and between them the shaded region where the far corners of the charts with a at least a0 lie. At its corner (l, B0) on the circle, three orange arrows point straight up, up and to the right, and diagonally, all above a dotted ray along the radius through the corner; two dashed orange lines through the corner, a horizontal one labelled q = 0 and a falling diagonal one labelled q = pi over 4, leave the whole region below them](figures/appendix-c/core-support.svg)

*Figure C.14.* Lemma C.15 in the plane of $(a + \frac12, |b| + \frac12)$. The
charts in the ceiling with $a \ge a_0$ have this point in the shaded region,
right of the line $a + \frac12 = l$ and inside the circle of radius $R_0$. For
$0 \le q \le \frac\pi4$ the direction $(\sin q, \cos q)$ (arrows, for $q = 0$,
$\frac\pi8$ and $\frac\pi4$) lies above the radius through the corner
$(l, B_0)$ (dotted), as $R_0\sin q < l$; so
$(a + \frac12)\sin q + (|b| + \frac12)\cos q$ is largest on the region at
that corner, and its level lines through the corner (dashed, for $q = 0$ and
$q = \frac\pi4$) leave the whole region on one side.

### Lemma C.16 (small phase gaps)

Let $(t, a, b)$ be a chart in the ceiling with $a \ge a_0$, let
$0 \le q \le \frac\pi4$ and $z < \frac9{40}$. Then
$a\sin q - b\cos q + z < \tau(q)$.

*Proof.* By Lemma C.15 and $a_0 < 0.888$, $U_0 < 0.463$, the left side is less
than $0.888\sin q + 0.463\cos q + 0.225$. As $\sin q \le \cos q$ on
$[0, \frac\pi4]$ ([Lemma A.6](appendix-a.md#lemma-a6-sine-and-cosine-compared)
(1)) and $\sin q < \frac34$,

```math
\tau(q) - \left(0.888\sin q + 0.463\cos q + 0.225\right) = 0.275 - 0.388\sin q + 0.037\cos q \ge 0.275 - 0.351\sin q > 0.275 - 0.26325 > 0 .
```

$\square$

*Lean:
[`Six.diagonal_secondary_excluded`](../../SquaresInCircles/Six/Separators/SmallAngle.lean#L44).*

*Proof of Lemma 9.42 (1).* Let $W$ and $D$ be separated along $e^D_2$, and put
$q = d - w > 0$. By Lemma C.2 (1), $b_D + a_W\sin q - b_W\cos q \ge \tau(q)$.
As $a_W \ge a_0$ and $b_D \le |b_D| < \frac9{40}$
(Lemma 9.40 (1)), Lemma C.16 with $z = b_D$ shows that $q \le \frac\pi4$ is
impossible. So $d - w > \frac\pi4$, that is, $w < d - \frac\pi4$
(Figure C.15 (a)).

Let $D$ and $S$ be separated along $e^D_2$, and put
$q = \frac\pi2 + s - d > 0$, so that $\cos(d - s) = \sin q$ and
$\sin(d - s) = \cos q$. By Lemma C.2 (2),
$a_S\sin q + b_S\cos q - b_D \ge \tau(q)$. Lemma C.16 for the chart
$(t_S, a_S, -b_S)$ and $z = -b_D < \frac9{40}$ shows that $q \le \frac\pi4$ is
impossible. So $\frac\pi2 + s - d > \frac\pi4$, that is, $s > d - \frac\pi4$
(Figure C.15 (b)). $\square$

*Lean:
[`Six.westDiagonal_wall`](../../SquaresInCircles/Six/Separators/Walls.lean#L58),
[`Six.diagonalSouth_wall`](../../SquaresInCircles/Six/Separators/Walls.lean#L70),
[`Six.westDiagonal_gap_gt_quarter`](../../SquaresInCircles/Six/Separators/Walls.lean#L28),
[`Six.diagonalSouth_gap_gt_quarter`](../../SquaresInCircles/Six/Separators/Walls.lean#L42).*

![Two panels in the plane of the angles, d from 1/2 to pi over 4 horizontally. (a) The window of w, from −2/3 to 5/8, as a dashed rectangle, and the purple wall w = d minus pi over 4 rising from about −0.29 at d = 1/2 to the model point (pi over 4, 0); the region below the wall is shaded and labelled: W and D may be separated along the secondary axis of D. (b) The window of s, from −5/8 to 2/3, with the wall s = d minus pi over 4 and the region above it shaded and labelled: D and S may be separated along the secondary axis of D](figures/appendix-c/walls.svg)

*Figure C.15.* The walls of Lemma 9.42 (1) in the plane of the angles, for
$\frac12 < d \le \frac\pi4$. (a) $W$ and $D$ can be separated along $e^D_2$ only
below the wall $w = d - \frac\pi4$ (shaded); elsewhere they are separated along
$e^W_2$, the west wing. (b) $D$ and $S$ can be separated along $e^D_2$ only above
the wall $s = d - \frac\pi4$. The model lies on both walls.

For part (2) we need a lower bound for the *cost* of a square on its own axis
in a stress whose edges have weight 1: the part $\omega(q)$ of the threshold of
its edge to $D$ less the work of its force. If the square is separated from $D$
along $e^D_2$, that force is $(1, 0)$, from its own axis, plus $\pm e^D_2$,
which in its frame is $(1 + \sin q, \pm\cos q)$ for the phase gap $q$ to $D$.

### Lemma C.17 (the cost of a wing)

Let $(t, a, b)$ be a chart in the ceiling and $\frac12 \le q \le \pi - \frac12$,
and let $\hat q = \frac\pi2 - |q - \frac\pi2|$ be the angle $q$ folded at
$\frac\pi2$. Then

```math
\omega(q) - (1 + \sin q)\,a - (\cos q)\,b > -0.73 - 0.65\,\hat q \ge -0.73 - 0.65\,q .
```

*Proof.* The second inequality holds as $\hat q \le q$.

(a) Let $\frac12 \le q \le \frac\pi2$, so that $\hat q = q$ and
$\omega(q) = \frac12(\cos q + \sin q)$. If $q \le 1$: the force
$(1 + \sin q, \cos q)$ has the squared length $2 + 2\sin q$, and Lemma A.14 with
the tangent at $\frac{49}{16}$ gives
$\sqrt{2 + 2\sin q} \le \frac{2 + 2\sin q + 49/16}{7/2} = \frac{81}{56} + \frac47\sin q$.
By Lemma C.7 (1),

```math
(1 + \sin q)a + (\cos q)b \le 1.689\left(\tfrac{81}{56} + \tfrac47\sin q\right) - \tfrac12(1 + \sin q + \cos q) ,
```

so the left side plus $0.73 + 0.65q$ is at least

```math
k(q) = 0.65\,q + \cos q + \left(1 - 1.689\cdot\tfrac47\right)\sin q + 1.23 - 1.689\cdot\tfrac{81}{56} ,
```

that is, $k(q) = 0.65q + \cos q + 0.034857\ldots\sin q - 1.213017\ldots$. By
[Lemma A.5](appendix-a.md#lemma-a5-concave-trigonometric-sums), $k$ is
positive on $[\frac12, 1]$ once it is positive at the ends, and
$k(\frac12) \ge 0.325 + 0.87758 + 0.034857 \cdot 0.47942 - 1.213018 > 0.0062$
and $k(1) \ge 0.65 + 0.540277 + 0.034857 \cdot 0.841468 - 1.213018 > 0.0065$,
with $\cos 1 \ge 0.540277$ and $\sin 1 \ge 0.841468$ from the Taylor polynomials
of degrees 6 and 7.

If $1 \le q \le \frac\pi2$: then $\sin q \ge \sin 1 \ge \frac56$, so
$\cos q = \sqrt{1 - \sin^2 q} \le \frac{\sqrt{11}}6 < \frac59$, and
$(\rho_0 + \frac12)\cos q < 1.613 \cdot \frac59 < 0.897 < \frac{11}{12} \le \frac12(1 + \sin q)$.
By Lemma C.7 (2), $(1 + \sin q)a + (\cos q)b \le 1.113(1 + \sin q)$, so the left
side plus $0.73 + 0.65q$ is at least

```math
\ell(q) = 0.65\,q + \tfrac12\cos q - 0.613\sin q - 0.383 .
```

Put $y = q - \frac{13}{10} \in [-\frac3{10}, 0.28]$. Expanding $\cos$ and $\sin$
of $\frac{13}{10} + y$,

```math
\ell(q) = \ell\left(\tfrac{13}{10}\right) + \left(0.65 + t_B\right)y + t_A\left(\cos y - 1\right) + t_B\left(\sin y - y\right) ,
```

with $t_A = \frac12\cos\frac{13}{10} - 0.613\sin\frac{13}{10}$ and
$t_B = -\frac12\sin\frac{13}{10} - 0.613\cos\frac{13}{10}$. The Taylor
polynomials give $0.26730 \le \cos\frac{13}{10} \le 0.27401$ and
$0.96352 \le \sin\frac{13}{10} \le 0.96478$, hence
$t_A \le 0.137005 - 0.590637 < -\frac9{20}$,
$-0.66 < -0.650359 \le t_B \le -0.645614$, so $|0.65 + t_B| \le \frac1{200}$, and
$\ell(\frac{13}{10}) \ge 0.845 + 0.13365 - 0.591411 - 0.383 > \frac1{250}$.
Moreover $\cos y - 1 \le -\frac{y^2}5$ (Lemma A.15 (4)) and
$|\sin y - y| \le \frac{|y|^3}6 \le \frac{y^2}{12}$ (Lemma A.7), so

```math
\ell(q) \ge \tfrac1{250} - \tfrac{|y|}{200} + \tfrac9{20}\cdot\tfrac{y^2}5 - \tfrac{33}{50}\cdot\tfrac{y^2}{12} \ge \tfrac1{250} - \tfrac1{400} > 0 .
```

(b) Let $\frac\pi2 < q \le \pi - \frac12$. Apply (a) to $\pi - q$ and the chart
$(t, a, -b)$: as $\omega(\pi - q) = \omega(q)$, $\sin(\pi - q) = \sin q$ and
$\cos(\pi - q) = -\cos q$, the left side is unchanged, and
$\pi - q = \hat q$ (Figure C.16). $\square$

*Lean:
[`Six.secondary_cost_first_quadrant`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L135),
[`Six.secondary_cost_folded_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L167),
[`Six.secondary_cost_affine_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L188),
[`Six.foldedSecondaryAngle`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L160),
[`Six.foldedSecondaryAngle_le`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L162),
[`Six.secondaryCapLine`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L34),
[`Six.secondary_cap_line_expansion`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L57),
[`Six.secondary_cap_line_positive`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L67),
[`Six.sine_error_on_half`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L26),
[`Six.secondary_vertex_positive`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L102),
[`Six.secondary_cap_slope`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L116),
[`Six.secondary_tangent_constants`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L40).*

![Graph over q from 1/2 to pi minus 1/2, symmetric about pi over 2: a blue curve, the least cost of a wing less the folded line, with humps of height about 0.035 near 0.75 and pi minus 0.75, dips to about 0.005 near 1.3 and pi minus 1.3, and a peak of about 0.025 at pi over 2. Below it, dashed, the lower bounds of the proof: green from the far vertex on 1/2 to 1 and pi minus 1 to pi minus 1/2, and purple from the cap on 1 to pi minus 1, close to the blue curve there. All curves stay positive](figures/appendix-c/cost.svg)

*Figure C.16.* Lemma C.17: the cost
$\omega(q) - (1 + \sin q)a - (\cos q)b$, less the folded line
$-0.73 - 0.65\hat q$. In blue, the least cost over the charts in the
ceiling; dashed, the lower bounds of the proof, by the far vertex with the
tangent of the square root up to $q = 1$ (green) and by the cap from $1$ to
$\frac\pi2$ (purple), and their reflections. All are positive, those of the
proof by at least $0.004$.

### Lemma C.18 (wings along the sides of C)

Let $\frac12 \le d \le \frac\pi4$.

1. For $|x| \le \frac25$, $\frac12 + \omega(d) \le \omega(x) + \omega(d - x)$.
2. For every chart $(t, a, b)$ in the ceiling and all real $w$ and $s$,

   ```math
   \left(\cos w + \sin(d - w)\right)a - \left(\sin w + \cos(d - w)\right)b \le 2.226\cos\left(\tfrac\pi4 - \tfrac d2\right) , \qquad
   \left(\cos s + \cos(d - s)\right)a + \left(\sin(d - s) - \sin s\right)b \le 2.226\cos\tfrac d2 .
   ```

3. $2\cos(\frac\pi4 - \frac d2) + 2\cos\frac d2 \le 3.696$, and
   $\cos d + \sin d \ge \frac{27}{20}$.

*Proof.* (1) Let $x \ge 0$ and $y = d - x$; then $x, y \in [0, \frac\pi2]$, and
with $\cos d = \cos x\cos y - \sin x\sin y$, $\sin d = \sin x\cos y + \cos x\sin y$,

```math
2\left(\omega(x) + \omega(y) - \tfrac12 - \omega(d)\right) = \left(\cos x + \sin x - 1\right)(1 - \cos y) + \left(1 - \cos x + \sin x\right)\sin y \ge 0 ,
```

by Lemma A.15 (2) (Figure C.17). Let $x = -v$ with $0 < v \le \frac25$; then
$d + v \le \frac\pi2$ and

```math
2\left(\omega(v) + \omega(d + v) - \tfrac12 - \omega(d)\right) = \sin v\left(1 + \cos d - \sin d\right) - (1 - \cos v)\left(1 + \cos d + \sin d\right) .
```

Here $\cos d \ge \sin d$ (Lemma A.6 (1)) and
$\cos d + \sin d \le \sqrt2 < \frac32$, so the right side is at least
$\sin v - \frac52(1 - \cos v)$, and for $0 < v \le \frac25$

```math
\sin v - \tfrac52(1 - \cos v) \ge v - \tfrac{v^3}6 - \tfrac54v^2 = v\left(1 - \tfrac54v - \tfrac{v^2}6\right) \ge 0 .
```

(2) The two vectors have the squared lengths

```math
\begin{aligned}
\left(\cos w + \sin(d - w)\right)^2 + \left(\sin w + \cos(d - w)\right)^2 &= 2 + 2\sin d = 4\cos^2\left(\tfrac\pi4 - \tfrac d2\right) , \\
\left(\cos s + \cos(d - s)\right)^2 + \left(\sin(d - s) - \sin s\right)^2 &= 2 + 2\cos d = 4\cos^2\tfrac d2 ,
\end{aligned}
```

as $\cos w\sin(d - w) + \sin w\cos(d - w) = \sin d$ and
$\cos s\cos(d - s) - \sin s\sin(d - s) = \cos d$. Lemma C.7 (3) gives the
bounds, the cosines being positive.

(3) By the sum formula for cosines,
$2\cos(\frac\pi4 - \frac d2) + 2\cos\frac d2 = 4\cos\frac\pi8\cos(\frac\pi8 - \frac d2)$,
which is at most $4\cos\frac\pi8$, and
$\cos^2\frac\pi8 = \frac{2 + \sqrt2}4 < \frac{2 + 1.415}4 < 0.924^2$. And
$\cos d + \sin d \ge \cos\frac12 + \sin\frac12 > 1.357$ by Lemma A.15 (3).
$\square$

*Lean:
[`Six.cardinal_width_triangle`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L297),
[`Six.west_cardinal_secondary_work`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L407),
[`Six.south_cardinal_secondary_work`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L418),
[`Six.west_cardinal_secondary_norm`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L389),
[`Six.south_cardinal_secondary_norm`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L397),
[`Six.westRadialLength`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L364),
[`Six.southRadialLength`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L365),
[`Six.west_radial_length`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L367),
[`Six.south_radial_length`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L378),
[`Six.radial_length_sum_bound`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L441),
[`Six.eighth_cos_upper`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L430),
[`Six.high_diagonal_width_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L457).*

![Graph over x from minus 2/5 to 2/5 of omega(x) + omega(d − x) − 1/2 − omega(d) for d = 1/2 (blue) and d = pi over 4 (purple): both curves touch zero at x = 0, marked by a dot, and rise on both sides, to about 0.18 and 0.10 at x = −2/5; for negative x a dashed orange curve, labelled bound of the proof, lies just below the purple one](figures/appendix-c/widths.svg)

*Figure C.17.* Lemma C.18 (1): $\omega(x) + \omega(d - x) - \frac12 - \omega(d)$ for
$|x| \le \frac25$, at $d = \frac12$ (blue) and $d = \frac\pi4$ (purple). It
vanishes at $x = 0$, the angle of $W$ and $S$ in the model, and is positive
elsewhere; for $x = -v < 0$ the proof bounds it below by
$\frac v2(1 - \frac54v - \frac{v^2}6)$ (dashed).

### Lemma C.19 (the reserves of the double separation)

1. For $0 \le x \le \frac23$,
   $\kappa(x) = 0.387\cos x + 0.613\sin x - 0.65x \ge \kappa(\frac23) > 0.2498$.
2. For $\frac12 \le d \le \frac\pi4$,
   $\frac12(\cos d + \sin d) - 2.226\cos\frac d2 - 0.65d > -1.9$.
3. For $-\frac58 \le s \le \frac23$ and $\frac12 \le d \le \frac\pi4$,

   ```math
   1.657 - 0.325\pi + \tfrac12(\cos d + \sin d) - 2.226\cos\left(\tfrac\pi4 - \tfrac d2\right) + 0.387\cos s + \tfrac12|\sin s| + 0.113\sin s + 0.65\,|s - d| > 0 .
   ```

*Proof.* (1) $\kappa$ is a first harmonic with nonnegative coefficients less a
linear function, so it is concave on $[0, \frac\pi2]$ (Lemma A.11 (1), Lemma A.10
(3)), and on $[0, \frac23]$ it is least at an end: $\kappa(0) = 0.387$ and
$\kappa(\frac23) \ge 0.387 \cdot 0.78588 + 0.613 \cdot 0.61836 - \frac{0.65 \cdot 2}3 > 0.24985$.

(2) With $\cos d \ge 1 - \frac{d^2}2$, $\sin d \ge d - \frac{d^3}6$ and
$\cos\frac d2 \le 1 - \frac{d^2}8 + \frac{d^4}{384}$, the left side is at least

```math
-1.726 - 0.15\,d + 0.02825\,d^2 - \tfrac{d^3}{12} - 0.00579\ldots d^4 \ge -1.726 - 0.12 + 0.0070625 - 0.042667 - 0.002375 > -1.884
```

for $\frac12 \le d \le \frac45$.

(3) Put $P(x) = 0.387\cos x + 0.613\sin x$ and
$G(s) = 0.387\cos s + \frac12|\sin s| + 0.113\sin s$. On $[0, \frac\pi4]$,
$P(x) - 0.65x$ is nonincreasing and $P(x) + 0.65x$ nondecreasing, their
derivatives being at most $0.613 - 0.65 < 0$ and at least $-0.387 + 0.65 > 0$.
We first show that $G(s) + 0.65|s - d'| \ge P(d')$ for $0 \le d' \le \frac\pi4$.
If $s \ge 0$, then $s \le \frac23 < \frac\pi4$ and $G(s) = P(s)$; if $s \le d'$,
then $P(s) - 0.65s \ge P(d') - 0.65d'$, and if $s \ge d'$, then
$P(s) + 0.65s \ge P(d') + 0.65d'$. If $s < 0$, then
$G(s) = 0.387(\cos s + |\sin s|) \ge 0.387$ by Lemma A.15 (2), while
$P(d') - 0.65d' \le P(0) = 0.387$, so $G(s) + 0.65(d' - s) > P(d')$.

Let $K_W = 1.657 - 0.325\pi$ and
$M(d) = K_W + 0.887\cos d + 1.113\sin d - 2.226\cos(\frac\pi4 - \frac d2)$. If
$d \le \frac23$, the claim with $d' = d$ shows that the left side of (3) is at
least $M(d)$ (Figure C.18). By Lemma A.14 with the tangent at $\frac{49}{16}$,
$2\cos(\frac\pi4 - \frac d2) = \sqrt{2 + 2\sin d} \le \frac{81}{56} + \frac47\sin d$,
so $M(d) \ge K_W - 1.113 \cdot \frac{81}{56} + 0.887\cos d + 0.477\sin d$, a first
harmonic with nonnegative coefficients plus a constant, which is positive on
$[\frac12, \frac23]$ by Lemma A.11 (2): with $K_W > 0.635982$ and
$1.113 \cdot \frac{81}{56} = 1.609875$, its values at the ends are more than
$-0.973893 + 0.887 \cdot 0.87758 + 0.477 \cdot 0.47942 > 0.0332$ and
$-0.973893 + 0.887 \cdot 0.78588 + 0.477 \cdot 0.61836 > 0.0181$.

If $d > \frac23$, then $s \le \frac23 < d$ and
$|s - d| = (\frac23 - s) + (d - \frac23)$, and the claim with $d' = \frac23$ shows
that the left side of (3) is at least $K_W + N(d) + P(\frac23) - 0.65 \cdot \frac23$,
where $N(d) = \frac12(\cos d + \sin d) - 2.226\cos(\frac\pi4 - \frac d2) + 0.65d$.
On $[\frac23, \frac\pi4]$,

```math
N'(d) = \tfrac12(\cos d - \sin d) - 1.113\sin\left(\tfrac\pi4 - \tfrac d2\right) + 0.65 \ge 0.65 - 1.113\left(\tfrac\pi4 - \tfrac13\right) > 0 ,
```

so $N(d) \ge N(\frac23)$, and the bound is at least $M(\frac23) > 0$. $\square$

*Lean:
[`Six.ownWingCost`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L278),
[`Six.ownWingCost_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L282),
[`Six.southMixedDepth`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L464),
[`Six.south_mixed_depth_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L482),
[`Six.ownWingPotential`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L194),
[`Six.positiveWing`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L198),
[`Six.ownWingPotential_nonnegative_angle`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L200),
[`Six.ownWingPotential_negative_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L207),
[`Six.positiveWing_minus_antitone`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L220),
[`Six.positiveWing_plus_monotone`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L232),
[`Six.own_wing_penalty_lower`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L246),
[`Six.own_wing_penalty_endpoint`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L268),
[`Six.westMixedConstant`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L472),
[`Six.westMixedBase`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L474),
[`Six.westMixedDepth`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L477),
[`Six.west_mixed_base_positive`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L500),
[`Six.west_mixed_depth_monotone`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L515),
[`Six.west_cardinal_own_south_reserve`](../../SquaresInCircles/Six/Separators/WingCosts.lean#L541).*

![Two graphs. (a) Three curves against s from minus 5/8 to 2/3, for d = 1/2 (blue), 2/3 (green) and pi over 4 (purple), falling steeply from about 0.7 at minus 5/8 to a corner at s = 0 and then slowly to their least values, marked by dots: about 0.034 at s = 1/2 for d = 1/2, after which the blue curve rises again, and about 0.02 and 0.05 at s = 2/3 for the others. (b) Against d from 1/2 to pi over 4, the least value falls from about 0.034 to 0.019 at d = 2/3, marked by a dashed vertical line, and rises to about 0.047 at pi over 4; the dashed bound of the proof follows it closely up to 2/3 and stays at about 0.018 beyond](figures/appendix-c/double-reserve.svg)

*Figure C.18.* Lemma C.19 (3). (a) The left side against $s$, for
$d = \frac12$, $\frac23$ and $\frac\pi4$: it has corners at $s = 0$ and
$s = d$, and its least value (dots) is at $s = d$, or at $s = \frac23$ when
$d > \frac23$. (b) That least value against $d$ (blue), which is $M(d)$ up to
$d = \frac23$, and the bound of the proof (dashed): the tangent bound
$K_W - 1.113\cdot\frac{81}{56} + 0.887\cos d + 0.477\sin d$ up to $\frac23$, and
its value at $\frac23$ beyond.

*Proof of Lemma 9.42 (2).* Suppose that $W$ and $D$, and $D$ and $S$, are both
separated along $e^D_2$. Let $n_W$ be $(-1, 0)$ if $W$ is on the west side of
$C$ and $e^W_1$ if it is on its own axis, and $n_S$ be $(0, -1)$ or $e^S_1$ in the
same way; $W$ and $S$ are separated from $C$ along these normals.
Take the stress with four edges of weight 1: $C \to W$ along $n_W$ with the
threshold $\tau(w)$, $C \to S$ along $n_S$ with $\tau(s)$, $W \to D$ along $e^D_2$
with $\tau(d - w)$, and $D \to S$ along $e^D_2$ with $\tau(d - s)$
(Lemma C.2). The forces are

```math
F_W = n_W - e^D_2, \qquad F_S = n_S + e^D_2, \qquad F_D = e^D_2 - e^D_2 = 0, \qquad F_C = -n_W - n_S ,
```

and in the frames of $W$ and $S$, $-e^D_2$ has the components
$(\sin(d - w), -\cos(d - w))$ and $e^D_2$ the components
$(\cos(d - s), \sin(d - s))$; $n_W$ is $(\cos w, -\sin w)$ or $(1, 0)$, and
$n_S$ is $(\cos s, -\sin s)$ or $(1, 0)$. The slack is

```math
\sigma = 2 + \omega(w) + \omega(s) + \omega(d - w) + \omega(d - s) - \left\langle F_W, c_W\right\rangle - \left\langle F_S, c_S\right\rangle - \left\langle F_C, c\right\rangle \le 0 .
```

Here $\frac12 < d \le \frac\pi4$, and by part (1), $d - w > \frac\pi4$ and
$\frac\pi2 + s - d > \frac\pi4 > \frac12$. We show $\sigma > 0$ in each of the
four cases.

(a) $W$ and $S$ on their matching sides: $|w|, |s| < \frac25$, and
$F_C = (1, 1)$, whose work is $c_x + c_y < 0.226$. By Lemma C.18,
$\omega(w) + \omega(d - w) \ge \frac12 + \omega(d)$,
$\omega(s) + \omega(d - s) \ge \frac12 + \omega(d)$, and the works on $W$ and $S$
add up to at most $1.113 \cdot 3.696 = 4.113648$. With
$2\omega(d) = \cos d + \sin d \ge \frac{27}{20}$,

```math
\sigma > 3 + 1.35 - 4.113648 - 0.226 = 0.010352 > 0 .
```

(b) $W$ on its own axis, $S$ on the south side: $w = -v$ with $0 < v < \frac23$
(Lemma 9.38), and $|s| < \frac25$. The force on $W$ is $(1 + \sin q, -\cos q)$
in its frame, with $q = d + v \in [\frac12, \pi - \frac12]$, and Lemma C.17 for
the chart $(t_W, a_W, -b_W)$ gives
$\omega(q) - \langle F_W, c_W\rangle > -0.73 - 0.65(d + v)$. The force on $C$ is
$(\cos v, 1 - \sin v)$, with work at most $0.113(\cos v + 1 - \sin v)$, and
Lemma C.18 bounds the terms of $S$. With $\omega(-v) = \frac12(\cos v + \sin v)$,

```math
\sigma > 1.657 + \kappa(v) + \tfrac12(\cos d + \sin d) - 2.226\cos\tfrac d2 - 0.65\,d > 1.657 + 0.2498 - 1.9 > 0
```

by Lemma C.19 (1) and (2).

(c) $W$ on the west side, $S$ on its own axis: $|w| < \frac25$ and
$-\frac58 < s < \frac23$. The force on $S$ is $(1 + \sin q_S, \cos q_S)$ with
$q_S = \frac\pi2 + s - d \in [\frac12, \pi - \frac12]$, folded to
$\hat q_S = \frac\pi2 - |s - d|$; by Lemma C.17,
$\omega(q_S) - \langle F_S, c_S\rangle > -0.73 - 0.65(\frac\pi2 - |s - d|)$. The
force on $C$ is $(1 - \sin s, \cos s)$, with work at most
$0.113(1 - \sin s + \cos s)$, and Lemma C.18 bounds the terms of $W$. With
$\omega(s) = \frac12(\cos s + |\sin s|)$, $\sigma$ exceeds the left side of
Lemma C.19 (3), which is positive.

(d) Both on their own axes (Figure C.19): $0 < v < \frac23$ and
$-\frac58 < s < \frac23$. By
Lemma C.17 in its affine form, the two costs exceed $-0.73 - 0.65(d + v)$ and
$-0.73 - 0.65(\frac\pi2 + s - d)$, whose sum $-1.46 - 0.65(\frac\pi2 + v + s)$
does not depend on $d$. The force on $C$ is $(\cos v - \sin s, \cos s - \sin v)$,
whose components are nonnegative as $\cos v, \cos s \ge 1 - \frac29 = \frac79$
and $\sin v, \sin s \le \frac23$; its work is at most
$0.113(\cos v - \sin s + \cos s - \sin v)$. So

```math
\sigma > 0.54 - 0.325\pi + \kappa(v) + \left(\omega(s) - 0.113\cos s + 0.113\sin s - 0.65\,s\right) .
```

If $s \ge 0$, the bracket is $\kappa(s) \ge 0.2498$, and
$\sigma > 0.54 - 1.021018 + 2 \cdot 0.2498 > 0.0185$. If $s < 0$, the bracket
is $0.387(\cos s - \sin s) - 0.65s \ge 0.387$ by Lemma A.15 (2), and
$\sigma > 0.54 - 1.021018 + 0.2498 + 0.387 > 0.15$.

In every case $\sigma > 0$, a contradiction. $\square$

*Lean:
[`Six.not_both_diagonal_secondary`](../../SquaresInCircles/Six/Separators/Walls.lean#L280),
[`Six.doubleSecondaryGap`](../../SquaresInCircles/Six/Separators/Walls.lean#L90),
[`Six.doubleSecondaryGap_nonpositive`](../../SquaresInCircles/Six/Separators/Walls.lean#L100),
[`Six.doubleSecondaryGap_pos_side_side`](../../SquaresInCircles/Six/Separators/Walls.lean#L141),
[`Six.doubleSecondaryGap_pos_own_side`](../../SquaresInCircles/Six/Separators/Walls.lean#L160),
[`Six.doubleSecondaryGap_pos_side_own`](../../SquaresInCircles/Six/Separators/Walls.lean#L190),
[`Six.doubleSecondaryGap_pos_own_own`](../../SquaresInCircles/Six/Separators/Walls.lean#L222),
[`Six.wingBaseX`](../../SquaresInCircles/Six/Separators/Walls.lean#L84),
[`Six.wingBaseY`](../../SquaresInCircles/Six/Separators/Walls.lean#L85),
[`Six.south_relative_width`](../../SquaresInCircles/Six/Separators/Walls.lean#L136).*

![The double separation at D: the grey square C, the purple square D turned by 45 degrees below left of it, the blue square W above left and the green square S below right, in a dashed circle of radius R0. Two dashed purple lines extend the two sides of D parallel to its primary axis; W touches the upper one and S the lower one. Orange arrows at the centre of D point both ways along its secondary axis and cancel; orange arrows show the forces on W (up and left), S (down and right) and C; the far vertices of W and S, marked in pink, lie outside the circle](figures/appendix-c/double.svg)

*Figure C.19.* The stress of Lemma 9.42 (2) at $w = -0.35$, $d = \frac\pi4$ and
$s = 0.35$, with $W$ and $S$ on their own axes, $C$ at $(c_0, c_0)$, and all four
separations at equality. The two unit forces on $D$ cancel; the forces on $W$,
$S$ and $C$ are drawn at $0.42$ times their length, and the far vertices of $W$
and $S$ lie well outside the disk.

## C.7 Proof of Lemma 9.43

The first part is the counterpart of Lemma 9.38 for $S$, but not its mirror
image: the reflection in the diagonal turns $d$ into $\frac\pi2 - d$, outside
the range of §C.2. Its proof uses instead that $d > \frac12$ and the bounds of
Lemma 9.40 on $D$. The second part adds the separations of $W$ and $S$ from
$C$, which share the centre of $C$.

### Lemma C.20 (S on its own axis at a negative angle)

Let $0 < v \le \frac45$, and let $T = Q_{3\pi/2 - v}(a, b)$ satisfy
$m_{\mathrm{own}} \ge 0 > m_{\mathrm{south}}$ against $C = Q(c)$. Then

```math
b < c_x + \tan\tfrac v2\,(a - c_y) .
```

*Proof.* By Lemma C.1 (2) with $s = -v$, and Lemma A.16 (2),

```math
0 < m_{\mathrm{own}} - m_{\mathrm{south}} = (1 - \cos v)(a - c_y) - \sin v\,(b - c_x) = \sin v\left(\tan\tfrac v2\,(a - c_y) - (b - c_x)\right) ,
```

and $\sin v > 0$. $\square$

*Lean:
[`Six.own_south_transverse_upper`](../../SquaresInCircles/Six/Separators/Signs.lean#L163).*

*Proof of Lemma 9.43 (1).* By Lemma 9.30 (2), $S$ is separated from $C$ along
its own axis: $m_{\mathrm{own}}(S) \ge 0 > m_{\mathrm{south}}(S)$. Suppose that
$s \le 0$. If $s = 0$, the two margins agree by Lemma C.1 (2), which is
impossible. So $s = -v$ with $0 < v < \frac58$. By Proposition 9.39,
$\frac12 < d \le \frac\pi4$, and $\theta = d + v$ lies in $(\frac12, \frac\pi2)$,
as $\frac\pi4 + \frac58 < \frac\pi2$; so $\cos\theta \ge 0$ and
$\sin\theta \ge \sin\frac12 \ge \frac12 - \frac1{48} = \frac{23}{48}$. The phases of
$D$ and $S$ differ by $\frac\pi2 - \theta$, so by Lemma C.2 (2), with
$\cos(d - s) = \cos\theta$ and $\sin(d - s) = \sin\theta$,

```math
\left\langle e^D_2, c_S - c_D\right\rangle = a_S\cos\theta + b_S\sin\theta - b_D , \qquad \left\langle e^S_2, c_S - c_D\right\rangle = b_S + a_D\cos\theta - b_D\sin\theta ,
```

with the threshold $\tau(\theta) = \frac12(1 + \cos\theta + \sin\theta)$. By
Proposition 9.41, one of them is at least $\tau(\theta)$. Put
$k = \tan\frac v2$, so that $0 \le k \le \frac{11}{20} \cdot \frac58 < \frac12$ by
Lemma A.16 (2), and $U = \frac{31}{100} - \frac{17}{100}d \le \frac9{40}$, so that
$|b_D| < U$ by Lemma 9.40 (1).

*Along $e^D_2$.* Let $\gamma = \cos d - k\sin d \ge \cos d - \frac12\sin d \ge 0$.
The identities $k(1 + \cos v) = \sin v$ and $k\sin v = 1 - \cos v$
(Lemma A.16 (2)) give, for all real $x$ and $y$,

```math
x\cos\theta + y\sin\theta = \gamma\left(x\cos v + y\sin v\right) + \sin d\left(y - kx\right) . \tag{C.4}
```

By Lemma C.1 (3), $m_{\mathrm{south}}(S) < 0$ reads
$a_S\cos v + b_S\sin v < \frac12 - c_y + \frac12(\cos v + \sin v)$, and by
Lemma C.20, $b_S - ka_S < c_x - kc_y$. So (C.4) with $(x, y) = (a_S, b_S)$, and
with $(x, y) = (\frac12, \frac12)$ for the threshold, give

```math
\left\langle e^D_2, c_S - c_D\right\rangle - \tau(\theta) < \gamma\left(\tfrac12 - c_y\right) + \sin d\left(c_x - kc_y - \tfrac12(1 - k)\right) - \tfrac12 - b_D .
```

Expanding $\gamma$, the right side is
$\frac12(\cos d - \sin d) + c_x\sin d - c_y\cos d - \frac12 - b_D$, and with
$c_y\cos d \ge 0$, $c_x \le c_0$, $-b_D < \frac9{40}$, $\cos d \le \cos\frac12$
and $\sin d \ge \sin\frac12$, it is less than

```math
\tfrac12\cos\tfrac12 - \left(\tfrac12 - c_0\right)\sin\tfrac12 - \tfrac{11}{40} < 0.438805 - 0.387 \cdot 0.47942 - 0.275 < -0.021 .
```

So $D$ and $S$ are not separated along $e^D_2$ (Figure C.20 (a)).

*Along $e^S_2$.* By Lemma C.20, with $c_y \ge 0$ and $a_S \le \rho_0$,
$b_S < c_0 + \rho_0k$. Put $A(d) = \rho_0 - 0.31(U + U^2)$. With $x = -b_D$, the
far corner of $D$ (Lemma 9.26 (1)) gives
$a_D \le \rho_0 - 0.31(|b_D| + b_D^2) \le \rho_0 - 0.31(x + x^2)$, and

```math
\left(A(d)\cos\theta + U\sin\theta\right) - \left(a_D\cos\theta + x\sin\theta\right) \ge (U - x)\left(\sin\theta - 0.31(1 + U + x)\cos\theta\right) \ge 0 ,
```

as $U \ge |b_D| \ge x$, $1 + U + x \le \frac{29}{20}$ and
$0.31 \cdot \frac{29}{20} < 0.45 < \frac{23}{48} \le \sin\theta$. So

```math
\left\langle e^S_2, c_S - c_D\right\rangle - \tau(\theta) < E(d, v) = c_0 + \rho_0k - \tfrac12 + \left(A(d) - \tfrac12\right)\cos\theta + \left(U - \tfrac12\right)\sin\theta .
```

For fixed $v$, $E$ is nonincreasing in $d$ on $[\frac12, \frac\pi4]$: as
$A'(d) = 0.31 \cdot 0.17(1 + 2U)$ and $U' = -0.17$,

```math
\tfrac{\partial E}{\partial d} = \left(0.0527(1 + 2U) + U - \tfrac12\right)\cos\theta - \left(A(d) - \tfrac12 + 0.17\right)\sin\theta \le 0 ,
```

the first coefficient being at most $0.0527 \cdot 1.45 + 0.225 - 0.5 < 0$ and the
second at least $\rho_0 - 0.31 \cdot 0.275625 - 0.33 > 0$. At $d = \frac12$,
$U = \frac9{40}$ and $A(\frac12) - \frac12 \le 1.11282 - 0.085443 - 0.5 < 0.53$,
and with the brackets of $\cos\frac12$ and $\sin\frac12$,

```math
0.53\cos\left(\tfrac12 + v\right) - \tfrac{11}{40}\sin\left(\tfrac12 + v\right) = \left(0.53\cos\tfrac12 - \tfrac{11}{40}\sin\tfrac12\right)\cos v - \left(0.53\sin\tfrac12 + \tfrac{11}{40}\cos\tfrac12\right)\sin v \le 0.34\cos v - 0.49\sin v .
```

With $c_0 < 0.113$, $\rho_0k \le 1.113 \cdot \frac{11}{20}v$,
$\cos v \le 1 - \frac{v^2}2 + \frac{v^4}{24}$ and $\sin v \ge v - \frac{v^3}6$,

```math
E\left(\tfrac12, v\right) \le -0.387 + 0.61215\,v + 0.34\cos v - 0.49\sin v \le -0.047 + 0.12215\,v - 0.17\,v^2 + \tfrac{0.49}6v^3 + \tfrac{0.34}{24}v^4 ,
```

and with $v^3 \le \frac58v^2$ and $v^4 \le \frac{25}{64}v^2$ this is at most
$-0.047 + 0.12215\,v - 0.1134\,v^2$, a quadratic with the negative discriminant
$0.12215^2 - 4 \cdot 0.1134 \cdot 0.047 < -0.006$. So
$E(d, v) \le E(\frac12, v) < 0$, and $D$ and $S$ are not separated along $e^S_2$
either (Figure C.20 (b)). This contradiction proves $s > 0$. $\square$

*Lean:
[`Six.own_south_positive`](../../SquaresInCircles/Six/Separators/Signs.lean#L242),
[`Six.own_south_transverse_upper`](../../SquaresInCircles/Six/Separators/Signs.lean#L163),
[`Six.south_diagonal_secondary_excluded`](../../SquaresInCircles/Six/Separators/Signs.lean#L181),
[`Six.diagonal_projection_upper`](../../SquaresInCircles/Six/Separators/Signs.lean#L53),
[`Six.southDefect`](../../SquaresInCircles/Six/Separators/Signs.lean#L29),
[`Six.southDefect_antitone_d`](../../SquaresInCircles/Six/Separators/Signs.lean#L73),
[`Six.southDefect_left_negative`](../../SquaresInCircles/Six/Separators/Signs.lean#L108),
[`Six.southDefect_negative`](../../SquaresInCircles/Six/Separators/Signs.lean#L152),
[`Six.transverseLimit`](../../SquaresInCircles/Six/Separators/Signs.lean#L26),
[`Six.radialLimit`](../../SquaresInCircles/Six/Separators/Signs.lean#L27),
[`Six.limit_bounds`](../../SquaresInCircles/Six/Separators/Signs.lean#L33),
[`Six.angle_sum_trig`](../../SquaresInCircles/Six/Separators/Signs.lean#L41).*

![Two graphs below zero. (a) Over d from 1/2 to pi over 4, the bound cos d/2 minus 0.387 sin d minus 11/40 for the separation along the secondary axis of D falls from about −0.022, marked, to about −0.19. (b) Over v from 0 to 5/8, with a legend: the bound E of the separation along the secondary axis of S at d = 1/2, near −0.05, and at d = pi over 4, near −0.23 to −0.26; above them, the trigonometric bound at d = 1/2, dashed, rising from −0.047 to about −0.015, and the quadratic bound, dotted, just above it; all negative](figures/appendix-c/south-sign.svg)

*Figure C.20.* The two cases of the proof of Lemma 9.43 (1). (a) Along
$e^D_2$: the bound $\frac12\cos d - 0.387\sin d - \frac{11}{40}$, largest at
$d = \frac12$. (b) Along $e^S_2$: $E(d, v)$ at $d = \frac12$ (blue) and
$d = \frac\pi4$ (cyan), below the trigonometric bound at $d = \frac12$ (dashed)
and the quadratic $-0.047 + 0.12215v - 0.1134v^2$ (dotted).

*Proof of Lemma 9.43 (2).* Let neither $W$ nor $S$ be separated from $C$ along
its matching side, so that both are separated from $C$ along their own axes,
and suppose that $s - w \ge \frac{24}{25}$. By Lemma 9.38,
$w < 0$; put $v = -w$, so that $0 < v < \frac23$, and $s < \frac23$. Then
$s \ge \frac{24}{25} - v > \frac{22}{75}$ and likewise $v > \frac{22}{75}$. By
Lemma C.1 (3), the two separations read

```math
a_W \ge \tfrac12 + \left(\tfrac12 - c_x\right)\cos v + \left(\tfrac12 + c_y\right)\sin v , \qquad a_S \ge \tfrac12 + \left(\tfrac12 - c_y\right)\cos s + \left(\tfrac12 + c_x\right)\sin s .
```

Their sum is

```math
a_W + a_S \ge 1 + \tfrac12\left(\cos v + \cos s + \sin v + \sin s\right) - c_x(\cos v - \sin s) - c_y(\cos s - \sin v) ,
```

and $\cos v - \sin s \ge 0$, $\cos s - \sin v \ge 0$, as the cosines are at least
$1 - \frac29 = \frac79$ and the sines at most $\frac23$. With $c_x, c_y \le c_0$,
$\frac12 - c_0 > 0.387$ and $\frac12 + c_0 > 0.61$,

```math
a_W + a_S \ge \left(\tfrac12 + 0.387\cos v + 0.61\sin v\right) + \left(\tfrac12 + 0.387\cos s + 0.61\sin s\right) .
```

On $[\frac{22}{75}, \frac23]$ the function $\frac12 + 0.387\cos x + 0.61\sin x$
lies above the line $\bar\rho + \frac9{25}(x - \frac{12}{25})$ (Figure C.21 (a)):
by Lemma A.5 with
$\alpha = -\frac9{25}$, it suffices to check the two ends, where, with
$\cos\frac{22}{75} \ge 0.957285$, $\sin\frac{22}{75} \ge 0.289144$ (the Taylor
polynomials of degrees 6 and 7) and Table C.1,

```math
\tfrac12 + 0.387 \cdot 0.957285 + 0.61 \cdot 0.289144 > 1.0468 > 1.11282 - \tfrac9{25}\cdot\tfrac{14}{75} , \qquad \tfrac12 + 0.387 \cdot 0.78588 + 0.61 \cdot 0.61836 > 1.1813 > 1.11282 + \tfrac9{25}\cdot\tfrac{14}{75} .
```

So $a_W + a_S > 2\bar\rho + \frac9{25}(v + s - \frac{24}{25})$, which is at
least $2\bar\rho > 2\rho_0$, contradicting $a_W, a_S \le \rho_0$. Hence
$s - w < \frac{24}{25}$. $\square$

*Lean:
[`Six.normalized_own_wing_angle_sum`](../../SquaresInCircles/Six/Separators/Signs.lean#L349),
[`Six.coupled_own_wing_radial_sum`](../../SquaresInCircles/Six/Separators/Signs.lean#L304),
[`Six.own_wing_profile_line`](../../SquaresInCircles/Six/Separators/Signs.lean#L333).*

![Two panels. (a) Over x from 0 to 0.7, the blue profile one half plus 0.387 cos x plus 0.61 sin x rises from about 0.89 to about 1.2, crossing a dashed orange line of slope 9/25 through the point (12/25, 1.11282); on the shaded interval from 22/75 to 2/3 the profile lies above the line, touching it nearly at both ends. (b) The square of the angles w from −2/3 to 0 and s from 0 to 2/3, dashed, with the pink corner triangle where s minus w is at least 24/25, bounded by the line from (−2/3, 22/75) to (−22/75, 2/3); the model point is at the corner (0, 0)](figures/appendix-c/own-wings.svg)

*Figure C.21.* Lemma 9.43 (2). (a) The profile
$\frac12 + 0.387\cos x + 0.61\sin x$, a lower bound for the radial coordinate of
an own wing at the angle $x$, against the line of slope $\frac9{25}$ through
$\bar\rho$ at $\frac{12}{25}$; on $[\frac{22}{75}, \frac23]$ it lies above the
line, with a margin of about $0.0012$ at the ends. (b) The angles of two own
wings: the corner $s - w \ge \frac{24}{25}$ would force $a_W + a_S > 2\rho_0$.
