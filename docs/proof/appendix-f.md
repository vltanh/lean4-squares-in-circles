# Appendix F. Seven squares: the marker arc

[Contents](README.md) · [← Appendix E](appendix-e.md) · [Appendix G →](appendix-g.md)

This appendix proves the marker arc lemma of [Chapter 10](10-seven.md),
[Lemma 10.9](10-seven.md#lemma-109-the-marker-arc): a square whose state is
admissible holds an arc of half-width $\frac12$ of the unit circle about its
marker. The proof is a typical use of the one-variable estimates of
[Appendix A](appendix-a.md): the monotonicity criterion and the tangent
parabolas of §A.1, the Taylor bounds of §A.2 and the peak of §A.3, together
with the elementary estimates of
[Lemma 3.29](03-tools.md#lemma-329-elementary-estimates). Of the classical bounds
on $\pi$ we use $\pi > 3.14$.

## F.1 Proof of Lemma 10.9

We prove [Lemma 10.9](10-seven.md#lemma-109-the-marker-arc):

> *Let $(a, b)$ be an admissible state and $t$ a real number with
> $|t - \ell(a, b)| \le \frac12$. Then $|\cos t - a| \le \frac12$ and
> $|\sin t - b| \le \frac12$.*

We recall the notions involved. A state $(a, b)$ is *admissible*
([Definition 10.4](10-seven.md#definition-104-states)) if

```math
\tfrac12 \le a , \qquad 0 \le b \le a , \qquad
\varphi(a, b) = \left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 \le \tfrac{13}4 ,
```

where $\varphi$ is the farthest-vertex function of
[Definition 3.3](03-tools.md#definition-33-farthest-vertex-function). Its
*label* ([Definition 10.6](10-seven.md#definition-106-labels-and-markers)) is

```math
\ell(a, b) = \min\left(\mathrm{axial}(b), \mathrm{side}(a, b), \tfrac\pi4\right) , \qquad
\mathrm{axial}(b) = \tfrac54 b , \qquad
\mathrm{side}(a, b) = \tfrac\pi6 + \tfrac13\left(b - \tfrac12\right) + \tfrac34(1 - a) ,
```

so $\ell(a, b)$ is at most each of the three terms. For an admissible state,
$b < \frac{31}{40}$ and $a < \frac54$
([Lemma 10.5](10-seven.md#lemma-105-admissible-states)), and
$\ell(a, b) \ge 0$ ([Lemma 10.7](10-seven.md#lemma-107-the-label)).

![The admissible states in the (a, b)-plane: a region bounded by the segment of the a-axis from one half to root 3 minus one half, the arc of the circle phi equals 13/4 up to the diagonal, the diagonal b equals a, and the vertical line a equals one half. An orange line touches the circle at about (0.85, 0.70); a green vertical segment at a = x + 1/2 rises from the a-axis to the circle; the side state (1, 1/2) is marked on the circle](figures/appendix-f/admissible.svg)

*Figure F.1.* The admissible states (shaded). The line
$\frac34(a + \frac12) + \frac23(b + \frac12) = \frac{\sqrt{1885}}{24}$ (orange)
touches the circle $\varphi = \frac{13}4$ at the dot, and the disk lies below
it (step 3 of Lemma F.2). At $a = x + \frac12$ the circle bounds
$b + \frac12$ by $\sqrt{13/4 - (x + 1)^2}$ (green; step 1 of Lemma F.8).

In the chart of an exterior square with state $(a, b)$ (Chapter 10) the closed
square is $[a - \frac12, a + \frac12] \times [b - \frac12, b + \frac12]$ and
the unit circle $\Gamma_1$ about the disk centre is
$t \mapsto (\cos t, \sin t)$. So the lemma says that the arc of $\Gamma_1$ of
half-width $\frac12$ about the direction $\ell(a, b)$ lies in the
closed square: it stays on the correct side of each of the four edge lines
(Figure F.2).

![Two panels, each showing an admissible square in its chart with the lines of its near, far, lower and upper edges dashed, the unit circle about o, a dashed ray at the label angle l, and a thick orange arc of the circle about that ray, whose half-width 1/2 is marked as an angle at o. The thin blue part of the circle between two dots is the part inside the square, and it contains the orange arc. Left, the state (1, 1/2), where the orange arc nearly fills the blue part; right, the state (0.9, 0.3)](figures/appendix-f/marker-arc.svg)

*Figure F.2.* The marker arc lemma in the chart, for the side state
$(1, \frac12)$ (left) and the state $(0.9, 0.3)$, whose label is axial
(right). The part of $\Gamma_1$ in the closed square (blue, between the dots)
contains the arc of half-width $\frac12$ about the label (orange). For the
side state the fit is tight at both ends: the square holds the arc from 0 to
$\frac\pi3$, of half-width $\frac\pi6 \approx 0.5236$, against $\frac12$.
For $(0.9, 0.3)$ the arc ends close to the lower and the upper edge.

*Idea of the proof.* The far edge is out of reach. For the lower and upper
edges we compare the label with $\arcsin(b \mp \frac12)$ using lines of slope
$\frac54$ (Lemmas F.1 to F.3). For the near edge we need
$\ell + \arcsin(a - \frac12) + \frac12 < \frac\pi2$. Bounding $\ell$
by the side term and $b$ by the circle $\varphi = \frac{13}4$ leaves a function
$E$ of $x = a - \frac12$ alone, the envelope. Its second derivative is at
most $-\frac18$ (Lemmas F.5 and F.6), so it lies below the parabola that
shares its value and slope at $x = 0$, where both radicands are squares of
rationals; that parabola is highest at $x = \frac29$, at the height
$\frac\pi6 + \frac{353}{648}$ (Lemma F.7). Lemma F.8 concludes.

### Lemma F.1 (a line against the arcsine)

Let $f(y) = \frac54 y - \arcsin y$ for $-1 \le y \le 1$ (Figure F.3).

1. $f$ is nondecreasing on $[-\frac35, \frac35]$.
2. $f$ is nonincreasing on $[\frac35, 1]$.
3. $\arcsin\frac12 = \frac\pi6$.

![The graph of f(y) = 5/4 y minus arcsin y on minus 1 to 1: it falls to a minimum at minus 3/5, rises to a maximum at 3/5 and falls again. An orange band over minus 1/2 to 11/40 with a dashed line at the value at minus 1/2 lies below the graph there; a green band over 1/2 to 1 with a dashed line at the value at 3/5 lies above the graph there](figures/appendix-f/asin-line.svg)

*Figure F.3.* The function $f$ of Lemma F.1. On the range
$[-\frac12, \frac{11}{40})$ of $y = b - \frac12$ (orange) it stays above
$f(-\frac12) = \frac\pi6 - \frac58$, which is step 2 of Lemma F.2. On the
range $[\frac12, 1]$ of $y = b + \frac12$ when $b \le \frac12$ (green) it
stays below $f(\frac35) = \frac34 - \arcsin\frac35$, which is step 2 of
Lemma F.3.

*Proof.* The arcsine is continuous on $[-1, 1]$ and has derivative
$1/\sqrt{1 - y^2}$ at every $y \in (-1, 1)$. So $f$ is continuous on
$[-1, 1]$, with $f'(y) = \frac54 - 1/\sqrt{1 - y^2}$ for $|y| < 1$.
(1) If $|y| < \frac35$, then $1 - y^2 > \frac{16}{25}$, so
$\sqrt{1 - y^2} > \frac45$ and $f'(y) > 0$; apply Lemma A.1 (1).
(2) If $\frac35 < y < 1$, then $0 < 1 - y^2 < \frac{16}{25}$, so
$\sqrt{1 - y^2} < \frac45$ and $f'(y) < 0$; apply Lemma A.1 (2).
(3) $\sin\frac\pi6 = \frac12$ and $-\frac\pi2 \le \frac\pi6 \le \frac\pi2$.
$\square$

*Lean:
[`Seven.asin_line_mono`](../../SquaresInCircles/Seven/Exterior.lean#L240),
[`asin_half`](../../SquaresInCircles/Common/Trigonometry.lean#L722).*

By (1) and (2), $f(\frac35) = \frac34 - \arcsin\frac35$ is the largest value of
$f$ on $[-\frac35, 1]$. The next two lemmas place the label between the lower
and the upper edge (Figure F.4).

![The (b, angle)-plane for b from 0 to 31/40. A thin blue shaded band, the labels of the admissible states, starts at the origin, widens towards the right and closes again in a point just below the angle pi/4. An orange curve, arcsin(b - 1/2) + 1/2, runs just below the band; a green curve, arcsin(b + 1/2) - 1/2, runs above it for b up to 1/2 and rises steeply there](figures/appendix-f/transverse.svg)

*Figure F.4.* Lemmas F.2 and F.3. For each $b$ the labels $\ell(a, b)$ of
the admissible states $(a, b)$ fill the shaded interval. It lies above the
curve $\arcsin(b - \frac12) + \frac12$ of the lower edge (orange) and, for
$b \le \frac12$, below the curve $\arcsin(b + \frac12) - \frac12$ of the
upper edge (green). The closest approach, about 0.005, is at the lower edge
near $b = 0.72$, where the label is a side label (Figure F.5).

### Lemma F.2 (the lower edge)

Let $(a, b)$ be an admissible state. Then
$\arcsin(b - \frac12) + \frac12 < \ell(a, b)$.

*Proof.* Put $y = b - \frac12$. As $0 \le b < \frac{31}{40}$,
$-\frac12 \le y < \frac{11}{40}$. We show that $\arcsin y + \frac12$ is
less than each of the three terms whose minimum is $\ell(a, b)$.

1. *A bound on the arcsine: $\arcsin y < y + 0.0052$.* If
   $y \ge 0$, then $y < \frac{11}{40} < \frac35$, and
   [Lemma 3.29](03-tools.md#lemma-329-elementary-estimates) (3) gives

   ```math
   \arcsin y \le y + \tfrac{y^3}4 \le y + \tfrac14\left(\tfrac{11}{40}\right)^3 < y + 0.0052 .
   ```

   If $y < 0$, then $\arcsin y \le y$ by Lemma 3.29 (2), as $y \ge -1$.
2. *The axial term.* Both $-\frac12$ and $y$ lie in $[-\frac35, \frac35]$, and
   $-\frac12 \le y$. By Lemma F.1 (1) and (3), and as the arcsine is odd,

   ```math
   \tfrac\pi6 - \tfrac58 = f\left(-\tfrac12\right) \le f(y) = \tfrac54 b - \tfrac58 - \arcsin y ,
   ```

   that is, $\arcsin y \le \mathrm{axial}(b) - \frac\pi6$. Since
   $\frac\pi6 > \frac{3.14}6 > \frac12$, we get
   $\arcsin y + \frac12 < \mathrm{axial}(b)$.
3. *The side term.* Put $p = a + \frac12$, $q = b + \frac12$ and
   $L = \frac34 p + \frac23 q$. By the Cauchy–Schwarz inequality, with
   $\varphi(a, b) = p^2 + q^2 \le \frac{13}4$,

   ```math
   L^2 \le \left(\tfrac9{16} + \tfrac49\right)\left(p^2 + q^2\right) \le \tfrac{145}{144} \cdot \tfrac{13}4 ,
   ```

   so $L \le \frac{\sqrt{1885}}{24}$, with equality where the line
   $L = \frac{\sqrt{1885}}{24}$ touches the circle (Figure F.1). By the
   definition of the side term, and as $\sqrt{1885} < 43.42$,

   ```math
   \mathrm{side}(a, b) - y = \tfrac\pi6 - \tfrac23 y - \tfrac34 (a - 1) = \tfrac\pi6 + \tfrac{43}{24} - L
   > \tfrac\pi6 - \tfrac{43.42 - 43}{24} = \tfrac\pi6 - 0.0175 .
   ```

   With step 1, and as $\frac\pi6 > \frac{3.14}6 > 0.5233$,

   ```math
   \mathrm{side}(a, b) - \arcsin y - \tfrac12 > \tfrac\pi6 - 0.0175 - 0.0052 - 0.5 > 0 .
   ```

4. *The cap.* By step 1, and as $y < \frac{11}{40}$,
   $\arcsin y + \frac12 < \frac{11}{40} + 0.0052 + \frac12 = 0.7802 < \frac{3.14}4 < \frac\pi4$.

So $\arcsin y + \frac12$ is less than $\mathrm{axial}(b)$,
$\mathrm{side}(a, b)$ and $\frac\pi4$, hence less than their minimum
$\ell(a, b)$. $\square$

*Lean:
[`Seven.marker_lower_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L262),
[`dot_gt`](../../SquaresInCircles/Common/DiskSupport.lean#L39).*

### Lemma F.3 (the upper edge)

Let $(a, b)$ be an admissible state with $b \le \frac12$. Then
$\ell(a, b) + \frac12 < \arcsin(b + \frac12)$.

*Proof.*

1. *$\arcsin\frac35 > \frac58$.* By Lemma A.7 (2),

   ```math
   \sin\tfrac58 \le \tfrac58 - \tfrac16\left(\tfrac58\right)^3 + \tfrac1{120}\left(\tfrac58\right)^5 < 0.5852 < \tfrac35 .
   ```

   If $\arcsin\frac35 \le \frac58$, then, as
   $-\frac\pi2 \le \arcsin\frac35 \le \frac58 < \frac\pi2$ and the sine
   is increasing on $[-\frac\pi2, \frac\pi2]$, we would get
   $\frac35 = \sin(\arcsin\frac35) \le \sin\frac58 < \frac35$.
2. Put $y = b + \frac12 \in [\frac12, 1]$. By Lemma F.1 (1) if
   $y \le \frac35$, and by Lemma F.1 (2) if $y \ge \frac35$,
   $f(y) \le f(\frac35)$, that is,
   $\arcsin y \ge \arcsin\frac35 + \frac54(y - \frac35)$. As
   $\frac54(y - \frac35) = \frac54 b - \frac18$, step 1 gives

   ```math
   \arcsin y > \tfrac58 + \tfrac54 b - \tfrac18 = \tfrac54 b + \tfrac12 .
   ```

3. As $\ell(a, b) \le \mathrm{axial}(b) = \frac54 b$, step 2 gives
   $\arcsin(b + \frac12) > \ell(a, b) + \frac12$. $\square$

*Lean:
[`Seven.marker_horizontal_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L464).*

The label does not increase with $a$, so for a given $b$ it comes closest to
the lower edge at the largest admissible $a$, on the circle
$\varphi = \frac{13}4$, and closest to the upper edge at $a = \frac12$.
Figure F.5 shows the two margins.

![The margins, for b from 0 to 31/40, by which the label clears the lower edge (orange) and, for b up to 1/2, the upper edge (green), on a vertical scale from 0 to 0.1. The lower margin rises from about 0.024 at b = 0 to a corner near b = 0.29, where the label of the closest state turns from axial to side, then falls to its minimum, about 0.0047, near b = 0.72. The upper margin starts at the same value, dips to its minimum arcsin 3/5 - 5/8 at b = 0.1 and then rises steeply](figures/appendix-f/margins.svg)

*Figure F.5.* Lemmas F.2 and F.3 in detail: the least of
$\ell(a, b) - \arcsin(b - \frac12) - \frac12$ (lower edge, orange) and of
$\arcsin(b + \frac12) - \frac12 - \ell(a, b)$ (upper edge, green) over the
admissible states $(a, b)$ with a given $b$. The lower margin is smallest,
about $0.0047$, near $b = 0.72$, where the closest state lies on the circle
with a side label; left of the dotted line, at the transition state
$b_0 \approx 0.29$ of [Definition 10.6](10-seven.md#definition-106-labels-and-markers),
that label is axial. The upper margin is smallest at $b = \frac1{10}$, where it is
$\arcsin\frac35 - \frac58 \approx 0.0185$, the number that step 1 of
Lemma F.3 shows to be positive.

### Definition F.4 (the envelope)

Let $J = (-1, \frac45)$. For $x \in J$ we have $1 - x^2 > 0$ and
$\frac{13}4 - (x + 1)^2 > 0$, since $|x| < 1$, $0 < x + 1 < \frac95$ and
$(\frac95)^2 = \frac{81}{25} < \frac{13}4$. On $J$ put

```math
\begin{aligned}
E(x) &= \tfrac\pi6 + \tfrac1{24} + \tfrac13\sqrt{\tfrac{13}4 - (x + 1)^2} + \arcsin x - \tfrac34 x , \\
E_1(x) &= \frac1{\sqrt{1 - x^2}} - \frac34 - \frac{x + 1}{3\sqrt{13/4 - (x + 1)^2}} , \\
E_2(x) &= \frac x{\left(1 - x^2\right)^{3/2}} - \frac{13}{12\left(13/4 - (x + 1)^2\right)^{3/2}} .
\end{aligned}
```

$E$ is the *envelope*; $E_1$ and $E_2$ are its first and second derivatives
on $[0, \frac34]$ (Lemma F.6).

*Lean: [`Seven.arcEnvelope`](../../SquaresInCircles/Seven/Exterior.lean#L291),
[`Seven.arcEnvelopeDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L294),
[`Seven.arcEnvelopeSecond`](../../SquaresInCircles/Seven/Exterior.lean#L297).*

The definition of the side term can be written

```math
\mathrm{side}(a, b) = \tfrac\pi6 + \tfrac1{24} + \tfrac13\left(b + \tfrac12\right) - \tfrac34\left(a - \tfrac12\right) . \tag{F.1}
```

For an admissible state with $a - \frac12 = x$, the disk bounds $b + \frac12$
by $\sqrt{13/4 - (x + 1)^2}$, so $E(x)$ bounds
$\mathrm{side}(a, b) + \arcsin x$ from above (Lemma F.8 and Figure F.6).

![For x from 0 to 3/4, a blue shaded region bounded below by a rising curve and above by a curve that meets an orange curve, the graph of E(x) - pi/6, for x beyond about 0.27 and stays below it before; the region ends at x = root 3 - 1. A dashed horizontal line slightly above the orange curve marks the level pi/3 - 1/2](figures/appendix-f/envelope-band.svg)

*Figure F.6.* The envelope. For each $x = a - \frac12$, the values of
$\mathrm{side}(a, b) + \arcsin x - \frac\pi6$ over the admissible states
$(a, b)$ fill the shaded interval; it ends at $x = \sqrt3 - 1$, beyond which
$b$ would have to be negative. The top of the interval lies on the graph of
$E(x) - \frac\pi6$ (orange) where the circle $\varphi = \frac{13}4$ rather
than $b \le a$ bounds $b$, that is, for $x \ge \sqrt{13/8} - 1 \approx 0.27$.
Lemma F.8 needs everything below the dashed level $\frac\pi3 - \frac12$.

### Lemma F.5 (the peak bound)

Let $P(x) = 9\left(x + \frac18\right)^2 (9 - 7x)^3$. Then $P(x) < 676$ for
every $x \in [0, \frac34]$.

![The graph of P on zero to 3/4, in blue: it rises from about 102 at 0 to its peak, about 596, at x = 123/280, marked by a dot with dotted lines to both axes, and falls to about 363 at 3/4. The strip over zero to 123/280 is shaded green and marked P prime at least 0; the strip over 123/280 to 3/4 is shaded orange and marked P prime at most 0. A dashed horizontal line at 676 lies above the whole graph](figures/appendix-f/peak-bound.svg)

*Figure F.7.* Lemma F.5. The polynomial $P$ on $[0, \frac34]$ (blue), from
$P(0) \approx 102.5$ to $P(\frac34) \approx 363.4$. Its derivative is
nonnegative up to $\frac{123}{280}$ (green) and nonpositive after it (orange),
so by Lemma A.9 its largest value is the peak
$P(\frac{123}{280}) \approx 596.1$, below 676 (dashed).

*Proof.* By the product rule, $P$ has at every real $y$ the derivative

```math
P'(y) = 9\left(y + \tfrac18\right)(9 - 7y)^2\left(2(9 - 7y) - 21\left(y + \tfrac18\right)\right)
= 9\left(y + \tfrac18\right)(9 - 7y)^2\left(\tfrac{123}8 - 35y\right) .
```

For $y \in [0, \frac34]$ the factors $y + \frac18$ and $(9 - 7y)^2$ are
nonnegative, and $\frac{123}8 - 35y = 35\left(\frac{123}{280} - y\right)$ is
nonnegative for $y \le \frac{123}{280}$ and nonpositive for
$y \ge \frac{123}{280}$. By Lemma A.9 on $[0, \frac34]$, with the peak
$c = \frac{123}{280}$, $P(x) \le P(c)$ (Figure F.7). At the peak
$c + \frac18 = \frac{79}{140} < \frac47$, so
$(c + \frac18)^2 < \frac{16}{49} < \frac13$; and
$9 - 7c = 9 - \frac{123}{40} = \frac{237}{40} < 6$. Hence

```math
P(c) < 9 \cdot \tfrac13 \cdot 6^3 = 648 < 676 . \qquad \square
```

*Lean:
[`Seven.curvature_peak_lt`](../../SquaresInCircles/Seven/Exterior.lean#L363).*

### Lemma F.6 (the curvature of the envelope)

Let $0 \le x \le \frac34$. Then

1. $1 - x^2 > 0$ and $\frac{13}4 - (x + 1)^2 > 0$;
2. $E$ has derivative $E_1(x)$ at $x$;
3. $E_1$ has derivative $E_2(x)$ at $x$;
4. $E_2(x) \le -\frac18$.

*Proof.* Put $A = \sqrt{1 - x^2}$ and $B = \sqrt{13/4 - (x + 1)^2}$.

1. $x^2 \le \frac9{16}$ and $1 \le x + 1 \le \frac74$ give
   $1 - x^2 \ge \frac7{16}$ and
   $\frac{13}4 - (x + 1)^2 \ge \frac{13}4 - \frac{49}{16} = \frac3{16}$.
2. By (1) and the chain rule, $y \mapsto \sqrt{13/4 - (y + 1)^2}$ has
   derivative $-(x + 1)/B$ at $x$, and the arcsine has derivative $1/A$. So
   $E$ has derivative $-\frac{x + 1}{3B} + \frac1A - \frac34 = E_1(x)$.
3. Likewise $y \mapsto \sqrt{1 - y^2}$ has derivative $-x/A$ at $x$. So
   $1/A$ has derivative $x/A^3$, and by the quotient rule
   $(x + 1)/(3B)$ has derivative

   ```math
   \frac{3B - 3(x + 1) \cdot \left(-(x + 1)/B\right)}{9B^2} = \frac{B^2 + (x + 1)^2}{3B^3} = \frac{13}{12B^3} ,
   ```

   because $B^2 + (x + 1)^2 = \frac{13}4$. So $E_1$ has derivative
   $\frac x{A^3} - \frac{13}{12B^3} = E_2(x)$.
4. By (1), $A > 0$ and $B > 0$, and $A \le 1$ as $A^2 = 1 - x^2 \le 1$. So
   $\frac18 \le \frac1{8A^3}$, and

   ```math
   E_2(x) + \tfrac18 \le \frac{x + \frac18}{A^3} - \frac{13}{12B^3}
   = \frac{12\left(x + \frac18\right)B^3 - 13A^3}{12A^3B^3} .
   ```

   We show that the numerator is negative. As
   $4B^2 = 13 - 4(x + 1)^2 = 9 - 8x - 4x^2$,

   ```math
   (9 - 7x)A^2 - 4B^2 = (9 - 7x)\left(1 - x^2\right) - \left(9 - 8x - 4x^2\right)
   = x\left(7x^2 - 5x + 1\right) = x\left(7\left(x - \tfrac5{14}\right)^2 + \tfrac3{28}\right) \ge 0 ,
   ```

   so $0 < 4B^2 \le (9 - 7x)A^2$, and cubing, $64B^6 \le (9 - 7x)^3 A^6$.
   With Lemma F.5 and $A^6 > 0$,

   ```math
   \left(12\left(x + \tfrac18\right)B^3\right)^2 = \tfrac94\left(x + \tfrac18\right)^2 \cdot 64B^6
   \le \tfrac14 \cdot 9\left(x + \tfrac18\right)^2(9 - 7x)^3 \cdot A^6
   < \tfrac{676}4 A^6 = \left(13A^3\right)^2 .
   ```

   Both $12(x + \frac18)B^3$ and $13A^3$ are positive, so
   $12(x + \frac18)B^3 < 13A^3$, and $E_2(x) < -\frac18$. $\square$

*Lean:
[`Seven.arcEnvelopeSecond_le`](../../SquaresInCircles/Seven/Exterior.lean#L389),
[`Seven.arc_radicands`](../../SquaresInCircles/Seven/Exterior.lean#L300),
[`Seven.arcEnvelope_hasDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L305),
[`Seven.arcEnvelopeDeriv_hasDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L322).*

The two terms of $E_2$ come from the arcsine, which bends up, and from the
circle $\varphi = \frac{13}4$, which bends down: $B$ is the value of
$b + \frac12$ on that circle at $a = x + \frac12$ (Figure F.1). On
$[0, \frac34]$ the circle wins by at least $\frac18$ (Figure F.8).

![The graph of E2 on zero to 3/4 in blue, below the x-axis: it starts at minus 26/81, rises to about minus 0.209 near x = 0.33 and then falls steeply, leaving the frame at about minus 1.15. A dashed purple curve, the bound of step 4, runs just above it, and a dashed black horizontal line at minus 1/8 lies above both](figures/appendix-f/curvature.svg)

*Figure F.8.* Lemma F.6 (4). The second derivative $E_2$ of the envelope
(blue) starts at $E_2(0) = -\frac{26}{81} \approx -0.321$, is largest, about
$-0.209$, near $x = 0.33$, and falls steeply towards $x = \frac34$. Step 4
bounds it by $(x + \frac18)/A^3 - 13/(12B^3) - \frac18$ (dashed) and shows,
with Lemma F.5, that this bound stays below $-\frac18$.

### Lemma F.7 (the envelope bound)

For every $x \in [0, \frac34]$, $E(x) \le \frac\pi6 + \frac{353}{648}$.

![The graph of E(x) - pi/6 on zero to 3/4 in orange: it starts at 13/24, marked by a dot on the vertical axis, rises slightly, and falls to about 0.47 at 3/4. A dashed purple parabola, 13/24 + x/36 - x squared/16, starts at the same dot with the same slope and stays above the orange curve; its highest point, at x = 2/9, is marked by a purple dot at the height 353/648. A black horizontal line at pi/3 - 1/2 lies just above that point](figures/appendix-f/parabola.svg)

*Figure F.9.* Lemma F.7. The envelope $E(x) - \frac\pi6$ (orange) and the
parabola $\frac{13}{24} + \frac x{36} - \frac{x^2}{16}$ (purple, dashed) have
the same value and slope at 0 (dot), and the envelope bends down at least as
fast, so it stays below the parabola. The parabola is highest at
$x = \frac29$, where it equals $\frac{353}{648} \approx 0.5448$, below the
level $\frac\pi3 - \frac12 \approx 0.5472$ that Lemma F.8 needs
(black).

*Proof.*

1. *The value and the slope at 0.* At $x = 0$ the radicands are $1$ and
   $\frac{13}4 - 1 = \frac94 = (\frac32)^2$, and $\arcsin 0 = 0$. So

   ```math
   E(0) = \tfrac\pi6 + \tfrac1{24} + \tfrac13 \cdot \tfrac32 = \tfrac\pi6 + \tfrac{13}{24} , \qquad
   E_1(0) = 1 - \tfrac34 - \frac1{3 \cdot \frac32} = \tfrac14 - \tfrac29 = \tfrac1{36} .
   ```

2. *A parabola above the envelope.* By Lemma F.6, at every
   $y \in [0, \frac34]$ the function $-E$ has derivative $-E_1(y)$, the
   function $-E_1$ has derivative $-E_2(y)$, and $-E_2(y) \ge \frac18$.
   Lemma A.2 with $\kappa = \frac18$, applied to $-E$ at $t = 0$, gives
   $-E(x) \ge -E(0) - E_1(0)\,x + \frac{x^2}{16}$, that is, by step 1,

   ```math
   E(x) \le \tfrac\pi6 + \tfrac{13}{24} + \tfrac x{36} - \tfrac{x^2}{16} . \tag{F.2}
   ```

3. *The top of the parabola.* Since
   $\frac1{16}(x - \frac29)^2 = \frac{x^2}{16} - \frac x{36} + \frac1{324}$ and
   $\frac{13}{24} + \frac1{324} = \frac{351}{648} + \frac2{648} = \frac{353}{648}$,
   completing the square gives

   ```math
   \tfrac{13}{24} + \tfrac x{36} - \tfrac{x^2}{16} = \tfrac{353}{648} - \tfrac1{16}\left(x - \tfrac29\right)^2 \le \tfrac{353}{648} .
   ```

   With (F.2), $E(x) \le \frac\pi6 + \frac{353}{648}$ (Figure F.9). $\square$

*Lean:
[`Seven.arcEnvelope_bound`](../../SquaresInCircles/Seven/Exterior.lean#L424).*

For orientation: the largest value of $E$ on $[0, \frac34]$ is about
$\frac\pi6 + 0.54293$, taken near $x = 0.094$, and
$\frac{353}{648} \approx 0.54475$. The parabola gives away about 0.0018, and
Lemma F.8 has a little more to spare:
$\frac\pi3 - \frac12 - \frac{353}{648} \approx 0.0024$.

### Lemma F.8 (the near edge)

Let $(a, b)$ be an admissible state. Then
$\ell(a, b) + \frac12 < \arccos(a - \frac12)$.

*Proof.* Put $x = a - \frac12$. Since $\frac12 \le a < \frac54$,
$0 \le x < \frac34$.

1. *The disk bounds $b$.* We have
   $\varphi(a, b) = (x + 1)^2 + (b + \frac12)^2 \le \frac{13}4$, so
   $(b + \frac12)^2 \le \frac{13}4 - (x + 1)^2$, which is positive by
   Lemma F.6 (1). As $b + \frac12 > 0$ and the square root is increasing,
   $b + \frac12 \le \sqrt{13/4 - (x + 1)^2}$ (Figure F.1).
2. *The envelope.* By (F.1) and step 1,
   $\mathrm{side}(a, b) + \arcsin x \le E(x)$, and by Lemma F.7,
   $\mathrm{side}(a, b) + \arcsin x \le \frac\pi6 + \frac{353}{648}$.
3. As $\ell(a, b) \le \mathrm{side}(a, b)$ and
   $\arccos x = \frac\pi2 - \arcsin x$,

   ```math
   \arccos x - \ell(a, b) - \tfrac12
   \ge \tfrac\pi2 - \tfrac\pi6 - \tfrac{353}{648} - \tfrac12
   = \tfrac\pi3 - \tfrac{677}{648} > 0 ,
   ```

   because $\frac\pi3 > \frac{3.14}3 > 1.0466$ and $\frac{677}{648} < 1.0448$.
   $\square$

*Lean:
[`Seven.marker_vertical_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L442).*

*Proof of [Lemma 10.9](10-seven.md#lemma-109-the-marker-arc).* Let $(a, b)$
be admissible, write $\ell = \ell(a, b)$, and let $|t - \ell| \le \frac12$,
so that $\ell - \frac12 \le t \le \ell + \frac12$. Put
$\theta = \arccos(a - \frac12)$. Since $0 \le a - \frac12 \le 1$,
$0 \le \theta \le \frac\pi2$ and $\cos\theta = a - \frac12$.

1. *$|t| < \theta$.* By Lemma F.8, $t \le \ell + \frac12 < \theta$; and as
   $\ell \ge 0$, $t \ge \ell - \frac12 \ge -\ell - \frac12 > -\theta$. In
   particular $t \in (-\frac\pi2, \frac\pi2)$.
2. *The near and the far edge.* The cosine is even and strictly decreasing on
   $[0, \pi]$, so by step 1, $\cos t = \cos|t| > \cos\theta = a - \frac12$.
   Also $\cos t \le 1 \le a + \frac12$. Hence $|\cos t - a| \le \frac12$.
3. *The lower edge.* By Lemma F.2,
   $\arcsin(b - \frac12) < \ell - \frac12 \le t$. Both
   $\arcsin(b - \frac12)$ and $t$ lie in $[-\frac\pi2, \frac\pi2]$, where the
   sine is strictly increasing, and $-1 \le b - \frac12 \le 1$, so
   $b - \frac12 = \sin\left(\arcsin(b - \frac12)\right) < \sin t$.
4. *The upper edge.* If $b > \frac12$, then $\sin t \le 1 < b + \frac12$. If
   $b \le \frac12$, Lemma F.3 gives
   $t \le \ell + \frac12 < \arcsin(b + \frac12)$; as in step 3, both
   sides lie in $[-\frac\pi2, \frac\pi2]$ and $\frac12 \le b + \frac12 \le 1$,
   so $\sin t < b + \frac12$. With step 3, $|\sin t - b| \le \frac12$.
   $\square$

*Lean: [`Seven.marker_arc`](../../SquaresInCircles/Seven/Exterior.lean#L491).*
