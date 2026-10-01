# Appendix B. Six squares: the normalization

[Contents](README.md) · [← Appendix A](appendix-a.md) · [Appendix C →](appendix-c.md)

Appendices B to E hold the long estimates of [Chapter 9](09-six.md). This one
proves five results of the normalization: the shallow support lines behind the
central box, [Lemma 9.14](09-six.md#lemma-914-shallow-support-lines) (§B.1); the
squares in a deep cap, [Lemma 9.17](09-six.md#lemma-917-deep-caps) (§B.2); the
squares separated from the central square along their own axis,
[Lemma 9.20](09-six.md#lemma-920-squares-separated-along-their-own-axis) (§B.3);
the supports of a square in the disk of squared radius $Q_0$,
[Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) (§B.4); and the west
stress, which puts $D$ on its own axis,
[Proposition 9.33](09-six.md#proposition-933-the-west-stress) (§B.5).

We use the notation of Chapter 9: $h = \frac{\sqrt2}2$, the constants of the
model ([Lemma 9.2](09-six.md#lemma-92-the-constants)) and of the ceiling
([Definition 9.4](09-six.md#definition-94-the-ceiling),
[Lemma 9.5](09-six.md#lemma-95-the-ceiling)), with the decimals
$\bar R = 1.6886$, $\bar\rho = 1.11282$ and $\bar c = 0.11282$; the squares
$Q_t(a, b)$, the charts in the ceiling and the widths $\omega(\delta)$ and
thresholds $\tau(\delta) = \frac12 + \omega(\delta)$
([Definition 9.9](09-six.md#definition-99-squares-in-a-frame)); the margins of a
square against the containing square $C = Q(c)$
([Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square)),
the pins ([Definition 9.18](09-six.md#definition-918-pins)) and the stresses of
§9.4. We write $u(\theta) = (\cos\theta, \sin\theta)$, and a square *holds*
a point when the point lies in its open square. The tools of
[Appendix A](appendix-a.md) are used throughout, in particular the Taylor
bounds of [Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds), the polynomial
brackets of [Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets) and the
concave functions and harmonics of
[§A.4](appendix-a.md#a4-concave-functions-and-harmonics), and so is
$3.141592 < \pi < 3.141593$.

## B.1 Proof of Lemma 9.14

We prove [Lemma 9.14](09-six.md#lemma-914-shallow-support-lines), which keeps the
free arc of [Proposition 9.15](09-six.md#proposition-915-the-central-box) out of
the squares separated from $C$ along one of their own axes:

> *Let $c_0 < c_x < \frac12$ and $0 \le c_y \le c_x$, and let $(q_1, q_2)$ be
> a point with $0 < q_1 \le \frac9{10}$ and either $c_y \le c_0$ and
> $-\frac9{40} \le q_2 \le \frac25$, or $c_y > c_0$ and $0 \le q_2 \le \frac35$.
> If a unit vector $(x, y)$ satisfies
> $c_x x + c_y y + \frac12(|x| + |y|) \le \rho_0 - \frac12$, then
> $q_1 x + q_2 y \le c_x x + c_y y + \frac12(|x| + |y|)$.*

Throughout this section $C = Q(c)$ with $c = (c_x, c_y)$ as in the lemma, and

```math
L = \rho_0 - \tfrac12 , \qquad g(x, y) = c_x x + c_y y + \tfrac12\left(|x| + |y|\right) ,
```

so that $0.61281 < L < 0.61282$ by [Lemma 9.5](09-six.md#lemma-95-the-ceiling)
(2). For a unit vector $n = (x, y)$, $g(n)$ is the largest value of
$\langle n, p\rangle$ over the points $p$ of $\overline C$, attained at a vertex
of $C$: the line $\langle n, p\rangle = g(n)$ is the support line of $C$
with outer normal $n$, at the distance $g(n)$ from the origin, which lies in
$C$. We call it *shallow* when $g(n) \le L$. The lemma says that no shallow
support line separates the point $q = (q_1, q_2)$ from $C$. We call its two
cases the *regimes* (i), $c_y \le c_0$, and (ii), $c_y > c_0$. In both,
$c_x + \frac12 > c_0 + \frac12 = L$.

The points $q$ lie between the lines of the north and the south sides of $C$
and east of its west side, so only the support lines whose normal points east
can separate them. For these, the depth $L$ forces a normal close to the
vertical (Figure B.1). The next lemma says this at the two eastern vertices of
$C$.

### Lemma B.1 (support lines at the eastern vertices)

Let $(x, w)$ be a unit vector with $x, w \ge 0$, and let $X > L$.

1. If $Xx + \frac12 w \le L$, then $x < \frac{21}{100}$.
2. If $Y \ge 1 - L$ and $Xx + Yw \le L$, then $x < \frac{43}{100}$.
3. If $0 \le Y < 1 - L$, $X + Y \ge 1$ and $w < x$, then $Xx + Yw > L$.

In use, $X = c_x + \frac12$ and $Y$ is $\frac12$ or $\frac12 - c_y$, and
$Xx + Yw$ bounds or equals the support $g$ along $(x, w)$ or $(x, -w)$: the
north-east vertex of $C$ is $(c_x + \frac12, c_y + \frac12)$ and the south-east
vertex is $(c_x + \frac12, c_y - \frac12)$.

*Proof.* (1) and (2). If $x = 0$ there is nothing to prove, so let $x > 0$.
Put $\beta = \frac12$ in (1) and $\beta = 1 - L$ in (2). In both cases the
hypothesis gives $Xx + \beta w \le L$, and $Xx > Lx$, so $\beta w < L(1 - x)$;
in particular $x < 1$. Squaring, with $w^2 = 1 - x^2 = (1 - x)(1 + x)$, and
dividing by $1 - x > 0$ gives $\beta^2(1 + x) < L^2(1 - x)$, that is

```math
x < \frac{L^2 - \beta^2}{L^2 + \beta^2} .
```

For $\beta = \frac12$ the right side is $1 - \frac2{4L^2 + 1}$, and
$4L^2 < 4\cdot 0.61282^2 < 1.5022$, so it is less than
$1 - \frac2{2.5022} < 0.2008$. For $\beta = 1 - L$ it is

```math
\frac{2L - 1}{2\left(L - \frac12\right)^2 + \frac12} < \frac{0.22564}{2\cdot 0.11281^2 + \frac12} < \frac{0.22564}{0.52545} < 0.4295 .
```

(3) Here $x > w \ge 0$ and $x^2 + w^2 = 1$, so $x^2 > \frac12$ and
$x > \frac7{10}$. Also $(x + w)^2 = 1 + 2xw \ge 1$, so $x + w \ge 1$ and
$0 < x - w \le (x - w)(x + w) = 2x^2 - 1$. As $X \ge 1 - Y$, $x > 0$, $Y \ge 0$
and $Y < 1 - L$,

```math
Xx + Yw \ge (1 - Y)x + Yw = x - Y(x - w) \ge x - Y\left(2x^2 - 1\right) > x - (1 - L)\left(2x^2 - 1\right) ,
```

and, as one checks by expanding,

```math
x - (1 - L)\left(2x^2 - 1\right) - L = (1 - x)\left(2(1 - L)x + 1 - 2L\right) \ge 0 ,
```

because $x \le 1$ and
$2(1 - L)x + 1 - 2L > \frac75(1 - L) + 1 - 2L = \frac{12 - 17L}5 > 0$.
$\square$

*Lean:
[`Six.Normalization.first_quadrant_steep`](../../SquaresInCircles/Six/Containing.lean#L62),
[`Six.Normalization.fourth_quadrant_steep`](../../SquaresInCircles/Six/Containing.lean#L76),
[`Six.Normalization.fourth_quadrant_flat`](../../SquaresInCircles/Six/Containing.lean#L94).*

So in regime (i) a shallow support line with a normal in the first quadrant
has its normal within $\arcsin\frac{21}{100} \approx 12°$ of the north, and one
with a normal in the fourth quadrant within $\arcsin\frac{43}{100} \approx 25°$
of the south. In regime (ii) the first quadrant has no shallow normal at all,
since both coordinates of the north-east vertex exceed $L$, and the fourth
quadrant has none closer to the east than to the south.

![Two panels, regimes (i) and (ii) of Lemma 9.14. In each, the containing square C near the origin o, the dashed circle of radius rho0 - 1/2, the dotted circle of radius 9/10 with the free arc in green, and the green rectangle of the points q allowed by the lemma. Thin lines are the shallow support lines of C: grey ones with a normal pointing west pass west of the rectangle; in regime (i) blue ones with a normal in the first quadrant pass above it and orange ones with a normal in the fourth quadrant below it; in regime (ii) only orange lines, nearly horizontal, remain below it](figures/appendix-b/shallow.svg)

*Figure B.1.* Lemma 9.14 in its two regimes, for $c = (0.16, 0.03)$ (left)
and $c = (0.3, 0.2)$ (right). The thin lines are the shallow support lines of
$C$, at distance at most $L = \rho_0 - \frac12$ (dashed circle) from the
origin; the green rectangle holds the points $q$ of the lemma, and the green
arc is the free arc of Proposition 9.15 on $\Gamma_{9/10}$ (dotted). The lines
with a normal pointing west (grey) pass west of the rectangle. In regime (i)
the lines with a normal in the first quadrant (blue) pass above it and those
with a normal in the fourth quadrant (orange) below it. In regime (ii) only
orange lines with a normal closer to the south than to the east remain. In
each family the bold line is the shallow line whose normal is closest to the
east.

*Proof of [Lemma 9.14](09-six.md#lemma-914-shallow-support-lines).* Let $(x, y)$
be a unit vector with $g(x, y) \le L$; we show that
$g(x, y) - q_1x - q_2y \ge 0$. First, $|q_2 - c_y| < \frac12$ in both
regimes: in (i), $-\frac9{40} - c_0 \le q_2 - c_y \le \frac25$, and
$\frac9{40} + c_0 < 0.34$; in (ii),
$-\frac12 < -c_y \le q_2 - c_y \le \frac35 - c_0 < 0.49$.

1. *$x \le 0$.* Then

   ```math
   g(x, y) - q_1x - q_2y = \left(q_1 + \tfrac12 - c_x\right)(-x) + \tfrac12|y| - (q_2 - c_y)\,y \ge 0 ,
   ```

   since $q_1 > 0 > c_x - \frac12$ and $|(q_2 - c_y)y| \le \frac12|y|$. Here
   the hypothesis $g(x, y) \le L$ is not needed.
2. *$x \ge 0$ and $y \ge 0$.* In regime (ii), $c_x + \frac12$ and
   $c_y + \frac12$ both exceed $L$, so
   $g(x, y) = (c_x + \frac12)x + (c_y + \frac12)y > L(x + y) \ge L$, as
   $(x, y) \ne 0$ and $x + y \ge \sqrt{x^2 + y^2} = 1$: this case does not
   occur. In regime (i), $g(x, y) \ge (c_x + \frac12)x + \frac12 y$, and
   Lemma B.1 (1) with $X = c_x + \frac12$ and $w = y$ gives
   $x < \frac{21}{100}$, so $y = \sqrt{1 - x^2} > \frac9{10}$. As
   $c_x + \frac12 - q_1 > c_0 - \frac25 > -\frac3{10}$ and
   $c_y + \frac12 - q_2 \ge \frac1{10}$,

   ```math
   g(x, y) - q_1x - q_2y = \left(c_x + \tfrac12 - q_1\right)x + \left(c_y + \tfrac12 - q_2\right)y \ge \tfrac1{10}(y - 3x) > \tfrac1{10}\left(\tfrac9{10} - \tfrac{63}{100}\right) > 0 .
   ```

3. *$x \ge 0 \ge y$.* Put $w = -y$, $X = c_x + \frac12 > L$ and
   $Y = \frac12 - c_y > 0$, so that $g(x, y) = Xx + Yw$ and
   $g(x, y) - q_1x - q_2y = (X - q_1)x + (Y + q_2)w$. In regime (i),
   $Y \ge \frac12 - c_0 = 1 - L$, and Lemma B.1 (2) gives
   $x < \frac{43}{100}$, so $w > \sqrt{1 - 0.1849} > \frac9{10}$. As
   $X - q_1 > -\frac3{10}$ and $Y + q_2 \ge \frac12 - c_0 - \frac9{40} > \frac3{20}$,

   ```math
   (X - q_1)x + (Y + q_2)w \ge \tfrac3{20}(w - 2x) > \tfrac3{20}\left(\tfrac9{10} - \tfrac{86}{100}\right) > 0 .
   ```

   In regime (ii), $Y < \frac12 - c_0 = 1 - L$ and
   $X + Y = 1 + c_x - c_y \ge 1$. If $w < x$, Lemma B.1 (3) gives
   $g(x, y) > L$: this does not occur. If $w \ge x$, then, as $q_2 \ge 0$
   and $Y > 0$,

   ```math
   (X - q_1)x + (Y + q_2)w \ge (X - q_1 + Y)x = \left(1 + c_x - c_y - q_1\right)x \ge \tfrac1{10}x \ge 0 . \qquad \square
   ```

*Lean:
[`Six.Normalization.shallow_support`](../../SquaresInCircles/Six/Containing.lean#L119),
[`Six.Normalization.FreeRegime`](../../SquaresInCircles/Six/Containing.lean#L112).*

## B.2 Proof of Lemma 9.17

We prove [Lemma 9.17](09-six.md#lemma-917-deep-caps):

> *Let $\eta \ge r_0$, and let $T = Q_t(a, b)$ with
> $(|a| + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ lie beyond the line
> $x = \eta$: $x_t(a, b) \ge \eta + \omega(t)$.*
>
> 1. *If $|t| \le \frac\pi4$, then $|t| < \frac25$, $|b| < a$,
>    $\eta + \frac12 \le a \le \rho_0$, $|b| \le U_0$ and $|b| < \frac12$,
>    and $T$ contains the point $(\eta + \frac12, 0)$.*
> 2. *If moreover $\eta \ge \frac12$, then $|t| < 0.203$.*
> 3. *If $a \ge 0$ and $|b| < \frac12$, then $T$ faces the cap: $t \equiv v$
>    modulo $2\pi$ for a $v$ with $|v| < \frac25$.*

The vertices of $T$ are
$c_T + \frac12\epsilon_1 u(t) + \frac12\epsilon_2 u(t + \frac\pi2)$ with
$\epsilon_1, \epsilon_2 = \pm1$; their first coordinates are
$x_t(a, b) + \frac12(\epsilon_1\cos t - \epsilon_2\sin t)$, and the least of
them is $x_t(a, b) - \omega(t)$. So the hypothesis says that $\overline T$ lies
in the half-plane $x \ge \eta$. The hypothesis and the conclusions depend on
$t$ only through $\cos t$ and $\sin t$. The reflection
$(x, y) \mapsto (x, -y)$ maps the square $Q_t(a, b)$ onto the square
$Q_{-t}(a, -b)$, and it keeps $x_{-t}(a, -b) = x_t(a, b)$,
$\omega(-t) = \omega(t)$, the condition on $(|a|, |b|)$, the line $x = \eta$
and the point $(\eta + \frac12, 0)$. So for $|t| \le \frac\pi4$ we may assume
$t \ge 0$.

How deep can a cap be that holds a square turned by $s$ against its normal?
In the frame of the square, the hypothesis bounds $\eta$ by the support of
the far corner $(|a| + \frac12, |b| + \frac12)$ along $(\cos s, \sin s)$, less
$\cos s + \sin s$; and the far corner ranges over the part $B \ge \frac12$ of
the disk $A^2 + B^2 \le Q_0$. A linear function on that part is largest at the
corner $(\rho_0 + \frac12, \frac12)$ while its direction lies below the
direction of the corner, and at the point of the circle in its direction
beyond it.

### Definition B.2 (the cap depth)

Let $\vartheta = \arcsin\frac1{2R_0}$, the *switch angle*, and for
$0 \le s \le \frac\pi4$ let

```math
\mathrm{cap}(s) = \begin{cases} \left(\rho_0 - \frac12\right)\cos s - \frac12\sin s & \text{if } s \le \vartheta, \\ R_0 - \cos s - \sin s & \text{if } s > \vartheta . \end{cases}
```

As $(\rho_0 + \frac12)^2 + \frac14 = Q_0$
([Lemma 9.5](09-six.md#lemma-95-the-ceiling) (3)), the corner
$(\rho_0 + \frac12, \frac12)$ lies on the circle of radius $R_0$ in the
direction $\vartheta$: $\cos\vartheta = (\rho_0 + \frac12)/R_0$ and
$\sin\vartheta = \frac1{2R_0}$. The two expressions agree at $s = \vartheta$,
and so do their derivatives: their differences are
$(\rho_0 + \frac12)\cos\vartheta + \frac12\sin\vartheta - R_0$ and
$-(\rho_0 + \frac12)\sin\vartheta + \frac12\cos\vartheta$, both $0$. Moreover
$0.29 < \vartheta < \frac25$: on the one hand
$\vartheta \ge \sin\vartheta = \frac1{2R_0}$ and
$\frac1{2R_0} > \frac1{3.3772} > 0.29$; on the other hand
$\sin\frac25 \ge \frac25 - \frac16(\frac25)^3 > 0.389 > \frac13 > \sin\vartheta$,
where the sine increases on $[0, \frac\pi2]$. Numerically
$\vartheta \approx 0.30062$.

*Lean:
[`Six.Normalization.capSwitch`](../../SquaresInCircles/Six/Normalization/Caps.lean#L29),
[`Six.Normalization.capFirst`](../../SquaresInCircles/Six/Normalization/Caps.lean#L32),
[`Six.Normalization.capSecond`](../../SquaresInCircles/Six/Normalization/Caps.lean#L36),
[`Six.Normalization.capDepth`](../../SquaresInCircles/Six/Normalization/Caps.lean#L40),
[`Six.Normalization.capSwitch_gt_29_100`](../../SquaresInCircles/Six/Normalization/Caps.lean#L54).*

### Lemma B.3 (the cap depth bounds the cap)

Let $|t| \le \frac\pi4$ and $(|a| + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$,
and let $\eta$ be a number with $x_t(a, b) \ge \eta + \omega(t)$. Then
$\eta \le \mathrm{cap}(|t|)$.

*Proof.* Put $s = |t|$. Then $\cos t = \cos s \ge 0$,
$|\sin t| = \sin s \ge 0$, $\omega(t) = \frac12(\cos s + \sin s)$ and
$x_t(a, b) = a\cos t - b\sin t \le |a|\cos s + |b|\sin s$, so

```math
\eta \le |a|\cos s + |b|\sin s - \tfrac12\left(\cos s + \sin s\right) . \tag{B.1}
```

If $s \le \vartheta$, then $\tan s \le \tan\vartheta = \frac{1/2}{\rho_0 + 1/2}$,
that is $(\rho_0 + \frac12)\sin s \le \frac12\cos s$, and
[Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk) (3), with
$R = R_0$, $U = \cos s$ and $V = \sin s$, applied to the numbers $|a|$ and
$-|b|$, gives $|a|\cos s + |b|\sin s \le \rho_0\cos s$; with (B.1),
$\eta \le \mathrm{cap}(s)$. If $s > \vartheta$, Lemma 9.25 (1) with the same
$U$ and $V$, applied to $|a|$ and $|b|$, gives
$|a|\cos s + |b|\sin s \le R_0 - \frac12(\cos s + \sin s)$, and again
$\eta \le \mathrm{cap}(s)$. $\square$

*Lean:
[`Six.Normalization.cap_support_bound_signed`](../../SquaresInCircles/Six/Normalization/Caps.lean#L105),
[`Six.disk_corner_support`](../../SquaresInCircles/Six/Supports.lean#L85).*

The bound is sharp: for $s \le \vartheta$ the square with $(a, b) = (\rho_0, 0)$,
whose far edge has both corners on the circle, attains it, and for
$s > \vartheta$ the square whose far vertex lies on the circle in the direction
of the normal.

### Lemma B.4 (the cap depth at large angles)

Let $0 \le s \le \frac\pi4$ and $\eta \le \mathrm{cap}(s)$.

1. If $\eta \ge r_0$, then $s < \frac25$.
2. If $\eta \ge \frac12$, then $s < \frac14$, and even $s < 0.203$.

*Proof.* On $[0, \frac\pi4]$ both expressions of $\mathrm{cap}$ decrease, as
$\cos s$ decreases, $\sin s$ increases and $\cos s + \sin s$ does not decrease
([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (3)). We use $\rho_0 - \frac12 < 0.61282$,
$R_0 < 1.6886$, and the bounds $\cos x \ge 1 - \frac{x^2}2$ and
$\sin x \ge x - \frac{x^3}6$ for $x \ge 0$ from the proof of
[Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds).

(1) Let $s \ge \frac25$. Then $s > \vartheta$, and, as
$\cos\frac25 \ge \frac{23}{25}$ and $\sin\frac25 \ge \frac25 - \frac4{375} > 0.3893$,

```math
\mathrm{cap}(s) \le R_0 - \cos\tfrac25 - \sin\tfrac25 < 1.6886 - 0.92 - 0.3893 < 0.3794 < r_0 ,
```

so $\eta < r_0$.

(2) Let $s \ge \frac14$; recall $\sin\frac14 \ge \frac14 - \frac1{384} > 0.2473$
and $\cos\frac14 \ge \frac{31}{32}$. If $s \le \vartheta$, then
$\mathrm{cap}(s) \le \rho_0 - \frac12 - \frac12\sin\frac14 < 0.61282 - 0.1236 < \frac12$;
if $s > \vartheta$, then
$\mathrm{cap}(s) \le R_0 - \cos\frac14 - \sin\frac14 < 1.6886 - 0.96875 - 0.2473 < 0.473$.
Let next $0.203 \le s < \frac14$. Then $s < \vartheta$, and by Lemma A.7 (1)
and (4), with $x = 0.203$,
$\cos x \le 1 - \frac{x^2}2 + \frac{x^4}{24} < 0.979467$ and
$\sin x \ge x - \frac{x^3}6 + \frac{x^5}{120} - \frac{x^7}{5040} > 0.201608$,
so

```math
\mathrm{cap}(s) \le \left(\rho_0 - \tfrac12\right)\cos 0.203 - \tfrac12\sin 0.203 < 0.61282 \cdot 0.979467 - \tfrac12 \cdot 0.201608 < 0.49944 .
```

In both cases $\eta < \frac12$. $\square$

*Lean:
[`Six.Normalization.cap_angle_lt_two_fifths`](../../SquaresInCircles/Six/Normalization/Caps.lean#L159),
[`Six.Normalization.cap_angle_lt_quarter`](../../SquaresInCircles/Six/Normalization/Caps.lean#L185),
[`Six.Normalization.cap_angle_small`](../../SquaresInCircles/Six/Normalization/PinAxes.lean#L26).*

The thresholds are close: $\mathrm{cap}$ falls through $\frac12$ at about
$0.20207$ and through $r_0$ at about $0.38320$ (Figure B.2).

![The graph of the cap depth for s from 0 to pi/4: a blue branch, (rho0 - 1/2) cos s - 1/2 sin s, from rho0 - 1/2 at s = 0 down to the switch angle theta, where an orange branch, R0 - cos s - sin s, takes over, the two touching there; dashed, each branch continued a little beyond the switch. The graph crosses the dashed level 1/2 at about 0.2021, marked, just before the tick 0.203, and the dashed level r0 at about 0.3832, just before the tick 2/5](figures/appendix-b/cap-depth.svg)

*Figure B.2.* The cap depth of Definition B.2: the depth of the deepest cap
that holds a square turned by $s$ against the normal of its line. Below the
switch angle $\vartheta$ (blue) the square touches the circle with both
corners of its far edge, beyond it (orange) with its far vertex; the two
branches touch at $\vartheta$ (dashed, their continuations). The depth falls
below $\frac12$ at about $0.2021$ and below $r_0$ at about $0.3832$, which are
Lemma B.4 (2) and (1).

### Lemma B.5 (a square in a deep cap)

Let $\eta \ge r_0$, $|t| \le \frac\pi4$,
$(|a| + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ and
$x_t(a, b) \ge \eta + \omega(t)$. Then $|t| < \frac25$, $|b| < a$,
$\eta + \frac12 \le a \le \rho_0$, $|b| \le U_0$ and $|b| < \frac12$.

*Proof.* By the reflection we may assume $0 \le t \le \frac\pi4$. By Lemmas
B.3 and B.4 (1), $t < \frac25$. So $\cos t \ge 1 - \frac{t^2}2 \ge \frac{23}{25}$,
$0 \le \sin t \le t < \frac25$, $\sin t \le \cos t$ and
$1 \le \cos t + \sin t \le \sqrt2 < \frac32$
([Lemma A.15](appendix-a.md#lemma-a15-small-angles)), and the hypothesis reads

```math
\eta + \tfrac12\left(\cos t + \sin t\right) \le a\cos t - b\sin t \le a\cos t + |b|\sin t . \tag{B.2}
```

Also $|b| \le \rho_0$, as $(|b| + \frac12)^2 \le Q_0 - \frac14 = (\rho_0 + \frac12)^2$.

1. *$a > 0$.* Otherwise the right side of (B.2) is at most
   $|b|\sin t < \frac25\rho_0 < 0.45$, while the left side is at least
   $r_0 + \frac12 > 0.88$.
2. *$|b| < a$.* Otherwise $|b| \ge a > 0$, and
   $(|b| - a)(\cos t - \sin t) \ge 0$ gives
   $2(a\cos t + |b|\sin t) \le (a + |b|)(\cos t + \sin t)$. The hypothesis on
   $(|a|, |b|)$ gives
   $(a + |b| + 1)^2 \le 2(a + \frac12)^2 + 2(|b| + \frac12)^2 \le 2Q_0$,
   and $2Q_0 < 5.71 < (\frac{12}5)^2$, so $a + |b| < \frac75$, and (B.2) gives
   $\eta \le \frac12(a + |b| - 1)(\cos t + \sin t) < \frac15\cdot\frac32 < r_0$,
   a contradiction.
3. *$a \ge \frac12$.* Otherwise, by 2,
   $a\cos t + |b|\sin t \le a(\cos t + \sin t) < \frac12(\cos t + \sin t)$, and
   (B.2) gives $\eta < 0$.
4. *$|b| < \frac12$.* Otherwise put $x = a - \frac12$ and $y = |b| - \frac12$,
   both nonnegative, and $r = \sqrt{x^2 + y^2}$. By (B.2) and Cauchy–Schwarz,
   $\eta \le x\cos t + y\sin t \le r$, so $r \ge r_0 > \frac38$; and as
   $x + y \ge r$,

   ```math
   Q_0 \ge (x + 1)^2 + (y + 1)^2 = r^2 + 2(x + y) + 2 \ge (r + 1)^2 + 1 > \left(\tfrac{11}8\right)^2 + 1 > 2.89 ,
   ```

   a contradiction.
5. *$\eta + \frac12 \le a$.* By 4, $|b|\sin t \le \frac12\sin t$, so (B.2)
   gives $\eta + \frac12\cos t \le a\cos t$, that is
   $\eta \le (a - \frac12)\cos t \le a - \frac12$, by 3.
6. *$a \le \rho_0$ and $|b| \le U_0$.* First
   $(a + \frac12)^2 \le Q_0 - \frac14 = (\rho_0 + \frac12)^2$. By 5,
   $a + \frac12 \ge \eta + 1 \ge r_0 + 1 = \frac52 - \rho_0 > 0$, so
   $(|b| + \frac12)^2 \le Q_0 - (\frac52 - \rho_0)^2 = (U_0 + \frac12)^2$.
   $\square$

*Lean:
[`Six.Normalization.deep_cap_bounds`](../../SquaresInCircles/Six/Normalization/Caps.lean#L330).*

### Lemma B.6 (the piercing point)

Under the hypotheses of Lemma B.5, $T$ holds the point $(\eta + \frac12, 0)$.

*Proof.* The reflection fixes the point, so again let $0 \le t < \frac25$, and
put $H = \eta + \frac12$ and $\sigma = \sin t \in [0, \frac25)$. By Lemma B.5,
$\frac78 < r_0 + \frac12 \le H \le a \le \rho_0 < \frac98$. In the frame of $T$
the point $(H, 0)$ has the local coordinates $(H\cos t - a, -H\sigma - b)$,
and we show that both lie in $(-\frac12, \frac12)$.

The first: $H\cos t - a \le H - a \le 0$, and
$H\cos t - a \ge \frac78\cdot\frac{23}{25} - \rho_0 > -0.31$. The second:
$-H\sigma - b \le -b < \frac12$ by Lemma B.5. It remains to show
$b < \frac12 - H\sigma$. Suppose not, and put $V = 1 - H\sigma$, so that
$V \ge 1 - \frac98\cdot\frac25 = \frac{11}{20}$. Then $b \ge V - \frac12 > 0$,
so $|b| + \frac12 = b + \frac12 \ge V$; and by (B.2), $a \ge \frac12$ and
$\cos t \le 1$,

```math
a - \tfrac12 \ge \left(a - \tfrac12\right)\cos t \ge \eta + \tfrac12\sigma + b\sigma \ge \eta + V\sigma .
```

So in the frame of $T$ the far corner $(a + \frac12, |b| + \frac12)$ lies beyond
the point $(\eta + 1 + V\sigma, V)$ in both coordinates, and both coordinates of
that point are positive; hence
$(\eta + 1 + V\sigma)^2 + V^2 \le (a + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$.
But, as one checks by expanding with $\eta + 1 = H + \frac12$,

```math
(\eta + 1 + V\sigma)^2 + V^2 - (\eta + 1)^2 - 1 = \sigma\left(1 + \left(1 - H - H^2\right)\sigma - 2H\sigma^2 + H^2\sigma^3\right) ,
```

and the bracket is positive: $H + H^2 < \frac98 + \frac{81}{64} < \frac{12}5$,
so it is at least $1 - \frac75\cdot\frac25 - 2\cdot\frac98\cdot\frac4{25} = \frac2{25}$.
So $(\eta + 1 + V\sigma)^2 + V^2 \ge (\eta + 1)^2 + 1 > (\frac{11}8)^2 + 1 > Q_0$,
a contradiction. $\square$

*Lean:
[`Six.Normalization.cap_piercing`](../../SquaresInCircles/Six/Normalization/Caps.lean#L414),
[`Six.Normalization.piercing_transverse_upper`](../../SquaresInCircles/Six/Normalization/Caps.lean#L385),
[`Six.Normalization.piercing_polynomial_lower`](../../SquaresInCircles/Six/Normalization/Caps.lean#L343),
[`Six.Normalization.piercing_polynomial_gt_ceiling`](../../SquaresInCircles/Six/Normalization/Caps.lean#L372).*

![The part of the disk of radius R0 beyond the dashed line x = eta, for the deepest cap eta = r0, shaded, with four squares drawn in it as outlines: two parallel to the axes and pushed up and down as far as the disk allows, and two turned by 0.3 and by minus 0.38, also pushed sideways. All four contain the point (eta + 1/2, 0), marked by a dot on the first axis](figures/appendix-b/piercing.svg)

*Figure B.3.* Lemma B.6 for the deepest cap, $\eta = r_0$: four squares in
the cap, two parallel to the axes and pushed up and down as far as the disk
allows, and two turned by $0.3$ and by $-0.38$ and pushed sideways. All of them
hold the point $(\eta + \frac12, 0)$. Pushed further, a square would have its
far corner beyond the point $(\eta + 1 + V\sigma, V)$ of the proof, outside the
disk.

### Lemma B.7 (facing the cap)

Let $\eta \ge r_0$, $a \ge 0$, $|b| < \frac12$,
$(|a| + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ and
$x_t(a, b) \ge \eta + \omega(t)$. Then $t \equiv v$ modulo $2\pi$ for a $v$
with $|v| < \frac25$, and $x_v(a, b) \ge \eta + \omega(v)$. If moreover
$|t| \le \frac{3\pi}4$, then $t = v$, so $|t| < \frac25$.

*Proof.* As $x_t(a, b)$ and $\omega(t)$ depend on $t$ only through $\cos t$ and
$\sin t$, we may replace $t$ by any $t' \equiv t$. Every real number is
congruent modulo $2\pi$ to one of $v$, $\frac\pi2 - v$, $\pi + v$ and
$-\frac\pi2 - v$ for some $|v| \le \frac\pi4$: take its representative in
$(-\pi, \pi]$ and the nearest of the directions $0$, $\pm\frac\pi2$, $\pi$. The
last three cases turn the frame of $T$ by a quarter, a half and three
quarters of a turn, which does not change the square, but puts the cap in front
of a coordinate that cannot reach it (Figure B.4).

- If $t \equiv \frac\pi2 - v$, then $\cos t = \sin v$ and $\sin t = \cos v$, so
  $x_t(a, b) = a\sin v - b\cos v = x_{-v}(-b, a)$, and $\omega(t) = \omega(-v)$
  ([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (2)). The hypotheses of Lemma B.5 hold
  for the phase $-v$ and the coordinates $(-b, a)$, and it gives
  $\eta + \frac12 \le -b$, against $|b| < \frac12$.
- If $t \equiv \pi + v$, then $x_t(a, b) = x_v(-a, -b)$, and Lemma B.5 gives
  $\eta + \frac12 \le -a$, against $a \ge 0$.
- If $t \equiv -\frac\pi2 - v$, then $\cos t = -\sin v$ and
  $\sin t = -\cos v$, so $x_t(a, b) = b\cos v - a\sin v = x_{-v}(b, -a)$, and
  Lemma B.5 gives $\eta + \frac12 \le b$, against $|b| < \frac12$.

So $t \equiv v$ with $|v| \le \frac\pi4$, $x_v(a, b) = x_t(a, b)$ and
$\omega(v) = \omega(t)$, and Lemma B.5 gives $|v| < \frac25$. If
$|t| \le \frac{3\pi}4$, then $t - v$ is a multiple of $2\pi$ with
$|t - v| < \frac{3\pi}4 + \frac25 < 2\pi$, so $t = v$. $\square$

*Lean:
[`Six.Normalization.deep_cap_faces`](../../SquaresInCircles/Six/Normalization/Caps.lean#L471),
[`Six.Normalization.primary_cap_angle`](../../SquaresInCircles/Six/Normalization/Caps.lean#L520),
[`Six.Normalization.cos_sin_eq_of_coe_eq`](../../SquaresInCircles/Six/Normalization/Caps.lean#L460),
[`Six.Normalization.four_primary_quadrants`](../../SquaresInCircles/Six/Normalization/Basic.lean#L172),
[`Six.Normalization.phase_eq_of_short_difference`](../../SquaresInCircles/Six/Normalization/Basic.lean#L205).*

![A square T in the cap beyond the dashed line x = eta, turned by 0.2, inside the circle of radius R0. From the origin, the four directions u(0.2 + k pi/2), k = 0, 1, 2, 3, that can serve as its primary axis, each labelled with the coordinates (a, b) of the centre of T in that frame: (1.05, 0.08) for the frame facing the cap, drawn in blue, and (0.08, -1.05), (-1.05, -0.08) and (-0.08, 1.05) for the others, drawn grey](figures/appendix-b/faces.svg)

*Figure B.4.* Lemma B.7. A square $T$ in a deep cap, at the phase $0.2$ with
$(a, b) = (1.05, 0.08)$. Each of the four directions
$u(0.2 + k\frac\pi2)$, $k = 0, 1, 2, 3$, can serve as its primary axis, since a
quarter turn of the frame does not change the square; beside each is the pair
of coordinates of the centre of $T$ in that frame. Only the frame facing the
cap (blue) has $a \ge 0$ and $|b| < \frac12$. In the others the cap lies in
front of the coordinate $-b$, $-a$ or $b$, which Lemma B.5 would make at
least $\eta + \frac12$.

*Proof of [Lemma 9.17](09-six.md#lemma-917-deep-caps).* (1) is Lemmas B.5 and
B.6. (2) By the reflection let $t \ge 0$; Lemma B.3 gives
$\eta \le \mathrm{cap}(t)$, and Lemma B.4 (2) gives $t < 0.203$. (3) is
Lemma B.7. $\square$

*Lean:
[`Six.Normalization.deep_cap_bounds`](../../SquaresInCircles/Six/Normalization/Caps.lean#L330),
[`Six.Normalization.cap_piercing`](../../SquaresInCircles/Six/Normalization/Caps.lean#L414),
[`Six.Normalization.cap_angle_small`](../../SquaresInCircles/Six/Normalization/PinAxes.lean#L26),
[`Six.Normalization.deep_cap_faces`](../../SquaresInCircles/Six/Normalization/Caps.lean#L471).*

## B.3 Proof of Lemma 9.20

We prove
[Lemma 9.20](09-six.md#lemma-920-squares-separated-along-their-own-axis):

> *Let $c \in [0, c_0]^2$, let $(t, a, b)$ be a chart in the ceiling with
> $|b| < \frac12$, and let $T = Q_t(a, b)$ be separated from $C = Q(c)$ along
> its own axis.*
>
> 1. *If $|t| \le \frac\pi4$, then $-\frac5{12} < t < \frac3{10}$ and $T$
>    holds $p_E$.*
> 2. *If $t = \pi + v$ with $|v| \le \frac\pi4$, then $v > -\frac23$; $T$ holds
>    $p_W$ or $p_D$; it holds $p_W$ if $v \le -\frac\pi{12}$; and if it holds
>    $p_W$, then $v < \frac58$.*
>
> *The same conclusion as in (2) for $v \le -\frac\pi{12}$ holds for a square
> in a deep cap beyond the west side of $C$: if $T = Q_{\pi + v}(a, b)$, with
> $|v| < \frac25$ and $v \le -\frac\pi{12}$, lies beyond the line $x = -\eta$
> for some $\eta \ge r_0$, that is $-x_{\pi + v}(a, b) \ge \eta + \omega(v)$,
> then $T$ holds $p_W$.*

Recall that a square holds a point when the point lies in its open square.
The point $r\,u(q)$ at distance $r$ in the direction $q$ has, in the frame of
$Q_t(a, b)$, the local coordinates

```math
\left(r\cos(q - t) - a,\ r\sin(q - t) - b\right) , \tag{B.3}
```

since $\langle u(q), u(t)\rangle = \cos(q - t)$ and
$\langle u(q), u(t + \frac\pi2)\rangle = \sin(q - t)$; it lies in the open
square when both are less than $\frac12$ in absolute value. By
[Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square),
$T$ is separated from $C$ along its own axis when

```math
a \ge \tfrac12 + c_x\cos t + c_y\sin t + \omega(t) . \tag{B.4}
```

The proof bounds the radial coordinate $a$ from below by (B.4) and from above
by $a \le \rho_0$ ([Lemma 9.10](09-six.md#lemma-910-charts-in-the-ceiling) (2)),
which confines the phase to a window. Inside the window the far corner
$(a + \frac12, |b| + \frac12)$ of $T$ in its frame confines $b$, and the pins
follow.

### Lemma B.8 (far corners)

Let $(t, a, b)$ be a chart in the ceiling, and let $A$, $B$ be numbers with
$0 \le A \le a + \frac12$ and $0 \le B \le |b| + \frac12$. Then
$A^2 + B^2 \le Q_0$. On the other hand, each of the following points
$(A, B)$ has $A^2 + B^2 > Q_0$:

1. $(\frac32 + \frac v4, 1 - v)$, for every real $v$;
2. $(\frac{11}8 + \frac w3, \frac{49}{40} - \frac9{10}w)$, for every real $w$;
3. $(1.54, 0.696)$.

*Proof.* $A^2 + B^2 \le (a + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ by the
definition of a chart in the ceiling. (1) The points lie on the line
$4A + B = 7$, and $17(A^2 + B^2) = (4A + B)^2 + (A - 4B)^2 \ge 49$, while
$\frac{49}{17} > 2.88 > Q_0$. (2) The points lie on the line
$27A + 10B = \frac{395}8$, and
$829(A^2 + B^2) = (27A + 10B)^2 + (10A - 27B)^2 \ge (\frac{395}8)^2$, while
$(\frac{395}8)^2/829 > 2.94$. (3) $1.54^2 + 0.696^2 = 2.856016$. $\square$

*Lean:
[`Six.Normalization.corner_sq_le`](../../SquaresInCircles/Six/Normalization/Basic.lean#L32),
[`Six.moving_pin_polynomial`](../../SquaresInCircles/Six/Normalization/Pins.lean#L336),
[`Six.western_flank_quadratic`](../../SquaresInCircles/Six/Normalization/Pins.lean#L672).*

So a far corner cannot lie beyond any point of the two lines, nor beyond the
point (3): these three obstacles lie just outside the disk (Figure B.5). Each
of the next proofs puts the far corner beyond one of them.

![The plane of the far corner (A, B) = (a + 1/2, |b| + 1/2) of a chart in the ceiling, whose possible positions fill the blue region inside the circle A^2 + B^2 = Q0. Three obstacles lie outside the circle: an orange segment on the dashed line 4A + B = 7, a green segment on the dashed line 27A + 10B = 395/8, and the purple point (1.54, 0.696)](figures/appendix-b/far-lines.svg)

*Figure B.5.* The obstacles of Lemma B.8 in the plane of the far corner
$(A, B) = (a + \frac12, |b| + \frac12)$, which ranges over the blue region,
inside the circle $A^2 + B^2 = Q_0$. The lines $4A + B = 7$ (orange) and
$27A + 10B = \frac{395}8$ (green) pass outside the circle, at the distances
$\frac7{\sqrt{17}} \approx 1.6977$ and $\approx 1.7149$ from the origin,
against $R_0 \approx 1.6885$; the thick segments are the points used by the
transverse obstruction (Lemma B.12) and on the western flank (Lemma B.14).
The point $(1.54, 0.696)$ (purple), used for the pin of $W$ (Lemma B.15), lies
only about $0.0014$ outside.

### Lemma B.9 (radial profiles)

Let $c \in [0, c_0]^2$, and let $t$ and $a$ satisfy (B.4).

1. If $0 \le t \le \frac\pi4$, then $a \ge \frac12 + \frac12(\cos t + \sin t)$.
2. If $t = -s$ with $0 \le s \le \frac\pi4$, then
   $a \ge \frac12 + \frac12\cos s + r_0\sin s$.
3. If $t = \pi - s$ with $0 \le s \le \frac\pi4$, then
   $a \ge \frac12 + r_0\cos s + \frac12\sin s$.
4. If $t = \pi + s$ with $0 \le s \le \frac\pi4$, then
   $a \ge \frac12 + r_0(\cos s + \sin s)$.
5. If $\cos t \ge 0$, then
   $a + \frac12 \ge 1 + (\frac12 + c_x)\cos t + \frac38|\sin t|$.

*Proof.* In (1) to (4), $\cos s$ and $\sin s$ are nonnegative,
$\omega(t) = \frac12(\cos s + \sin s)$, and $\frac12 - c_0 = r_0$
([Lemma 9.5](09-six.md#lemma-95-the-ceiling) (3)). The term
$c_x\cos t + c_y\sin t$ of (B.4) is $c_x\cos s + c_y\sin s \ge 0$ in (1),
$c_x\cos s - c_y\sin s \ge -c_0\sin s$ in (2),
$-c_x\cos s + c_y\sin s \ge -c_0\cos s$ in (3), and
$-c_x\cos s - c_y\sin s \ge -c_0(\cos s + \sin s)$ in (4). In (5),
$\omega(t) = \frac12(\cos t + |\sin t|)$ and
$c_y\sin t \ge -c_0|\sin t| \ge -\frac18|\sin t|$. $\square$

*Lean:
[`Six.own_east_positive_profile`](../../SquaresInCircles/Six/Normalization/Pins.lean#L424),
[`Six.own_east_negative_profile`](../../SquaresInCircles/Six/Normalization/Pins.lean#L437),
[`Six.own_west_negative_profile`](../../SquaresInCircles/Six/Normalization/Pins.lean#L496),
[`Six.own_west_positive_profile`](../../SquaresInCircles/Six/Normalization/Pins.lean#L511),
[`Six.own_radial_lower`](../../SquaresInCircles/Six/Normalization/Pins.lean#L407).*

### Lemma B.10 (an affine minorant)

Let $A, B \ge 0$ and $0 \le s \le r$. Then

```math
A\cos s + B\sin s \ge A + \left(B - \tfrac{Ar}2 - \tfrac{Br^2}6\right)s .
```

*Proof.* $\cos s \ge 1 - \frac{s^2}2 \ge 1 - \frac{rs}2$ and
$\sin s \ge s - \frac{s^3}6 \ge s - \frac{r^2s}6$, by the bounds of the proof
of [Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds) and $0 \le s \le r$;
multiply by $A$ and $B$ and add. $\square$

*Lean:
[`Six.trig_affine_lower`](../../SquaresInCircles/Six/Normalization/Pins.lean#L585).*

### Lemma B.11 (the windows)

Let $c \in [0, c_0]^2$, let $(t, a, b)$ be a chart in the ceiling, and let
(B.4) hold.

1. If $|t| \le \frac\pi4$, then $-\frac5{12} < t < \frac3{10}$.
2. If $t = \pi + v$ with $|v| \le \frac\pi4$, then $v > -\frac23$.

*Proof.* Outside the windows the profiles of Lemma B.9 exceed $\rho_0$,
against $a \le \rho_0$. Put $K = \frac12 - \rho_0$, so $K > -0.61282$, and
recall $r_0 > 0.387$ and $\cos\frac\pi4 = \sin\frac\pi4 = h > 0.7071$. Each
profile, less $\rho_0$, is $K$ plus a first harmonic $A\cos s + B\sin s$ with
$A, B \ge 0$; by [Lemma A.11](appendix-a.md#lemma-a11-first-harmonics) (2) it is positive on an
interval $[l, \frac\pi4]$ once it is positive at both ends. At the left ends
we bound $\cos$ and $\sin$ below by their Taylor polynomials of degrees 6 and 7
([Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds) (3), (4)).

(1) Let $t \ge \frac3{10}$. By Lemma B.9 (1), and as $\cos + \sin$ does not
decrease on $[0, \frac\pi4]$ ([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (3)),

```math
a - \rho_0 \ge K + \tfrac12\left(\cos\tfrac3{10} + \sin\tfrac3{10}\right) > -0.61282 + \tfrac12(0.955 + 0.2955) > 0.0124 ,
```

with $\cos\frac3{10} \ge 1 - \frac9{200}$ and
$\sin\frac3{10} \ge \frac3{10} - \frac9{2000}$. Let next $t \le -\frac5{12}$,
and put $s = -t \in [\frac5{12}, \frac\pi4]$. By Lemma B.9 (2),
$a - \rho_0 \ge f(s) = K + \frac12\cos s + r_0\sin s$, and, with
$\cos\frac5{12} > 0.914443$ and $\sin\frac5{12} > 0.404714$,

```math
f\left(\tfrac5{12}\right) > -0.61282 + \tfrac12 \cdot 0.914443 + 0.387 \cdot 0.404714 > 0.00102 , \qquad f\left(\tfrac\pi4\right) > -0.61282 + 0.887 \cdot 0.7071 > 0.0143 .
```

So $f > 0$ on $[\frac5{12}, \frac\pi4]$. In both cases $a > \rho_0$, a
contradiction.

(2) Let $v \le -\frac23$, and put $s = -v \in [\frac23, \frac\pi4]$, so that
$t = \pi - s$. By Lemma B.9 (3), $a - \rho_0 \ge g(s) = K + r_0\cos s + \frac12\sin s$,
and, with $\cos\frac23 > 0.785886$ and $\sin\frac23 > 0.618369$,

```math
g\left(\tfrac23\right) > -0.61282 + 0.387 \cdot 0.785886 + \tfrac12 \cdot 0.618369 > 0.0005 , \qquad g\left(\tfrac\pi4\right) > -0.61282 + 0.887 \cdot 0.7071 > 0.0143 .
```

So $g > 0$ on $[\frac23, \frac\pi4]$, and $a > \rho_0$, a contradiction.
$\square$

*Lean:
[`Six.own_east_window`](../../SquaresInCircles/Six/Normalization/Pins.lean#L455),
[`Six.own_west_lower_window`](../../SquaresInCircles/Six/Normalization/Pins.lean#L528),
[`Six.quarter_trig_lower`](../../SquaresInCircles/Six/Normalization/Pins.lean#L419),
[`harmonic_pos_of_endpoints`](../../SquaresInCircles/Common/Trigonometry.lean#L340).*

The margins are small: the profiles cross $\rho_0$ at about $-0.4095$ and
$0.2631$ near the east axis, and at about $-0.6625$ near the west axis
(Figure B.6).

![Two graphs over the angles from minus pi/4 to pi/4. Left, near the east axis: the least radial coordinate a allowed by the separation along the own axis, a blue curve with a corner at 0, rises above the dashed level rho0 outside the green window from minus 5/12 to 3/10. Right, near the west axis: the blue curve rises above rho0 left of minus 2/3, and on the right it meets the dashed orange curve of the largest a for a square that holds the pin p_W before 5/8](figures/appendix-b/profiles.svg)

*Figure B.6.* The radial profiles of Lemma B.9, the least radial coordinate
allowed by the separation along the own axis (blue), against $a \le \rho_0$
(dashed), with the windows of Lemma 9.20 shaded. Left, the phase $t$ near the
east axis: the profile exceeds $\rho_0$ outside $(-0.4095, 0.2631)$. Right, the
phase $\pi + v$ near the west axis: on the left the profile exceeds $\rho_0$
before $v = -0.6625$; on the right it stays below $\rho_0$, and it is the pin
$p_W$ that bounds $v$: the largest radial coordinate of a square that holds
$p_W$ (orange) falls below the profile at about $v = 0.6169$
(Lemma B.15).

### Lemma B.12 (the transverse obstruction)

Let $(t, a, b)$ be a chart in the ceiling with $|t| \le \frac5{12}$, and let
$0 \le x \le \frac18$ be a number with
$a + \frac12 \ge 1 + (\frac12 + x)\cos t + \frac38|\sin t|$. Then
$|b| + (1 + x)|\sin t| < \frac12$.

*Proof.* Put $\gamma = \cos t$ and $\sigma = |\sin t|$, so that
$\gamma^2 + \sigma^2 = 1$, $\gamma \ge 1 - \frac{t^2}2 \ge 1 - \frac{25}{288} > \frac56$
and $\sigma \le |t| \le \frac5{12}$ ([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (1)).
Suppose that $|b| + (1 + x)\sigma \ge \frac12$, and put

```math
A_0 = 1 + \tfrac12\gamma + \tfrac38\sigma , \qquad B_0 = 1 - \sigma , \qquad A = A_0 + x\gamma , \qquad B = B_0 - x\sigma .
```

Then $A \le a + \frac12$ by hypothesis, $B \le |b| + \frac12$ by the
supposition, and $A > 0$, $B \ge 1 - \frac98\cdot\frac5{12} > 0$; so
$A^2 + B^2 \le Q_0$ by Lemma B.8. Now

```math
A^2 + B^2 = A_0^2 + B_0^2 + 2x\left(A_0\gamma - B_0\sigma\right) + x^2 \ge A_0^2 + B_0^2 ,
```

as $A_0\gamma \ge \gamma > \frac56 > \frac5{12} \ge \sigma \ge B_0\sigma$. Next,
$\gamma \ge 1 - \frac\sigma4$: indeed $(1 - \gamma)(\gamma - \frac56) \ge 0$
gives $\frac{11}6\gamma \ge \gamma^2 + \frac56 = \frac{11}6 - \sigma^2$, so
$\gamma \ge 1 - \frac6{11}\sigma^2 \ge 1 - \frac\sigma4$, as
$\sigma \le \frac5{12} < \frac{11}{24}$. Hence
$A_0 \ge \frac32 + \frac\sigma4 \ge 0$, and the point
$(\frac32 + \frac\sigma4, 1 - \sigma)$ has squared norm at most
$A_0^2 + B_0^2 \le Q_0$, against Lemma B.8 (1). $\square$

*Lean:
[`Six.own_transverse_obstruction`](../../SquaresInCircles/Six/Normalization/Pins.lean#L343),
[`Six.moving_pin_trig`](../../SquaresInCircles/Six/Normalization/Pins.lean#L400),
[`Six.moving_pin_polynomial`](../../SquaresInCircles/Six/Normalization/Pins.lean#L336).*

### Lemma B.13 (the east pin)

1. Let $c \in [0, c_0]^2$, let $(t, a, b)$ be a chart in the ceiling with
   $|t| \le \frac\pi4$, and let (B.4) hold. Then
   $-\frac5{12} < t < \frac3{10}$, and $Q_t(a, b)$ holds $p_E$.
2. Let $(t, a, b)$ be a chart in the ceiling with $|b| < \frac12$ and
   $|t| \le \frac5{12}$, whose square holds a point $(L, 0)$ with
   $L \ge \frac9{10}$. Then it holds $p_E$.

*Proof.* By (B.3), $p_E = \frac9{10}u(0)$ has the local coordinates
$(\frac9{10}\cos t - a, -\frac9{10}\sin t - b)$, and $(L, 0)$ has
$(L\cos t - a, -L\sin t - b)$. In both parts $|t| \le \frac5{12}$, so
$\cos t > \frac56$, and $\frac12 \le a \le \rho_0$; hence
$\frac9{10}\cos t - a > \frac34 - \rho_0 > -\frac12$.

(1) The window is Lemma B.11 (1). As $c_y \le c_0 < \frac18$, Lemma B.9 (5)
gives $a + \frac12 \ge 1 + (\frac12 + c_x)\cos t + \frac38|\sin t|$. In
particular $a \ge \frac12 + \frac12\cos t > \frac{11}{12}$, so the first
coordinate of $p_E$ is negative; and Lemma B.12 with $x = c_x$ gives

```math
\left|\tfrac9{10}\sin t + b\right| \le \tfrac9{10}|\sin t| + |b| \le (1 + c_x)|\sin t| + |b| < \tfrac12 .
```

(2) The first coordinate is at most $\frac9{10} - a \le \frac25$. The second,
$-\frac9{10}\sin t - b$, lies between $-b$ and $-L\sin t - b$, as
$0 \le \frac9{10} \le L$; both lie in $(-\frac12, \frac12)$, the second
because $(L, 0)$ is held. $\square$

*Lean:
[`Six.own_east_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L645),
[`Six.east_pin_of_axis_point`](../../SquaresInCircles/Six/Normalization/Pins.lean#L621),
[`Six.contract_transverse`](../../SquaresInCircles/Six/Normalization/Pins.lean#L604).*

Part (2) is used for squares in a deep cap beyond the east side of $C$, which
by Lemma 9.17 hold the point $(1 + c_x, 0)$.

![Two copies of the disk of radius R0 with the containing square C, grey, and a square T, orange, separated from C along its own axis by the dashed support line of C. Left, T at the phase 0.262, with C = Q(0, 0); right, T at the phase -0.409, with C = Q(0, c0). Each T is pushed out to the circle, and each holds the east pin p_E at (9/10, 0), marked by a dot](figures/appendix-b/east-pin.svg)

*Figure B.7.* Squares at the two ends of the east window, separated from $C$
along their own axis by the dashed support line of $C$: left at the phase
$0.262$ with $C = Q(0, 0)$, right at $-0.409$ with $C = Q(0, c_0)$, the
centres of $C$ that make the profiles of Lemma B.9 (1) and (2) exact. Both are
pushed out to the circle of radius $R_0$, with $b \approx 0$, and both hold
the east pin $p_E$ on $\Gamma_{9/10}$ (dotted).

### Lemma B.14 (the western flank)

Let $(t, a, b)$ be a chart in the ceiling with $|b| < \frac12$ and
$t = \pi - w$, $\frac\pi{12} \le w \le \frac23$, such that

```math
a \ge \tfrac12 + \tfrac38\cos w + \tfrac12\sin w \qquad \text{if } b < 0 . \tag{B.5}
```

Then $Q_t(a, b)$ holds $p_W$. Condition (B.5) holds in each of the following
cases:

1. $c \in [0, c_0]^2$ and (B.4) holds;
2. $w < \frac25$ and $-x_t(a, b) \ge \eta + \omega(t)$ for some
   $\eta \ge r_0$.

*Proof.* Put $\delta = w - \frac\pi{12}$, so that
$0 \le \delta \le \frac23 - \frac\pi{12} < \frac5{12}$, $\cos\delta > \frac56$
and $0 \le \sin\delta \le \delta$. As $p_W = \frac9{10}u(\pi - \frac\pi{12})$,
(B.3) gives its local coordinates
$(\frac9{10}\cos\delta - a, \frac9{10}\sin\delta - b)$. The first lies
between $\frac34 - \rho_0 > -\frac12$ and $\frac9{10} - \frac12 < \frac12$,
as $\frac56 < \cos\delta \le 1$ and $\frac12 \le a \le \rho_0$. The second
exceeds $-\frac12$, as $b < \frac12$ and $\sin\delta \ge 0$. Suppose
that it is at least $\frac12$. Then
$b \le \frac9{10}\sin\delta - \frac12 \le \frac9{10}\cdot\frac5{12} - \frac12 < 0$,
and (B.5) applies; by Lemma B.10 with $A = \frac38$, $B = \frac12$ and
$r = \frac23$,

```math
a + \tfrac12 \ge 1 + \tfrac38\cos w + \tfrac12\sin w \ge \tfrac{11}8 + \left(\tfrac12 - \tfrac18 - \tfrac1{27}\right)w = \tfrac{11}8 + \tfrac{73}{216}w \ge \tfrac{11}8 + \tfrac w3 .
```

And, as $\frac{3\pi}{40} > 0.2355 > \frac9{40}$,

```math
|b| + \tfrac12 = \tfrac12 - b \ge 1 - \tfrac9{10}\sin\delta \ge 1 - \tfrac9{10}\delta = 1 + \tfrac{3\pi}{40} - \tfrac9{10}w > \tfrac{49}{40} - \tfrac9{10}w .
```

Both $\frac{11}8 + \frac w3$ and
$\frac{49}{40} - \frac9{10}w \ge \frac{49}{40} - \frac35$ are positive, so by
Lemma B.8 the point $(\frac{11}8 + \frac w3, \frac{49}{40} - \frac9{10}w)$ has
squared norm at most $Q_0$, against Lemma B.8 (2).

(1) Here $t = \pi - w$ with $0 \le w \le \frac\pi4$, and Lemma B.9 (3) gives
$a \ge \frac12 + r_0\cos w + \frac12\sin w$, which implies (B.5), whatever the
sign of $b$, as $r_0 > \frac38$ and $\cos w \ge 0$.

(2) As $\cos t = -\cos w$ and $\sin t = \sin w$, the hypothesis reads
$a\cos w + b\sin w \ge \eta + \frac12(\cos w + \sin w)$. If $b < 0$, then
$a\cos w \ge \eta + \frac12\cos w + \frac12\sin w$, and as $a \ge \frac12$ and
$\eta \ge r_0 > \frac38$,

```math
a \ge a\cos w + \tfrac12(1 - \cos w) \ge \eta + \tfrac12 + \tfrac12\sin w > \tfrac12 + \tfrac38\cos w + \tfrac12\sin w . \qquad \square
```

*Lean:
[`Six.western_left_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L679),
[`Six.western_flank_quadratic`](../../SquaresInCircles/Six/Normalization/Pins.lean#L672),
[`Six.own_west_left_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L713),
[`Six.west_cap_left_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L772),
[`Six.west_cap_rotated_identity`](../../SquaresInCircles/Six/Normalization/Pins.lean#L764),
[`Six.polar_rotate`](../../SquaresInCircles/Six/Normalization/Pins.lean#L597).*

On this flank the phase of $T$ lies between $\pi - \frac23$ and the direction
$\pi - \frac\pi{12}$ of $p_W$, so the sixty-degree lemma does not apply; the
pin is held because a square that misses it on the north side would reach
too far out (Figure B.8).

![Two panels with the arc of the circle of radius R0 and the dotted circle of radius 9/10 through the pins p_W and p_D. Left: a square T at the phase pi - 0.5, separated from C = Q(c0, 0) along its own axis by the dashed line, pushed sideways as far as the disk allows; it holds p_W. Dashed purple, the same square moved across until it just misses p_W: its far vertex, marked, lies outside the circle. Right: a square T at the phase pi - 0.3 beyond the dashed line x = -eta of the west side of C; it holds p_W](figures/appendix-b/flank.svg)

*Figure B.8.* The western flank, Lemma B.14. Left, case (1): a square at the
phase $\pi - 0.5$, separated from $C = Q(c_0, 0)$ along its own axis (dashed),
pushed sideways as far as the disk allows; it holds $p_W$. Moved across until
it just misses $p_W$ (dashed purple), it would put its far vertex outside the
circle of radius $R_0$. Right, case (2): a square at the phase $\pi - 0.3$
beyond the line $x = -\eta$ of the west side of $C = Q(c_0, c_0)$, with
$\eta = r_0$; it holds $p_W$.

### Lemma B.15 (the pin of W bounds the turn)

Let $c \in [0, c_0]^2$, let $(t, a, b)$ be a chart in the ceiling with
$t = \pi + v$ and $|v| \le \frac\pi4$, let (B.4) hold, and let $Q_t(a, b)$
hold $p_W$. Then $v < \frac58$.

*Proof.* Suppose $v \ge \frac58$. By Lemma B.9 (4) and Lemma A.15 (3), with
$\cos\frac58 > 0.810962$ and $\sin\frac58 > 0.585097$ (Lemma A.7 (3), (4)),

```math
a + \tfrac12 \ge 1 + r_0\left(\cos\tfrac58 + \sin\tfrac58\right) > 1 + 0.387 \cdot 1.39605 > 1.54 .
```

By (B.3), the second local coordinate of $p_W$ is
$\frac9{10}\sin(\frac{11\pi}{12} - \pi - v) - b = -\frac9{10}\sin(\frac\pi{12} + v) - b$,
and it exceeds $-\frac12$; so
$|b| + \frac12 \ge \frac12 - b > \frac9{10}\sin(\frac\pi{12} + v)$. Here
$0.8866 < \frac\pi{12} + \frac58 \le \frac\pi{12} + v \le \frac\pi3 < \frac\pi2$,
so $\sin(\frac\pi{12} + v) > \sin 0.8866 > 0.7749$ (Lemma A.7 (4)), and
$|b| + \frac12 > 0.6974 > 0.696$. By Lemma B.8 the point $(1.54, 0.696)$ then
has squared norm at most $Q_0$, against Lemma B.8 (3). $\square$

*Lean:
[`Six.own_west_pin_upper`](../../SquaresInCircles/Six/Normalization/Pins.lean#L553).*

*Proof of
[Lemma 9.20](09-six.md#lemma-920-squares-separated-along-their-own-axis).* (1) is
Lemma B.13 (1). (2) Let $t = \pi + v$. By Lemma B.11 (2), $v > -\frac23$. If
$v \le -\frac\pi{12}$, Lemma B.14 (1) with $w = -v \in [\frac\pi{12}, \frac23)$
shows that $T$ holds $p_W$. Otherwise
$\frac{11\pi}{12} < t \le \frac{5\pi}4 = \frac{11\pi}{12} + \frac\pi3$, and
[Lemma 9.19](09-six.md#lemma-919-sixty-degrees) with $q = \frac{11\pi}{12}$ shows
that $T$ holds $\frac9{10}u(\frac{11\pi}{12}) = p_W$ or
$\frac9{10}u(\frac{5\pi}4) = p_D$. If $T$ holds $p_W$, then $v < \frac58$ by
Lemma B.15. Finally, the claim for a square in a deep cap beyond the west side
of $C$ is Lemma B.14 (2) with $w = -v$, as $\omega(\pi + v) = \omega(v)$.
$\square$

*Lean:
[`Six.own_east_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L645),
[`Six.own_east_window`](../../SquaresInCircles/Six/Normalization/Pins.lean#L455),
[`Six.own_west_lower_window`](../../SquaresInCircles/Six/Normalization/Pins.lean#L528),
[`Six.own_west_pins`](../../SquaresInCircles/Six/Normalization/Pins.lean#L734),
[`Six.own_west_left_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L713),
[`Six.own_west_pin_upper`](../../SquaresInCircles/Six/Normalization/Pins.lean#L553),
[`Six.west_cap_left_pin`](../../SquaresInCircles/Six/Normalization/Pins.lean#L772),
[`Six.sixty_pin_cover`](../../SquaresInCircles/Six/Normalization/Pins.lean#L317).*

## B.4 Proof of Lemma 9.26

We prove [Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling):

> *Let $(t, a, b)$ be a chart in the ceiling.*
>
> 1. *(the far corner) $a + \frac{31}{100}(|b| + b^2) \le \rho_0$.*
> 2. *(the cones) For real $U$ and $V$: if $|V| \le \frac{31}{100}U$, then
>    $Ua + Vb \le \bar\rho U$; if $U \ge \frac75$ and $|V| \le \frac12 U$,
>    then $Ua + Vb \le \bar\rho U + \frac1{12}V^2$; if $U \ge \frac{33}{20}$
>    and $|V| \le \frac35 U$, then $Ua + Vb \le \bar\rho U + \frac3{25}V^2$;
>    and if $\frac35 \le U \le \frac7{10}$ and $|V| \le \frac25 U$, then
>    $Ua + Vb \le \rho_0 U + \frac1{160}$.*
> 3. *(the chord) For $z \ge 0$ and $0 \le q \le \pi$,*
>
>    ```math
>    (z + \sin q)\,a + (\cos q - 1)\,b \le \bar R\left(\left(2 + \tfrac{z^2}4\right)\sin\tfrac q2 + z\cos\tfrac q2\right) - \tfrac12\left(z + \sin q + 1 - \cos q\right) .
>    ```
>
> 4. *(the box) If $0 \le c_x, c_y \le c_0$, then
>    $Xc_x + Yc_y \le \bar c(X + Y)$ for $X, Y \ge 0$, and for $X \ge 0$ and
>    real $Y$, $Xc_x + Yc_y \le \bar c X + yY$ for $y = 0$ or $y = \bar c$.*

The centre $(a, b)$ of a chart in the ceiling ranges over the region bounded
by the lines $a = \frac12$ and $|b| = a$ and by the circle
$(a + \frac12)^2 + (|b| + \frac12)^2 = Q_0$ (Figure B.9). Part (1) puts this
region inside a parabola that touches the circle at its tip $(\rho_0, 0)$, and
the bounds (2) for forces close to the primary axis follow from it by
completing squares. For part (3) recall from
[Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk) that the work of
a force with the components $(U, V)$ in the frame of the square on its centre
is $Ua + Vb$.

*Proof.* (1) By [Lemma 9.5](09-six.md#lemma-95-the-ceiling) (3),
$Q_0 - \frac14 = (\rho_0 + \frac12)^2$, so

```math
|b| + b^2 = \left(|b| + \tfrac12\right)^2 - \tfrac14 \le Q_0 - \left(a + \tfrac12\right)^2 - \tfrac14 = (\rho_0 - a)(\rho_0 + a + 1) .
```

As $a \le \rho_0$ ([Lemma 9.10](09-six.md#lemma-910-charts-in-the-ceiling) (2)),
$\rho_0 - a \ge 0$, and $2\rho_0 + 1 < 3.22564$, so
$\frac{31}{100}(\rho_0 + a + 1) \le \frac{31}{100}(2\rho_0 + 1) < 0.99995$;
hence $\frac{31}{100}(|b| + b^2) \le \rho_0 - a$.

(2) By (1), for $U \ge 0$,

```math
Ua + Vb \le Ua + |V|\,|b| \le \rho_0 U - \tfrac{31}{100}U\left(|b| + b^2\right) + |V|\,|b| . \tag{B.6}
```

In each case $U \ge 0$, and we bound the sum of the last two terms of (B.6).

- If $|V| \le \frac{31}{100}U$, it is at most $-\frac{31}{100}Ub^2 \le 0$, so
  $Ua + Vb \le \rho_0 U \le \bar\rho U$.
- If $U \ge \frac75$ and $|V| \le \frac12 U$, then
  $\frac{31}{100}U \ge \frac{31}{50}|V|$ and
  $\frac{31}{100}U \ge \frac{217}{500}$, so it is at most

  ```math
  \tfrac{19}{50}|V|\,|b| - \tfrac{217}{500}b^2 = \tfrac1{12}V^2 - \tfrac1{12}\left(|V| - \tfrac{57}{25}|b|\right)^2 - \tfrac1{1250}b^2 \le \tfrac1{12}V^2 .
  ```

- If $U \ge \frac{33}{20}$ and $|V| \le \frac35 U$, then
  $\frac{31}{100}U \ge \frac{31}{60}|V|$ and
  $\frac{31}{100}U \ge \frac{1023}{2000} > \frac12$, so it is at most

  ```math
  \tfrac{29}{60}|V|\,|b| - \tfrac12 b^2 = \tfrac3{25}V^2 - \tfrac12\left(|b| - \tfrac{29}{60}|V|\right)^2 - \tfrac{23}{7200}V^2 \le \tfrac3{25}V^2 .
  ```

- If $\frac35 \le U \le \frac7{10}$ and $|V| \le \frac25 U$, then
  $\frac{31}{100}U \ge \frac{31}{40}|V|$ and
  $\frac{31}{100}U \ge \frac{93}{500}$, so it is at most

  ```math
  \tfrac9{40}|V|\,|b| - \tfrac{93}{500}b^2 = \tfrac7{100}V^2 - \tfrac7{100}\left(|V| - \tfrac{45}{28}|b|\right)^2 - \tfrac{291}{56000}b^2 \le \tfrac7{100}V^2 ,
  ```

  and $|V| \le \frac25\cdot\frac7{10} = \frac7{25}$, so
  $\frac7{100}V^2 \le \frac{343}{62500} < \frac1{160}$.

In the first three cases $\rho_0 U \le \bar\rho U$ completes the bound.

(3) Lemma 9.25 (1) with $R = R_0$, $U = z + \sin q$ and $V = \cos q - 1$
gives $Ua + Vb \le R_0\sqrt{U^2 + V^2} - \frac12(|U| + |V|)$, and
$|U| + |V| \ge U - V = z + \sin q + 1 - \cos q$. Put
$\sigma = \sin\frac q2 \ge 0$ and $\gamma = \cos\frac q2 \ge 0$, so that
$\sin q = 2\sigma\gamma$ and $1 - \cos q = 2\sigma^2$, and let
$M = (2 + \frac{z^2}4)\sigma + z\gamma \ge 0$. Then
$U^2 + V^2 = (z + 2\sigma\gamma)^2 + 4\sigma^4 = z^2 + 4z\sigma\gamma + 4\sigma^2$,
and, as one checks by expanding with $\sigma^2 + \gamma^2 = 1$,

```math
M^2 - U^2 - V^2 = \tfrac{z^3}2\sigma\gamma + \tfrac{z^4}{16}\sigma^2 \ge 0 .
```

So $\sqrt{U^2 + V^2} \le M$, and $R_0\sqrt{U^2 + V^2} \le \bar R M$.

(4) For $X, Y \ge 0$, $Xc_x \le c_0X \le \bar cX$ and $Yc_y \le \bar cY$. For
$X \ge 0$ and real $Y$, $Xc_x \le \bar cX$; if $Y \ge 0$, then
$Yc_y \le \bar cY$, and $y = \bar c$ will do; if $Y < 0$, then
$Yc_y \le 0$, and $y = 0$ will do. $\square$

*Lean:
[`Six.radial_transverse_quadratic`](../../SquaresInCircles/Six/Supports.lean#L164),
[`Six.cone_support`](../../SquaresInCircles/Six/Supports.lean#L176),
[`Six.soft_support`](../../SquaresInCircles/Six/Supports.lean#L187),
[`Six.wide_support`](../../SquaresInCircles/Six/Supports.lean#L205),
[`Six.narrow_support`](../../SquaresInCircles/Six/Supports.lean#L223),
[`Six.chordMajorant`](../../SquaresInCircles/Six/Supports.lean#L55),
[`Six.chord_support`](../../SquaresInCircles/Six/Supports.lean#L60),
[`Six.vertex_support`](../../SquaresInCircles/Six/Supports.lean#L34),
[`Six.center_corner`](../../SquaresInCircles/Six/Supports.lean#L267),
[`Six.center_face`](../../SquaresInCircles/Six/Supports.lean#L275).*

The number $\frac{31}{100}$ is just below the slope
$\frac{1/2}{\rho_0 + 1/2} > 0.31001$ of the circle at the tip, where the
parabola of (1) touches it; the cones of (2) are the forces whose support
lines meet the parabola near the tip (Figure B.9). In (3), the force
$(z + \sin q, \cos q - 1)$ is $z$ times the primary axis plus the chord from
$(0, 1)$ to $(\sin q, \cos q)$ of the unit circle; for $z = 0$ its
length is the chord $2\sin\frac q2$, which the majorant $M$ equals
(Figure B.10).

![The centres (a, b) of the charts in the ceiling, a blue region bounded by the lines a = 1/2 and |b| = a and by the circle of the far corner, and around it the dashed parabola a + 0.31(|b| + b^2) = rho0, which touches it at (rho0, 0). Four support lines, one for the extreme force of each cone of Lemma 9.26 (2), listed in a legend, fan out from the tip; each lies beyond the parabola and comes close to it near a dot](figures/appendix-b/centres.svg)

*Figure B.9.* The centres $(a, b)$ of the charts in the ceiling (blue), inside
the parabola $a + \frac{31}{100}(|b| + b^2) = \rho_0$ (dashed) of Lemma 9.26
(1). For the extreme force of each cone of (2) the line
$Ua + Vb = \text{bound}$ is drawn: $V = \frac{31}{100}U$ (black),
$(U, V) = (\frac35, \frac6{25})$ (purple), $(\frac75, \frac7{10})$ (orange)
and $(\frac{33}{20}, \frac{99}{100})$ (green). Each line lies beyond the
parabola and comes closest to it at the dot; the black line passes the tip
with the slope of the parabola there.

![For z = 0, 0.5, 1 and 1.5, the length of the force (z + sin q, cos q - 1) as a function of q from 0 to pi, solid, and its majorant (2 + z^2/4) sin(q/2) + z cos(q/2), dashed in the same colour just above it; for z = 0 the two coincide, as the chord 2 sin(q/2)](figures/appendix-b/chord.svg)

*Figure B.10.* The chord majorant of Lemma 9.26 (3): the length
$\sqrt{(z + \sin q)^2 + (1 - \cos q)^2}$ of the force (solid) and its majorant
$(2 + \frac{z^2}4)\sin\frac q2 + z\cos\frac q2$ (dashed) for
$z = 0, 0.5, 1, 1.5$ and $0 \le q \le \pi$. They agree for $z = 0$, and the
excess of the square, $\frac{z^3}2\sigma\gamma + \frac{z^4}{16}\sigma^2$, is
small for small $z$.

A few further bounds of the same kind, with decimal constants, are used in
the later appendices.

### Lemma B.16 (further supports)

Let $(t, a, b)$ be a chart in the ceiling and $U$, $V$ real numbers.

1. If $r \ge 0$ and $U^2 + V^2 \le r^2$, then
   $Ua + Vb \le \bar R r - \frac12(|U| + |V|)$; if moreover $V \ge 0$, then
   $Ua - Vb \le 1.689\,r - \frac12(U + V)$.
2. $Ua + Vb \le 1.113\sqrt{U^2 + V^2}$; and if $U, V \ge 0$ and
   $(\rho_0 + \frac12)V \le \frac12 U$, then $Ua - Vb \le 1.113\,U$.
3. Let $0 < l \le a + \frac12$, and let $s, \gamma \ge 0$ with
   $s^2 + \gamma^2 = 1$ and $R_0 s \le l$. Then
   $as + b\gamma \le (l - \frac12)s + (\sqrt{Q_0 - l^2} - \frac12)\gamma$.
4. If $0 \le c_x, c_y \le c_0$, $X, Y \ge 0$, $g_x \le X$ and $g_y \le Y$,
   then $g_xc_x + g_yc_y \le 0.113(X + Y)$. If $0 \le x \le \kappa$, then
   $xv \le \kappa\max(v, 0)$ for every real $v$.

*Proof.* (1) Lemma 9.25 (1) with $R = R_0$, as
$\sqrt{U^2 + V^2} \le r$ and $R_0 < \bar R < 1.689$; for the second claim
apply it to $(U, -V)$ and use $|U| \ge U$. (2) Lemma 9.25 (2) and (3), as
$\rho_0 < 1.113$. (3) Put $\beta = \sqrt{Q_0 - l^2}$, $A = a + \frac12 \ge l$
and $B = |b| + \frac12$, so that $A^2 + B^2 \le Q_0$. As
$l^2 \le A^2 \le Q_0 - \frac14$, $\beta \ge \frac12$, and $(l, \beta)$ lies on
the circle $A^2 + B^2 = Q_0$; so the disk lies on one side of the tangent there,
$l(A - l) + \beta(B - \beta) \le 0$, since twice the left side is
$(A^2 + B^2) - Q_0 - (A - l)^2 - (B - \beta)^2$. Next,
$(\beta s)^2 - (l\gamma)^2 = s^2(Q_0 - l^2) - l^2(1 - s^2) = (R_0s)^2 - l^2 \le 0$,
so $\beta s \le l\gamma$. Hence

```math
\beta\left(sA + \gamma B - sl - \gamma\beta\right) = s\beta(A - l) + \gamma\beta(B - \beta) \le s\beta(A - l) - \gamma l(A - l) = (A - l)(s\beta - \gamma l) \le 0 ,
```

so $sA + \gamma B \le sl + \gamma\beta$, and

```math
as + b\gamma \le sA + \gamma B - \tfrac12(s + \gamma) \le \left(l - \tfrac12\right)s + \left(\beta - \tfrac12\right)\gamma .
```

(4) $g_xc_x \le Xc_x \le c_0X < 0.113X$, and likewise for $y$; and $xv$ is at
most $0$ if $v < 0$ and at most $\kappa v$ if $v \ge 0$. $\square$

*Lean:
[`Six.local_vertex_support`](../../SquaresInCircles/Six/Supports.lean#L28),
[`Six.vertex_support`](../../SquaresInCircles/Six/Supports.lean#L34),
[`Six.vertex_linear_upper`](../../SquaresInCircles/Six/Supports.lean#L44),
[`Six.chart_radial_work`](../../SquaresInCircles/Six/Supports.lean#L113),
[`Six.cap_linear_upper`](../../SquaresInCircles/Six/Supports.lean#L101),
[`Six.disk_corner_support`](../../SquaresInCircles/Six/Supports.lean#L85),
[`Six.circle_support_above_primary`](../../SquaresInCircles/Six/Supports.lean#L134),
[`Six.coarse_central_work`](../../SquaresInCircles/Six/Supports.lean#L253),
[`Six.scalar_box_support`](../../SquaresInCircles/Six/Supports.lean#L244).*

Part (3) is the analogue of Lemma 9.25 (3) for the part $A \ge l$ of the disk:
a force at the angle $\arcsin s$ from the secondary axis does the most work at
the corner $(l, \sqrt{Q_0 - l^2})$ of that part as long as $R_0 s \le l$.

## B.5 Proof of Proposition 9.33

We prove [Proposition 9.33](09-six.md#proposition-933-the-west-stress):

> *Let $c \in [0, c_0]^2$, and let $W = Q_{\pi + t}(a, b)$ and
> $D = Q_{\pi + u}(a', b')$, for charts in the ceiling, avoid the open disk of
> radius $r_0$ about the origin, with $-\frac23 \le t \le u$ and
> $-\frac25 \le u \le \frac25$. If $W$ is separated from $C = Q(c)$ along its
> own axis and $D$ along the west side of $C$, then $W$ and $D$ are not
> disjoint.*

This is the first stress argument of the book written out in full, and it
follows the plan of §9.4. Three separating inequalities between $C$, $W$ and
$D$, weighted and added, become the works of three forces on the centres
([Lemma 9.24](09-six.md#lemma-924-balance)); the disk bounds the works on $W$
and $D$ ([Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk)), and
the box $[0, c_0]^2$ the work on $C$, as in
[Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) (4); and what remains
is a function of the two angles $t$ and $u$ that would have to be at most 0,
but is positive on the whole triangle of angles. The function is concave in the
right directions ([Lemmas A.11](appendix-a.md#lemma-a11-first-harmonics) and
[A.12](appendix-a.md#lemma-a12-a-harmonic-less-a-radical)), so its values at seven points
decide. In this section $t$ and $u$ are the angles of $W$ and $D$, as in the
proposition, and vectors are written in coordinates.

Suppose that $W$ and $D$ are disjoint. Their phases differ by
$u - t \in [0, \frac{16}{15}]$, so by
[Lemma 9.31](09-six.md#lemma-931-turned-pairs) they are separated along
$e^W_2 = (\sin t, -\cos t)$ or along $e^D_2 = (\sin u, -\cos u)$, from $W$ to
$D$. Let $z = t$ in the first case and $z = u$ in the second, and
$n_z = (\sin z, -\cos z)$. The three separations form the stress of
Table B.1 ([Definition 9.23](09-six.md#definition-923-stress)). Indeed, the
margin $m_{\mathrm{own}} \ge 0$ of $W$
([Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square))
says $\langle e^W_1, c_W - c\rangle \ge \tau(\pi + t) = \tau(t)$, as
$\langle e^W_1, c_W\rangle = a$; the margin $m_{\mathrm{west}} \ge 0$ of $D$
says $\langle (-1, 0), c_D - c\rangle \ge \tau(\pi + u) = \tau(u)$; and the
separation of $W$ and $D$ is (9.1) of
[Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares) with
$\delta = u - t$.

| edge | source | target | normal $n_e$ | weight $\lambda_e$ | threshold $\tau_e$ |
| :-: | :-: | :-: | :-: | :-: | :-: |
| own axis of $W$ | $C$ | $W$ | $e^W_1 = (-\cos t, -\sin t)$ | $\frac9{20}$ | $\tau(t)$ |
| west side of $C$ | $C$ | $D$ | $(-1, 0)$ | $\frac3{10}$ | $\tau(u)$ |
| secondary axis | $W$ | $D$ | $n_z = (\sin z, -\cos z)$ | $\frac14$ | $\tau(u - t)$ |

*Table B.1.* The west stress: its three edges, with $z = t$ if $W$ and $D$ are
separated along the secondary axis of $W$ and $z = u$ if along that of $D$.

### Definition B.17 (the west stress)

For real numbers $t$, $u$, $r$ and $s$ let

```math
\begin{aligned}
\Phi(t, u; r, s) = {}& \tfrac{17}{20} + \tfrac3{10}\cos u + \tfrac3{10}\max(-\sin u, 0) + \tfrac9{40}\left(\cos t + |\sin t|\right) + \tfrac14\left(\cos(u - t) + \sin(u - t)\right) \\
& - c_0\left(\tfrac3{10} + \tfrac9{20}\cos t + \tfrac9{20}\max(\sin t, 0)\right) - R_0\,r - R_0\,s ,
\end{aligned}
```

and

```math
\Phi_W(t, u) = \Phi\left(t, u; \sqrt{\tfrac{53}{200}}, \sqrt{\tfrac{61}{400} - \tfrac3{20}\sin t}\right), \qquad \Phi_D(t, u) = \Phi\left(t, u; \sqrt{\tfrac{53}{200} + \tfrac9{40}\sin(u - t)}, \sqrt{\tfrac{61}{400} - \tfrac3{20}\sin u}\right) .
```

The *triangle* $\Delta$ is the set of the pairs $(t, u)$ with
$-\frac23 \le t \le u$ and $-\frac25 \le u \le \frac25$.

*Lean:
[`Six.westStress`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L41),
[`Six.westStressW`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L47),
[`Six.westStressD`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L51),
[`Six.westCentralSupport`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L36).*

### Lemma B.18 (the stress bounds the separations)

In the setting of Proposition 9.33, if $W$ and $D$ are separated along
$e^W_2$, then $\Phi_W(t, u) \le 0$; if they are separated along $e^D_2$, then
$\Phi_D(t, u) \le 0$.

*Proof.* Let $z$ be $t$ or $u$ accordingly. Note that $|t| \le \frac23$ and
$|u| \le \frac25$, so $\cos t$ and $\cos u$ are positive, and that
$0 \le u - t \le \frac{16}{15} < \frac\pi2$.

1. *The forces.* Adding $\lambda_e n_e$ at the target and $-\lambda_e n_e$ at
   the source of each edge of Table B.1,

   ```math
   F_C = \left(\tfrac3{10} + \tfrac9{20}\cos t,\ \tfrac9{20}\sin t\right), \quad F_W = \left(-\tfrac9{20}\cos t - \tfrac14\sin z,\ -\tfrac9{20}\sin t + \tfrac14\cos z\right), \quad F_D = \left(-\tfrac3{10} + \tfrac14\sin z,\ -\tfrac14\cos z\right) .
   ```

2. *The balance.* By Lemma 9.24 with $o$ the origin, as the stress separates
   the squares,

   ```math
   \tfrac9{20}\tau(t) + \tfrac3{10}\tau(u) + \tfrac14\tau(u - t) \le \langle F_C, c\rangle + \langle F_W, c_W\rangle + \langle F_D, c_D\rangle . \tag{B.7}
   ```

3. *The work on $C$.* As $\frac3{10} + \frac9{20}\cos t > 0$ and
   $0 \le c_x, c_y \le c_0$,

   ```math
   \langle F_C, c\rangle \le c_0\left(\tfrac3{10} + \tfrac9{20}\cos t + \tfrac9{20}\max(\sin t, 0)\right) .
   ```

4. *The work on $W$.* In the frame $e^W_1 = (-\cos t, -\sin t)$,
   $e^W_2 = (\sin t, -\cos t)$ of $W$ the force has the components

   ```math
   U = \langle F_W, e^W_1\rangle = \tfrac9{20} + \tfrac14\sin(z - t), \qquad V = \langle F_W, e^W_2\rangle = -\tfrac14\cos(z - t) ,
   ```

   so $|F_W|^2 = U^2 + V^2 = \frac{53}{200} + \frac9{40}\sin(z - t)$. The
   square $W$ lies in the closed disk of radius $R_0$
   ([Lemma 9.10](09-six.md#lemma-910-charts-in-the-ceiling) (2)), its work is
   $Ua + Vb$, and Lemma 9.25 (1) with $|U| + |V| \ge U - V$ gives

   ```math
   \langle F_W, c_W\rangle \le R_0|F_W| - \tfrac9{40} - \tfrac18\left(\sin(z - t) + \cos(z - t)\right) .
   ```

5. *The work on $D$.* In the frame $e^D_1 = (-\cos u, -\sin u)$,
   $e^D_2 = (\sin u, -\cos u)$ of $D$,

   ```math
   U' = \tfrac3{10}\cos u + \tfrac14\sin(u - z), \qquad V' = -\tfrac3{10}\sin u + \tfrac14\cos(u - z) ,
   ```

   so $|F_D|^2 = \frac{61}{400} - \frac3{20}\sin z$, and Lemma 9.25 (1) with
   $|U'| + |V'| \ge U' + V'$ gives

   ```math
   \langle F_D, c_D\rangle \le R_0|F_D| - \tfrac3{20}(\cos u - \sin u) - \tfrac18\left(\sin(u - z) + \cos(u - z)\right) .
   ```

6. *The thresholds.* As $\cos t$, $\cos u$, $\cos(u - t)$ and $\sin(u - t)$
   are nonnegative, $\tau(t) = \frac12 + \frac12(\cos t + |\sin t|)$,
   $\tau(u) = \frac12 + \frac12(\cos u + |\sin u|)$ and
   $\tau(u - t) = \frac12 + \frac12(\cos(u - t) + \sin(u - t))$.

For $z = t$ and for $z = u$ alike, the terms subtracted in 4 and 5 add up to
$\frac7{20} + \frac3{20}(\cos u - \sin u) + \frac18(\cos(u - t) + \sin(u - t))$.
Insert 3 to 6 into (B.7) and move everything to the left; with
$\frac3{20}(|\sin u| - \sin u) = \frac3{10}\max(-\sin u, 0)$ this is
$\Phi(t, u; |F_W|, |F_D|) \le 0$. For $z = t$ the two lengths are
$\sqrt{53/200}$ and $\sqrt{61/400 - 3\sin t/20}$, which gives
$\Phi_W(t, u) \le 0$; for $z = u$ they are those of $\Phi_D$. $\square$

*Lean:
[`Six.west_geometric_defect_nonpos`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L732),
[`Six.west_defect_at_secondary_axes`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L763),
[`Six.westGeometricDefect`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L634),
[`Six.west_force_balance`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L640),
[`Six.westForceC`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L613),
[`Six.westForceW`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L615),
[`Six.westForceD`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L618),
[`Six.westNormal`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L620),
[`Six.westThreshold`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L623),
[`Six.west_forceW_norm`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L647),
[`Six.west_forceD_norm`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L652),
[`Six.west_forceW_frameX`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L656),
[`Six.west_forceW_frameY`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L662),
[`Six.west_forceD_frameX`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L668),
[`Six.west_forceD_frameY`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L675),
[`Six.westWidthW`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L627),
[`Six.westWidthD`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L629),
[`Six.west_widthW_lower`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L682),
[`Six.west_widthD_lower`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L690),
[`Six.west_central_support`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L698),
[`Six.west_own_separator`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L709),
[`Six.west_cardinal_separator`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L723),
[`center_le_vertexSupport`](../../SquaresInCircles/Common/DiskSupport.lean#L70).*

The forces add up to zero, and on $W$ and $D$ they point outwards, roughly
at the far vertices, where the bound of Lemma 9.25 (1) is attained
(Figure B.11). The separations are tight in the figure, and yet the squares
do not fit: the stress shows that this is so for all angles of the triangle.

![The containing square C, grey, the square W, orange, turned by -0.3 from the west and separated from C along its own axis, and the square D, blue, turned by 0.1 and separated from C along the west side of C and from W along the secondary axis of W; the three separating lines are dashed and labelled with their weights 9/20, 3/10 and 1/4. Thick arrows are the forces F_C, F_W and F_D of the west stress. With every separation tight and W placed as well as possible, two vertices, marked, still lie outside the circle of radius R0; the dashed circle through the farther one has radius about 1.80](figures/appendix-b/west-stress.svg)

*Figure B.11.* The situation of Proposition 9.33 for $t = -0.3$, $u = 0.1$ and
$z = t$, with $c = (\frac12 c_0, \frac12 c_0)$: $W$ (orange) separated from $C$
along its own axis, $D$ (blue) along the west side of $C$ and from $W$ along
$e^W_2$; the separating lines are dashed, with the weights of Table B.1. All
three separations are tight, and $W$ is placed along its secondary axis so as
to bring its far vertices and those of $D$ as close to the origin as possible;
still two vertices (pink) lie outside the circle of radius $R_0$, the farther
at distance about $1.80$ (dashed circle). The arrows are the forces $F_C$,
$F_W$ and $F_D$, drawn at $0.9$ times their length.

### Lemma B.19 (the terms)

Let $\alpha = \frac9{40} - \frac9{20}c_0$, and for $0 \le R \le R_0$ let

```math
\begin{aligned}
J_\pm(x; R) &= \alpha\cos x + \beta_\pm\sin x - R\sqrt{\tfrac{61}{400} - \tfrac3{20}\sin x} , \qquad \beta_- = -\tfrac9{40} , \quad \beta_+ = \alpha , \\
H_\pm(x; R) &= \tfrac3{10}\cos x + \gamma_\pm\sin x - R\sqrt{\tfrac{61}{400} - \tfrac3{20}\sin x} , \qquad \gamma_- = -\tfrac3{10} , \quad \gamma_+ = 0 , \\
G(x; R) &= \tfrac14\left(\cos x + \sin x\right) - R\sqrt{\tfrac{53}{200} + \tfrac9{40}\sin x} .
\end{aligned}
```

Let $J(x; R)$ be $J_-(x; R)$ for $x \le 0$ and $J_+(x; R)$ for $x \ge 0$, and
$H(x; R)$ likewise; the two expressions agree at $x = 0$.

1. On the triangle,

   ```math
   \Phi_W(t, u) = K_W + J(t; R_0) + H(u; 0) + G(u - t; 0) , \qquad \Phi_D(t, u) = K_D + J(t; 0) + H(u; R_0) + G(u - t; R_0) ,
   ```

   with $K_W = \frac{17}{20} - \frac3{10}c_0 - R_0\sqrt{\frac{53}{200}}$ and
   $K_D = \frac{17}{20} - \frac3{10}c_0$.
2. For $0 \le R \le R_0$, $J_-(\cdot; R)$ is concave on $[-\frac23, 0]$,
   $J_+(\cdot; R)$ on $[0, \frac25]$, $H_-(\cdot; R)$ on $[-\frac25, 0]$,
   $H_+(\cdot; R)$ on $[0, \frac25]$, and $G(\cdot; R)$ on
   $[0, \frac{16}{15}]$.

*Proof.* (1) On the triangle, $-\frac23 \le t \le \frac25$ and
$-\frac25 \le u \le \frac25$, so $\sin t$ has the sign of $t$ and $\sin u$
that of $u$. For $t \le 0$ the terms of $\Phi$ in $t$ are
$\frac9{40}(\cos t - \sin t) - \frac9{20}c_0\cos t = \alpha\cos t - \frac9{40}\sin t$,
and for $t \ge 0$ they are
$(\frac9{40} - \frac9{20}c_0)(\cos t + \sin t) = \alpha(\cos t + \sin t)$; the
terms in $u$ are $\frac3{10}(\cos u - \sin u)$ for $u \le 0$ and
$\frac3{10}\cos u$ for $u \ge 0$. The rest is the constant
$\frac{17}{20} - \frac3{10}c_0$, the term
$\frac14(\cos(u - t) + \sin(u - t))$, and $R_0$ times the two lengths. In
$\Phi_W$ the first length is the constant $\sqrt{53/200}$, which goes into
$K_W$, and the second is the radical of $J(t; R_0)$; in $\Phi_D$ they are the
radicals of $G(u - t; R_0)$ and $H(u; R_0)$.

(2) Each function has the form $A\cos x + B\sin x - R\sqrt{p + q\sin x}$ of
Lemma A.12, with $q^2 \le p^2$: $(\frac3{20})^2 = 0.0225 < (\frac{61}{400})^2$
and $(\frac9{40})^2 = 0.050625 < (\frac{53}{200})^2 = 0.070225$. The
radicands are positive: $\frac{61}{400} - \frac3{20}\sin x > 0$ always, and
$\sin x \ge 0$ on $[0, \frac{16}{15}]$. It remains to check
$R\sqrt{p + q\sin x} \le 4(A\cos x + B\sin x)$ on each interval, and for the
first three functions it suffices to check it with $\bar R > R_0 \ge R$ in the
place of $R$. We use $c_0 < \bar c$, so that
$4\alpha = \frac9{10} - \frac95c_0 > 0.6969$, and the bounds of
[Lemma A.15](appendix-a.md#lemma-a15-small-angles).

- $J_-$ on $[-\frac23, 0]$. Put $\sigma = \sin x$; then
  $-\frac23 \le x \le \sigma \le 0$, so $\sigma^2 \le -\frac23\sigma$. By
  [Lemma A.14](appendix-a.md#lemma-a14-tangents-of-the-square-root) with $c = \frac25$,
  $\sqrt{\frac{61}{400} - \frac3{20}\sigma} \le \frac{25}{64} - \frac3{16}\sigma$,
  and $\cos x \ge \cos^2 x = 1 - \sigma^2$ as $0 \le \cos x \le 1$. So

  ```math
  4\left(\alpha\cos x - \tfrac9{40}\sigma\right) - \bar R\left(\tfrac{25}{64} - \tfrac3{16}\sigma\right) \ge \tfrac{69}{100}\left(1 - \sigma^2\right) - \tfrac9{10}\sigma - \bar R\left(\tfrac{25}{64} - \tfrac3{16}\sigma\right) \ge \left(\tfrac{69}{100} - \tfrac{25}{64}\bar R\right) - \left(\tfrac{11}{25} - \tfrac3{16}\bar R\right)\sigma ,
  ```

  which is positive, as $\frac{69}{100} - \frac{25}{64}\bar R > 0.0303$,
  $\frac{11}{25} - \frac3{16}\bar R > 0.12$ and $\sigma \le 0$.
- $J_+$ on $[0, \frac25]$. Here $\sin x \ge 0$, so
  $\sqrt{\frac{61}{400} - \frac3{20}\sin x} \le \sqrt{\frac{61}{400}} < \frac25$,
  and $\cos x + \sin x \ge 1$; so the left side is less than
  $\frac25\bar R < 0.6755 < 4\alpha \le 4\alpha(\cos x + \sin x)$.
- $H_\pm$ on $[-\frac25, 0]$ and $[0, \frac25]$. Here $\gamma_\pm\sin x \ge 0$,
  $\cos x \ge 1 - \frac{x^2}2 \ge \frac{23}{25}$ and $|\sin x| \le \frac25$,
  so $\sqrt{\frac{61}{400} - \frac3{20}\sin x} \le \sqrt{\frac{85}{400}} < \frac12$;
  the left side is less than $\frac12\bar R < 0.85$, and the right side is
  at least $4\cdot\frac3{10}\cdot\frac{23}{25} > 1.1$.
- $G$ on $[0, \frac{16}{15}]$. Here $\sin x \ge 0$, and
  [Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets) with
  $\ell = \frac{16}{15}$ gives
  $\cos x \ge 1 - \frac{\ell^2}2 + \frac{\ell^4}{24} - \frac{\ell^6}{720} > 0.483$,
  so $\cos x > \frac{12}{25}$. Both $R_0\sqrt{\frac{53}{200} + \frac9{40}\sin x}$
  and $\cos x + \sin x$ are nonnegative, and their squares compare:

  ```math
  Q_0\left(\tfrac{53}{200} + \tfrac9{40}\sin x\right) < 0.7556 + 0.6416\sin x < 1 + \tfrac{24}{25}\sin x \le 1 + 2\sin x\cos x = (\cos x + \sin x)^2 .
  ```

  So $R\sqrt{\frac{53}{200} + \frac9{40}\sin x}$ is at most
  $\cos x + \sin x = 4\cdot\frac14(\cos x + \sin x)$.

Lemma A.12 applies in each case. $\square$

*Lean:
[`Six.westStress_eq`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L217),
[`Six.westWForm`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L206),
[`Six.westDForm`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L211),
[`Six.westWForm_eq`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L243),
[`Six.westDForm_eq`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L251),
[`Six.westJ`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L192),
[`Six.westH`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L198),
[`Six.westG`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L202),
[`Six.westJ_negative_concave`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L298),
[`Six.westJ_positive_concave`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L306),
[`Six.westH_negative_concave`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L375),
[`Six.westH_positive_concave`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L384),
[`Six.westG_concave`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L323),
[`Six.west_affine_radical`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L69),
[`Six.westJ_coefficient_pos`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L261),
[`Six.west_angle_bounds`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L58),
[`Six.west_sin_nonpos`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L82),
[`Six.west_difference_trig`](../../SquaresInCircles/Six/Normalization/WestPair.lean#L87),
[`radicalTrig`](../../SquaresInCircles/Common/Trigonometry.lean#L350),
[`radicalTrig_concave`](../../SquaresInCircles/Common/Trigonometry.lean#L391),
[`sqrt_le_tangent`](../../SquaresInCircles/Common/Trigonometry.lean#L609).*

So in $\Phi_W$ the length of the force on $W$ is the constant
$\sqrt{53/200}$, and that of the force on $D$ enters the term in $t$; in
$\Phi_D$ the lengths enter the terms in $u - t$ and $u$ (Figure B.12). At
$x = 0$ the slopes of $J$ and $H$ jump up, from $-\frac9{40}$ to $\alpha$ and
from $-\frac3{10}$ to $0$: they are concave on either side of $0$ but not
across it. This is why the triangle is cut along $t = 0$ and $u = 0$.

![Six graphs in two rows and three columns: the terms J(t) on -2/3 to 2/5, H(u) on -2/5 to 2/5 and G(d) on 0 to 16/15 of the west stress, each on its own vertical scale, with its range written above it. The top row has the terms of Phi_W, where the length of the force on D enters J (R = R0) and H and G are plain harmonics (R = 0); the bottom row has those of Phi_D, where the lengths enter H and G. Each curve lies above its dashed chords on either side of 0, where J and H have a convex corner](figures/appendix-b/terms.svg)

*Figure B.12.* The terms of Lemma B.19, each on its own vertical scale (its
range above it): top, those of $\Phi_W$, namely $J(t; R_0)$, $H(u; 0)$ and
$G(d; 0)$; bottom, those of $\Phi_D$, namely $J(t; 0)$, $H(u; R_0)$ and
$G(d; R_0)$. Each lies above its chords (dashed) on either side of $0$; at $0$,
$J$ and $H$ have a convex corner.

### Lemma B.20 (positivity on the triangle)

Let $K$ be a number and $J$, $H$, $G$ functions such that $J$ is concave on
$[-\frac23, 0]$ and on $[0, \frac25]$, $H$ on $[-\frac25, 0]$ and on
$[0, \frac25]$, and $G$ on $[0, \frac{16}{15}]$, and put
$F(t, u) = K + J(t) + H(u) + G(u - t)$. If $F$ is positive at the seven points

```math
v_1 = \left(-\tfrac23, -\tfrac25\right), \quad v_2 = \left(-\tfrac25, -\tfrac25\right), \quad v_3 = \left(-\tfrac23, 0\right), \quad v_4 = (0, 0), \quad v_5 = \left(-\tfrac23, \tfrac25\right), \quad v_6 = \left(0, \tfrac25\right), \quad v_7 = \left(\tfrac25, \tfrac25\right),
```

then $F$ is positive on the triangle $\Delta$.

*Proof.* The lines $u = 0$ and $t = 0$ cut $\Delta$ into three parts: where
$u \le 0$, the quadrilateral $v_1v_2v_4v_3$; where $t \le 0 \le u$, the
rectangle $v_3v_4v_6v_5$; and where $t \ge 0$, the triangle $v_4v_7v_6$
(Figure B.13). Inside each part $J$ and $H$ keep one concave piece, and
$u - t$ stays in $[0, \frac{16}{15}]$, so by
[Lemma A.10](appendix-a.md#lemma-a10-concave-functions) (3) $F$ is concave in $t$ for fixed
$u$, concave in $u$ along each vertical edge $t = -\frac23$ and $t = 0$ (there
$G(u - t)$ is $G$ composed with an affine map), and concave along the
diagonal $t = u$, where $F(u, u) = K + J(u) + H(u) + G(0)$. We use Lemma A.10
(2) with $m = 0$ along segments.

1. *The edges.* $u \mapsto F(-\frac23, u)$ is concave on $[-\frac25, 0]$ and
   on $[0, \frac25]$, so it is positive there by its values at $v_1$, $v_3$
   and at $v_3$, $v_5$. $u \mapsto F(0, u)$ is concave on $[0, \frac25]$ and
   positive by its values at $v_4$, $v_6$. $u \mapsto F(u, u)$ is concave on
   $[-\frac25, 0]$ and on $[0, \frac25]$, and positive by its values at
   $v_2$, $v_4$ and at $v_4$, $v_7$.
2. *The parts.* Let $(t, u) \in \Delta$. If $u \le 0$, then $F(\cdot, u)$ is
   concave on $[-\frac23, u]$ and positive at its ends $-\frac23$ and $u$, by
   step 1. If $t \le 0 \le u$, it is concave on $[-\frac23, 0]$ and positive at
   $-\frac23$ and $0$. If $t \ge 0$, it is concave on $[0, u]$ and positive at
   $0$ and $u$. In each case $F(t, u) > 0$. $\square$

*Lean:
[`Six.triangle_positive`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L113),
[`concave_gt_of_endpoints`](../../SquaresInCircles/Common/Analysis.lean#L81),
[`concave_affine_argument`](../../SquaresInCircles/Common/Analysis.lean#L107).*

### Lemma B.21 (the seven vertices)

$\Phi_W$ and $\Phi_D$ are positive at the seven points $v_1, \dots, v_7$ of
Lemma B.20.

*Proof.* At each vertex we bound $\Phi$ from below, as follows (Table B.3).

- Replace $c_0$ by $\bar c$ and $R_0$ by $\bar R$; both multiply nonnegative
  numbers that are subtracted, so $\Phi$ can only decrease.
- Replace the two lengths by their upper brackets in Table B.2; the square
  of each bracket exceeds the radicand, by the upper brackets of the sines
  there.
- Replace each cosine and sine that does not vanish by its lower bracket in
  Table B.2, using $\cos(-x) = \cos x$ and $|\sin(-x)| = \sin x$. This is
  legitimate because, once $c_0$ is replaced by $\bar c$, each of them has a
  positive coefficient: $\cos t$, and $\sin t$ for $t > 0$, the coefficient
  $\frac9{40} - \frac9{20}\bar c > 0$; $|\sin t|$ for $t < 0$ the coefficient
  $\frac9{40}$; $\cos u$ and $\max(-\sin u, 0)$ the coefficient $\frac3{10}$;
  and $\cos(u - t)$ and $\sin(u - t)$ the coefficient $\frac14$.

The brackets of Table B.2 are those of
[Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds): the lower ones from the
Taylor polynomials of degrees 6 and 7, the upper ones of the sine from that
of degree 5. The resulting lower bounds, listed in Table B.3, are positive.
$\square$

| $x$ | $\cos x \ge$ | $\sin x \ge$ | $\sin x \le$ |
| :-: | :-: | :-: | :-: |
| $\frac4{15}$ | $0.964654$ | $0.263517$ | $0.263518$ |
| $\frac25$ | $0.921060$ | $0.389418$ | $0.389419$ |
| $\frac23$ | $0.785886$ | $0.618369$ | $0.618382$ |
| $\frac{16}{15}$ | $0.483004$ | $0.875590$ | $0.875903$ |

| length | $\le$ | length | $\le$ |
| :-: | :-: | :-: | :-: |
| $\sqrt{\frac{53}{200}}$ | $0.515$ | $\sqrt{\frac{61}{400} + \frac3{20}\sin\frac23}$ | $0.496$ |
| $\sqrt{\frac{53}{200} + \frac9{40}\sin\frac4{15}}$ | $0.57$ | $\sqrt{\frac{61}{400} + \frac3{20}\sin\frac25}$ | $0.46$ |
| $\sqrt{\frac{53}{200} + \frac9{40}\sin\frac25}$ | $0.6$ | $\sqrt{\frac{61}{400}}$ | $0.391$ |
| $\sqrt{\frac{53}{200} + \frac9{40}\sin\frac23}$ | $0.64$ | $\sqrt{\frac{61}{400} - \frac3{20}\sin\frac25}$ | $0.31$ |
| $\sqrt{\frac{53}{200} + \frac9{40}\sin\frac{16}{15}}$ | $0.7$ | | |

*Table B.2.* The brackets used at the vertices: of the cosine and the sine at
the four angles that occur (Lemma A.7 (2) to (4)), and of the lengths of the
forces, from the upper brackets of the sines; for instance
$\frac{53}{200} + \frac9{40}\cdot 0.263518 < 0.3243 < 0.57^2$.

| vertex | $(t, u)$ | $u - t$ | $\Phi_W$ | lengths | bound | $\Phi_D$ | lengths | bound |
| :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $v_1$ | $(-\frac23, -\frac25)$ | $\frac4{15}$ | $0.08695$ | $0.515$, $0.496$ | $0.0852$ | $0.05537$ | $0.57$, $0.46$ | $0.0531$ |
| $v_2$ | $(-\frac25, -\frac25)$ | $0$ | $0.06270$ | $0.515$, $0.46$ | $0.0610$ | $0.06270$ | $0.515$, $0.46$ | $0.0610$ |
| $v_3$ | $(-\frac23, 0)$ | $\frac23$ | $0.03783$ | $0.515$, $0.496$ | $0.0361$ | $0.01045$ | $0.64$, $0.391$ | $0.0023$ |
| $v_4$ | $(0, 0)$ | $0$ | $0.01176$ | $0.515$, $0.391$ | $0.0105$ | $0.01176$ | $0.515$, $0.391$ | $0.0105$ |
| $v_5$ | $(-\frac23, \frac25)$ | $\frac{16}{15}$ | $0.00274$ | $0.515$, $0.496$ | $0.0010$ | $0.04253$ | $0.7$, $0.31$ | $0.0026$ |
| $v_6$ | $(0, \frac25)$ | $\frac25$ | $0.06570$ | $0.515$, $0.391$ | $0.0644$ | $0.07370$ | $0.6$, $0.31$ | $0.0576$ |
| $v_7$ | $(\frac25, \frac25)$ | $0$ | $0.18363$ | $0.515$, $0.31$ | $0.1777$ | $0.18363$ | $0.515$, $0.31$ | $0.1777$ |

*Table B.3.* The west stresses at the seven vertices: the values of $\Phi_W$
and $\Phi_D$ (to five decimals), the brackets of the lengths $r$, $s$ used,
and the lower bounds obtained with $\bar c$, $\bar R$ and the brackets of
Table B.2 (rounded down). At $v_2$, $v_4$ and $v_7$, where $u = t$, the two
stresses coincide.

*Lean:
[`Six.westStressW_vertices`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L488),
[`Six.westStressD_vertices`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L512),
[`Six.diagonalVertexExpression`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L396),
[`Six.diagonal_lower_from_roots`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L401),
[`Six.diagonal_root_endpoints`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L412),
[`Six.west_minorant_positive`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L432),
[`Six.diagonal_minorant_endpoints`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L460),
[`Six.west_root_bound`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L55),
[`Six.westCentralSupport_upper`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L74),
[`cos_lower_six`](../../SquaresInCircles/Common/Trigonometry.lean#L214),
[`sin_lower_seven`](../../SquaresInCircles/Common/Trigonometry.lean#L221),
[`sin_upper_five`](../../SquaresInCircles/Common/Trigonometry.lean#L207).*

![The triangle of the angles (t, u) with -2/3 at most t, t at most u, and u between -2/5 and 2/5, cut by the lines u = 0 and t = 0 into three parts, shaded differently: u negative, t negative and u positive, and t positive. The seven vertices v1 to v7 of the parts are marked, each labelled with the values of the two west stresses there, Phi_W first and Phi_D second, all positive; dotted horizontal segments indicate directions in which the stresses are concave](figures/appendix-b/triangle.svg)

*Figure B.13.* The triangle $\Delta$ of the angles $(t, u)$, cut into its
three parts, and the seven vertices with the values $\Phi_W / \Phi_D$ there.
Along each horizontal segment (dotted) inside a part, the stresses are concave
in $t$; along the vertical edges $t = -\frac23$ and $t = 0$ and along the
diagonal they are concave in $u$, piece by piece. So their values at the
vertices bound them below on the whole triangle (Lemma B.20). The smallest
value is $\Phi_W(v_5) \approx 0.0027$, where $W$ is turned furthest from
$D$.

*Proof of [Proposition 9.33](09-six.md#proposition-933-the-west-stress).*
Suppose that $W$ and $D$ are disjoint. By Lemma 9.31 they are separated along
$e^W_2$ or along $e^D_2$, and by Lemma B.18, $\Phi_W(t, u) \le 0$ or
$\Phi_D(t, u) \le 0$, where $(t, u) \in \Delta$. But by Lemma B.19 each of
$\Phi_W$ and $\Phi_D$ has the form of Lemma B.20, with
$J = J(\cdot; R_0)$, $H = H(\cdot; 0)$, $G = G(\cdot; 0)$ for $\Phi_W$ and
$J = J(\cdot; 0)$, $H = H(\cdot; R_0)$, $G = G(\cdot; R_0)$ for $\Phi_D$, and
by Lemma B.21 both are positive at the seven vertices. By Lemma B.20 both are
positive on $\Delta$, a contradiction. $\square$

*Lean:
[`Six.west_cardinal_impossible`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L788),
[`Six.west_secondary_axes`](../../SquaresInCircles/Six/Normalization/WestPair.lean#L157),
[`Six.turned_pair_secondary`](../../SquaresInCircles/Six/Normalization/WestPair.lean#L103),
[`Six.westStressW_positive`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L545),
[`Six.westStressD_positive`](../../SquaresInCircles/Six/Normalization/WestStress.lean#L578).*
