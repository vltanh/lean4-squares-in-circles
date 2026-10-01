# Appendix A. One-variable estimates and the marker arc

[Contents](README.md) · [← 9. Seven squares](seven.md) · [Appendix B →](appendix-b.md)

This appendix proves the facts about functions of one real variable on which
the analysis of seven squares rests, and then uses them to prove the marker
arc lemma of [Chapter 9](seven.md), [Lemma 9.9](seven.md#lemma-99-the-marker-arc).

§A.1 derives monotonicity, tangent parabolas and concavity bounds from
derivatives. §A.2 compares the sine and the cosine and bounds them by their
Taylor polynomials of degrees 4 to 7. §A.3 bounds a function by its value at
the point where its derivative changes sign. With these tools an inequality
between functions of one angle becomes an inequality between polynomials on an
interval, and that is settled by completing squares, by the signs of a few
factors and by comparing rational numbers. Chapter 9 and Appendices B to D use
them in this way throughout. §A.4 proves the marker arc lemma, a typical
instance: it needs all three tools, together with the elementary estimates of
[Lemma 3.29](common.md#lemma-329-elementary-estimates).

We use the conventions of §2.1: in particular $\arcsin$ is extended to all of
$\mathbb R$ (it is odd and nondecreasing) and
$\arccos x = \frac\pi2 - \arcsin x$. Of the classical bounds on $\pi$ we only
need $\pi > 3.14$.

## A.1 Monotonicity and concavity

A function $f$ *has derivative* $c$ at a point $y$ if it is defined on a
neighbourhood of $y$, differentiable at $y$, and $f'(y) = c$. A function that
has a derivative at every point of an interval is continuous on it.

### Lemma A.1 (monotonicity from the derivative)

Let $f$ be a real function and $l$, $u$ real numbers.

1. If $f$ is continuous on $[l, u]$ and has a derivative $f'(y) \ge 0$ at every
   $y \in (l, u)$, then $f$ is nondecreasing on $[l, u]$.
2. If $f$ is continuous on $[l, u]$ and has a derivative $f'(y) \le 0$ at every
   $y \in (l, u)$, then $f$ is nonincreasing on $[l, u]$.
3. If $f$ is differentiable on $\mathbb R$, $f(0) = 0$ and $f'(y) \ge 0$ for
   every $y \ge 0$, then $f(x) \ge 0$ for every $x \ge 0$.

*Proof.* (1) Let $l \le x < y \le u$. By the mean value theorem there is
$\xi \in (x, y)$ with $f(y) - f(x) = f'(\xi)(y - x) \ge 0$. (2) Apply (1) to
$-f$. (3) For $x > 0$, (1) on $[0, x]$ gives $f(x) \ge f(0) = 0$. $\square$

*Lean:
[`monoOn_of_hasDeriv_nonneg`](../../SquaresInCircles/Common/Analysis.lean#L29),
[`antiOn_of_hasDeriv_nonpos`](../../SquaresInCircles/Common/Analysis.lean#L37),
[`nonneg_of_deriv_nonneg`](../../SquaresInCircles/Common/Analysis.lean#L47).*

### Lemma A.2 (tangent parabolas)

Let $l$, $u$, $\kappa$ be real numbers and $f$, $d$, $e$ real functions such
that at every $y \in [l, u]$, $f$ has derivative $d(y)$, $d$ has derivative
$e(y)$, and $e(y) \ge \kappa$. Then for all $x, t \in [l, u]$

```math
f(x) \ge f(t) + d(t)(x - t) + \tfrac\kappa2 (x - t)^2 .
```

*Proof.* Fix $t \in [l, u]$ and put

```math
h(y) = f(y) - f(t) - d(t)(y - t) - \tfrac\kappa2 (y - t)^2 , \qquad
h_1(y) = d(y) - d(t) - \kappa(y - t) .
```

At every $y \in [l, u]$, $h$ has derivative $h_1(y)$ and $h_1$ has derivative
$e(y) - \kappa \ge 0$; in particular both are continuous on $[l, u]$. By
Lemma A.1 (1), $h_1$ is nondecreasing on $[l, u]$, and $h_1(t) = 0$, so
$h_1 \le 0$ on $[l, t]$ and $h_1 \ge 0$ on $[t, u]$. By Lemma A.1 again, $h$ is
nonincreasing on $[l, t]$ and nondecreasing on $[t, u]$. As $h(t) = 0$, we get
$h \ge 0$ on $[l, u]$, and $h(x) \ge 0$ is the claim. $\square$

*Lean: [`curvature_tangent`](../../SquaresInCircles/Common/Analysis.lean#L148).*

With $\kappa = 0$, Lemma A.2 says that a function with a nonnegative second
derivative lies above its tangent lines; applied to $-f$, that a function with
a nonpositive second derivative lies below them.

### Lemma A.3 (positivity from curvature)

Let $l$, $u$, $\kappa$ be real numbers with $\kappa > 0$, and $f$, $d$, $e$ real
functions such that at every $y \in [l, u]$, $f$ has derivative $d(y)$, $d$ has
derivative $e(y)$, and $e(y) \ge \kappa$. If some $t \in [l, u]$ satisfies
$d(t)^2 < 2\kappa f(t)$, then $f(x) > 0$ for every $x \in [l, u]$.

![A convex blue curve f over an interval from l to u, touching at the point (t, f(t)) a dashed orange parabola that stays below it; a green vertical segment from the x-axis up to the lowest point of the parabola shows that this lowest value f(t) minus d(t) squared over 2 kappa is positive](figures/appa-curvature.svg)

*Figure A.1.* Lemmas A.2 and A.3. The function $f$ (blue) has second
derivative at least $\kappa$ on $[l, u]$, so it lies above its tangent parabola
of curvature $\kappa$ at $t$ (dashed). When $d(t)^2 < 2\kappa f(t)$, the lowest
value of the parabola, $f(t) - d(t)^2/2\kappa$ (green), is positive.

*Proof.* Let $x \in [l, u]$ and $s = x - t$. By Lemma A.2 and $\kappa > 0$,

```math
2\kappa f(x) \ge 2\kappa f(t) + 2\kappa d(t) s + \kappa^2 s^2
= \left(\kappa s + d(t)\right)^2 + \left(2\kappa f(t) - d(t)^2\right) > 0 . \qquad \square
```

*Lean:
[`positive_of_curvature`](../../SquaresInCircles/Common/Analysis.lean#L178).*

### Lemma A.4 (positivity from concavity)

Let $l \le u$, and let $f$, $d$, $e$ be real functions such that at every
$y \in [l, u]$, $f$ has derivative $d(y)$, $d$ has derivative $e(y)$, and
$e(y) \le 0$. If $f(l) > 0$ and $f(u) > 0$, then $f(x) > 0$ for every
$x \in [l, u]$.

*Proof.* For $x = l$ or $x = u$ there is nothing to prove, so let
$l < x < u$. By Lemma A.1 (2), $d$ is nonincreasing on $[l, u]$. By the mean
value theorem there are $\xi_1 \in (l, x)$ and $\xi_2 \in (x, u)$ with

```math
\frac{f(x) - f(l)}{x - l} = d(\xi_1) \ge d(\xi_2) = \frac{f(u) - f(x)}{u - x} .
```

Multiplying out,

```math
f(x) \ge \frac{(u - x) f(l) + (x - l) f(u)}{u - l} \ge \min\left(f(l), f(u)\right) > 0 . \qquad \square
```

*Lean:
[`positive_of_second_nonpos`](../../SquaresInCircles/Common/Analysis.lean#L139).*

### Lemma A.5 (concave trigonometric sums)

Let $\alpha$, $A$, $B$, $m$, $l$, $u$ be real numbers with $A \ge 0$, $B \ge 0$
and $0 \le l \le u \le \frac\pi2$, and put
$F(y) = \alpha y + A\sin y + B\cos y$. If $m < F(l)$ and $m < F(u)$, then
$m < F(x)$ for every $x \in [l, u]$.

![A concave blue arc over an interval from l to u inside zero to pi over 2, above the orange chord joining its end points, and a dashed horizontal level m below both end points](figures/appa-concave.svg)

*Figure A.2.* Lemmas A.4 and A.5, for $F(y) = -\frac y5 + \sin y + \cos y$. On
$[l, u] \subset [0, \frac\pi2]$ the function is concave, so it lies above its
chord (orange); if both end values exceed $m$, so does every value between.

*Proof.* Apply Lemma A.4 to $F - m$, with $d(y) = \alpha + A\cos y - B\sin y$
and $e(y) = -A\sin y - B\cos y$. For $y \in [l, u] \subset [0, \frac\pi2]$ we
have $\sin y \ge 0$ and $\cos y \ge 0$, so $e(y) \le 0$. $\square$

*Lean:
[`trig_concave_gt`](../../SquaresInCircles/Common/Trigonometry.lean#L323).*

## A.2 Sine and cosine

### Lemma A.6 (sine and cosine compared)

1. If $0 \le x \le \frac\pi4$, then $\sin x \le \cos x$.
2. If $\frac\pi4 \le x \le \frac\pi2$, then $\cos x \le \sin x$.
3. If $0 \le z \le \frac\pi3$, then $\cos z \ge \frac12$.

![The sine rising and the cosine falling on zero to pi over 2; they cross at pi over 4, and the cosine reaches one half at pi over 3](figures/appa-sin-cos.svg)

*Figure A.3.* Lemma A.6: on $[0, \frac\pi2]$ the sine and the cosine cross at
$\frac\pi4$, and the cosine stays at least $\frac12$ up to $\frac\pi3$.

*Proof.* The cosine is decreasing on $[0, \pi]$, and
$\sin y = \cos(\frac\pi2 - y)$. (1) Here $0 \le x \le \frac\pi2 - x \le \pi$,
so $\sin x = \cos(\frac\pi2 - x) \le \cos x$. (2) Here
$0 \le \frac\pi2 - x \le x \le \pi$, so
$\cos x \le \cos(\frac\pi2 - x) = \sin x$. (3)
$\cos z \ge \cos\frac\pi3 = \frac12$. $\square$

*Lean:
[`sin_le_cos_of_small`](../../SquaresInCircles/Common/Trigonometry.lean#L50),
[`cos_le_sin_of_quarter`](../../SquaresInCircles/Common/Trigonometry.lean#L54),
[`cos_ge_half`](../../SquaresInCircles/Common/Trigonometry.lean#L59).*

### Lemma A.7 (Taylor bounds)

For every $x \ge 0$:

1. $\cos x \le 1 - \frac{x^2}2 + \frac{x^4}{24}$;
2. $\sin x \le x - \frac{x^3}6 + \frac{x^5}{120}$;
3. $\cos x \ge 1 - \frac{x^2}2 + \frac{x^4}{24} - \frac{x^6}{720}$;
4. $\sin x \ge x - \frac{x^3}6 + \frac{x^5}{120} - \frac{x^7}{5040}$.

![Two panels on zero to 3.2. Left: the cosine in blue between its Taylor polynomial of degree 4, dashed orange above, and of degree 6, dashed green below. Right: the sine in blue between its Taylor polynomial of degree 5 above and of degree 7 below. The curves agree near zero and separate beyond about 2](figures/appa-taylor.svg)

*Figure A.4.* Lemma A.7 on $[0, 3.2]$: the cosine lies between its Taylor
polynomials of degrees 6 (below) and 4 (above), the sine between those of
degrees 7 (below) and 5 (above). On $[0, \frac\pi2]$, where the bounds are
mostly used, the polynomials cannot be told apart from the functions at this
scale.

*Proof.* Consider the eight functions

```math
\begin{aligned}
g_0(x) &= 1 - \cos x , &
g_1(x) &= x - \sin x , \\
g_2(x) &= \cos x - 1 + \tfrac{x^2}2 , &
g_3(x) &= \sin x - x + \tfrac{x^3}6 , \\
g_4(x) &= 1 - \tfrac{x^2}2 + \tfrac{x^4}{24} - \cos x , &
g_5(x) &= x - \tfrac{x^3}6 + \tfrac{x^5}{120} - \sin x , \\
g_6(x) &= \cos x - 1 + \tfrac{x^2}2 - \tfrac{x^4}{24} + \tfrac{x^6}{720} , &
g_7(x) &= \sin x - x + \tfrac{x^3}6 - \tfrac{x^5}{120} + \tfrac{x^7}{5040} .
\end{aligned}
```

Up to sign, $g_k$ is the remainder of the Taylor polynomial of degree $k$ at 0
of the cosine ($k$ even) or the sine ($k$ odd). Since $\sin' = \cos$ and
$\cos' = -\sin$, each remainder has the previous one as its derivative:
$g_k' = g_{k-1}$ for $k = 1, \dots, 7$, as one checks term by term; and
$g_k(0) = 0$ for $k \ge 1$. Now $g_0 \ge 0$ everywhere, and if
$g_{k-1} \ge 0$ on $[0, \infty)$, then Lemma A.1 (3) gives $g_k \ge 0$ on
$[0, \infty)$. So $g_0, \dots, g_7 \ge 0$ on $[0, \infty)$. For $k \le 3$ these
are the classical bounds $\sin x \le x$, $\cos x \ge 1 - \frac{x^2}2$ and
$\sin x \ge x - \frac{x^3}6$; $g_4, g_5, g_6, g_7 \ge 0$ are (1) to (4).
$\square$

*Lean: [`cos_upper_four`](../../SquaresInCircles/Common/Trigonometry.lean#L200),
[`sin_upper_five`](../../SquaresInCircles/Common/Trigonometry.lean#L207),
[`cos_lower_six`](../../SquaresInCircles/Common/Trigonometry.lean#L214),
[`sin_lower_seven`](../../SquaresInCircles/Common/Trigonometry.lean#L221).*

Both sides of (1) and (3) are even functions of $x$, so these two bounds hold
for every real $x$.

### Lemma A.8 (polynomial brackets)

Let $0 \le l \le u \le \frac\pi2$ and $x \in [l, u]$. Then

```math
l - \tfrac{l^3}6 + \tfrac{l^5}{120} - \tfrac{l^7}{5040} \le \sin x \le u - \tfrac{u^3}6 + \tfrac{u^5}{120} ,
\qquad
1 - \tfrac{u^2}2 + \tfrac{u^4}{24} - \tfrac{u^6}{720} \le \cos x \le 1 - \tfrac{l^2}2 + \tfrac{l^4}{24} .
```

*Proof.* The sine is increasing on $[-\frac\pi2, \frac\pi2] \supset [l, u]$ and
the cosine decreasing on $[0, \pi] \supset [l, u]$, so
$\sin l \le \sin x \le \sin u$ and $\cos u \le \cos x \le \cos l$. Now apply
Lemma A.7 (4) at $l$, (2) at $u$, (3) at $u$ and (1) at $l$. $\square$

*Lean: [`trig_bracket`](../../SquaresInCircles/Common/Trigonometry.lean#L229).*

## A.3 A peak

### Lemma A.9 (a peak)

Let $l \le c \le u$, and let $f$, $d$ be real functions such that $f$ has
derivative $d(y)$ at every real $y$, with $d(y) \ge 0$ for $y \in [l, c]$ and
$d(y) \le 0$ for $y \in [c, u]$. Then $f(x) \le f(c)$ for every
$x \in [l, u]$.

![Two curves over an interval from l to u, split at c into a green strip on the left and an orange strip on the right. Below, the derivative d in purple: positive at l, touching zero at one point, rising to a hump, crossing zero at c and negative after it. Above, the function f in blue: it rises, flattens where d touches zero (a dashed segment joins the two points), rises again to its peak at c and falls; a dashed horizontal line at the height f(c) lies above the whole graph](figures/appa-peak.svg)

*Figure A.5.* Lemma A.9 for $f(y) = \frac{y^3}3 - \frac{y^4}4$ on
$[l, u] = [-0.35, 1.25]$ and $c = 1$. The derivative $d(y) = y^2(1 - y)$
(below) is nonnegative on $[l, c]$ (green), where it vanishes at $y = 0$, and
nonpositive on $[c, u]$ (orange). So $f$ (above) rises up to $c$, with a flat
point at 0, falls after it, and stays below its value at $c$ (dashed),
although it is not concave.

*Proof.* As $f$ has a derivative everywhere, it is continuous. Let
$x \in [l, u]$. If $x \le c$, then $f$ is nondecreasing on $[l, c]$ by
Lemma A.1 (1), so $f(x) \le f(c)$. If $x \ge c$, then $f$ is nonincreasing on
$[c, u]$ by Lemma A.1 (2), so again $f(x) \le f(c)$. $\square$

*Lean: [`le_at_peak`](../../SquaresInCircles/Common/Analysis.lean#L54).*

In use, $d(y)$ is a product of factors of constant sign on $[l, u]$ and one
affine factor that vanishes at $c$; Lemma A.14 is an example (Figure A.11).

## A.4 Proof of Lemma 9.9

We prove the marker arc lemma of Chapter 9, [Lemma 9.9](seven.md#lemma-99-the-marker-arc):

> *Let $(a, u)$ be an admissible state and $t$ a real number with
> $|t - \ell(a, u)| \le \frac12$. Then $|\cos t - a| \le \frac12$ and
> $|\sin t - u| \le \frac12$.*

We recall the notions involved. A state $(a, u)$ is *admissible*
([Definition 9.4](seven.md#definition-94-states)) if

```math
\tfrac12 \le a , \qquad 0 \le u \le a , \qquad
\varphi(a, u) = \left(a + \tfrac12\right)^2 + \left(u + \tfrac12\right)^2 \le \tfrac{13}4 ,
```

where $\varphi$ is the farthest-vertex function of
[Definition 3.3](common.md#definition-33-farthest-vertex-function). Its
*label* ([Definition 9.6](seven.md#definition-96-labels-and-markers)) is

```math
\ell(a, u) = \min\left(\mathrm{axial}(u), \mathrm{side}(a, u), \tfrac\pi4\right) , \qquad
\mathrm{axial}(u) = \tfrac54 u , \qquad
\mathrm{side}(a, u) = \tfrac\pi6 + \tfrac13\left(u - \tfrac12\right) + \tfrac34(1 - a) ,
```

so $\ell(a, u)$ is at most each of the three terms. For an admissible state,
$u < \frac{31}{40}$ ([Lemma 9.5](seven.md#lemma-95-admissible-states)), $a < \frac54$
([Lemma 9.5](seven.md#lemma-95-admissible-states)) and $\ell(a, u) \ge 0$
([Lemma 9.7](seven.md#lemma-97-the-label)).

![The admissible states in the (a, u)-plane: a region bounded by the segment of the a-axis from one half to root 3 minus one half, the arc of the circle phi equals 13/4 up to the diagonal, the diagonal u equals a, and the vertical line a equals one half. An orange line touches the circle at about (0.85, 0.70); a green vertical segment at a = x + 1/2 rises from the a-axis to the circle; the side state (1, 1/2) is marked on the circle](figures/appa-admissible.svg)

*Figure A.6.* The admissible states (shaded). The line
$\frac34(a + \frac12) + \frac23(u + \frac12) = \frac{\sqrt{1885}}{24}$ (orange)
touches the circle $\varphi = \frac{13}4$ at the dot, and the disk lies below
it (step 3 of Lemma A.11). At $a = x + \frac12$ the circle bounds
$u + \frac12$ by $\sqrt{13/4 - (x + 1)^2}$ (green; step 1 of Lemma A.17).

In the chart of an exterior square with state $(a, u)$ (Chapter 9) the closed
square is $[a - \frac12, a + \frac12] \times [u - \frac12, u + \frac12]$ and
the unit circle $\Gamma_1$ about the disk centre is
$t \mapsto (\cos t, \sin t)$. So the lemma says that the arc of $\Gamma_1$ of
half-width $\frac12$ about the direction $\ell(a, u)$ lies in the
closed square: it stays on the correct side of each of the four edge lines
(Figure A.7).

![Two panels, each showing an admissible square in its chart with the lines of its near, far, lower and upper edges dashed, the unit circle about o, a dashed ray at the label angle, and a thick orange arc of the circle about that ray. The thin blue part of the circle between two dots is the part inside the square, and it contains the orange arc. Left, the state (1, 1/2), where the orange arc nearly fills the blue part; right, the state (0.9, 0.3)](figures/appa-marker-arc.svg)

*Figure A.7.* The marker arc lemma in the chart, for the side state
$(1, \frac12)$ (left) and the state $(0.9, 0.3)$, whose label is axial
(right). The part of $\Gamma_1$ in the closed square (blue, between the dots)
contains the arc of half-width $\frac12$ about the label (orange). For the
side state the fit is tight at both ends: the square holds the arc from 0 to
$\frac\pi3$, of half-width $\frac\pi6 \approx 0.5236$, against $\frac12$.

*Idea of the proof.* The far edge is out of reach. For the lower and upper
edges we compare the label with $\arcsin(u \mp \frac12)$ using lines of slope
$\frac54$ (Lemmas A.10 to A.12). For the near edge we need
$\ell + \arcsin(a - \frac12) + \frac12 < \frac\pi2$. Bounding $\ell$
by the side term and $u$ by the circle $\varphi = \frac{13}4$ leaves a function
$E$ of $x = a - \frac12$ alone, the envelope. Its second derivative is at
most $-\frac18$ (Lemmas A.14 and A.15), so it lies below the parabola that
shares its value and slope at $x = 0$, where both radicands are squares of
rationals; that parabola is highest at $x = \frac29$, at the height
$\frac\pi6 + \frac{353}{648}$ (Lemma A.16). Lemma A.17 concludes.

### Lemma A.10 (a line against the arcsine)

Let $g(y) = \frac54 y - \arcsin y$ for $-1 \le y \le 1$.

1. $g$ is nondecreasing on $[-\frac35, \frac35]$.
2. $g$ is nonincreasing on $[\frac35, 1]$.
3. $\arcsin\frac12 = \frac\pi6$.

![The graph of g(y) = 5/4 y minus arcsin y on minus 1 to 1: it falls to a minimum at minus 3/5, rises to a maximum at 3/5 and falls again. An orange band over minus 1/2 to 11/40 with a dashed line at the value at minus 1/2 lies below the graph there; a green band over 1/2 to 1 with a dashed line at the value at 3/5 lies above the graph there](figures/appa-asin-line.svg)

*Figure A.8.* The function $g$ of Lemma A.10. On the range
$[-\frac12, \frac{11}{40})$ of $y = u - \frac12$ (orange) it stays above
$g(-\frac12) = \frac\pi6 - \frac58$, which is step 2 of Lemma A.11. On the
range $[\frac12, 1]$ of $y = u + \frac12$ when $u \le \frac12$ (green) it
stays below $g(\frac35) = \frac34 - \arcsin\frac35$, which is step 2 of
Lemma A.12.

*Proof.* The arcsine is continuous on $[-1, 1]$ and has derivative
$1/\sqrt{1 - y^2}$ at every $y \in (-1, 1)$. So $g$ is continuous on
$[-1, 1]$, with $g'(y) = \frac54 - 1/\sqrt{1 - y^2}$ for $|y| < 1$.
(1) If $|y| < \frac35$, then $1 - y^2 > \frac{16}{25}$, so
$\sqrt{1 - y^2} > \frac45$ and $g'(y) > 0$; apply Lemma A.1 (1).
(2) If $\frac35 < y < 1$, then $0 < 1 - y^2 < \frac{16}{25}$, so
$\sqrt{1 - y^2} < \frac45$ and $g'(y) < 0$; apply Lemma A.1 (2).
(3) $\sin\frac\pi6 = \frac12$ and $-\frac\pi2 \le \frac\pi6 \le \frac\pi2$.
$\square$

*Lean:
[`Seven.asin_line_mono`](../../SquaresInCircles/Seven/Exterior.lean#L235),
[`asin_half`](../../SquaresInCircles/Common/Trigonometry.lean#L717).*

By (1) and (2), $g(\frac35) = \frac34 - \arcsin\frac35$ is the largest value of
$g$ on $[-\frac35, 1]$. The next two lemmas place the label between the lower
and the upper edge (Figure A.9).

![The (u, angle)-plane for u from 0 to 31/40. A thin blue shaded band, the labels of the admissible states, starts at the origin, widens towards the right and closes again in a point just below the angle pi/4. An orange curve, arcsin(u - 1/2) + 1/2, runs just below the band; a green curve, arcsin(u + 1/2) - 1/2, runs above it for u up to 1/2 and rises steeply there](figures/appa-transverse.svg)

*Figure A.9.* Lemmas A.11 and A.12. For each $u$ the labels $\ell(a, u)$ of
the admissible states $(a, u)$ fill the shaded interval. It lies above the
curve $\arcsin(u - \frac12) + \frac12$ of the lower edge (orange) and, for
$u \le \frac12$, below the curve $\arcsin(u + \frac12) - \frac12$ of the
upper edge (green). The closest approach, about 0.005, is at the lower edge
near $u = 0.72$, where the label is a side label.

### Lemma A.11 (the lower edge)

Let $(a, u)$ be an admissible state. Then
$\arcsin(u - \frac12) + \frac12 < \ell(a, u)$.

*Proof.* Put $y = u - \frac12$. As $0 \le u < \frac{31}{40}$,
$-\frac12 \le y < \frac{11}{40}$. We show that $\arcsin y + \frac12$ is
less than each of the three terms whose minimum is $\ell(a, u)$.

1. *A bound on the arcsine: $\arcsin y < y + 0.0052$.* If
   $y \ge 0$, then $y < \frac{11}{40} < \frac35$, and
   [Lemma 3.29](common.md#lemma-329-elementary-estimates) (3) gives

   ```math
   \arcsin y \le y + \tfrac{y^3}4 \le y + \tfrac14\left(\tfrac{11}{40}\right)^3 < y + 0.0052 .
   ```

   If $y < 0$, then $\arcsin y \le y$ by Lemma 3.29 (2), as $y \ge -1$.
2. *The axial term.* Both $-\frac12$ and $y$ lie in $[-\frac35, \frac35]$, and
   $-\frac12 \le y$. By Lemma A.10 (1) and (3), and as the arcsine is odd,

   ```math
   \tfrac\pi6 - \tfrac58 = g\left(-\tfrac12\right) \le g(y) = \tfrac54 u - \tfrac58 - \arcsin y ,
   ```

   that is, $\arcsin y \le \mathrm{axial}(u) - \frac\pi6$. Since
   $\frac\pi6 > \frac{3.14}6 > \frac12$, we get
   $\arcsin y + \frac12 < \mathrm{axial}(u)$.
3. *The side term.* Put $p = a + \frac12$, $q = u + \frac12$ and
   $L = \frac34 p + \frac23 q$. By the Cauchy–Schwarz inequality, with
   $\varphi(a, u) = p^2 + q^2 \le \frac{13}4$,

   ```math
   L^2 \le \left(\tfrac9{16} + \tfrac49\right)\left(p^2 + q^2\right) \le \tfrac{145}{144} \cdot \tfrac{13}4 ,
   ```

   so $L \le \frac{\sqrt{1885}}{24}$, with equality where the line
   $L = \frac{\sqrt{1885}}{24}$ touches the circle (Figure A.6). By the
   definition of the side term, and as $\sqrt{1885} < 43.42$,

   ```math
   \mathrm{side}(a, u) - y = \tfrac\pi6 - \tfrac23 y - \tfrac34 (a - 1) = \tfrac\pi6 + \tfrac{43}{24} - L
   > \tfrac\pi6 - \tfrac{43.42 - 43}{24} = \tfrac\pi6 - 0.0175 .
   ```

   With step 1, and as $\frac\pi6 > \frac{3.14}6 > 0.5233$,

   ```math
   \mathrm{side}(a, u) - \arcsin y - \tfrac12 > \tfrac\pi6 - 0.0175 - 0.0052 - 0.5 > 0 .
   ```

4. *The cap.* By step 1, and as $y < \frac{11}{40}$,
   $\arcsin y + \frac12 < \frac{11}{40} + 0.0052 + \frac12 = 0.7802 < \frac{3.14}4 < \frac\pi4$.

So $\arcsin y + \frac12$ is less than $\mathrm{axial}(u)$,
$\mathrm{side}(a, u)$ and $\frac\pi4$, hence less than their minimum
$\ell(a, u)$. $\square$

*Lean:
[`Seven.marker_lower_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L257),
[`dot_gt`](../../SquaresInCircles/Common/DiskSupport.lean#L34).*

### Lemma A.12 (the upper edge)

Let $(a, u)$ be an admissible state with $u \le \frac12$. Then
$\ell(a, u) + \frac12 < \arcsin(u + \frac12)$.

*Proof.*

1. *$\arcsin\frac35 > \frac58$.* By Lemma A.7 (2),

   ```math
   \sin\tfrac58 \le \tfrac58 - \tfrac16\left(\tfrac58\right)^3 + \tfrac1{120}\left(\tfrac58\right)^5 < 0.5852 < \tfrac35 .
   ```

   If $\arcsin\frac35 \le \frac58$, then, as
   $-\frac\pi2 \le \arcsin\frac35 \le \frac58 < \frac\pi2$ and the sine
   is increasing on $[-\frac\pi2, \frac\pi2]$, we would get
   $\frac35 = \sin(\arcsin\frac35) \le \sin\frac58 < \frac35$.
2. Put $y = u + \frac12 \in [\frac12, 1]$. By Lemma A.10 (1) if
   $y \le \frac35$, and by Lemma A.10 (2) if $y \ge \frac35$,
   $g(y) \le g(\frac35)$, that is,
   $\arcsin y \ge \arcsin\frac35 + \frac54(y - \frac35)$. As
   $\frac54(y - \frac35) = \frac54 u - \frac18$, step 1 gives

   ```math
   \arcsin y > \tfrac58 + \tfrac54 u - \tfrac18 = \tfrac54 u + \tfrac12 .
   ```

3. As $\ell(a, u) \le \mathrm{axial}(u) = \frac54 u$, step 2 gives
   $\arcsin(u + \frac12) > \ell(a, u) + \frac12$. $\square$

*Lean:
[`Seven.marker_horizontal_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L459).*

### Definition A.13 (the envelope)

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
on $[0, \frac34]$ (Lemma A.15).

*Lean: [`Seven.arcEnvelope`](../../SquaresInCircles/Seven/Exterior.lean#L286),
[`Seven.arcEnvelopeDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L289),
[`Seven.arcEnvelopeSecond`](../../SquaresInCircles/Seven/Exterior.lean#L292).*

The definition of the side term can be written

```math
\mathrm{side}(a, u) = \tfrac\pi6 + \tfrac1{24} + \tfrac13\left(u + \tfrac12\right) - \tfrac34\left(a - \tfrac12\right) . \tag{A.1}
```

For an admissible state with $a - \frac12 = x$, the disk bounds $u + \frac12$
by $\sqrt{13/4 - (x + 1)^2}$, so $E(x)$ bounds
$\mathrm{side}(a, u) + \arcsin x$ from above; this is where the name comes
from (Lemma A.17 and Figure A.10).

![For x from 0 to 3/4, a blue shaded region bounded below by a rising curve and above by a curve that meets an orange curve, the graph of E(x) - pi/6, for x beyond about 0.27 and stays below it before; the region ends at x = root 3 - 1. A dashed horizontal line slightly above the orange curve marks the level pi/3 - 1/2](figures/appa-envelope-band.svg)

*Figure A.10.* The envelope. For each $x = a - \frac12$, the values of
$\mathrm{side}(a, u) + \arcsin x - \frac\pi6$ over the admissible states
$(a, u)$ fill the shaded interval; it ends at $x = \sqrt3 - 1$, beyond which
$u$ would have to be negative. The top of the interval lies on the graph of
$E(x) - \frac\pi6$ (orange) where the circle $\varphi = \frac{13}4$ rather
than $u \le a$ bounds $u$, that is, for $x \ge \sqrt{13/8} - 1 \approx 0.27$.
Lemma A.17 needs everything below the dashed level $\frac\pi3 - \frac12$.

### Lemma A.14 (the peak bound)

Let $h(x) = 9\left(x + \frac18\right)^2 (9 - 7x)^3$. Then $h(x) < 676$ for
every $x \in [0, \frac34]$.

![The graph of h on zero to 3/4, in blue: it rises from about 102 at 0 to its peak, about 596, at x = 123/280, marked by a dot with dotted lines to both axes, and falls to about 363 at 3/4. The strip over zero to 123/280 is shaded green and marked h prime at least 0; the strip over 123/280 to 3/4 is shaded orange and marked h prime at most 0. A dashed horizontal line at 676 lies above the whole graph](figures/appa-peak-bound.svg)

*Figure A.11.* Lemma A.14. The polynomial $h$ on $[0, \frac34]$ (blue). Its
derivative is nonnegative up to $\frac{123}{280}$ (green) and nonpositive after
it (orange), so by Lemma A.9 its largest value is the peak
$h(\frac{123}{280}) \approx 596.1$, below 676 (dashed).

*Proof.* By the product rule, $h$ has at every real $y$ the derivative

```math
h'(y) = 9\left(y + \tfrac18\right)(9 - 7y)^2\left(2(9 - 7y) - 21\left(y + \tfrac18\right)\right)
= 9\left(y + \tfrac18\right)(9 - 7y)^2\left(\tfrac{123}8 - 35y\right) .
```

For $y \in [0, \frac34]$ the factors $y + \frac18$ and $(9 - 7y)^2$ are
nonnegative, and $\frac{123}8 - 35y = 35\left(\frac{123}{280} - y\right)$ is
nonnegative for $y \le \frac{123}{280}$ and nonpositive for
$y \ge \frac{123}{280}$. By Lemma A.9 on $[0, \frac34]$, with the peak
$c = \frac{123}{280}$, $h(x) \le h(c)$. At the peak
$c + \frac18 = \frac{79}{140} < \frac47$, so
$(c + \frac18)^2 < \frac{16}{49} < \frac13$; and
$9 - 7c = 9 - \frac{123}{40} = \frac{237}{40} < 6$. Hence

```math
h(c) < 9 \cdot \tfrac13 \cdot 6^3 = 648 < 676 . \qquad \square
```

*Lean:
[`Seven.curvature_peak_lt`](../../SquaresInCircles/Seven/Exterior.lean#L358).*

For orientation, $h(0) \approx 102.5$, $h(\frac{123}{280}) \approx 596.1$ and
$h(\frac34) \approx 363.4$.

### Lemma A.15 (the curvature of the envelope)

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
   With Lemma A.14 and $A^6 > 0$,

   ```math
   \left(12\left(x + \tfrac18\right)B^3\right)^2 = \tfrac94\left(x + \tfrac18\right)^2 \cdot 64B^6
   \le \tfrac14 \cdot 9\left(x + \tfrac18\right)^2(9 - 7x)^3 \cdot A^6
   < \tfrac{676}4 A^6 = \left(13A^3\right)^2 .
   ```

   Both $12(x + \frac18)B^3$ and $13A^3$ are positive, so
   $12(x + \frac18)B^3 < 13A^3$, and $E_2(x) < -\frac18$. $\square$

*Lean:
[`Seven.arcEnvelopeSecond_le`](../../SquaresInCircles/Seven/Exterior.lean#L384),
[`Seven.arc_radicands`](../../SquaresInCircles/Seven/Exterior.lean#L295),
[`Seven.arcEnvelope_hasDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L300),
[`Seven.arcEnvelopeDeriv_hasDeriv`](../../SquaresInCircles/Seven/Exterior.lean#L317).*

The two terms of $E_2$ come from the arcsine, which bends up, and from the
circle $\varphi = \frac{13}4$, which bends down: $B$ is the value of
$u + \frac12$ on that circle at $a = x + \frac12$ (Figure A.6). On
$[0, \frac34]$ the circle wins by at least $\frac18$. For orientation,
$E_2(0) = -\frac{26}{81} \approx -0.321$, and the largest value of $E_2$ on
$[0, \frac34]$ is about $-0.209$, near $x = 0.33$.

### Lemma A.16 (the envelope bound)

For every $x \in [0, \frac34]$, $E(x) \le \frac\pi6 + \frac{353}{648}$.

![The graph of E(x) - pi/6 on zero to 3/4 in orange: it starts at 13/24, marked by a dot on the vertical axis, rises slightly, and falls to about 0.47 at 3/4. A dashed purple parabola, 13/24 + x/36 - x squared/16, starts at the same dot with the same slope and stays above the orange curve; its highest point, at x = 2/9, is marked by a purple dot at the height 353/648. A black horizontal line at pi/3 - 1/2 lies just above that point](figures/appa-parabola.svg)

*Figure A.12.* Lemma A.16. The envelope $E(x) - \frac\pi6$ (orange) and the
parabola $\frac{13}{24} + \frac x{36} - \frac{x^2}{16}$ (purple, dashed) have
the same value and slope at 0 (dot), and the envelope bends down at least as
fast, so it stays below the parabola. The parabola is highest at
$x = \frac29$, where it equals $\frac{353}{648} \approx 0.5448$, below the
level $\frac\pi3 - \frac12 \approx 0.5472$ that Lemma A.17 needs
(black).

*Proof.*

1. *The value and the slope at 0.* At $x = 0$ the radicands are $1$ and
   $\frac{13}4 - 1 = \frac94 = (\frac32)^2$, and $\arcsin 0 = 0$. So

   ```math
   E(0) = \tfrac\pi6 + \tfrac1{24} + \tfrac13 \cdot \tfrac32 = \tfrac\pi6 + \tfrac{13}{24} , \qquad
   E_1(0) = 1 - \tfrac34 - \frac1{3 \cdot \frac32} = \tfrac14 - \tfrac29 = \tfrac1{36} .
   ```

2. *A parabola above the envelope.* By Lemma A.15, at every
   $y \in [0, \frac34]$ the function $-E$ has derivative $-E_1(y)$, the
   function $-E_1$ has derivative $-E_2(y)$, and $-E_2(y) \ge \frac18$.
   Lemma A.2 with $\kappa = \frac18$, applied to $-E$ at $t = 0$, gives
   $-E(x) \ge -E(0) - E_1(0)\,x + \frac{x^2}{16}$, that is, by step 1,

   ```math
   E(x) \le \tfrac\pi6 + \tfrac{13}{24} + \tfrac x{36} - \tfrac{x^2}{16} . \tag{A.2}
   ```

3. *The top of the parabola.* Since
   $\frac1{16}(x - \frac29)^2 = \frac{x^2}{16} - \frac x{36} + \frac1{324}$ and
   $\frac{13}{24} + \frac1{324} = \frac{351}{648} + \frac2{648} = \frac{353}{648}$,
   completing the square gives

   ```math
   \tfrac{13}{24} + \tfrac x{36} - \tfrac{x^2}{16} = \tfrac{353}{648} - \tfrac1{16}\left(x - \tfrac29\right)^2 \le \tfrac{353}{648} .
   ```

   With (A.2), $E(x) \le \frac\pi6 + \frac{353}{648}$. $\square$

*Lean:
[`Seven.arcEnvelope_bound`](../../SquaresInCircles/Seven/Exterior.lean#L419).*

For orientation: the largest value of $E$ on $[0, \frac34]$ is about
$\frac\pi6 + 0.54293$, taken near $x = 0.094$, and
$\frac{353}{648} \approx 0.54475$. The parabola gives away about 0.0018, and
Lemma A.17 has a little more to spare:
$\frac\pi3 - \frac12 - \frac{353}{648} \approx 0.0024$.

### Lemma A.17 (the near edge)

Let $(a, u)$ be an admissible state. Then
$\ell(a, u) + \frac12 < \arccos(a - \frac12)$.

*Proof.* Put $x = a - \frac12$. Since $\frac12 \le a < \frac54$,
$0 \le x < \frac34$.

1. *The disk bounds $u$.* We have
   $\varphi(a, u) = (x + 1)^2 + (u + \frac12)^2 \le \frac{13}4$, so
   $(u + \frac12)^2 \le \frac{13}4 - (x + 1)^2$, which is positive by
   Lemma A.15 (1). As $u + \frac12 > 0$ and the square root is increasing,
   $u + \frac12 \le \sqrt{13/4 - (x + 1)^2}$ (Figure A.6).
2. *The envelope.* By (A.1) and step 1,
   $\mathrm{side}(a, u) + \arcsin x \le E(x)$, and by Lemma A.16,
   $\mathrm{side}(a, u) + \arcsin x \le \frac\pi6 + \frac{353}{648}$.
3. As $\ell(a, u) \le \mathrm{side}(a, u)$ and
   $\arccos x = \frac\pi2 - \arcsin x$,

   ```math
   \arccos x - \ell(a, u) - \tfrac12
   \ge \tfrac\pi2 - \tfrac\pi6 - \tfrac{353}{648} - \tfrac12
   = \tfrac\pi3 - \tfrac{677}{648} > 0 ,
   ```

   because $\frac\pi3 > \frac{3.14}3 > 1.0466$ and $\frac{677}{648} < 1.0448$.
   $\square$

*Lean:
[`Seven.marker_vertical_endpoint`](../../SquaresInCircles/Seven/Exterior.lean#L437).*

*Proof of [Lemma 9.9](seven.md#lemma-99-the-marker-arc).* Let $(a, u)$ be admissible, write
$\ell = \ell(a, u)$, and let $|t - \ell| \le \frac12$, so that
$\ell - \frac12 \le t \le \ell + \frac12$. Put
$\theta = \arccos(a - \frac12)$. Since $0 \le a - \frac12 \le 1$,
$0 \le \theta \le \frac\pi2$ and $\cos\theta = a - \frac12$.

1. *$|t| < \theta$.* By Lemma A.17, $t \le \ell + \frac12 < \theta$; and as
   $\ell \ge 0$, $t \ge \ell - \frac12 \ge -\ell - \frac12 > -\theta$. In
   particular $t \in (-\frac\pi2, \frac\pi2)$.
2. *The near and the far edge.* The cosine is even and strictly decreasing on
   $[0, \pi]$, so by step 1, $\cos t = \cos|t| > \cos\theta = a - \frac12$.
   Also $\cos t \le 1 \le a + \frac12$. Hence $|\cos t - a| \le \frac12$.
3. *The lower edge.* By Lemma A.11,
   $\arcsin(u - \frac12) < \ell - \frac12 \le t$. Both
   $\arcsin(u - \frac12)$ and $t$ lie in $[-\frac\pi2, \frac\pi2]$, where the
   sine is strictly increasing, and $-1 \le u - \frac12 \le 1$, so
   $u - \frac12 = \sin\left(\arcsin(u - \frac12)\right) < \sin t$.
4. *The upper edge.* If $u > \frac12$, then $\sin t \le 1 < u + \frac12$. If
   $u \le \frac12$, Lemma A.12 gives
   $t \le \ell + \frac12 < \arcsin(u + \frac12)$; as in step 3, both
   sides lie in $[-\frac\pi2, \frac\pi2]$ and $\frac12 \le u + \frac12 \le 1$,
   so $\sin t < u + \frac12$. With step 3, $|\sin t - u| \le \frac12$.
   $\square$

*Lean: [`Seven.marker_arc`](../../SquaresInCircles/Seven/Exterior.lean#L486).*
