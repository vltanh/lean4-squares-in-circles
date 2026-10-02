# Appendix D. Six squares: the wings

[Contents](README.md) · [← Appendix C](appendix-c.md) · [Appendix E →](appendix-e.md)

This appendix proves [Proposition 9.46](09-six.md#proposition-946-no-missing-wing)
of Chapter 9: in a normalized packing
([Definition 9.34](09-six.md#definition-934-normalized-packing)) neither wing is
missing ([Definition 9.44](09-six.md#definition-944-wings)). In the model the
turned square $D$ sits in the corner between $W$ and $S$, with its top vertex on
the lower side of $W$ and its right vertex on the left side of $S$: $W$ and $D$
are separated along the secondary axis $e^W_2$ of $W$, and $D$ and $S$ along the
secondary axis $e^S_2$ of $S$. These are the two wings (Figure D.2). The west
wing is *missing* if $W$ and $D$ are separated along $e^D_2$ while $D$ and $S$
are separated along $e^S_2$; the south wing is missing if $D$ and $S$ are
separated along $e^D_2$ while $W$ and $D$ are separated along $e^W_2$. In a
missing wing the line of a side of $D$, not of a side of its neighbour,
separates the two squares, and this costs room. We show that it costs more room
than the disk of squared radius $Q_0$ has.

§D.1 writes the separations of $W$, $D$, $S$ and the central square $C$ as
inequalities between the coordinates of the squares, collects the facts of
Chapter 9 that we use, and introduces the reflection in the diagonal, which
turns a missing west wing into a missing south wing. §D.2 bounds the curvature
of the *chord term*, which the force on $D$ leaves in a missing south wing. §D.3
shows that a missing west wing needs a phase gap of more than one radian between
$W$ and $D$, and §D.4 narrows the angles of a missing west wing with $W$ on its
own axis. §D.5 to §D.9 treat the cases, by the separators of $W$ and $S$ from
$C$, and §D.10 assembles them.

Every case is a stress ([Definition 9.23](09-six.md#definition-923-stress)). We add
the separating inequalities of the case with weights. Read as forces
([Lemma 9.24](09-six.md#lemma-924-balance)), the sum of their left sides is the
work of the forces on the centres of the squares, and the supports of
[Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk) and
[Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) bound each work. What is
left, the threshold sum less the bounds of the works, is a function of two or
three angles, the *profile* of the case, and the separations make it
nonpositive. We show that it is positive on the domain of the angles. In each
angle it is concave, or a constant plus a first harmonic with nonnegative
coefficients, so by [Lemma A.10](appendix-a.md#lemma-a10-concave-functions) and
[Lemma A.11](appendix-a.md#lemma-a11-first-harmonics) it is positive once it is
positive at the corners of the domain, and there Taylor polynomials give its
sign.

**Notation.** We use the notation of Chapter 9: $h = \frac{\sqrt2}2$, the
ceiling $Q_0 = 2.85118$ with $R_0 = \sqrt{Q_0}$, $\rho_0$ and $c_0$, and the
decimals $\bar R = 1.6886$, $\bar\rho = 1.11282$ and $\bar c = 0.11282$
([Definition 9.4](09-six.md#definition-94-the-ceiling)), which bound them:
$R_0 < \bar R$, $1.11281 < \rho_0 < \bar\rho$ and $c_0 < \bar c$
([Lemma 9.5](09-six.md#lemma-95-the-ceiling)). The squares $Q_t(a, b)$, the charts
in the ceiling, the widths
$\omega(\delta) = \frac12(\lvert\cos\delta\rvert + \lvert\sin\delta\rvert)$ and
the thresholds $\tau(\delta) = \frac12 + \omega(\delta)$ are those of
[Definition 9.9](09-six.md#definition-99-squares-in-a-frame), and
$\varphi(a, b) = (a + \frac12)^2 + (b + \frac12)^2$. Two decimals recur:

```math
\mu_- = \tfrac12 - \bar c = 0.38718, \qquad \mu_+ = \tfrac12 + \bar c = \bar\rho - \tfrac12 = 0.61282 .
```

For the Taylor bounds we write

```math
C_4(x) = 1 - \tfrac{x^2}2 + \tfrac{x^4}{24}, \quad C_6(x) = C_4(x) - \tfrac{x^6}{720}, \quad S_5(x) = x - \tfrac{x^3}6 + \tfrac{x^5}{120}, \quad S_7(x) = S_5(x) - \tfrac{x^7}{5040} .
```

By [Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds),
$C_6(x) \le \cos x \le C_4(x)$ for every real $x$, and
$S_7(x) \le \sin x \le S_5(x)$ for $x \ge 0$; as the polynomials $S_5$ and $S_7$
are odd, $S_5(x) \le \sin x \le S_7(x)$ for $x \le 0$. We also use the
elementary bounds $\cos x \ge 1 - \frac{x^2}2$, $\sin x \le x$ and
$\sin x \ge x - \frac{x^3}6$ for $x \ge 0$, the bracket
$3.141592 < \pi < 3.141593$, and the monotonicity of a function with a
derivative of constant sign
([Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative)). A *first
harmonic* is a function $A\cos x + B\sin x$ (Lemma A.11).

## D.1 The wings in coordinates

We read $W$, $D$ and $S$ at the phases $\pi - v$, $\pi + d$ and
$\frac{3\pi}2 + s$, so that $v = -w$ and $s$ are the angles by which $W$ and
$S$ turn away from $D$, and we write

```math
q = d + v, \qquad r = d - s
```

for the two gaps: the phase of $D$ exceeds that of $W$ by $q$ and falls short of
that of $S$ by $\frac\pi2 - r$ (Figure D.1). In the model $v = s = 0$ and
$d = \frac\pi4$, so $q = r = \frac\pi4$.

![Two panels. Left: the central square C at the disk centre o and the squares W, D and S in the lower left part of the disk, each with the two axes of its frame drawn as short arrows from its centre and labelled e1 and e2 with the name of the square. Right: from a point o, the primary axes of W, D and S as arrows in their colours, and dashed the directions of phase pi and 3 pi/2; arcs mark the angle v from the first dashed direction up to the axis of W, the angle d from it down to the axis of D, the angle s from the second dashed direction to the axis of S, the gap q from W to D, and the angle pi/2 - r from D to S](figures/appendix-d/angles.svg)

*Figure D.1.* The angles and the frames of wing data, at $v = 0.3$, $s = 0.25$
and $d = 0.65$, with $W$ and $D$ separated along $e^W_2$ and $D$ and $S$ along
$e^S_2$, in the smallest disk that allows these and the separations of $W$ and
$S$ from $C$ along their own axes (radius $1.709$, pink; the circle of radius
$R_0$ is dashed). (a) The frames: $e^X_1 = u(t_X)$ points away from $o$, and
$e^X_2$ is a quarter turn further. (b) The phases: $W$ and $S$ are turned by
$v$ and $s$ away from $D$, whose phase is $\pi + d$; the gaps are $q = d + v$
and $\frac\pi2 - r = \frac\pi2 - d + s$.

### Definition D.1 (wing data)

*Wing data* are real numbers $v$, $s$, $d$, $a_W$, $b_W$, $a_D$, $b_D$, $a_S$,
$b_S$, $c_x$, $c_y$ such that each of the pairs $(a_W, b_W)$, $(a_D, b_D)$ and
$(a_S, b_S)$ satisfies the conditions $\frac12 \le a$, $\lvert b\rvert \le a$,
$\varphi(a, \lvert b\rvert) \le Q_0$ of a chart in the ceiling,
$0 \le c_x, c_y \le c_0$, and

```math
a_D + c_x\cos d + c_y\sin d \ge \tfrac12 + \omega(d) . \tag{D.1}
```

We call $v$, $s$, $d$ the *angles*. The *separating inequalities* of wing data
are (D.1) and

```math
\begin{aligned}
a_W + c_x\cos v - c_y\sin v &\ge \tfrac12 + \omega(v) , & \text{(D.2)} \\
a_W\cos v + b_W\sin v + c_x &\ge \tfrac12 + \omega(v) , & \text{(D.3)} \\
a_S - c_x\sin s + c_y\cos s &\ge \tfrac12 + \omega(s) , & \text{(D.4)} \\
a_S\cos s - b_S\sin s + c_y &\ge \tfrac12 + \omega(s) , & \text{(D.5)} \\
a_D\sin q + b_D\cos q - b_W &\ge \tfrac12 + \omega(q) , & \text{(D.6)} \\
a_W\sin q - b_W\cos q + b_D &\ge \tfrac12 + \omega(q) , & \text{(D.7)} \\
b_S + a_D\cos r - b_D\sin r &\ge \tfrac12 + \omega(r) , & \text{(D.8)} \\
a_S\cos r + b_S\sin r - b_D &\ge \tfrac12 + \omega(r) . & \text{(D.9)}
\end{aligned}
```

The wing data have a *missing west wing* if (D.7) and (D.8) hold, and a *missing
south wing* if (D.6) and (D.9) hold.

*Lean: [`Six.Wings.Chart`](../../SquaresInCircles/Six/Wings/Chart.lean#L27),
[`Six.Wings.Chart.WestOwn`](../../SquaresInCircles/Six/Wings/Chart.lean#L49),
[`Six.Wings.Chart.WestSide`](../../SquaresInCircles/Six/Wings/Chart.lean#L52),
[`Six.Wings.Chart.SouthOwn`](../../SquaresInCircles/Six/Wings/Chart.lean#L55),
[`Six.Wings.Chart.SouthSide`](../../SquaresInCircles/Six/Wings/Chart.lean#L58),
[`Six.Wings.Chart.WestWing`](../../SquaresInCircles/Six/Wings/Chart.lean#L61),
[`Six.Wings.Chart.WestDiagonal`](../../SquaresInCircles/Six/Wings/Chart.lean#L65),
[`Six.Wings.Chart.SouthWing`](../../SquaresInCircles/Six/Wings/Chart.lean#L69),
[`Six.Wings.Chart.SouthDiagonal`](../../SquaresInCircles/Six/Wings/Chart.lean#L73),
[`Six.Wings.Chart.MissingSouth`](../../SquaresInCircles/Six/Wings/Chart.lean#L78),
[`Six.Wings.Chart.MissingWest`](../../SquaresInCircles/Six/Wings/Chart.lean#L84).*

The numbers describe four squares: $C = Q(c)$ with $c = (c_x, c_y)$, and

```math
W = Q_{\pi - v}(a_W, b_W), \qquad D = Q_{\pi + d}(a_D, b_D), \qquad S = Q_{3\pi/2 + s}(a_S, b_S) .
```

Lemma D.2 shows that (D.1) separates $D$ from $C$ along its own axis, (D.2) and
(D.3) separate $W$ from $C$ along its own axis and along the west side of $C$,
(D.4) and (D.5) separate $S$ from $C$ along its own axis and along the south
side of $C$, (D.6) and (D.7) separate $W$ and $D$ along $e^W_2$ and along
$e^D_2$, and (D.8) and (D.9) separate $D$ and $S$ along $e^S_2$ and along
$e^D_2$.

### Lemma D.2 (the wing data of a normalized packing)

In a normalized packing put $v = -w$. The angles $v$, $s$, $d$, the coordinates
$(a_X, b_X)$ of $X = W, D, S$ in their charts
([Proposition 9.22](09-six.md#proposition-922-labels)) and the centre
$c = (c_x, c_y)$ of $C$ are wing data, and:

1. if $W$ is separated from $C$ along its own axis, then (D.2) holds, and if
   along the west side of $C$, then (D.3); if $S$ is separated from $C$ along
   its own axis, then (D.4), and if along the south side of $C$, then (D.5);
2. if $W$ and $D$ are separated along $e^W_2$, then (D.6) holds, and if along
   $e^D_2$, then (D.7); if $D$ and $S$ are separated along $e^S_2$, then (D.8),
   and if along $e^D_2$, then (D.9); so a missing west or south wing of the
   packing is a missing west or south wing of the wing data;
3. $\frac12 < d \le \frac\pi4$, $v < \frac23$ and $s < \frac23$;
4. if $W$ is on its own axis, then $v > 0$, and if it is on its matching side,
   then $\lvert v\rvert < \frac25$; if $S$ is on its own axis, then $s > 0$, and
   if it is on its matching side, then $\lvert s\rvert < \frac25$;
5. if $W$ and $S$ are both on their own axes, then $v + s < \frac{24}{25}$;
6. if the west wing is missing, then $v > \frac\pi4 - d$, and if the south wing
   is missing, then $r < \frac\pi4$.

*Proof.* The phases are $t_W = \pi - v$, $t_D = \pi + d$ and
$t_S = \frac{3\pi}2 + s$, so

```math
u(t_W) = (-\cos v, \sin v), \qquad u(t_D) = -(\cos d, \sin d), \qquad u(t_S) = (\sin s, -\cos s),
```

and $\tau(t_W) = \frac12 + \omega(v)$, $\tau(t_D) = \frac12 + \omega(d)$,
$\tau(t_S) = \frac12 + \omega(s)$, since $\omega$ does not change when its
argument is replaced by $-t$, $\pi + t$ or $\frac\pi2 + t$
([Lemma A.15](appendix-a.md#lemma-a15-small-angles) (2)). The charts are in the
ceiling and $c \in [0, c_0]^2$ (Definition 9.34).

The margins of
[Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square)
are, with $x_t(a, b) = a\cos t - b\sin t$ and $y_t(a, b) = a\sin t + b\cos t$:
for $D$, $m_{\mathrm{own}} = a_D + c_x\cos d + c_y\sin d - \tau(t_D)$; for $W$,
$m_{\mathrm{own}} = a_W + c_x\cos v - c_y\sin v - \tau(t_W)$ and
$m_{\mathrm{west}} = c_x - x_{t_W}(a_W, b_W) - \tau(t_W)$ with
$x_{t_W}(a_W, b_W) = -a_W\cos v - b_W\sin v$; for $S$,
$m_{\mathrm{own}} = a_S - c_x\sin s + c_y\cos s - \tau(t_S)$ and
$m_{\mathrm{south}} = c_y - y_{t_S}(a_S, b_S) - \tau(t_S)$ with
$y_{t_S}(a_S, b_S) = -a_S\cos s + b_S\sin s$. As $D$ is separated from $C$ along
its own axis ([Proposition 9.35](09-six.md#proposition-935-normalization) (2)),
(D.1) holds, and (1) follows.

(2) By [Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares) for $U = W$
and $V = D$, with $\delta = t_D - t_W = q$,
$\langle e^W_2, c_D - c_W\rangle = a_D\sin q + b_D\cos q - b_W$ and
$\langle e^D_2, c_D - c_W\rangle = b_D + a_W\sin q - b_W\cos q$, and the
threshold is $\tau(q)$. For $U = D$ and $V = S$,
$\delta = t_S - t_D = \frac\pi2 - r$, so $\sin\delta = \cos r$,
$\cos\delta = \sin r$ and $\tau(\delta) = \frac12 + \omega(r)$ (Lemma A.15 (2));
and $\langle e^D_2, c_S - c_D\rangle = a_S\cos r + b_S\sin r - b_D$,
$\langle e^S_2, c_S - c_D\rangle = b_S + a_D\cos r - b_D\sin r$.

(3) $d > \frac12$ is [Proposition 9.39](09-six.md#proposition-939-the-angle-of-d),
$d \le \frac\pi4$ is $t_D \le \frac{5\pi}4$, and the windows of Proposition 9.35
(1) give $w > -\frac23$ and $s < \frac23$.

(4) $w < 0$ for $W$ on its own axis is
[Lemma 9.38](09-six.md#lemma-938-w-on-its-own-axis-turns-away-from-d), $s > 0$ for
$S$ on its own axis is [Lemma 9.43](09-six.md#lemma-943-signs-of-the-own-wings)
(1), and the bounds on the matching sides are Proposition 9.35 (3).

(5) is Lemma 9.43 (2), $s - w < \frac{24}{25}$.

(6) In a missing west wing $W$ and $D$ are separated along $e^D_2$, so
$w < d - \frac\pi4$, and in a missing south wing $D$ and $S$ are separated along
$e^D_2$, so $s > d - \frac\pi4$ ([Lemma 9.42](09-six.md#lemma-942-walls) (1)).
$\square$

*Lean: [`Six.Wings.chart`](../../SquaresInCircles/Six/Wings/Chart.lean#L147),
[`Six.Wings.west_phase`](../../SquaresInCircles/Six/Wings/Chart.lean#L172),
[`Six.Wings.diagonal_phase`](../../SquaresInCircles/Six/Wings/Chart.lean#L177),
[`Six.Wings.south_phase`](../../SquaresInCircles/Six/Wings/Chart.lean#L181),
[`Six.Wings.west_own`](../../SquaresInCircles/Six/Wings/Chart.lean#L185),
[`Six.Wings.west_side`](../../SquaresInCircles/Six/Wings/Chart.lean#L194),
[`Six.Wings.south_own`](../../SquaresInCircles/Six/Wings/Chart.lean#L204),
[`Six.Wings.south_side`](../../SquaresInCircles/Six/Wings/Chart.lean#L213),
[`Six.Wings.west_wing`](../../SquaresInCircles/Six/Wings/Chart.lean#L224),
[`Six.Wings.west_diagonal`](../../SquaresInCircles/Six/Wings/Chart.lean#L234),
[`Six.Wings.south_wing`](../../SquaresInCircles/Six/Wings/Chart.lean#L246),
[`Six.Wings.south_diagonal`](../../SquaresInCircles/Six/Wings/Chart.lean#L259),
[`Six.Wings.missing_south`](../../SquaresInCircles/Six/Wings/Chart.lean#L270),
[`Six.Wings.missing_west`](../../SquaresInCircles/Six/Wings/Chart.lean#L273),
[`Six.Wings.diagonal_range`](../../SquaresInCircles/Six/Wings/Chart.lean#L278),
[`Six.Wings.west_upper`](../../SquaresInCircles/Six/Wings/Chart.lean#L281),
[`Six.Wings.south_upper`](../../SquaresInCircles/Six/Wings/Chart.lean#L286),
[`Six.Wings.west_own_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L288),
[`Six.Wings.south_own_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L293),
[`Six.Wings.west_side_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L296),
[`Six.Wings.south_side_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L301),
[`Six.Wings.own_angle_sum`](../../SquaresInCircles/Six/Wings/Chart.lean#L305).*

![Three panels, each with the central square C at the disk centre o and the squares W, D and S in the lower left part of the disk. In the first, the model, the turned square D touches the lower side of W with its top vertex and the left side of S with its right vertex, and these two sides are drawn as thick blue and green lines, labelled (D.6) and (D.8). In the second, S is turned and separated from D by the line of the lower right side of D, drawn in purple and labelled (D.9), and the squares cross the dashed circle of radius R0. The third is the mirror image of the second in the diagonal, with the lines (D.7) and (D.8)](figures/appendix-d/wings.svg)

*Figure D.2.* The wings. (a) The model (Theorem 9.1), without $E$ and $N$: the
top vertex of $D$ lies on the lower side of $W$, along which (D.6) separates $W$
and $D$, and its right vertex on the left side of $S$, along which (D.8)
separates $D$ and $S$; the dashed circle has the radius $R_6$. (b) A missing
south wing, at $v = 0$, $s = 0.32$ and $d = \frac\pi4$, with $W$ and $S$ on the
sides of $C$: $D$ and $S$ are separated along $e^D_2$, (D.9). For fixed angles
the separating inequalities and the conditions of wing data are convex in the
coordinates; the squares are placed in the smallest disk about $o$ that allows
them, found numerically, of radius $1.722$ (pink), and they cross the circle of
radius $R_0$ (dashed). (c) The reflection of (b) in the diagonal (Lemma D.3), a
missing west wing.

**Stresses in coordinates.** Each separating inequality has the form
$\langle n, c_V - c_U\rangle \ge \tau$, an edge from $U$ to $V$ with normal $n$
([Definition 9.23](09-six.md#definition-923-stress)). With a weight $\lambda \ge 0$
it puts the force $\lambda n$ on $V$ and $-\lambda n$ on $U$. For an exterior
square $T$ we write a force $F$ in the frame of $T$, as
$(U, V) = (\langle F, e^T_1\rangle, \langle F, e^T_2\rangle)$; its work on the
centre $c_T = a_Te^T_1 + b_Te^T_2$ is $Ua_T + Vb_T$. For $C$ we write the force
as $(X, Y)$ in the standard frame; its work is $Xc_x + Yc_y$. Table D.1 lists
the forces of the separating inequalities, and Figure D.3 draws them. In each
row $\lambda$ times the left side of the inequality is the sum of the works of
its two forces, as one checks term by term; this is the balance of
[Lemma 9.24](09-six.md#lemma-924-balance) in coordinates.

| inequality | separation | forces on $W$, $D$, $S$ (in their frames) | force on $C$ |
| :-: | --- | --- | --- |
| (D.1) | $C$, $D$ along $e^D_1$ | $D$: $(\lambda, 0)$ | $\lambda(\cos d, \sin d)$ |
| (D.2) | $C$, $W$ along $e^W_1$ | $W$: $(\lambda, 0)$ | $\lambda(\cos v, -\sin v)$ |
| (D.3) | $C$, $W$ along $(-1, 0)$ | $W$: $\lambda(\cos v, \sin v)$ | $(\lambda, 0)$ |
| (D.4) | $C$, $S$ along $e^S_1$ | $S$: $(\lambda, 0)$ | $\lambda(-\sin s, \cos s)$ |
| (D.5) | $C$, $S$ along $(0, -1)$ | $S$: $\lambda(\cos s, -\sin s)$ | $(0, \lambda)$ |
| (D.6) | $W$, $D$ along $e^W_2$ | $W$: $(0, -\lambda)$; $D$: $\lambda(\sin q, \cos q)$ | |
| (D.7) | $W$, $D$ along $e^D_2$ | $W$: $\lambda(\sin q, -\cos q)$; $D$: $(0, \lambda)$ | |
| (D.8) | $D$, $S$ along $e^S_2$ | $D$: $\lambda(\cos r, -\sin r)$; $S$: $(0, \lambda)$ | |
| (D.9) | $D$, $S$ along $e^D_2$ | $D$: $(0, -\lambda)$; $S$: $\lambda(\cos r, \sin r)$ | |

*Table D.1.* The forces of the separating inequalities with the weight
$\lambda$.

![Four panels, for the squares C, W, D and S. Each shows the axes of the frame of its square dashed, the first pointing right and the second up, the unit circle, and an arrow for the unit force that each separating inequality puts on the square, labelled (D.1) to (D.9) and coloured by the other square of the separation: blue for W, purple for D, green for S and black for C](figures/appendix-d/forces.svg)

*Figure D.3.* The forces of Table D.1 for $\lambda = 1$, at $v = 0.3$,
$s = 0.25$ and $d = 0.65$, so that $q = 0.95$ and $r = 0.4$: on each square
the unit force of each separating inequality in which it takes part, in the
frame of $W$, $D$ or $S$ and in the standard frame for $C$, coloured by the
other square of the pair. A stress adds these arrows with its weights.

So a weighted sum of separating inequalities reads

```math
\sum_e \lambda_e\left(\tfrac12 + \omega_e\right) \le \sum_{T = W, D, S}\left(U_Ta_T + V_Tb_T\right) + X_Cc_x + Y_Cc_y ,
```

with the total forces $(U_T, V_T)$ and $(X_C, Y_C)$, where $\omega_e$ is the
width in the threshold of the edge $e$. The works are bounded by the following
supports, for an exterior square with the force $(U, V)$ and a pair $(a, b)$ as
in Definition D.1.

- (V) *The far vertex*
  ([Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk) (1) with
  $R = R_0$):
  $Ua + Vb \le R_0\sqrt{U^2 + V^2} - \frac12(\lvert U\rvert + \lvert V\rvert)$,
  and so $Ua + Vb \le \bar R\ell - \frac12(\lvert U\rvert + \lvert V\rvert)$
  whenever $\sqrt{U^2 + V^2} \le \ell$.
- (K) *The cones* ([Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) (2)):
  $Ua + Vb \le \bar\rho U$ if $\lvert V\rvert \le \frac{31}{100}U$;
  $Ua + Vb \le \bar\rho U + \frac1{12}V^2$ if $U \ge \frac75$ and
  $\lvert V\rvert \le \frac12U$; $Ua + Vb \le \bar\rho U + \frac3{25}V^2$ if
  $U \ge \frac{33}{20}$ and $\lvert V\rvert \le \frac35U$.
- (Ch) *The chord* (Lemma 9.26 (3)): for $z \ge 0$ and $0 \le q \le \pi$,

  ```math
  (z + \sin q)a + (\cos q - 1)b \le \bar R\left(\left(2 + \tfrac{z^2}4\right)\sin\tfrac q2 + z\cos\tfrac q2\right) - \tfrac12(z + \sin q + 1 - \cos q) .
  ```

- (B) *The box* (Lemma 9.26 (4)): $Xc_x + Yc_y \le \bar c(X + Y)$ if
  $X, Y \ge 0$, and $Xc_x + Yc_y \le \bar cX + yY$ for $y = 0$ or $y = \bar c$
  if $X \ge 0$.

For the thresholds, $\omega(x) \ge \frac12(\cos x + \sin x)$ for every $x$, with
equality for $0 \le x \le \frac\pi2$, and
$\omega(x) = \frac12(\cos x + \lvert\sin x\rvert)$ when $\cos x \ge 0$ (Lemma
A.15 (2)).

### Lemma D.3 (the reflection)

The reflection of wing data, the numbers

```math
\begin{gathered}
v' = s, \quad s' = v, \quad d' = \tfrac\pi2 - d, \quad (c'_x, c'_y) = (c_y, c_x), \\
(a'_W, b'_W) = (a_S, -b_S), \quad (a'_D, b'_D) = (a_D, -b_D), \quad (a'_S, b'_S) = (a_W, -b_W),
\end{gathered}
```

are wing data. If the wing data satisfy (D.4), (D.2) or (D.3), the reflection
satisfies (D.2), (D.4) or (D.5), in this order; and if the wing data have a
missing west wing, the reflection has a missing south wing. The gaps of the
reflection are $q' = \frac\pi2 - r$ and $r' = \frac\pi2 - q$.

*Proof.* The conditions on the pairs involve $\lvert b\rvert$ only, and the box
is symmetric. As $\omega(\frac\pi2 - x) = \omega(x)$ (Lemma A.15 (2)),
$\cos(\frac\pi2 - x) = \sin x$ and $\sin(\frac\pi2 - x) = \cos x$, each
inequality of the reflection is one of the given wing data: (D.1) for the
reflection is $a_D + c_y\sin d + c_x\cos d \ge \frac12 + \omega(d)$, which is
(D.1); (D.2) for the reflection is
$a_S + c_y\cos s - c_x\sin s \ge \frac12 + \omega(s)$, which is (D.4); (D.4) for
the reflection is $a_W - c_y\sin v + c_x\cos v \ge \frac12 + \omega(v)$, which
is (D.2); and (D.5) for the reflection is
$a_W\cos v + b_W\sin v + c_x \ge \frac12 + \omega(v)$, which is (D.3). The gaps
are $q' = \frac\pi2 - d + s = \frac\pi2 - r$ and
$r' = \frac\pi2 - d - v = \frac\pi2 - q$. So (D.6) for the reflection is
$a_D\cos r - b_D\sin r + b_S \ge \frac12 + \omega(r)$, which is (D.8), and (D.9)
for the reflection is $a_W\sin q - b_W\cos q + b_D \ge \frac12 + \omega(q)$,
which is (D.7). $\square$

*Lean:
[`Six.Wings.Chart.reflect`](../../SquaresInCircles/Six/Wings/Chart.lean#L90),
[`Six.Wings.Chart.SouthOwn.reflect`](../../SquaresInCircles/Six/Wings/Chart.lean#L112),
[`Six.Wings.Chart.WestOwn.reflect`](../../SquaresInCircles/Six/Wings/Chart.lean#L116),
[`Six.Wings.Chart.WestSide.reflect`](../../SquaresInCircles/Six/Wings/Chart.lean#L120),
[`Six.Wings.Chart.MissingWest.reflect`](../../SquaresInCircles/Six/Wings/Chart.lean#L125).*

Geometrically, the reflection is the reflection in the diagonal
([Lemma 9.29](09-six.md#lemma-929-the-reflection-in-the-diagonal)): it exchanges
$W$ and $S$ and maps the angle $d$ of $D$ to $\frac\pi2 - d$ (Figure D.2 (b)
and (c)). The reflection of a normalized packing has
$\frac\pi4 \le d' < \frac\pi2 - \frac12$, outside the range of a normalized
packing; this is why the cases below are stated for wing data with explicit
ranges of the angles.

## D.2 The chord term

Let $D$ be separated from $W$ along $e^W_2$ and from $S$ along $e^D_2$, as in a
missing south wing, with the weight $1$ on both separations, and from $C$ along
its own axis with a weight $z \ge 0$. By Table D.1 the force on $D$ is
$(z + \sin q, \cos q - 1)$ (Figure D.4), and the chord (Ch) bounds its work.
The threshold $\frac12 + \omega(q)$ of (D.6), which is at least
$\frac12 + \frac12(\cos q + \sin q)$, less this bound is at least

```math
\tfrac12 + \tfrac12(\cos q + \sin q) - \bar R\left(\left(2 + \tfrac{z^2}4\right)\sin\tfrac q2 + z\cos\tfrac q2\right) + \tfrac12(z + \sin q + 1 - \cos q) = 1 + \tfrac z2 + H_{L, M}(q) ,
```

where $L = \bar R(2 + \frac{z^2}4)$, $M = \bar Rz$, and

```math
H_{L, M}(q) = \sin q - L\sin\tfrac q2 - M\cos\tfrac q2
```

is the *chord term*. Its derivatives are
$H'_{L, M}(q) = \cos q - \frac L2\cos\frac q2 + \frac M2\sin\frac q2$ and

```math
H''_{L, M}(q) = -\sin q + \tfrac L4\sin\tfrac q2 + \tfrac M4\cos\tfrac q2 .
```

![In the frame of D, for q = 1 and z = 9/20: a blue unit arrow of (D.6) from the centre of D at the angle q from the second axis, a purple unit arrow of (D.9) straight down from its tip, a short black arrow of (D.1) to the right, and the orange total force F from the centre; a dashed chord of the unit circle joins the top of the circle to the tip of the blue arrow](figures/appendix-d/chord.svg)

*Figure D.4.* The force on $D$ in its frame, for $q = 1$ and $z = \frac9{20}$.
The unit force $(\sin q, \cos q)$ of (D.6) and the force $(0, -1)$ of (D.9)
add up to the chord of the unit circle from $(0, 1)$ to $(\sin q, \cos q)$, of
length $2\sin\frac q2$, and with $(z, 0)$ of (D.1) they give
$F = (z + \sin q, \cos q - 1)$.

The weights $z$ used below are at most $\frac9{20}$, and we put

```math
L_* = \bar R\left(2 + \tfrac{(9/20)^2}4\right) = 3.462685375, \qquad M_* = \tfrac9{20}\bar R = 0.75987 .
```

### Lemma D.4 (the chord term)

Let $L \le L_*$ and $M \le M_*$.

1. $H''_{L, M}(q) \le \frac3{40} - \frac3{10}\min(q, 1)$ for
   $\frac12 \le q \le \frac32$.
2. $H''_{L, M}(q) \le -\frac{19}{100}$ for $\frac{157}{200} \le q \le \frac53$.
3. $H''_{L, M}(q) < 0$ for $\frac12 \le q \le \frac53$. So $H_{L, M}$ is concave
   on $[\frac12, \frac53]$, and $H'_{L, M}$ is nonincreasing there.

*Proof.* For $0 \le q \le \frac53 < \pi$ both $\sin\frac q2$ and $\cos\frac q2$
are nonnegative, so $H''_{L, M}(q) \le G(q)$ with $G = H''_{L_*, M_*}$.

Let $a$, $c$ be real numbers and $[l, u] \subseteq [\frac12, \frac53]$. The
function $g(q) = a + cq - G(q) = a + cq + H_{L_*/4, M_*/4}(q)$ has the second
derivative

```math
g''(q) = H''_{L_*/4, M_*/4}(q) = -\sin q + \tfrac{L_*}{16}\sin\tfrac q2 + \tfrac{M_*}{16}\cos\tfrac q2 \le -\tfrac{29}{54}q + \tfrac{L_*}{32}q + \tfrac{M_*}{16} ,
```

since $\sin q \ge q - \frac{q^3}6 \ge q(1 - \frac{25}{54}) = \frac{29}{54}q$ for
$0 \le q \le \frac53$, $\sin\frac q2 \le \frac q2$ and $\cos\frac q2 \le 1$. As
$\frac{29}{54} - \frac{L_*}{32} = 0.42882\ldots$, for $q \ge \frac12$ the right
side is at most $-0.2144 + 0.0475 < 0$. So $g$ is concave on $[l, u]$
([Lemma A.10](appendix-a.md#lemma-a10-concave-functions) (1)), and $g > 0$ on
$[l, u]$ once $g(l) > 0$ and $g(u) > 0$ (Lemma A.10 (2)).

At a point $q_0 \ge 0$, Lemma A.7 gives

```math
G(q_0) \le -S_7(q_0) + \tfrac{L_*}4S_5\left(\tfrac{q_0}2\right) + \tfrac{M_*}4C_4\left(\tfrac{q_0}2\right) ,
```

and Table D.2 lists these bounds (Figure D.5).

| $q_0$ | $\frac12$ | $1$ | $\frac32$ | $\frac{157}{200}$ | $\frac53$ |
| --- | :-: | :-: | :-: | :-: | :-: |
| bound of $G(q_0)$ | $-0.08119$ | $-0.25972$ | $-0.26824$ | $-0.20018$ | $-0.22652$ |

*Table D.2.* Upper bounds of $G = H''_{L_*, M_*}$ by Taylor polynomials, rounded
towards zero.

(1) On $[\frac12, 1]$ take $a + cq = \frac3{40} - \frac3{10}q$, whose values at
the ends are $-\frac3{40} = -0.075$ and $-\frac9{40} = -0.225$; on
$[1, \frac32]$ take $a + cq = -\frac9{40}$. In both cases Table D.2 gives
$g > 0$ at the ends, hence $G(q) < \frac3{40} - \frac3{10}\min(q, 1)$ on
$[\frac12, \frac32]$. (2) On $[\frac{157}{200}, \frac53]$ take
$a + cq = -\frac{19}{100}$. (3) By (1),
$H''_{L, M}(q) \le \frac3{40} - \frac3{10}q \le -\frac3{40}$ on $[\frac12, 1]$,
and by (2) $H''_{L, M}(q) \le -\frac{19}{100}$ on $[1, \frac53]$; concavity is
Lemma A.10 (1), and $H'_{L, M}$ is nonincreasing by Lemma A.1. $\square$

*Lean: [`Six.Wings.chord`](../../SquaresInCircles/Six/Wings/Chord.lean#L24),
[`Six.Wings.chordFirst`](../../SquaresInCircles/Six/Wings/Chord.lean#L25),
[`Six.Wings.chordSecond`](../../SquaresInCircles/Six/Wings/Chord.lean#L33),
[`Six.Wings.chordSin`](../../SquaresInCircles/Six/Wings/Chord.lean#L29),
[`Six.Wings.chordCos`](../../SquaresInCircles/Six/Wings/Chord.lean#L30),
[`Six.Wings.chord_hasDerivAt`](../../SquaresInCircles/Six/Wings/Chord.lean#L35),
[`Six.Wings.chordFirst_hasDerivAt`](../../SquaresInCircles/Six/Wings/Chord.lean#L40),
[`Six.Wings.second_le_top`](../../SquaresInCircles/Six/Wings/Chord.lean#L48),
[`Six.Wings.top_concave`](../../SquaresInCircles/Six/Wings/Chord.lean#L60),
[`Six.Wings.top_endpoint`](../../SquaresInCircles/Six/Wings/Chord.lean#L80),
[`Six.Wings.chord_second_envelope`](../../SquaresInCircles/Six/Wings/Chord.lean#L93),
[`Six.Wings.chord_second_high`](../../SquaresInCircles/Six/Wings/Chord.lean#L113),
[`Six.Wings.chord_second_nonpositive`](../../SquaresInCircles/Six/Wings/Chord.lean#L122).*

![The second derivative of the chord term on q from 1/2 to 5/3: a purple curve for the largest weights, z = 9/20, and a blue one below it for z = 3/8, both below a dashed orange broken line and, from 157/200 on, below a dashed green horizontal line, with five black dots on or just above the purple curve](figures/appendix-d/curvature.svg)

*Figure D.5.* Lemma D.4: $H''_{L_*, M_*}$ (purple, $z = \frac9{20}$) and
$H''_{L, M}$ for $z = \frac38$ (blue) on $[\frac12, \frac53]$, below the
envelope $\frac3{40} - \frac3{10}\min(q, 1)$ (orange) and the level
$-\frac{19}{100}$ (green); the dots are the Taylor bounds of Table D.2.

## D.3 The gap of W and D

### Lemma D.5 (a gap of one radian)

In a normalized packing, if $W$ and $D$ are separated along $e^D_2$, then
$t_D - t_W > 1$, that is, $q = d + v > 1$.

*Proof.* By the wall of [Lemma 9.42](09-six.md#lemma-942-walls) (1),
$w < d - \frac\pi4 \le 0$, so $v > 0$; the phases increase in the order $W$, $D$
([Proposition 9.35](09-six.md#proposition-935-normalization) (1)), so $q > 0$; and
$d > \frac12$ ([Proposition 9.39](09-six.md#proposition-939-the-angle-of-d)).
Suppose that $q \le 1$. Then $v < \frac12$, and on $[0, 1]$, by
[Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets),

```math
\cos q \ge C_6(1) = \tfrac{389}{720}, \qquad 0 \le \sin q \le S_5(1) = \tfrac{101}{120} .
```

Put $x = -b_W$. We collect three bounds.

- The far corner of $W$ ([Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling)
  (1)): $a_W + \frac{31}{100}(x + x^2) \le \rho_0$, as
  $\lvert b_W\rvert + b_W^2 \ge x + x^2$.
- The profile of $D$ ([Lemma 9.40](09-six.md#lemma-940-transverse-profiles) (1)):
  $b_D < \frac{31}{100} - \frac{17}{100}d$.
- The profile of $W$: $x < U(v)$ for an affine function $U(v) = U_0 - kv$. If
  $W$ is on its matching side, then $\lvert w\rvert < \frac25$ (Proposition 9.35
  (3)), so $0 \le v \le \frac25$, and Lemma 9.40 (2) gives
  $x < \frac{47}{100} - \frac23v$. If $W$ is on its own axis, then
  $0 \le v \le \frac12$, and Lemma 9.40 (3) gives
  $x \le \lvert b_W\rvert < \frac{233}{500} - \frac{73}{100}v$. In both cases
  $0 \le U(v) \le \frac{47}{100}$.

Now (D.7) holds (Lemma D.2), and $\omega(q) = \frac12(\cos q + \sin q)$. With
$A(y) = \rho_0 - \frac12 - \frac{31}{100}(y + y^2)$ and
$\Phi(y, q) = A(y)\sin q + (y - \frac12)\cos q$, the first two bounds give

```math
0 \le a_W\sin q + x\cos q + b_D - \tfrac12 - \tfrac12(\cos q + \sin q) < \Phi(x, q) - \tfrac{19}{100} - \tfrac{17}{100}d .
```

The function $\Phi$ does not decrease when $y$ is raised from $x$ to $U = U(v)$:
as $A(U) - A(x) = -\frac{31}{100}(U - x)(1 + x + U)$,

```math
\Phi(U, q) - \Phi(x, q) = (U - x)\left(\cos q - \tfrac{31}{100}(1 + x + U)\sin q\right) ,
```

and, since $x < U \le \frac{47}{100}$ gives $1 + x + U \le \frac{97}{50}$, the
last factor is at least

```math
\tfrac{389}{720} - \tfrac{31}{100}\cdot\tfrac{97}{50}\cdot\tfrac{101}{120} = 0.0340\ldots > 0 .
```

With $d = q - v$ we obtain $0 < F(U(v), v, q)$, where

```math
F(U, v, q) = A(U)\sin q + \left(U - \tfrac12\right)\cos q - \tfrac{19}{100} - \tfrac{17}{100}q + \tfrac{17}{100}v .
```

For $0 \le U \le \frac{47}{100}$,

```math
A(U) \ge \rho_0 - \tfrac12 - \tfrac{31}{100}\left(\tfrac{47}{100} + \tfrac{47^2}{100^2}\right) > 0.398 ,
```

so

```math
\tfrac{\partial F}{\partial q} = A(U)\cos q - \left(U - \tfrac12\right)\sin q - \tfrac{17}{100} \ge 0.39\cdot\tfrac{389}{720} - \tfrac{17}{100} > 0
```

on $[0, 1]$, and $F(U(v), v, q) \le F(U(v), v, 1)$ (Lemma A.1). Along the
profile $U(v) = U_0 - kv$, for $0 \le v \le V$, expanding gives

```math
F(U(V), V, 1) - F(U(v), v, 1) = (V - v)\left(\tfrac{31}{100}k\left(1 + U(v) + U(V)\right)\sin 1 - k\cos 1 + \tfrac{17}{100}\right) ,
```

and with $U(v) \ge U(V)$, $\sin 1 \ge 1 - \frac16 = \frac56$ and
$\cos 1 \le C_4(1) = \frac{13}{24}$ the bracket is at least
$\frac{31}{100}k(1 + 2U(V))\frac56 - \frac{13}{24}k + \frac{17}{100}$. For the
matching side, $k = \frac23$, $V = \frac25$ and $U(V) = \frac{61}{300}$, and the
bracket is at least $0.051 > 0$; for the own axis, $k = \frac{73}{100}$,
$V = \frac12$ and $U(V) = 0.101$, and it is at least $0.00126 > 0$. So
$F(U(v), v, 1) \le F(U(V), V, 1)$. Finally, as $\rho_0 - \frac12 < \mu_+$,
$A(U) > 0$, $U - \frac12 < 0$, $\sin 1 \le \frac{101}{120}$ and
$\cos 1 \ge \frac{389}{720}$,

```math
F(U, V, 1) < \left(\mu_+ - \tfrac{31}{100}\left(U + U^2\right)\right)\tfrac{101}{120} + \left(U - \tfrac12\right)\tfrac{389}{720} - \tfrac9{25} + \tfrac{17}{100}V ,
```

which is $-0.000332\ldots$ at $(U, V) = (\frac{61}{300}, \frac25)$ and
$-0.00379\ldots$ at $(U, V) = (0.101, \frac12)$. So $F(U(v), v, q) < 0$, a
contradiction (Figure D.6). $\square$

*Lean:
[`Six.westDiagonal_gap_gt_one`](../../SquaresInCircles/Six/Wings/WestGap.lean#L161),
[`Six.westDefect`](../../SquaresInCircles/Six/Wings/WestGap.lean#L24),
[`Six.trig_one_bounds`](../../SquaresInCircles/Six/Wings/WestGap.lean#L28),
[`Six.signed_radial_quadratic`](../../SquaresInCircles/Six/Wings/WestGap.lean#L35),
[`Six.quadratic_projection_mono`](../../SquaresInCircles/Six/Wings/WestGap.lean#L40),
[`Six.westDefect_mono_q`](../../SquaresInCircles/Six/Wings/WestGap.lean#L52),
[`Six.westDefect_profile_endpoint`](../../SquaresInCircles/Six/Wings/WestGap.lean#L79),
[`Six.westDefect_endpoint_bounds`](../../SquaresInCircles/Six/Wings/WestGap.lean#L107),
[`Six.westDefect_own_negative`](../../SquaresInCircles/Six/Wings/WestGap.lean#L121),
[`Six.westDefect_cardinal_negative`](../../SquaresInCircles/Six/Wings/WestGap.lean#L132),
[`Six.west_secondary_defect_upper`](../../SquaresInCircles/Six/Wings/WestGap.lean#L143),
[`Six.Wings.west_gap`](../../SquaresInCircles/Six/Wings/Separators.lean#L65).*

![Two graphs over q from 0 to 1, each with three increasing curves below the dashed zero line: left for W on its own axis with v = 0, 1/4, 1/2, right for W on the west side of C with v = 0, 1/5, 2/5; the curves for larger v start lower and end higher, and the highest end, at q = 1, is marked by an orange dot just below zero](figures/appendix-d/gap.svg)

*Figure D.6.* The bound $F(U(v), v, q)$ of the margin of (D.7) in the proof of
Lemma D.5, for $0 \le q \le 1$, computed with $\rho_0$ itself: left with the
profile of $W$ on its own axis, right with that of $W$ on the west side of $C$.
Each curve increases in $q$, and the value at $q = 1$ increases in $v$; the
largest (orange dot) is still negative.

## D.4 The range of a missing west wing

When $W$ is on its own axis, a missing west wing is first confined to a small
range of the angles $v$ and $d$, by four stresses on the separations of $C$ from
$W$ and from $D$ along their own axes and of $W$ and $D$ along $e^D_2$
(Figure D.7). Their profile is the following.

### Lemma D.6 (the profile of W and D)

Let wing data satisfy (D.2) and (D.7), with $v \ge 0$, $d \ge 0$ and
$q \le \frac\pi2$. Let $b, z \ge 0$ and let $w_0$, $w_1$, $w_2$, $D_0$ be
numbers with

```math
(b + \sin q)a_W - b_W\cos q \le w_0 + w_1\sin q + w_2\cos q , \qquad za_D + b_D \le D_0 .
```

Then, for one of $y = 0$ and $y = \bar c$,

```math
P(v, d) = K + b\left(\mu_-\cos v + \left(\tfrac12 + y\right)\sin v\right) + z\left(\mu_-\cos d + \left(\tfrac12 - y\right)\sin d\right) + \alpha\cos q + \beta\sin q \le 0 ,
```

where $\alpha = \frac12 - w_2$, $\beta = \frac12 - w_1$ and
$K = \frac12(b + z + 1) - w_0 - D_0$.

*Proof.* Add (D.2), (D.1) and (D.7) with the weights $b$, $z$ and $1$. By Table
D.1 the forces are $(b + \sin q, -\cos q)$ on $W$, $(z, 1)$ on $D$ and
$(b\cos v + z\cos d, z\sin d - b\sin v)$ on $C$, and as $v$, $d$, $q$ lie in
$[0, \frac\pi2]$ the thresholds are $\frac12 + \frac12(\cos x + \sin x)$ for
$x = v, d, q$. So

```math
\tfrac{b + z + 1}2 + \tfrac b2(\cos v + \sin v) + \tfrac z2(\cos d + \sin d) + \tfrac12(\cos q + \sin q) \le w_0 + w_1\sin q + w_2\cos q + D_0 + c_x(b\cos v + z\cos d) + c_y(z\sin d - b\sin v) .
```

Here $c_x(b\cos v + z\cos d) \le \bar c(b\cos v + z\cos d)$, and
$c_y(z\sin d - b\sin v) \le y(z\sin d - b\sin v)$ with $y = \bar c$ if the
bracket is nonnegative and $y = 0$ otherwise. Moving everything to the left and
using $\frac12 - \bar c = \mu_-$ gives $P(v, d) \le 0$. $\square$

*Lean:
[`Six.Wings.WestRange.profile`](../../SquaresInCircles/Six/Wings/WestRange.lean#L38),
[`Six.Wings.WestRange.profile_nonpos`](../../SquaresInCircles/Six/Wings/WestRange.lean#L204).*

![The squares C, W, D and S of a missing west wing with W on its own axis, W turned up by about 30 degrees, in the lower left part of the disk: the separating lines of the stress in colour, along the side of W facing C, along the upper right side of D facing C, and along the upper left side of D facing W; in grey the separations of S. Orange arrows show the forces on W, D and C; there is none on S](figures/appendix-d/range.svg)

*Figure D.7.* The stress of Lemma D.6, with the weights $b = \frac{13}6$ and
$z = \frac{12}5$ of Proposition D.7 (1), on a missing west wing with $W$ and
$S$ on their own axes, at $v = 0.55$, $s = 0.1$ and $d = 0.55$, in the
smallest disk that allows its separations (radius $1.698$, pink; the circle of
radius $R_0$ is dashed). The forces are $(b + \sin q, -\cos q)$ on $W$, close
to its own axis, $(z, 1)$ on $D$, and $(b\cos v + z\cos d, z\sin d - b\sin v)$
on $C$.

The profile is a constant plus a first harmonic in each of four directions: in
$v$ at fixed $d$, in $d$ at fixed $v$, in $d$ along a line $q = k$, and in $q$
at fixed $d$. Expanding $\cos q$ and $\sin q$,

```math
\begin{aligned}
P &= K_1(d) + \left(b\mu_- + \alpha\cos d + \beta\sin d\right)\cos v + \left(b\left(\tfrac12 + y\right) - \alpha\sin d + \beta\cos d\right)\sin v , \\
P &= K_2(v) + \left(z\mu_- + \alpha\cos v + \beta\sin v\right)\cos d + \left(z\left(\tfrac12 - y\right) - \alpha\sin v + \beta\cos v\right)\sin d , \\
P &= K_3(k) + \left(z\mu_- + b\left(\mu_-\cos k + \left(\tfrac12 + y\right)\sin k\right)\right)\cos d + \left(z\left(\tfrac12 - y\right) + b\left(\mu_-\sin k - \left(\tfrac12 + y\right)\cos k\right)\right)\sin d \quad (v = k - d), \\
P &= K_1(d) + \left(\alpha + b\left(\mu_-\cos d - \left(\tfrac12 + y\right)\sin d\right)\right)\cos q + \left(\beta + b\left(\mu_-\sin d + \left(\tfrac12 + y\right)\cos d\right)\right)\sin q \quad (v = q - d),
\end{aligned}
```

with $K_1(d) = K + z(\mu_-\cos d + (\frac12 - y)\sin d)$,
$K_2(v) = K + b(\mu_-\cos v + (\frac12 + y)\sin v)$ and
$K_3(k) = K + \alpha\cos k + \beta\sin k$. When the two coefficients of a
direction are nonnegative along a segment of $[0, \frac\pi2]$ in that direction,
the profile is positive on the segment once it is positive at its ends (Lemma
A.11 (2)). In the three stresses with $\alpha = \frac12$ and $\beta = -\mu_+$ the
coefficients in $v$ and in $d$ are nonnegative as soon as $\mu_+ \le b\mu_-$ and
$\frac45 \le b(\frac12 + y)$, and $\mu_+ \le z\mu_-$ and
$\frac45 \le z(\frac12 - y)$: for $x \in [0, \frac\pi2]$,
$\frac12\cos x - \mu_+\sin x \ge -\mu_+$, and

```math
\tfrac12\sin x + \mu_+\cos x \le \sqrt{\tfrac14 + \mu_+^2} = \sqrt{0.62554\ldots} < \tfrac45 .
```

### Proposition D.7 (the range of a missing west wing)

Let wing data satisfy (D.2) and (D.7).

1. If $v \le \frac23$, $d \ge \frac12$ and $q \ge 1$, then $d > \frac35$.
2. If $v \ge 0$, $\frac35 \le d \le \frac{11}{14}$ and $q \ge 1$, then
   $q > \frac{53}{50}$.
3. If $v \le \frac23$, $\frac35 \le d \le \frac{11}{14}$ and $q \ge 1$, then
   $v < \frac{31}{50}$.
4. If $v \le \frac{31}{50}$, $d \ge \frac35$ and $q \ge \frac{53}{50}$, then
   $d > \frac{16}{25}$.

Consequently, in a normalized packing with a missing west wing and $W$ on its
own axis,

```math
q > \tfrac{53}{50}, \qquad v < \tfrac{31}{50}, \qquad d > \tfrac{16}{25} .
```

*Proof.* In each part suppose the contrary. Then $(v, d)$ lies in a domain
$\mathcal D$ of the first quadrant with $1 \le q \le \frac\pi2$, listed in Table
D.3, and Lemma D.6 applies with the weights and supports of the table. In part
(1), $d \le \frac35$ and $q \ge 1$ give $v \ge \frac25$, and in all parts
$q \le \frac{11}{14} + \frac23 < \frac\pi2$.

| part | domain $\mathcal D$ | $b$ | $z$ | support of $W$ | support of $D$ |
| :-: | --- | :-: | :-: | --- | --- |
| (1) | $\frac12 \le d \le \frac35$, $1 - d \le v \le \frac23$ | $\frac{13}6$ | $\frac{12}5$ | cone | far vertex, $\ell = \frac{13}5$ |
| (2) | $\frac35 \le d \le \frac{11}{14}$, $1 \le q \le \frac{53}{50}$ | $\frac27$ | $\frac{12}5$ | far vertex, tangent at $\frac54$ | far vertex, $\ell = \frac{13}5$ |
| (3) | $\frac35 \le d \le \frac{11}{14}$, $\frac{31}{50} \le v \le \frac23$ | $\frac{17}3$ | $\frac{14}3$ | cone | cone |
| (4) | $\frac35 \le d \le \frac{16}{25}$, $\frac{53}{50} - d \le v \le \frac{31}{50}$ | $\frac{25}{12}$ | $\frac94$ | cone | far vertex, $\ell = 2.4623$ |

*Table D.3.* The four stresses of Proposition D.7.

*The supports.* The force on $W$ is $(b + \sin q, -\cos q)$. For $b \ge 2$ and
$1 \le q \le \frac\pi2$ it lies in the first cone (K), since
$\cos q \le \cos 1 \le \frac{13}{24} < \frac{31}{100}\cdot 2$; so
$w_0 = \bar\rho b$, $w_1 = \bar\rho$, $w_2 = 0$, that is, $\alpha = \frac12$ and
$\beta = \frac12 - \bar\rho = -\mu_+$. In part (2) the force has the length
$\sqrt{\frac4{49} + 1 + \frac47\sin q}$, at most
$\frac25(\frac{53}{49} + \frac{25}{16} + \frac47\sin q)$ by the tangent of the
square root at $\frac54$
([Lemma A.14](appendix-a.md#lemma-a14-tangents-of-the-square-root)), and the far
vertex (V) gives
$w_0 = \frac25(\frac{53}{49} + \frac{25}{16})\bar R - \frac17 = 1.64309\ldots$,
$w_1 = \frac8{35}\bar R - \frac12$, $w_2 = -\frac12$, so $\alpha = 1$ and
$\beta = 1 - \frac8{35}\bar R = 0.61403\ldots$. The force on $D$ is $(z, 1)$.
Its length is $\frac{13}5$ for $z = \frac{12}5$ and $\frac{\sqrt{97}}4 < 2.4623$
for $z = \frac94$, and the far vertex gives $D_0 = \bar R\ell - \frac12(z + 1)$;
for $z = \frac{14}3$ it lies in the first cone, $1 \le \frac{31}{100}z$, and
$D_0 = \bar\rho z$. With these numbers $K = -2.31813\ldots$, $-2.49059\ldots$,
$-5.83247\ldots$ and $-2.18454\ldots$ in parts (1) to (4).

*From the corners to the domain.* In parts (1), (3) and (4) the coefficients in
$v$ and $d$ are nonnegative, by the criterion above: $b\mu_-$ and $z\mu_-$ are
at least $\frac{25}{12}\mu_- = 0.806\ldots > \mu_+$,
$b(\frac12 + y) \ge \frac{25}{24}$ and
$z(\frac12 - y) \ge \frac94\mu_- = 0.871\ldots$. Along the lines $q = k$ with
$k \ge 1$ the coefficients of $\cos d$ are positive, and those of $\sin d$ are
at least $z\mu_- - b\mu_+\cos k \ge z\mu_- - \frac{13}{24}b\mu_+$, which is
$0.929 - 0.719 > 0$ in part (1) and $0.871 - 0.692 > 0$ in part (4). In part
(2), along $q = k$ the coefficient of $\sin d$ is at least
$z\mu_- - b\mu_+ = 0.929 - 0.175 > 0$, and in $q$ the coefficients are at least
$1 - \frac27\mu_+ > 0$ and $\beta > 0$. Hence, in parts (1) and (4)
($d_1 \le d \le d_2$, $k - d \le v \le t$), positivity at the four corners
$(k - d_1, d_1)$, $(t, d_1)$, $(t, d_2)$, $(k - d_2, d_2)$ gives positivity on
the edges $v = k - d$ and $v = t$, as harmonics in $d$, and then on each segment
in $v$ between them. In part (3), the rectangle, positivity at the corners gives
it on the edges $v = \frac{31}{50}$ and $v = \frac23$ and then in $v$. In part
(2) it gives positivity on the edges $q = 1$ and $q = \frac{53}{50}$, and then
on each segment in $q$ at fixed $d$.

*The corners.* At a corner, $P$ is at least the value of the polynomial obtained
by replacing $\cos x$ by $C_6(x)$ for $x = v, d, q$ and $\sin x$ by $S_7(x)$ for
$x = v, d$, and $\beta\sin q$ by $\beta S_5(q)$ if $\beta < 0$ and by
$\beta S_7(q)$ if $\beta > 0$ (all angles are nonnegative and the other
coefficients are positive). Table D.4 lists these values for both faces $y$; all
are positive, which contradicts $P \le 0$.

| part | $(v, d)$ at the corners | $y = 0$ | $y = \bar c$ |
| :-: | --- | --- | --- |
| (1) | $(\frac12, \frac12)$, $(\frac23, \frac12)$, $(\frac23, \frac35)$, $(\frac25, \frac35)$ | $0.08257$, $0.03458$, $0.01986$, $0.07524$ | $0.06995$, $0.05592$, $0.01813$, $0.01755$ |
| (2) | $(\frac25, \frac35)$, $(\frac{23}{50}, \frac35)$, $(\frac{48}{175}, \frac{11}{14})$, $(\frac3{14}, \frac{11}{14})$ | $0.16838$, $0.14093$, $0.18472$, $0.21049$ | $0.02805$, $0.00235$, $0.00192$, $0.02582$ |
| (3) | $(\frac{31}{50}, \frac35)$, $(\frac23, \frac35)$, $(\frac23, \frac{11}{14})$, $(\frac{31}{50}, \frac{11}{14})$ | $0.00398$, $0.01690$, $0.02017$, $0.00332$ | $0.07817$, $0.11495$, $0.04309$, $0.00238$ |
| (4) | $(\frac{23}{50}, \frac35)$, $(\frac{31}{50}, \frac35)$, $(\frac{31}{50}, \frac{16}{25})$, $(\frac{21}{50}, \frac{16}{25})$ | $0.06453$, $0.02719$, $0.01655$, $0.05695$ | $0.02554$, $0.02042$, $0.00152$, $0.00120$ |

*Table D.4.* Lower bounds of the profile $P$ at the corners of the domains, by
Taylor polynomials, rounded down.

*The consequences.* In a normalized packing with a missing west wing and $W$ on
its own axis, Lemma D.2 gives (D.2), (D.7), $0 < v < \frac23$ and
$\frac12 < d \le \frac\pi4 < \frac{11}{14}$, and Lemma D.5 gives $q > 1$. Part
(1) gives $d > \frac35$, and then parts (2) and (3) give $q > \frac{53}{50}$ and
$v < \frac{31}{50}$, and part (4) gives $d > \frac{16}{25}$ (Figure D.8).
$\square$

*Lean:
[`Six.Wings.WestRange.profile_west`](../../SquaresInCircles/Six/Wings/WestRange.lean#L44),
[`Six.Wings.WestRange.profile_diagonal`](../../SquaresInCircles/Six/Wings/WestRange.lean#L56),
[`Six.Wings.WestRange.profile_wall`](../../SquaresInCircles/Six/Wings/WestRange.lean#L62),
[`Six.Wings.WestRange.profile_gap`](../../SquaresInCircles/Six/Wings/WestRange.lean#L50),
[`Six.Wings.adverse_harmonic`](../../SquaresInCircles/Six/Wings/WestRange.lean#L28),
[`Six.Wings.WestRange.cone_coefficients`](../../SquaresInCircles/Six/Wings/WestRange.lean#L72),
[`Six.Wings.WestRange.lower`](../../SquaresInCircles/Six/Wings/WestRange.lean#L85),
[`Six.Wings.WestRange.lower_le_profile`](../../SquaresInCircles/Six/Wings/WestRange.lean#L91),
[`Six.Wings.WestRange.positive_wall`](../../SquaresInCircles/Six/Wings/WestRange.lean#L114),
[`Six.Wings.WestRange.positive_rectangle`](../../SquaresInCircles/Six/Wings/WestRange.lean#L144),
[`Six.Wings.WestRange.positive_gap`](../../SquaresInCircles/Six/Wings/WestRange.lean#L172),
[`Six.Wings.WestRange.west_cone`](../../SquaresInCircles/Six/Wings/WestRange.lean#L243),
[`Six.Wings.WestRange.west_vertex`](../../SquaresInCircles/Six/Wings/WestRange.lean#L272),
[`Six.Wings.WestRange.diagonal_vertex`](../../SquaresInCircles/Six/Wings/WestRange.lean#L257),
[`Six.Wings.WestRange.diagonal_cone`](../../SquaresInCircles/Six/Wings/WestRange.lean#L264),
[`Six.Wings.WestRange.diagonal_gt_three_fifths`](../../SquaresInCircles/Six/Wings/WestRange.lean#L292),
[`Six.Wings.WestRange.gap_gt`](../../SquaresInCircles/Six/Wings/WestRange.lean#L322),
[`Six.Wings.WestRange.west_lt`](../../SquaresInCircles/Six/Wings/WestRange.lean#L345),
[`Six.Wings.WestRange.diagonal_gt`](../../SquaresInCircles/Six/Wings/WestRange.lean#L368),
[`Six.Wings.own_west_range`](../../SquaresInCircles/Six/Wings/Separators.lean#L72).*

![Two plots of angle domains. Left, in the plane of s and d: a grey region left of a purple line from s = 1/2 − π/4 at d = 1/2 to s = 0 at d = π/4, the wall, and a green region to its right, with dashed vertical lines at s = 0, 2/5 and 12/25. Right, in the plane of v and d: a grey triangle under the wall, a yellow band where q = d + v is at most 1, and four pieces labelled (1) to (4) for the four parts of Proposition D.7, shaded from white to blue, which leave a small green quadrilateral at the top right with three marked points](figures/appendix-d/walls.svg)

*Figure D.8.* The walls and the range. Left: the angles $(s, d)$ of a missing
south wing; the wall of Lemma 9.42 excludes $s \le d - \frac\pi4$ (grey), and
the dashed lines $s = 0$, $\frac25$ and $\frac{12}{25}$ bound the angles of $S$
on its own axis and on the south side of $C$ and separate Propositions D.11 and
D.12. Right: the angles $(v, d)$ of a missing west wing with $W$ on its own
axis; the wall $v \le \frac\pi4 - d$ (grey), the gap $q \le 1$ of Lemma D.5
(yellow) and the parts (1) to (4) of Proposition D.7, each shaded by the
profile $P$ of its stress, the smaller over the two faces $y$, leave the green
domain of §D.9, with the three points of Lemma D.18.

## D.5 W on the west side of C

Let $W$ be separated from $C$ along the west side of $C$. The separation (D.3)
pushes $W$ along $(-1, 0)$, which in the frame of $W$ is the force
$(\cos v, \sin v)$: a transverse component that the separation of $W$ and $D$
along $e^W_2$ balances. Three stresses cover the missing wings: a missing west
wing with $S$ on the south side of $C$ (Proposition D.10), a missing south wing
with $s \le \frac{12}{25}$ (Proposition D.11), and a missing south wing with $S$
on its own axis and $s \ge \frac{12}{25}$ (Proposition D.12). In the first two
all works are bounded by far vertices, and the radicals they bring are handled
by [Lemma A.12](appendix-a.md#lemma-a12-a-harmonic-less-a-radical).

### Lemma D.8 (far-vertex terms)

1. $\cos x \ge \frac{23}{25}$ for $\lvert x\rvert \le \frac25$, and the function

   ```math
   T(x) = 4\cos x + 4\max(-\sin x, 0) - R_0\sqrt{25 - 24\sin x}
   ```

   is concave on $[-\frac25, 0]$ and on $[0, \frac25]$.
2. For $0 \le x \le \frac65$, $\cos\frac x2 \ge \sin\frac x2$,
   $\cos^2x + (1 - \sin x)^2 = 2(\cos\frac x2 - \sin\frac x2)^2$, and, for
   $c \le 4$, $\cos x - c\cos\frac x2 + c\sin\frac x2$ is concave in $x$ on
   $[0, \frac65]$.

*Proof.* (1) $\cos x \ge 1 - \frac{x^2}2 \ge 1 - \frac2{25}$. On
$[-\frac25, 0]$, $\sin x \le 0$ and
$T(x) = 4\cos x - 4\sin x - R_0\sqrt{25 - 24\sin x}$; on $[0, \frac25]$,
$T(x) = 4\cos x - R_0\sqrt{25 - 24\sin x}$. Lemma A.12 applies with $A = 4$,
$B = -4$ or $B = 0$, $R = R_0$ and the radicand $25 - 24\sin x$ (its constants
$p = 25$ and $-24$ satisfy $24^2 \le 25^2$): $25 - 24\sin x \ge 1$, and

```math
R_0\sqrt{25 - 24\sin x} \le 7R_0 < 11.9 < 16\cdot\tfrac{23}{25} \le 4\left(4\cos x + B\sin x\right) ,
```

as $B\sin x \ge 0$ on each piece.

(2) Here $0 \le \frac x2 < \frac\pi4$, so $\cos\frac x2 \ge \sin\frac x2$; both
sides of the identity are $2 - 2\sin x$ by $\sin x = 2\sin\frac x2\cos\frac x2$;
and with $\cos x = (\cos\frac x2 - \sin\frac x2)(\cos\frac x2 + \sin\frac x2)$
the second derivative of the function is

```math
-\cos x + \tfrac c4\left(\cos\tfrac x2 - \sin\tfrac x2\right) = \left(\cos\tfrac x2 - \sin\tfrac x2\right)\left(\tfrac c4 - \cos\tfrac x2 - \sin\tfrac x2\right) \le 0 ,
```

since $\cos\frac x2 + \sin\frac x2 \ge 1 \ge \frac c4$. $\square$

*Lean:
[`Six.Wings.WestSide.southTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L38),
[`Six.Wings.WestSide.cos_small`](../../SquaresInCircles/Six/Wings/WestSide.lean#L41),
[`Six.Wings.WestSide.south_radical_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L47),
[`Six.Wings.WestSide.southTerm_negative_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L66),
[`Six.Wings.WestSide.southTerm_positive_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L81),
[`Six.Wings.WestSide.halfDifference`](../../SquaresInCircles/Six/Wings/WestSide.lean#L100),
[`Six.Wings.WestSide.half_difference_lower`](../../SquaresInCircles/Six/Wings/WestSide.lean#L106),
[`Six.Wings.WestSide.norm_identity`](../../SquaresInCircles/Six/Wings/WestSide.lean#L113),
[`Six.Wings.WestSide.diagonalTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L102),
[`Six.Wings.WestSide.diagonalFirst`](../../SquaresInCircles/Six/Wings/WestSide.lean#L103),
[`Six.Wings.WestSide.diagonalSecond`](../../SquaresInCircles/Six/Wings/WestSide.lean#L104),
[`Six.Wings.WestSide.diagonal_hasDeriv`](../../SquaresInCircles/Six/Wings/WestSide.lean#L120),
[`Six.Wings.WestSide.diagonal_first_hasDeriv`](../../SquaresInCircles/Six/Wings/WestSide.lean#L127),
[`Six.Wings.WestSide.diagonal_second_nonpositive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L137),
[`Six.Wings.WestSide.diagonal_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L156).*

The force $(4\cos x, 3 - 4\sin x)$ has the length $\sqrt{25 - 24\sin x}$, and
the threshold $4\tau(x)$ of its separation less the far-vertex bound of its
work is $\frac72 + T(x)$ (Figure D.9). It is the force on $S$ in Proposition
D.10, and, with $x = v$ and its second component negated, the force on $W$ in
Proposition D.11. Part (2) serves the force $(\cos x, 1 - \sin x)$ on $D$ in
Propositions D.10, D.19 and D.20.

![The graph of T(x) on x from -2/5 to 2/5, in blue: on the left half it rises slowly from about -4.65 to about -4.44, on the right half steeply to about -3.00, with a corner at 0; on each half it lies above its dashed orange chord, and dots mark the values at -2/5, 0 and 2/5](figures/appendix-d/far-term.svg)

*Figure D.9.* Lemma D.8 (1): the function $T$ is concave on $[-\frac25, 0]$ and
on $[0, \frac25]$, above its chords (dashed), but its slope jumps up at $0$,
from about $0.05$ to about $4.05$. Propositions D.10 and D.11 therefore check
the three points $-\frac25$, $0$ and $\frac25$.

### Lemma D.9 (brackets)

1. $0.921 \le \cos\frac25$, $0.389 \le \sin\frac25 \le 0.39$;
   $0.8775 \le \cos\frac12$, $0.4794 \le \sin\frac12 \le 0.4795$;
   $0.621 \le \cos\frac9{10}$, $0.783 \le \sin\frac9{10}$;
   $0.995 \le \cos\frac1{10}$, $0.099 \le \sin\frac1{10}$.
2. $0.707 \le h \le 0.708$, $\cos(\frac\pi4 + \frac25) \ge 0.375$,
   $\sin(\frac\pi4 + \frac25) \ge 0.926$, $\cos(\frac\pi4 - \frac25) \ge 0.926$,
   $\sin(\frac\pi4 - \frac25) \ge 0.375$ and
   $\cos(\frac\pi4 + \frac25) + \sin(\frac\pi4 + \frac25) \ge 1.302$.

*Proof.* (1) By Lemma A.7: $C_6(\frac25) = 0.92106\ldots$,
$S_7(\frac25) = 0.38941\ldots$, $S_5(\frac25) = 0.38941\ldots$,
$C_6(\frac12) = 0.87758\ldots$, $S_7(\frac12) = 0.47942\ldots$,
$S_5(\frac12) = 0.47942\ldots$, $C_6(\frac9{10}) = 0.62159\ldots$,
$S_7(\frac9{10}) = 0.78332\ldots$, $S_7(\frac1{10}) = 0.09983\ldots$, and
$\cos\frac1{10} \ge 1 - \frac1{200}$. (2) $0.707^2 < \frac12 < 0.708^2$. As
$\cos(\frac\pi4 \pm x) = h(\cos x \mp \sin x)$ and
$\sin(\frac\pi4 \pm x) = h(\cos x \pm \sin x)$, (1) gives the lower bounds
$0.707(0.921 - 0.39) = 0.375417$, $0.707(0.921 + 0.389) = 0.92617$ and
$0.707\cdot 2\cdot 0.921 = 1.302294$. $\square$

*Lean:
[`Six.Wings.WestSide.trig_two_fifths`](../../SquaresInCircles/Six/Wings/WestSide.lean#L165),
[`Six.trig_bracket_half`](../../SquaresInCircles/Six/Constants.lean#L41),
[`Six.Wings.WestSide.trig_nine_tenths`](../../SquaresInCircles/Six/Wings/WestSide.lean#L171),
[`Six.Wings.WestSide.trig_tenth`](../../SquaresInCircles/Six/Wings/WestSide.lean#L175),
[`Six.Wings.WestSide.half_root_bounds`](../../SquaresInCircles/Six/Wings/WestSide.lean#L179),
[`Six.Wings.WestSide.quarter_shift_bounds`](../../SquaresInCircles/Six/Wings/WestSide.lean#L185).*

### Proposition D.10 (W on the west side: a missing west wing)

There are no wing data with a missing west wing that satisfy (D.3) and (D.5),
with $0 \le v \le \frac25$, $\lvert s\rvert \le \frac25$ and
$\frac12 \le d \le \frac\pi4$.

*Proof.* *The stress.* Add (D.3), (D.5), (D.7) and (D.8) with the weights $2$,
$4$, $3$ and $3$. By Table D.1 the forces are

```math
F_W = (2\cos v + 3\sin q,\ 2\sin v - 3\cos q), \quad F_D = (3\cos r,\ 3 - 3\sin r), \quad F_S = (4\cos s,\ 3 - 4\sin s), \quad F_C = (2, 4),
```

with $\lvert F_W\rvert^2 = 13 + 12\sin(q - v) = 13 + 12\sin d$,
$\lvert F_D\rvert^2 = 18 - 18\sin r$ and $\lvert F_S\rvert^2 = 25 - 24\sin s$.
The gaps $q \in [\frac12, \frac\pi4 + \frac25]$ and
$r \in [\frac1{10}, \frac\pi4 + \frac25]$ lie in $[0, \frac\pi2]$, and
$\cos s > 0$, so the thresholds are $\frac12 + \frac12(\cos x + \sin x)$ for
$x = v, q, r$ and $\frac12 + \frac12(\cos s + \lvert\sin s\rvert)$.

*The supports.* The far vertex (V) with $R_0$ bounds the works on $W$, $D$ and
$S$; in its term $\frac12(\lvert U\rvert + \lvert V\rvert)$ we use
$\lvert x\rvert \ge x$ and $\lvert x\rvert \ge -x$ to replace it by
$\frac12(2\cos v + 3\sin q - 2\sin v + 3\cos q)$,
$\frac12(3\cos r + 3 - 3\sin r)$ and $\frac12(4\cos s + 3 - 4\sin s)$. The box
gives $2c_x + 4c_y \le 6c_0$. Collecting the terms, the weighted sum becomes
$\Pi(v, s, d) \le 0$, where

```math
\Pi(v, s, d) = 9 - 6c_0 + 2\cos v + T(s) + \Delta(d - s) + 3(\cos q + \sin q) - R_0\sqrt{13 + 12\sin d},
\qquad \Delta(x) = 3\cos x - R_0\sqrt{18 - 18\sin x} ,
```

with $T$ of Lemma D.8 (1): the term $2(\lvert\sin s\rvert - \sin s)$ is
$4\max(-\sin s, 0)$.

*Concavity.* For $0 \le x \le \frac65$, Lemma D.8 (2) gives
$\sqrt{18 - 18\sin x} = 3\sqrt2(\cos\frac x2 - \sin\frac x2)$, so
$\Delta(x) = 3(\cos x - c\cos\frac x2 + c\sin\frac x2)$ with
$c = \sqrt2R_0 < 4$, and $\Delta$ is concave on $[0, \frac65]$.

As $3(\cos q + \sin q) = A\cos d + B\sin d$ with $A = 3(\cos v + \sin v)$ and
$B = 3(\cos v - \sin v)$, the function
$d \mapsto 3(\cos q + \sin q) - R_0\sqrt{13 + 12\sin d}$ is concave on
$[\frac12, \frac\pi4]$, by Lemma A.12 with these $A$ and $B$, $R = R_0$ and the
radicand $13 + 12\sin d$: there
$R_0\sqrt{13 + 12\sin d} \le 5R_0 < 8.45 < 12 \le 12(\cos q + \sin q)$, by Lemma
A.15 (2). So $\Pi$ is concave in $d$. In $v$, $2\cos v + 3(\cos q + \sin q)$
is a first harmonic, at least $2\cdot\frac{23}{25} + 3 > 0$, hence concave
(Lemma A.11 (1)), and the rest of $\Pi$ does not depend on $v$. In $s$, $T$ is
concave on $[-\frac25, 0]$ and on $[0, \frac25]$ (Lemma D.8 (1)), and so is
$s \mapsto \Delta(d - s)$ (Lemma A.10 (3)). By Lemma A.10 (2), applied in $d$,
then in $v$, then in $s$ on each half, $\Pi > 0$ on the box
$[0, \frac25] \times [-\frac25, \frac25] \times [\frac12, \frac\pi4]$ once
$\Pi > 0$ at the twelve points with $v \in \lbrace 0, \frac25\rbrace$,
$s \in \lbrace -\frac25, 0, \frac25\rbrace$ and
$d \in \lbrace \frac12, \frac\pi4\rbrace$.

*The twelve points.* At these points the angles $q$ and $r$ take the values
$\frac1{10}$, $\frac12$, $\frac9{10}$ and $\frac\pi4$, $\frac\pi4 \pm \frac25$,
where Lemma D.9 bounds the sines and cosines. Table D.5 lists the resulting
bounds of the terms; each bound of a root holds because its square exceeds the
radicand at the bracket, for instance $18 - 18\cdot 0.783 = 3.906 < 1.977^2$.

| term | bounds |
| --- | --- |
| $2\cos v$ | $2$ at $v = 0$; $\ge 1.842$ at $v = \frac25$ |
| $4\cos s + 4\max(-\sin s, 0)$ | $\ge 5.24$, $4$, $\ge 3.684$ at $s = -\frac25, 0, \frac25$ |
| $\sqrt{25 - 24\sin s}$ | $\le 5.862$, $5$, $\le 3.958$ at $s = -\frac25, 0, \frac25$ |
| $\sqrt{13 + 12\sin d}$ | $\le 4.331$, $\le 4.637$ at $d = \frac12, \frac\pi4$ |
| $\cos q + \sin q$ | $\ge 1.356$, $1.414$, $1.404$, $1.302$ at $q = \frac12, \frac\pi4, \frac9{10}, \frac\pi4 + \frac25$ |
| $\cos r$ | $\ge 0.995$, $0.877$, $0.621$, $0.926$, $0.707$, $0.375$ at $r = \frac1{10}, \frac12, \frac9{10}, \frac\pi4 - \frac25, \frac\pi4, \frac\pi4 + \frac25$ |
| $\sqrt{18 - 18\sin r}$ | $\le 4.028$, $3.062$, $1.977$, $3.355$, $2.297$, $1.155$ at the same $r$ |

*Table D.5.* Bounds of the terms of $\Pi$ at the twelve points.

With $R_0 < \bar R$ and $c_0 < \bar c$, $\Pi$ is at least $9 - 6\bar c$ plus
the lower bounds of $2\cos v$, $4\cos s + 4\max(-\sin s, 0)$,
$3(\cos q + \sin q)$ and $3\cos r$, less $\bar R$ times the upper bounds of the
three roots. Table D.6 lists these lower bounds; all are positive, a
contradiction (Figure D.10). $\square$

| $(v, s)$ | $d = \frac12$ | $d = \frac\pi4$ |
| :-: | :-: | :-: |
| $(0, -\frac25)$ | $0.94381$ | $1.25113$ |
| $(0, 0)$ | $0.09526$ | $0.53432$ |
| $(0, \frac25)$ | $0.26159$ | $0.84831$ |
| $(\frac25, -\frac25)$ | $0.92981$ | $0.75713$ |
| $(\frac25, 0)$ | $0.08126$ | $0.04032$ |
| $(\frac25, \frac25)$ | $0.24759$ | $0.35431$ |

*Table D.6.* Lower bounds of $\Pi$ at the twelve points, rounded down.

*Lean:
[`Six.Wings.WestSide.MissingWest.impossible`](../../SquaresInCircles/Six/Wings/WestSide.lean#L495),
[`Six.Wings.WestSide.MissingWest.gap`](../../SquaresInCircles/Six/Wings/WestSide.lean#L226),
[`Six.Wings.WestSide.MissingWest.westTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L223),
[`Six.Wings.WestSide.MissingWest.diagonalTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L220),
[`Six.Wings.WestSide.MissingWest.diagonalTerm_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L241),
[`Six.Wings.WestSide.MissingWest.westTerm_diagonal_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L254),
[`Six.Wings.WestSide.MissingWest.gap_diagonal_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L280),
[`Six.Wings.WestSide.MissingWest.gap_west_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L295),
[`Six.Wings.WestSide.MissingWest.gap_south_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L320),
[`Six.Wings.WestSide.MissingWest.endpoint_root_bounds`](../../SquaresInCircles/Six/Wings/WestSide.lean#L337),
[`Six.Wings.WestSide.MissingWest.endpoint_trig`](../../SquaresInCircles/Six/Wings/WestSide.lean#L381),
[`Six.Wings.WestSide.MissingWest.endpoint_roots`](../../SquaresInCircles/Six/Wings/WestSide.lean#L411),
[`Six.Wings.WestSide.MissingWest.rationalReserve_positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L429),
[`Six.Wings.WestSide.MissingWest.endpoint_positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L436),
[`Six.Wings.WestSide.MissingWest.positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L453).*

![Left: the squares C, W, D and S of a missing west wing in the lower left part of the disk, W slightly turned, with the separating lines of the stress in colour, a grey dashed line between C and D, and orange arrows for the forces on the four squares; the squares reach the pink circle, just outside the dashed circle of radius R0. Right: the rectangle of the angles s and d, shaded from white near s = 0 to blue at s = −2/5, with two lower bounds written at each of its six marked points](figures/appendix-d/side-west.svg)

*Figure D.10.* Proposition D.10. Left: a missing west wing with $W$ and $S$ on
the sides of $C$, at $v = 0.3$, $s = 0$ and $d = 0.75$, in the smallest disk
that allows its separations (radius $1.722$, pink; the circle of radius $R_0$ is
dashed): the separating lines of the stress, with the weights $2$, $4$, $3$,
$3$, in colour, the separation (D.1), which the stress does not use, in grey,
and the forces of the stress on $C$, $W$, $D$ and $S$ (orange). Right: the
domain of $(s, d)$, shaded by the minimum over $v$ of $\Pi$, with the bounds
of Table D.6 for $v = 0$ and $v = \frac25$.

### Proposition D.11 (W on the west side: a missing south wing with s ≤ 12/25)

There are no wing data with a missing south wing that satisfy (D.3), with
$\lvert v\rvert \le \frac25$, $\frac12 \le d \le \frac\pi4$,
$s \le \frac{12}{25}$ and $r \le \frac\pi4$.

*Proof.* *The stress.* Add (D.3), (D.6) and (D.9) with the weights $4$, $3$ and
$3$. By Table D.1 the forces are

```math
F_W = (4\cos v,\ 4\sin v - 3), \quad F_D = (3\sin q,\ 3\cos q - 3), \quad F_S = 3(\cos r, \sin r), \quad F_C = (4, 0),
```

with $\lvert F_W\rvert^2 = 25 - 24\sin v$,
$\lvert F_D\rvert = \sqrt{18 - 18\cos q} = 6\sin\frac q2$ and
$\lvert F_S\rvert = 3$. Here
$q \in [\frac1{10}, \frac\pi4 + \frac25] \subset [0, \frac65]$, and
$r \in [d - \frac{12}{25}, \frac\pi4]$ with $d - \frac{12}{25} \ge \frac1{50}$;
and $\cos v \ge \frac{23}{25}$. The thresholds are
$\frac12 + \frac12(\cos v + \lvert\sin v\rvert)$,
$\frac12 + \frac12(\cos q + \sin q)$ and $\frac12 + \omega(r)$.

*The supports.* The far vertex (V) with $R_0$ bounds the three works; for $S$ it
gives
$3R_0 - \frac32(\lvert\cos r\rvert + \lvert\sin r\rvert) = 3R_0 - 3\omega(r)$.
The box gives $4c_x \le 4c_0$. Collecting the terms, the weighted sum becomes

```math
8 - 4c_0 - 3R_0 + T(v) + \chi(q) + 6\omega(r) \le 0, \qquad \chi(q) = 3\sin q - 6R_0\sin\tfrac q2 ,
```

with $T$ of Lemma D.8 (1). As $0 \le d - \frac{12}{25} \le r \le \frac\pi4$ and
$\cos x + \sin x$ is nondecreasing on $[0, \frac\pi4]$ (Lemma A.15 (3)),

```math
6\omega(r) \ge 3(\cos r + \sin r) \ge 3\left(\cos\left(d - \tfrac{12}{25}\right) + \sin\left(d - \tfrac{12}{25}\right)\right) .
```

So $\Pi(v, d) \le 0$, where

```math
\Pi(v, d) = 8 - 4c_0 - 3R_0 + T(v) + \chi(d + v) + 3\left(\cos\left(d - \tfrac{12}{25}\right) + \sin\left(d - \tfrac{12}{25}\right)\right) .
```

*Concavity.* $\chi$ is concave on $[0, \frac65]$: as
$\sin q = 2\sin\frac q2\cos\frac q2$,
$\chi''(q) = \sin\frac q2(\frac32R_0 - 6\cos\frac q2) \le 0$, because
$\cos\frac q2 \ge 1 - \frac12(\frac35)^2 = \frac{41}{50}$ and
$6\cdot\frac{41}{50} > \frac32\bar R$. The last term of $\Pi$ is a
nonnegative first harmonic of $d - \frac{12}{25} \in [0, \frac\pi2]$, concave by
Lemma A.11 (1). So $\Pi$ is concave in $d$ on $[\frac12, \frac\pi4]$, and
concave in $v$ on $[-\frac25, 0]$ and on $[0, \frac25]$ (Lemma D.8 (1)), and it
suffices to show $\Pi > 0$ at the six points with
$v \in \lbrace -\frac25, 0, \frac25\rbrace$ and
$d \in \lbrace \frac12, \frac\pi4\rbrace$.

*The six points.* There $q = d + v$ takes the values $\frac1{10}$, $\frac12$,
$\frac9{10}$, $\frac\pi4 - \frac25$, $\frac\pi4$ and $\frac\pi4 + \frac25$, and
Lemma D.9 gives: $\cos v \ge 0.921$ at $v = \pm\frac25$;
$\max(-\sin v, 0) \ge 0.389$ at $v = -\frac25$;
$\sqrt{25 - 24\sin v} \le 5.862$, $5$, $3.958$ at $v = -\frac25, 0, \frac25$;
$\sin q \ge 0.099$, $0.479$, $0.783$, $0.375$, $0.707$, $0.926$ at these six
values of $q$, in this order; and, from the brackets of $\cos q$,
$6\sin\frac q2 = \sqrt{18 - 18\cos q} \le 0.3$, $1.488$, $2.612$, $1.155$,
$2.297$, $3.355$. For the last term, at $d = \frac12$ and at $d = \frac\pi4$
(where $\frac\pi4 - \frac{12}{25} \ge \frac3{10}$ and $\cos x + \sin x$
increases on $[0, \frac\pi4]$),

```math
\begin{aligned}
\cos\tfrac1{50} + \sin\tfrac1{50} &\ge 1 - \tfrac1{5000} + \tfrac1{50} - \tfrac1{750000} > 1.019 , \\
\cos\left(\tfrac\pi4 - \tfrac{12}{25}\right) + \sin\left(\tfrac\pi4 - \tfrac{12}{25}\right) &\ge \cos\tfrac3{10} + \sin\tfrac3{10} \ge 1 - 0.045 + 0.3 - 0.0045 > \tfrac54 .
\end{aligned}
```

With $R_0 < \bar R$ and $c_0 < \bar c$ these give the lower bounds of Table D.7,
all positive, a contradiction (Figure D.11). $\square$

| $v$ | $d = \frac12$ | $d = \frac\pi4$ |
| :-: | :-: | :-: |
| $-\frac25$ | $0.67176$ | $0.74901$ |
| $0$ | $0.02128$ | $0.03220$ |
| $\frac25$ | $0.47881$ | $0.34618$ |

*Table D.7.* Lower bounds of $\Pi$ at the six points, rounded down.

*Lean:
[`Six.Wings.WestSide.SmallSouth.impossible`](../../SquaresInCircles/Six/Wings/WestSide.lean#L807),
[`Six.Wings.WestSide.SmallSouth.gap`](../../SquaresInCircles/Six/Wings/WestSide.lean#L552),
[`Six.Wings.WestSide.SmallSouth.westTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L549),
[`Six.Wings.WestSide.SmallSouth.chordTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L550),
[`Six.Wings.WestSide.SmallSouth.widthTerm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L551),
[`Six.Wings.WestSide.SmallSouth.chord_norm`](../../SquaresInCircles/Six/Wings/WestSide.lean#L654),
[`Six.Wings.WestSide.SmallSouth.chordTerm_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L559),
[`Six.Wings.WestSide.SmallSouth.widthTerm_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L589),
[`Six.Wings.WestSide.SmallSouth.westTerm_negative_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L609),
[`Six.Wings.WestSide.SmallSouth.westTerm_positive_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L617),
[`Six.Wings.WestSide.SmallSouth.gap_diagonal_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L625),
[`Six.Wings.WestSide.SmallSouth.gap_west_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L637),
[`Six.Wings.WestSide.SmallSouth.south_width_lower`](../../SquaresInCircles/Six/Wings/WestSide.lean#L794),
[`Six.Wings.WestSide.SmallSouth.width_endpoints`](../../SquaresInCircles/Six/Wings/WestSide.lean#L676),
[`Six.Wings.WestSide.SmallSouth.endpoint_bounds`](../../SquaresInCircles/Six/Wings/WestSide.lean#L703),
[`Six.Wings.WestSide.SmallSouth.reserve_positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L743),
[`Six.Wings.WestSide.SmallSouth.endpoint_positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L748),
[`Six.Wings.WestSide.SmallSouth.positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L774).*

![Left: the squares of a missing south wing with W and S on the sides of C; D is separated from S by the line of its lower right side, and orange arrows show the forces of the stress. Right: the rectangle of the angles v and d, shaded from white along v = 0 to blue at the sides, with a lower bound at each of its six marked points](figures/appendix-d/side-small.svg)

*Figure D.11.* Proposition D.11. Left: a missing south wing with $W$ and $S$ on
the sides of $C$, at $v = 0$, $s = 0.2$ and $d = 0.75$, in the smallest disk
that allows its separations (radius $1.739$): the separating lines of the
stress, with the weights $4$, $3$, $3$, in colour, the separations (D.1) and
(D.5), not used, in grey, and the forces of the stress. Right: the domain of
$(v, d)$, shaded by $\Pi$, with the bounds of Table D.7.

### Proposition D.12 (W on the west side: a missing south wing with s ≥ 12/25)

There are no wing data with a missing south wing that satisfy (D.3) and (D.4),
with $\lvert v\rvert \le \frac25$, $\frac{12}{25} \le s \le \frac23$ and
$\frac12 \le d \le \frac{11}{14}$.

*Proof.* *The stress.* Add (D.3), (D.4), (D.6) and (D.9) with the weights $4$,
$10$, $3$ and $3$. By Table D.1 the forces are

```math
F_W = (4\cos v,\ 4\sin v - 3), \quad F_D = (3\sin q,\ 3\cos q - 3), \quad F_S = (10 + 3\cos r,\ 3\sin r), \quad F_C = (4 - 10\sin s,\ 10\cos s) .
```

Here $q \in [\frac1{10}, \frac{11}{14} + \frac25] \subset [0, \frac65]$,
$r \in [-\frac16, \frac{107}{350}]$, $s \in [0, \frac\pi2]$ and
$\sin s \ge S_7(\frac{12}{25}) > \frac25$.

*The supports.* For $W$ the far vertex with
$\ell = 5 - \frac{12}5\sin v \ge \lvert F_W\rvert$, as
$(5 - \frac{12}5\sin v)^2 = 25 - 24\sin v + \frac{144}{25}\sin^2v$; it bounds
the work by $\bar R(5 - \frac{12}5\sin v) - \frac12(4\cos v + 3 - 4\sin v)$. For
$D$ the far vertex with $\ell = 6\sin\frac q2$, which bounds the work by
$6\bar R\sin\frac q2 - \frac12(3\sin q + 3 - 3\cos q)$. For $S$ the first cone:
$\cos r \ge 0$, so
$\lvert 3\sin r\rvert \le 3 \le \frac{31}{100}(10 + 3\cos r)$, and the work is
at most $\bar\rho(10 + 3\cos r)$. For $C$, $(4 - 10\sin s)c_x \le 0$ and
$10c_y\cos s \le 10\bar c\cos s$. The thresholds are
$\frac12 + \frac12(\cos v + \lvert\sin v\rvert)$,
$\frac12 + \frac12(\cos x + \sin x)$ for $x = s, q$, and
$\frac12 + \omega(r) \ge \frac12 + \frac12(\cos r + \sin r)$. Collecting the
terms, the weighted sum becomes $\Pi(v, s, d) \le 0$, where

```math
\Pi = 13 - 5\bar R - 10\bar\rho + (5 - 10\bar c)\cos s + 5\sin s + 4\cos v + \kappa\sin v + 3\sin q - 6\bar R\sin\tfrac q2 - \left(3\bar\rho - \tfrac32\right)\cos r + \tfrac32\sin r ,
```

with $\kappa = \frac{12}5\bar R$ for $v \ge 0$ and
$\kappa = \frac{12}5\bar R - 4$ for $v \le 0$, since
$2(\lvert\sin v\rvert - \sin v) + \frac{12}5\bar R\sin v = \kappa\sin v$.

*Monotonicity in $d$.* With $c = \cos\frac q2 \in [0, 1]$,
$3\cos q - 3\bar Rc = 6c^2 - 3 - 3\bar Rc \le 3 - 3\bar R$, as the difference is
$(c - 1)(6c + 6 - 3\bar R) \le 0$; and $\sin r \le \frac{107}{350}$,
$\cos r \le 1$. So

```math
\tfrac{\partial\Pi}{\partial d} = 3\cos q - 3\bar R\cos\tfrac q2 + \left(3\bar\rho - \tfrac32\right)\sin r + \tfrac32\cos r \le 3 - 3\bar R + \left(3\bar\rho - \tfrac32\right)\tfrac{107}{350} + \tfrac32 = -0.00375\ldots < 0 ,
```

and $\Pi(v, s, d) \ge \Pi(v, s, \frac{11}{14})$ (Lemma A.1).

*The angles $s$ and $v$.* Expanding $\cos r$ and $\sin r$, at fixed $v$ and $d$
the profile is a constant plus $A\cos s + B\sin s$ with
$A = 5 - 10\bar c - (3\bar\rho - \frac32)\cos d + \frac32\sin d$, at least
$5 - 10\bar c - 3\bar\rho > 0$, and
$B = 5 - (3\bar\rho - \frac32)\sin d - \frac32\cos d \ge 5 - 3\bar\rho > 0$; by
Lemma A.11 (2) it suffices to take $s = \frac{12}{25}$ and $s = \frac23$. At
$d = \frac{11}{14}$ the profile is concave in $v$ on $[-\frac25, 0]$ and on
$[0, \frac25]$, where $\kappa$ is constant:

```math
\tfrac{\partial^2\Pi}{\partial v^2} = -4\cos v - \kappa\sin v - 3\sin q + \tfrac32\bar R\sin\tfrac q2 \le -4\cdot\tfrac{23}{25} + \tfrac1{10} + \tfrac32\bar R < 0 ,
```

since $\kappa\sin v \ge -\frac1{10}$ (for $v \le 0$, $0 < \kappa < \frac1{10}$
and $\sin v \ge -\frac25$) and $\sin q \ge 0$. So $\Pi > 0$ on the domain once
it is positive at the six points $(v, s, \frac{11}{14})$ with
$v \in \lbrace -\frac25, 0, \frac25\rbrace$ and
$s \in \lbrace \frac{12}{25}, \frac23\rbrace$.

*The six points.* Replacing $\cos s$, $\cos v$ by $C_6$, $\sin s$, $\sin q$,
$\sin r$ by $S_7$ (here $r = \frac{11}{14} - s \ge \frac5{42} > 0$), $\sin v$ by
$S_7(v)$ for $v \ge 0$ and by $S_5(v)$ for $v < 0$, and $\sin\frac q2$ and
$\cos r$, which have negative coefficients, by $S_5$ and $C_4$, gives the lower
bounds of Table D.8, all positive, a contradiction (Figure D.12). $\square$

| $v$ | $s = \frac{12}{25}$ | $s = \frac23$ |
| :-: | :-: | :-: |
| $-\frac25$ | $0.72075$ | $0.76669$ |
| $0$ | $0.11351$ | $0.15945$ |
| $\frac25$ | $0.25197$ | $0.29791$ |

*Table D.8.* Lower bounds of $\Pi$ at $d = \frac{11}{14}$, by Taylor
polynomials, rounded down.

*Lean:
[`Six.Wings.WestSide.LargeSouth.impossible`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1163),
[`Six.Wings.WestSide.LargeSouth.totalThreshold`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1114),
[`Six.Wings.WestSide.LargeSouth.defect`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1118),
[`Six.Wings.WestSide.LargeSouth.westUpper`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1064),
[`Six.Wings.WestSide.LargeSouth.diagonalUpper`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1067),
[`Six.Wings.WestSide.LargeSouth.west_support`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1070),
[`Six.Wings.WestSide.LargeSouth.diagonal_support`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1078),
[`Six.Wings.WestSide.LargeSouth.south_support`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1092),
[`Six.Wings.WestSide.LargeSouth.south_trig`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1100),
[`Six.Wings.WestSide.LargeSouth.central_support`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1106),
[`Six.Wings.WestSide.LargeSouth.profile`](../../SquaresInCircles/Six/Wings/WestSide.lean#L864),
[`Six.Wings.WestSide.LargeSouth.coefficient`](../../SquaresInCircles/Six/Wings/WestSide.lean#L859),
[`Six.Wings.WestSide.LargeSouth.sine_term_lower`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1122),
[`Six.Wings.WestSide.LargeSouth.profile_le_defect`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1143),
[`Six.Wings.WestSide.LargeSouth.diagonal_derivative_nonpositive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L898),
[`Six.Wings.WestSide.LargeSouth.profile_at_upper_diagonal`](../../SquaresInCircles/Six/Wings/WestSide.lean#L926),
[`Six.Wings.WestSide.LargeSouth.extend_s`](../../SquaresInCircles/Six/Wings/WestSide.lean#L994),
[`Six.Wings.WestSide.LargeSouth.profile_v_concave`](../../SquaresInCircles/Six/Wings/WestSide.lean#L955),
[`Six.Wings.WestSide.LargeSouth.coefficient_sine_lower`](../../SquaresInCircles/Six/Wings/WestSide.lean#L881),
[`Six.Wings.WestSide.LargeSouth.endpointPolynomial`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1016),
[`Six.Wings.WestSide.LargeSouth.endpointPolynomial_le`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1022),
[`Six.Wings.WestSide.LargeSouth.corner`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1037),
[`Six.Wings.WestSide.LargeSouth.positive`](../../SquaresInCircles/Six/Wings/WestSide.lean#L1047).*

![Left: the squares of a missing south wing with W on the west side of C and S turned on its own axis; a long orange arrow shows the force on S, close to its own axis. Right: the rectangle of the angles v and s at d = 11/14, shaded from white along v = 0 to blue at v = −2/5, with a lower bound at each of its six marked points](figures/appendix-d/side-large.svg)

*Figure D.12.* Proposition D.12. Left: a missing south wing with $W$ on the west
side of $C$ and $S$ on its own axis, at $v = 0$, $s = 0.55$ and $d = 0.75$
(radius $1.704$): the stress with the weights $4$, $10$, $3$, $3$ and its
forces; the large force on $S$ lies close to its own axis, in the cone where its
work is at most $\bar\rho$ times its radial component. Right: the domain of
$(v, s)$ at $d = \frac{11}{14}$, where $\Pi$ is smallest in $d$, shaded by
$\Pi$, with the bounds of Table D.8.

## D.6 W on its own axis, S on the south side of C

Let $W$ be separated from $C$ along its own axis and $S$ along the south side of
$C$, and let the south wing be missing. With the weight $1$ on the separations
of $S$ from $C$ and from $D$, the force on $S$ is the sum of two unit vectors at
the angles $-s$ and $r = d - s$ in its frame, so it points in the direction of
their bisector, at the angle $\frac d2 - s$, and its length $2\cos\frac d2$
depends on $d$ only (Figure D.13). A second-order support makes the angle of
$S$ drop out of the stress altogether.

### Lemma D.13 (the force on S)

For real $s$ and $d$ let $U = \cos s + \cos(d - s)$, $V = \sin(d - s) - \sin s$
and $\xi(d) = \sin\frac d2 - 2\mu_+\cos\frac d2$.

1. If $\frac12 \le d \le \frac{11}{14}$, $s \le \frac25$ and
   $d - s \le \frac{11}{14}$, then $U \ge \frac{33}{20}$,
   $\lvert V\rvert \le \frac35U$ and

   ```math
   -\mu_+U + \tfrac12\left(\lvert\sin s\rvert + \sin(d - s)\right) - \tfrac3{25}V^2 \ge \xi(d) - \tfrac1{250} .
   ```

2. If $\frac{11}{14} \le d \le \frac{34}{35}$, $0 \le s \le \frac25$ and
   $0 \le d - s \le \frac47$, then $U \ge \frac74$,
   $\lvert V\rvert \le \frac{31}{100}U$ and
   $-\mu_+U + \frac12(\sin s + \sin(d - s)) \ge \xi(d)$.

*Proof.* Put $x = \frac d2 - s$ and $c = \cos\frac d2$. The sum formulas give

```math
U = 2c\cos x, \qquad V = 2c\sin x, \qquad \sin s + \sin(d - s) = 2\sin\tfrac d2\cos x .
```

(1) First, $s \ge d - \frac{11}{14} \ge -\frac27$, and
$s^2 + (d - s)^2 \le (\frac{11}{14})^2 + (\frac27)^2 = \frac{137}{196}$: for
$s \ge 0$ the left side is at most $d^2$, and for $s < 0$ each square is bounded
separately. So
$U \ge 2 - \frac12(s^2 + (d - s)^2) \ge 2 - \frac{137}{392} > \frac{33}{20}$.
Next, $x = (d - s) - \frac d2 \le \frac{11}{14} - \frac14 = \frac{15}{28}$ and
$x \ge \frac14 - \frac25$, so $\cos x \ge 1 - \frac12(\frac{15}{28})^2 > 0.8565$
and $\lvert\sin x\rvert \le S_5(\frac{15}{28}) < 0.5105 < \frac35\cdot 0.8565$;
as $c \ge 0$, $\lvert V\rvert \le \frac35U$.

For the inequality put $P = \frac{12}{25}c^2$ and $\xi = \xi(d)$. As
$\frac d2 \in [\frac14, \frac{11}{28}]$,
$c \ge C_6(\frac{11}{28}) > \frac{23}{25}$, so $P > \frac25$, and
$t = \sin\frac d2$ satisfies $0 \le t \le S_5(\frac{11}{28}) < 0.383$. Since
$c \ge \frac{23}{25}$,
$1 - c \le \frac{25}{48}(1 - c)(1 + c) = \frac{25}{48}t^2$, and therefore

```math
2P + \xi = \tfrac{24}{25}\left(1 - t^2\right) - 2\mu_+c + t \le \tfrac{24}{25} - 2\mu_+ + t - \left(\tfrac{24}{25} - \tfrac{25}{24}\mu_+\right)t^2 ,
```

which increases in $t$ on $[0, 0.383]$ (the vertex of the parabola lies beyond
$t = 1$) and equals $0.0701\ldots < \frac3{40}$ at $t = 0.383$. If
$\sin s \ge 0$, the left side of the inequality is

```math
-2\mu_+c\cos x + \sin\tfrac d2\cos x - \tfrac{12}{25}c^2\sin^2x = \xi\cos x - P\sin^2x ,
```

and with $y = \cos x - 1 \le 0$

```math
\xi\cos x - P\sin^2x - \xi = Py^2 + (2P + \xi)y \ge \tfrac25y^2 + \tfrac3{40}y = \tfrac25\left(y + \tfrac3{32}\right)^2 - \tfrac9{2560} > -\tfrac1{250} .
```

If $\sin s < 0$, then $-\frac27 \le s < 0$, and the left side is
$N(x) = -2\mu_+c\cos x + c\sin x - P\sin^2x$, because
$\frac12(\sin(d - s) - \sin s) = \frac12V$. On $[0, \frac\pi2]$

```math
N'(x) = c\left(\left(2\mu_+ - \tfrac{24}{25}c\cos x\right)\sin x + \cos x\right) \ge 0 ,
```

as $c\cos x \le 1 < \frac{25}{24}\cdot 2\mu_+$; and
$\frac d2 \le x \le \frac{11}{28} + \frac27 < \frac\pi2$. So
$N(x) \ge N(\frac d2) = \xi\cos\frac d2 - P\sin^2\frac d2$, which is the value
of the first case at $x = \frac d2$, and at least $\xi - \frac1{250}$.

(2) Here $s^2 + (d - s)^2 \le (\frac25)^2 + (\frac47)^2$, so
$U \ge 2 - \frac12(\frac4{25} + \frac{16}{49}) > \frac74$. Both $\sin s$ and
$\sin(d - s)$ lie in $[0, \sin\frac47]$, so
$\lvert V\rvert \le \sin\frac47 \le S_5(\frac47) < 0.5409$, and
$0.5409 < \frac{31}{100}\cdot\frac74$. Finally
$c \ge 1 - \frac12(\frac12)^2 = \frac78$, as $\frac d2 \le \frac12$, so
$\xi \le 1 - \frac74\mu_+ < 0$, and
$-\mu_+U + \frac12(\sin s + \sin(d - s)) = \xi\cos x \ge \xi$. $\square$

*Lean:
[`Six.Wings.SouthSide.southRadial`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L34),
[`Six.Wings.SouthSide.southTransverse`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L35),
[`Six.Wings.SouthSide.south_half_angle`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L37),
[`Six.Wings.SouthSide.square_sum_bound`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L52),
[`Six.Wings.SouthSide.half_angle_ratio`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L68),
[`Six.Wings.SouthSide.south_force_cone`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L86),
[`Six.Wings.SouthSide.south_force_axial`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L110),
[`Six.Wings.SouthSide.halfQuadratic`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L137),
[`Six.Wings.SouthSide.halfLinear`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L138),
[`Six.Wings.SouthSide.southContribution`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L140),
[`Six.Wings.SouthSide.positiveExpression`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L144),
[`Six.Wings.SouthSide.negativeExpression`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L147),
[`Six.Wings.SouthSide.half_trig_bounds`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L151),
[`Six.Wings.SouthSide.half_quadratic_lower`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L158),
[`Six.Wings.SouthSide.half_coefficient_upper`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L169),
[`Six.Wings.SouthSide.positive_expression_lower`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L181),
[`Six.Wings.SouthSide.negative_expression_monotone`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L200),
[`Six.Wings.SouthSide.contribution_of_nonnegative`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L230),
[`Six.Wings.SouthSide.contribution_of_nonpositive`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L244),
[`Six.Wings.SouthSide.south_angle_lower`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L257),
[`Six.Wings.SouthSide.south_angle_lower_high`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L283).*

![Two panels. Left: in the frame of S, for s = 0.2 and d = 0.75, a black unit arrow of (D.5) at the angle s below the first axis, a purple unit arrow of (D.9) at the angle r above it, and their sum (U, V), of length 2 cos(d/2), in orange along the bisector, with the dashed parallelogram. Right: the plane of (U, V) with the part U at least 33/20 and V at most 3U/5 of the third cone shaded green, and the dashed line V = 0.31 U; the forces of part (1) fill a blue crescent inside the green part that nearly touches its corner, and those of part (2) a small orange region below the dashed line](figures/appendix-d/south-force.svg)

*Figure D.13.* Lemma D.13. Left: the force on $S$ for $s = 0.2$ and
$d = 0.75$, the sum of the unit forces of (D.5) and (D.9), at the angles $-s$
and $r = d - s$. Right: all the forces $(U, V)$ of (1), for
$\frac12 \le d \le \frac{11}{14}$, lie in the third cone of (K)
($U \ge \frac{33}{20}$, $V \le \frac35U$, green; the edge $V = -\frac35U$ lies
below the picture), and those of (2), for
$\frac{11}{14} \le d \le \frac{34}{35}$, in the first cone
($\lvert V\rvert \le \frac{31}{100}U$, below the dashed line).

### Proposition D.14 (W on its own axis, S on the south side: a missing south wing)

There are no wing data with a missing south wing that satisfy (D.2) and (D.5),
with $0 \le v \le \frac23$, $\lvert s\rvert \le \frac25$,
$\frac12 \le d \le \frac{34}{35}$ and $r \le \frac\pi4$, and, if
$d > \frac{11}{14}$, also $s \ge 0$ and $r \le \frac47$.

*Proof.* *The stress.* Add (D.2), (D.5), (D.1), (D.6) and (D.9) with the weights
$\frac{41}{20}$, $1$, $\frac38$, $1$ and $1$. By Table D.1 the forces are

```math
F_W = \left(\tfrac{41}{20}, -1\right), \quad F_D = \left(\tfrac38 + \sin q, \cos q - 1\right), \quad F_S = (U, V), \quad F_C = \left(\tfrac{41}{20}\cos v + \tfrac38\cos d,\ 1 - \tfrac{41}{20}\sin v + \tfrac38\sin d\right),
```

with $U$ and $V$ as in Lemma D.13. Here
$q \in [\frac12, \frac{34}{35} + \frac23] \subset [\frac12, \frac53]$ and
$r \in [\frac1{10}, \frac\pi4]$. The thresholds are
$\frac12 + \frac12(\cos x + \sin x)$ for $x = v, d, r$,
$\frac12 + \frac12(\cos s + \lvert\sin s\rvert)$, and
$\frac12 + \omega(q) \ge \frac12 + \frac12(\cos q + \sin q)$.

*The supports.* For $W$ the far vertex with $\ell = 2.281$, as
$\sqrt{1 + (\frac{41}{20})^2} = \sqrt{5.2025} < 2.281$; for $D$ the chord (Ch)
with $z = \frac38$; for $S$ the third cone (K) with $k = \frac3{25}$ if
$d \le \frac{11}{14}$, and the first cone, $k = 0$, if $d > \frac{11}{14}$, by
Lemma D.13 (the work is at most $\bar\rho U + kV^2$); for $C$ a face of the box
(B), as the first component of $F_C$ is nonnegative. Collecting the terms as in
§D.2, with $\bar\rho - \frac12 = \mu_+$, the weighted sum becomes

```math
P_y(v, d) + \left(\omega(q) - \tfrac12(\cos q + \sin q)\right) + \left(-\mu_+U + \tfrac12\left(\lvert\sin s\rvert + \sin r\right) - kV^2 - \xi(d)\right) \le 0 ,
```

where $L = \bar R(2 + \frac{(3/8)^2}4)$, $M = \frac38\bar R$,
$K_0 = \frac{41}{20} + \frac38 + \frac52 - 2.281\bar R$ and

```math
P_y(v, d) = K_0 - y + \tfrac{41}{20}\left(\mu_-\cos v + \left(\tfrac12 + y\right)\sin v\right) + \tfrac38\left(\mu_-\cos d + \left(\tfrac12 - y\right)\sin d\right) + H_{L, M}(q) + \xi(d) .
```

The first bracket is nonnegative, and by Lemma D.13 the second is at least
$-\frac1{250}$ if $d \le \frac{11}{14}$, and at least $0$ if
$d > \frac{11}{14}$, where $s \ge 0$ and $r \le \frac47$. So
$P_y(v, d) \le \frac1{250}$ for $d \le \frac{11}{14}$ and $P_y(v, d) \le 0$ for
$d > \frac{11}{14}$: the angle of $S$ is gone.

*Concavity.* As $L \le L_*$ and $M \le M_*$, Lemma D.4 (1) and (2) give
$H''_{L, M}(q) \le -\frac3{40}$ on $[\frac12, \frac53]$. In $v$, on
$[0, \frac23]$,

```math
\partial^2_vP_y = -\tfrac{41}{20}\left(\mu_-\cos v + \left(\tfrac12 + y\right)\sin v\right) + H''_{L, M}(q) < 0 .
```

In $d$, with $\xi''(d) = \frac{\mu_+}2\cos\frac d2 - \frac14\sin\frac d2$,

```math
\partial^2_dP_y = -\tfrac38\left(\mu_-\cos d + \left(\tfrac12 - y\right)\sin d\right) + H''_{L, M}(q) + \xi''(d) \le -\tfrac38\cdot\tfrac43\mu_- - \tfrac3{40} + \tfrac{\mu_+}2 - \tfrac14\left(\tfrac14 - \tfrac1{384}\right) < -0.024 ,
```

on $[\frac12, \frac{34}{35}]$: there $\frac12 - y \ge \mu_-$, $\sin d \ge 0$,
$\sin\frac d2 \ge \sin\frac14 \ge \frac14 - \frac1{384}$, and
$\cos d + \sin d \ge \frac43$ by Lemma A.11 (2), as
$\cos\frac12 + \sin\frac12 \ge \frac78 + \frac{23}{48}$, and
$C_6(\frac{34}{35}) + S_7(\frac{34}{35}) = 1.3897\ldots$ bounds
$\cos\frac{34}{35} + \sin\frac{34}{35}$ from below.

*The six points.* At $v \in \lbrace 0, \frac23\rbrace$ and
$d \in \lbrace \frac12, \frac{11}{14}, \frac{34}{35}\rbrace$ we replace
$\cos v$, $\cos d$ by $C_6$, $\sin v$, $\sin d$, $\sin q$, $\sin\frac d2$ by
$S_7$, and $\sin\frac q2$, $\cos\frac q2$, $\cos\frac d2$, which have negative
coefficients, by $S_5$, $C_4$, $C_4$. Table D.9 lists the resulting lower
bounds: they exceed $\frac1{100}$ at $d = \frac12$ and $d = \frac{11}{14}$, and
$0$ at $d = \frac{34}{35}$. By concavity in $v$ (Lemma A.10 (2)) the same holds
for every $v \in [0, \frac23]$ at these three values of $d$, and then by
concavity in $d$, $P_y > \frac1{100} > \frac1{250}$ on
$[0, \frac23] \times [\frac12, \frac{11}{14}]$ and $P_y > 0$ on
$[0, \frac23] \times [\frac{11}{14}, \frac{34}{35}]$, a contradiction
(Figure D.14). $\square$

| $y$ | $v$ | $d = \frac12$ | $d = \frac{11}{14}$ | $d = \frac{34}{35}$ |
| :-: | :-: | :-: | :-: | :-: |
| $0$ | $0$ | $0.15986$ | $0.15955$ | $0.14803$ |
| $0$ | $\frac23$ | $0.10606$ | $0.05399$ | $0.00480$ |
| $\bar c$ | $0$ | $0.02676$ | $0.01681$ | $0.00028$ |
| $\bar c$ | $\frac23$ | $0.11597$ | $0.05427$ | $0.00006$ |

*Table D.9.* Lower bounds of $P_y$ by Taylor polynomials, rounded down.

*Lean:
[`Six.Wings.SouthSide.impossible`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L513),
[`Six.Wings.SouthSide.forceX`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L477),
[`Six.Wings.SouthSide.forceY`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L478),
[`Six.Wings.SouthSide.defect`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L482),
[`Six.Wings.SouthSide.defect_sub_profile`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L491),
[`Six.Wings.SouthSide.profile`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L320),
[`Six.Wings.SouthSide.constantTerm`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L316),
[`Six.Wings.SouthSide.chordL`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L310),
[`Six.Wings.SouthSide.chordM`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L311),
[`Six.Wings.SouthSide.chord_second_upper`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L324),
[`Six.Wings.SouthSide.profile_west_concave`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L334),
[`Six.Wings.SouthSide.profile_diagonal_concave`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L357),
[`Six.Wings.SouthSide.lower`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L403),
[`Six.Wings.SouthSide.lower_le`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L409),
[`Six.Wings.SouthSide.corners`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L432),
[`Six.Wings.SouthSide.section_lower`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L440),
[`Six.Wings.SouthSide.positive`](../../SquaresInCircles/Six/Wings/SouthSide.lean#L458).*

The range $d \le \frac{34}{35}$ goes beyond $\frac\pi4$ for the sake of the
reflection: in §D.10 the same stress excludes a missing west wing with $W$ on
the west side of $C$ and $S$ on its own axis, whose reflection has
$\frac\pi4 \le d < \frac\pi2 - \frac35$.

![Left: the squares of a missing south wing with W turned on its own axis and S on the south side of C, the separating lines of the stress, two of them along sides of D, and orange arrows for the forces. Right: the rectangle of the angles v and d from 1/2 to 34/35, shaded green, lighter along the top edge, with a dashed line at d = 11/14 and two lower bounds at each of six marked points](figures/appendix-d/own-side.svg)

*Figure D.14.* Proposition D.14. Left: a missing south wing with $W$ on its own
axis and $S$ on the south side of $C$, at $v = 0.2$, $s = 0.1$ and $d = 0.75$
(radius $1.742$): the stress with the weights $\frac{41}{20}$, $1$, $\frac38$,
$1$, $1$ and its forces; the force on $S$ is the sum of two unit forces and
points along their bisector. Right: the domain of $(v, d)$, shaded by the
minimum of $P_y$ over the faces $y$, with the bounds of Table D.9 for $y = 0$
and $y = \bar c$; above the dashed line $d = \frac{11}{14}$ the work on $S$ is
bounded by the first cone.

## D.7 Own wings, S turned at least as far as W

Let $W$ and $S$ both be separated from $C$ along their own axes, and let the
south wing be missing. By Lemma D.2 (4) and (5), $v > 0$, $s > 0$ and
$v + s < \frac{24}{25}$. The two stresses of this section and the next differ by
the order of $v$ and $s$. Both use the *wing harmonic*

```math
\zeta(x) = \mu_-\cos x + \mu_+\sin x ,
```

which is what the separation of $W$ (or $S$) from $C$ along its own axis leaves
after its threshold and the corner of the box: the threshold
$\frac12 + \frac12(\cos v + \sin v)$ less $\bar c$ times the components
$(\cos v, -\sin v)$ of the force on $C$ is $\frac12 + \zeta(v)$.

### Proposition D.15 (own wings with v ≤ s: a missing south wing)

There are no wing data with a missing south wing that satisfy (D.2) and (D.4),
with $0 \le v \le s \le \frac23$, $v + s \le \frac{24}{25}$ and
$\frac12 \le d \le \frac\pi4$.

*Proof.* *The stress.* Add (D.2), (D.4), (D.6) and (D.9) with the weights
$1.82$, $1.59$, $1.09$ and $1$. By Table D.1 the forces are

```math
F_W = (1.82, -1.09), \quad F_D = (1.09\sin q,\ 1.09\cos q - 1), \quad F_S = (1.59 + \cos r,\ \sin r), \quad F_C = (1.82\cos v - 1.59\sin s,\ 1.59\cos s - 1.82\sin v) .
```

Here $v \le \frac{12}{25}$, as $2v \le v + s$;
$q \in [\frac12, \frac\pi4 + \frac{12}{25}]$; and $r \in [-\frac16, \frac\pi4]$,
so $\cos r \ge h > 0.707$. The thresholds are
$\frac12 + \frac12(\cos x + \sin x)$ for $x = v, s, q$, and
$\frac12 + \omega(r) \ge \frac12 + \frac12(\cos r + \sin r)$.

*The supports.* For $W$ the far vertex with $\ell = 2.122$, as
$1.82^2 + 1.09^2 = 4.5005 < 2.122^2$. For $D$, with $t = \sin\frac q2$ and
$\cos q = 1 - 2t^2$,
$\lvert F_D\rvert^2 = 1.09^2 + 1 - 2.18\cos q = 0.09^2 + 4.36t^2$, and

```math
(0.011 + 2.076t)^2 - \left(0.09^2 + 4.36t^2\right) = -0.007979 + 0.045672t - 0.050224t^2
```

is a concave quadratic, positive at $t = \frac6{25}$ and at $t = \frac35$ (about
$0.00009$ and $0.00134$), hence on $[\frac6{25}, \frac35]$, which contains $t$:
$\sin\frac q2 \ge S_7(\frac14) > \frac6{25}$ and
$\sin\frac q2 \le S_5(\frac12(\frac{11}{14} + \frac{12}{25})) < \frac35$. So the
far vertex with $\ell = 0.011 + 2.076\sin\frac q2$ bounds the work on $D$ by
$\bar R(0.011 + 2.076\sin\frac q2) - \frac12(1.09\sin q + 1 - 1.09\cos q)$. For
$S$ the first cone: $\lvert\sin r\rvert \le \sqrt{1 - 0.707^2} < 0.708$ and
$0.708 < \frac{31}{100}(1.59 + 0.707)$, so the work is at most
$\bar\rho(1.59 + \cos r)$. For $C$ the corner of the box: as
$\cos v, \cos s \ge 1 - \frac12(\frac23)^2 = \frac79$, $\sin s \le \frac23$ and
$\sin v \le \frac{12}{25}$, both components of $F_C$ are positive. Collecting
the terms, the weighted sum becomes $\Pi(v, s, d) \le 0$, where

```math
\Pi(v, s, d) = K_2 + 1.82\,\zeta(v) + 1.59\,\zeta(s) + 1.09\,H_{L, 0}(q) + J_1(r), \qquad J_1(r) = -\mu_+\cos r + \tfrac12\sin r ,
```

with $L = \frac{2.076}{1.09}\bar R = 3.2160\ldots \le L_*$ and
$K_2 = 4.705 - 2.133\bar R - 1.59\bar\rho = -0.6661676$.

*Monotonicity in $d$.* $\partial_d\Pi = 1.09H'_{L, 0}(d + v) + J_1'(d - s)$. By
Lemma D.4 (3), $H'_{L, 0}$ is nonincreasing on $[\frac12, \frac53]$, so
$H'_{L, 0}(d + v) \le H'_{L, 0}(d)$. On $[-\frac16, \frac45]$,
$J_1''(r) = \mu_+\cos r - \frac12\sin r \ge \frac{17}{25}\mu_+ - \frac25 > 0$,
so $J_1'(r) = \mu_+\sin r + \frac12\cos r$ is nondecreasing there and
$J_1'(d - s) \le J_1'(d)$. Hence, for $\frac12 \le d \le \frac{11}{14}$,
$\partial_d\Pi \le f(d) = 1.59\cos d + \mu_+\sin d - \kappa\cos\frac d2$ with
$\kappa = \frac{1.09}2L = 1.038\bar R = 1.7527668$. With $\cos d \le C_4(d)$,
$\sin d \le S_5(d)$, $\cos\frac d2 \ge 1 - \frac{d^2}8$,
$d^4 \le (\frac{11}{14})^2d^2$, $d^5 \le (\frac{11}{14})^2d^3$ and
$d^3 \ge \frac12d^2$,

```math
f(d) \le 1.59 - \kappa + \mu_+d + c_2d^2, \qquad c_2 = -0.795 + \tfrac\kappa8 + \tfrac{1.59}{24}\left(\tfrac{11}{14}\right)^2 - \tfrac{\mu_+}{12}\left(1 - \tfrac1{20}\left(\tfrac{11}{14}\right)^2\right) = -0.58449\ldots ,
```

and the right side is at most

```math
1.59 - \kappa + \frac{\mu_+^2}{4\lvert c_2\rvert} = -0.16276\ldots + 0.16062\ldots < 0 .
```

So $\Pi(v, s, d) \ge \Pi(v, s, \frac{11}{14})$ (Figure D.15).

![Graph over d from 1/2 to 11/14: the bound f(d) of the derivative of the profile in d, in blue, falls from about -0.009 to about -0.062; above it the dashed orange parabola that bounds it, whose highest point, about -0.0021, is marked; both stay below the dashed zero line](figures/appendix-d/monotone.svg)

*Figure D.15.* The monotonicity in $d$ in the proof of Proposition D.15: the
bound $f(d)$ of $\partial_d\Pi$ (blue) and the parabola
$1.59 - \kappa + \mu_+d + c_2d^2$ above it (orange); the top of the parabola,
$1.59 - \kappa + \mu_+^2/4\lvert c_2\rvert = -0.0021\ldots$, is still
negative.

*The angle $s$.* At $d = \frac{11}{14}$, expanding $J_1(\frac{11}{14} - s)$,
$\Pi$ is a constant plus $A\cos s + B\sin s$ with

```math
A = 1.59\mu_- - \mu_+\cos\tfrac{11}{14} + \tfrac12\sin\tfrac{11}{14} \ge 1.59\mu_- - \mu_+ > 0, \qquad B = 1.59\mu_+ - \mu_+\sin\tfrac{11}{14} - \tfrac12\cos\tfrac{11}{14} \ge 1.59\mu_+ - \tfrac45\mu_+ - \tfrac38 > 0 ,
```

as $\sin\frac{11}{14} \le \frac{11}{14} < \frac45$ and
$\cos\frac{11}{14} \le C_4(\frac{11}{14}) < \frac34$. So at each $v$, by Lemma
A.11 (2), $\Pi > 0$ for $s$ between $v$ and the largest value
$\min(\frac23, \frac{24}{25} - v)$ once it is positive at both.

*The edges.* The domain of $(v, s)$ is the quadrilateral with the vertices
$(0, 0)$, $(0, \frac23)$, $(\frac{22}{75}, \frac23)$ and
$(\frac{12}{25}, \frac{12}{25})$, and we need positivity on its edges $s = v$,
$s = \frac23$ and $s = \frac{24}{25} - v$. Along each of them, at
$d = \frac{11}{14}$, $\Pi$ is a constant plus $P\cos v + Q\sin v$ plus
$1.09H_{L, 0}(\frac{11}{14} + v)$, with $P, Q \ge 0$; such a function is concave
in $v$, as its second derivative is
$-(P\cos v + Q\sin v) + 1.09H''_{L, 0}(\frac{11}{14} + v) \le 0$ (Lemma D.4
(3)). Expanding the terms in $s$ and $r$: on $s = v$,
$P \ge 3.41\mu_- - \mu_+ > 0$ and $Q \ge 3.41\mu_+ - \mu_+ - \frac12 > 0$; on
$s = \frac23$, $P = 1.82\mu_-$ and $Q = 1.82\mu_+$; on $s = \frac{24}{25} - v$,
with $k = \frac{11}{14} - \frac{24}{25} \in [-\frac15, 0]$,

```math
\begin{aligned}
P &= 1.82\mu_- + 1.59\left(\mu_-\cos\tfrac{24}{25} + \mu_+\sin\tfrac{24}{25}\right) - \mu_+\cos k + \tfrac12\sin k \ge 1.82\mu_- + 1.59\cdot\tfrac12\mu_- - \mu_+ - \tfrac1{10} > 0 , \\
Q &= 1.82\mu_+ + 1.59\left(\mu_-\sin\tfrac{24}{25} - \mu_+\cos\tfrac{24}{25}\right) + \mu_+\sin k + \tfrac12\cos k \ge 1.82\mu_+ - 1.59\mu_+ - \tfrac15\mu_+ > 0 ,
\end{aligned}
```

using $\cos\frac{24}{25} \ge 1 - \frac12(\frac{24}{25})^2 > \frac12$ and
$\sin k \ge k \ge -\frac15$. So $\Pi > 0$ on the domain at $d = \frac{11}{14}$,
and hence for $\frac12 \le d \le \frac\pi4$, once it is positive at the four
vertices.

*The four vertices.* Replacing $\cos v$, $\cos s$ by $C_6$, $\sin v$, $\sin s$,
$\sin q$, $\sin r$ by $S_7$, and $\sin\frac q2$ and $\cos r$, which have
negative coefficients, by $S_5$ and $C_4$, gives at $d = \frac{11}{14}$ the
lower bounds of Table D.10, all positive, a contradiction (Figure D.16).
$\square$

| $(v, s)$ | $(0, 0)$ | $(0, \frac23)$ | $(\frac{22}{75}, \frac23)$ | $(\frac{12}{25}, \frac{12}{25})$ |
| --- | :-: | :-: | :-: | :-: |
| bound of $\Pi(v, s, \frac{11}{14})$ | $0.00335$ | $0.00470$ | $0.02806$ | $0.00224$ |

*Table D.10.* Lower bounds of $\Pi$ at the vertices, by Taylor polynomials,
rounded down.

*Lean:
[`Six.Wings.SouthTurned.impossible`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L310),
[`Six.Wings.SouthTurned.chordL`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L31),
[`Six.Wings.SouthTurned.chordL_le`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L33),
[`Six.Wings.SouthTurned.half_sine_bounds`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L37),
[`Six.Wings.SouthTurned.diagonal_support`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L47),
[`Six.Wings.SouthTurned.south`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L69),
[`Six.Wings.SouthTurned.southFirst`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L70),
[`Six.Wings.SouthTurned.south_hasDerivAt`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L72),
[`Six.Wings.SouthTurned.southFirst_hasDerivAt`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L76),
[`Six.Wings.SouthTurned.constantTerm`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L85),
[`Six.Wings.SouthTurned.profile`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L88),
[`Six.Wings.SouthTurned.chordFirst_antitone`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L91),
[`Six.Wings.SouthTurned.diagonal_comparison_negative`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L104),
[`Six.Wings.SouthTurned.profile_at_upper_diagonal`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L118),
[`Six.Wings.SouthTurned.edge_concave`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L163),
[`Six.Wings.SouthTurned.upper_trig`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L182),
[`Six.Wings.SouthTurned.s_identity`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L192),
[`Six.Wings.SouthTurned.s_coefficients`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L200),
[`Six.Wings.SouthTurned.lower`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L208),
[`Six.Wings.SouthTurned.lower_le`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L213),
[`Six.Wings.SouthTurned.four_vertices`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L225),
[`Six.Wings.SouthTurned.positive`](../../SquaresInCircles/Six/Wings/SouthTurned.lean#L235).*

![Left: the squares of a missing south wing with W and S turned on their own axes, S turned further than W, with the separating lines and the forces of the stress. Right: a quadrilateral of the angles v and s with the vertices (0, 0), (0, 2/3), (22/75, 2/3) and (12/25, 12/25), shaded green, lighter near its vertices, with a lower bound at each vertex](figures/appendix-d/south-turned.svg)

*Figure D.16.* Proposition D.15. Left: a missing south wing with $W$ and $S$ on
their own axes, at $v = 0.15$, $s = 0.35$ and $d = 0.75$ (radius $1.717$): the
stress with the weights $1.82$, $1.59$, $1.09$, $1$ and its forces. Right: the
quadrilateral of $(v, s)$ at $d = \frac{11}{14}$, shaded by $\Pi$, with the
bounds of Table D.10 at its vertices.

## D.8 Own wings, W turned at least as far as S

When $s \le v$ the stress puts a smaller weight on the separation of $S$ from
$C$, and the force on $S$ lies only in the second cone of (K); the quadratic
term of that support brings the *transverse term* $J$ below.

### Lemma D.16 (three bounds in one variable)

Let $J(r) = -\mu_+\cos r + \frac12\sin r - \frac1{12}\sin^2r$.

1. $\zeta(x) \ge \mu_- + \frac49x$ for $0 \le x \le \frac{12}{25}$.
2. $J''(r) \le \mu_+ - \frac16 - \frac r3$ for $0 \le r \le 1$.
3. $\cos d + \sin d \ge \frac43$ for $\frac12 \le d \le \frac{163}{175}$.

*Proof.* (1) The function $\zeta(x) - \mu_- - \frac49x$ is concave on
$[0, \frac{12}{25}]$, as $\zeta'' = -\zeta \le 0$ there (Lemma A.11 (1)); it
vanishes at $0$, and at $\frac{12}{25}$ it is at least

```math
\mu_-C_6\left(\tfrac{12}{25}\right) + \mu_+S_7\left(\tfrac{12}{25}\right) - \mu_- - \tfrac49\cdot\tfrac{12}{25} = 0.6264\ldots - 0.6005\ldots > 0 .
```

By concavity it is nonnegative in between.

(2) As $\sin^2r = \frac12(1 - \cos 2r)$,
$J(r) = -\mu_+\cos r + \frac12\sin r - \frac1{24} + \frac1{24}\cos 2r$, so

```math
J'' = \mu_+\cos r - \tfrac12\sin r - \tfrac16\cos 2r, \qquad J''' = -\mu_+\sin r - \tfrac12\cos r + \tfrac13\sin 2r .
```

On $[0, 1]$ put $x = \sin r \in [0, 1]$ and $c = \cos r \ge 0$, so that
$J''' = -\mu_+x - c(\frac12 - \frac23x)$. If $x \le \frac34$, then
$c \ge 1 - x$, as $c^2 = (1 - x)(1 + x) \ge (1 - x)^2$, and

```math
J''' \le -\mu_+x - (1 - x)\left(\tfrac12 - \tfrac23x\right) = -\tfrac13 - \tfrac23\left(x - \tfrac12\right)^2 - \left(\mu_+ - \tfrac12\right)x \le -\tfrac13 .
```

If $x \ge \frac34$, then $c^2 \le \frac7{16}$, so $c \le \frac23$ and
$c(\frac23x - \frac12) \le \frac c6 \le \frac19$, and
$J''' \le -\frac34\mu_+ + \frac19 < -\frac13$. So $J'' + \frac r3$ is
nonincreasing on $[0, 1]$, and
$J''(r) \le J''(0) - \frac r3 = \mu_+ - \frac16 - \frac r3$.

(3) Lemma A.11 (2) with $A = B = 1$ and $K = -\frac43$: at $\frac12$,
$\cos\frac12 + \sin\frac12 \ge \frac78 + \frac{23}{48} > \frac43$, and at
$x = \frac{163}{175}$,
$\cos x + \sin x \ge 1 - \frac{x^2}2 + x - \frac{x^3}6 = 1.3629\ldots > \frac43$.
$\square$

*Lean:
[`Six.Wings.WestTurned.wing_affine_lower`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L99),
[`Six.Wings.WestTurned.transverse`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L30),
[`Six.Wings.WestTurned.transverse_eq`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L35),
[`Six.Wings.WestTurned.transverseFirst`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L31),
[`Six.Wings.WestTurned.transverseSecond`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L32),
[`Six.Wings.WestTurned.transverseThird`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L33),
[`Six.Wings.WestTurned.transverse_hasDerivAt`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L41),
[`Six.Wings.WestTurned.transverseFirst_hasDerivAt`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L47),
[`Six.Wings.WestTurned.transverseSecond_hasDerivAt`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L54),
[`Six.Wings.WestTurned.transverse_third_upper`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L64),
[`Six.Wings.WestTurned.transverse_second_upper`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L81),
[`Six.Wings.WestTurned.diagonal_trig_lower`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L120).*

![Three graphs. (1) Over x from 0 to 12/25, the wing harmonic, in blue, concave and above the dashed orange line mu- + 4x/9, which it meets at 0. (2) Over r from 0 to 1, the second derivative of J, in blue, falling from about 0.45 to about -0.02, below the dashed orange line mu+ - 1/6 - r/3, which it meets at 0. (3) Over d from 1/2 to 163/175, cos d + sin d, in blue, a concave arch with its top at pi/4, above the dashed orange level 4/3](figures/appendix-d/bounds.svg)

*Figure D.17.* The three bounds of Lemma D.16 (dashed): (1) a line through
$\zeta(0)$ under the concave wing harmonic $\zeta$; (2) the line through
$J''(0)$ of slope $-\frac13$, above $J''$ as $J''' \le -\frac13$; (3) the
level $\frac43$ under $\cos d + \sin d$.

### Proposition D.17 (own wings with s ≤ v: a missing south wing)

There are no wing data with a missing south wing that satisfy (D.2) and (D.4),
with $0 \le s \le v \le \frac23$, $v + s \le \frac{24}{25}$,
$\frac12 \le d \le \frac{163}{175}$ and $r \le \frac\pi4$.

*Proof.* *The stress.* Add (D.2), (D.4), (D.1), (D.6) and (D.9) with the weights
$\frac94$, $\frac34$, $\frac9{20}$, $1$ and $1$. By Table D.1 the forces are

```math
F_W = \left(\tfrac94, -1\right), \quad F_D = \left(\tfrac9{20} + \sin q, \cos q - 1\right), \quad F_S = \left(\tfrac34 + \cos r, \sin r\right),
```

and $F_C = (X, Y)$ with $X = \frac94\cos v - \frac34\sin s + \frac9{20}\cos d$
and $Y = \frac34\cos s - \frac94\sin v + \frac9{20}\sin d$. Here
$s \le \frac{12}{25}$,
$q \in [\frac12, \frac{163}{175} + \frac23] \subset [\frac12, \frac53]$ and
$r \in [\frac1{50}, \frac\pi4]$. The thresholds are
$\frac12 + \frac12(\cos x + \sin x)$ for $x = v, s, d, r$, and
$\frac12 + \omega(q) \ge \frac12 + \frac12(\cos q + \sin q)$.

*The supports.* For $W$ the far vertex with $\ell = 2.4623$, as
$\lvert F_W\rvert = \frac{\sqrt{97}}4 < 2.4623$; for $D$ the chord (Ch) with
$z = \frac9{20}$, so $L = L_*$ and $M = M_*$; for $S$ the second cone of (K):
$\cos r \ge \frac7{10}$ (Lemma A.15 (3)), so
$U = \frac34 + \cos r \ge \frac{29}{20} > \frac75$, and $\sin r \le \cos r$,
$\sin r \le \sqrt{1 - 0.49} < \frac34$ give $2\sin r \le U$; so the work is at
most $\bar\rho(\frac34 + \cos r) + \frac1{12}\sin^2r$. For $C$ a face of the
box, as $X \ge \frac94\cdot\frac79 - \frac34\cdot\frac{12}{25} > 0$. Collecting
the terms, the weighted sum becomes $\Pi_y(v, s, d) \le 0$ for $y = 0$ or
$y = \bar c$, where

```math
\Pi_y = K_3 + \tfrac9{20}\left(\mu_-\cos d + \left(\tfrac12 - y\right)\sin d\right) + \tfrac94\left(\mu_-\cos v + \left(\tfrac12 + y\right)\sin v\right) + H_{L_*, M_*}(q) + \tfrac34\left(\left(\tfrac12 - y\right)\cos s + \mu_+\sin s\right) + J(r) ,
```

with $J$ of Lemma D.16 and

```math
K_3 = \tfrac12\left(\tfrac94 + \tfrac34 + \tfrac9{20} + 2\right) + \tfrac12\left(\tfrac94 + 1\right) + \tfrac12\left(\tfrac9{20} + 1\right) - 2.4623\bar R - \tfrac34\bar\rho = 0.08254522 .
```

*Concavity.* $\Pi_y$ is concave in each angle on the domain.

- In $v$ on $[0, \frac23]$, by Lemma D.4 (3),

  ```math
  \partial^2_v\Pi_y = -\tfrac94\left(\mu_-\cos v + \left(\tfrac12 + y\right)\sin v\right) + H''_{L_*, M_*}(q) < 0 .
  ```

- In $s$ on $[0, \frac{12}{25}]$: with $\frac12 - y \ge \mu_-$ and Lemma D.16
  (1) and (2), and $r \in [0, 1]$, $d \ge \frac12$,

  ```math
  \partial^2_s\Pi_y = -\tfrac34\left(\left(\tfrac12 - y\right)\cos s + \mu_+\sin s\right) + J''(d - s) \le -\tfrac34\left(\mu_- + \tfrac49s\right) + \mu_+ - \tfrac16 - \tfrac{d - s}3 \le -\tfrac34\mu_- + \mu_+ - \tfrac13 < -0.0108 .
  ```

- In $d$ on $[\frac12, \frac{163}{175}]$: in

  ```math
  \partial^2_d\Pi_y = -\tfrac9{20}\left(\mu_-\cos d + \left(\tfrac12 - y\right)\sin d\right) + H''_{L_*, M_*}(q) + J''(r)
  ```

  the first term is at most
  $-\frac9{20}\mu_-(\cos d + \sin d) \le -\frac35\mu_-$ (Lemma D.16 (3)). If
  $q \le \frac32$, Lemma D.4 (1) and Lemma D.16 (2) bound the other two by
  $\frac3{40} - \frac3{10}\min(q, 1) + \mu_+ - \frac16 - \frac r3$, and
  $\min(q, 1) + r \ge 1$ (if $q \le 1$, then $q + r = 2d + v - s \ge 2d \ge 1$);
  if $q > \frac32$, then $H''_{L_*, M_*}(q) \le -\frac{19}{100}$ (Lemma D.4
  (2)), and $r = d - s > (\frac32 - v) - (\frac{24}{25} - v) = \frac{27}{50}$.
  So, in the two cases,

  ```math
  \partial^2_d\Pi_y \le -\tfrac35\mu_- + \tfrac3{40} + \mu_+ - \tfrac16 - \tfrac3{10} < -0.011 , \qquad \partial^2_d\Pi_y \le -\tfrac35\mu_- - \tfrac{19}{100} + \mu_+ - \tfrac16 - \tfrac9{50} < -0.15 .
  ```

*From the vertices to the domain.* At a fixed $d$ the domain of $(v, s)$ is the
quadrilateral with the vertices $(0, 0)$, $(\frac23, 0)$,
$(\frac23, \frac{22}{75})$ and $(\frac{12}{25}, \frac{12}{25})$. Along its edges
$v = s$, $v = \frac23$ and $v = \frac{24}{25} - s$, $\Pi_y$ is a sum of concave
functions of $s$ (Lemma A.10 (3)), so it is positive on the edges once it is
positive at the vertices; and at each $s$ it is concave in $v$, so it is
positive on the segment from $v = s$ to the far edge. Positivity at
$d = \frac12$ and $d = \frac{163}{175}$ then gives it for all $d$, by concavity
in $d$.

*The vertices.* We replace $\cos d$, $\cos v$, $\cos s$ by $C_6$, $\sin d$,
$\sin v$, $\sin s$, $\sin q$, $\sin r$ by $S_7$, $\sin\frac q2$, $\cos\frac q2$,
$\cos r$ (negative coefficients) by $S_5$, $C_4$, $C_4$, and write
$-\frac1{12}\sin^2r = -\frac1{24} + \frac1{24}\cos 2r$ with $\cos 2r$ replaced
by $C_6(2r)$. Table D.11 lists the resulting lower bounds, all positive, a
contradiction (Figure D.18). $\square$

| $y$ | $d$ | $(0, 0)$ | $(\frac23, 0)$ | $(\frac23, \frac{22}{75})$ | $(\frac{12}{25}, \frac{12}{25})$ |
| :-: | :-: | :-: | :-: | :-: | :-: |
| $0$ | $\frac12$ | $0.15871$ | $0.15924$ | $0.09268$ | $0.10805$ |
| $0$ | $\frac{163}{175}$ | $0.16298$ | $0.09099$ | $0.00262$ | $0.01784$ |
| $\bar c$ | $\frac12$ | $0.04975$ | $0.20725$ | $0.14431$ | $0.12587$ |
| $\bar c$ | $\frac{163}{175}$ | $0.03763$ | $0.12261$ | $0.03785$ | $0.01927$ |

*Table D.11.* Lower bounds of $\Pi_y$ at the vertices $(v, s)$, by Taylor
polynomials, rounded down.

*Lean:
[`Six.Wings.WestTurned.impossible`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L364),
[`Six.Wings.WestTurned.westLength`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L134),
[`Six.Wings.WestTurned.constantTerm`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L139),
[`Six.Wings.WestTurned.westPart`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L143),
[`Six.Wings.WestTurned.southPart`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L144),
[`Six.Wings.WestTurned.profile`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L147),
[`Six.Wings.WestTurned.forceX`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L334),
[`Six.Wings.WestTurned.forceY`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L335),
[`Six.Wings.WestTurned.defect`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L339),
[`Six.Wings.WestTurned.profile_le_defect`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L348),
[`Six.Wings.WestTurned.west_concave`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L150),
[`Six.Wings.WestTurned.south_curvature_negative`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L167),
[`Six.Wings.WestTurned.south_concave`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L177),
[`Six.Wings.WestTurned.diagonal_concave`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L188),
[`Six.Wings.WestTurned.positive_of_vertices`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L233),
[`Six.Wings.WestTurned.lower`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L275),
[`Six.Wings.WestTurned.lower_le`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L282),
[`Six.Wings.WestTurned.positive`](../../SquaresInCircles/Six/Wings/WestTurned.lean#L311).*

The range $d \le \frac{163}{175}$ again serves the reflection: in §D.10 this
stress also excludes a missing west wing with $W$ and $S$ on their own axes and
$v < s$, whose reflection has $\frac\pi4 \le d < \frac\pi2 - \frac{16}{25}$.

![Left: the squares of a missing south wing with W and S turned on their own axes, W turned further than S, with the separating lines and the forces of the stress. Right: a quadrilateral of the angles v and s with the vertices (0, 0), (2/3, 0), (2/3, 22/75) and (12/25, 12/25), shaded green, with two lower bounds at each vertex](figures/appendix-d/west-turned.svg)

*Figure D.18.* Proposition D.17. Left: a missing south wing with $W$ and $S$ on
their own axes, at $v = 0.35$, $s = 0.15$ and $d = 0.75$ (radius $1.732$): the
stress with the weights $\frac94$, $\frac34$, $\frac9{20}$, $1$, $1$ and its
forces. Right: the quadrilateral of $(v, s)$, shaded by the minimum of $\Pi_y$
over the faces $y$ and the ends $d = \frac12$, $\frac{163}{175}$, with the
smaller bound of Table D.11 over the faces at each vertex, for $d = \frac12$ and
$d = \frac{163}{175}$.

## D.9 A missing west wing with W on its own axis

Let $W$ be separated from $C$ along its own axis and let the west wing be
missing. By Proposition D.7 the angles lie in the small domain

```math
\tfrac{16}{25} \le d \le \tfrac{11}{14}, \qquad \tfrac{53}{50} - d \le v \le \tfrac{31}{50} .
```

The two stresses of this section put the weight $\frac{41}{20}$ on the
separation (D.2) of $W$ from $C$, the weight $1$ on the separations (D.7) and
(D.8) of $D$ from $W$ and from $S$, and a weight $\gamma$ on the separation of
$S$ from $C$. By Table D.1 the forces on $W$ and $D$ are

```math
F_W = \left(\tfrac{41}{20} + \sin q, -\cos q\right), \qquad F_D = (\cos r, 1 - \sin r) .
```

As
$q \in [\frac{53}{50}, \frac{31}{50} + \frac{11}{14}] \subset [1, \frac\pi2]$,
the force on $W$ lies in the first cone (as in Proposition D.7), and the work on
$W$ is at most $\bar\rho(\frac{41}{20} + \sin q)$. The two separations of $D$
are both along secondary axes, of $D$ and of $S$, and
$\lvert F_D\rvert = \sqrt2(\cos\frac r2 - \sin\frac r2)$ for
$0 \le r \le \frac65$ (Lemma D.8 (2)). With $\sqrt2 < 1.415$ and
$\sigma = 1.415\bar R = 2.389369$, the far vertex bounds the work on $D$ by
$\sigma(\cos\frac r2 - \sin\frac r2) - \frac12(\cos r + 1 - \sin r)$. These
terms, with the thresholds of (D.2), (D.7) and (D.8) and the corner of the box
for the work on $C$ of the force $\frac{41}{20}(\cos v, -\sin v)$, form, up to
constants, the *base profile*

```math
B(v, s, d) = \tfrac{41}{20}\zeta(v) + g(v + d) + \psi(d - s), \qquad g(q) = \tfrac12\cos q - \mu_+\sin q, \qquad \psi(x) = \cos x - \sigma\cos\tfrac x2 + \sigma\sin\tfrac x2 ,
```

with the wing harmonic $\zeta$ of §D.7.

### Lemma D.18 (the base profile)

1. $\psi'(x) \ge \frac7{10}$ for $0 \le x \le \frac65$.
2. Let $-\frac25 \le s \le \frac{12}{25}$ and let $K$ be a number. If
   $K + B(v, s, d) > 0$ at the three points

   ```math
   (v, d) = \left(\tfrac{21}{50}, \tfrac{16}{25}\right), \quad \left(\tfrac{48}{175}, \tfrac{11}{14}\right), \quad \left(\tfrac{31}{50}, \tfrac{16}{25}\right) ,
   ```

   then $K + B(v, s, d) > 0$ whenever $\frac{16}{25} \le d \le \frac{11}{14}$
   and $\frac{53}{50} - d \le v \le \frac{31}{50}$.

*Proof.* (1) As $\sigma < 4$, $\psi$ is concave on $[0, \frac65]$
(Lemma D.8 (2)), so $\psi'$ is nonincreasing there, and

```math
\psi'(x) \ge \psi'\left(\tfrac65\right) = -\sin\tfrac65 + \tfrac\sigma2\left(\sin\tfrac35 + \cos\tfrac35\right) \ge -S_5\left(\tfrac65\right) + \tfrac\sigma2\left(S_7\left(\tfrac35\right) + C_6\left(\tfrac35\right)\right) = 0.7278\ldots .
```

(2) Here $d - s \in [\frac4{25}, \frac{11}{14} + \frac25] \subset [0, \frac65]$,
and the argument runs along the wall, the top and the segments between them
(Figure D.19). *The wall.* Along $v = \frac{53}{50} - d$ the term
$g(v + d) = g(\frac{53}{50})$ is constant, and $B$ is concave in $d$: $\zeta$ is
concave on $[0, \frac23]$, being a nonnegative first harmonic there
(Lemma A.11 (1)), and $\psi$ by Lemma D.8 (2). So $K + B > 0$ along the
wall, from its ends $(\frac{21}{50}, \frac{16}{25})$ and
$(\frac{48}{175}, \frac{11}{14})$. *The top.* Along $v = \frac{31}{50}$, $B$ is
nondecreasing in $d$: as $\frac{31}{50} + d$ lies between $\frac{63}{50}$ and
$\frac{31}{50} + \frac{11}{14} < \frac\pi2$, we have
$\cos(\frac{31}{50} + d) \le C_4(\frac{63}{50}) < \frac8{25}$, and by (1)

```math
\partial_dB = -\tfrac12\sin\left(\tfrac{31}{50} + d\right) - \mu_+\cos\left(\tfrac{31}{50} + d\right) + \psi'(d - s) \ge -\tfrac12 - \tfrac8{25}\mu_+ + \tfrac7{10} > 0 .
```

So $K + B > 0$ along the top, from $(\frac{31}{50}, \frac{16}{25})$. *The
segments.* At a fixed $d$, $\frac{41}{20}\zeta(v) + g(v + d)$ is the first
harmonic

```math
\left(\tfrac{41}{20}\mu_- + \tfrac12\cos d - \mu_+\sin d\right)\cos v + \left(\tfrac{41}{20}\mu_+ - \tfrac12\sin d - \mu_+\cos d\right)\sin v ,
```

whose coefficients are at least $\frac{41}{20}\mu_- - \mu_+ > 0$ and
$\frac{41}{20}\mu_+ - \frac45 > 0$ (by the bound
$\frac12\sin d + \mu_+\cos d < \frac45$ of §D.4); so $K + B$ is concave in $v$
on $[0, \frac{31}{50}]$ (Lemma A.11 (1)) and positive between the wall and the
top. $\square$

*Lean:
[`Six.Wings.WestDiagonal.norm_upper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L45),
[`Six.Wings.WestDiagonal.rootSlope`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L39),
[`Six.Wings.WestDiagonal.rootCoefficient`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L40),
[`Six.Wings.WestDiagonal.coefficient_le`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L42),
[`Six.Wings.WestDiagonal.diagonalUpper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L54),
[`Six.Wings.WestDiagonal.support`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L57),
[`Six.Wings.WestDiagonal.west_support`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L210),
[`Six.Wings.WestDiagonal.diagonal_first_lower`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L67),
[`Six.Wings.WestDiagonal.beta`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L94),
[`Six.Wings.WestDiagonal.wing`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L96),
[`Six.Wings.WestDiagonal.gapTerm`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L97),
[`Six.Wings.WestDiagonal.base`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L99),
[`Six.Wings.WestDiagonal.pointV`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L102),
[`Six.Wings.WestDiagonal.pointD`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L103),
[`Six.Wings.WestDiagonal.wing_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L105),
[`Six.Wings.WestDiagonal.west_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L109),
[`Six.Wings.WestDiagonal.wall_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L131),
[`Six.Wings.WestDiagonal.top_monotone`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L157),
[`Six.Wings.WestDiagonal.positive_of_three_points`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L187).*

![Two panels. Left: over x from 0 to 6/5, the derivative of psi, in blue, falling from about 1.19 to about 0.73 and staying above the dashed orange level 7/10; the Taylor bound 0.7278 at 6/5 is marked. Right: the domain of (v, d) of section D.9, a green quadrilateral: its left edge, the wall, drawn purple, its right edge, the top, drawn orange with an arrow pointing up, and green horizontal segments across it; black dots mark the three points of the lemma, and an open circle the fourth corner](figures/appendix-d/base.svg)

*Figure D.19.* Lemma D.18. Left, (1): $\psi'$ decreases on $[0, \frac65]$, as
$\psi$ is concave, and stays above $\frac7{10}$. Right, (2): from the three
points (dots), $K + B$ is positive along the wall (purple), where it is concave
in $d$, along the top (orange), where it does not decrease in $d$, and then on
each segment at fixed $d$ (green), where it is concave in $v$; the fourth corner
(open circle) needs no check.

### Proposition D.19 (W on its own axis, S on the south side: a missing west wing)

There are no wing data with a missing west wing that satisfy (D.2) and (D.5),
with $\lvert s\rvert \le \frac25$, $\frac{16}{25} \le d \le \frac{11}{14}$ and
$\frac{53}{50} - d \le v \le \frac{31}{50}$.

*Proof.* *The stress.* Add (D.2), (D.5), (D.7) and (D.8) with the weights
$\frac{41}{20}$, $\gamma = \frac32$, $1$ and $1$. Besides $F_W$ and $F_D$, Table
D.1 gives the forces

```math
F_S = \left(\tfrac32\cos s, 1 - \tfrac32\sin s\right), \qquad F_C = \left(\tfrac{41}{20}\cos v, \tfrac32 - \tfrac{41}{20}\sin v\right) .
```

Here $v \in [\frac{48}{175}, \frac{31}{50}]$, $q \in [1, \frac\pi2]$ and
$r \in [\frac6{25}, \frac{11}{14} + \frac25] \subset [0, \frac65]$, and the
thresholds are $\frac12 + \frac12(\cos x + \sin x)$ for $x = v, q, r$ and
$\frac12 + \frac12(\cos s + \lvert\sin s\rvert)$.

*The supports.* $W$ and $D$ as above. For $S$,
$\lvert F_S\rvert^2 = \frac{13}4 - 3\sin s$, and the tangent of the square root
at $\frac95$ ([Lemma A.14](appendix-a.md#lemma-a14-tangents-of-the-square-root))
gives the first bound below, and the far vertex gives the second, on the work on
$S$:

```math
\lvert F_S\rvert \le \tfrac5{18}\left(\tfrac{13}4 - 3\sin s + \tfrac{81}{25}\right) = \tfrac{649}{360} - \tfrac56\sin s, \qquad \bar R\left(\tfrac{649}{360} - \tfrac56\sin s\right) - \tfrac12\left(\tfrac32\cos s + 1 - \tfrac32\sin s\right) .
```

For $C$ the corner of the box, as $\frac32 - \frac{41}{20}\sin v$ is at least
$\frac32 - \frac{41}{20}\cdot\frac{31}{50} > 0$. Collecting the terms, the
weighted sum becomes $\Pi \le 0$, where, with $x = \lvert s\rvert$,

```math
\Pi = K_4 + B(v, s, d) + \tfrac32\cos x + \sigma_\pm\sin x, \qquad K_4 = \tfrac32\mu_- - \tfrac{41}{20}\mu_+ + 2 - \tfrac{649}{360}\bar R = -1.71968\ldots ,
```

and $\sigma_+ = \frac56\bar R = 1.40716\ldots$ for $s \ge 0$,
$\sigma_- = \frac32 - \frac56\bar R = 0.09283\ldots$ for $s < 0$.

*Positivity.* For either sign, $x \mapsto \Pi$ is concave on $[0, \frac25]$:
$\psi(d \mp x)$ is concave by Lemma D.8 (2), and
$\frac32\cos x + \sigma_\pm\sin x$ is a nonnegative first harmonic. So at each
of the three points of Lemma D.18 (2), positivity at $s = 0$ and
$s = \pm\frac25$ gives positivity for all $s \in [-\frac25, \frac25]$, and then
Lemma D.18 (2), with $K = K_4 + \frac32\cos x + \sigma_\pm\sin x$, gives
$\Pi > 0$ on the domain. At the points we replace $\cos v$, $\cos q$, $\cos r$,
$\cos x$ by $C_6$, $\sin v$, $\sin\frac r2$, $\sin x$ by $S_7$, and $\sin q$,
$\cos\frac r2$, which have negative coefficients, by $S_5$ and $C_4$. Table D.12
lists the resulting lower bounds, all positive, a contradiction (Figure D.20).
$\square$

| $(v, d)$ | $s = 0$ | $s = \frac25$ | $s = -\frac25$ |
| --- | :-: | :-: | :-: |
| $(\frac{21}{50}, \frac{16}{25})$ | $0.01258$ | $0.04171$ | $0.26450$ |
| $(\frac{48}{175}, \frac{11}{14})$ | $0.00852$ | $0.06326$ | $0.24082$ |
| $(\frac{31}{50}, \frac{16}{25})$ | $0.01065$ | $0.03977$ | $0.26257$ |

*Table D.12.* Lower bounds of $\Pi$ at the three points, by Taylor polynomials,
rounded down.

*Lean:
[`Six.Wings.WestDiagonal.SideSouth.impossible`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L429),
[`Six.Wings.WestDiagonal.SideSouth.gamma`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L226),
[`Six.Wings.WestDiagonal.SideSouth.rootIntercept`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L230),
[`Six.Wings.WestDiagonal.SideSouth.rootSin`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L231),
[`Six.Wings.WestDiagonal.SideSouth.south_root`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L360),
[`Six.Wings.WestDiagonal.SideSouth.southUpper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L345),
[`Six.Wings.WestDiagonal.SideSouth.south_support`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L372),
[`Six.Wings.WestDiagonal.SideSouth.centerUpper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L349),
[`Six.Wings.WestDiagonal.SideSouth.center_support`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L387),
[`Six.Wings.WestDiagonal.SideSouth.thresholdSum`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L352),
[`Six.Wings.WestDiagonal.SideSouth.defect`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L356),
[`Six.Wings.WestDiagonal.SideSouth.constantTerm`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L233),
[`Six.Wings.WestDiagonal.SideSouth.side`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L234),
[`Six.Wings.WestDiagonal.SideSouth.sineCoefficient`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L235),
[`Six.Wings.WestDiagonal.SideSouth.southTerm`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L238),
[`Six.Wings.WestDiagonal.SideSouth.profile`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L241),
[`Six.Wings.WestDiagonal.SideSouth.profile_eq_defect`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L400),
[`Six.Wings.WestDiagonal.SideSouth.south_term_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L244),
[`Six.Wings.WestDiagonal.SideSouth.south_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L250),
[`Six.Wings.WestDiagonal.SideSouth.lowerPolynomial`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L272),
[`Six.Wings.WestDiagonal.SideSouth.polynomial_le`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L279),
[`Six.Wings.WestDiagonal.SideSouth.endpoint`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L297),
[`Six.Wings.WestDiagonal.SideSouth.endpoint_margin`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L299),
[`Six.Wings.WestDiagonal.SideSouth.boundary_positive`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L306),
[`Six.Wings.WestDiagonal.SideSouth.positive`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L328).*

![Three panels. The first two show missing west wings with W turned on its own axis: D is separated from W by the line of its own upper left side and from S by a side of S, with S on the south side of C in the first panel and turned on its own axis in the second, and orange arrows for the forces. The third shows the small quadrilateral domain of the angles v and d, shaded green, with three marked points and two lower bounds at each](figures/appendix-d/diagonal.svg)

*Figure D.20.* Propositions D.19 and D.20. (a) A missing west wing with $W$ on
its own axis and $S$ on the south side of $C$, at $v = 0.45$, $s = 0$ and
$d = 0.72$ (radius $1.696$), with the weights $\frac{41}{20}$, $\frac32$, $1$,
$1$; (b) the same with $S$ on its own axis and $s = 0.2$ (radius $1.700$), with
the weights $\frac{41}{20}$, $2$, $1$, $1$. The separations of $D$ from $W$ and
from $S$ are along the secondary axes of $D$ and of $S$. (c) The domain of
$(v, d)$ left by Proposition D.7, shaded by the minimum over $s$ of the profiles
of both propositions, with the three points of Lemma D.18 and the smallest
bounds there in Tables D.12 and D.13, for (a) and for (b).

### Proposition D.20 (W and S on their own axes: a missing west wing)

There are no wing data with a missing west wing that satisfy (D.2) and (D.4),
with $0 \le s \le \frac{12}{25}$, $\frac{16}{25} \le d \le \frac{11}{14}$ and
$\frac{53}{50} - d \le v \le \frac{31}{50}$.

*Proof.* *The stress.* The angle $s$ lies in one of the pieces
$[0, \frac3{20}]$, $[\frac3{20}, \frac3{10}]$ and $[\frac3{10}, \frac{12}{25}]$;
on these let $\gamma = \frac85$, $2$, $\frac{13}5$ and $\ell_\gamma = 1.887$,
$2.237$, $2.786$. Add (D.2), (D.4), (D.7) and (D.8) with the weights
$\frac{41}{20}$, $\gamma$, $1$ and $1$. Besides $F_W$ and $F_D$, Table D.1 gives

```math
F_S = (\gamma, 1), \qquad F_C = \left(\tfrac{41}{20}\cos v - \gamma\sin s,\ \gamma\cos s - \tfrac{41}{20}\sin v\right) .
```

The thresholds are $\frac12 + \frac12(\cos x + \sin x)$ for $x = v, s, q, r$.

*The supports.* $W$ and $D$ as above. For $S$ the far vertex with
$\ell = \ell_\gamma$, as $\sqrt{\gamma^2 + 1} = \sqrt{3.56}$, $\sqrt5$,
$\sqrt{7.76}$ are below $\ell_\gamma$: the work is at most
$\bar R\ell_\gamma - \frac12(\gamma + 1)$. For $C$ the corner of the box: as
$\cos v \ge 1 - \frac12(\frac{31}{50})^2 > \frac45$,
$\cos s \ge 1 - \frac12(\frac{12}{25})^2 > \frac{22}{25}$,
$\sin v \le \frac{31}{50}$ and $\sin s \le \frac{12}{25}$, the components of
$F_C$ are at least
$\frac{41}{20}\cdot\frac45 - \frac{13}5\cdot\frac{12}{25} > 0$ and
$\frac85\cdot\frac{22}{25} - \frac{41}{20}\cdot\frac{31}{50} > 0$. Collecting
the terms, the weighted sum becomes $\Pi \le 0$, where

```math
\Pi = 2 - \tfrac{41}{20}\mu_+ + B(v, s, d) + \gamma\left(1 + \zeta(s)\right) - \bar R\ell_\gamma .
```

*Positivity.* $\Pi$ is concave in $s$ on $[0, \frac{12}{25}]$, by Lemma D.8 (2)
and the concavity of $\zeta$. So at each of the three points of Lemma D.18 (2),
positivity at the ends of a piece gives positivity on the piece, and then Lemma
D.18 (2), with
$K = 2 - \frac{41}{20}\mu_+ + \gamma(1 + \zeta(s)) - \bar R\ell_\gamma$, gives
$\Pi > 0$ on the domain. At the points we replace $\cos v$, $\cos q$, $\cos r$,
$\cos s$ by $C_6$, $\sin v$, $\sin\frac r2$, $\sin s$ by $S_7$, and $\sin q$,
$\cos\frac r2$ by $S_5$ and $C_4$. Table D.13 lists the resulting lower bounds,
all positive, a contradiction (Figure D.20). $\square$

| $(v, d)$ | $\gamma = \frac85$: $s = 0$, $\frac3{20}$ | $\gamma = 2$: $s = \frac3{20}$, $\frac3{10}$ | $\gamma = \frac{13}5$: $s = \frac3{10}$, $\frac{12}{25}$ |
| --- | :-: | :-: | :-: |
| $(\frac{21}{50}, \frac{16}{25})$ | $0.00908$, $0.00689$ | $0.00565$, $0.00700$ | $0.01055$, $0.01103$ |
| $(\frac{48}{175}, \frac{11}{14})$ | $0.00502$, $0.01207$ | $0.01082$, $0.02193$ | $0.02548$, $0.03785$ |
| $(\frac{31}{50}, \frac{16}{25})$ | $0.00715$, $0.00496$ | $0.00372$, $0.00506$ | $0.00862$, $0.00910$ |

*Table D.13.* Lower bounds of $\Pi$ at the three points and the ends of the
pieces, by Taylor polynomials, rounded down.

*Lean:
[`Six.Wings.WestDiagonal.OwnSouth.impossible`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L649),
[`Six.Wings.WestDiagonal.OwnSouth.pieceStart`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L476),
[`Six.Wings.WestDiagonal.OwnSouth.pieceEnd`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L477),
[`Six.Wings.WestDiagonal.OwnSouth.gamma`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L478),
[`Six.Wings.WestDiagonal.OwnSouth.length`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L479),
[`Six.Wings.WestDiagonal.OwnSouth.gamma_bounds`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L487),
[`Six.Wings.WestDiagonal.OwnSouth.length_bound`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L490),
[`Six.Wings.WestDiagonal.OwnSouth.piece_range`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L493),
[`Six.Wings.WestDiagonal.OwnSouth.southUpper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L587),
[`Six.Wings.WestDiagonal.OwnSouth.south_support`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L602),
[`Six.Wings.WestDiagonal.OwnSouth.forceX`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L589),
[`Six.Wings.WestDiagonal.OwnSouth.forceY`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L590),
[`Six.Wings.WestDiagonal.OwnSouth.central_forces`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L611),
[`Six.Wings.WestDiagonal.OwnSouth.centerUpper`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L592),
[`Six.Wings.WestDiagonal.OwnSouth.thresholdSum`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L594),
[`Six.Wings.WestDiagonal.OwnSouth.defect`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L598),
[`Six.Wings.WestDiagonal.OwnSouth.constantTerm`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L481),
[`Six.Wings.WestDiagonal.OwnSouth.profile`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L484),
[`Six.Wings.WestDiagonal.OwnSouth.profile_eq_defect`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L630),
[`Six.Wings.WestDiagonal.OwnSouth.south_concave`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L498),
[`Six.Wings.WestDiagonal.OwnSouth.lowerPolynomial`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L518),
[`Six.Wings.WestDiagonal.OwnSouth.polynomial_le`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L524),
[`Six.Wings.WestDiagonal.OwnSouth.endpoint_margin`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L543),
[`Six.Wings.WestDiagonal.OwnSouth.boundary_positive`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L549),
[`Six.Wings.WestDiagonal.OwnSouth.positive`](../../SquaresInCircles/Six/Wings/WestDiagonal.lean#L570).*

## D.10 Proof of Proposition 9.46

[Proposition 9.46](09-six.md#proposition-946-no-missing-wing) states that in a
normalized packing neither the west wing nor the south wing is missing.

*Proof.* Let a normalized packing be given, put $v = -w$, and take its wing data
(Lemma D.2). Recall that $\frac12 < d \le \frac\pi4$, $v < \frac23$ and
$s < \frac23$ (Lemma D.2 (3)), and that a square on its own axis has a positive
angle and one on its matching side an angle below $\frac25$ in absolute value
(Lemma D.2 (4)). The propositions of §D.5 to §D.9 are applied on the ranges of
$d$ shown in Figure D.21; two of them are applied to the reflection of the wing
data (Lemma D.3), whose angle of $D$ lies in $[\frac\pi4, \frac\pi2 - \frac12)$.

![Seven horizontal bars over the axis of d, one for each of Propositions D.10, D.11, D.12, D.14, D.15, D.17 and D.19 with D.20: each grey bar is the range of d of the proposition, a blue part inside it the range used for normalized packings, and for Propositions D.14 and D.17 an orange part from π/4 to π/2 − 3/5 or π/2 − 16/25 the range used for the reflections](figures/appendix-d/ranges.svg)

*Figure D.21.* For each case, the range of the angle $d$ on which its
proposition is proved (grey), the part used for normalized packings (blue) and
the part used for the reflections of missing west wings (orange). The upper ends
$\frac{34}{35}$ and $\frac{163}{175}$ lie just beyond $\frac\pi2 - \frac35$ and
$\frac\pi2 - \frac{16}{25}$.

*No missing south wing.* Suppose the south wing is missing. Then the wing data
satisfy (D.6) and (D.9), and $r < \frac\pi4$ (Lemma D.2 (6)). We go through the
separators of $W$ and $S$ from $C$ (Lemma D.2 (1)).

- $W$ and $S$ on their matching sides: (D.3) holds, $\lvert v\rvert < \frac25$
  and $s < \frac25 < \frac{12}{25}$, which Proposition D.11 excludes.
- $W$ on the west side of $C$, $S$ on its own axis: (D.3) and (D.4) hold, with
  $\lvert v\rvert < \frac25$. If $s \le \frac{12}{25}$, Proposition D.11
  applies; otherwise $\frac{12}{25} < s < \frac23$ and
  $d \le \frac\pi4 < \frac{11}{14}$, and Proposition D.12 applies.
- $W$ on its own axis, $S$ on the south side of $C$: (D.2) and (D.5) hold, with
  $0 < v < \frac23$ and $\lvert s\rvert < \frac25$; as
  $d \le \frac\pi4 < \frac{11}{14}$, the condition of Proposition D.14 for
  $d > \frac{11}{14}$ is void, and Proposition D.14 applies.
- $W$ and $S$ on their own axes: (D.2) and (D.4) hold, with $v, s > 0$ and
  $v + s < \frac{24}{25}$ (Lemma D.2 (5)). If $v \le s$, Proposition D.15
  applies. If $s < v$, Proposition D.17 applies, as
  $d \le \frac\pi4 < \frac{163}{175}$.

*No missing west wing.* Suppose the west wing is missing. Then the wing data
satisfy (D.7) and (D.8), $v > \frac\pi4 - d \ge 0$ (Lemma D.2 (6)), and
$q = d + v > 1$ (Lemma D.5).

- $W$ and $S$ on their matching sides: (D.3) and (D.5) hold, with
  $0 \le v < \frac25$ and $\lvert s\rvert < \frac25$, which Proposition D.10
  excludes.
- $W$ on the west side of $C$, $S$ on its own axis: (D.3) and (D.4) hold, with
  $\lvert v\rvert < \frac25$ and $0 < s < \frac23$. By Lemma D.3 the reflection
  of the wing data has a missing south wing and satisfies (D.2) and (D.5), with
  the angles $v' = s \in (0, \frac23)$, $s' = v$, $\lvert s'\rvert < \frac25$
  and $d' = \frac\pi2 - d$. Here $d' \ge \frac\pi4 > \frac12$, and, as
  $d > 1 - v > \frac35$, $d' < \frac\pi2 - \frac35 < \frac{34}{35}$. Its gap
  $r' = \frac\pi2 - q$ is below $\frac\pi4$, as $v > \frac\pi4 - d$, and below
  $\frac\pi2 - 1 < \frac47$, as $q > 1$; and $s' = v > 0$. So Proposition D.14
  applies to the reflection.
- $W$ on its own axis, $S$ on the south side of $C$: (D.2) and (D.5) hold, and
  by Proposition D.7, $\frac{16}{25} < d \le \frac\pi4 < \frac{11}{14}$ and
  $\frac{53}{50} - d < v < \frac{31}{50}$. With $\lvert s\rvert < \frac25$,
  Proposition D.19 applies.
- $W$ and $S$ on their own axes: (D.2) and (D.4) hold, with $v, s > 0$ and
  $v + s < \frac{24}{25}$, and Proposition D.7 gives the domain of the previous
  case. If $s \le v$, then $2s < \frac{24}{25}$, so $0 < s < \frac{12}{25}$, and
  Proposition D.20 applies. If $v < s$, the reflection of the wing data (Lemma
  D.3) has a missing south wing and satisfies (D.2) and (D.4), with the angles
  $v' = s < \frac23$, $s' = v > 0$, $s' < v'$, $v' + s' < \frac{24}{25}$ and
  $d' = \frac\pi2 - d$, where
  $\frac12 < \frac\pi4 \le d' < \frac\pi2 - \frac{16}{25} < \frac{163}{175}$;
  its gap $r' = \frac\pi2 - q$ is below $\frac\pi4$. So Proposition D.17 applies
  to the reflection.

In every case the separations are impossible, so neither wing is missing.
$\square$

With [Lemma 9.37](09-six.md#lemma-937-secondary-axes),
[Proposition 9.41](09-six.md#proposition-941-d-and-s-along-a-secondary-axis) and
[Lemma 9.42](09-six.md#lemma-942-walls) (2), which leave a missing wing as the only
alternative to a wing, this proves
[Proposition 9.45](09-six.md#proposition-945-the-wings).

*Lean:
[`Six.Wings.not_missing_south`](../../SquaresInCircles/Six/Wings/Separators.lean#L31),
[`Six.Wings.not_missing_west`](../../SquaresInCircles/Six/Wings/Separators.lean#L87),
[`Six.Wings.west_gap`](../../SquaresInCircles/Six/Wings/Separators.lean#L65),
[`Six.Wings.own_west_range`](../../SquaresInCircles/Six/Wings/Separators.lean#L72),
[`Six.westDiagonal_gap_gt_one`](../../SquaresInCircles/Six/Wings/WestGap.lean#L161),
[`Six.wing_separators`](../../SquaresInCircles/Six/Wings/Separators.lean#L133).*
