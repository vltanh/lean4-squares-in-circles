# Appendix E. Six squares: the tails and the stress of the model

[Contents](README.md) · [← Appendix D](appendix-d.md) · [Appendix F →](appendix-f.md)

This appendix proves three statements of [Chapter 9](09-six.md). §E.1 bounds the
angles of $W$ and $S$ when they are separated from $C$ along their own axes
([Proposition 9.47](09-six.md#proposition-947-the-tails)). §E.2 proves the pair
estimate ([Proposition 9.50](09-six.md#proposition-950-the-pair-estimate)): on its
domain the value of the pair $N$, $W$ is at least
$\beta_* + \ell(w) + \frac1{1000}|n|$. §E.3 proves the diagonal estimate
([Proposition 9.53](09-six.md#proposition-953-the-diagonal-estimate)): the
remainder $\mathcal R$ of the turned square $D$ is nonnegative and vanishes
only at the angles of the model. All three rest on stresses
([Definition 9.23](09-six.md#definition-923-stress)): weighted sums of separating
inequalities, whose threshold sums are compared with the supports of the
forces. In §E.1 the weights are chosen for the purpose and the thresholds win,
so the separations are impossible; in §E.2 and §E.3 the weights are those of
the model ([Proposition 9.27](09-six.md#proposition-927-the-stress-of-the-model)),
and the comparison is an estimate that is tight at the model.

We use the notation of Chapter 9: $h = \frac{\sqrt2}2$; the constants $s_*$,
$t_*$, $q_*$, $R_6$ and $\rho_*$ of [Lemma 9.2](09-six.md#lemma-92-the-constants)
and $r_*$, $m_*$, $K_*$ and $\beta_*$ of Proposition 9.27; the ceiling
$Q_0 = 2.85118$, $R_0$, $\rho_0$ and $c_0$ and the decimals $\bar R = 1.6886$,
$\bar\rho = 1.11282$ and $\bar c = 0.11282$
([Definition 9.4](09-six.md#definition-94-the-ceiling),
[Lemma 9.5](09-six.md#lemma-95-the-ceiling)); the squares $Q_t(a, b)$, the charts
in the ceiling, the widths $\omega(\delta)$ and the thresholds
$\tau(\delta) = \frac12 + \omega(\delta)$
([Definition 9.9](09-six.md#definition-99-squares-in-a-frame)); and the angles $e$,
$n$, $w$, $d$, $s$ of a normalized packing
([Definition 9.34](09-six.md#definition-934-normalized-packing)). Note that
$\bar\rho = 1 + \bar c$. The tools of
[§A.4](appendix-a.md#a4-concave-functions-and-harmonics) are used throughout:
concave functions ([Lemma A.10](appendix-a.md#lemma-a10-concave-functions)),
first harmonics ([Lemma A.11](appendix-a.md#lemma-a11-first-harmonics)), a
turning vector ([Lemma A.13](appendix-a.md#lemma-a13-a-turning-vector)), the
tangents of the square root
([Lemma A.14](appendix-a.md#lemma-a14-tangents-of-the-square-root)) and small
angles ([Lemma A.15](appendix-a.md#lemma-a15-small-angles)); so are the Taylor
bounds of [Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds), the polynomial
brackets of [Lemma A.8](appendix-a.md#lemma-a8-polynomial-brackets) and the
concave trigonometric sums of
[Lemma A.5](appendix-a.md#lemma-a5-concave-trigonometric-sums). We write

```math
C_4(t) = 1 - \tfrac{t^2}2 + \tfrac{t^4}{24}, \quad C_6(t) = C_4(t) - \tfrac{t^6}{720}, \quad S_5(t) = t - \tfrac{t^3}6 + \tfrac{t^5}{120}, \quad S_7(t) = S_5(t) - \tfrac{t^7}{5040}
```

for the Taylor polynomials. By Lemma A.7 and parity, $C_6(t) \le \cos t \le C_4(t)$
for every real $t$, $S_7(t) \le \sin t \le S_5(t)$ for $t \ge 0$, and
$S_5(t) \le \sin t \le S_7(t)$ for $t \le 0$. A *Taylor lower bound* of a
trigonometric expression replaces each cosine and sine by the polynomial on the
side that makes the expression smaller, according to the sign of its coefficient
and of its argument; it is a rational number when the arguments are, and we
compute it exactly. Every decimal in a table below is such a bound, or a value,
rounded down.

## E.1 Proof of Proposition 9.47

Throughout this section a normalized packing in a closed disk of squared radius
at most $Q_0$ is fixed, with the containing square $C = Q(c)$,
$c = (c_x, c_y) \in [0, c_0]^2$. We write the phases of $W$, $D$ and $S$ as

```math
t_W = \pi - v, \qquad t_D = \pi + d, \qquad t_S = \tfrac{3\pi}2 + s ,
```

so that $v = -w$ is the angle by which $W$ is turned clockwise from its phase in
the model, and

```math
W = Q_{\pi - v}(a_W, b_W), \qquad D = Q_{\pi + d}(a_D, b_D), \qquad S = Q_{3\pi/2 + s}(a_S, b_S)
```

for charts in the ceiling ([Proposition 9.22](09-six.md#proposition-922-labels)).
So $(a + \frac12)^2 + (|b| + \frac12)^2 \le Q_0$ and $\frac12 \le a \le \rho_0$
for each of the three centres
([Lemma 9.10](09-six.md#lemma-910-charts-in-the-ceiling)). The west tail is
$v \ge \frac{11}{25}$ for $W$ on its own axis, the south tail $s \ge \frac{11}{25}$
for $S$ on its own axis; we show that neither occurs.

### Lemma E.1 (the separations in coordinates)

1. If $W$ is separated from $C$ along its own axis, then
   $a_W + c_x\cos v - c_y\sin v \ge \tau(v)$; if along the west side of $C$,
   then $a_W\cos v + b_W\sin v + c_x \ge \tau(v)$.
2. If $S$ is separated from $C$ along its own axis, then
   $a_S - c_x\sin s + c_y\cos s \ge \tau(s)$; if along the south side of $C$,
   then $a_S\cos s - b_S\sin s + c_y \ge \tau(s)$.
3. If $W$ and $D$ are separated along $e^W_2$, then
   $a_D\sin(v + d) + b_D\cos(v + d) - b_W \ge \tau(v + d)$; if $D$ and $S$ are
   separated along $e^S_2$, then
   $b_S + a_D\cos(d - s) - b_D\sin(d - s) \ge \tau(d - s)$.

*Proof.* (1) In [Definition 9.12](09-six.md#definition-912-separators-of-the-containing-square)
take $t = \pi - v$: then $u(t) = (-\cos v, \sin v)$, so
$\langle c, u(t)\rangle = -c_x\cos v + c_y\sin v$, and
$x_t(a, b) = -a\cos v - b\sin v$; and $\tau(\pi - v) = \tau(v)$ by Lemma A.15 (2).
The margins $m_{\mathrm{own}}$ and $m_{\mathrm{west}}$ are the two differences.
(2) Here $t = \frac{3\pi}2 + s$, $u(t) = (\sin s, -\cos s)$,
$y_t(a, b) = -a\cos s + b\sin s$ and $\tau(t) = \tau(s)$; the margins
$m_{\mathrm{own}}$ and $m_{\mathrm{south}}$ are the two differences.
(3) In [Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares) take
$U = W$ and $V = D$, with $\delta = (\pi + d) - (\pi - v) = v + d$: the offset
along $e^U_2$ is $a_D\sin\delta + b_D\cos\delta - b_W$. Then take $U = D$ and
$V = S$, with $\delta = \frac\pi2 - (d - s)$: the offset along $e^V_2$ is
$b_S + a_D\sin\delta - b_D\cos\delta = b_S + a_D\cos(d - s) - b_D\sin(d - s)$,
and $\tau(\delta) = \tau(d - s)$. $\square$

*Lean: [`Six.Wings.Chart`](../../SquaresInCircles/Six/Wings/Chart.lean#L27),
[`Six.Wings.chart`](../../SquaresInCircles/Six/Wings/Chart.lean#L147),
[`Six.Wings.Chart.WestOwn`](../../SquaresInCircles/Six/Wings/Chart.lean#L49),
[`Six.Wings.Chart.WestSide`](../../SquaresInCircles/Six/Wings/Chart.lean#L52),
[`Six.Wings.Chart.SouthOwn`](../../SquaresInCircles/Six/Wings/Chart.lean#L55),
[`Six.Wings.Chart.SouthSide`](../../SquaresInCircles/Six/Wings/Chart.lean#L58),
[`Six.Wings.Chart.WestWing`](../../SquaresInCircles/Six/Wings/Chart.lean#L61),
[`Six.Wings.Chart.SouthWing`](../../SquaresInCircles/Six/Wings/Chart.lean#L69),
[`Six.Wings.west_own`](../../SquaresInCircles/Six/Wings/Chart.lean#L185),
[`Six.Wings.west_side`](../../SquaresInCircles/Six/Wings/Chart.lean#L194),
[`Six.Wings.south_own`](../../SquaresInCircles/Six/Wings/Chart.lean#L204),
[`Six.Wings.south_side`](../../SquaresInCircles/Six/Wings/Chart.lean#L213),
[`Six.Wings.west_wing`](../../SquaresInCircles/Six/Wings/Chart.lean#L224),
[`Six.Wings.south_wing`](../../SquaresInCircles/Six/Wings/Chart.lean#L246).*

### Lemma E.2 (the angles)

1. $\frac12 < d \le \frac\pi4 < \frac{11}{14}$, $v < \frac23$ and
   $s < \frac23$.
2. If $W$ is on its own axis, then $v > 0$; if $S$ is on its own axis, then
   $s > 0$; if both are, then $v + s < \frac{24}{25}$.
3. If $W$ is on its matching side, then $|v| < \frac25$; if $S$ is, then
   $|s| < \frac25$.
4. $|b_D| < \frac9{40}$.

*Proof.* (1) is [Proposition 9.39](09-six.md#proposition-939-the-angle-of-d),
[Proposition 9.35](09-six.md#proposition-935-normalization) (1) and $\pi < \frac{22}7$;
(2) is [Lemma 9.38](09-six.md#lemma-938-w-on-its-own-axis-turns-away-from-d) and
[Lemma 9.43](09-six.md#lemma-943-signs-of-the-own-wings), as $s - w = v + s$;
(3) is Proposition 9.35 (3); (4) is
[Lemma 9.40](09-six.md#lemma-940-transverse-profiles) (1). $\square$

*Lean:
[`Six.Wings.diagonal_range`](../../SquaresInCircles/Six/Wings/Chart.lean#L278),
[`Six.Wings.west_upper`](../../SquaresInCircles/Six/Wings/Chart.lean#L281),
[`Six.Wings.south_upper`](../../SquaresInCircles/Six/Wings/Chart.lean#L286),
[`Six.Wings.west_own_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L288),
[`Six.Wings.south_own_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L293),
[`Six.Wings.own_angle_sum`](../../SquaresInCircles/Six/Wings/Chart.lean#L305),
[`Six.Wings.west_side_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L296),
[`Six.Wings.south_side_angle`](../../SquaresInCircles/Six/Wings/Chart.lean#L301),
[`Six.normalized_diagonal_transverse_small`](../../SquaresInCircles/Six/Separators/Profiles.lean#L260).*

Both tails are excluded by a stress on the four edges $C$–$W$, $C$–$S$, $W$–$D$
and $D$–$S$, along the axes of Lemma E.1, with weights $\lambda_1$, $\lambda_2$,
$\lambda_3$, $\lambda_4$. Adding the four inequalities with these weights gives
the threshold sum on the left and, on the right, the works of the forces on the
four centres ([Lemma 9.24](09-six.md#lemma-924-balance)): the force on $W$ is
$\lambda_1$ times the normal of $C$–$W$ less $\lambda_3 e^W_2$, the force on $D$
is $\lambda_3e^W_2 - \lambda_4e^S_2$, and so on. The supports of
[Lemma 9.25](09-six.md#lemma-925-supports-of-a-square-in-a-disk), at $R = R_0$,
and of [Lemma 9.26](09-six.md#lemma-926-supports-in-the-ceiling) bound the works
on $W$, $D$ and $S$, and the box $[0, c_0]^2$ the work on $C$. What remains is a
function of the angles that must be at most $0$, and is shown to be positive.
Figure E.1 shows what goes wrong at the edge of the west tail.

![Four unit squares near the disk centre inside a faint circle of radius R0: the central square C slightly right of the centre, W to its left turned clockwise by about 25 degrees with its upper left corner on the circle, S below C turned slightly with its lower right corner on the circle, and the turned square D in the lower left corner between them, touching W and S along dashed separating lines, with its far vertex outside the circle and the part of D beyond the circle shaded red; arrows from the centres show the forces of the stress](figures/appendix-e/west-tail.svg)

*Figure E.1.* At the edge of the west tail, $v = \frac{11}{25}$, with
$s = \frac1{20}$, $d = \frac\pi4$ and $c = (c_0, 0)$. The squares $W$ and $S$,
separated from $C$ along their own axes, are pushed out until their far
vertices meet the circle of radius $R_0$ (grey), and $D$ touches both along the
secondary axes of $W$ and $S$ (dashed separating lines). Then the far vertex of
$D$ lies at distance $1.79 > R_0$ from the disk centre (red). The arrows are the
forces of the stress with the weights $\frac8{15}$, $\frac15$, $\frac16$,
$\frac1{10}$ on $C$–$W$, $C$–$S$, $W$–$D$, $D$–$S$. Lemma E.4 shows that the
four separations cannot hold together anywhere in the tail.

### Lemma E.3 (the west minorant)

Let $\sigma_0 = \sigma_1 = 1$, $\sigma_2 = -1$, $x_0 = x_1 = \frac35$,
$x_2 = \frac25$,

```math
K = 1 - \left(0.5588 + \tfrac{161}{720}\right)\bar R - \tfrac{1073}{5400}\bar\rho ,
```

$K_0 = K$, $K_1 = K_2 = K - \frac1{10}$, and

```math
(g_0, h_0) = \left(\tfrac1{10},\ \tfrac15(\tfrac12 + 0.1128)\right), \qquad (g_1, h_1) = \left(\tfrac15,\ 0.09\bar R\right), \qquad (g_2, h_2) = \left(\tfrac15,\ \tfrac15 - 0.09\bar R\right) .
```

For $k \in \lbrace 0, 1, 2\rbrace$ put

```math
\begin{aligned}
m_k(v, x, d) = K_k &+ \tfrac8{15}\left(\tfrac12 - \bar c\right)\cos v + \tfrac4{15}\sin v + g_k\cos x + h_k\sin x \\
&+ \tfrac1{12}\left(\cos(v + d) + \sin(v + d)\right) + \tfrac1{20}\left(\cos(d - \sigma_kx) + \sin(d - \sigma_kx)\right) - \tfrac5{72}\bar\rho\sin(v + \sigma_kx) .
\end{aligned}
```

Then $m_k(v, x, d) > 0$ for $\frac{11}{25} \le v \le \frac23$, $0 \le x \le x_k$
and $\frac12 \le d \le \frac{11}{14}$.

Here $K \approx -0.54230$, $h_0 = 0.12256$, $h_1 = 0.151974$ and
$h_2 = 0.048026$.

*Proof.* We show that $m_k$ is a constant plus a first harmonic with nonnegative
coefficients in each variable, the others being fixed. The three intervals lie
in $[0, \frac\pi2]$. On the box, $\cos v \ge 1 - \frac{v^2}2 \ge \frac79$ and
$\sin v \le v \le \frac23$; $\cos x \ge 1 - \frac{x^2}2 \ge \frac{41}{50}$ and
$0 \le \sin x \le x \le \frac35$; $\cos d \ge 0$ and
$\sin d \ge \sin\frac12 \ge S_7(\frac12) > \frac{23}{48}$. Write
$e = \frac5{72}\bar\rho < 0.07729$.

1. *In $v$.* Expanding $\cos(v + d)$, $\sin(v + d)$ and $\sin(v + \sigma_kx)$,
   the coefficients of $\cos v$ and $\sin v$ are

   ```math
   \tfrac8{15}\left(\tfrac12 - \bar c\right) + \tfrac1{12}(\cos d + \sin d) - e\,\sigma_k\sin x \ge 0.2064 - \tfrac35e > 0, \qquad
   \tfrac4{15} + \tfrac1{12}(\cos d - \sin d) - e\cos x \ge \tfrac4{15} - \tfrac1{12} - e > 0 .
   ```

2. *In $x$.* As

   ```math
   \cos(d - \sigma x) + \sin(d - \sigma x) = (\cos d + \sin d)\cos x + \sigma(\sin d - \cos d)\sin x ,
   ```

   the coefficients of $\cos x$ and $\sin x$ are

   ```math
   g_k + \tfrac1{20}(\cos d + \sin d) - e\sin v \ge \tfrac1{10} - e > 0, \qquad
   h_k + \sigma_k\left(\tfrac1{20}(\sin d - \cos d) - e\cos v\right) .
   ```

   For $k = 0$ and $k = 1$ the second is at least
   $h_k + \frac1{20}(\frac{23}{48} - 1) - e \ge 0.12256 - 0.0261 - 0.0773 > 0$;
   for $k = 2$ it is at least
   $h_2 - \frac1{20} + \frac79e > 0.048 - 0.05 + 0.06 > 0$.
3. *In $d$.* The coefficients of $\cos d$ and $\sin d$ are

   ```math
   \tfrac1{12}(\cos v + \sin v) + \tfrac1{20}(\cos x - \sigma_k\sin x) \ge 0, \qquad
   \tfrac1{12}(\cos v - \sin v) + \tfrac1{20}(\cos x + \sigma_k\sin x) \ge 0 ,
   ```

   as $\cos v \ge \frac79 > \frac23 \ge \sin v$ and
   $\cos x \ge \frac{41}{50} > \frac35 \ge \sin x$.

By Lemma A.11 (2), applied in $d$ on each edge of the box parallel to the
$d$-axis, then in $x$ on each face $v = \text{const}$, then in $v$, $m_k$ is
positive on the box once it is positive at its eight corners. Table E.1 lists
Taylor lower bounds of the corner values; they are all positive. At $x = 0$ the
three functions agree, since $K_k + g_k$ does not depend on $k$. $\square$

| $v$ | $d$ | $x = 0$ | $k = 0$, $x = \frac35$ | $k = 1$, $x = \frac35$ | $k = 2$, $x = \frac25$ |
| :-: | :-: | :-: | :-: | :-: | :-: |
| $\frac{11}{25}$ | $\frac12$ | 0.00948 | 0.00438 | 0.00352 | 0.04462 |
| $\frac{11}{25}$ | $\frac{11}{14}$ | 0.00250 | 0.00815 | 0.00729 | 0.02964 |
| $\frac23$ | $\frac12$ | 0.01432 | 0.01694 | 0.01608 | 0.04705 |
| $\frac23$ | $\frac{11}{14}$ | 0.00035 | 0.01372 | 0.01286 | 0.02509 |

*Table E.1.* Taylor lower bounds of $m_k$ at the corners of the box, rounded down.

The corner $v = \frac23$, $x = 0$, $d = \frac{11}{14}$ is tight. There the
weighted threshold sum exceeds the supports by about $5.1 \cdot 10^{-4}$ when
$R_0$, $\rho_0$, $c_0$ and the lengths of the forces are kept exact (the weights
add up to $1$); the decimals $\bar R$, $\bar\rho$, $\bar c$, $0.5588$ and the
tangents leave $m_0 \approx 4.0 \cdot 10^{-4}$, and the Taylor polynomials
$3.5 \cdot 10^{-4}$ (Figure E.2).

![Three boxes drawn in perspective, one for each case k = 0, 1, 2, with axes v from 11/25 to 2/3, x from 0 to x_k and d from 1/2 to 11/14; each corner carries the Taylor lower bound of the minorant there, all positive, and the corner v = 2/3, x = 0, d = 11/14 is marked in orange with the smallest value 0.00035](figures/appendix-e/west-box.svg)

*Figure E.2.* The boxes of Lemma E.3 for the three separators of $S$: on its own
axis ($k = 0$), or along the south side of $C$ with $s \ge 0$ ($k = 1$) or
$s \le 0$ ($k = 2$). The minorant is concave along every edge, so its least
value on the box is at a corner; the orange corner is the tight one.

*Lean:
[`Six.WestTail.minorant`](../../SquaresInCircles/Six/Tails/West.lean#L73),
[`Six.WestTail.positive`](../../SquaresInCircles/Six/Tails/West.lean#L229),
[`Six.WestTail.constantTerm`](../../SquaresInCircles/Six/Tails/West.lean#L69),
[`Six.WestTail.side`](../../SquaresInCircles/Six/Tails/West.lean#L54),
[`Six.WestTail.xMax`](../../SquaresInCircles/Six/Tails/West.lean#L61),
[`Six.WestTail.gCoeff`](../../SquaresInCircles/Six/Tails/West.lean#L62),
[`Six.WestTail.hCoeff`](../../SquaresInCircles/Six/Tails/West.lean#L63),
[`Six.WestTail.offset`](../../SquaresInCircles/Six/Tails/West.lean#L65),
[`Six.WestTail.v_coefficients`](../../SquaresInCircles/Six/Tails/West.lean#L133),
[`Six.WestTail.x_coefficients`](../../SquaresInCircles/Six/Tails/West.lean#L141),
[`Six.WestTail.d_coefficients`](../../SquaresInCircles/Six/Tails/West.lean#L151),
[`Six.WestTail.polynomial_le`](../../SquaresInCircles/Six/Tails/West.lean#L193),
[`Six.WestTail.corners`](../../SquaresInCircles/Six/Tails/West.lean#L217).*

### Lemma E.4 (the west stress)

Let $\frac{11}{25} \le v \le \frac23$ and $\frac12 \le d \le \frac{11}{14}$, let
$(a_W, b_W)$, $(a_D, b_D)$, $(a_S, b_S)$ be charts in the ceiling, and let
$c_x \le c_0$ and $c_y \ge 0$. Then the inequality of Lemma E.1 (1) for the
own axis of $W$, the two inequalities of Lemma E.1 (3), and either the
inequality of Lemma E.1 (2) for the own axis of $S$ with $0 \le s \le \frac35$
or the one for the south side of $C$ with $-\frac25 \le s \le \frac35$, do not
all hold.

*Proof.* Suppose they hold. Let $k = 0$ in the first case, and in the second
$k = 1$ if $s \ge 0$ and $k = 2$ if $s \le 0$; write $s = \sigma_kx$ with
$0 \le x \le x_k$. Take the weights $\lambda_1 = \frac8{15}$,
$\lambda_2 = \frac15$, $\lambda_3 = \frac16$, $\lambda_4 = \frac1{10}$, which
add up to $1$. Adding the four inequalities with these weights gives

```math
\lambda_1\tau(v) + \lambda_2\tau(s) + \lambda_3\tau(v + d) + \lambda_4\tau(d - s) \le \left(\lambda_1a_W - \lambda_3b_W\right) + \left(Ua_D + Vb_D\right) + \Sigma_S + \Sigma_C ,
```

where $U = \lambda_3\sin(v + d) + \lambda_4\cos(d - s)$ and
$V = \lambda_3\cos(v + d) - \lambda_4\sin(d - s)$ are the components of the
force on $D$ in its frame, the work on $S$ is
$\Sigma_S = \lambda_2a_S + \lambda_4b_S$ for $k = 0$ and
$\Sigma_S = \lambda_2\cos s\,a_S + (\lambda_4 - \lambda_2\sin s)\,b_S$ otherwise,
and the work on $C$ is

```math
\Sigma_C = \lambda_1(c_x\cos v - c_y\sin v) + \begin{cases} \lambda_2(-c_x\sin s + c_y\cos s), & k = 0, \\ \lambda_2c_y, & k = 1, 2 . \end{cases}
```

We bound the four works.

1. *$W$.* By Lemma 9.25 (1) with $R = R_0 < \bar R$, and
   $\sqrt{\lambda_1^2 + \lambda_3^2} = \frac{\sqrt{281}}{30} < 0.5588$,
   $\lambda_1a_W - \lambda_3b_W \le 0.5588\bar R - \frac7{20}$.
2. *$S$.* The force on $S$ has the squared length
   $\lambda_2^2 + \lambda_4^2 = \frac1{20}$ for $k = 0$, and
   $\frac1{20} - \frac1{25}\sin s$ otherwise. By Lemma A.14 with $c = \frac29$,
   its length is at most $\frac{161}{720}$, respectively
   $\frac{161}{720} - 0.09\sin s$. With Lemma 9.25 (1) and
   $|X| + |Y| \ge X + Y$,

   ```math
   \Sigma_S \le \tfrac{161}{720}\bar R - \tfrac3{20} \quad (k = 0), \qquad
   \Sigma_S \le \left(\tfrac{161}{720} - 0.09\sin s\right)\bar R - \tfrac12\left(\tfrac15\cos s + \tfrac1{10} - \tfrac15\sin s\right) \quad (k = 1, 2) .
   ```

3. *$D$.* As $\sin(v + s) = \sin(v + d)\cos(d - s) - \cos(v + d)\sin(d - s)$,

   ```math
   U^2 + V^2 = \lambda_3^2 + \lambda_4^2 + 2\lambda_3\lambda_4\sin(v + s) = \tfrac{17}{450} + \tfrac1{30}\sin(v + s) ,
   ```

   and by Lemma A.14 with $c = \frac6{25}$ the length of the force is at most
   $\frac{1073}{5400} + \frac5{72}\sin(v + s)$. So Lemma 9.25 (2), with
   $\rho_0 < \bar\rho$, gives
   $Ua_D + Vb_D \le \bar\rho\left(\frac{1073}{5400} + \frac5{72}\sin(v + s)\right)$.
4. *$C$.* For $k = 0$,

   ```math
   \Sigma_C = c_x(\lambda_1\cos v - \lambda_2\sin s) + c_y(\lambda_2\cos s - \lambda_1\sin v) .
   ```

   The first coefficient is positive, as $\lambda_1\cos v \ge \frac{56}{135}$
   and $\lambda_2\sin s \le \frac3{25}$; the second is negative, as
   $\sin v \ge \sin\frac{11}{25} \ge S_7(\frac{11}{25}) > \frac25$ and so
   $\lambda_1\sin v > \frac{16}{75} > \frac15$. As $c_x \le c_0$, $c_y \ge 0$
   and $0.1128 < c_0 < \bar c$ (Lemma 9.5),

   ```math
   \Sigma_C \le c_0(\lambda_1\cos v - \lambda_2\sin s) \le \lambda_1\bar c\cos v - 0.1128\,\lambda_2\sin s .
   ```

   For $k = 1, 2$ the coefficient $\lambda_2 - \lambda_1\sin v$ of $c_y$ is
   negative, and $\Sigma_C \le \lambda_1\bar c\cos v$.

On the left, $\tau(t) \ge \frac12 + \frac12(\cos t + \sin t)$ for every $t$
(Lemma A.15 (2)), and $\tau(s) = \tau(x)$. Moving the four bounds to the left,
we obtain a quantity that is at most $0$; collecting its terms, it is at least
$m_k(v, x, d)$. For instance, for $k = 1$ the terms in $x$ are
$\frac1{10}(\cos x + \sin x)$ from $\lambda_2\tau(x)$ and
$0.09\bar R\sin x + \frac1{10}(\cos x - \sin x) + \frac1{20}$ from the bound for
$\Sigma_S$, which add up to $g_1\cos x + h_1\sin x$ plus a constant; and the
constants add up to

```math
\tfrac12 + \tfrac7{20} + \tfrac1{20} - \left(0.5588 + \tfrac{161}{720}\right)\bar R - \tfrac{1073}{5400}\bar\rho = K_1 .
```

So $m_k(v, x, d) \le 0$, contradicting Lemma E.3. $\square$

*Lean:
[`Six.WestTail.scalar_impossible`](../../SquaresInCircles/Six/Tails/West.lean#L413),
[`Six.WestTail.totalThreshold`](../../SquaresInCircles/Six/Tails/West.lean#L382),
[`Six.WestTail.defect`](../../SquaresInCircles/Six/Tails/West.lean#L388),
[`Six.WestTail.minorant_le_defect`](../../SquaresInCircles/Six/Tails/West.lean#L393),
[`Six.WestTail.west_support`](../../SquaresInCircles/Six/Tails/West.lean#L291),
[`Six.WestTail.south_support`](../../SquaresInCircles/Six/Tails/West.lean#L300),
[`Six.WestTail.south_root`](../../SquaresInCircles/Six/Tails/West.lean#L258),
[`Six.WestTail.diagonal_support`](../../SquaresInCircles/Six/Tails/West.lean#L321),
[`Six.WestTail.diagonal_root`](../../SquaresInCircles/Six/Tails/West.lean#L249),
[`Six.WestTail.center_support`](../../SquaresInCircles/Six/Tails/West.lean#L343).*

### Lemma E.5 (the south stress, W on the west side)

Let $\sigma = \pm1$, $0 \le x \le \frac25$ and $v = \sigma x$, let
$\frac{11}{25} \le s \le \frac23$ and $\frac12 \le d \le \frac{11}{14}$, let the
three centres be charts in the ceiling, and let $0 \le c_x \le \bar c$ and
$c_y \le \bar c$. Then the inequality of Lemma E.1 (1) for the west side of $C$,
that of Lemma E.1 (2) for the own axis of $S$ and the two of Lemma E.1 (3) do
not all hold.

*Proof.* Suppose they all hold, and take the weights $\lambda_1 = \frac35$,
$\lambda_2 = 1$, $\lambda_3 = \frac25$, $\lambda_4 = \frac3{10}$. Adding the
four inequalities gives

```math
\lambda_1\tau(v) + \tau(s) + \lambda_3\tau(v + d) + \lambda_4\tau(d - s) \le \Sigma_W + \left(a_S + \lambda_4b_S\right) + \left(Ua_D + Vb_D\right) + \left((\lambda_1 - \sin s)c_x + \cos s\,c_y\right) ,
```

with $\Sigma_W = \lambda_1\cos v\,a_W + (\lambda_1\sin v - \lambda_3)\,b_W$,
$U = \lambda_3\sin(d + v) + \lambda_4\cos(d - s)$ and
$V = \lambda_3\cos(d + v) - \lambda_4\sin(d - s)$.

1. *$W$.* The force on $W$ has the squared length
   $\lambda_1^2 + \lambda_3^2 - 2\lambda_1\lambda_3\sin v$, that is,
   $\frac{13}{25} - \frac{12}{25}\sin v$. By Lemma 9.25 (1) and Lemma A.14, for
   every $c > 0$,

   ```math
   \Sigma_W \le \bar R\,\frac{\frac{13}{25} - \frac{12}{25}\sin v + c^2}{2c} - \tfrac12\left(\lambda_1\cos v + \lambda_3 - \lambda_1\sin v\right) .
   ```

   We take $c = \frac{18}{25}$, except $c = \frac{21}{25}$ when $\sigma = -1$
   and $x > \frac3{20}$: the length runs from about $0.58$ at $v = \frac25$ to
   $0.84$ at $v = -\frac25$, and one tangent is not close enough over the whole
   range (Figure E.3).
2. *$S$.* As $\sqrt{1 + \lambda_4^2} < 1.0441$,
   $a_S + \lambda_4b_S \le 1.0441\bar R - \frac{13}{20}$.
3. *$D$.* As in Lemma E.4,
   $U^2 + V^2 = \frac14 + \frac6{25}\sin(v + s)$, and by Lemma A.14 with
   $c = \frac35$ the length is at most $\frac{61}{120} + \frac15\sin(v + s)$.
   By Lemma 9.25 (1),

   ```math
   Ua_D + Vb_D \le \bar R\left(\tfrac{61}{120} + \tfrac15\sin(v + s)\right) - \tfrac12(U + V) ,
   \qquad U + V = \lambda_3\left(\sin(d + v) + \cos(d + v)\right) + \lambda_4\left(\cos(d - s) - \sin(d - s)\right) .
   ```

4. *$C$.* As $\cos s \ge \frac79 > 0$ and $c_y \le \bar c$,
   $\cos s\,c_y \le \bar c\cos s$; and as $0 \le c_x \le \bar c$,
   $(\lambda_1 - \sin s)c_x \le y(\lambda_1 - \sin s)$ for $y = 0$ (if
   $\lambda_1 \le \sin s$) or $y = \bar c$ (otherwise), as in Lemma 9.26 (4).
   So the work on $C$ is at most $\bar c\cos s + y(\lambda_1 - \sin s)$.

On the left, $\tau(v) = \frac12 + \frac12(\cos x + \sin x)$ exactly, as
$|v| = x \le \frac25$; the other thresholds are at least
$\frac12 + \frac12(\cos t + \sin t)$. Collecting the terms as in Lemma E.4, the
inequalities imply $p(x, s, d) \le 0$, where

```math
\begin{aligned}
p(x, s, d) = 2 &- \tfrac35y - \left(1.0441 + \tfrac{61}{120}\right)\bar R + \tfrac35\cos x + \tfrac35[\sigma = -1]\sin x - \bar R\,\frac{\frac{13}{25} - \frac{12}{25}\sigma\sin x + c^2}{2c} \\
&+ \left(\tfrac12 - \bar c\right)\cos s + \left(\tfrac12 + y\right)\sin s + \tfrac25\left(\cos(d + \sigma x) + \sin(d + \sigma x)\right) + \tfrac3{10}\cos(d - s) - \tfrac{\bar R}5\sin(\sigma x + s) ,
\end{aligned}
```

with $[\sigma = -1]$ equal to $1$ if $\sigma = -1$ and $0$ otherwise. We show
$p > 0$ on the box
$[l, u] \times [\frac{11}{25}, \frac23] \times [\frac12, \frac{11}{14}]$, with
$[l, u] = [0, \frac25]$ for $\sigma = 1$, and $[0, \frac3{20}]$ or
$[\frac3{20}, \frac25]$ for $\sigma = -1$, with the matching $c$.

On these boxes $\frac79 \le \cos s$, $0 \le \sin s \le \frac23$,
$\frac{69}{100} \le \cos d \le 1$ and $\frac{23}{48} \le \sin d \le \frac{71}{100}$
(Lemma A.8), and $\frac{23}{25} \le \cos x$, $0 \le \sin x \le \frac25$. The
function $p$ is a constant plus a first harmonic in each variable, with the
coefficients

- of $\cos x$:
  $\frac35 + \frac25(\cos d + \sin d) - \frac{\bar R}5\sin s \ge \frac35 - \frac{\bar R}5 > 0$;
- of $\sin x$:

  ```math
  \tfrac35[\sigma = -1] + \sigma\left(\tfrac{12\bar R}{50c} + \tfrac25(\cos d - \sin d) - \tfrac{\bar R}5\cos s\right) ,
  ```

  which for $\sigma = 1$ and $c = \frac{18}{25}$ is at least
  $\frac{\bar R}3 - \frac25\cdot\frac2{100} - \frac{\bar R}5 > 0$, and for
  $\sigma = -1$ at least
  $\frac35 - \frac{12\bar R}{50c} - \frac25(1 - \frac{23}{48}) + \frac79\cdot\frac{\bar R}5$,
  which is $0.091\ldots > 0$ for $c = \frac{18}{25}$ and $0.171\ldots > 0$ for
  $c = \frac{21}{25}$;
- of $\cos s$ and $\sin s$:
  $\frac12 - \bar c + \frac3{10}\cos d - \frac{\bar R}5\sigma\sin x \ge 0.387 - 0.34\cdot\frac25 > 0$
  and $\frac12 + y + \frac3{10}\sin d - \frac{\bar R}5\cos x \ge \frac12 - 0.34 > 0$;
- of $\cos d$ and $\sin d$:
  $\frac25(\cos x + \sigma\sin x) + \frac3{10}\cos s \ge 0$ and
  $\frac25(\cos x - \sigma\sin x) + \frac3{10}\sin s \ge 0$, as
  $\cos x > \sin x$.

All the intervals lie in $[0, \frac\pi2]$. By Lemma A.11 (2), one variable at a
time, $p$ is positive on each box once it is positive at the eight corners, for
both values of $y$. Table E.2 lists Taylor lower bounds of the corner values;
they are all positive, which contradicts $p \le 0$. $\square$

| $\sigma$ | $c$ | $x$ | $y$ | $s = \frac{11}{25}$, $d = \frac12$ | $s = \frac{11}{25}$, $d = \frac{11}{14}$ | $s = \frac23$, $d = \frac12$ | $s = \frac23$, $d = \frac{11}{14}$ |
| :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $\pm1$ | $\frac{18}{25}$ | $0$ | $0$ | 0.02257 | 0.02824 | 0.00416 | 0.02907 |
| $\pm1$ | $\frac{18}{25}$ | $0$ | $\bar c$ | 0.00294 | 0.00861 | 0.00623 | 0.03115 |
| $1$ | $\frac{18}{25}$ | $\frac25$ | $0$ | 0.10592 | 0.04765 | 0.10818 | 0.06916 |
| $1$ | $\frac{18}{25}$ | $\frac25$ | $\bar c$ | 0.08628 | 0.02802 | 0.11026 | 0.07124 |
| $-1$ | $\frac{18}{25}$ | $\frac3{20}$ | $0$ | 0.03877 | 0.06801 | 0.01509 | 0.06357 |
| $-1$ | $\frac{18}{25}$ | $\frac3{20}$ | $\bar c$ | 0.01913 | 0.04837 | 0.01716 | 0.06564 |
| $-1$ | $\frac{21}{25}$ | $\frac3{20}$ | $0$ | 0.03658 | 0.06582 | 0.01290 | 0.06138 |
| $-1$ | $\frac{21}{25}$ | $\frac3{20}$ | $\bar c$ | 0.01694 | 0.04618 | 0.01497 | 0.06345 |
| $-1$ | $\frac{21}{25}$ | $\frac25$ | $0$ | 0.03225 | 0.09821 | 0.00334 | 0.08854 |
| $-1$ | $\frac{21}{25}$ | $\frac25$ | $\bar c$ | 0.01262 | 0.07857 | 0.00541 | 0.09061 |

*Table E.2.* Taylor lower bounds of $p$ at the corners of the three boxes of
Lemma E.5, rounded down. At $x = 0$ the value does not depend on $\sigma$.

![Graph over v from -2/5 to 2/5 of the length of the force on W, the square root of 13/25 minus 12/25 sin v, falling from about 0.84 to 0.58, with two dashed tangent lines in sin v: the one at c = 18/25 touches near v = 0 and lies well above the curve at v = -2/5, the one at c = 21/25 touches near v = -0.4; the bound used, the first tangent for v > -3/20 and the second below, is drawn thick; a second panel below shows the excess of each tangent over the length, times 1000](figures/appendix-e/south-tangents.svg)

*Figure E.3.* Lemma E.5 (1): the length $\sqrt{\frac{13}{25} - \frac{12}{25}\sin v}$
of the force on $W$ (blue) and its tangent majorants of Lemma A.14 at
$c = \frac{18}{25}$ and $c = \frac{21}{25}$ (dashed), as functions of $v$, and
below their excess over the length. The proof uses the first for
$v \ge -\frac3{20}$ and the second for $v \le -\frac3{20}$ (thick orange). The
first tangent alone would exceed the
length by $0.0101$ at $v = -\frac25$, which costs $0.017$ in $p$ and makes the
corners of Table E.2 with $\sigma = -1$, $x = \frac25$, $s = \frac23$,
$d = \frac12$ negative.

*Lean:
[`Six.SouthTail.side_impossible`](../../SquaresInCircles/Six/Tails/South.lean#L680),
[`Six.SouthTail.sideProfile`](../../SquaresInCircles/Six/Tails/South.lean#L158),
[`Six.SouthTail.side_positive`](../../SquaresInCircles/Six/Tails/South.lean#L302),
[`Six.SouthTail.sideCenter`](../../SquaresInCircles/Six/Tails/South.lean#L295),
[`Six.SouthTail.side_forms`](../../SquaresInCircles/Six/Tails/South.lean#L172),
[`Six.SouthTail.side_piece_positive`](../../SquaresInCircles/Six/Tails/South.lean#L196),
[`Six.SouthTail.side_lower_le`](../../SquaresInCircles/Six/Tails/South.lean#L251),
[`Six.SouthTail.west_side_support`](../../SquaresInCircles/Six/Tails/South.lean#L139),
[`Six.SouthTail.south_support`](../../SquaresInCircles/Six/Tails/South.lean#L60),
[`Six.SouthTail.diagonal_norm`](../../SquaresInCircles/Six/Tails/South.lean#L83),
[`Six.SouthTail.diagonal_root_upper`](../../SquaresInCircles/Six/Tails/South.lean#L95),
[`Six.SouthTail.diagonal_vertex_support`](../../SquaresInCircles/Six/Tails/South.lean#L103),
[`Six.SouthTail.d_coefficients`](../../SquaresInCircles/Six/Tails/South.lean#L127),
[`Six.center_face`](../../SquaresInCircles/Six/Supports.lean#L275).*

### Lemma E.6 (the south stress, W on its own axis)

Let $0 \le v \le \frac{11}{25}$, $\frac{11}{25} \le s \le \frac23$ and
$\frac12 \le d \le \frac{11}{14}$, let the three centres be charts in the
ceiling with $|b_D| \le \frac{23}{100}$, and let $0 \le c_x \le \bar c$ and
$c_y \le \bar c$. Then the inequalities of Lemma E.1 (1) and (2) for the own
axes of $W$ and $S$ and the two of Lemma E.1 (3) do not all hold.

*Proof.* Suppose they all hold, and take the weights $\lambda_1 = \frac58$,
$\lambda_2 = 1$, $\lambda_3 = \frac25$, $\lambda_4 = \frac3{10}$. The force on
$W$ is
$(\lambda_1, -\lambda_3)$, of length $\sqrt{0.550625} < 0.7421$, so
$\lambda_1a_W - \lambda_3b_W \le 0.7421\bar R - \frac{41}{80}$ by Lemma 9.25 (1);
the work on $S$ is bounded as in Lemma E.5 (2). The work on $C$ is
$(\lambda_1\cos v - \sin s)c_x + (\cos s - \lambda_1\sin v)c_y$, and as
$\cos s - \lambda_1\sin v \ge \frac79 - \frac58\cdot\frac{11}{25} > 0$, the
same argument bounds it by
$\bar c(\cos s - \lambda_1\sin v) + y(\lambda_1\cos v - \sin s)$ with $y = 0$ or
$y = \bar c$. We keep the work $Ua_D + Vb_D$ on $D$, with $U$ and $V$ as in
Lemma E.5. Adding the four inequalities and collecting terms as
before, with $\lambda_1 + 1 + \lambda_3 + \lambda_4 = \frac{93}{40}$, they imply
$q(v, s, d) \le 0$, where

```math
\begin{aligned}
q(v, s, d) = \tfrac{93}{40} &- (0.7421 + 1.0441)\bar R + \tfrac58\left(\tfrac12 - y\right)\cos v + \tfrac58\left(\tfrac12 + \bar c\right)\sin v + \left(\tfrac12 - \bar c\right)\cos s + \left(\tfrac12 + y\right)\sin s \\
&+ \tfrac25\left(\left(\tfrac12 - b_D\right)\cos(d + v) + \left(\tfrac12 - a_D\right)\sin(d + v)\right) + \tfrac3{10}\left(\left(\tfrac12 - a_D\right)\cos(d - s) + \left(\tfrac12 + b_D\right)\sin(d - s)\right) .
\end{aligned}
```

The last two terms are what the thresholds of $W$–$D$ and $D$–$S$ leave after
the work $Ua_D + Vb_D$ is subtracted. We show $q > 0$ in three steps.

1. *A harmonic in $v$ and in $s$.* We have $\frac12 \le a_D \le \rho_0 < 1.113$,
   $|b_D| \le \frac{23}{100}$, $\cos d \ge \frac{69}{100}$, $\sin d \ge 0$, and
   $0.73\sin d + 0.613\cos d \le \sqrt{0.73^2 + 0.613^2} < 0.955$ (Cauchy–Schwarz),
   and the same with $\sin d$ and $\cos d$ exchanged. So the coefficients of
   $\cos v$, $\sin v$, $\cos s$, $\sin s$ in $q$ satisfy

   ```math
   \begin{aligned}
   \tfrac58\left(\tfrac12 - y\right) + \tfrac25\left(\left(\tfrac12 - b_D\right)\cos d + \left(\tfrac12 - a_D\right)\sin d\right) &\ge \tfrac58 \cdot 0.38718 + \tfrac25\left(0.27 \cdot 0.69 - 0.613\right) > 0 , \\
   \tfrac58\left(\tfrac12 + \bar c\right) + \tfrac25\left(-\left(\tfrac12 - b_D\right)\sin d + \left(\tfrac12 - a_D\right)\cos d\right) &\ge 0.38301 - \tfrac25 \cdot 0.955 > 0 , \\
   \tfrac12 - \bar c + \tfrac3{10}\left(\left(\tfrac12 - a_D\right)\cos d + \left(\tfrac12 + b_D\right)\sin d\right) &\ge 0.38718 - \tfrac3{10} \cdot 0.613 > 0 , \\
   \tfrac12 + y + \tfrac3{10}\left(\left(\tfrac12 - a_D\right)\sin d - \left(\tfrac12 + b_D\right)\cos d\right) &\ge \tfrac12 - \tfrac3{10} \cdot 0.955 > 0 .
   \end{aligned}
   ```

   By Lemma A.11 (2), in $s$ and then in $v$, it suffices that $q > 0$ at the
   four corners $(v, s)$ with $v \in \lbrace 0, \frac{11}{25}\rbrace$ and
   $s \in \lbrace\frac{11}{25}, \frac23\rbrace$, for every $d$, $a_D$ and $b_D$.
2. *Three corners.* By the far-vertex support of $D$ as in Lemma E.5 (3),
   $q \ge \hat q$, where $\hat q$ is $q$ with its last two terms replaced by

   ```math
   \tfrac25\left(\cos(d + v) + \sin(d + v)\right) + \tfrac3{10}\cos(d - s) - \tfrac{\bar R}5\sin(v + s) - \tfrac{61}{120}\bar R .
   ```

   In $d$, $\hat q$ is a constant plus a first harmonic with the coefficients
   $\frac25(\cos v + \sin v) + \frac3{10}\cos s \ge 0$ and
   $\frac25(\cos v - \sin v) + \frac3{10}\sin s \ge 0$. At the corners
   $(0, \frac{11}{25})$, $(0, \frac23)$ and $(\frac{11}{25}, \frac23)$, and at
   $d = \frac12$ and $d = \frac{11}{14}$, the Taylor lower bounds of $\hat q$ in
   Table E.3 are positive; by Lemma A.11 (2), $\hat q > 0$ there for all $d$.
3. *The corner $v = s = \frac{11}{25}$.* Here the far vertex is too weak:
   $\hat q$ is negative at $d = \frac{11}{14}$ (about $-0.0067$ for $y = 0$).
   We use instead that the force on $D$ is nearly radial. Let
   $\gamma = \frac{11}{25}$, $A' = \frac25\sin\gamma + \frac3{10}\cos\gamma$
   and $B' = \frac25\cos\gamma + \frac3{10}\sin\gamma$; by Lemma A.8,
   $0.44 \le A' \le 0.45$ and $0.48 \le B' \le 0.49$. Expanding,
   $U = A'\cos d + B'\sin d$ and $V = B'\cos d - A'\sin d$. On
   $[\frac12, \frac{11}{14}]$, $\cos d + \sin d > \frac43$ (a first harmonic,
   checked at the two ends),
   $\frac{69}{100} \le \cos d \le \cos\frac12 < \frac9{10}$ and
   $\frac{23}{48} \le \sin d \le \frac{71}{100}$, so

   ```math
   \begin{aligned}
   U &\ge 0.44(\cos d + \sin d) + 0.04\sin d > \tfrac35 , & U &\le \tfrac25 + \tfrac3{10} = \tfrac7{10} , \\
   V &\ge 0.48 \cdot 0.69 - 0.45 \cdot 0.71 > 0 , & \tfrac25U - V &\ge (0.176 - 0.49)\tfrac9{10} + 0.632 \cdot \tfrac{23}{48} > 0 .
   \end{aligned}
   ```

   So the force lies in the narrow cone of Lemma 9.26 (2), and
   $Ua_D + Vb_D \le \rho_0U + \frac1{160} \le \bar\rho U + \frac1{160}$
   (Figure E.4). With $\frac12 - \bar\rho = -(\frac12 + \bar c)$, this gives
   $q(\gamma, \gamma, d) \ge P(d)$, where

   ```math
   \begin{aligned}
   P(d) = \tfrac{93}{40} &- (0.7421 + 1.0441)\bar R + \left(\tfrac58\left(\tfrac12 - y\right) + \tfrac12 - \bar c\right)\cos\gamma + \left(\tfrac58\left(\tfrac12 + \bar c\right) + \tfrac12 + y\right)\sin\gamma - \tfrac1{160} \\
   &+ \tfrac15\cos(d + \gamma) - \tfrac25\left(\tfrac12 + \bar c\right)\sin(d + \gamma) - \tfrac3{10}\left(\tfrac12 + \bar c\right)\cos(d - \gamma) + \tfrac3{20}\sin(d - \gamma) .
   \end{aligned}
   ```

   Its derivative is

   ```math
   P'(d) = -\tfrac25\left(\left(\tfrac12 + \bar c\right)\cos(d + \gamma) + \tfrac12\sin(d + \gamma)\right) + \tfrac3{10}\left(\tfrac12\cos(d - \gamma) + \left(\tfrac12 + \bar c\right)\sin(d - \gamma)\right) .
   ```

   For $d + \gamma$ in $[\frac{47}{50}, \frac{11}{14} + \frac{11}{25}] \subset [0, \frac\pi2]$
   the first bracket is a first harmonic with nonnegative coefficients, larger
   than $\frac23$ at both ends (its Taylor lower bounds there are $0.7652$ and
   $0.6777$), hence on the interval (Lemma A.11 (2)); and as
   $0 \le d - \gamma \le \frac{11}{14} - \frac{11}{25}$, the second bracket is at
   most $\frac12 + 0.61282 \cdot (\frac{11}{14} - \frac{11}{25}) < 0.712$. So
   $P'(d) < -\frac4{15} + 0.214 < 0$, $P$ is nonincreasing on
   $[\frac12, \frac{11}{14}]$ (Lemma A.1 (2)), and $P(d) \ge P(\frac{11}{14})$,
   whose Taylor lower bound is $0.02633$ for $y = 0$ and $0.01059$ for
   $y = \bar c$.

So $q > 0$ at the four corners, hence everywhere, which contradicts $q \le 0$.
$\square$

| $v$ | $s$ | $y$ | $d = \frac12$ | $d = \frac{11}{14}$ |
| :-: | :-: | :-: | :-: | :-: |
| $0$ | $\frac{11}{25}$ | $0$ | 0.02463 | 0.03030 |
| $0$ | $\frac{11}{25}$ | $\bar c$ | 0.00217 | 0.00784 |
| $0$ | $\frac23$ | $0$ | 0.00622 | 0.03113 |
| $0$ | $\frac23$ | $\bar c$ | 0.00547 | 0.03038 |
| $\frac{11}{25}$ | $\frac23$ | $0$ | 0.06243 | 0.01721 |
| $\frac{11}{25}$ | $\frac23$ | $\bar c$ | 0.06840 | 0.02318 |

*Table E.3.* Taylor lower bounds of $\hat q$ at the three corners of Lemma E.6
(2), rounded down.

![The plane of the components U and V of the force on D, with the narrow cone between the U-axis and the line V = 2U/5, the band of U between 3/5 and 7/10 marked by two vertical lines, and a short blue arc of the force (U(d), V(d)) for d from 1/2 to 11/14 lying inside the shaded part of the band](figures/appendix-e/south-cone.svg)

*Figure E.4.* Lemma E.6 (3): at the corner $v = s = \frac{11}{25}$ the force
$(U, V)$ on $D$, for $\frac12 \le d \le \frac{11}{14}$ (blue arc), lies in the
part $\frac35 \le U \le \frac7{10}$, $|V| \le \frac25U$ of the narrow cone of
Lemma 9.26 (2), where the support exceeds $\rho_0U$ by at most $\frac1{160}$.

*Lean:
[`Six.SouthTail.own_impossible`](../../SquaresInCircles/Six/Tails/South.lean#L641),
[`Six.SouthTail.Own.raw`](../../SquaresInCircles/Six/Tails/South.lean#L339),
[`Six.SouthTail.Own.positive_raw`](../../SquaresInCircles/Six/Tails/South.lean#L613),
[`Six.SouthTail.Own.raw_coefficients`](../../SquaresInCircles/Six/Tails/South.lean#L375),
[`Six.SouthTail.Own.vertexProfile`](../../SquaresInCircles/Six/Tails/South.lean#L408),
[`Six.SouthTail.Own.vertex_le_raw`](../../SquaresInCircles/Six/Tails/South.lean#L414),
[`Six.SouthTail.Own.vertex_corner`](../../SquaresInCircles/Six/Tails/South.lean#L438),
[`Six.SouthTail.west_own_support`](../../SquaresInCircles/Six/Tails/South.lean#L69),
[`Six.SouthTail.Own.force_rotation`](../../SquaresInCircles/Six/Tails/South.lean#L484),
[`Six.SouthTail.Own.rotation_bounds`](../../SquaresInCircles/Six/Tails/South.lean#L490),
[`Six.SouthTail.Own.force_cone`](../../SquaresInCircles/Six/Tails/South.lean#L512),
[`Six.narrow_support`](../../SquaresInCircles/Six/Supports.lean#L223),
[`Six.SouthTail.Own.specialTerm`](../../SquaresInCircles/Six/Tails/South.lean#L537),
[`Six.SouthTail.Own.specialFirst`](../../SquaresInCircles/Six/Tails/South.lean#L540),
[`Six.SouthTail.Own.special_derivative_nonpositive`](../../SquaresInCircles/Six/Tails/South.lean#L554),
[`Six.SouthTail.Own.specialValue`](../../SquaresInCircles/Six/Tails/South.lean#L576),
[`Six.SouthTail.Own.raw_special_corner`](../../SquaresInCircles/Six/Tails/South.lean#L580).*

*Proof of Proposition 9.47.* By
[Proposition 9.45](09-six.md#proposition-945-the-wings) both wings hold: $W$ and
$D$ are separated along $e^W_2$, and $D$ and $S$ along $e^S_2$. By Lemma E.2 (1),
$\frac12 \le d \le \frac{11}{14}$.

*The west tail.* Let $W$ be separated from $C$ along its own axis. If $W$ is
also separated from $C$ along the west side, then $|w| < \frac25$ by Lemma E.2
(3), and $w > -\frac{11}{25}$. Otherwise $W$ is on its own axis
([Definition 9.34](09-six.md#definition-934-normalized-packing)); suppose
$v = -w \ge \frac{11}{25}$. Then $\frac{11}{25} \le v < \frac23$. If $S$ is on
its own axis, it is separated from $C$ along it, $s > 0$ and
$s < \frac{24}{25} - v \le \frac{13}{25} < \frac35$ by Lemma E.2 (2); otherwise
$S$ is separated from $C$ along the south side and $|s| < \frac25$ by Lemma E.2
(3). In both cases Lemma E.1 and Lemma E.4 give a contradiction. So
$w > -\frac{11}{25}$.

*The south tail.* Let $S$ be separated from $C$ along its own axis. If $S$ is
also separated along the south side, $|s| < \frac25$. Otherwise $S$ is on its
own axis; suppose $s \ge \frac{11}{25}$, so $\frac{11}{25} \le s < \frac23$. If
$W$ is on its matching side, it is separated from $C$ along the west side, with
$|v| < \frac25$, and Lemma E.5 gives a contradiction. If $W$ is on its own axis,
it is separated from $C$ along it, $v > 0$ by Lemma E.2 (2), and
$v < \frac{11}{25}$ by the west tail just proved; as
$|b_D| < \frac9{40} < \frac{23}{100}$ (Lemma E.2 (4)) and
$c \in [0, c_0]^2 \subset [0, \bar c]^2$, Lemma E.6 gives a contradiction. So
$s < \frac{11}{25}$. $\square$

*Lean:
[`Six.WestTail.own_west_bound`](../../SquaresInCircles/Six/Tails/West.lean#L451),
[`Six.SouthTail.own_south_bound`](../../SquaresInCircles/Six/Tails/South.lean#L723),
[`Six.wing_separators`](../../SquaresInCircles/Six/Wings/Separators.lean#L133).*

## E.2 Proof of Proposition 9.50

In this section a facet $f$ and the kinds of $N$ and $W$ (on its own axis, or on
its matching side) are fixed, and $\Pi$, $F_N$, $F_W$, $\phi_f$, $\psi_f$, $V$,
$B_f$ and $P$ are as in
[Definition 9.48](09-six.md#definition-948-the-value-of-a-pair). The facets
$-e^W_1$ and $-e^N_2$ are the facets *of the model*. We write
$\mathcal D = [n_-, n_+] \times [w_-, w_+]$ for the domain of the pair of
Proposition 9.50, $q = n - w$, and

```math
G(n, w) = \Pi(n, w) - \beta_* - \ell(w) - \tfrac1{1000}|n|
```

for the *gap*; Proposition 9.50 says that $G \ge 0$ on $\mathcal D$. The proof
has three parts. On each of the regions into which the lines $n = 0$, $w = 0$
and $n = w$ cut $\mathcal D$, the gap is a sum of first harmonics, linear terms
and the lengths of two forces (Lemma E.7); along a line in $n$, a line in $w$,
or the diagonal $n = w$, each force is a constant vector plus a turning one, and
Lemma A.13 bounds the curvature of its length, so the gap is concave there
(Lemma E.11). A function with this property is nonnegative on the rectangle once
it is nonnegative at finitely many points (Lemma E.12); and at those points the
gap is evaluated with Taylor polynomials and rational constants, with an error
of at most $5 \cdot 10^{-4}$ (Lemmas E.13 to E.16).

We use the brackets $0.3687847 < r_* < 0.3687848$,
$0.8896968 < m_* < 0.889697$, $0.07097 < \beta_* < 0.07098$ and
$1.258 < K_* < 1.259$, which follow from those of $h$, $s_*$ and $t_*$ in
Lemma 9.2 (1), as $r_* = (s_* + \frac12)/(s_* + \frac32)$ is increasing in
$s_*$ and $m_* = (1 + r_*)(t_* + \frac12)/(\frac32 - s_*)$ is increasing in
$s_*$ and in $t_*$; and $1.68854 < R_6 < 1.68855$, $R_6^2 = q_* < Q_0$,
$1.11281 < \rho_* < \rho_0 < \bar\rho$ and $0.11281 < c_0 < \bar c$
(Lemmas 9.2 and 9.5).

### Lemma E.7 (the gap on a sector)

On $\mathcal D$, $-\frac3{10} \le n \le \frac5{12}$,
$-\frac{11}{25} \le w \le \frac25$ and $-\frac7{10} \le n - w \le \frac67$; in
particular the cosines of $n$, $w$ and $n - w$ are positive. A *sector* is a
choice of signs $\epsilon_n, \epsilon_w, \epsilon_q \in \lbrace 1, -1\rbrace$,
and $(n, w)$ lies in it if $\epsilon_nn \ge 0$, $\epsilon_ww \ge 0$ and
$\epsilon_q(n - w) \ge 0$. Write $\epsilon^+ = \frac12(1 + \epsilon)$ and
$\epsilon^- = \frac12(1 - \epsilon)$, and $[\cdot]$ for a bracket that is $1$ if
its condition holds and $0$ otherwise. On the part of $\mathcal D$ in a sector,

```math
G(n, w) = \Gamma + H_N(n) + H_W(w) + H_Q(n - w) - \lambda_ww - \tfrac{\epsilon_n}{1000}n - R_f|F_N| - R_6|F_W| , \tag{E.1}
```

where $R_f = R_6$ for the facets of the model and $R_f = \rho_*$ for the other
two, $\lambda_w = -\frac{13}{50}$ if $\epsilon_w = 1$ and
$\lambda_w = -\frac{18}{25}$ if $\epsilon_w = -1$, each $H_X$ is a first harmonic
$H_X(t) = \mu_X\cos t + \nu_X\sin t$ with the coefficients

| | $\mu_X$ | $\nu_X$ |
| --- | :-: | :-: |
| $N$ on its own axis | $\frac12 + c_0$ | $\frac12\epsilon_n - c_0\epsilon_n^+$ |
| $N$ on its matching side, $f$ of the model | $1$ | $\epsilon_n^+$ |
| $N$ on its matching side, $f = -e^W_2, e^N_1$ | $\frac12$ | $\frac12\epsilon_n$ |
| $W$ on its own axis | $\frac12$ | $\frac12\epsilon_w - c_0\epsilon_w^+$ |
| $W$ on its matching side | $1$ | $\epsilon_w^+$ |
| $Q$, $f = -e^W_1, -e^N_2$ | $r_*$ | $-r_*\epsilon_q^-$ |
| $Q$, $f = -e^W_2$ | $\frac12r_*$ | $\frac12r_*\epsilon_q$ |
| $Q$, $f = e^N_1$ | $0$ | $-r_*\epsilon_q^-$ |

and the constant is
$\Gamma = 1 + m_* - \beta_* + \frac12[W\text{ own}] - c_0[N\text{ own}] + \Gamma_f$,
with $\Gamma_f = r_* + \frac12[N\text{ own}]$ for the facets of the model,
$\Gamma_f = 0$ for $-e^W_2$ and $\Gamma_f = \frac12r_*$ for $e^N_1$.

*Proof.* The bounds on $n$ and $w$ are those of the four domains, and
$n - w \le \frac5{12} + \frac{11}{25} = \frac{257}{300} < \frac67$,
$n - w \ge -\frac3{10} - \frac25$. So $n$, $w$ and $q = n - w$ lie in
$[-\frac67, \frac67] \subset (-\frac\pi2, \frac\pi2)$, where the cosine is
positive and the sine has the sign of its argument. On the sector, therefore,
$\tau(t) = \frac12 + \frac12(\cos t + \epsilon\sin t)$ and
$\max(\sin t, 0) = \epsilon^+\sin t$ for $t = n, w, q$ with the matching sign,
$|n| = \epsilon_nn$ and $\ell(w) = \lambda_ww$. For a vector $F = (F_1, F_2)$
the linear part of $V(F)$ is $-\frac12(F_1 - F_2)$, and by Definition 9.48,

```math
\Pi = \tau(n) + \tau(w) + r_*\tau(q) + \tfrac12m_* + [f\text{ of the model}]\,\tfrac12\left(F_{N,1} - F_{N,2}\right) + \tfrac12\left(F_{W,1} - F_{W,2}\right) - R_f|F_N| - R_6|F_W| - P ,
```

and the differences of coordinates are, from the table of Definition 9.48,
$\kappa_1 - \kappa_2 = 1$ on the own axis and $\cos t + \sin t$ on the matching
side; $\phi_{f,1} - \phi_{f,2} = \cos q - \sin q$, $\cos q + \sin q$, $1$, $1$
and $\psi_{f,1} - \psi_{f,2} = 1$, $-1$, $-\cos q - \sin q$, $\cos q - \sin q$
for $f = -e^W_1, -e^W_2, e^N_1, -e^N_2$; and
$F_{W,1} - F_{W,2} = \kappa_{W,1} - \kappa_{W,2} + r_*(\psi_{f,1} - \psi_{f,2}) + m_*$.
Collecting the terms in $n$, in $w$, in $q$ and the constants gives (E.1). For
instance, for $f = -e^W_1$ the terms in $q$ are
$\frac12r_*(\cos q + \epsilon_q\sin q)$ from $r_*\tau(q)$ and
$\frac12r_*(\cos q - \sin q)$ from $F_N$, which add up to
$r_*\cos q - r_*\epsilon_q^-\sin q$; and for $N$ on its own axis the penalty
contributes $-c_0\epsilon_n^+\sin n - c_0 + c_0\cos n$. $\square$

*Lean:
[`Six.Stress.Pair.gap`](../../SquaresInCircles/Six/Stress/PairStress.lean#L186),
[`Six.Stress.Pair.Sector`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L35),
[`Six.Stress.Pair.HasSign`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L32),
[`Six.Stress.Pair.sectorGap`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L97),
[`Six.Stress.Pair.gap_eq_sectorGap`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L103),
[`Six.Stress.Pair.constant`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L64),
[`Six.Stress.Pair.aN`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L73),
[`Six.Stress.Pair.bN`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L74),
[`Six.Stress.Pair.aW`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L76),
[`Six.Stress.Pair.bW`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L77),
[`Six.Stress.Pair.aQ`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L78),
[`Six.Stress.Pair.bQ`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L83),
[`Six.Stress.Pair.slope`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L91),
[`Six.Stress.Pair.northRadius`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L94),
[`Six.Stress.Pair.domain_bounds`](../../SquaresInCircles/Six/Stress/PairStress.lean#L172),
[`Six.Stress.Pair.domain_cos_pos`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L38),
[`Six.Stress.Pair.sign_sin`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L49).*

### Lemma E.8 (the harmonics are large)

On the part of $\mathcal D$ in a sector:

1. $H_N(n) \ge \frac12$, and $H_N(n) > \frac9{10}$ if $N$ is on its matching side
   and $f$ is a facet of the model;
2. $H_W(w) \ge \frac12$ if $W$ is on its own axis, and $H_W(w) \ge \frac{23}{25}$
   if $W$ is on its matching side, with $H_W(w) \ge 1$ if moreover $w \ge 0$;
3. $H_Q(q) > \frac{11}{50}$ for the facets of the model, with
   $H_Q(q) > \frac13$ if moreover $W$ is on its matching side and $w \ge 0$;
   $H_Q(q) > \frac9{50}$ for $f = -e^W_2$; and $H_Q(q) \ge 0$ for $f = e^N_1$.

*Proof.* We use $\cos t + |\sin t| \ge 1$ (Lemma A.15 (2)) and
$\cos t \ge 1 - \frac{t^2}2$; on the sector $\epsilon\sin t = |\sin t|$.

(1) On its own axis,

```math
H_N = \tfrac12\left(\cos n + |\sin n|\right) + c_0\left(\cos n - \epsilon_n^+\sin n\right) \ge \tfrac12 + c_0\left(\cos n - |\sin n|\right) \ge \tfrac12 ,
```

as $|n| \le \frac5{12}$ gives $\cos n \ge \frac{263}{288} > \frac5{12} \ge |\sin n|$.
On the matching side with $f$ of the model,
$H_N = \cos n + \epsilon_n^+\sin n \ge \cos n \ge \frac{263}{288} > \frac9{10}$; with
the other facets, $H_N = \frac12(\cos n + |\sin n|) \ge \frac12$.

(2) On its own axis $w \le 0$. If $\epsilon_w = -1$, then
$H_W = \frac12(\cos w - \sin w) = \frac12(\cos w + |\sin w|) \ge \frac12$; if
$\epsilon_w = 1$, then $w = 0$ and $H_W = \frac12$. On the matching side
$|w| \le \frac25$ and
$H_W = \cos w + \epsilon_w^+\sin w \ge \cos w \ge \frac{23}{25}$; for $w \ge 0$,
$H_W = \cos w + \sin w \ge 1$.

(3) For the facets of the model,

```math
H_Q = r_*\left(\cos q + \epsilon_q^-|\sin q|\right) \ge r_*\cos q \ge r_*\left(1 - \tfrac12\left(\tfrac67\right)^2\right) = \tfrac{31}{49}r_* > \tfrac{11}{50} .
```

If $W$ is on its matching side and $w \ge 0$, then either $q \le 0$ and
$H_Q = r_*(\cos q + |\sin q|) \ge r_* > \frac13$, or $0 \le q \le n \le \frac5{12}$ and
$H_Q = r_*\cos q \ge \frac{263}{288}r_* > \frac13$. For $-e^W_2$,
$H_Q = \frac12r_*(\cos q + |\sin q|) \ge \frac12r_* > \frac9{50}$; for $e^N_1$,
$H_Q = r_*\epsilon_q^-|\sin q| \ge 0$. $\square$

*Lean:
[`Six.Stress.Pair.trigN_lower`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L134),
[`Six.Stress.Pair.trigW_lower`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L161),
[`Six.Stress.Pair.trigQ_lower`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L197),
[`Six.Stress.Pair.cos_add_abs_sin`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L128).*

A *line in $n$* is a segment on which $w$ is constant and $n = x$ varies; a
*line in $w$* one on which $n$ is constant and $w = x$ varies; and the
*diagonal* the segment on which $n = w = x$.

### Lemma E.9 (the forces along lines)

Along a line in $n$, a line in $w$ or the diagonal, each of $F_N$ and $F_W$ is
either constant or the sum of a constant vector of length $a$ and a vector of
length $b$ that turns with $x$ at unit speed, as in Table E.4. So its squared
length is $\Lambda(x) = a^2 + b^2 + Q\cos x + T\sin x$ with
$Q^2 + T^2 = 4a^2b^2$, as in Lemma A.13.

| force, facet | kind | line in $n$ | line in $w$ | diagonal |
| --- | --- | :-: | :-: | :-: |
| $F_N$; $-e^W_1$, $-e^W_2$ | own | $1$, $r_*$ | $1$, $r_*$ | const |
| | matching | const | $1$, $r_*$ | $r_*$, $1$ |
| $F_N$; $e^N_1$, $-e^N_2$ | own | const | const | const |
| | matching | $r_*$, $1$ | const | $r_*$, $1$ |
| $F_W$; $-e^W_1$ | own | const | const | const |
| | matching | const | $\sqrt{r_*^2 + m_*^2}$, $1$ | $\sqrt{r_*^2 + m_*^2}$, $1$ |
| $F_W$; $-e^W_2$ | own | const | const | const |
| | matching | const | $m_* - r_*$, $1$ | $m_* - r_*$, $1$ |
| $F_W$; $e^N_1$ | own | $\sqrt{1 + m_*^2}$, $r_*$ | $\sqrt{1 + m_*^2}$, $r_*$ | const |
| | matching | $\sqrt{1 + m_*^2 + 2m_*\sin w}$, $r_*$ | $m_*$, $\sqrt{1 + r_*^2 - 2r_*\sin n}$ | $m_* - r_*$, $1$ |
| $F_W$; $-e^N_2$ | own | $\sqrt{1 + m_*^2}$, $r_*$ | $\sqrt{1 + m_*^2}$, $r_*$ | const |
| | matching | $\sqrt{1 + m_*^2 + 2m_*\sin w}$, $r_*$ | $m_*$, $\sqrt{1 + r_*^2 + 2r_*\cos n}$ | $\sqrt{r_*^2 + m_*^2}$, $1$ |

*Table E.4.* The forces along the lines: "const" if the force is constant,
otherwise the lengths $a$ of the constant part and $b$ of the turning part.

*Proof.* With $u(\theta) = (\cos\theta, \sin\theta)$, the vectors of Definition
9.48 are $\kappa(t) = u(-t)$ on the matching side and $(1, 0)$ on the own axis;
$\phi_f(q) = u(-\frac\pi2 - q)$, $u(-q)$, $(1, 0)$, $(0, -1)$ and
$\psi_f(q) = (1, 0)$, $(0, 1)$, $u(\frac\pi2 + q)$, $u(q)$ for
$f = -e^W_1, -e^W_2, e^N_1, -e^N_2$. Along a line in $n$, $u(-n)$ and every
$u(-q + \theta)$ turn at the speed $-1$, and every $u(q + \theta)$ at the speed
$1$; along a line in $w$, $u(-w)$ and every $u(q + \theta)$ turn at the speed
$-1$, and every $u(-q + \theta)$ at the speed $1$; along the diagonal $q = 0$
and only $\kappa$ turns. Vectors that turn at the same
speed add up to one turning vector of constant length; the rest is constant.
For example, along a line in $w$ with $W$ on its matching side and $f = e^N_1$,

```math
F_W = u(-w) + r_*u\left(\tfrac\pi2 + n - w\right) - (0, m_*) ,
```

and the first two terms turn together, with
$|1 + r_*u(\frac\pi2 + n)|^2 = 1 + r_*^2 - 2r_*\sin n$; along a line in $n$
with $N$ on its matching side and $f = -e^W_1$,
$F_N = u(-n) + r_*u(-n + w - \frac\pi2)$ has the constant length
$\sqrt{1 + r_*^2 + 2r_*\sin w}$. The other entries are found in the same way.
Finally $|c + b\,u(\pm x + \theta)|^2 = a^2 + b^2 + 2ab\cos(\pm x + \theta - \theta_c)$
for a vector $c$ of length $a$ and direction $\theta_c$, which is of the stated
form. $\square$

*Lean:
[`Six.Stress.Pair.Sweep`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L240),
[`Six.Stress.Pair.Harmonic`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L257),
[`Six.Stress.Pair.northHarmonic`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L273),
[`Six.Stress.Pair.westHarmonic`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L300),
[`Six.Stress.Pair.northHarmonic_arg`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L336),
[`Six.Stress.Pair.westHarmonic_arg`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L345),
[`Six.Stress.Pair.northHarmonic_amplitude`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L354),
[`Six.Stress.Pair.westHarmonic_amplitude`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L360).*

![Two panels in the frame of W. Left: as w runs over a line, the force F_W on W on its matching side for the facet -e^W_1 is the constant vector (r*, -m*) plus a turning unit vector, whose tip runs on an arc of the unit circle about the end of the constant vector; the length runs from 1.38 to 1.82. Right: along a line in n for the facet e^N_1 with W on its own axis, F_W is the constant vector (1, -m*) plus a short turning vector of length r* that points against it, its tip on an arc of a small circle](figures/appendix-e/pair-turning.svg)

*Figure E.5.* Lemma E.9 in the frame of $W$, for $n = 0$. Left: along a line in
$w$, with $W$ on its matching side and $f = -e^W_1$,
$F_W = (r_*, -m_*) + u(-w)$; the dots mark $w = -\frac25, 0, \frac25$. Right:
along a line in $n$, with $W$ on its own axis and $f = e^N_1$,
$F_W = (1, -m_*) + r_*u(\frac\pi2 + n - w)$ for $w = -\frac15$; the turning part
points against the constant part, which is the case (3) of Lemma A.13, so
$-R_6|F_W|$ is concave there.

### Lemma E.10 (curvature of the forces)

Along a segment in $\mathcal D$ of a line in $n$, a line in $w$ or the
diagonal, the second derivatives in $x$ of $-R_f|F_N|$ and of $-R_6|F_W|$ exist
and satisfy:

1. that of $-R_f|F_N|$ is at most $\frac{23}{50}$; it is $0$ where $F_N$ is
   constant in Table E.4; and along a line in $w$ with $f = -e^W_1$, at the
   points where $w \le 0$, it is at most $\frac3{10}$;
2. that of $-R_6|F_W|$ is at most $\chi_W$, given by the table (the entries
   $0$ are where $F_W$ is constant, except for $e^N_1$ along a line in $n$)

   | facet | line in $n$ | line in $w$, own | line in $w$, matching | diagonal, own | diagonal, matching |
   | --- | :-: | :-: | :-: | :-: | :-: |
   | $-e^W_1$ | $0$ | $0$ | $\frac{21}{25}$ | $0$ | $\frac{21}{25}$ |
   | $-e^W_2$ | $0$ | $0$ | $\frac35$ | $0$ | $\frac{21}{25}$ |
   | $e^N_1$ | $0$ | $\frac12$ | $\frac9{10}$ | $0$ | $\frac{21}{25}$ |
   | $-e^N_2$ | $\frac35$ | $\frac12$ | $1$ | $0$ | $\frac{21}{25}$ |

*Proof.* On $\mathcal D$ both forces have a first coordinate larger than
$\frac12$: $F_{N,1} \ge \cos n - r_* > \frac9{10} - \frac{37}{100}$ and
$F_{W,1} \ge \cos w - r_* > \frac9{10} - \frac{37}{100}$. So $\Lambda > 0$ and
Lemma A.13 (2) applies: the second derivative of $-R\sqrt\Lambda$ is
$R\,(L^4 - (a^2 - b^2)^2)/(4L^3)$, with $L = \sqrt\Lambda$, and is at most
$R\,\frac{ab}{a + b}$. The function $\frac{ab}{a + b}$ increases in $a$ and in
$b$, and $R \le R_6 < \frac{17}{10}$ (also for $R = \rho_*$). With upper bounds
$\bar a$, $\bar b$ for $a$, $b$, the second derivative is at most
$\frac{17}{10}\,\frac{\bar a\bar b}{\bar a + \bar b}$.

(1) For $F_N$, Table E.4 gives $\lbrace a, b\rbrace = \lbrace 1, r_*\rbrace$, and
$\frac{17}{10}\cdot\frac{0.37}{1.37} < 0.4592 < \frac{23}{50}$. For the last
claim, along a line in $w$ with $f = -e^W_1$ the squared length is
$1 + r_*^2 + 2r_*\langle\kappa_N(n), \phi_f(q)\rangle$. The inner product is
$-\sin(n - w) \le \frac3{10}$ for $N$ on its own axis, as
$n - w \ge n \ge -\frac3{10}$ where $w \le 0$, and $\sin w \le 0$ for $N$ on its
matching side. So
$L^2 \le 1 + r_*^2 + \frac35r_* < (\frac76)^2$, while
$(a^2 - b^2)^2 = (1 - r_*^2)^2 \ge (\frac{43}{50})^2$. As
$L \mapsto L - D/L^3$ increases for $D \ge 0$, the second derivative is at most
$\frac{R_6}4\left(\frac76 - (\frac{43}{50})^2(\frac67)^3\right) < 0.296 < \frac3{10}$.

(2) The entries of Table E.4 are bounded as follows:
$\sqrt{1 + m_*^2 + 2m_*\sin w} \le \sqrt{1 + m_*^2 + \frac45m_*} < \frac85$
and $\sqrt{1 + m_*^2} < \frac{27}{20}$ against $r_* < \frac{37}{100}$;
$\sqrt{r_*^2 + m_*^2} < \frac{97}{100}$ and $m_* - r_* < \frac{21}{40}$ against
$1$; and $m_* < \frac9{10}$ against $\sqrt{1 + r_*^2 + \frac35r_*} < \frac76$
(as $\sin n \ge -\frac3{10}$) and $1 + r_* < \frac{137}{100}$. The corresponding
values of $\frac{17}{10}\frac{\bar a\bar b}{\bar a + \bar b}$ are $0.511 < \frac35$,
$0.494 < \frac12$, $0.838 < \frac{21}{25}$, $0.586 < \frac35$, $0.864 < \frac9{10}$
and $0.924 < 1$. It remains to treat $f = e^N_1$ along a line in $n$, where the
entry is $0$. There the constant part is $c = (1, -m_*)$ on the own axis and
$c = \kappa_W(w) - (0, m_*)$ on the matching side, and the turning part is
$r_*\psi_f(q) = r_*(-\sin q, \cos q)$. Their inner product is
$-r_*(\sin q + m_*\cos q)$, respectively $-r_*(\sin n + m_*\cos q)$, and it is at
most $-r_*^2$: on the own axis $q \ge n \ge -\frac3{10}$ and, if $q \le 0$,
$|q| \le \frac3{10}$, so $\sin q + m_*\cos q \ge -\frac3{10} + 0.8896\cdot0.955 > r_*$,
while for $q \ge 0$ it is at least $m_*\cdot\frac{31}{49} > r_*$; on the matching
side, if $n \le 0$, then $|q| \le \frac7{10}$ and
$\sin n + m_*\cos q \ge -\frac3{10} + 0.8896\cdot0.755 > r_*$, and if $n \ge 0$ it
is at least $\frac{31}{49}m_* > r_*$. So
$Q\cos x + T\sin x = 2\langle c, r_*\psi_f\rangle \le -2r_*^2$. As
$\Lambda = a^2 + b^2 + Q\cos x + T\sin x > 0$ with $b = r_*$, this also gives
$a > b$, and Lemma A.13 (3), with the roles of $a$ and $b$ exchanged (the lemma
depends on them only through $a^2 + b^2$ and $4a^2b^2$), shows that the second
derivative is at most $0$. $\square$

*Lean:
[`Six.Stress.Pair.north_curvature`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L425),
[`Six.Stress.Pair.north_curvature_zero`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L655),
[`Six.Stress.Pair.north_curvature_westFirst`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L495),
[`Six.Stress.Pair.west_curvature`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L579),
[`Six.Stress.Pair.westCap`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L566),
[`Six.Stress.Pair.west_opposition`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L541),
[`Six.Stress.Pair.Harmonic.curvature_le`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L401),
[`Six.Stress.Pair.Harmonic.curvature_nonpos`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L449),
[`Six.Stress.Pair.harmonicCurvature_le_length`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L467),
[`Six.Stress.Pair.northForce_first`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L368),
[`Six.Stress.Pair.westForce_first`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L377).*

### Lemma E.11 (concavity along lines)

The gap $G$ is concave on every segment of a line in $n$, a line in $w$ or the
diagonal that lies in $\mathcal D$ and in one sector.

*Proof.* On the segment $G$ is given by (E.1). The linear terms have the second
derivative $0$, and a first harmonic satisfies $H'' = -H$ (Lemma A.11 (1)). Along
a line in $n$, $\frac{d^2}{dx^2}H_Q(x - w) = -H_Q(x - w)$; along a line in $w$,
$\frac{d^2}{dx^2}H_Q(n - x) = -H_Q(n - x)$; along the diagonal $H_Q(0)$ is
constant. So the second derivative of $G$ is

```math
-H_N - H_Q + \chi_N + \chi_W , \qquad -H_W - H_Q + \chi_N + \chi_W , \qquad -H_N - H_W + \chi_N + \chi_W
```

along the three kinds of lines, where $\chi_N$ and $\chi_W$ are the second
derivatives of $-R_f|F_N|$ and $-R_6|F_W|$. Table E.5 bounds the three terms by
Lemmas E.8 and E.10; the sum is at most $0$ in every case, and Lemma A.10 (1)
gives the concavity. $\square$

| line | facet | kind | $-H$ terms | $\chi_N$ | $\chi_W$ | sum at most |
| --- | --- | --- | :-: | :-: | :-: | :-: |
| in $n$ | $-e^W_1$ | any | $-\frac12 - \frac{11}{50}$ | $\frac{23}{50}$ | $0$ | $-\frac{13}{50}$ |
| in $n$ | $-e^W_2$ | any | $-\frac12 - \frac9{50}$ | $\frac{23}{50}$ | $0$ | $-\frac{11}{50}$ |
| in $n$ | $e^N_1$ | any | $-\frac12 - 0$ | $\frac{23}{50}$ | $0$ | $-\frac1{25}$ |
| in $n$ | $-e^N_2$ | $N$ matching | $-\frac9{10} - \frac{11}{50}$ | $\frac{23}{50}$ | $\frac35$ | $-\frac3{50}$ |
| in $n$ | $-e^N_2$ | $N$ own | $-\frac12 - \frac{11}{50}$ | $0$ | $\frac35$ | $-\frac3{25}$ |
| in $w$ | $-e^W_1$ | $W$ matching, $w \le 0$ | $-\frac{23}{25} - \frac{11}{50}$ | $\frac3{10}$ | $\frac{21}{25}$ | $0$ |
| in $w$ | $-e^W_1$ | $W$ matching, $w \ge 0$ | $-1 - \frac13$ | $\frac{23}{50}$ | $\frac{21}{25}$ | $-\frac1{30}$ |
| in $w$ | $-e^W_1$ | $W$ own | $-\frac12 - \frac{11}{50}$ | $\frac{23}{50}$ | $0$ | $-\frac{13}{50}$ |
| in $w$ | $-e^W_2$ | $W$ matching | $-\frac{23}{25} - \frac9{50}$ | $\frac{23}{50}$ | $\frac35$ | $-\frac1{25}$ |
| in $w$ | $-e^W_2$ | $W$ own | $-\frac12 - \frac9{50}$ | $\frac{23}{50}$ | $0$ | $-\frac{11}{50}$ |
| in $w$ | $e^N_1$ | $W$ matching | $-\frac{23}{25} - 0$ | $0$ | $\frac9{10}$ | $-\frac1{50}$ |
| in $w$ | $e^N_1$ | $W$ own | $-\frac12 - 0$ | $0$ | $\frac12$ | $0$ |
| in $w$ | $-e^N_2$ | $W$ matching | $-\frac{23}{25} - \frac{11}{50}$ | $0$ | $1$ | $-\frac7{50}$ |
| in $w$ | $-e^N_2$ | $W$ own | $-\frac12 - \frac{11}{50}$ | $0$ | $\frac12$ | $-\frac{11}{50}$ |
| diagonal | any | $W$ matching | $-\frac12 - \frac{23}{25}$ | $\frac{23}{50}$ | $\frac{21}{25}$ | $-\frac3{25}$ |
| diagonal | any | $W$ own | $-\frac12 - \frac12$ | $\frac{23}{50}$ | $0$ | $-\frac{27}{50}$ |

*Table E.5.* The second derivative of the gap along the lines, by Lemmas E.8
and E.10. In the first column of bounds, the first term bounds $-H_N$ or $-H_W$
and the second $-H_Q$ (or $-H_W$ on the diagonal).

*Lean:
[`Six.Stress.Pair.sweepCurvature`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L662),
[`Six.Stress.Pair.sweepCurvature_nonpos`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L672),
[`Six.Stress.Pair.sweepGap_eq`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L772),
[`Six.Stress.Pair.sweepGap_deriv`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L780),
[`Six.Stress.Pair.sweepGapD_deriv`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L797),
[`Six.Stress.Pair.gap_sweep_concave`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L818).*

### Lemma E.12 (sweeping a rectangle)

Let $\mathcal R = [n_-, n_+] \times [w_-, w_+]$ contain the origin, let
$z_- = \max(n_-, w_-)$ and $z_+ = \min(n_+, w_+)$, and let $g$ be a function on
$\mathcal R$ that is concave on every segment in $\mathcal R$ of a line in $n$,
a line in $w$ or the diagonal on which each of $n$, $w$ and $n - w$ keeps one
sign. If $g \ge 0$ at the points $(x, y)$ with $x \in \lbrace n_-, 0, n_+\rbrace$
and $y \in \lbrace w_-, 0, w_+\rbrace$ and at $(z_-, z_-)$ and $(z_+, z_+)$, then
$g \ge 0$ on $\mathcal R$.

*Proof.* (a) *One variable.* Let $l \le r$ and $k$ be real, and let $f$ be a
function on $[l, r]$ that is concave on every closed interval on which neither
$y$ nor $y - k$ changes sign. If $f \ge 0$ at $l$ and $r$, and at $0$ and at $k$
when these lie in $[l, r]$, then $f \ge 0$ on $[l, r]$: the points $0$ and $k$
cut $[l, r]$ into at most three closed intervals of this kind, whose ends are
among $l$, $r$, $0$ and $k$, and a concave function on an interval is at least
the smaller of its two end values.

(b) *The diagonal.* On $[z_-, z_+]$ the function $z \mapsto g(z, z)$ is concave
on each side of $0$ (where $n - w = 0$ keeps its sign), and (a) with $k = 0$
gives $g(z, z) \ge 0$ for $z_- \le z \le z_+$.

(c) *Three lines in $w$.* Let $x \in \lbrace n_-, 0, n_+\rbrace$. On $[w_-, w_+]$
the function $y \mapsto g(x, y)$ is concave on every interval on which $y$ and
$x - y$ keep their signs, so (a) applies with $k = x$. Its values at $w_-$, $0$
and $w_+$ are nonnegative by hypothesis, and at $y = x$, if $x \in [w_-, w_+]$,
by (b), since then $z_- \le x \le z_+$. So $g(x, y) \ge 0$ on the three lines.

(d) *All lines in $n$.* Let $y \in [w_-, w_+]$. On $[n_-, n_+]$ the function
$x \mapsto g(x, y)$ is concave on every interval on which $x$ and $x - y$ keep
their signs, and (a) applies with $k = y$: its values at $n_-$, $0$ and $n_+$
are nonnegative by (c), and at $x = y$, if $y \in [n_-, n_+]$, by (b).
$\square$

*Lean:
[`Six.Stress.Pair.two_wall_nonneg`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L33),
[`Six.Stress.Pair.rectangle_nonneg`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L78),
[`Six.Stress.Pair.exists_hasSign`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L22).*

![Four rectangles, one for each choice of N and W on their own axes or matching sides, in the plane of n (horizontal) and w (vertical): each is cut by the lines n = 0, w = 0 and n = w into sign sectors; the diagonal segment is drawn thick, three vertical segments at n = n-, 0, n+ in blue, and one horizontal segment in orange with small marks where it crosses n = 0 and n = w; black dots mark the corner and axis points and the two ends of the diagonal](figures/appendix-e/pair-domain.svg)

*Figure E.6.* The domains of the pair, cut into sectors by the lines $n = 0$,
$w = 0$ and $n = w$, and the order of Lemma E.12: the diagonal (thick), the three
lines in $w$ (blue), then any line in $n$ (orange), each concave between the
marks where it crosses the sector boundaries. The gap is checked at the dots.
When $W$ is on its own axis, $w_+ = 0$ and only six of the nine corner and axis
points are distinct.

At finitely many points we compare the gap with an approximation in which the
sine and the cosine are polynomials and the constants are decimals. The bounds of
Lemma A.7 have two more terms of the same kind.

### Lemma E.13 (Taylor bounds of degrees 8 and 9)

For $t \ge 0$, $\cos t \le C_6(t) + \frac{t^8}{40320}$ and
$\sin t \le S_7(t) + \frac{t^9}{362880}$. Hence, for $|t| \le \frac67$,
$|\cos t - C_6(t)| \le 10^{-5}$ and $|\sin t - S_7(t)| \le 10^{-5}$.

*Proof.* Let $g_8(t) = C_6(t) + \frac{t^8}{40320} - \cos t$ and
$g_9(t) = S_7(t) + \frac{t^9}{362880} - \sin t$. Then $g_8(0) = g_9(0) = 0$,
$g_9' = g_8$, and $g_8'(t) = \sin t - S_7(t) \ge 0$ for $t \ge 0$ by Lemma A.7
(4). By [Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative)
(3), $g_8 \ge 0$ and then $g_9 \ge 0$ on $[0, \infty)$. For $0 \le t \le \frac67$
this gives $0 \le \cos t - C_6(t) \le (\frac67)^8/40320 < 7.3 \cdot 10^{-6}$ and
$0 \le \sin t - S_7(t) \le (\frac67)^9/362880 < 7 \cdot 10^{-7}$, with Lemma A.7;
for $-\frac67 \le t \le 0$ use that $C_6$ is even and $S_7$ odd. $\square$

*Lean:
[`Six.Stress.Pair.cos_upper_eight`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L28),
[`Six.Stress.Pair.sin_upper_nine`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L37),
[`Six.Stress.Pair.trig_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L47).*

### Definition E.14 (the approximate gap)

Let $\tilde r = 0.36878$, $\tilde m = 0.8897$ and $\tilde\beta = 0.071$. The
*approximation* of a quantity of Definition 9.48 is obtained by replacing $\cos t$ and
$\sin t$ by $C_6(t)$ and $S_7(t)$, $r_*$, $m_*$ and $c_0$ by $\tilde r$,
$\tilde m$ and $\bar c$, and $\beta_*$ by $\tilde\beta$; we mark it with a
tilde. So $\tilde\kappa(t) = (C_6(t), -S_7(t))$ on the matching side,
$\tilde\tau(t) = \frac12 + \frac12(|C_6(t)| + |S_7(t)|)$,
$\tilde F_N = \tilde\kappa_N(n) + \tilde r\tilde\phi_f(q)$,
$\tilde F_W = \tilde\kappa_W(w) + \tilde r\tilde\psi_f(q) - (0, \tilde m)$, and
$\tilde P$ is $P$ with $c_0$, $\sin$, $\cos$ replaced. The *approximate gap* is

```math
\tilde G(n, w) = E - \sqrt{S_f|\tilde F_N|^2} - \sqrt{Q_0|\tilde F_W|^2} ,
```

where $S_f = Q_0$ for the facets of the model and $S_f = \bar\rho^2$ for the
other two, and

```math
E = \tilde\tau(n) + \tilde\tau(w) + \tilde r\,\tilde\tau(q) + \tfrac12\tilde m + [f\text{ of the model}]\,\tfrac12\left(\tilde F_{N,1} - \tilde F_{N,2}\right) + \tfrac12\left(\tilde F_{W,1} - \tilde F_{W,2}\right) - \tilde P - \tilde\beta - \ell(w) - \tfrac1{1000}|n| .
```

At a rational point, $E$, $S_f|\tilde F_N|^2$ and $Q_0|\tilde F_W|^2$ are
rational numbers.

*Lean:
[`Six.Stress.Pair.rA`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L72),
[`Six.Stress.Pair.mA`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L73),
[`Six.Stress.Pair.baseA`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L75),
[`Six.Stress.Pair.centralP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L80),
[`Six.Stress.Pair.northP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L82),
[`Six.Stress.Pair.westP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L88),
[`Six.Stress.Pair.northForceP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L94),
[`Six.Stress.Pair.westForceP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L97),
[`Six.Stress.Pair.widthP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L100),
[`Six.Stress.Pair.penaltyP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L102),
[`Six.Stress.Pair.linearP`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L108),
[`Six.Stress.Pair.scaleSq`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L115).*

### Lemma E.15 (the error budget)

On $\mathcal D$, $G(n, w) \ge \tilde G(n, w) - 4.52 \cdot 10^{-4}$. In
particular $G(n, w) > 0$ wherever $\tilde G(n, w) > 5 \cdot 10^{-4}$, and this
holds at a rational point if, with $E' = E - 5 \cdot 10^{-4}$,
$X = S_f|\tilde F_N|^2$ and $Y = Q_0|\tilde F_W|^2$,

```math
E' > 0, \qquad X + Y < E'^2, \qquad 4XY < \left(E'^2 - X - Y\right)^2 . \tag{E.2}
```

*Proof.* On $\mathcal D$ the angles $n$, $w$, $q$ lie in $[-\frac67, \frac67]$
(Lemma E.7), so each sine and cosine is within $10^{-5}$ of its approximation
(Lemma E.13), and $|r_* - \tilde r|$, $|m_* - \tilde m|$, $|c_0 - \bar c|$ are
below $10^{-5}$ by the brackets above. We add up the errors.

1. *Forces.* Each coordinate of $\kappa$, $\phi_f$, $\psi_f$ is within $10^{-5}$
   of its approximation and at most $1$ in absolute value; so
   $|r_*x - \tilde rX| \le |r_* - \tilde r|\,|x| + \tilde r\,|x - X| < 2 \cdot 10^{-5}$,
   and each coordinate of $F_N$ and $F_W$ is within
   $10^{-5} + 2 \cdot 10^{-5} + 10^{-5} = 4 \cdot 10^{-5}$ of its approximation
   (the last term from $m_*$).
2. *Lengths.* If $|x - X|, |y - Y| \le \eta$ and $L = \sqrt{X^2 + Y^2}$, then
   $x^2 + y^2 \le L^2 + 2(|X| + |Y|)\eta + 2\eta^2 \le (L + 2\eta)^2$, as
   $|X|, |Y| \le L$. So $|F| \le |\tilde F| + 8 \cdot 10^{-5}$ for both forces.
   For $0 \le R \le \frac{17}{10}$ and $R^2 \le S$ this gives
   $R|F| \le \sqrt{S|\tilde F|^2} + 1.36 \cdot 10^{-4}$; we use it with
   $(R, S) = (R_6, Q_0)$ and $(\rho_*, \bar\rho^2)$.
3. *Linear parts.* For each force,
   $\frac12|(F_1 - F_2) - (\tilde F_1 - \tilde F_2)| \le 4 \cdot 10^{-5}$.
4. *Thresholds.* $|\tau(t) - \tilde\tau(t)| \le 10^{-5}$, as
   $||\alpha| - |\alpha'|| \le |\alpha - \alpha'|$; with $\tau \le \frac32$,
   $|r_*\tau(q) - \tilde r\tilde\tau(q)| < 1.5 \cdot 10^{-5} + 0.37 \cdot 10^{-5}$;
   and $\frac12|m_* - \tilde m| < 0.5 \cdot 10^{-5}$. In all, at most
   $5 \cdot 10^{-5}$.
5. *Penalty.* As $|\max(\alpha, 0) - \max(\alpha', 0)| \le |\alpha - \alpha'|$ and
   $0 \le \max(\sin n, 0) + 1 - \cos n \le 2$, the two terms of $P$ are within
   $2 \cdot 10^{-5} + 0.2 \cdot 2 \cdot 10^{-5}$ and
   $10^{-5} + 0.2 \cdot 10^{-5}$ of their approximations; at most
   $5 \cdot 10^{-5}$ in all.
6. *Base.* $\beta_* < \tilde\beta$.

So

```math
G \ge \tilde G - 2\left(1.36 \cdot 10^{-4} + 4 \cdot 10^{-5}\right) - 5 \cdot 10^{-5} - 5 \cdot 10^{-5} = \tilde G - 4.52 \cdot 10^{-4} .
```

For the last claim: if (E.2) holds, then
$2\sqrt{XY} < E'^2 - X - Y$, so $(\sqrt X + \sqrt Y)^2 < E'^2$ and
$\sqrt X + \sqrt Y < E'$, that is, $\tilde G > 5 \cdot 10^{-4}$. $\square$

*Lean:
[`Six.Stress.Pair.gap_ge_model`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L310),
[`Six.Stress.Pair.constants_close`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L170),
[`Six.Stress.Pair.normal_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L180),
[`Six.Stress.Pair.product_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L157),
[`Six.Stress.Pair.force_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L198),
[`Six.Stress.Pair.length_le`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L131),
[`Six.Stress.Pair.scaled_length_le`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L163),
[`Six.Stress.Pair.width_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L229),
[`Six.Stress.Pair.threshold_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L238),
[`Six.Stress.Pair.penalty_error`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L263),
[`Six.Stress.Pair.two_roots_lt`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L147),
[`Six.Stress.Pair.gap_pos_of_check`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L340),
[`Six.Stress.Pair.ModelCheck`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L119).*

### Lemma E.16 (the vertices)

For each facet and each choice of the kinds of $N$ and $W$, the gap is positive
at the points of Lemma E.12 for the domain of the pair, except at the origin for
the facets of the model, where it is $0$.

*Proof.* At the origin, for a facet of the model, $F_N = (1, -r_*)$,
$F_W = (1 + r_*, -m_*)$, $P = 0$ and $\tau(0) = 1$. These are the forces of
the stress of the model on $N$ and $W$, in their frames, whose works on the
centres equal their far-vertex bounds (Proposition 9.27 (2)): with the centres
at
$(a, b) = (s_* + 1, -s_*)$ in the frame of $N$ and $(1 - s_*, -t_*)$ in that of
$W$, $V(F_N) = 1 + s_* + r_*s_*$ and
$V(F_W) = (1 + r_*)(1 - s_*) + m_*t_*$. So

```math
\Pi(0, 0) = 2 + r_* + \tfrac12m_* - (1 + s_* + r_*s_*) - (1 + r_*)(1 - s_*) - m_*t_* = m_*\left(\tfrac12 - t_*\right) = \beta_* ,
```

and $G(0, 0) = 0$. At the other points, including the origin for the facets
$-e^W_2$ and $e^N_1$, (E.2) holds; we checked it in exact rational arithmetic.
Table E.6 lists the approximate gap $\tilde G$ at all these points; every entry
exceeds $5 \cdot 10^{-4}$, and Lemma E.15 gives $G > 0$. $\square$

| $n$ | $w$ | $N$ | $W$ | $-e^W_1$ | $-e^W_2$ | $e^N_1$ | $-e^N_2$ |
| :-: | :-: | :-: | :-: | :-: | :-: | :-: | :-: |
| $-\frac3{10}$ | $-\frac{11}{25}$ | own | own | 0.04846 | 0.07147 | 0.11829 | 0.01656 |
| $-\frac3{10}$ | $-\frac25$ | own | side | 0.23112 | 0.18099 | 0.22306 | 0.19650 |
| $-\frac3{10}$ | $0$ | own | either | 0.04748 | 0.25577 | 0.12811 | 0.13054 |
| $-\frac3{10}$ | $\frac25$ | own | side | 0.03108 | 0.47540 | 0.17094 | 0.17306 |
| $-\frac14$ | $-\frac{11}{25}$ | side | own | 0.07948 | 0.09276 | 0.13975 | 0.03330 |
| $-\frac14$ | $-\frac25$ | side | side | 0.26216 | 0.19916 | 0.25017 | 0.20759 |
| $-\frac14$ | $0$ | side | either | 0.04840 | 0.22377 | 0.13818 | 0.12809 |
| $-\frac14$ | $\frac25$ | side | side | 0.00565 | 0.41342 | 0.18483 | 0.17643 |
| $0$ | $-\frac{11}{25}$ | either | own | 0.08233 | 0.01432 | 0.12333 | 0.00063 |
| $0$ | $-\frac25$ | either | side | 0.26852 | 0.12302 | 0.27246 | 0.14815 |
| $0$ | $0$ | either | either | $0$ | 0.07597 | 0.07597 | $0$ |
| $0$ | $\frac25$ | either | side | 0.00351 | 0.28877 | 0.14042 | 0.07570 |
| $\frac14$ | $-\frac{11}{25}$ | side | own | 0.24917 | 0.13645 | 0.29818 | 0.16315 |
| $\frac14$ | $-\frac25$ | side | side | 0.43850 | 0.24767 | 0.50119 | 0.28765 |
| $\frac14$ | $0$ | side | either | 0.20457 | 0.22377 | 0.31872 | 0.16295 |
| $\frac14$ | $\frac25$ | side | side | 0.15604 | 0.36491 | 0.30812 | 0.17022 |
| $\frac5{12}$ | $-\frac{11}{25}$ | own | own | 0.34036 | 0.21131 | 0.29479 | 0.24518 |
| $\frac5{12}$ | $-\frac25$ | own | side | 0.53462 | 0.31970 | 0.53860 | 0.35740 |
| $\frac5{12}$ | $0$ | own | either | 0.32670 | 0.26454 | 0.37088 | 0.24784 |
| $\frac5{12}$ | $\frac25$ | own | side | 0.21728 | 0.31460 | 0.31882 | 0.21487 |
| $-\frac3{10}$ | $-\frac3{10}$ | own | own | 0.02949 | 0.10549 | 0.10549 | 0.02949 |
| $-\frac3{10}$ | $-\frac3{10}$ | own | side | 0.16536 | 0.18189 | 0.18189 | 0.16536 |
| $\frac25$ | $\frac25$ | own | side | 0.20571 | 0.30967 | 0.30967 | 0.20571 |
| $-\frac14$ | $-\frac14$ | side | own | 0.04765 | 0.12139 | 0.12139 | 0.04765 |
| $-\frac14$ | $-\frac14$ | side | side | 0.15936 | 0.18606 | 0.18606 | 0.15936 |
| $\frac14$ | $\frac14$ | side | side | 0.15022 | 0.29045 | 0.29045 | 0.15022 |

*Table E.6.* The approximate gap $\tilde G$ at the points of Lemma E.12,
rounded down: the corner and axis points of the domains, then the ends of the
diagonals.
"Own" and "side" are the kinds of $N$ and $W$ for which the point is one of the
listed points; at $n = 0$ the gap does not depend on the kind of $N$, and at
$w = 0$ not on that of $W$ ("either"). The entries $0$ are the exact values of
$G$ at the origin for the facets of the model.

The smallest entry, $0.00063$ at $n = 0$, $w = -\frac{11}{25}$ for
$f = -e^N_2$, is where the decimals of $r_*$ matter: the gap itself is
$6.6 \cdot 10^{-4}$ there, and the budget of Lemma E.15 leaves $1.3 \cdot 10^{-4}$
of $\tilde G$. Figure E.7 shows the gap of the two facets of the model on the
domain where it is smallest.

*Lean:
[`Six.Stress.Pair.gap_vertices`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L395),
[`Six.Stress.Pair.gap_origin`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L386),
[`Six.Stress.Pair.value_origin`](../../SquaresInCircles/Six/Stress/PairStress.lean#L127),
[`Six.radius_mul_north_length`](../../SquaresInCircles/Six/Constants.lean#L281),
[`Six.radius_mul_west_length`](../../SquaresInCircles/Six/Constants.lean#L294).*

![Two heat maps of the gap over the domain of the pair for N and W on their own axes, n from -3/10 to 5/12 horizontally and w from -11/25 to 0 vertically: light where the gap is near 0 and darker where it is larger, with contour lines; for the facet -e^W_1 (left) the gap vanishes at the origin, at the top edge, and grows away from it; for -e^N_2 (right) it also vanishes at the origin and nearly vanishes at the point n = 0, w = -11/25 at the bottom edge, marked with a dot](figures/appendix-e/pair-gap.svg)

*Figure E.7.* The gap $G$ for $N$ and $W$ on their own axes, for the facets
$-e^W_1$ (left) and $-e^N_2$ (right), with contour lines at $0.01$, $0.02$,
$0.04$, $0.08$, $0.16$ and $0.32$.
It vanishes only at the origin, where both facets are tight, and comes within
$6.6 \cdot 10^{-4}$ of $0$ at $(0, -\frac{11}{25})$ for $-e^N_2$ (dot).

*Proof of Proposition 9.50.* Fix the facet $f$ and the kinds of $N$ and $W$.
The domain $\mathcal D$ contains the origin. By Lemma E.11 the gap is concave
on every segment of a line in $n$, a line in $w$ or the diagonal on which $n$,
$w$ and $n - w$ keep their signs, since such a segment lies in one sector; by
Lemma E.16 it is nonnegative at the points of Lemma E.12. So Lemma E.12 gives
$G \ge 0$ on $\mathcal D$, that is,
$\Pi(n, w) \ge \beta_* + \ell(w) + \frac1{1000}|n|$. At $n = w = 0$, Lemma E.16
gives $\Pi(0, 0) = \beta_*$ for the facets of the model and
$\Pi(0, 0) = \beta_* + G(0, 0) > \beta_*$ for the other two. $\square$

*Lean:
[`Six.Stress.Pair.lower_bound`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L124),
[`Six.Stress.Pair.model_of_value_origin`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L133),
[`Six.Stress.Pair.rectangle_nonneg`](../../SquaresInCircles/Six/Stress/PairEstimate.lean#L78),
[`Six.Stress.Pair.gap_sweep_concave`](../../SquaresInCircles/Six/Stress/PairEstimate/Curvature.lean#L818),
[`Six.Stress.Pair.gap_vertices`](../../SquaresInCircles/Six/Stress/PairEstimate/Vertices.lean#L395).*

## E.3 Proof of Proposition 9.53

In this section $w$, $s$, $d$ lie in the domain of the diagonal, and $\beta$,
$\delta$, $L$, $\sigma$, $\Delta$ and $\mathcal R$ are as in
[Definition 9.51](09-six.md#definition-951-the-diagonal-value). The square $D$ is
held by the two wings, and the force of the stress of the model on it is the
sum of $m_*e^W_2$, from $W$–$D$, and $-m_*e^S_2$, from $D$–$S$. In the frame of
$D$ it makes the angle $-\delta$ with the primary axis, and the support
$\sigma(L, \delta)$ bounds its work ([Lemma 9.52](09-six.md#lemma-952-the-diagonal-bound)):
the work is largest with the centre of $D$ at the corner $(\rho_*, 0)$ of the
region of its possible centres when the force is nearly radial, and with a far
vertex of $D$ on the circle otherwise (Figure E.8). We first write $\Delta$ in
these terms, then treat the two cases.

### Lemma E.17 (the turned square)

1. $-\frac{11}{25} \le \beta \le \frac25$, $|\delta| \le \frac{71}{100}$,
   $0 \le d - w \le \frac\pi2$ and $0 \le d - s \le \frac\pi2$; and
   $d - w = \frac\pi4 + \delta - \beta$, $d - s = \frac\pi4 + \delta + \beta$.
2. $\cos\beta - \sin\beta > 0$, $\cos\delta > 0$ and $|\sin\delta| \le \cos\delta$;
   in particular $L > 0$.
3. In the frame of $D = Q_{\pi + d}(a_D, b_D)$, with $W$ at the phase $\pi + w$
   and $S$ at $\frac{3\pi}2 + s$, the force $m_*(e^W_2 - e^S_2)$ has the
   components

   ```math
   m_*\left(\sin(d - w) + \cos(d - s),\ \cos(d - w) - \sin(d - s)\right) = L\left(\cos\delta, -\sin\delta\right) .
   ```

4. $m_*\left(\omega(d - w) + \omega(d - s)\right) = K_*\cos\beta\cos\delta$.
5. If $2R_6|\sin\delta| \le 1$ (the *cap case*), then
   $\Delta = K_*\left((1 - \rho_*)\cos\beta + \rho_*\sin\beta\right)\cos\delta$;
   otherwise (the *vertex case*)

   ```math
   \Delta = K_*\left(\tfrac12(3\cos\beta - \sin\beta)\cos\delta + \tfrac12(\cos\beta - \sin\beta)|\sin\delta| - R_6(\cos\beta - \sin\beta)\right) .
   ```

*Proof.* (1) $\beta = \frac12(w - s)$ lies between
$\frac12(-\frac{11}{25} - \frac{11}{25})$ and $\frac12(\frac25 + \frac25)$. As
$\frac12 - \frac\pi4 \le d - \frac\pi4 \le 0$ with $\frac\pi4 - \frac12 < 0.2855$,
and $|w + s| \le \frac{21}{25}$, we get
$-0.2855 - \frac{21}{50} \le \delta \le \frac{21}{50}$. Also
$d - w \ge \frac12 - \frac25$, $d - w \le \frac\pi4 + \frac{11}{25} < \frac\pi2$,
and the same for $d - s$. The two identities are the definitions of $\beta$ and
$\delta$.

(2) $|\beta| \le \frac{11}{25}$ gives
$\cos\beta \ge 1 - \frac12(\frac{11}{25})^2 > \frac{11}{25} \ge |\sin\beta|$,
and $|\delta| \le \frac{71}{100}$ gives
$\cos\delta \ge 1 - \frac12(\frac{71}{100})^2 > \frac{71}{100} \ge |\sin\delta|$.

(3) Turning by $-(\pi + d)$, the vector $e^W_2 = u(\frac{3\pi}2 + w)$ becomes
$u(\frac\pi2 - (d - w)) = (\sin(d - w), \cos(d - w))$, and
$e^S_2 = u(2\pi + s)$ becomes $u(s - d - \pi) = (-\cos(d - s), \sin(d - s))$.
With (1), $\sin(\frac\pi4 + x) = h(\cos x + \sin x)$ and
$\cos(\frac\pi4 + x) = h(\cos x - \sin x)$, the first component is

```math
m_*h\left(\cos(\delta - \beta) + \sin(\delta - \beta) + \cos(\delta + \beta) - \sin(\delta + \beta)\right) = 2hm_*\left(\cos\delta\cos\beta - \cos\delta\sin\beta\right) = L\cos\delta ,
```

and the second is

```math
m_*h\left(\cos(\delta - \beta) - \sin(\delta - \beta) - \cos(\delta + \beta) - \sin(\delta + \beta)\right) = 2hm_*\left(\sin\delta\sin\beta - \sin\delta\cos\beta\right) = -L\sin\delta ,
```

as $K_* = 2hm_*$.

(4) For $0 \le t \le \frac\pi2$, $\omega(t) = \frac12(\cos t + \sin t)$, and
$\cos(\frac\pi4 + x) + \sin(\frac\pi4 + x) = 2h\cos x$. So

```math
\omega(d - w) + \omega(d - s) = h\left(\cos(\delta - \beta) + \cos(\delta + \beta)\right) = 2h\cos\beta\cos\delta .
```

(5) Insert (4) and $L = K_*(\cos\beta - \sin\beta)$ into Definition 9.51. $\square$

*Lean:
[`Six.Stress.diagonal_parameters`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L58),
[`Six.Stress.diagonal_trig_signs`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L68),
[`Six.Stress.diagonalLocalForce`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L30),
[`Six.Stress.diagonal_force_formula`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L123),
[`Six.Stress.diagonal_threshold_formula`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L137),
[`Six.Stress.diagonal_value_formula`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L180),
[`Six.Stress.diagonalCap`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L169),
[`Six.Stress.diagonalVertex`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L174).*

![Two panels in the frame of D, with the disk centre at the origin, the circle of radius R6 and the region of the possible centres of D, bounded by four arcs that meet in corners on the axes. Left, the cap case: the force on D points within the narrow angle between the normals of the two arcs at the corner (rho*, 0), and the square D is drawn with its centre at that corner, two vertices on the circle. Right, the vertex case: the force points more steeply, the best centre lies on an arc, and the square D has its far vertex on the circle in the direction of the force](figures/appendix-e/diagonal-support.svg)

*Figure E.8.* The support $\sigma(L, \delta)$ of the force $L(\cos\delta, -\sin\delta)$
on $D$ (Definition 9.51), in the frame of $D$. The centres of the unit squares of
this frame in the disk of radius $R_6$ form the region bounded by the four arcs
$(|a| + \frac12)^2 + (|b| + \frac12)^2 = R_6^2$ (grey). Left: if
$2R_6|\sin\delta| \le 1$, the force lies in the angle of the normals at the
corner $(\rho_*, 0)$ (dashed), and the work is largest there:
$\sigma = \rho_*L\cos\delta$. Right: otherwise it is largest where the far vertex
of $D$ lies on the circle in the direction of the force:
$\sigma = L(R_6 - \frac12(\cos\delta + |\sin\delta|))$.

### Lemma E.18 (the lines and the base)

For all real $w$ and $s$,

```math
\ell(w) + \ell(-s) = \tfrac{23}{100}\left(|w| + |s|\right) - \tfrac{49}{50}\beta , \qquad 2|\beta| \le |w| + |s| ,
```

and $2\beta_* = K_*(\rho_* - 1)$.

*Proof.* For $w \ge 0$, $\ell(w) = -\frac{13}{50}w$, and for $w \le 0$,
$\ell(w) = -\frac{18}{25}w$; in both cases
$\ell(w) = \frac{23}{100}|w| - \frac{49}{100}w$. In the same way
$\ell(-s) = \frac{23}{100}|s| + \frac{49}{100}s$, and the sum is the claim, as
$w - s = 2\beta$. Next, $2|\beta| = |w - s| \le |w| + |s|$. The last identity is
Proposition 9.27 (3). $\square$

*Lean:
[`Six.Stress.line_sum`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L195),
[`Six.Stress.twice_beta_abs_le`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L188),
[`Six.Stress.pairBase_eq_diagonal_scale`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L209),
[`Six.pairBase_diagonal_identity`](../../SquaresInCircles/Six/Constants.lean#L310).*

### Lemma E.19 (the cap case)

On the domain of the diagonal let

```math
\mathcal R_{\mathrm{cap}} = \ell(w) + \ell(-s) + K_*\left((1 - \rho_*)\cos\beta + \rho_*\sin\beta\right)\cos\delta + 2\beta_* .
```

Then $\mathcal R_{\mathrm{cap}} \ge \frac3{200}(|w| + |s|)$, and
$\mathcal R_{\mathrm{cap}} = 0$ only for $w = s = 0$ and $d = \frac\pi4$.

*Proof.* Put $Z = |w| + |s|$, $T = K_*\rho_*$ and
$\Psi = K_*(\rho_* - 1)(1 - \cos\beta\cos\delta)$. Then $1.39 < T < 1.41$, and
$\Psi \ge 0$ as $\rho_* > 1$ and $0 < \cos\beta\cos\delta \le 1$. By Lemma E.18,

```math
\mathcal R_{\mathrm{cap}} = \tfrac{23}{100}Z - \tfrac{49}{50}\beta + T\sin\beta\cos\delta + \Psi .
```

*If $\beta \le 0$:* then $\beta \le \sin\beta \le 0$ and $0 < \cos\delta \le 1$, so
$T\sin\beta\cos\delta \ge T\sin\beta \ge T\beta \ge 1.41\,\beta$, and, by
$|\beta| \le \frac12Z$,

```math
\mathcal R_{\mathrm{cap}} \ge \tfrac{23}{100}Z - \tfrac{43}{100}|\beta| \ge \left(\tfrac{23}{100} - \tfrac{43}{200}\right)Z = \tfrac3{200}Z .
```

*If $\beta \ge 0$:* then $\beta \le \frac25$. Let
$q = \frac16\beta^2 + \frac12\delta^2$, so that
$q \le \frac{4}{150} + \frac12(\frac{71}{100})^2 < \frac7{25}$. As
$\sin\beta \ge \beta - \frac{\beta^3}6$, $\cos\delta \ge 1 - \frac{\delta^2}2$ and
$(\beta - \sin\beta)(1 - \cos\delta) \ge 0$,

```math
\sin\beta\cos\delta \ge \sin\beta + \beta\cos\delta - \beta \ge \beta\left(1 - \tfrac{\beta^2}6\right) - \beta\tfrac{\delta^2}2 = \beta(1 - q) .
```

So
$T\sin\beta\cos\delta - \frac{49}{50}\beta \ge \beta(1.39 \cdot \frac{18}{25} - \frac{49}{50}) \ge 0$,
and $\mathcal R_{\mathrm{cap}} \ge \frac{23}{100}Z \ge \frac3{200}Z$.

If $\mathcal R_{\mathrm{cap}} = 0$, then $Z = 0$, so $w = s = 0$, $\beta = 0$,
$\delta = d - \frac\pi4$ and
$\mathcal R_{\mathrm{cap}} = \Psi = K_*(\rho_* - 1)\left(1 - \cos(d - \frac\pi4)\right)$.
So $\cos(d - \frac\pi4) = 1$, and Lemma A.15 (4) gives
$\frac15(d - \frac\pi4)^2 \le 1 - \cos(d - \frac\pi4) = 0$, that is,
$d = \frac\pi4$. $\square$

*Lean:
[`Six.Stress.diagonal_cap_lower`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L214),
[`Six.Stress.diagonal_cap_zero`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L285).*

In the vertex case $|\delta|$ is not small, so $|w + s|$ is large, and the lines
of the two pairs pay for the loss of the support.

### Lemma E.20 (the vertex minorant)

For real $x$, $y$, $t$ with $y \ge 0$, $x + y \le \frac{11}{25}$ and
$\frac{29}{100} \le t \le \frac27 + x$,

```math
\Phi(x, y, t) = \tfrac9{25}\max(x, y) + \tfrac{77}{100}y + \left(\tfrac32 + \tfrac y2\right)\cos t + \left(\tfrac12 + \tfrac y2\right)\sin t - 1.689(1 + y) + 0.112 > 0 .
```

*Proof.* Rearranging,
$\Phi = \frac32\cos t + \frac12\sin t - 1.577 + \frac9{25}\max(x, y) - p(t)\,y$
with $p(t) = 0.919 - \frac12(\cos t + \sin t)$. Here
$t \le \frac27 + x \le \frac27 + \frac{11}{25} < \frac34 < \frac\pi4$, so
$\cos t + \sin t$ is nondecreasing in $t$ (Lemma A.15 (3)), and $p(t) \le p(l)$
for $0 \le l \le t$. Also $x \ge t - \frac27 > 0$. We cut the range of $t$ into
three pieces $[l, u]$.

1. *$[l, u] = [\frac{29}{100}, \frac{11}{25}]$ and $[\frac{11}{25}, \frac12]$.* By
   Lemma A.8, $0 \le p(l) \le \frac9{25}$ (Table E.7). As
   $\max(x, y) \ge y$ and $\max(x, y) \ge x \ge t - \frac27$,

   ```math
   \tfrac9{25}\max(x, y) - p(t)y \ge \left(\tfrac9{25} - p(l)\right)\max(x, y) + p(l)\left(\max(x, y) - y\right) \ge \left(\tfrac9{25} - p(l)\right)\left(t - \tfrac27\right) ,
   ```

   so

   ```math
   \Phi \ge F_l(t) = \tfrac32\cos t + \tfrac12\sin t - 1.577 + \left(\tfrac9{25} - p(l)\right)\left(t - \tfrac27\right) .
   ```

2. *$[l, u] = [\frac12, \frac34]$.* Here $y \le \frac{11}{25} - x$, so

   ```math
   \tfrac9{25}\max(x, y) - p(t)y \ge \tfrac9{25}x - p(l)\left(\tfrac{11}{25} - x\right) \ge \left(\tfrac9{25} + p(l)\right)\left(t - \tfrac27\right) - \tfrac{11}{25}p(l) ,
   ```

   and $\Phi \ge F_l(t)$ with

   ```math
   F_l(t) = \tfrac32\cos t + \tfrac12\sin t - 1.577 + \left(\tfrac9{25} + p(l)\right)\left(t - \tfrac27\right) - \tfrac{11}{25}p(l) .
   ```

Each $F_l$ is an affine function plus $\frac32\cos t + \frac12\sin t$, hence
concave on $[l, u] \subset [0, \frac\pi2]$, and by Lemma A.5 it is positive on
$[l, u]$ once it is positive at $l$ and $u$. Table E.7 gives these end values,
bounded below with the brackets of Lemma A.8 for the sines and cosines of the
ends and of $l$; they are positive. $\square$

| piece $[l, u]$ | bracket of $p(l)$ | $F_l(l) \ge$ | $F_l(u) \ge$ |
| :-: | :-: | :-: | :-: |
| $[\frac{29}{100}, \frac{11}{25}]$ | $[0.29690, 0.29691]$ | $0.00361$ | $0.00283$ |
| $[\frac{11}{25}, \frac12]$ | $[0.25364, 0.25366]$ | $0.00950$ | $0.00187$ |
| $[\frac12, \frac34]$ | $[0.24048, 0.24050]$ | $0.00194$ | $0.03433$ |

*Table E.7.* The three pieces of Lemma E.20: brackets of $p(l)$ from
$C_6 \le \cos \le C_4$ and $S_7 \le \sin \le S_5$ at $l$, and Taylor lower bounds
of the end values of $F_l$, rounded down.

![Graph over t from 0.29 to 0.75 of the three concave lower bounds F_l of the vertex minorant, one on each piece, each positive at both of its ends and dipping close to zero near t = 0.44 and t = 0.5; the least value of the minorant over the admissible x and y at each t is drawn above them](figures/appendix-e/vertex-minorant.svg)

*Figure E.9.* Lemma E.20: the least value of $\Phi(x, y, t)$ over the admissible
$x$ and $y$ (blue), and the three concave lower bounds $F_l$ on their pieces
(orange). Each bound turns negative soon after the right end of its piece,
which is why three pieces are needed.

*Lean:
[`Six.Stress.vertexMinorant`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L318),
[`Six.Stress.vertexMinorant_pos`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L329).*

### Lemma E.21 (the vertex case)

On the domain of the diagonal, if $2R_6|\sin\delta| \ge 1$, then

```math
\mathcal R_{\mathrm{vertex}} = \ell(w) + \ell(-s) + K_*\left(\tfrac12(3\cos\beta - \sin\beta)\cos\delta + \tfrac12(\cos\beta - \sin\beta)|\sin\delta| - R_6(\cos\beta - \sin\beta)\right) + 2\beta_* > 0 .
```

*Proof.* Let $x = \frac12|w + s|$, $y = |\beta|$ and $t = |\delta|$, so that
$\cos\delta = \cos t$ and $|\sin\delta| = \sin t$ (as $t \le \frac{71}{100}$).

1. $x + y = \max(|w|, |s|) \le \frac{11}{25}$, as
   $|\alpha| + |\alpha'| = \max(|\alpha + \alpha'|, |\alpha - \alpha'|)$ for
   $\alpha = \frac12(w + s)$, $\alpha' = \beta$; and
   $2\max(x, y) \le |w| + |s|$.
2. $t \ge \frac{29}{100}$: $1 \le 2R_6|\sin\delta| \le \frac{17}5t$.
3. $t \le \frac27 + x$: $t \le |d - \frac\pi4| + x \le \frac\pi4 - \frac12 + x$,
   and $\pi < \frac{22}7$.

By Lemma E.18 and (1),

```math
\mathcal R_{\mathrm{vertex}} \ge \tfrac{46}{100}M - \tfrac{49}{50}\beta + K_*\left(\mathcal A\cos\beta + \mathcal B\sin\beta + \rho_* - 1\right), \qquad M = \max(x, y),
```

where $\mathcal A = \frac32\cos t + \frac12\sin t - R_6$ and
$\mathcal B = R_6 - \frac12(\cos t + \sin t)$. Now
$\frac32\cos t + \frac12\sin t \le \sqrt{\frac52} < \frac85 < R_6$, so
$\mathcal A \le 0$ and $\mathcal A\cos\beta \ge \mathcal A$; and
$\cos t + \sin t \le \sqrt2 < \frac32$, so $\mathcal B \ge \frac{17}{20}$ and
$K_*\mathcal B \ge \frac54 \cdot \frac{17}{20} = \frac{17}{16}$. We claim
$-\frac{49}{50}\beta + K_*\mathcal B\sin\beta \ge \frac{49}{50}y - K_*\mathcal By$.
If $\beta \le 0$, this follows from $\sin\beta \ge \beta = -y$. If
$\beta \ge 0$, then $\beta \le \frac12$ and
$\sin\beta \ge \beta - \frac{\beta^3}6 \ge \frac{23}{24}\beta$,
so
$K_*\mathcal B(\sin\beta + \beta) \ge \frac{17}{16} \cdot \frac{47}{24}\beta > \frac{49}{25}\beta$,
which is the claim. Hence

```math
\mathcal R_{\mathrm{vertex}} \ge \tfrac{46}{100}M + \tfrac{49}{50}y + K_*\left(\mathcal A - \mathcal By + \rho_* - 1\right) .
```

Expanding $\mathcal A - \mathcal By$, the right side equals

```math
K_*\,\Phi(x, y, t) + \left(\tfrac{46}{100} - \tfrac9{25}K_*\right)M + \left(\tfrac{49}{50} - \tfrac{77}{100}K_*\right)y + K_*(1.689 - R_6)(1 + y) + K_*(\rho_* - 1.112) .
```

The four last terms are nonnegative, as $K_* < 1.27$, $R_6 < 1.689$ and
$\rho_* > 1.112$; and $\Phi(x, y, t) > 0$ by Lemma E.20, whose hypotheses are
(1), (2) and (3). So $\mathcal R_{\mathrm{vertex}} > 0$. $\square$

*Lean:
[`Six.Stress.diagonal_vertex_pos`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L490),
[`Six.Stress.vertex_expression_pos`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L381),
[`Six.Stress.diamond_bound`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L459),
[`Six.Stress.max_bound`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L476).*

![Three heat maps of the remainder over the box of w from -11/25 to 2/5 (horizontal) and s from -2/5 to 11/25 (vertical), for d = pi/4, d = 0.65 and d = 1/2; light near zero and darker where larger, with contour lines; dashed lines of slope -1 separate the cap case, a band around a line w + s = const, from the vertex case on either side; for d = pi/4 the remainder vanishes only at the origin, marked with a dot](figures/appendix-e/diagonal-remainder.svg)

*Figure E.10.* The remainder $\mathcal R(w, s, d)$ over the box of $w$ and $s$,
for $d = \frac\pi4$, $0.65$ and $\frac12$, with contour lines at multiples of
$0.05$. Between the dashed lines, $2R_6|\sin\delta| \le 1$ (the cap case of
Lemma E.19); outside them the vertex case of Lemma E.21. The remainder vanishes
only at the model, $w = s = 0$, $d = \frac\pi4$ (dot).

*Proof of Proposition 9.53.* By Definition 9.51 and Lemma E.17 (5),
$\mathcal R = \mathcal R_{\mathrm{cap}}$ in the cap case and
$\mathcal R = \mathcal R_{\mathrm{vertex}}$ in the vertex case. In the cap case
$\mathcal R \ge \frac3{200}(|w| + |s|) \ge 0$, with equality only for
$w = s = 0$ and $d = \frac\pi4$ (Lemma E.19); in the vertex case
$2R_6|\sin\delta| > 1$ and $\mathcal R > 0$ (Lemma E.21). $\square$

*Lean:
[`Six.Stress.remainder_nonnegative`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L541),
[`Six.Stress.remainder_zero`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L548),
[`Six.Stress.diagonal_cap_lower`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L214),
[`Six.Stress.diagonal_cap_zero`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L285),
[`Six.Stress.diagonal_vertex_pos`](../../SquaresInCircles/Six/Stress/DiagonalEstimate.lean#L490).*
