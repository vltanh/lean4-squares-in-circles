# Appendix K. Eight squares: the central core

[Contents](README.md) · [← Appendix J](appendix-j.md) · [Appendix L →](appendix-l.md)

This appendix proves
[Lemma 11.8](11-eight.md#lemma-118-arcs-on-two-circles), the inequality
$3L_1(S) + L_{5/4}(S) \ge \pi$ for a square that avoids the disk centre, and
[Theorem 11.10](11-eight.md#theorem-1110-the-one-twelfth-core), the
one-twelfth core. It also proves the common-point lemma used in
[Lemma 11.18](11-eight.md#lemma-1118-a-common-point) and the bound on a
square beyond a line used in
[Lemma 11.19](11-eight.md#lemma-1119-four-forward-axes). The disk centre is
the origin $o$, and $\Gamma_r$ is the circle of radius $r$ about it.

## K.1 Arcs on two circles

Throughout this section $Q = \frac{98}{25}$, and $S$ is a unit square in the
closed disk of squared radius $Q$ with $o \notin S^\circ$. The lengths $L_r$
do not change under a rotation about $o$ or a reflection in a line through
$o$, so we may place $S$ in a *canonical position*: with its centre at
$(a_S, b_S)$, the state of
[Definition 3.1](03-tools.md#definition-31-position-of-the-disk-centre),

```math
S = [x, x + 1] \times [y, y + 1], \qquad x = a_S - \tfrac12 \ge 0, \qquad -\tfrac12 \le y = b_S - \tfrac12 \le x, \qquad (x + 1)^2 + (y + 1)^2 \le Q , \tag{K.1}
```

the last inequality being
[Lemma 3.4](03-tools.md#lemma-34-farthest-vertex). Two constants recur:

```math
x_0 = \sqrt{Q - 1} - 1 = \tfrac{\sqrt{73}}5 - 1 < \tfrac57, \qquad b_0 = \sqrt{Q - \tfrac14} - 1 = \tfrac{\sqrt{367}}{10} - 1 < \tfrac{11}{12},
```

the comparisons being $49 \cdot 73 < 3600$ and $367 \cdot 144 < 52900$. By
(K.1), $x \le b_0 < 1$ for every canonical square.

### Lemma K.1 (a factorization)

For $r \ge 1$ let $P_r(z) = z^2\left(r^2 - (z - 1)^2\right)$. If $X \ge Y > 0$
and $X^2 + Y^2 = Q$, then, with $\sigma = X + Y$,

```math
P_r(X) - P_r(Y) = (X - Y)\left((r^2 - 1)\,\sigma + \sigma^2 - Q\sigma + Q\right),
```

and the second factor is positive. So $P_r(X) > P_r(Y)$ if $X > Y$.

*Proof.* $P_r(z) = (r^2 - 1)z^2 + 2z^3 - z^4$, so
$P_r(X) - P_r(Y) = (X - Y)\left((r^2 - 1)\sigma + 2(X^2 + XY + Y^2) - \sigma(X^2 + Y^2)\right)$,
and $2(X^2 + XY + Y^2) = Q + \sigma^2$ and $\sigma(X^2 + Y^2) = \sigma Q$. The
second factor is at least $\sigma^2 - Q\sigma + Q = (\sigma - \frac Q2)^2 + Q(1 - \frac Q4) > 0$,
as $0 < Q < 4$. $\square$

### Lemma K.2 (two monotone angles)

Let $r \ge 1$.

1. *Straddling.* For $0 \le \nu \le \frac12$ let $X(\nu) = \sqrt{Q - (1 - \nu)^2}$.
   Then $\nu \mapsto \arccos\frac{X(\nu) - 1}r + \arcsin\frac\nu r$ is
   strictly increasing; so if $0 \le x \le X(\nu) - 1$, then
   $\arccos\frac xr + \arcsin\frac\nu r \ge \arccos\frac{x_0}r$.
2. *Corner.* For $0 \le y \le \frac25$ let $X(y) = \sqrt{Q - (1 + y)^2}$. Then
   $y \mapsto \arcsin\frac{X(y) - 1}r + \arcsin\frac yr$ is increasing; so a
   canonical square with $y \ge 0$ has
   $\arcsin\frac xr + \arcsin\frac yr \le 2\arcsin\frac2{5r}$.

*Proof.* (1) With $Y = 1 - \nu$, $X' = Y/X$, and the derivative is

```math
\frac1{\sqrt{r^2 - \nu^2}} - \frac Y{X\sqrt{r^2 - (X - 1)^2}} ;
```

the denominators are positive as $X - 1 \le b_0 < 1 \le r$ and
$\nu \le \frac12$. After clearing them and squaring, positivity is
$X^2(r^2 - (X - 1)^2) > Y^2(r^2 - (Y - 1)^2)$, that is
$P_r(X) > P_r(Y)$, which holds by Lemma K.1 since
$X^2 \ge Q - 1 > 1 \ge Y^2$ and $X^2 + Y^2 = Q$. For the consequence,
$\arccos$ decreases, so the sum is at least its value at $x = X(\nu) - 1$,
which is at least its value at $\nu = 0$, where $X(0) - 1 = x_0$.

(2) The derivative has the same form with $Y = 1 + y$, and $X \ge Y$ exactly
when $(1 + y)^2 \le \frac Q2 = \frac{49}{25}$, that is $y \le \frac25$, with
equality $X = Y = \frac75$ at $y = \frac25$. A canonical square with
$y \ge 0$ has $2(1 + y)^2 \le Q$, so $y \le \frac25$, and $x \le X(y) - 1$;
increasing $x$ to $X(y) - 1$ and then $y$ to $\frac25$ increases the sum, to
$2\arcsin\frac{2/5}r$. $\square$

*Lean:
[`Eight.TwoCircle.straddling_polynomial_upper`](../../SquaresInCircles/Eight/CentralCore.lean#L693),
[`Eight.TwoCircle.straddling_unit_angle`](../../SquaresInCircles/Eight/CentralCore.lean#L708),
[`Eight.TwoCircle.straddling_larger_angle`](../../SquaresInCircles/Eight/CentralCore.lean#L756),
[`Eight.TwoCircle.corner_arcsin_sum`](../../SquaresInCircles/Eight/CentralCore.lean#L518),
[`Eight.TwoCircle.corner_quadratic`](../../SquaresInCircles/Eight/CentralCore.lean#L500).*

### Proof of Lemma 11.8

We bound $L_1$ and $L_{5/4}$ in three regions of the canonical positions
(Figure K.1).

*The region $x < \frac14$.* The far side $x + 1 \ge 1$ does not cut
$\Gamma_1$. If $y = -\nu \le 0$, put $A_1 = \arccos x$,
$B_1 = \arcsin(1 - \nu)$, $C_1 = \arcsin\nu$; the unit circle meets
$\overline S$ in the arc of the angles from $-\min(A_1, C_1)$ to
$\min(A_1, B_1)$, so

```math
L_1 = \min(A_1, B_1) + \min(A_1, C_1) = \min(A_1 + C_1,\ B_1 + C_1) ,
```

as $A_1 > \arccos\frac14 > \frac\pi3 \ge 2C_1 \ge C_1$. Here
$A_1 + C_1 > \frac\pi3$, and $B_1 + C_1 \ge 2\arcsin\frac12 = \frac\pi3$ by the
convexity of $\arcsin$ on $[0, 1]$, with equality only for $\nu = \frac12$.
If $y \ge 0$, then
$L_1 = \frac\pi2 - \arcsin x - \arcsin y > \frac\pi2 - 2\arcsin\frac14 > \frac\pi3$,
as $\sin(2\arcsin\frac14) = \frac{\sqrt{15}}8 < \frac12$. So
$3L_1 + L_{5/4} \ge \pi$, with equality only if $y = -\frac12$ and
$L_{5/4} = 0$. For $y = -\frac12$ the farthest vertex is at squared distance
$(x + 1)^2 + \frac14$; if it exceeds $\frac{25}{16}$, the open square has
points on both sides of $\Gamma_{5/4}$ and so holds an arc of it, of positive
length; if not, $\overline S$ meets $\Gamma_{5/4}$ in at most two points. So
equality holds exactly for $(x + 1)^2 + \frac14 \le \frac{25}{16}$, that is
$x \le \frac{\sqrt{21} - 4}4 < \frac14$; then $L_1 = \frac\pi3$.

*The region $x \ge \frac14$, $y < 0$.* Write $y = -\nu$, $0 < \nu \le \frac12$,
with $A_1, B_1, C_1$ as above. We show $L_1 > \alpha_0 = \arccos\frac57$.
If $A_1 \ge B_1$, then $L_1 = B_1 + C_1 \ge \frac\pi3 > \alpha_0$. If
$C_1 \le A_1 \le B_1$, then $L_1 = A_1 + C_1 \ge \arccos x_0 > \alpha_0$ by
Lemma K.2 (1), as (K.1) gives $x \le X(\nu) - 1$. If $A_1 \le C_1$, then
$L_1 = 2A_1$ and $\cos 2A_1 = 2x^2 - 1 < 2(\frac{11}{12})^2 - 1 = \frac{49}{72} < \frac57$.
On $\Gamma_{5/4}$, with $A_r = \arccos\frac{4x}5$, $B_r = \arcsin\frac{4(1 - \nu)}5$,
$C_r = \arcsin\frac{4\nu}5$: the far side does not cut, $A_r > C_r$ as
$x^2 + \nu^2 < (\frac{11}{12})^2 + \frac14 < \frac{25}{16}$, and
$L_{5/4} = \min(A_r + C_r, B_r + C_r)$. Now
$B_r + C_r \ge 2\arcsin\frac25$ by convexity, and
$A_r + C_r \ge \arccos\frac{4x_0}5 > \arccos\frac47 > 2\arcsin\frac25$ by
Lemma K.2 (1), as $\cos(2\arcsin\frac25) = \frac{17}{25} > \frac47$. So with
$\beta_0 = \arcsin\frac25$,

```math
3L_1 + L_{5/4} > 3\alpha_0 + 2\beta_0 > \pi ,
```

the last because $3\alpha_0 < \pi$ and
$\cos 3\alpha_0 = 4(\frac57)^3 - 3 \cdot \frac57 = -\frac{235}{343} < -\frac{17}{25} = \cos(\pi - 2\beta_0)$,
that is $5875 > 5831$.

*The region $x \ge \frac14$, $y \ge 0$.* By Lemma K.2 (2) with $r = 1$,
$L_1 = \frac\pi2 - \arcsin x - \arcsin y \ge \frac\pi2 - 2\beta_0$. On
$\Gamma_{5/4}$, with $\gamma_0 = \arcsin\frac8{25}$: if $y \ge \frac14$,
neither far side cuts and Lemma K.2 (2) with $r = \frac54$ gives
$L_{5/4} = \frac\pi2 - \arcsin\frac{4x}5 - \arcsin\frac{4y}5 \ge \frac\pi2 - 2\gamma_0$;
if $0 \le y < \frac14$, $L_{5/4}$ is the smaller of that expression and
$\arcsin\frac{4(y + 1)}5 - \arcsin\frac{4y}5$, which increases with $y$ and so
is at least $\arcsin\frac45 > \frac\pi2 - 2\gamma_0$, as
$\cos(\arcsin\frac45) = \frac35 < \frac{16\sqrt{561}}{625} = \sin 2\gamma_0$.
Hence

```math
3L_1 + L_{5/4} \ge 2\pi - 6\beta_0 - 2\gamma_0 > \pi ,
```

since $3\beta_0 < \frac\pi2$ and
$\sin 3\beta_0 = \frac{118}{125} < \frac{\sqrt{561}}{25} = \cos\gamma_0$,
that is $13924 < 14025$.

Only the first region allows equality, exactly for the squares of the
statement. $\square$

*Lean:
[`Eight.TwoCircle.intervalLength_straddling`](../../SquaresInCircles/Eight/CentralCore.lean#L650),
[`Eight.TwoCircle.intervalLength_corner`](../../SquaresInCircles/Eight/CentralCore.lean#L658),
[`Eight.TwoCircle.small_straddling_length`](../../SquaresInCircles/Eight/CentralCore.lean#L890),
[`Eight.TwoCircle.general_straddling_unit_length`](../../SquaresInCircles/Eight/CentralCore.lean#L910),
[`Eight.TwoCircle.general_straddling_larger_length`](../../SquaresInCircles/Eight/CentralCore.lean#L949),
[`Eight.TwoCircle.small_corner_length`](../../SquaresInCircles/Eight/CentralCore.lean#L982),
[`Eight.TwoCircle.corner_unit_length`](../../SquaresInCircles/Eight/CentralCore.lean#L993),
[`Eight.TwoCircle.corner_larger_length`](../../SquaresInCircles/Eight/CentralCore.lean#L1005),
[`Eight.TwoCircle.weighted_straddling_constant`](../../SquaresInCircles/Eight/CentralCore.lean#L811),
[`Eight.TwoCircle.corner_larger_far_side`](../../SquaresInCircles/Eight/CentralCore.lean#L870),
[`Eight.one_square_two_circle_inequality`](../../SquaresInCircles/Eight/CentralCore.lean#L1030).*

![Three panels, each a canonical square S = [x, x + 1] x [y, y + 1] with the unit circle and the circle of radius 5/4 about o, and the arcs of each circle in the closed square drawn thick, blue on the unit circle and orange on the larger one. Left: x = 0.1 and y = -1/2, the square straddling the axis, holding an arc of exactly 60 degrees of the unit circle and missing the larger circle. Middle: x = 0.4 and y = -0.25, holding arcs of both circles. Right: x = 0.35 and y = 0.2, a corner square holding arcs of both circles. Under each panel, its region and the lengths L1 and L5/4](figures/appendix-k/regions.svg)

*Figure K.1.* The three regions of the proof of Lemma 11.8, with the arcs of
$\Gamma_1$ and $\Gamma_{5/4}$ in the square (thick). Left: an equality square,
$y = -\frac12$, $x = 0.1$, with $L_1 = \frac\pi3$ and $L_{5/4} = 0$. Middle
and right: squares with $x \ge \frac14$, for which $3L_1 + L_{5/4}$ is about
$4.15$ and $4.16$, well above $\pi$.

![The region of canonical positions (x, y), with x from 0 to about 0.92 and y from -1/2 up to the diagonal y = x and to the circle (x + 1)^2 + (y + 1)^2 = 98/25, coloured by the value of 3 L1 + L5/4 in bands of width 0.25, from pi (lightest) upwards, with a legend; the value equals pi only on the thick red segment of the bottom edge y = -1/2 with x at most (root 21 - 4)/4, grows away from it, and changes steeply just left of the dashed line x = 1/4, where the far side of the square leaves the circle of radius 5/4](figures/appendix-k/weighted.svg)

*Figure K.2.* The value of $3L_1 + L_{5/4}$ over the canonical positions
(K.1), in bands of width $0.25$ above $\pi$. It attains $\pi$ only on the
segment $y = -\frac12$, $0 \le x \le \frac{\sqrt{21} - 4}4$ (thick).

## K.2 A positive depth

Let eight unit squares form a packing in a closed disk of squared radius at
most $Q_0 = \frac{9789}{2500}$ about $o$, and let $K$ be the central square of
[Proposition 11.9](11-eight.md#proposition-119-a-central-square). In a frame
of $K$ with the origin at $o$, after a quarter turn and a reflection, its
centre is $(a, u)$ with $0 \le u \le a < \frac12$; let $\Delta = \frac12 - a$,
the distance from $o$ to the boundary of $K$. For an exterior square $S$ write
$(A, B) = (a_S, b_S)$ for its state.

### Lemma K.3 (positive depth)

$\Delta > \frac1{1000}$, and every exterior square has
$A \ge \frac12 + \frac\Delta{\sqrt2}$; so $A > \frac{5007}{10000}$, and if
$a \le \frac9{20}$, then $A > \frac{107}{200}$.

*Proof.* Suppose $\Delta \le \frac1{1000}$ and let $p$ be a point of the
boundary of $K$ with $|p| = \Delta$. No square contains $p$ in its interior:
not $K$, and no other square, since a neighbourhood of $p$ meets $K^\circ$.
All eight squares lie in the closed disk about $p$ of radius $R + \Delta$,
where $R \le \sqrt{Q_0} < 2$ is the radius of the original disk, and

```math
(R + \Delta)^2 < Q_0 + \tfrac4{1000} + \tfrac1{10^6} = \tfrac{3919601}{10^6} < \tfrac{98}{25} .
```

So Proposition 11.9, applied with $p$ as the disk centre, gives a square
containing $p$ in its interior, a contradiction. Next, the open disk
$D(o, \Delta)$ lies in $K^\circ$ and so misses every exterior square; the
distance from $o$ to $\overline S$ is
$\sqrt{(A - \frac12)_+^2 + (B - \frac12)_+^2} \le \sqrt2\,(A - \frac12)_+$, which
gives $A \ge \frac12 + \frac\Delta{\sqrt2}$. Finally $\frac1{\sqrt2} > \frac7{10}$,
and $a \le \frac9{20}$ means $\Delta \ge \frac1{20}$. $\square$

*Lean:
[`Eight.centralDepth`](../../SquaresInCircles/Eight/CentralCore.lean#L1376),
[`Eight.centralDepth_gt_milli`](../../SquaresInCircles/Eight/CentralCore.lean#L1475),
[`Eight.translated_ceiling_reserve`](../../SquaresInCircles/Eight/CentralCore.lean#L392),
[`Eight.translated_containment_reserve`](../../SquaresInCircles/Eight/CentralCore.lean#L1445),
[`Eight.exterior_distance_from_centralDepth`](../../SquaresInCircles/Eight/CentralCore.lean#L1488),
[`Eight.primary_distance_lower`](../../SquaresInCircles/Eight/CentralCore.lean#L1496),
[`Eight.exterior_primary_bandA`](../../SquaresInCircles/Eight/CentralCore.lean#L1516),
[`Eight.exterior_primary_bandB`](../../SquaresInCircles/Eight/CentralCore.lean#L1525).*

## K.3 Common points

Let $S$ be a unit square in the closed disk of squared radius $Q_0$. Turn the
plane so that the centre direction of $S$ is the positive horizontal axis,
and choose a frame of $S$ and a reflection so that its centre is
$(a, -b) = (r\cos\alpha, -r\sin\alpha)$ in it, with $0 \le \alpha \le \frac\pi4$
and $a \ge b \ge 0$. For $0 \le \theta \le \frac\pi2$ let $\rho(\theta) > 0$
solve $\rho^2 + \rho(\cos\theta + \sin\theta) + \frac12 = Q_0$, the distance
of a centre on the outer curve at the angle $\theta$; containment gives
$r \le \rho(\alpha)$, and $\rho(\frac\pi2 - \theta) = \rho(\theta)$.

### Lemma K.4 (common points)

1. If $a > \frac12$, the segment
   $V = \lbrace (\frac{11}{12}, y) : |y| \le \frac7{20}\rbrace$ lies in $S^\circ$.
2. If $a > \frac{5007}{10000}$ and the centre direction of $S$ is within
   $\frac{3741}{10000}$ of a direction $\psi$, then
   $o + \frac{10007}{10000}u(\psi) \in S^\circ$; so two such squares with
   disjoint interiors have centre directions more than $\frac{3741}{5000}$
   apart.
3. If $a \ge \frac{107}{200}$ and the centre direction of $S$ is within
   $\frac{19}{50}$ of $\psi$, then $o + \frac{41}{40}u(\psi) \in S^\circ$; so
   two such squares with disjoint interiors have centre directions more than
   $\frac{19}{25}$ apart.

The proof reduces each claim to the positivity of two polynomials on
intervals, which is checked by a table of 19 rows. For constants
$A_0, C_-, C_+, D$ with $D < \frac12$, and with $u = \tan\frac\theta2$,
$z = 1 + u^2$, $c = 1 - u^2$, $s = 2u$, let

```math
H = \tfrac12 z + C_- c - D s, \qquad P = H^2 z + H c\,(c + s) + \left(\tfrac12 - Q_0\right)c^2 z, \qquad V = \tfrac12 c z + A_0 s z - C_+ s c - D c^2 ,
```

polynomials in $u$ of degrees 6 and 4. Then:

- if $P > 0$ on $[0, 1]$, then
  $\rho(\theta)\cos\theta < \frac12 + C_-\cos\theta - D\sin\theta$ for
  $0 \le \theta \le \frac\pi2$; indeed $\rho\cos\theta$ is the nonnegative root
  of $X^2 + X\cos\theta(\cos\theta + \sin\theta) + (\frac12 - Q_0)\cos^2\theta$,
  which increases for $X \ge 0$, and its value at $X = H/z$, the right side
  of the claim, is $P/z^3 > 0$;
- if $V > 0$ on $[0, \frac37]$, then
  $C_+\sin\alpha + D\cos\alpha - A_0\tan\alpha < \frac12$ for
  $0 \le \alpha \le \frac\pi4$, as $\tan\frac\alpha2 \le \sqrt2 - 1 < \frac37$
  and the left side minus $\frac12$ is $-V/(cz)$.

| case | $A_0$ | $C_-$ | $C_+$ | $D$ | $\lambda$, $\omega$ |
| --- | :-: | :-: | :-: | :-: | :-: |
| segment | $\frac12$ | $\frac{11}{12}$ | $\frac{11}{12}$ | $\frac7{20}$ | |
| band A | $\frac{5007}{10000}$ | $\lambda \cdot 0.9308368$ | $\lambda \cdot 0.9308369$ | $\lambda \cdot 0.365435$ | $\frac{10007}{10000}$, $\frac{3741}{10000}$ |
| band B | $\frac{107}{200}$ | $\lambda \cdot 0.9286$ | $\lambda \cdot 0.9287$ | $\lambda \cdot 0.371$ | $\frac{41}{40}$, $\frac{19}{50}$ |

*Table K.1.* The constants of the three cases. For the bands,
$C_- < \lambda\cos\omega < C_+$ and $\lambda\sin\omega < D$, by the alternating
series of cosine through degrees 6 and 8 and of sine through degree 9.

On an interval $[l, r]$, substitute $u = l + (r - l)v$ and write a polynomial
of degree $n$ as $\sum_k b_k\binom nk v^k(1 - v)^{n - k}$; the basis terms are
nonnegative on $[0, 1]$ and add up to 1, so positive coefficients prove the
polynomial positive on $[l, r]$. If $\sum_j a_j v^j$ is the expansion after
substitution, $b_k = \sum_{j \le k} a_j\binom kj/\binom nj$. The following
lower bounds, in units of $10^{-6}$, are all positive.

| case | polynomial | interval | lower bounds of $b_0, \dots, b_n$ |
| --- | :-: | :-: | --- |
| segment | $P$ | $[0, \frac14]$ | 8011, 14261, 20852, 24921, 25307, 22675, 18731 |
| segment | $P$ | $[\frac14, \frac12]$ | 18731, 14787, 9532, 4674, 2967, 7433, 19695 |
| segment | $P$ | $[\frac12, 1]$ | 19695, 44218, 99921, 199778, 334345, 418333, 180000 |
| segment | $V$ | $[0, \frac3{14}]$ | 150000, 105357, 66071, 39112, 29658 |
| segment | $V$ | $[\frac3{14}, \frac37]$ | 29658, 20203, 28253, 58985, 115785 |
| band A | $P$ | $[0, \frac14]$ | 65047, 66616, 68215, 66933, 61593, 52875, 42551 |
| band A | $P$ | $[\frac14, \frac38]$ | 42551, 37389, 31825, 26080, 20444, 15250, 10838 |
| band A | $P$ | $[\frac38, \frac7{16}]$ | 10838, 8631, 6620, 4847, 3354, 2183, 1375 |
| band A | $P$ | $[\frac7{16}, \frac12]$ | 1375, 566, 120, 76, 471, 1339, 2709 |
| band A | $P$ | $[\frac12, 1]$ | 2709, 13672, 56758, 146628, 276434, 364583, 144311 |
| band A | $V$ | $[0, \frac3{14}]$ | 134309, 88153, 47594, 19679, 9628 |
| band A | $V$ | $[\frac3{14}, \frac9{28}]$ | 9628, 4603, 4043, 8602, 18819 |
| band A | $V$ | $[\frac9{28}, \frac37]$ | 18819, 29035, 44909, 66978, 95668 |
| band B | $P$ | $[0, \frac12]$ | 143981, 138542, 131658, 99535, 46555, 9605, 5160 |
| band B | $P$ | $[\frac12, 1]$ | 5160, 714, 28774, 105813, 227896, 317762, 114672 |
| band B | $V$ | $[0, \frac3{14}]$ | 119725, 75055, 36206, 10492, 3374 |
| band B | $V$ | $[\frac3{14}, \frac{15}{56}]$ | 3374, 1595, 977, 1608, 3563 |
| band B | $V$ | $[\frac{15}{56}, \frac9{28}]$ | 3563, 5519, 8800, 13485, 19645 |
| band B | $V$ | $[\frac9{28}, \frac37]$ | 19645, 31963, 50179, 74860, 106455 |

*Table K.2.* The 19 Bernstein rows of Lemma K.4.

*Proof of Lemma K.4.* (1) A point $(\frac{11}{12}, y)$ with
$|y| \le \frac7{20}$ has the coordinates
$d_e = \frac{11}{12}\cos\alpha + y\sin\alpha - a$ and
$d_f = -\frac{11}{12}\sin\alpha + y\cos\alpha + b$ in the frame of $S$ about
its centre. First $d_e \le \sqrt{(\frac{11}{12})^2 + (\frac7{20})^2} - a < 1 - \frac12$,
as $(\frac{11}{12})^2 + (\frac7{20})^2 = \frac{1733}{1800} < 1$. Then
$a \le \rho(\alpha)\cos\alpha < \frac12 + \frac{11}{12}\cos\alpha - \frac7{20}\sin\alpha$
by the first bullet, which gives $-d_e < \frac12$. The first bullet at
$\frac\pi2 - \alpha$ gives
$b \le \rho(\alpha)\sin\alpha < \frac12 + \frac{11}{12}\sin\alpha - \frac7{20}\cos\alpha$,
that is $d_f < \frac12$. Finally $b = a\tan\alpha \ge \frac12\tan\alpha$ and
the second bullet give $-d_f < \frac12$.

(2) and (3). Turn $\psi$ to the horizontal; the centre direction is then at an
angle $\beta$ with $|\beta| \le \omega$, and the point $(\lambda, 0)$ has the
coordinates $d_e = \lambda\cos(\alpha + \beta) - a$ and
$d_f = -\lambda\sin(\alpha + \beta) + b$. Now $d_e \le \lambda - a < \frac12$
by the hypothesis on $a$; $a - \lambda\cos(\alpha + \beta) \le a - \lambda\cos(\alpha + \omega) < \frac12$
by the first bullet and $C_- < \lambda\cos\omega$, $D > \lambda\sin\omega$; the first
bullet at $\frac\pi2 - \alpha$ gives $b < \frac12 + \lambda\sin(\alpha - \omega)$,
so $d_f < \frac12$; and the second bullet with $C_+ > \lambda\cos\omega$ and
$b \ge A_0\tan\alpha$ gives $\lambda\sin(\alpha + \omega) - b < \frac12$, so
$-d_f < \frac12$. For the consequences, if two centre directions were at most
$2\omega$ apart, the direction $\psi$ halfway between them would be within $\omega$ of
both, and $o + \lambda u(\psi)$ would lie in both open squares. $\square$

*Lean:
[`Eight.Arithmetic.centralBandP`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L39),
[`Eight.Arithmetic.centralBandV`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L49),
[`Eight.Arithmetic.segment_P_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L99),
[`Eight.Arithmetic.segment_V_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L109),
[`Eight.Arithmetic.bandA_P_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L117),
[`Eight.Arithmetic.bandA_V_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L131),
[`Eight.Arithmetic.bandB_P_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L141),
[`Eight.Arithmetic.bandB_V_positive`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L149),
[`Eight.Arithmetic.centralBandP_normalized`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L162),
[`Eight.Arithmetic.centralBandV_normalized`](../../SquaresInCircles/Eight/Arithmetic/CentralBandPolynomials.lean#L174),
[`Eight.CentralBand.bandA_sides`](../../SquaresInCircles/Eight/CentralCore.lean#L1339),
[`Eight.CentralBand.bandB_sides`](../../SquaresInCircles/Eight/CentralCore.lean#L1351),
[`Eight.CentralBand.RayData.common_point_A`](../../SquaresInCircles/Eight/CentralCore.lean#L1632),
[`Eight.CentralBand.RayData.common_point_B`](../../SquaresInCircles/Eight/CentralCore.lean#L1658),
[`Eight.CentralBand.closed_caps_strictly_separated`](../../SquaresInCircles/Eight/CentralCore.lean#L1684).*

![Two graphs on a common logarithmic scale from 10^3 to 10^6 millionths. Left: the polynomial P of the segment case against u from 0 to 1, positive throughout, with its Bernstein control points on the three cells [0, 1/4], [1/4, 1/2] and [1/2, 1] drawn as polygons with dots, the least of them, about 0.003, on the middle cell. Right: the polynomial V of the segment case against u from 0 to 3/7, positive, with its control points on the two cells [0, 3/14] and [3/14, 3/7]](figures/appendix-k/polys.svg)

*Figure K.3.* The polynomials $P$ and $V$ of the segment case of Lemma K.4
(curves), in units of $10^{-6}$ on a common logarithmic scale, and their
Bernstein control points on the cells of Table K.2 (polygons). All control
points are positive, so the polynomials are.

![Four squares in the disk of squared radius Q0, part of whose circle is dashed, each turned so that its centre direction is the horizontal axis through o: two with the frame angle 0 and two with the frame angle 45 degrees, each with its centre as near to o as a > 1/2 allows and as far as the disk allows. All four contain the vertical segment V at x = 11/12 from y = -7/20 to 7/20, drawn thick](figures/appendix-k/segment.svg)

*Figure K.4.* Lemma K.4 (1): every square in the disk of squared radius $Q_0$
with $a > \frac12$, its centre direction turned to the horizontal, contains
the segment $V$ (thick). Drawn are squares at the corners of the allowed
states.

## K.4 Directions blocked by a rectangle

Let $\Lambda = \frac{11}{12}$, $\kappa = \frac7{20}$,
$r_0 = \sqrt{\Lambda^2 + \kappa^2}$, so $r_0^2 = \frac{1733}{1800} < 1$, and
$\phi_0 = \arctan\frac\kappa\Lambda$, and let $R_\psi$ be the rotation by
$\psi$ about $o$. For $\Lambda \le A_1 < r_0$ and $y \ge 0$, let
$T_{A_1}(y) = [0, A_1] \times [0, y]$, $k = \sqrt{r_0^2 - A_1^2}$, and

```math
F_{A_1}(y) = \begin{cases} \arctan\dfrac y{A_1} + \arccos\dfrac\Lambda{\sqrt{A_1^2 + y^2}}, & 0 \le y \le k, \\[6pt] E(y) = \arcsin\dfrac y{r_0} + \phi_0, & k \le y \le \Lambda, \\[6pt] \dfrac\pi2 + \arccos\dfrac\Lambda y, & \Lambda \le y \le r_0, \\[6pt] \dfrac\pi2 + \phi_0, & y \ge r_0 . \end{cases}
```

### Lemma K.5 (blocked directions)

For $0 \le \psi \le F_{A_1}(y)$ the rotated segment $R_\psi V$ meets
$T_{A_1}(y)$. Consequently, for $0 \le d \le \frac12$, every rotation
$R_\psi V$ with $-F_{A_1}(d) \le \psi \le F_{A_1}(1 - d)$ meets the rectangle
$[0, A_1] \times [-d, 1 - d]$, an interval of directions of length
$F_{A_1}(d) + F_{A_1}(1 - d)$.

*Proof.* If $p \in T_{A_1}(y)$ has $|p| \le r_0$ and
$\langle p, u(\psi)\rangle \ge \Lambda$, then
$q = \frac\Lambda{\langle p, u(\psi)\rangle}p$ lies in $T_{A_1}(y)$, as the
rectangle is star-shaped about $o$, and has
$\langle q, u(\psi)\rangle = \Lambda$ and a transverse coordinate of absolute
value at most $\sqrt{r_0^2 - \Lambda^2} = \kappa$; so $q \in R_\psi V$. If
$y < \Lambda$, the points $\Lambda u(\psi)$ cover the directions
$0 \le \psi \le \arcsin\frac y\Lambda$. For the first line of $F_{A_1}$ take
$p = (A_1, y)$, and for the second $p = (\sqrt{r_0^2 - y^2}, y)$; both lie in
the rectangle and in the disk of radius $r_0$, and the directions with
$\langle p, u(\psi)\rangle \ge \Lambda$ form an interval that contains the
direction of $p$, which is at most $\arcsin\frac y\Lambda$, and ends at
$F_{A_1}(y)$. So the two intervals join without a gap. If $y \ge \Lambda$, the
points $\Lambda u(\psi)$ cover $[0, \frac\pi2]$, and $p = (0, \min(y, r_0))$
gives the rest. Reflecting in the horizontal axis gives the negative
directions. $\square$

*Lean:
[`Eight.CentralForbidden.rectangle_segment_interval`](../../SquaresInCircles/Eight/CentralForbidden.lean#L133),
[`Eight.CentralForbidden.Row.Valid.forbidden`](../../SquaresInCircles/Eight/CentralForbidden.lean#L251),
[`Eight.central_rectangle_forbids`](../../SquaresInCircles/Eight/CentralCore.lean#L1811).*

![The rectangle T_Lambda(0.3) = [0, 11/12] x [0, 0.3], shaded, with o at its lower left corner, and seven copies of the segment V turned about o by equally spaced angles from 0 up to F_Lambda(0.3), drawn thin, the last one thick and red; each copy meets the rectangle, the last one only at the corner (A1, 0.3). The arc of directions from 0 to F_Lambda(0.3) is marked at o, and a dotted segment from o to the corner shows the radial projection of the corner onto the middle copy](figures/appendix-k/blocked.svg)

*Figure K.5.* Lemma K.5 for $A_1 = \Lambda$ and $y = 0.3$: the segment $V$
turned by every angle from 0 to $F_{\Lambda}(0.3)$ (thin; seven of them are
drawn) meets the rectangle $T_\Lambda(0.3)$ (shaded), the last only at its
corner; radial projection (dotted) moves a point of the rectangle onto the
turned segment.

### Lemma K.6 (two widths)

For $0 \le d \le \frac12$,

```math
F_\Lambda(d) + F_\Lambda(1 - d) > \tfrac{347}{200}, \qquad F_{19/20}(d) + F_{19/20}(1 - d) > \tfrac{899}{500} .
```

*Proof.* *The first width.* For $A_1 = \Lambda$ the first line reads
$F_\Lambda(y) = 2\arctan\frac y\Lambda$ for $0 \le y \le \kappa$; let
$d_0 = 1 - \Lambda = \frac1{12}$. For $0 \le d \le d_0$: if $1 - d \ge r_0$ the
sum is at least $\frac\pi2 + \phi_0 > \frac{157}{100} + \frac9{25}$; otherwise
$\Lambda \le 1 - d \le r_0$, and the derivative of the sum,
$\frac{2\Lambda}{\Lambda^2 + d^2} - \frac\Lambda{(1 - d)\sqrt{(1 - d)^2 - \Lambda^2}}$,
is at most $\frac2\Lambda - \frac\Lambda{r_0\kappa} < 0$, as
$\Lambda^4 > 4r_0^2\kappa^2$; so the minimum is at $d_0$, where the sum is
$\frac\pi2 + 2\arctan\frac1{11} > \frac{157}{100} + \frac9{50}$. For
$d_0 \le d \le \kappa$ the sum is $w(d) = 2\arctan\frac d\Lambda + E(1 - d)$;
comparing the two terms of $w'$ and squaring, $w'$ has the sign opposite to

```math
P_w(d) = d^4 + 6\Lambda^2 d^2 - 8\Lambda^2 d + 4\Lambda^2 - 3\Lambda^4 - 4\Lambda^2\kappa^2 ,
```

which decreases ($P_w' \le 4\kappa^3 + 12\Lambda^2\kappa - 8\Lambda^2 < 0$),
with $P_w(0.1379) > 0 > P_w(0.138)$. So $w$ has a single minimum, between
$0.1379$ and $0.138$, where
$w \ge 2\arctan\frac{0.1379}\Lambda + E(0.862) > \frac{149}{500} + \frac{1437}{1000} = \frac{347}{200}$.
For $\kappa \le d \le \frac12$ both terms are values of $E$, which is convex,
so the sum is at least $2E(\frac12) > 2 \cdot \frac{899}{1000}$.

*The second width.* Let $A_1 = \frac{19}{20}$; then $k^2 = \frac{217}{3600}$,
so $\frac1{12} < k < \frac14$. For $0 \le d \le \frac1{12}$ the first term is
at least $F_{A_1}(0) = \arccos\frac\Lambda{A_1} > \frac14$ and the second at
least $\frac\pi2$. For $\frac1{12} \le d \le k$, the derivative of the first
line is $\frac{A_1 + \Lambda d/\sqrt{A_1^2 + d^2 - \Lambda^2}}{A_1^2 + d^2} > \frac{A_1 + 5\Lambda/16}{r_0^2} > \frac54$,
and $F_{A_1}(\frac1{12}) > \frac9{25}$ as
$A_1\cos\frac9{25} + \frac1{12}\sin\frac9{25} > \Lambda$; so the sum exceeds
$\frac9{25} + \frac54(d - \frac1{12}) + E(1 - d)$, which decreases on
$[\frac1{12}, \frac14]$ (as $r_0^2 - (1 - d)^2 \le \frac{1441}{3600} < \frac{16}{25}$),
and at $\frac14$ exceeds $\frac9{25} + \frac5{24} + \frac{123}{100} = \frac{1079}{600}$.
For $k \le d \le \frac12$, convexity again gives at least
$2E(\frac12) > \frac{899}{500}$.

The trigonometric bounds come from the alternating series: the bounds
$E(0.862) > 1.437$, $E(\frac12) > 0.899$ and $E(\frac34) > 1.23$ follow
from $y - \Lambda S_9(x) + \kappa C_{10}(x) > 0$ at $(x, y) = (1.437, 0.862)$,
$(0.899, \frac12)$, $(1.23, \frac34)$, where $S_9$ and $C_{10}$ are the Taylor
polynomials of sine and cosine of degrees 9 and 10 and
$\Lambda\sin x - \kappa\cos x$ increases on $[0, \frac\pi2]$; and
$\arctan x > x - \frac{x^3}3$ gives the arctangent bounds. $\square$

The formal proof checks the two widths differently, by tables of rectangle
rows: 128 rows for the first width and 102 for the second, each covering an
interval of $d$ by an explicit point of the rectangle at an explicit angle,
with a bound on its squared distance from $o$ and a Taylor bound for its
projection, as in the proof of Lemma K.5; the rows of each table cover
$[0, \frac12]$.

*Lean:
[`Eight.CentralForbidden.bandA_cover`](../../SquaresInCircles/Eight/CentralForbidden.lean#L681),
[`Eight.CentralForbidden.bandA_forbidden`](../../SquaresInCircles/Eight/CentralForbidden.lean#L1321),
[`Eight.CentralForbidden.bandB_cover`](../../SquaresInCircles/Eight/CentralForbidden.lean#L1639),
[`Eight.CentralForbidden.bandB_forbidden`](../../SquaresInCircles/Eight/CentralForbidden.lean#L2149).*

![The two widths as functions of d from 0 to 1/2: the upper curve F_{19/20}(d) + F_{19/20}(1 - d) and the lower curve F_Lambda(d) + F_Lambda(1 - d), each with kinks and a steep drop near d = 1/12, where the definition of F changes; both stay above their dashed horizontal bounds 899/500 and 347/200, the lower one coming within 0.002 of its bound near d = 0.138](figures/appendix-k/widths.svg)

*Figure K.6.* Lemma K.6: the widths
$F_\Lambda(d) + F_\Lambda(1 - d)$ and $F_{19/20}(d) + F_{19/20}(1 - d)$ of the
blocked intervals (curves), above $\frac{347}{200}$ and $\frac{899}{500}$
(dashed).

## K.5 Proof of Theorem 11.10

*Proof of Theorem 11.10.* Let $K$, $(a, u)$ and $\Delta$ be as in §K.2, and
suppose $a \ge \frac5{12}$. In the frame of $K$,
$K = [a - \frac12, a + \frac12] \times [u - \frac12, u + \frac12]$; put
$d = \frac12 - u \in (0, \frac12]$.

If $\frac5{12} \le a \le \frac9{20}$, then $\overline K$ contains
$[0, \Lambda] \times [-d, 1 - d]$. By Lemmas K.5 and K.6 there is an interval
$J$ of directions, of length more than $\frac{347}{200}$, such that the
segment $R_\psi V$ meets $\overline K$ for every $\psi \in J$. No exterior
square has its centre direction in $J$: by Lemma K.4 (1), turned to its
centre direction, its segment lies in its open square, and a point of
$\overline K$ in an open set meets $K^\circ$ as well. By Lemma K.3,
$A > \frac{107}{200}$ for every exterior square, so by Lemma K.4 (3) the seven
centre directions, which lie in the complement of $J$, are pairwise more than
$\frac{19}{25}$ apart: the six gaps between consecutive ones in that arc add
up to more than $\frac{114}{25}$. Then

```math
2\pi > \tfrac{347}{200} + 6 \cdot \tfrac{19}{25} = \tfrac{1259}{200} > \tfrac{44}7 ,
```

which is false as $\pi < \frac{22}7$. If $\frac9{20} \le a < \frac12$, then
$\overline K$ contains $[0, \frac{19}{20}] \times [-d, 1 - d]$, the blocked
interval is longer than $\frac{899}{500}$, and Lemmas K.3 and K.4 (2) give
gaps of more than $\frac{3741}{5000}$; then
$2\pi > \frac{899}{500} + 6 \cdot \frac{3741}{5000} = \frac{7859}{1250} > \frac{44}7$,
again false. Hence $a < \frac5{12}$.

Every point $p$ of $\overline D(o, \frac1{12})$ then has
$|p_x - a| \le \frac1{12} + a < \frac12$ and
$|p_y - u| \le \frac1{12} + u < \frac12$ in the frame of $K$, so
$\overline D(o, \frac1{12}) \subset K^\circ$. Another closed square cannot meet
this disk, since a common point would be a limit of interior points of that
square lying in $K^\circ$; and a closed square is compact, so its distance
from $o$ is attained and exceeds $\frac1{12}$. $\square$

*Lean:
[`Eight.seven_rays_avoid_interval_budget`](../../SquaresInCircles/Eight/CentralCore.lean#L1738),
[`Eight.central_core_and_exteriors`](../../SquaresInCircles/Eight/CentralCore.lean#L1837),
[`Eight.containsCore_of_center_bounds`](../../SquaresInCircles/Eight/CentralCore.lean#L313),
[`Eight.strictCoreAvoiding_of_containsCore`](../../SquaresInCircles/Eight/CentralCore.lean#L385).*

![The circle of directions about o with a shaded sector of length 347/200, the directions blocked by a shallow central square, and seven rays, the centre directions, placed one after another at the least gap 19/25 starting from one edge of the sector, with the six gaps marked; the seventh ray, red, falls about 0.012 inside the shaded sector](figures/appendix-k/rays.svg)

*Figure K.7.* The proof of Theorem 11.10. A shallow central square blocks an
interval of directions longer than $\frac{347}{200}$ (shaded); the seven centre
directions would need six gaps of more than $\frac{19}{25}$ in the rest. Drawn
at the least gaps, the seventh direction (red) already falls inside the blocked
interval, since $\frac{347}{200} + 6 \cdot \frac{19}{25} > 2\pi$.

## K.6 A square beyond a line

### Lemma K.7 (a square beyond a line)

Let a unit square lie in the closed disk of squared radius $Q$ about $o$, and
let every point $p$ of it satisfy $\langle n, p\rangle \ge d$ for a unit vector
$n$ and a number $d \ge 0$. Then $Q \ge (d + 1)^2 + \frac14$.

*Proof.* Choose the frame $e$, $f$ of the square with
$c = \langle n, e\rangle \ge s = \langle n, f\rangle \ge 0$, so
$c^2 + s^2 = 1$. If $d'$ is the least value of $\langle n, \cdot\rangle$ on the
square, the midpoint $m$ of the side reached along $e$ has

```math
\langle n, m\rangle = d' + c + \tfrac s2 \ge d + 1 ,
```

as $(c + \frac s2)^2 = 1 + cs - \frac34 s^2 \ge 1 + \frac{s^2}4 \ge 1$. The two
ends $m \pm \frac12 f$ of that side have the mean squared distance
$|m|^2 + \frac14 \ge (d + 1)^2 + \frac14$ from $o$, so one of them is at
least that far. $\square$

*Lean:
[`Eight.boundary_forward_complete`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L254).*

![A unit square turned by 20 degrees, lying beyond the dashed vertical line at distance d = 11/12 from o and touching it with a corner; the midpoint m of its far side, on the horizontal axis at distance more than d + 1 from o, and the two ends of that side, joined to o by dotted segments. Two arcs of circles about o almost coincide, the dashed one of radius root((d + 1)^2 + 1/4) and the red dotted one of radius root Q0 just inside it; the lower end of the far side lies outside both](figures/appendix-k/cap.svg)

*Figure K.8.* Lemma K.7: a unit square beyond a line at distance $d$ from $o$
reaches distance $\sqrt{(d + 1)^2 + \frac14}$. For $d = \frac{11}{12}$ this is
more than $\sqrt{Q_0}$, so no square of a packing of eight lies beyond the far
side of an exterior square.
