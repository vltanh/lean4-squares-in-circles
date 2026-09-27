# Appendix D. The critical gap: the forward axis

[Contents](README.md) · [← Appendix C](appendix-c.md)

This appendix proves the critical-gap proposition ([Proposition 9.17](seven.md#proposition-917-the-critical-gap)) on
the forward axis, for the sign pairs that Appendix B leaves open. We use the
notation of Chapter 9: two admissible states $(a, u)$ and $(A, v)$
([Definition 9.4](seven.md#definition-94-states)), their labels $\ell = \ell(a, u)$ and
$\lambda = \ell(A, v)$ ([Definition 9.6](seven.md#definition-96-labels-and-markers)), their remainders $r(a, u)$ and $r(A, v)$
([Definition 9.4](seven.md#definition-94-states)), signs $s, t \in \lbrace 1, -1\rbrace$, and the canonical
pair $S$, $T$ with its support sums $\sigma_k$ ([Definition 9.12](seven.md#definition-912-canonical-pair-and-support-sums)). The
forward axis is $n_1 = u(\frac\pi2)$ in the chart of $S$. It points in the
direction of increasing angle, from the marker of $S$ towards the marker of $T$,
and

```math
\sigma_1 = \max_{\overline S}\,\langle\cdot, n_1\rangle - \min_{\overline T}\,\langle\cdot, n_1\rangle
```

compares how far $S$ reaches forward with how far $T$ reaches back. We must show
the *pair property* ([Definition B.1](appendix-b.md#definition-b1-the-gap-property)) at the gap $g = \frac\pi3$:
$\sigma_1 \ge 0$, and $\sigma_1 = 0$ only if the two states with the two signs
form a contact ([Definition 9.15](seven.md#definition-915-contacts)). Appendix B reduces capped labels to
active ones and settles the signs $(s, t) = (1, 1)$
([Proposition B.29](appendix-b.md#proposition-b29-the-forward-axis-with-positive-signs)). The other sectors are settled here.

| signs $(s, t)$ | label of $(a, u)$ | label of $(A, v)$ | statement | $\sigma_1 = 0$ only if |
| --- | --- | --- | --- | --- |
| $(1, -1)$ | any | axial or side | Proposition D.7 | $(a, u)$ axial state, $(A, v) = (1, \frac12)$ |
| $(-1, -1)$ | axial | axial or side | Proposition D.7 | $(a, u)$ axial state, $(A, v) = (1, \frac12)$ |
| $(-1, 1)$ | axial or side | axial or side | Proposition D.16 | $(a, u) = (A, v) = (1, \frac12)$ |
| $(-1, -1)$ | side | axial or side | Proposition D.26 | never |

These possible zeros are the contacts of the optimal packings: a side square
touching the top or bottom square, and the two squares of a side column
(Figure D.1).

Every proof follows the same pattern. First $\sigma_1$ is written in closed form
in one angle, the *turn*, which measures how far $T$ is turned from its position
at a contact. Then the support of $T$ is bounded below, either by Cauchy–Schwarz
on the disk $\varphi \le \frac{13}4$ (§D.2, §D.3) or by following the exact
boundary of the label regions (§D.4). What remains is an inequality in the turn
alone, which is reduced to exact polynomial checks.

![Three canonical pairs in the chart of S, each with the forward normal n1 drawn as a vertical arrow on the right and the shadows of S (blue) and T (green) on it; in each panel the dashed marker rays of S and T are pi/3 apart. Left, signs (1, −1): S = Q(1, 0), and T is an axis-parallel square above it that shares half of the top edge of S; the shadows touch. Middle, signs (−1, 1): S = Q(1, −1/2) and T = Q(1, 1/2) share an edge; the shadows touch. Right, signs (−1, −1): S = Q(1, −1/2), and T is turned by 30 degrees and pokes into S; the shadows overlap.](figures/appd-forward-pairs.svg)

*Figure D.1.* The three sectors of this appendix, each at one pair of states, in
the chart of $S$. On the right of each panel are the shadows of $S$ (blue) and
$T$ (green) on the forward axis $n_1$; $\sigma_1(\frac\pi3)$ is their overlap.
Left: the signs $(1, -1)$, the axial state $(1, 0)$ and the side state
$(1, \frac12)$, a contact with $\sigma_1 = 0$ (Proposition D.7). Middle: the
signs $(-1, 1)$ and two side states, a contact with $\sigma_1 = 0$ (Proposition
D.16). Right: the signs $(-1, -1)$, the side state $(1, \frac12)$ and the axial
state $(1, 0)$, with $\sigma_1 = \frac14(\sqrt3 - 1)$ (Proposition D.26).

## D.1 The forward support sum and the tools

**The closed form.** In the definition of the support sums ([Definition 9.12](seven.md#definition-912-canonical-pair-and-support-sums))
take $k = 1$ and $g = \frac\pi3$, so that the relative phase is
$d = \frac\pi3 + s\ell - t\lambda$. The first term is
$h(a, su, \frac\pi2) = su + \frac12$, and
$\frac\pi2 + \pi - d = \frac{7\pi}6 - s\ell + t\lambda$. Hence
([Lemma B.5](appendix-b.md#lemma-b5-support-sums-in-closed-form))

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 + su + h\left(A,\ tv,\ \tfrac{7\pi}6 - s\ell + t\lambda\right),
\qquad
h(A, b, z) = A\cos z + b\sin z + \tfrac12\left(\lvert\cos z\rvert + \lvert\sin z\rvert\right) .
\tag{D.1}
```

In each sector below the direction $\frac{7\pi}6 - s\ell + t\lambda$ is
$\pi - e$, $\frac{3\pi}2 + w$ or $\frac{3\pi}2 - d$ for a turn $e$, $w$ or $d$,
and we use $\cos(\pi - x) = -\cos x$, $\sin(\pi - x) = \sin x$,
$\cos(\frac{3\pi}2 \pm x) = \pm\sin x$ and $\sin(\frac{3\pi}2 \pm x) = -\cos x$.

**Cauchy–Schwarz on the disk.** Let $\varphi(A, v) \le \frac{13}4$, and let $p$,
$q$ and $c \ge 0$ be real numbers. If $\frac{13}4(p^2 + q^2) \le c^2$, then

```math
p\left(A + \tfrac12\right) + q\left(v + \tfrac12\right) \ge -c ,
```

and the inequality is strict if $\frac{13}4(p^2 + q^2) < c^2$ ([Lemma 9.11](seven.md#lemma-911-the-support-function)). Indeed, by Cauchy–Schwarz the square of the left side is at
most $(p^2 + q^2)\,\varphi(A, v) \le \frac{13}4(p^2 + q^2)$. Geometrically, the
disk $\varphi \le \frac{13}4$ is the disk of radius $\frac{\sqrt{13}}2$ about
$(-\frac12, -\frac12)$ in the $(A, v)$-plane; the least value of the linear form
on it is taken where one of its level lines supports the disk (Figure D.2), and
this least value is at least $-c$. The same holds for $(a, u)$ in place of
$(A, v)$.

![The admissible states in the (A, v)-plane: the region cut from the disk phi at most 13/4 (dashed circle) by A at least 1/2 and 0 at most v at most A, divided into axial labels (blue, below the dashed tie line), side labels (green) and capped labels (grey). The thick orange line 3A + 2v = 4, marked r(A, v) = 0, touches the circle at the side state (1, 1/2), where the normal (3, 2) is drawn; two thin parallel orange lines cut the disk.](figures/appd-disk-support.svg)

*Figure D.2.* The admissible states $(A, v)$, with axial labels (blue), side
labels (green) and capped labels (grey); the tie line (dashed) separates the
first two and meets the circle $\varphi = \frac{13}4$ at the transition state
$(a_0, u_0)$. A linear form $p(A + \frac12) + q(v + \frac12)$ is constant on
parallel lines (orange), and on the disk it is at least its value on the one
that supports the disk. Drawn is the case $(p, q) = -(\frac9{10}, \frac35)$ of
Proposition D.10, whose supporting line is $r(A, v) = 0$, touching at the side
state $(1, \frac12)$.

**Taylor bounds.** Put

```math
S_3(x) = x - \tfrac{x^3}6, \quad S_5(x) = S_3(x) + \tfrac{x^5}{120}, \quad S_7(x) = S_5(x) - \tfrac{x^7}{5040},
```

```math
C_2(x) = 1 - \tfrac{x^2}2, \quad C_4(x) = C_2(x) + \tfrac{x^4}{24}, \quad C_6(x) = C_4(x) - \tfrac{x^6}{720}, \quad
K_6(x) = 1 - x^2 + \tfrac{x^4}3 - \tfrac{2x^6}{45} .
```

Then $\cos x \ge C_2(x)$ for all real $x$, and for $x \ge 0$

```math
S_3(x) \le \sin x \le x, \qquad S_7(x) \le \sin x \le S_5(x), \qquad
C_6(x) \le \cos x \le C_4(x), \qquad \cos^2 x \ge K_6(x) .
\tag{D.2}
```

Starting from $\sin x \le x$, each of $1 - \cos x \le \frac{x^2}2$,
$\sin x \ge S_3$, $\cos x \le C_4$, $\sin x \le S_5$, $\cos x \ge C_6$,
$\sin x \ge S_7$ follows from the previous one by integrating from $0$ to $x$;
and $\cos^2 x = \frac12(1 + \cos 2x) \ge \frac12(1 + C_6(2x)) = K_6(x)$
([Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds)).

**Bernstein coefficients.** Let $p$ be a polynomial of degree at most $n$ and
$x_0 < x_1$. Its *Bernstein coefficients* on $[x_0, x_1]$ are the numbers
$c_0, \dots, c_n$ with

```math
p(x)\,(x_1 - x_0)^n = \sum_{i=0}^n c_i \binom ni (x - x_0)^i (x_1 - x)^{n-i} .
```

If $q(y) = p(x_0 + (x_1 - x_0)y) = \sum_k \alpha_k y^k$, then
$c_i = \sum_{k \le i} \binom ik \binom nk^{-1} \alpha_k$. If all $c_i$ are
positive, then $p > 0$ on $[x_0, x_1]$ ([Lemma A.10](appendix-a.md#lemma-a10-bernstein-criterion)), since every term
of the sum is nonnegative there and one of the two end terms is positive. The
four such certificates of this appendix are listed in full, with exact
coefficients, in Lemmas D.2, D.6 and D.12 (Figure D.3).

![Four graphs, each of a polynomial (black) on its interval with its Bernstein control polygon (orange, dashed, with dots): Q of degree 14 on [0, 1/3], R of degree 7 on [1/3, 11/7], H of degree 6 on [0, 1/6], and p5 of degree 5 on [0, 11/10]. All control points lie above the horizontal axis.](figures/appd-bernstein.svg)

*Figure D.3.* The four Bernstein certificates of this appendix. Each polynomial
(black) is drawn with its control polygon (orange), whose vertices are the
points $(x_0 + \frac in(x_1 - x_0), c_i)$. The graph lies in the convex hull of
the control points, which is why positive coefficients give a positive
polynomial. The last coefficient of $H$ is about $0.0003$: $H$ nearly vanishes
at $\frac16$, where Lemma D.6 changes its method.

**Constants.** We use $3.14 < \pi < \frac{22}7$, and occasionally the sharper
bounds of §2.1. Also $\frac{173}{100} < \sqrt3 < \frac{1733}{1000}$
([Lemma 9.5](seven.md#lemma-95-admissible-states)), since $1.73^2 = 2.9929$ and $1.733^2 = 3.003289$;
so $\frac7{10} < \sqrt3 - 1 < \frac{11}{15}$.

**Admissible states.** For an admissible state $(a, u)$ with label $\ell$ we use
the following facts from Chapter 9.

- $0 \le \ell \le \frac\pi4$, $\ell \le \mathrm{axial}(u) = \frac54u$ and
  $\ell \le \mathrm{side}(a, u)$ ([Lemma 9.7](seven.md#lemma-97-the-label)); and
  $\ell = 0$ only if $u = 0$ ([Lemma 9.7](seven.md#lemma-97-the-label)).
- $u < \frac{31}{40}$ ([Lemma 9.5](seven.md#lemma-95-admissible-states)) and $a \le \sqrt3 - \frac12$
  ([Lemma 9.5](seven.md#lemma-95-admissible-states)).
- $r(a, u) = 4 - 3a - 2u \ge 0$ ([Lemma 9.5](seven.md#lemma-95-admissible-states)), and, by
  [Lemma 9.7](seven.md#lemma-97-the-label),

  ```math
  \mathrm{side}(a, u) = \tfrac\pi6 + \tfrac56\left(u - \tfrac12\right) + \tfrac14 r(a, u)
  = \tfrac\pi6 - \tfrac54(a - 1) - \tfrac16 r(a, u) .
  \tag{D.3}
  ```

- If $r(a, u) = 0$, then $(a, u)$ is the side state $(1, \frac12)$
  ([Lemma 9.16](seven.md#lemma-916-contacts)), whose label is $\frac\pi6$ ([Lemma 9.16](seven.md#lemma-916-contacts)). If
  $u = 0$, then $(a, u)$ is an axial state ([Lemma 9.16](seven.md#lemma-916-contacts)).
- If the label is side, then $\ell > \frac9{25}$
  ([Lemma 9.8](seven.md#lemma-98-side-and-axial-labels)) and $a < \frac98$
  ([Lemma 9.8](seven.md#lemma-98-side-and-axial-labels)); and $u \le \frac12 + \frac65(\ell - \frac\pi6)$
  by (D.3) and $r \ge 0$.
- If the label is axial, then $u = \frac45\ell \le \frac\pi5$;
  $9a + 11u \le 2\pi + 7$, which is $\mathrm{axial}(u) \le \mathrm{side}(a, u)$
  multiplied by 12 ([Lemma 9.8](seven.md#lemma-98-side-and-axial-labels)); and $a + u < \frac{113}{80}$
  ([Lemma 9.8](seven.md#lemma-98-side-and-axial-labels)).

**The boundary of the label regions.** From Appendix B we use the following
objects and facts. Except for the two profiles at the end, they concern one
admissible state, which we write $(A, v)$, with label $\lambda$, or $\tau$ when
the label is a variable.

- The *tie line* $9A + 11v = 2\pi + 7$, where the axial and the side label
  agree, meets the circle $\varphi = \frac{13}4$ at the *transition state*
  $(a_0, u_0)$ ([Definition B.9](appendix-b.md#definition-b9-boundary-curves-and-special-states)), of label
  $s_0 = \frac54 u_0$ ([Definition B.9](appendix-b.md#definition-b9-boundary-curves-and-special-states)). We write $X_0 = a_0 + \frac12$ and
  $Y_0 = u_0 + \frac12$, so that $X_0^2 + Y_0^2 = \frac{13}4$
  ([Lemma B.10](appendix-b.md#lemma-b10-the-transition-state)), and $\frac{11}{10} < a_0 < \frac98$,
  $\frac{29}{100} < u_0 < \frac3{10}$, $\frac9{25} < s_0 < \frac25$
  ([Lemma B.10](appendix-b.md#lemma-b10-the-transition-state)) (numerically
  $(a_0, u_0) \approx (1.1198, 0.2914)$ and $s_0 \approx 0.3642$). Every
  admissible state with side label has $u_0 \le v$, $A \le a_0$ and
  $s_0 \le \lambda$ ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)).
- *Tie states.* Let $\mathrm{tie}(\tau) = \frac{2\pi + 7}9 - \frac{44}{45}\tau$.
  A state with side label $\tau$ lies on the line
  $A = \mathrm{tie}(\tau) + \frac49\left(v - \frac45\tau\right)$
  ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)). For $s_0 \le \tau \le \frac\pi4$ the tie state
  $(\mathrm{tie}(\tau), \frac45\tau)$ is admissible, and its label, its axial
  label and its side label all equal $\tau$ ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)).
- *The diagonal corner.* Let $r_d = \sqrt{13/8} - \frac12$, so that the diagonal
  state $(r_d, r_d)$ is on the circle, with
  $\frac{77475}{100000} < r_d < \frac{77476}{100000}$
  ([Lemma B.11](appendix-b.md#lemma-b11-the-diagonal-corner)). Its side label is
  $\tau_d = \frac\pi6 + \frac7{12} - \frac5{12}r_d$, and
  $\frac{18}{25} < \tau_d < \frac\pi4$ ([Lemma B.11](appendix-b.md#lemma-b11-the-diagonal-corner)). The
  diagonal state $(\mathrm{diag}(\tau), \mathrm{diag}(\tau))$ with
  $\mathrm{diag}(\tau) = \frac15(2\pi + 7 - 12\tau)$ has side label $\tau$, and
  $\mathrm{diag}(\tau_d) = r_d$ ([Lemma B.11](appendix-b.md#lemma-b11-the-diagonal-corner)).
- *The circle parametrised by the side label.* For $s_0 \le \tau \le \tau_d$ let
  $N = \frac{97}{144}$, $D(\tau) = \frac\pi6 + \frac{19}{24} - \tau$,
  $Z(\tau) = \sqrt{\frac{13}4N - D(\tau)^2}$, and
  $X(\tau) = \frac1N\left(\frac34D + \frac13Z\right)$,
  $Y(\tau) = \frac1N\left(-\frac13D + \frac34Z\right)$. Then
  $X^2 + Y^2 = \frac{13}4$, $\frac34X - \frac13Y = D$ and
  $\frac13X + \frac34Y = Z$ ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)), so the state
  $(X(\tau) - \frac12, Y(\tau) - \frac12)$ is on the circle and has side label
  $\tau$ ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)). It is the transition state at
  $\tau = s_0$ and the diagonal state $(r_d, r_d)$ at $\tau = \tau_d$
  ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)). On
  $[s_0, \tau_d]$ we have $\frac12 < D < 1$ ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)); $0 < Y$,
  $Y_0 \le Y \le X$, $\frac54 < X \le X_0$ and $1 < Z < \frac75$
  ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)); and $X' = -Y/Z$, $Y' = X/Z$, $Z' = D/Z$
  ([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)).
- *Side segments.* For $s_0 \le \tau \le \frac\pi4$ let
  $\mathrm{top}(\tau) = (\mathrm{top}_a(\tau), \mathrm{top}_u(\tau))$ be
  $(X(\tau) - \frac12, Y(\tau) - \frac12)$ if $\tau \le \tau_d$ and
  $(\mathrm{diag}(\tau), \mathrm{diag}(\tau))$ if $\tau > \tau_d$. It is
  admissible with side label $\tau$ ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)). Every
  admissible $(A, v)$ with side label $\tau$ lies on the *side segment* from the
  tie state to $\mathrm{top}(\tau)$:
  $\frac45\tau \le v \le \mathrm{top}_u(\tau)$ and
  $A = \mathrm{tie}(\tau) + \frac49(v - \frac45\tau)$
  ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)).
- *The axial boundary.* Let
  $\mathrm{circ}(v) = \sqrt{\frac{13}4 - (v + \frac12)^2} - \frac12$ and
  $\mathrm{line}(v) = \frac19(2\pi + 7 - 11v)$. Every admissible $(A, v)$ with
  axial label has $A \le \min(\mathrm{circ}(v), \mathrm{line}(v))$
  ([Proposition B.15](appendix-b.md#proposition-b15-the-axial-region)); the minimum is $\mathrm{circ}(v)$ for
  $0 \le v \le u_0$ and $\mathrm{line}(v)$ for $u_0 \le v \le r_d$
  ([Lemma B.12](appendix-b.md#lemma-b12-the-circle-over-the-u-axis)).
- *The target support on the boundary.* For a source label $\ell$ and a target
  label $\tau$ put $\delta = \frac\pi3 - \ell + \tau$ and

  ```math
  G_\delta(A, v) = -\left(A - \tfrac12\right)\sin\delta + \left(v + \tfrac12\right)\cos\delta .
  ```

  Its values at the axial state on the circle, at the tie state and at the top
  of the side segment of label $\tau$ are

  ```math
  \begin{aligned}
  G^{\mathrm{ax}}(\ell, \tau) &= -\left(X^{\mathrm{ax}}(\tau) - 1\right)\sin\delta + \left(\tfrac12 + \tfrac45\tau\right)\cos\delta, \qquad X^{\mathrm{ax}}(\tau) = \sqrt{\tfrac{13}4 - \left(\tfrac12 + \tfrac45\tau\right)^2}, \\
  G^{\mathrm{tie}}(\ell, \tau) &= -\left(\mathrm{tie}(\tau) - \tfrac12\right)\sin\delta + \left(\tfrac45\tau + \tfrac12\right)\cos\delta, \\
  G^{\mathrm{top}}(\ell, \tau) &= -\left(\mathrm{top}_a(\tau) - \tfrac12\right)\sin\delta + \left(\mathrm{top}_u(\tau) + \tfrac12\right)\cos\delta .
  \end{aligned}
  ```

  Here $X^{\mathrm{ax}}(\tau) - \frac12 = \mathrm{circ}(\frac45\tau)$. If
  $\frac25 \le \ell \le \frac\pi4$, then
  $\tau \mapsto G^{\mathrm{ax}}(\ell, \tau)$ is nonincreasing on $[0, s_0]$
  ([Proposition B.23](appendix-b.md#proposition-b23-the-circular-piece)), and, by
  [Proposition B.23](appendix-b.md#proposition-b23-the-circular-piece),

  ```math
  G^{\mathrm{ax}}(\ell, s_0) = -\left(a_0 - \tfrac12\right)\sin\left(\tfrac\pi3 - \ell + s_0\right) + Y_0\cos\left(\tfrac\pi3 - \ell + s_0\right) .
  ```

- *The switch.* Let $\psi = \arctan\frac94$, so that $0 < \psi < \frac\pi2$ and
  $\cos\psi = \frac49\sin\psi$; for $0 \le x \le \frac\pi2$,
  $\cos x - \frac49\sin x \ge 0$ if and only if $x \le \psi$
  ([Lemma B.24](appendix-b.md#lemma-b24-the-switch-angle)). Put
  $\mathrm{sw}(\ell) = \psi - \frac\pi3 + \ell$, so that $\delta \le \psi$ if
  and only if $\tau \le \mathrm{sw}(\ell)$. If $\frac25 \le \ell \le \frac\pi4$,
  $s_0 \le \tau \le \frac\pi4$ and $\tau \le \mathrm{sw}(\ell)$, then
  $G^{\mathrm{ax}}(\ell, s_0) \le G^{\mathrm{tie}}(\ell, \tau)$
  ([Proposition B.25](appendix-b.md#proposition-b25-the-straight-piece)).
- *Two profiles.* If $(a, u)$ is admissible with side label $\ell \ge \frac25$,
  then ([Lemma B.18](appendix-b.md#lemma-b18-the-transition-profile))

  ```math
  \tfrac12 - u + G^{\mathrm{ax}}(\ell, s_0) > 0 .
  \tag{D.4}
  ```

  For $\frac25 \le \ell \le \frac\pi4$ ([Lemma B.20](appendix-b.md#lemma-b20-the-diagonal-profile)),

  ```math
  K(\ell) = \tfrac65\left(\tfrac\pi6 - \ell\right) + \tfrac{51}{40}\cos\left(\tfrac{7\pi}{12} - \ell\right) - \tfrac{11}{40}\sin\left(\tfrac{7\pi}{12} - \ell\right) > 0 .
  \tag{D.5}
  ```

## D.2 Target sign negative

In this section $t = -1$, and $s = 1$ or the label of $(a, u)$ is axial. The
turn is $e = s\ell + \lambda - \frac\pi6$. The frame of $T$ is turned by
$d = \frac\pi3 + s\ell + \lambda = \frac\pi2 + e$ against that of $S$, so
$e = 0$ when $T$ is turned by a quarter turn, as when a side square touches the
top or bottom square (Figure D.1, left).

### Lemma D.1 (the support sum for target sign negative)

Let $(a, u)$ and $(A, v)$ be admissible states and $s \in \lbrace 1, -1\rbrace$,
and suppose that $s = 1$ or that the label of $(a, u)$ is axial. Let
$e = s\ell + \lambda - \frac\pi6$, and for real $e'$, $\rho$ put

```math
\beta(A, v; e', \rho) = \tfrac12 + \tfrac45\rho - \left(A - \tfrac12\right)\cos e' - v\sin e' + \tfrac12\lvert\sin e'\rvert .
```

Then on the forward axis, for the signs $(s, -1)$,
$\sigma_1(\frac\pi3) \ge \beta(A, v; e, s\ell)$.

*Proof.* By (D.1) with $t = -1$ the direction is
$\frac{7\pi}6 - s\ell - \lambda = \pi - e$, and

```math
h(A, -v, \pi - e) = -A\cos e - v\sin e + \tfrac12\left(\lvert\cos e\rvert + \lvert\sin e\rvert\right) .
```

As $0 \le \ell, \lambda \le \frac\pi4$, the turn satisfies
$-\frac{5\pi}{12} \le e \le \frac\pi3$, so $\cos e \ge 0$ and

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 + su - \left(A - \tfrac12\right)\cos e - v\sin e + \tfrac12\lvert\sin e\rvert .
```

It remains to show $su \ge \frac45 s\ell$. If $s = 1$ this is
$\ell \le \mathrm{axial}(u) = \frac54u$. If $s = -1$, the label is axial, so
$\ell = \frac54u$ and $su = -u = \frac45 s\ell$. $\square$

*Lean:
[`Seven.forward_negative_target_lower`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L22),
[`Seven.rawTarget`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L19).*

### Lemma D.2 (an axial target at a negative turn)

Let $(A, v)$ be admissible with axial label, and $0 \le z \le \frac\pi2$. Then

```math
1 + \tfrac{2\pi}{15} - \tfrac45z + \cos z - \left(A + \tfrac12\right)\cos z - \left(v + \tfrac12\right)(1 - \sin z) > 0 .
```

*Proof.* Put $X = A + \frac12$ and $Y = v + \frac12$, so that
$X^2 + Y^2 = \varphi(A, v) \le \frac{13}4$, and
$\Lambda(z) = 1 + \frac{2\pi}{15} - \frac45z + \cos z$. The claim is
$X\cos z + Y(1 - \sin z) < \Lambda(z)$, a linear bound on the disk. The label is
axial, so $9A + 11v \le 2\pi + 7$, that is

```math
9X + 11Y \le 2\pi + 17 .
\tag{D.6}
```

1. *For $z \le \frac13$ we split off the tie line.* Let
   $n = \frac3{40}(1 - 2\sin z)$ and

   ```math
   L(z) = \cos z - \tfrac{11}{40} - \tfrac\pi{60} - \tfrac45z + \left(\tfrac{51}{20} + \tfrac{3\pi}{10}\right)\sin z .
   ```

   Then $n \ge 0$, as $\sin z \le z \le \frac13$, and expanding gives
   $L(z) + (2\pi + 17)n = \Lambda(z)$. Hence

   ```math
   \Lambda(z) - X\cos z - Y(1 - \sin z)
   = \Bigl[L(z) - (\cos z - 9n)X - (1 - \sin z - 11n)Y\Bigr] + n\,(2\pi + 17 - 9X - 11Y) .
   ```

   The last term is nonnegative by (D.6). We show that the bracket is positive
   by Cauchy–Schwarz on the disk with $p = -(\cos z - 9n)$,
   $q = -(1 - \sin z - 11n)$ and $c = L(z)$. For this we need $L(z) \ge 0$ and
   $\frac{13}4(p^2 + q^2) < L(z)^2$.
2. *A lower bound for $L$.* As $\pi > 3.14 = \frac{157}{50}$, the coefficient
   $\frac{51}{20} + \frac{3\pi}{10}$ exceeds $\frac{873}{250}$; as
   $\pi < \frac{22}7$, $\frac{11}{40} + \frac\pi{60} < \frac{55}{168}$. With
   $\cos z \ge C_6(z)$, $\sin z \ge 0$ and $\sin z \ge S_7(z)$ from (D.2),
   $L(z) \ge P(z)$, where
   $P(z) = C_6(z) - \frac{55}{168} - \frac45z + \frac{873}{250}S_7(z)$, that is

   ```math
   P(z) = \tfrac{113}{168} + \tfrac{673}{250}z - \tfrac{1}{2}z^{2} - \tfrac{291}{500}z^{3} + \tfrac{1}{24}z^{4} + \tfrac{291}{10000}z^{5} - \tfrac{1}{720}z^{6} - \tfrac{97}{140000}z^{7} .
   ```

   On $[0, \frac13]$ we have $z^2 \le \frac19$ and $z^3 \le \frac1{27}$, the
   linear term of $P$ is nonnegative, and

   ```math
   \tfrac1{24}z^4 - \tfrac1{720}z^6 = z^4\left(\tfrac1{24} - \tfrac{z^2}{720}\right) \ge 0, \qquad
   \tfrac{291}{10000}z^5 - \tfrac{97}{140000}z^7 = \tfrac{873}{250}z^5\left(\tfrac1{120} - \tfrac{z^2}{5040}\right) \ge 0 .
   ```

   So

   ```math
   P(z) \ge \tfrac{113}{168} - \tfrac1{18} - \tfrac{291}{13500} = \tfrac{37517}{63000} > \tfrac12 ,
   ```

   and $L(z) \ge P(z) > \frac12$.
3. *An upper bound for $p^2 + q^2$.* We have
   $\cos z - 9n = \cos z - \frac{27}{40} + \frac{27}{20}\sin z$ and
   $1 - \sin z - 11n = \frac7{40} + \frac{13}{20}\sin z$. Expanding the squares
   and using $\cos^2 z = 1 - \sin^2 z$,

   ```math
   p^2 + q^2 = \tfrac{1189}{800} - \tfrac{27}{20}\cos z + \tfrac{27}{10}\sin z\cos z + \tfrac{249}{200}\sin^2 z - \tfrac{319}{200}\sin z .
   ```

   By (D.2), $\cos z \ge C_6(z)$, $0 \le \sin z\cos z \le S_5(z)C_4(z)$ (both
   factors are nonnegative), $\sin^2 z = 1 - \cos^2 z \le 1 - K_6(z)$ and
   $\sin z \ge S_7(z)$. So $p^2 + q^2 \le U(z)$, where

   ```math
   \begin{aligned}
   U(z) &= \tfrac{1189}{800} - \tfrac{27}{20}C_6(z) + \tfrac{27}{10}S_5(z)C_4(z) + \tfrac{249}{200}\bigl(1 - K_6(z)\bigr) - \tfrac{319}{200}S_7(z) \\
   &= \tfrac{109}{800} + \tfrac{221}{200}z + \tfrac{48}{25}z^{2} - \tfrac{1841}{1200}z^{3} - \tfrac{377}{800}z^{4} + \tfrac{8321}{24000}z^{5} + \tfrac{1373}{24000}z^{6} - \tfrac{29921}{1008000}z^{7} + \tfrac{3}{3200}z^{9} .
   \end{aligned}
   ```

4. *The certificate.* The polynomial $Q = P^2 - \frac{13}4U$ of degree 14 is

   ```math
   \begin{aligned}
   Q(z) = {} & \tfrac{13553}{1411200} + \tfrac{2531}{84000}z + \tfrac{877393}{2625000}z^{2} + \tfrac{253867}{168000}z^{3} - \tfrac{163280113}{126000000}z^{4} - \tfrac{315081}{1120000}z^{5} + \tfrac{1005239077}{3780000000}z^{6} + \tfrac{1476347}{141120000}z^{7} \\
   & - \tfrac{1206721}{35000000}z^{8} + \tfrac{11341}{6720000}z^{9} + \tfrac{29059789}{18900000000}z^{10} - \tfrac{97}{700000}z^{11} - \tfrac{544253}{14175000000}z^{12} + \tfrac{97}{50400000}z^{13} + \tfrac{9409}{19600000000}z^{14} ,
   \end{aligned}
   ```

   and its Bernstein coefficients on $[0, \frac13]$ are

   ```math
   \begin{aligned}
   & \tfrac{13553}{1411200},\ \tfrac{72827}{7056000},\ \tfrac{393747163}{34398000000},\ \tfrac{2710739309}{206388000000},\ \tfrac{9910498733}{638512875000},\ \tfrac{153072314621}{8172964800000},\ \tfrac{47296571468413}{2068781715000000},\ \tfrac{3708166534047959}{132402029760000000}, \\
   & \tfrac{188854262621881}{5516751240000000},\ \tfrac{6257753867831}{150456852000000},\ \tfrac{6998517462046433}{139642765762500000},\ \tfrac{48606823214392757}{812467000800000000},\ \tfrac{29832818108969789}{421857865800000000},\ \tfrac{34918908326684453}{421857865800000000},\ \tfrac{80964059146525129}{843715731600000000} ,
   \end{aligned}
   ```

   all positive (they increase from about $0.0096$ to about $0.096$). So $Q > 0$
   on $[0, \frac13]$, and as $0 < P \le L$,

   ```math
   \tfrac{13}4\left(p^2 + q^2\right) \le \tfrac{13}4U(z) < P(z)^2 \le L(z)^2 .
   ```

   Cauchy–Schwarz on the disk makes the bracket of step 1 positive, which proves
   the claim for $0 \le z \le \frac13$.
5. *For $\frac13 < z \le \frac\pi2$ Cauchy–Schwarz alone suffices.* Let
   $\gamma = \cos\frac z2 - \sin\frac z2$, which is nonnegative as
   $0 \le \frac z2 \le \frac\pi4$. Then
   $\cos^2 z + (1 - \sin z)^2 = 2 - 2\sin z = 2\gamma^2$, and Cauchy–Schwarz on
   the disk with $p = -\cos z$, $q = -(1 - \sin z)$ and
   $c = \frac{51}{20}\gamma$ applies, since
   $\frac{13}4(p^2 + q^2) = \frac{13}2\gamma^2$ and
   $\frac{13}2 = \frac{2600}{400} < \frac{2601}{400} = (\frac{51}{20})^2$. So
   $X\cos z + Y(1 - \sin z) \le \frac{51}{20}\gamma$, and it suffices that
   $\Lambda(z) - \frac{51}{20}(\cos\frac z2 - \sin\frac z2) > 0$. By
   $\frac{2\pi}{15} > \frac{157}{375}$ (that is, $\pi > \frac{157}{50}$) and
   (D.2) at $z$ and at $\frac z2$, this is at least

   ```math
   \begin{aligned}
   R(z) &= 1 + \tfrac{157}{375} - \tfrac45z + C_6(z) - \tfrac{51}{20}\Bigl(C_4\bigl(\tfrac z2\bigr) - S_7\bigl(\tfrac z2\bigr)\Bigr) \\
   &= -\tfrac{197}{1500} + \tfrac{19}{40}z - \tfrac{29}{160}z^{2} - \tfrac{17}{320}z^{3} + \tfrac{269}{7680}z^{4} + \tfrac{17}{25600}z^{5} - \tfrac{1}{720}z^{6} - \tfrac{17}{4300800}z^{7} .
   \end{aligned}
   ```

   Its Bernstein coefficients of degree 7 on $[\frac13, \frac{11}7]$ are

   ```math
   \tfrac{27834859}{5225472000},\ \tfrac{21646979107}{329204736000},\ \tfrac{85094698273}{768144384000},\ \tfrac{83663391929}{597445632000},\ \tfrac{650018406713}{4182119424000},\ \tfrac{224217116981}{1394039808000},\ \tfrac{1222825127771}{7589772288000},\ \tfrac{8516973787387}{53128406016000} ,
   ```

   all positive, and $\frac\pi2 < \frac{11}7$; so $R > 0$ on
   $[\frac13, \frac\pi2]$. $\square$

![Graph over z from 0 to pi/2: the least value of the left side of Lemma D.2 over the admissible states with axial label (blue), near 0.008 at z = 0 and rising to about 0.16; just below it the orange curve P minus the root of 13U/4 on [0, 1/3]; on [1/3, pi/2] the green Cauchy–Schwarz bound and the dashed orange curve R, which almost coincide, start near 0.005 at z = 1/3 and approach the blue curve.](figures/appd-axial-profile.svg)

*Figure D.4.* Lemma D.2. The left side of the lemma, minimised over the
admissible states with axial label (blue), and the lower bounds of the proof:
$P - \sqrt{13U/4}$ on $[0, \frac13]$ (orange), and on $[\frac13, \frac\pi2]$ the
Cauchy–Schwarz bound $\Lambda(z) - \frac{51}{20}(\cos\frac z2 - \sin\frac z2)$
(green) and $R$ (dashed). Near $z = 0$ the minimum is small; there the
Cauchy–Schwarz bound alone is negative, and the tie line (D.6) is needed.

*Lean:
[`Seven.axial_target_support`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L56).*

### Lemma D.3 (an axial target)

Let $(A, v)$ be admissible with axial label $\lambda$, and let $e$, $\rho$ be
real numbers with $-\frac\pi2 \le e \le \frac\pi3$ and
$e = \rho + \lambda - \frac\pi6$. Then $\beta(A, v; e, \rho) > 0$.

*Proof.* As $\lambda = \frac54v$, we have $\rho = e - \lambda + \frac\pi6$ and
$\frac45\rho = \frac45e - v + \frac{2\pi}{15}$, so

```math
\beta(A, v; e, \rho) = \tfrac12 + \tfrac{2\pi}{15} + \tfrac45e - \left(A - \tfrac12\right)\cos e - v(1 + \sin e) + \tfrac12\lvert\sin e\rvert .
```

If $e \ge 0$, then $\sin e \ge 0$, as $e \le \frac\pi3$, and expanding shows

```math
\beta = \left(1 + \tfrac{2\pi}{15} - A - v\right) + \left(A - \tfrac12\right)(1 - \cos e) + \left(\tfrac{13}{20} - v\right)\sin e + \tfrac3{20}(e - \sin e) + \tfrac{13}{20}e .
```

The first term is positive: $A + v < \frac{113}{80}$ ([Lemma 9.8](seven.md#lemma-98-side-and-axial-labels)) and
$\frac{2\pi}{15} > \frac{33}{80}$, as $\pi > \frac{99}{32}$. The others are
nonnegative, as $A \ge \frac12$, $v \le \frac\pi5 < \frac{13}{20}$ and
$0 \le \sin e \le e$.

If $e < 0$, let $z = -e$, so $0 < z \le \frac\pi2$, $\sin e = -\sin z \le 0$ and
$\lvert\sin e\rvert = \sin z$. Then

```math
\beta = 1 + \tfrac{2\pi}{15} - \tfrac45z + \cos z - \left(A + \tfrac12\right)\cos z - \left(v + \tfrac12\right)(1 - \sin z) ,
```

which is positive by Lemma D.2. $\square$

*Lean:
[`Seven.negative_target_axial_pos`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L253).*

### Lemma D.4 (the tangent at the transition state)

Let $(A, v)$ be admissible with side label. Then
$\frac{12}{25}(v - u_0) \le a_0 - A$.

*Proof.* Write $A + \frac12 = X_0 + (A - a_0)$ and
$v + \frac12 = Y_0 + (v - u_0)$. Since
$\varphi(A, v) \le \frac{13}4 = X_0^2 + Y_0^2$, expanding gives

```math
2X_0(A - a_0) + 2Y_0(v - u_0) \le -(A - a_0)^2 - (v - u_0)^2 \le 0 :
```

the state lies on the side of the tangent of the circle at the transition state
that contains the disk (Figure D.5). By
[Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label), $v - u_0 \ge 0$. By the bounds
on $a_0$ and $u_0$,
$\frac{12}{25}X_0 < \frac{12}{25}\cdot\frac{13}8 = \frac{39}{50}$ and
$\frac{39}{50} < \frac{79}{100} < Y_0$. Hence
$\frac{12}{25}X_0(v - u_0) \le Y_0(v - u_0) \le X_0(a_0 - A)$, and we divide by
$X_0 > 0$. $\square$

![A magnified part of the (A, v)-plane around the transition state: the thin curved region of side labels between the dashed tie line and the circle, above the horizontal line v = u0 and to the left of the vertical line A = a0, and the orange tangent of the circle at the transition state, with the region on its inner side.](figures/appd-transition-tangent.svg)

*Figure D.5.* Lemma D.4. The states with side label (green) lie in the quarter
plane $v \ge u_0$, $A \le a_0$ and on the inner side of the tangent (orange) of
the circle at the transition state $(a_0, u_0)$. In that quarter plane the
tangent, of slope $-X_0/Y_0$, may be replaced by the slightly steeper line
$\frac{12}{25}(v - u_0) = a_0 - A$ of slope $-\frac{25}{12}$, which at this
scale cannot be told apart from it.

*Lean:
[`Seven.side_transition_trade`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L137).*

### Lemma D.5 (a side target at a nonnegative turn)

Let $(A, v)$ be admissible, and for real $e$ put

```math
\beta_{\mathrm{side}}(A, v; e) = \tfrac45e + \tfrac2{15}r(A, v) + \left(A - \tfrac12\right)(1 - \cos e) - v\sin e + \tfrac12\lvert\sin e\rvert .
```

If $0 \le e \le \frac\pi3$, then
$\beta_{\mathrm{side}}(A, v; e) \ge \frac{21}{40}e + \frac2{15}r(A, v)$.

*Proof.* Here $0 \le \sin e \le e$, and expanding shows

```math
\beta_{\mathrm{side}}(A, v; e) - \tfrac{21}{40}e - \tfrac2{15}r(A, v)
= \left(A - \tfrac12\right)(1 - \cos e) + \left(\tfrac{31}{40} - v\right)\sin e + \tfrac{11}{40}(e - \sin e) .
```

The three terms are nonnegative, since $A \ge \frac12$ and $v < \frac{31}{40}$
([Lemma 9.5](seven.md#lemma-95-admissible-states)). $\square$

*Lean:
[`Seven.sideTarget`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L157),
[`Seven.sideTarget_positive_angle`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L161).*

### Lemma D.6 (a side target at a negative turn)

Let $(A, v)$ be admissible with side label, and $0 < z < 1$. Then
$\beta_{\mathrm{side}}(A, v; -z) > 0$.

*Proof.* As $0 < z < \pi$, $\lvert\sin(-z)\rvert = \sin z$. Substituting
$r(A, v) = 4 - 3A - 2v$ and expanding gives

```math
\beta_{\mathrm{side}}(A, v; -z) = E(A, v) := L_0(z) + \left(\tfrac35 - \cos z\right)\left(A + \tfrac12\right) + \left(\sin z - \tfrac4{15}\right)\left(v + \tfrac12\right),
\qquad L_0(z) = \cos z - \tfrac2{15} - \tfrac45z .
```

We treat three ranges of $z$ (Figure D.6).

1. *For $0 < z \le \frac16$, Cauchy–Schwarz on the disk.* Here
   $L_0(z) \ge 1 - \frac1{72} - \frac4{15} = \frac{259}{360} > 0$, by
   $\cos z \ge C_2(z)$. Let $p = \frac35 - \cos z$ and
   $q = \sin z - \frac4{15}$. Expanding and using $\sin^2 z + \cos^2 z = 1$,

   ```math
   L_0(z)^2 - \tfrac{13}4\left(p^2 + q^2\right) = \cos^2 z + \left(\tfrac{109}{30} - \tfrac85z\right)\cos z + \tfrac{26}{15}\sin z + \left(\tfrac2{15} + \tfrac45z\right)^2 - \tfrac{2093}{450} .
   ```

   By (D.2), $\cos^2 z \ge K_6(z)$,
   $\frac{109}{30}\cos z \ge \frac{109}{30}C_6(z)$,
   $-\frac85z\cos z \ge -\frac85zC_4(z)$ and
   $\frac{26}{15}\sin z \ge \frac{26}{15}S_7(z)$. Replacing each term by its
   bound gives exactly $zH(z)$, where

   ```math
   H(z) = \tfrac{26}{75} - \tfrac{653}{300}z + \tfrac{23}{45}z^{2} + \tfrac{349}{720}z^{3} - \tfrac{47}{900}z^{4} - \tfrac{1069}{21600}z^{5} - \tfrac{13}{37800}z^{6} .
   ```

   Its Bernstein coefficients of degree 6 on $[0, \frac16]$ are

   ```math
   \tfrac{26}{75},\ \tfrac{3091}{10800},\ \tfrac{11017}{48600},\ \tfrac{523261}{3110400},\ \tfrac{3882011}{34992000},\ \tfrac{55351163}{1007769600},\ \tfrac{1001149}{3527193600} ,
   ```

   all positive, so $H > 0$ on $[0, \frac16]$ and
   $L_0(z)^2 - \frac{13}4(p^2 + q^2) \ge zH(z) > 0$. Cauchy–Schwarz on the disk
   gives $p(A + \frac12) + q(v + \frac12) > -L_0(z)$, that is $E(A, v) > 0$.
2. *The transition state.* We show $E(a_0, u_0) > 0$ for $0 \le z \le 1$.
   Expanding,

   ```math
   E(a_0, u_0) = \left(X_0 - \tfrac85\right)(1 - \cos z) + \left(Y_0 - \tfrac{79}{100}\right)\sin z + \tfrac25\left(\tfrac{13}8 - X_0\right) + \tfrac4{15}\left(\tfrac45 - Y_0\right) + \Bigl[-\tfrac35\cos z + \tfrac{79}{100}\sin z - \tfrac45z + \tfrac{181}{300}\Bigr] .
   ```

   Since $\frac85 < X_0 < \frac{13}8$ and $\frac{79}{100} < Y_0 < \frac45$, the
   first four terms are nonnegative and the third is positive. By (D.2) the
   bracket is at least

   ```math
   -\tfrac35C_4(z) + \tfrac{79}{100}S_3(z) - \tfrac45z + \tfrac{181}{300}
   = \tfrac1{300}\left(43z^2 - 3z + 1\right) + \tfrac{79}{600}\left(z^2 - z^3\right) + \tfrac1{40}\left(z^2 - z^4\right),
   ```

   which is nonnegative for $0 \le z \le 1$, as $43z^2 - 3z + 1$ has negative
   discriminant $9 - 172$.
3. *For $\frac16 < z < 1$ and $\cos z \ge \frac35$, comparison with the
   transition state.* By [Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label),
   $a_0 - A \ge 0$ and $v - u_0 \ge 0$, and

   ```math
   E(A, v) - E(a_0, u_0) = \left(\cos z - \tfrac35\right)(a_0 - A) + \left(\sin z - \tfrac4{15}\right)(v - u_0) .
   ```

   If $\sin z \ge \frac4{15}$, both terms are nonnegative, and
   $E(A, v) \ge E(a_0, u_0) > 0$. If $\sin z < \frac4{15}$, then
   $\cos^2 z > 1 - \frac{16}{225} = \frac{209}{225} > (\frac{24}{25})^2$, so
   $\cos z > \frac{24}{25}$; and $\sin z \ge \sin\frac16 \ge S_3(\frac16)$, as
   $\sin$ increases on $[0, \frac\pi2]$, with
   $S_3(\frac16) = \frac{215}{1296} > \frac{33}{200}$. Then

   ```math
   E(A, v) - E(a_0, u_0) = \left(\cos z - \tfrac35\right)\left[(a_0 - A) - \tfrac{12}{25}(v - u_0)\right] + (v - u_0)\left[\tfrac{12}{25}\left(\cos z - \tfrac35\right) + \sin z - \tfrac4{15}\right] .
   ```

   The first product is nonnegative by Lemma D.4, and the second bracket exceeds
   $\frac{12}{25}\cdot\frac9{25} + \frac{33}{200} - \frac4{15}$, which is
   $\frac{1067}{15000} > 0$. Again $E(A, v) \ge E(a_0, u_0) > 0$.
4. *For $\frac16 < z < 1$ and $\cos z < \frac35$.* Here
   $\cos z \ge C_2(z) > \frac12$, so $\cos^2 z < \frac9{25}$ and
   $\sin z > \frac45$. As $A \ge 0$ and $v \ge u_0 > \frac{29}{100}$,

   ```math
   \begin{aligned}
   E(A, v) &= L_0(z) + \left(\tfrac35 - \cos z\right)A + \tfrac12\left(\tfrac35 - \cos z\right) + \left(\sin z - \tfrac4{15}\right)\left(v - \tfrac{29}{100}\right) + \tfrac{79}{100}\left(\sin z - \tfrac4{15}\right) \\
   &\ge \tfrac12\cos z + \tfrac3{10} - \tfrac2{15} - \tfrac45z + \tfrac{79}{100}\left(\sin z - \tfrac4{15}\right)
   > \tfrac14 + \tfrac3{10} - \tfrac2{15} - \tfrac45 + \tfrac{79}{100}\left(\tfrac45 - \tfrac4{15}\right) = \tfrac{19}{500} . \qquad\square
   \end{aligned}
   ```

![Graph over z from 0 to 1 of the least value of the expression of Lemma D.6 over the admissible states with side label (blue), from 0 at z = 0 up to about 0.16 at z = 1; the dashed green value at the transition state, which is slightly above it near z = 0 and coincides with it further on; the orange Cauchy–Schwarz bound on [0, 1/6], a small positive arch; vertical lines at z = 1/6 and z = arccos 3/5 separate the steps of the proof.](figures/appd-side-profile.svg)

*Figure D.6.* Lemma D.6. The least value of $\beta_{\mathrm{side}}(A, v; -z)$
over the admissible states with side label (blue). It tends to 0 as $z \to 0$,
at the side state $(1, \frac12)$, where the contact of Proposition D.7 sits;
there step 1 uses Cauchy–Schwarz on the disk (orange), with the margin $zH(z)$.
For larger $z$ the value at the transition state (dashed), which steps 2 and 3
compare with, is the minimum.

*Lean:
[`Seven.sideTarget_negative_pos`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L175).*

### Proposition D.7 (target sign negative)

Let $(a, u)$ and $(A, v)$ be admissible states and $s \in \lbrace 1, -1\rbrace$.
Suppose that $s = 1$ or that the label of $(a, u)$ is axial, and that the label
of $(A, v)$ is axial or side. Then on the forward axis, for the signs $(s, -1)$,
$\sigma_1(\frac\pi3) \ge 0$. If $\sigma_1(\frac\pi3) = 0$, then $(a, u)$ is an
axial state and $(A, v) = (1, \frac12)$, so that the two states with these signs
form a contact.

*Proof.* Let $e = s\ell + \lambda - \frac\pi6$. By Lemma D.1,
$\sigma_1 \ge \beta(A, v; e, s\ell)$, and $-\frac{5\pi}{12} \le e \le \frac\pi3$
as $0 \le \ell, \lambda \le \frac\pi4$.

*Axial target.* Lemma D.3 with $\rho = s\ell$ gives $\sigma_1 \ge \beta > 0$.

*Side target.* By (D.3),
$\lambda = \mathrm{side}(A, v) = \frac\pi6 - \frac54(A - 1) - \frac16r(A, v)$,
so $s\ell = e - \lambda + \frac\pi6 = e + \frac54(A - 1) + \frac16r(A, v)$ and
$\frac45s\ell = \frac45e + A - 1 + \frac2{15}r(A, v)$. Substituting,
$\beta(A, v; e, s\ell) = \beta_{\mathrm{side}}(A, v; e)$.

If $e \ge 0$, Lemma D.5 gives
$\sigma_1 \ge \frac{21}{40}e + \frac2{15}r(A, v) \ge 0$. If moreover
$\sigma_1 = 0$, then $e = 0$ and $r(A, v) = 0$. So $(A, v) = (1, \frac12)$ and
$\lambda = \frac\pi6$, hence $s\ell = e - \lambda + \frac\pi6 = 0$, so
$\ell = 0$, $u = 0$, and $(a, u)$ is an axial state. With $t = -1$, the axial
state $(a, u)$ and the side state $(A, v)$ form a contact (the third case of
[Definition 9.15](seven.md#definition-915-contacts)).

If $e < 0$, let $z = -e > 0$. Since $\lambda > \frac9{25}$ and
$s\ell \ge -\frac\pi4$, we have $e > \frac9{25} - \frac{5\pi}{12}$, and
$\frac9{25} - \frac{5\pi}{12} > \frac9{25} - \frac{55}{42} = -\frac{997}{1050}$.
So $z < 1$, and Lemma D.6 gives
$\sigma_1 \ge \beta_{\mathrm{side}}(A, v; -z) > 0$. $\square$

*Lean:
[`Seven.fixed_gap_forward_negative_target`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L289).*

## D.3 Opposite signs

In this section $s = -1$ and $t = 1$, and the turn is
$w = \ell + \lambda - \frac\pi3$. The frame of $T$ is turned by
$d = \frac\pi3 - \ell - \lambda = -w$ against that of $S$, so $w = 0$ when the
sides of $T$ are parallel to those of $S$, as for the two squares of a side
column (Figure D.1, middle).

### Lemma D.8 (the support sum for opposite signs)

Let $(a, u)$ and $(A, v)$ be admissible, and $w = \ell + \lambda - \frac\pi3$.
Then $-\frac\pi3 \le w \le \frac\pi6$, and on the forward axis, for the signs
$(-1, 1)$,

```math
\sigma_1\left(\tfrac\pi3\right) = F(u, A, v; w), \qquad
F(u, A, v; w) = \tfrac12 - u + A\sin w - v\cos w + \tfrac12\left(\lvert\sin w\rvert + \cos w\right) .
```

*Proof.* The range of $w$ holds as $0 \le \ell, \lambda \le \frac\pi4$. By (D.1)
with $s = -1$ and $t = 1$ the direction is
$\frac{7\pi}6 + \ell + \lambda = \frac{3\pi}2 + w$, and

```math
h\left(A, v, \tfrac{3\pi}2 + w\right) = A\sin w - v\cos w + \tfrac12\left(\lvert\sin w\rvert + \lvert\cos w\rvert\right),
```

where $\cos w \ge 0$ as $\lvert w\rvert \le \frac\pi3$. $\square$

*Lean:
[`Seven.sideSideSupport`](../../SquaresInCircles/Seven/OppositeForward.lean#L17),
[`Seven.forward_turn_range`](../../SquaresInCircles/Seven/OppositeForward.lean#L21),
[`Seven.pairSupport_forward_opposite`](../../SquaresInCircles/Seven/OppositeForward.lean#L28).*

### Lemma D.9 (the side margin)

For $-\frac\pi3 \le w \le \frac\pi6$ let

```math
M(w) = \tfrac{19}{20} + \cos w - \min(\sin w, 0) - \tfrac65w .
```

Then $M(w) > 0$, and if $w \ne 0$,

```math
M(w)^2 > \tfrac{13}4\left(\left(\sin w - \tfrac9{10}\right)^2 + \left(\tfrac25 - \cos w\right)^2\right) .
\tag{D.7}
```

At $w = 0$ both sides of (D.7) equal $(\frac{39}{20})^2$.

*Proof.* At $w = 0$, $M(0) = \frac{39}{20}$ and
$\frac{13}4(\frac{81}{100} + \frac9{25}) = \frac{1521}{400}$, which is
$(\frac{39}{20})^2$.

*The case $0 \le w \le \frac\pi6$.* Here $w < \frac8{15}$ and $\sin w \ge 0$, so
by $\cos w \ge C_2(w)$,

```math
M(w) = \tfrac{19}{20} + \cos w - \tfrac65w \ge \tfrac{39}{20} - \tfrac{32}{225} - \tfrac{16}{25} = \tfrac{1051}{900} > 0 .
```

Let $w > 0$. Multiplying the difference of the two sides of (D.7) by 400 and
using $\sin^2 w + \cos^2 w = 1$,

```math
\begin{aligned}
400\left[M^2 - \tfrac{13}4\left(\left(\sin w - \tfrac9{10}\right)^2 + \left(\tfrac25 - \cos w\right)^2\right)\right]
&= (19 + 20\cos w - 24w)^2 - 13(197 - 180\sin w - 80\cos w) \\
&= 400\cos^2 w + (1800 - 960w)\cos w + 2340\sin w + 576w^2 - 912w - 2200 .
\end{aligned}
```

Since $0 \le \sin w \le w$, $\cos^2 w = 1 - \sin^2 w \ge 1 - w^2$. With
$\cos w \ge C_2(w)$, $w\cos w \le wC_4(w)$ and $\sin w \ge S_3(w)$ from (D.2),
the right side is at least

```math
400(1 - w^2) + 1800C_2(w) - 960wC_4(w) + 2340S_3(w) + 576w^2 - 912w - 2200
= w\left(468 - 724w + 90w^2 - 40w^4\right),
```

and for $0 < w < \frac8{15}$

```math
468 - 724w + 90w^2 - 40w^4 \ge 468 - 724\cdot\tfrac8{15} - 40\left(\tfrac8{15}\right)^4 = \tfrac{796132}{10125} > 0 .
```

*The case $-\frac\pi3 \le w < 0$.* Let $z = -w$, so $0 < z \le \frac\pi3$,
$\cos z \ge \frac12$, $\sin z \ge 0$ and $\min(\sin w, 0) = -\sin z$. Then
$M(w) = \frac{19}{20} + \cos z + \sin z + \frac65z \ge \frac{29}{20} > 0$, and
multiplying by 400 and using $\sin^2 z + \cos^2 z = 1$,

```math
400\left[M^2 - \tfrac{13}4\left(\left(\sin z + \tfrac9{10}\right)^2 + \left(\tfrac25 - \cos z\right)^2\right)\right]
= N(z) := 800\sin z\cos z + 960z\cos z + 1800(\cos z - 1) + 960z\sin z - 1580\sin z + 576z^2 + 912z .
```

Expanding shows

```math
N(z) - z\left(212 + 636z - 160z^3\right)
= 800\left(\cos z - \tfrac12\right)\sin z + 960z\left(\cos z - \tfrac12\right) + 1800\bigl(\cos z - C_2(z)\bigr) + 1180(z - \sin z) + 960z\bigl(\sin z - S_3(z)\bigr),
```

a sum of nonnegative terms by (D.2). Finally $z \le \frac\pi3 < \frac98$, so
$160z^2 < \frac{405}2 < 636$ and $212 + z(636 - 160z^2) > 0$; hence $N(z) > 0$.
$\square$

*Lean:
[`Seven.sideSideL`](../../SquaresInCircles/Seven/OppositeForward.lean#L46),
[`Seven.sideSideL_pos`](../../SquaresInCircles/Seven/OppositeForward.lean#L49),
[`Seven.sideSide_margin_pos`](../../SquaresInCircles/Seven/OppositeForward.lean#L68).*

### Proposition D.10 (two side labels)

Let $(a, u)$ and $(A, v)$ be admissible with side labels, and
$w = \ell + \lambda - \frac\pi3$. Then $F(u, A, v; w) \ge 0$, with equality only
if $(a, u) = (A, v) = (1, \frac12)$.

*Proof.* As both labels are side,

```math
w = \mathrm{side}(a, u) + \mathrm{side}(A, v) - \tfrac\pi3 = \tfrac13(u + v - 1) + \tfrac34(2 - a - A) .
```

Using this and $\lvert\sin w\rvert = \sin w - 2\min(\sin w, 0)$, expanding shows

```math
F(u, A, v; w) = \tfrac3{10}r(a, u) + B(w), \qquad
B(w) = M(w) + \left(\sin w - \tfrac9{10}\right)\left(A + \tfrac12\right) + \left(\tfrac25 - \cos w\right)\left(v + \tfrac12\right) .
\tag{D.8}
```

By Lemma D.9 and Cauchy–Schwarz on the disk with $p = \sin w - \frac9{10}$,
$q = \frac25 - \cos w$ and $c = M(w)$, $B(w) \ge 0$, and $B(w) > 0$ if
$w \ne 0$. As $r(a, u) \ge 0$, $F \ge 0$. If $F = 0$, then $w = 0$, and

```math
B(0) = \tfrac{39}{20} - \tfrac9{10}\left(A + \tfrac12\right) - \tfrac35\left(v + \tfrac12\right) = \tfrac3{10}r(A, v) ,
```

so $F = \frac3{10}(r(a, u) + r(A, v)) = 0$. Both remainders vanish, and both
states are $(1, \frac12)$ ([Lemma 9.16](seven.md#lemma-916-contacts)). $\square$

*Remark.* At $w = 0$ both terms of (D.8) are multiples of remainders, and
$r = 0$ is the tangent of the circle $\varphi = \frac{13}4$ at the side state.
For $w \ne 0$ the line $B(w) = 0$ in the $(A, v)$-plane misses the disk, by a
margin that vanishes only at $w = 0$ (Figure D.7).

![Left: graph over w from −pi/3 to pi/6 of 400 times the margin of Lemma D.9 (blue), zero only at w = 0, where it has a corner, above its polynomial lower bounds (dashed orange). Right: part of the (A, v)-plane with the admissible region (green) and the dashed circle phi = 13/4, and short pieces of the lines B(w) = 0 for w = −0.8, −0.4, 0 and 0.4 near their points closest to the disk; only the line for w = 0 touches the circle, at the side state (1, 1/2).](figures/appd-side-side.svg)

*Figure D.7.* Lemma D.9 and Proposition D.10. Left: 400 times
$M(w)^2 - \frac{13}4((\sin w - \frac9{10})^2 + (\frac25 - \cos w)^2)$ (blue) and
its lower bounds $w(468 - 724w + 90w^2 - 40w^4)$ for $w > 0$ and
$z(212 + 636z - 160z^3)$ for $w = -z < 0$ (dashed). Right: the lines $B(w) = 0$;
each misses the disk, so $B(w) > 0$ on it, except the line for $w = 0$, the
tangent $r(A, v) = 0$ at the side state.

*Lean:
[`Seven.side_side_property`](../../SquaresInCircles/Seven/OppositeForward.lean#L131),
[`Seven.side_side_zero`](../../SquaresInCircles/Seven/OppositeForward.lean#L177).*

### Lemma D.11 (bounds in the turn)

1. For $0 \le w \le \frac\pi6$, $\sin w - \frac45w - \frac12(1 - \cos w) \ge 0$.
2. If $A \ge \frac12$, $v \ge 0$ and $0 \le w \le \frac\pi6$, then
   $F(u, A, v; w) \ge 1 - u - v + \sin w - \frac12(1 - \cos w)$.
3. If $(A, v)$ is admissible and $0 \le z \le \frac\pi3$, then
   $F(u, A, v; -z) \ge 1 - u - v - (A - \frac12)\sin z - \frac12(1 - \cos z)$.

*Proof.* (1) By (D.2) the left side is at least
$S_3(w) - \frac45w - \frac14w^2$, which is
$w(\frac15 - \frac w4 - \frac{w^2}6)$, and for
$0 \le w \le \frac\pi6 < \frac8{15}$ the bracket is at least
$\frac15 - \frac2{15} - \frac{32}{675} = \frac{13}{675} > 0$.

(2) Here $\sin w \ge 0$, and the difference of the two sides is
$(A - \frac12)\sin w + v(1 - \cos w) \ge 0$.

(3) Here $\lvert\sin(-z)\rvert = \sin z$, and the difference of the two sides is
$v(1 - \cos z) \ge 0$. $\square$

*Lean:
[`Seven.forward_turn_nonneg`](../../SquaresInCircles/Seven/OppositeForward.lean#L186),
[`Seven.opposite_support_positive_turn`](../../SquaresInCircles/Seven/OppositeForward.lean#L196),
[`Seven.opposite_support_negative_turn`](../../SquaresInCircles/Seven/OppositeForward.lean#L208).*

### Lemma D.12 (two axial labels)

1. For $0 \le z \le \frac\pi3$,

   ```math
   1 - \tfrac{4\pi}{15} + \tfrac45z - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) > 0 .
   ```

2. If $(a, u)$ and $(A, v)$ are admissible with axial labels, then
   $F(u, A, v; w) > 0$ for $w = \ell + \lambda - \frac\pi3$.

*Proof.* (1) Let $\kappa = \sqrt3 - 1$, so $\frac7{10} < \kappa < \frac34$. By
(D.2), $\sin z \le S_5(z)$, and

```math
\tfrac34z - \tfrac7{60}z^3 + \tfrac1{160}z^5 - \kappa S_5(z)
= \left(\tfrac34 - \kappa\right)z + \tfrac16\left(\kappa - \tfrac7{10}\right)z^3 + \tfrac1{120}\left(\tfrac34 - \kappa\right)z^5 \ge 0 .
```

With $1 - \cos z \le \frac{z^2}2$ and
$1 - \frac{4\pi}{15} > 1 - \frac{88}{105} = \frac{17}{105}$, the left side of
(1) is greater than

```math
p_5(z) = \tfrac{17}{105} + \tfrac{1}{20}z - \tfrac{1}{4}z^{2} + \tfrac{7}{60}z^{3} - \tfrac{1}{160}z^{5} .
```

Its Bernstein coefficients of degree 5 on $[0, \frac{11}{10}]$ are

```math
\tfrac{17}{105},\ \tfrac{3631}{21000},\ \tfrac{12907}{84000},\ \tfrac{502669}{4200000},\ \tfrac{22711}{262500},\ \tfrac{20033129}{336000000} ,
```

all positive, and $\frac\pi3 < \frac{11}{10}$; so $p_5 > 0$ on $[0, \frac\pi3]$.

(2) Both labels are axial, so
$u + v = \frac45(\ell + \lambda) = \frac45(\frac\pi3 + w)$. If $w \ge 0$, Lemma
D.11 (2) and (1) give

```math
F \ge 1 - \tfrac45\left(\tfrac\pi3 + w\right) + \sin w - \tfrac12(1 - \cos w) \ge 1 - \tfrac{4\pi}{15} > 0 .
```

If $w < 0$, let $z = -w$; then $0 < z \le \frac\pi3$, and Lemma D.11 (3),
$A - \frac12 \le \sqrt3 - 1$ and $\sin z \ge 0$ give

```math
F \ge 1 - \tfrac45\left(\tfrac\pi3 - z\right) - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) ,
```

which is positive by (1). $\square$

*Lean:
[`Seven.opposite_axial_scalar`](../../SquaresInCircles/Seven/OppositeForward.lean#L220),
[`Seven.opposite_axial_axial_pos`](../../SquaresInCircles/Seven/OppositeForward.lean#L242).*

### Lemma D.13 (the mixed clearance)

1. Let $(A, v)$ be admissible with side label, and let $(a, u)$ be a state with
   $\ell(a, u) = \mathrm{axial}(u)$. Then, with
   $w = \ell + \lambda - \frac\pi3$, $1 - u - v \ge \frac1{170} - \frac45w$.
2. Let $(A, v)$ be admissible, $0 \le w \le \frac\pi6$ and
   $1 - u - v \ge \frac1{170} - \frac45w$. Then $F(u, A, v; w) > 0$.

*Proof.* (1) We have $\ell = \frac54u$ and $\lambda = \mathrm{side}(A, v)$, that
is, $\lambda = \frac\pi6 + \frac13(v - \frac12) + \frac34(1 - A)$. Expanding
gives

```math
1 - u - v - \tfrac1{170} + \tfrac45w = \tfrac{217}{102} - \tfrac{2\pi}{15} - \tfrac35\left(A + \tfrac12\right) - \tfrac{11}{15}\left(v + \tfrac12\right) .
```

Cauchy–Schwarz on the disk with $p = -\frac35$, $q = -\frac{11}{15}$ and
$c = \frac{41}{24}$ applies, since

```math
\tfrac{13}4\left(\tfrac9{25} + \tfrac{121}{225}\right) = \tfrac{1313}{450} < \tfrac{1681}{576} = \left(\tfrac{41}{24}\right)^2 .
```

So the right side is at least

```math
\tfrac{217}{102} - \tfrac{41}{24} - \tfrac{2\pi}{15} > \tfrac{217}{102} - \tfrac{41}{24} - \tfrac{44}{105} = \tfrac1{14280} > 0 .
```

(2) As $A \ge \frac12$ and $v \ge 0$, Lemma D.11 (2) and (1) give

```math
F \ge 1 - u - v + \sin w - \tfrac12(1 - \cos w) \ge \tfrac1{170} + \Bigl[\sin w - \tfrac45w - \tfrac12(1 - \cos w)\Bigr] \ge \tfrac1{170} . \qquad\square
```

*Lean:
[`Seven.mixed_clearance_bound`](../../SquaresInCircles/Seven/OppositeForward.lean#L277),
[`Seven.mixed_positive_turn`](../../SquaresInCircles/Seven/OppositeForward.lean#L287).*

### Lemma D.14 (an axial source and a side target)

Let $(a, u)$ and $(A, v)$ be admissible, the label of $(a, u)$ axial and that of
$(A, v)$ side. Then $F(u, A, v; w) > 0$ for $w = \ell + \lambda - \frac\pi3$.

*Proof.* By Lemma D.13 (1), $1 - u - v \ge \frac1{170} - \frac45w$. If
$w \ge 0$, Lemma D.13 (2) concludes. Let $w < 0$ and $z = -w$. As
$\lambda > \frac9{25}$ and $\ell \ge 0$,
$z = \frac\pi3 - \ell - \lambda < \frac{22}{21} - \frac9{25}$, and
$\frac{22}{21} - \frac9{25} = \frac{361}{525} < \frac7{10}$. As the label of
$(A, v)$ is side, $A < \frac98$, so $0 \le A - \frac12 < \frac58$. By Lemma D.11
(3), $0 \le \sin z \le z$ and $1 - \cos z \le \frac{z^2}2$,

```math
F \ge \tfrac1{170} + \tfrac45z - \tfrac58\sin z - \tfrac14z^2 \ge \tfrac1{170} + \tfrac7{40}z - \tfrac14z^2
= \tfrac1{170} + z\left(\tfrac7{40} - \tfrac z4\right) > 0 . \qquad\square
```

*Lean:
[`Seven.opposite_axial_side_pos`](../../SquaresInCircles/Seven/OppositeForward.lean#L323).*

### Lemma D.15 (a side source and an axial target)

1. For $\frac13 \le z \le \frac7{10}$,

   ```math
   \Psi(z) = \tfrac12 - \tfrac\pi5 + \tfrac65z - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) > 0 .
   ```

2. If $(a, u)$ and $(A, v)$ are admissible, the label of $(a, u)$ side and that
   of $(A, v)$ axial, then $F(u, A, v; w) > 0$ for
   $w = \ell + \lambda - \frac\pi3$.

*Proof.* (1) On $[\frac13, \frac7{10}]$,

```math
\Psi'(x) = \tfrac65 - (\sqrt3 - 1)\cos x - \tfrac12\sin x \ge \tfrac65 - \tfrac{11}{15} - \tfrac12\cdot\tfrac7{10} = \tfrac7{60} > 0 ,
```

as $\cos x \le 1$, $\sin x \le x$ and $\sqrt3 - 1 < \frac{11}{15}$. So $\Psi$
increases there, and it suffices that $\Psi(\frac13) > 0$. With
$\pi < \frac{22}7$, $(\sqrt3 - 1)\sin\frac13 \le \frac{11}{15}S_5(\frac13)$ and
$1 - \cos\frac13 \le \frac1{18}$,

```math
\Psi\left(\tfrac13\right) > \tfrac12 - \tfrac{22}{35} + \tfrac25 - \tfrac{11}{15}S_5\left(\tfrac13\right) - \tfrac1{36} = \tfrac{11353}{3061800} > 0 .
```

(2) Lemma D.13 (1), applied with the two states exchanged, gives
$1 - u - v \ge \frac1{170} - \frac45w$, since $w$ is symmetric in the two
labels. If $w \ge 0$, Lemma D.13 (2) concludes. Let $w < 0$ and $z = -w$; as
$\ell > \frac9{25}$ and $\lambda \ge 0$, $z < \frac7{10}$ as in Lemma D.14. By
Lemma D.11 (3), $A - \frac12 \le \sqrt3 - 1$ and $\sin z \ge 0$,

```math
F \ge 1 - u - v - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) .
\tag{D.9}
```

If $z \le \frac13$, then with $1 - u - v \ge \frac1{170} + \frac45z$,
$\sqrt3 - 1 < \frac{11}{15}$, $\sin z \le z$ and $1 - \cos z \le \frac{z^2}2$,

```math
F \ge \tfrac1{170} + \tfrac45z - \tfrac{11}{15}z - \tfrac14z^2 = \tfrac1{170} - \tfrac z{60} + \tfrac14z\left(\tfrac13 - z\right) \ge \tfrac1{170} - \tfrac1{180} > 0 .
```

If $z > \frac13$, we use the labels themselves. The side label of $(a, u)$ gives
$u \le \frac12 + \frac65(\ell - \frac\pi6)$, the axial label of $(A, v)$ gives
$v = \frac45\lambda$, and $\ell = \frac\pi3 - z - \lambda$. So

```math
1 - u - v \ge \tfrac12 - \tfrac65\left(\tfrac\pi6 - z - \lambda\right) - \tfrac45\lambda = \tfrac12 - \tfrac\pi5 + \tfrac65z + \tfrac25\lambda \ge \tfrac12 - \tfrac\pi5 + \tfrac65z ,
```

and (D.9) gives $F \ge \Psi(z) > 0$ by (1). $\square$

*Lean:
[`Seven.side_axial_far_profile`](../../SquaresInCircles/Seven/OppositeForward.lean#L295),
[`Seven.opposite_side_axial_pos`](../../SquaresInCircles/Seven/OppositeForward.lean#L354).*

### Proposition D.16 (opposite signs)

Let $(a, u)$ and $(A, v)$ be admissible states whose labels are axial or side.
Then on the forward axis, for the signs $(-1, 1)$, $\sigma_1(\frac\pi3) \ge 0$.
If $\sigma_1(\frac\pi3) = 0$, then $(a, u) = (A, v) = (1, \frac12)$, and the two
states with these signs form a contact.

*Proof.* By Lemma D.8, $\sigma_1 = F(u, A, v; w)$ with
$w = \ell + \lambda - \frac\pi3$. If both labels are side, Proposition D.10
gives $F \ge 0$, with equality only at two side states, which with the signs
$(-1, 1)$ form a contact (the first case of [Definition 9.15](seven.md#definition-915-contacts)). Otherwise
$F > 0$: by Lemma D.12 if both labels are axial, by Lemma D.14 if the label of
$(a, u)$ is axial and that of $(A, v)$ side, and by Lemma D.15 if the label of
$(a, u)$ is side and that of $(A, v)$ axial. $\square$

![Graph over the turn w from −pi/3 to pi/6 of three lower bounds: for two axial labels (blue), between about 0.12 and 0.2; for an axial source and a side target (green), two low arches from 1/170 at w = −7/10 to 1/170 at w = 0 and beyond; for a side source and an axial target (dashed pink), falling from about 0.12 at w = −7/10 to nearly 0 at w = −1/3, then a low arch that joins the green curve at w = 0. Vertical lines at w = −7/10 and w = −1/3.](figures/appd-opposite-profiles.svg)

*Figure D.8.* The lower bounds of Lemmas D.12, D.14 and D.15 for
$F(u, A, v; w)$, as functions of the turn $w$. For mixed labels the turn exceeds
$-\frac7{10}$. The bound for a side source and an axial target is weakest at
$w = -\frac13$, where Lemma D.15 changes its method.

*Lean:
[`Seven.fixed_gap_forward_opposite_active`](../../SquaresInCircles/Seven/OppositeForward.lean#L405).*

## D.4 Both signs negative

In this section $s = t = -1$ and the label of $(a, u)$ is side. The frame of $T$
is turned by $d = \frac\pi3 - \ell + \lambda$ against that of $S$, and no
contact occurs: $\sigma_1(\frac\pi3) > 0$ throughout (Figure D.1, right). If
$\ell \le \frac25$, a single point of the marker arc of $T$ suffices (Lemma
D.17). For larger $\ell$ the support of $T$ is bounded below exactly over the
label region of $(A, v)$. With $\delta = d$ it is, up to a constant, the
function $G_\delta(A, v)$ of §D.1, which is affine along each segment of
constant label. So it is smallest at an end of the segment, and the ends make up
the boundary curves of Appendix B (Figure D.10): the circle, the tie line and
the diagonal for side labels, and the circle and the tie line for axial labels.
Along the circle the support is concave in the label (Lemma D.20), so it
suffices to check the ends of that piece.

### Lemma D.17 (a small source label)

Let $(a, u)$ and $(A, v)$ be admissible, and suppose that the label of $(a, u)$
is side with $\ell \le \frac25$. Then on the forward axis, for the signs
$(-1, -1)$, $\sigma_1(\frac\pi3) > 0$.

*Proof.* By (D.1), $\sigma_1 = \frac12 - u + h(A, -v, z)$ with
$z = \frac{7\pi}6 + \ell - \lambda$. Let $x = -\lambda - \frac12$. Then
$\lvert x - (-1)\lambda\rvert = \frac12 \le \frac{801}{1600}$, so by the marker
arc ([Lemma 9.11](seven.md#lemma-911-the-support-function)), applied to $(A, v)$ with the sign $-1$,
$h(A, -v, z) \ge \cos(z - x)$. Let $\theta = \frac\pi3 - \ell - \frac12$. Then
$z - x = \frac{7\pi}6 + \ell + \frac12 = 2\pi - (\frac\pi2 + \theta)$, so

```math
\cos(z - x) = \cos\left(\tfrac\pi2 + \theta\right) = -\sin\theta .
```

As $\ell \le \frac25$, $\theta \ge \frac\pi3 - \frac9{10} > 0$, so
$\sin\theta \le \theta$, and
$\sigma_1 \ge \frac12 - u - \theta = 1 - u + \ell - \frac\pi3$. The label of
$(a, u)$ is side, so $u \le \frac12 + \frac65(\ell - \frac\pi6)$, and

```math
\sigma_1 \ge \tfrac12 - \tfrac15\ell - \tfrac{2\pi}{15} \ge \tfrac12 - \tfrac2{25} - \tfrac{2\pi}{15}
> \tfrac{21}{50} - \tfrac{44}{105} = \tfrac1{1050} > 0 . \qquad\square
```

*Remark.* In the chart of $S$ the argument reads as follows. The marker of $T$
is the direction $d - \lambda = \frac\pi3 - \ell$, and the point $u(\theta)$ of
the unit circle is $\frac12$ behind it, inside the marker arc of $T$, so it lies
in $\overline T$. Its height $\sin\theta$ is below the top $\frac12 - u$ of $S$
(Figure D.9).

![A canonical pair for the signs (−1, −1) in the chart of S: S = Q(a0, −u0) mostly below the horizontal axis and T above it, turned by about 69 degrees; the unit circle about o with the marker arc of T drawn thick inside T, and the point u(theta) at the lower end of the arc, at angle theta above the horizontal axis. A magnified inset shows that the height sin theta of u(theta) is a little below the top edge of S at height 1/2 − u.](figures/appd-marker-point.svg)

*Figure D.9.* Lemma D.17, for the source $(a_0, u_0)$, whose label $s_0$ is
below $\frac25$, and the target $(1, \frac12)$. The marker arc of $T$ (thick)
lies in $\overline T$, so its point $u(\theta)$, $\frac12$ behind the marker of
$T$, bounds how far $T$ reaches back along $n_1$. Its height $\sin\theta$ is
below the top $\frac12 - u$ of $S$ (inset), so the shadows of $S$ and $T$ on
$n_1$ overlap.

*Lean:
[`Seven.forward_negative_negative_small`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L344).*

For $\ell \ge \frac25$ we follow the segments of constant label (Figure D.10),
and first the circular piece of the upper ends of the side segments.

![The admissible region in the (A, v)-plane divided into segments of constant label: horizontal blue segments where the label is axial, green segments of slope 9/4 where it is side, from the tie line to the circle or the diagonal; the capped part is grey. Orange dots mark one end of each segment: the right end of every axial segment, the end on the tie line for the side segments below a dashed orange segment, and the upper end for those above it. The transition state and the diagonal corner are marked.](figures/appd-segments.svg)

*Figure D.10.* The segments of constant label, along which the target support
$G_\delta(A, v)$ is affine, for the source label $\ell = 0.55$, so that
$\mathrm{sw}(\ell) \approx 0.655$. The orange dots mark the end where it is
least: the right end of an axial segment, on the circle below $u_0$ and on the
tie line above; the tie state of a side segment with
$\tau \le \mathrm{sw}(\ell)$; and the top of a side segment with
$\tau > \mathrm{sw}(\ell)$, on the circle or, beyond the corner $(r_d, r_d)$, on
the diagonal. The dashed segment has $\tau = \mathrm{sw}(\ell)$.

### Definition D.18 (the target support along the circle)

For real $\ell$ and $s_0 \le \tau \le \tau_d$, with
$\delta = \frac\pi3 - \ell + \tau$ and $X$, $Y$, $Z$, $D$ taken at $\tau$, let

```math
\begin{aligned}
G^{\mathrm{circ}}(\ell, \tau) &= -(X - 1)\sin\delta + Y\cos\delta, \\
G^{\mathrm{circ}}_1(\ell, \tau) &= \cos\delta + \left(\tfrac1Z - 1\right)\left(X\cos\delta + Y\sin\delta\right), \\
G^{\mathrm{circ}}_2(\ell, \tau) &= -\sin\delta - \frac{D}{Z^3}\left(X\cos\delta + Y\sin\delta\right) - \left(\tfrac1Z - 1\right)^2\left(Y\cos\delta - X\sin\delta\right) .
\end{aligned}
```

So
$G^{\mathrm{circ}}(\ell, \tau) = G_\delta(X(\tau) - \frac12, Y(\tau) - \frac12)$
is the value of $G_\delta$ at the state of the circle with side label $\tau$,
which is $\mathrm{top}(\tau)$; hence
$G^{\mathrm{circ}}(\ell, \tau) = G^{\mathrm{top}}(\ell, \tau)$ for
$s_0 \le \tau \le \tau_d$.

*Lean:
[`Seven.Boundary.sideCircleTarget`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L17),
[`Seven.Boundary.sideCircleTargetD`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L19),
[`Seven.Boundary.sideCircleTargetDD`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L21).*

### Lemma D.19 (derivatives along the circle)

Let $\ell$ be real and $s_0 \le \tau \le \tau_d$. Then
$G^{\mathrm{circ}}(\ell, \cdot)$ is differentiable at $\tau$ with derivative
$G^{\mathrm{circ}}_1(\ell, \tau)$, and $G^{\mathrm{circ}}_1(\ell, \cdot)$ is
differentiable at $\tau$ with derivative $G^{\mathrm{circ}}_2(\ell, \tau)$.

*Proof.* On $[s_0, \tau_d]$ we have $Z > 1$, $X' = -Y/Z$, $Y' = X/Z$ and
$Z' = D/Z$, and $\delta' = 1$. So

```math
\frac{d}{d\tau}G^{\mathrm{circ}} = \frac YZ\sin\delta - (X - 1)\cos\delta + \frac XZ\cos\delta - Y\sin\delta
= \cos\delta + \left(\tfrac1Z - 1\right)\left(X\cos\delta + Y\sin\delta\right) .
```

Next, $(\frac1Z)' = -\frac{Z'}{Z^2} = -\frac D{Z^3}$, and

```math
\left(X\cos\delta + Y\sin\delta\right)' = -\frac YZ\cos\delta - X\sin\delta + \frac XZ\sin\delta + Y\cos\delta
= \left(1 - \tfrac1Z\right)\left(Y\cos\delta - X\sin\delta\right) .
```

Hence the derivative of $G^{\mathrm{circ}}_1$ is

```math
-\sin\delta - \frac D{Z^3}\left(X\cos\delta + Y\sin\delta\right) + \left(\tfrac1Z - 1\right)\left(1 - \tfrac1Z\right)\left(Y\cos\delta - X\sin\delta\right) = G^{\mathrm{circ}}_2(\ell, \tau) . \qquad\square
```

*Lean:
[`Seven.Boundary.sideTarget_derivatives`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L25).*

### Lemma D.20 (concavity along the circle)

Let $\frac25 \le \ell \le \frac\pi4$, $s_0 \le \tau \le \tau_d$ and
$\tau \ge \mathrm{sw}(\ell)$. Then $G^{\mathrm{circ}}_2(\ell, \tau) \le 0$.

*Proof.* Let $\delta = \frac\pi3 - \ell + \tau$. Then $0 < \delta < \frac\pi2$,
since $\delta \ge \frac\pi3 - \frac\pi4 + s_0 > 0$ and
$\delta \le \frac\pi3 - \frac25 + \frac\pi4 < \frac\pi2$; so $\sin\delta \ge 0$
and $\cos\delta \ge 0$. As $\tau \ge \mathrm{sw}(\ell)$, $\delta \ge \psi$ and
$\cos\delta \le \frac49\sin\delta$. Squaring,
$1 - \sin^2\delta \le \frac{16}{81}\sin^2\delta$, so
$\sin^2\delta \ge \frac{81}{97} > \frac{16}{25}$ and $\sin\delta > \frac45$.

Since $1 < Z < \frac75$, $-\frac27 < \frac1Z - 1 \le 0$ and
$(\frac1Z - 1)^2 < \frac4{49}$. Since $X^2 + Y^2 = \frac{13}4$, Cauchy–Schwarz
gives $\lvert Y\cos\delta - X\sin\delta\rvert \le \frac{\sqrt{13}}2$, and
$\frac{\sqrt{13}}2 < \frac{181}{100}$ as
$(\frac{181}{100})^2 = 3.2761 > \frac{13}4$. Finally $X, Y > 0$, $D > 0$ and
$Z > 0$, so the middle term of $G^{\mathrm{circ}}_2$ is at most 0. Therefore

```math
G^{\mathrm{circ}}_2(\ell, \tau) \le -\sin\delta + \tfrac{181}{100}\left(\tfrac1Z - 1\right)^2
< -\tfrac45 + \tfrac{181}{100}\cdot\tfrac4{49} = -\tfrac{799}{1225} < 0 . \qquad\square
```

*Lean:
[`Seven.Boundary.sideTarget_concave_second`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L47).*

### Lemma D.21 (the ends of the circular piece)

1. For every real $\ell$,
   $G^{\mathrm{circ}}(\ell, s_0) = G^{\mathrm{ax}}(\ell, s_0)$.
2. If $s_0 \le \tau \le \tau_d$ and $\tau = \mathrm{sw}(\ell)$, then
   $G^{\mathrm{circ}}(\ell, \tau) = G^{\mathrm{tie}}(\ell, \tau)$.

*Proof.* (1) $X(s_0) = a_0 + \frac12$ and $Y(s_0) = Y_0$
([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)), so
$G^{\mathrm{circ}}(\ell, s_0) = -(a_0 - \frac12)\sin\delta + Y_0\cos\delta$ with
$\delta = \frac\pi3 - \ell + s_0$, which is $G^{\mathrm{ax}}(\ell, s_0)$
([Proposition B.23](appendix-b.md#proposition-b23-the-circular-piece)).

(2) Here $\delta = \psi$. The state $(X(\tau) - \frac12, Y(\tau) - \frac12)$ has
side label $\tau$, so ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label))

```math
X(\tau) - \tfrac12 = \mathrm{tie}(\tau) + \tfrac49\left(Y(\tau) - \tfrac12 - \tfrac45\tau\right) .
```

Substituting,

```math
G^{\mathrm{circ}}(\ell, \tau) - G^{\mathrm{tie}}(\ell, \tau) = \left(Y(\tau) - \tfrac12 - \tfrac45\tau\right)\left(\cos\psi - \tfrac49\sin\psi\right) = 0 . \qquad\square
```

*Lean:
[`Seven.Boundary.sideTarget_at_transition`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L95),
[`Seven.Boundary.sideTarget_at_switch`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L109).*

### Lemma D.22 (the diagonal piece)

Let $(a, u)$ be admissible with side label $\ell \ge \frac25$, let
$\tau_d \le \tau \le \frac\pi4$ and $\delta = \frac\pi3 - \ell + \tau$. Then

```math
\tfrac12 - u - \left(\mathrm{diag}(\tau) - \tfrac12\right)\sin\delta + \left(\mathrm{diag}(\tau) + \tfrac12\right)\cos\delta > 0 .
```

*Proof.* Let $\eta = \frac{7\pi}{12} - \ell$. Then
$\frac\pi4 \le \delta \le \eta < \frac\pi2$: first,
$\delta - \frac\pi4 = \tau - (\ell - \frac\pi{12})$ and
$\ell - \frac\pi{12} \le \frac\pi6 < \frac{18}{25} < \tau_d \le \tau$; next,
$\delta \le \eta$ as $\tau \le \frac\pi4$; and $\eta < \frac\pi2$ as
$\ell \ge \frac25 > \frac\pi{12}$. So $\sin\delta \ge \cos\delta \ge 0$. As
$\mathrm{diag}$ decreases,
$\mathrm{diag}(\tau) \le \mathrm{diag}(\tau_d) = r_d < \frac{31}{40}$. Hence

```math
\begin{aligned}
-\left(\mathrm{diag}(\tau) - \tfrac12\right)\sin\delta + \left(\mathrm{diag}(\tau) + \tfrac12\right)\cos\delta
&= \tfrac12(\sin\delta + \cos\delta) - \mathrm{diag}(\tau)(\sin\delta - \cos\delta) \\
&\ge \tfrac12(\sin\delta + \cos\delta) - \tfrac{31}{40}(\sin\delta - \cos\delta)
= \tfrac{51}{40}\cos\delta - \tfrac{11}{40}\sin\delta
\ge \tfrac{51}{40}\cos\eta - \tfrac{11}{40}\sin\eta ,
\end{aligned}
```

as $\cos$ decreases and $\sin$ increases on $[0, \frac\pi2]$. With
$u \le \frac12 + \frac65(\ell - \frac\pi6)$, the left side of the claim is at
least $K(\ell)$, which is positive by (D.5). $\square$

*Lean:
[`Seven.Boundary.diagonal_target_pos`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L127).*

### Lemma D.23 (the top of a side segment)

Let $(a, u)$ be admissible with side label $\ell \ge \frac25$, and let
$s_0 \le \tau \le \frac\pi4$ with $\tau \ge \mathrm{sw}(\ell)$. Then
$\frac12 - u + G^{\mathrm{top}}(\ell, \tau) > 0$.

*Proof.* *The case $\tau \ge \tau_d$.* Then
$\mathrm{top}(\tau) = (\mathrm{diag}(\tau), \mathrm{diag}(\tau))$; at
$\tau = \tau_d$ this holds as
$(X(\tau_d) - \frac12, Y(\tau_d) - \frac12) = (r_d, r_d)$
([Lemma B.14](appendix-b.md#lemma-b14-the-parametrisation)) and $\mathrm{diag}(\tau_d) = r_d$. So the
claim is Lemma D.22.

*The case $\tau < \tau_d$.* Then
$G^{\mathrm{top}}(\ell, \tau) = G^{\mathrm{circ}}(\ell, \tau)$. Let
$l = \max(s_0, \mathrm{sw}(\ell))$, so that $l \le \tau < \tau_d$, and let
$f(x) = \frac12 - u + G^{\mathrm{circ}}(\ell, x)$ for $l \le x \le \tau_d$.
Every such $x$ has $x \ge \mathrm{sw}(\ell)$, so by Lemmas D.19 and D.20 the
second derivative of $f$ is at most 0 on $[l, \tau_d]$. So $f$ is concave, and
$f(\tau) \ge \min(f(l), f(\tau_d))$ ([Lemma A.4](appendix-a.md#lemma-a4-positivity-from-concavity)). Both
ends are positive.

- *The left end.* If $\mathrm{sw}(\ell) \le s_0$, then $l = s_0$ and
  $f(s_0) = \frac12 - u + G^{\mathrm{ax}}(\ell, s_0) > 0$ by Lemma D.21 (1) and
  (D.4). Otherwise $l = \mathrm{sw}(\ell)$, with $s_0 < l < \tau_d$, and by
  Lemma D.21 (2), the switch bound ([Proposition B.25](appendix-b.md#proposition-b25-the-straight-piece)) with
  $\tau = l$, and (D.4),

  ```math
  f(l) = \tfrac12 - u + G^{\mathrm{tie}}(\ell, l) \ge \tfrac12 - u + G^{\mathrm{ax}}(\ell, s_0) > 0 .
  ```

- *The right end.* $X(\tau_d) = Y(\tau_d) = r_d + \frac12$ and
  $r_d = \mathrm{diag}(\tau_d)$, so $f(\tau_d)$ is the left side of Lemma D.22
  at $\tau = \tau_d$, which is positive.

Hence $f(\tau) > 0$, which is the claim. $\square$

![Graph over the side label tau from s0 to pi/4, for the source label 0.5: the purple curve is one half minus u plus the target support at the tie state of the side segment of label tau, the green curve the same at its top; they meet at tau = sw(l). The lower of the two is drawn solid: the purple one before the meeting point and the green one after it. A horizontal orange line at the value of (D.4) lies below the solid purple part.](figures/appd-circle-profile.svg)

*Figure D.11.* Lemmas D.21 to D.24 for the source label $\ell = 0.5$, with $u$
the largest transverse coordinate of a state with side label $0.5$:
$\frac12 - u$ plus the target support at the tie state (purple) and at the top
(green) of the side segment of label $\tau$. On each segment the smaller of the
two is the minimum (solid). They agree at $\tau = \mathrm{sw}(\ell)$ (Lemma D.21
(2)). Below it the tie values stay above the value (D.4) at the transition
state; above it the top values form a concave curve, positive at both ends
(Lemma D.23).

*Lean:
[`Seven.Boundary.upper_target_pos`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L166).*

### Lemma D.24 (the side segment of the target)

Let $(a, u)$ and $(A, v)$ be admissible, the label of $(a, u)$ side with
$\ell \ge \frac25$ and the label of $(A, v)$ side, and let
$\delta = \frac\pi3 - \ell + \lambda$. Then $\frac12 - u + G_\delta(A, v) > 0$.

*Proof.* Let $\tau = \lambda$. Then $s_0 \le \tau \le \frac\pi4$
([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)), so $0 < \delta < \frac\pi2$ as
in Lemma D.20. By the side segment lemma ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)),
$A = \mathrm{tie}(\tau) + \frac49(v - \frac45\tau)$ with
$\frac45\tau \le v \le \mathrm{top}_u(\tau)$, and substituting,

```math
G_\delta(A, v) = G^{\mathrm{tie}}(\ell, \tau) + \left(v - \tfrac45\tau\right)\left(\cos\delta - \tfrac49\sin\delta\right) .
\tag{D.10}
```

So along the segment $G_\delta$ is affine in $v$, smallest at the tie state if
$\cos\delta - \frac49\sin\delta \ge 0$ and at the top otherwise.

If $\tau \le \mathrm{sw}(\ell)$, then $\delta \le \psi$ and
$\cos\delta - \frac49\sin\delta \ge 0$. So
$G_\delta(A, v) \ge G^{\mathrm{tie}}(\ell, \tau) \ge G^{\mathrm{ax}}(\ell, s_0)$
([Proposition B.25](appendix-b.md#proposition-b25-the-straight-piece)), and (D.4) concludes.

If $\tau > \mathrm{sw}(\ell)$, then $\delta > \psi$ and
$\cos\delta - \frac49\sin\delta \le 0$. The state $\mathrm{top}(\tau)$ also has
side label $\tau$ ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)), so (D.10) holds for it too,
with $v = \mathrm{top}_u(\tau)$ and value $G^{\mathrm{top}}(\ell, \tau)$.
Subtracting,

```math
G_\delta(A, v) - G^{\mathrm{top}}(\ell, \tau) = \bigl(\mathrm{top}_u(\tau) - v\bigr)\left(\tfrac49\sin\delta - \cos\delta\right) \ge 0 ,
```

and Lemma D.23 concludes. $\square$

*Lean:
[`Seven.Boundary.target_side_pos`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L240).*

### Lemma D.25 (the axial segment of the target)

Let $(a, u)$ and $(A, v)$ be admissible, the label of $(a, u)$ side with
$\ell \ge \frac25$ and the label of $(A, v)$ axial, and let
$\delta = \frac\pi3 - \ell + \lambda$. Then $\frac12 - u + G_\delta(A, v) > 0$.

*Proof.* Let $\tau = \lambda = \frac54v$, so $0 \le \tau \le \frac\pi4$ and
$\frac\pi{12} \le \delta < \frac\pi2$. As $\sin\delta \ge 0$, $G_\delta$
decreases in $A$, and $A \le \min(\mathrm{circ}(v), \mathrm{line}(v))$
([Proposition B.15](appendix-b.md#proposition-b15-the-axial-region)).

If $\tau \le s_0$, then $v = \frac45\tau \le u_0$ and $A \le \mathrm{circ}(v)$
([Lemma B.12](appendix-b.md#lemma-b12-the-circle-over-the-u-axis)). As
$\mathrm{circ}(\frac45\tau) + \frac12 = X^{\mathrm{ax}}(\tau)$, and as
$G^{\mathrm{ax}}(\ell, \cdot)$ is nonincreasing on $[0, s_0]$
([Proposition B.23](appendix-b.md#proposition-b23-the-circular-piece)),

```math
G_\delta(A, v) \ge G_\delta\bigl(\mathrm{circ}(v), v\bigr) = G^{\mathrm{ax}}(\ell, \tau) \ge G^{\mathrm{ax}}(\ell, s_0) ,
```

and (D.4) concludes.

If $\tau > s_0$, then $u_0 < v \le \frac\pi5 < r_d$, so $A \le \mathrm{line}(v)$
([Lemma B.12](appendix-b.md#lemma-b12-the-circle-over-the-u-axis)); and
$\mathrm{line}(\frac45\tau) = \frac{2\pi + 7}9 - \frac{44}{45}\tau$, which is
$\mathrm{tie}(\tau)$. So
$G_\delta(A, v) \ge G_\delta(\mathrm{tie}(\tau), \frac45\tau)$. The tie state is
admissible with side label $\tau$ ([Proposition B.16](appendix-b.md#proposition-b16-segments-of-constant-side-label)), and Lemma D.24,
applied to $(a, u)$ and the tie state, gives
$\frac12 - u + G_\delta(\mathrm{tie}(\tau), \frac45\tau) > 0$. $\square$

*Lean:
[`Seven.Boundary.target_axial_pos`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L291).*

### Proposition D.26 (both signs negative)

Let $(a, u)$ and $(A, v)$ be admissible, the label of $(a, u)$ side and the
label of $(A, v)$ axial or side. Then on the forward axis, for the signs
$(-1, -1)$, $\sigma_1(\frac\pi3) > 0$.

*Proof.* If $\ell \le \frac25$, this is Lemma D.17. Let $\ell \ge \frac25$ and
$\delta = \frac\pi3 - \ell + \lambda$. Then
$\frac\pi{12} \le \delta \le \frac{7\pi}{12} - \frac25 < \frac\pi2$, as
$\frac25 \le \ell \le \frac\pi4$ and $0 \le \lambda \le \frac\pi4$; so
$\sin\delta, \cos\delta \ge 0$. By (D.1) with $s = t = -1$ the direction is
$\frac{7\pi}6 + \ell - \lambda = \frac{3\pi}2 - \delta$, and

```math
h\left(A, -v, \tfrac{3\pi}2 - \delta\right) = -A\sin\delta + v\cos\delta + \tfrac12(\sin\delta + \cos\delta) .
```

Hence

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 - u + G_\delta(A, v) ,
```

which is positive by Lemma D.24 if the label of $(A, v)$ is side, and by Lemma
D.25 if it is axial. $\square$

*Lean:
[`Seven.fixed_gap_forward_both_negative_side`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L371).*

Together with the sector $(1, 1)$ of Appendix B, Propositions D.7, D.16 and D.26
give the pair property on the forward axis for all active labels: for the signs
$(1, -1)$ by Proposition D.7; for $(-1, 1)$ by Proposition D.16; and for
$(-1, -1)$ by Proposition D.7 if the label of $(a, u)$ is axial and by
Proposition D.26 if it is side. These are the forward cases of the assembly
([Proposition B.32](appendix-b.md#proposition-b32-active-labels)).
