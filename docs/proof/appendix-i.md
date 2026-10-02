# Appendix I. Seven squares: the critical gap, the forward axis

[Contents](README.md) · [← Appendix H](appendix-h.md)

This appendix proves the critical-gap proposition
([Proposition 10.17](10-seven.md#proposition-1017-the-critical-gap)) on the forward axis, for the signs that
Appendix G leaves open. We use the notation of Chapter 10 and Appendix G: the
admissible *source* state $(a, b)$ with sign $s$ and label $\ell = \ell(a, b)$,
the admissible *target* state $(A, B)$ with sign $t$ and label
$\ell' = \ell(A, B)$ ([Definition 10.4](10-seven.md#definition-104-states),
[Definition 10.6](10-seven.md#definition-106-labels-and-markers)), their remainders $r(a, b)$ and $r(A, B)$, and
the canonical pair $S$, $T$ with its support sums $\sigma_k$
([Definition 10.12](10-seven.md#definition-1012-canonical-pair-and-support-sums)). The forward axis is
$n_1 = u(\frac\pi2)$ in the chart of $S$. It points in the direction of
increasing angle, from the marker of $S$ towards the marker of $T$, and

```math
\sigma_1 = \max_{\overline S}\,\langle\cdot, n_1\rangle - \min_{\overline T}\,\langle\cdot, n_1\rangle
```

compares how far $S$ reaches forward with how far $T$ reaches back. We must show
the *gap property* ([Definition G.1](appendix-g.md#definition-g1-the-gap-property)) on this axis:
$\sigma_1(\frac\pi3) \ge 0$, and $\sigma_1(\frac\pi3) = 0$ only if the two states
with the two signs form a contact ([Definition 10.15](10-seven.md#definition-1015-contacts)). Appendix G
reduces capped labels to active ones and settles the signs $(s, t) = (1, 1)$
([Proposition G.29](appendix-g.md#proposition-g29-the-forward-axis-with-positive-signs)); the other sectors are
settled here.

| signs $(s, t)$ | label of $(a, b)$ | label of $(A, B)$ | statement | $\sigma_1 = 0$ only if |
| --- | --- | --- | --- | --- |
| $(1, -1)$ | any | axial or side | Proposition I.7 | $(a, b)$ axial state, $(A, B) = (1, \frac12)$ |
| $(-1, -1)$ | axial | axial or side | Proposition I.7 | $(a, b)$ axial state, $(A, B) = (1, \frac12)$ |
| $(-1, 1)$ | axial or side | axial or side | Proposition I.16 | $(a, b) = (A, B) = (1, \frac12)$ |
| $(-1, -1)$ | side | axial or side | Proposition I.26 | never |

These possible zeros are the contacts of the optimal packings: a side square
touching the top or bottom square, and the two squares of a side column
(Figure I.1).

All the proofs follow the same plan. First $\sigma_1$ is written in closed form
in one angle, the *turn*, which measures how far $T$ is turned from its position
at a contact. Then the support of $T$ is bounded below over the admissible
targets: by Cauchy–Schwarz on the disk $\varphi \le \frac{13}4$ (§I.2, §I.3),
sharpened near the transition state, where the tie line meets the circle
(§I.2), or by following the boundary of the label regions exactly (§I.4). What
remains is an inequality in the turn alone, proved by elementary calculus: the
sign of a derivative, a bound on a second derivative or concavity, together
with Taylor bounds and exact values at a few points.

![Three canonical pairs in the chart of S, each with the disk centre o, part of the unit circle, the dashed marker rays of S and T pi/3 apart, and on the right a vertical arrow n1 carrying the shadows of S (blue) and T (green), with their overlap sigma1 in orange. Left, signs (1, −1): S = Q(1, 0), and T is an axis-parallel square above it that shares half of the top edge of S; the shadows touch and sigma1 = 0. Middle, signs (−1, 1): S = Q(1, −1/2) and T = Q(1, 1/2) share an edge; sigma1 = 0. Right, signs (−1, −1): S = Q(1, −1/2), and T is turned by 30 degrees and pokes into S; the shadows overlap by sigma1 of about 0.18.](figures/appendix-i/forward-pairs.svg)

*Figure I.1.* The three sectors of this appendix, each at one pair of states, in
the chart of $S$. On the right of each panel are the shadows of $S$ (blue) and
$T$ (green) on the forward axis $n_1$; $\sigma_1(\frac\pi3)$ is their overlap
(orange). Left: the signs $(1, -1)$, the axial state $(1, 0)$ and the side state
$(1, \frac12)$, a contact with $\sigma_1 = 0$ (Proposition I.7). Middle: the
signs $(-1, 1)$ and two side states, a contact with $\sigma_1 = 0$
(Proposition I.16). Right: the signs $(-1, -1)$, the side state $(1, \frac12)$
and the axial state $(1, 0)$, with $\sigma_1 = \frac14(\sqrt3 - 1) \approx 0.18$
(Proposition I.26).

## I.1 The forward support sum and the tools

**The closed form.** In the definition of the support sums
([Definition 10.12](10-seven.md#definition-1012-canonical-pair-and-support-sums)) take $k = 1$ and $g = \frac\pi3$, so that the
relative phase is $d = \frac\pi3 + s\ell - t\ell'$. The first term is
$h(a, sb, \frac\pi2) = sb + \frac12$, and
$\frac\pi2 + \pi - d = \frac{7\pi}6 - s\ell + t\ell'$. Hence
([Lemma G.5](appendix-g.md#lemma-g5-support-sums-in-closed-form))

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 + sb + h\left(A,\ tB,\ \tfrac{7\pi}6 - s\ell + t\ell'\right),
\qquad
h(x, y, z) = x\cos z + y\sin z + \tfrac12\left(\lvert\cos z\rvert + \lvert\sin z\rvert\right) ,
\tag{I.1}
```

where $h$ is the support function
([Definition 10.10](10-seven.md#definition-1010-support-function)). In each sector below the direction
$\frac{7\pi}6 - s\ell + t\ell'$ is $\pi - e$, $\frac{3\pi}2 + w$ or
$\frac{3\pi}2 - d$, for the turn $e$ or $w$ of the sector or the relative phase
$d$ itself (as in the Remark after
[Lemma G.6](appendix-g.md#lemma-g6-the-inward-sum-with-a-positive-source-sign)), and we use $\cos(\pi - x) = -\cos x$,
$\sin(\pi - x) = \sin x$, $\cos(\frac{3\pi}2 \pm x) = \pm\sin x$ and
$\sin(\frac{3\pi}2 \pm x) = -\cos x$.

**Cauchy–Schwarz on the disk.** For an admissible state $(A, B)$ put
$X = A + \frac12$ and $Y = B + \frac12$, so that
$X^2 + Y^2 = \varphi(A, B) \le \frac{13}4$. We call the coefficient vector
$(p, q)$ of a linear form $pX + qY$ its *force*. If $c \ge 0$ and
$\frac{13}4(p^2 + q^2) \le c^2$, then

```math
-c \le p\left(A + \tfrac12\right) + q\left(B + \tfrac12\right) \le c ,
```

and the first inequality is strict if $\frac{13}4(p^2 + q^2) < c^2$
([Lemma G.3](appendix-g.md#lemma-g3-cauchyschwarz-on-the-disk); the upper bound is the lower bound for the force
$(-p, -q)$). Geometrically, $\varphi \le \frac{13}4$ is the disk of radius
$\frac{\sqrt{13}}2$ about $(-\frac12, -\frac12)$ in the $(A, B)$-plane, and the
least and the greatest value of the form on it,
$\mp\frac{\sqrt{13}}2\sqrt{p^2 + q^2}$, are taken where its level lines support
the disk (Figure I.2). The same holds for $(a, b)$ in place of $(A, B)$.

![The admissible states in the (A, B)-plane: the region cut from the disk phi at most 13/4 (dashed circle) by A at least 1/2 and 0 at most B at most A, divided into axial labels (blue, below the dashed tie line), side labels (green) and capped labels (grey); the tie line meets the circle at the transition state (a0, b0). The thick orange line 3A + 2B = 4, marked r(A, B) = 0, touches the circle at the side state (1, 1/2), where the normal (3, 2) is drawn; two dashed parallel orange lines cut the disk.](figures/appendix-i/disk-support.svg)

*Figure I.2.* The admissible states $(A, B)$, with axial labels (blue), side
labels (green) and capped labels (grey); the tie line (dashed) separates the
first two and meets the circle $\varphi = \frac{13}4$ at the transition state
$(a_0, b_0)$. A linear form $p(A + \frac12) + q(B + \frac12)$ is constant on
parallel lines (orange), and on the disk it is at least its value on the one
that supports the disk. Drawn is the case $(p, q) = -(\frac9{10}, \frac35)$ of
Proposition I.10, whose supporting line is $r(A, B) = 0$, touching at the side
state $(1, \frac12)$.

**Taylor bounds.** Put

```math
S_3(x) = x - \tfrac{x^3}6, \quad S_5(x) = S_3(x) + \tfrac{x^5}{120}, \quad
C_2(x) = 1 - \tfrac{x^2}2, \quad C_4(x) = C_2(x) + \tfrac{x^4}{24} .
```

Then $\cos x \ge C_2(x)$ for all real $x$, and for $x \ge 0$

```math
S_3(x) \le \sin x \le x, \qquad \sin x \le S_5(x), \qquad \cos x \le C_4(x) .
\tag{I.2}
```

Starting from $\cos x \le 1$, each of $\sin x \le x$, $\cos x \ge C_2(x)$,
$\sin x \ge S_3(x)$, $\cos x \le C_4(x)$ and $\sin x \le S_5(x)$ follows from
the previous one by integrating from $0$ to $x$
([Lemma A.7](appendix-a.md#lemma-a7-taylor-bounds)); and $\cos x \ge C_2(x)$ holds for $x < 0$ too, as
both sides are even.

**Calculus in one variable.** The inequalities in the turn alone are proved
with the tools of Appendix A. A function with a nonnegative derivative on an
interval is nondecreasing there
([Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative)). A function whose second derivative
is at least $\kappa$ on an interval lies above its tangent parabolas of
curvature $\kappa$ there,
$f(x) \ge f(t) + f'(t)(x - t) + \frac\kappa2(x - t)^2$
([Lemma A.2](appendix-a.md#lemma-a2-tangent-parabolas)). A function whose second derivative is at most 0 on an
interval is concave there, so it is positive on the interval if it is positive
at both ends ([Lemma A.4](appendix-a.md#lemma-a4-positivity-from-concavity)).

**Constants.** We use $3.14 < \pi < \frac{22}7$, and occasionally the sharper
bounds of [§2.1](02-preliminaries.md#21-conventions). Also $1.73 < \sqrt3 < 1.733$, since
$1.73^2 < 3 < 1.733^2$ ([Lemma 10.5](10-seven.md#lemma-105-admissible-states) (2)); so
$\frac7{10} < \sqrt3 - 1 < \frac{11}{15}$.

**Admissible states.** For an admissible state $(a, b)$ with label $\ell$ we use
the following facts from Chapter 10.

- $0 \le \ell \le \frac\pi4$, $\ell \le \mathrm{axial}(b) = \frac54b$ and
  $\ell \le \mathrm{side}(a, b)$; and $\ell = 0$ only if $b = 0$
  ([Lemma 10.7](10-seven.md#lemma-107-the-label) (2)).
- $a + b < \frac{31}{20}$, $b < \frac{31}{40}$ and $a \le \sqrt3 - \frac12$
  ([Lemma 10.5](10-seven.md#lemma-105-admissible-states) (2)).
- $r(a, b) = 4 - 3a - 2b \ge 0$ ([Lemma 10.5](10-seven.md#lemma-105-admissible-states) (1)), and
  ([Lemma 10.7](10-seven.md#lemma-107-the-label) (1))

  ```math
  \mathrm{side}(a, b) = \tfrac\pi6 + \tfrac56\left(b - \tfrac12\right) + \tfrac14 r(a, b)
  = \tfrac\pi6 - \tfrac54(a - 1) - \tfrac16 r(a, b) .
  \tag{I.3}
  ```

- If $r(a, b) = 0$, then $(a, b)$ is the side state $(1, \frac12)$, whose label
  is $\frac\pi6$; if $b = 0$, then $(a, b)$ is an axial state
  ([Lemma 10.16](10-seven.md#lemma-1016-contacts) (2), (1), (3)).
- If the label is side, then $\ell > \frac9{25}$ and $a < \frac98$
  ([Lemma 10.8](10-seven.md#lemma-108-side-and-axial-labels) (1)); and $b \le \frac12 + \frac65(\ell - \frac\pi6)$ by
  (I.3) and $r \ge 0$.
- If the label is axial, then $b = \frac45\ell \le \frac\pi5$;
  $9a + 11b \le 2\pi + 7$, which is $\mathrm{axial}(b) \le \mathrm{side}(a, b)$
  multiplied by 12; and $a + b < 1 + \frac{2\pi}{15}$
  ([Lemma 10.8](10-seven.md#lemma-108-side-and-axial-labels) (2)).

**The boundary of the label regions.** From Appendix G we use the following
objects and facts. They concern one admissible state, which we write $(A, B)$,
with label $\ell'$, or $\tau$ when the label is a variable.

- The *tie line* $9A + 11B = 2\pi + 7$, where the axial and the side label
  agree, meets the circle $\varphi = \frac{13}4$ at the *transition state*
  $(a_0, b_0)$, whose label is $s_0 = \frac54 b_0$ ([Definition G.9](appendix-g.md#definition-g9-boundary-curves-and-special-states)).
  With $X_0 = a_0 + \frac12$ and $Y_0 = b_0 + \frac12$ we have
  $X_0^2 + Y_0^2 = \frac{13}4$, $9X_0 + 11Y_0 = 2\pi + 17$,
  $1.11979 < a_0 < 1.1198$ and $0.29136 < b_0 < 0.29137$; hence
  $\frac{11}{10} < a_0 < \frac98$, $\frac{29}{100} < b_0 < \frac3{10}$ and
  $\frac9{25} < s_0 < \frac25$, with $s_0 \approx 0.3642$
  ([Lemma G.10](appendix-g.md#lemma-g10-the-transition-state)). Every admissible state with side label has
  $b_0 \le B$, $A \le a_0$ and $s_0 \le \ell'$
  ([Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (1)).
- *Tie states.* Let $\alpha(\tau) = \frac{2\pi + 7}9 - \frac{44}{45}\tau$. Every
  state with side label $\tau$ lies on the line
  $A = \alpha(\tau) + \frac49\left(B - \frac45\tau\right)$
  ([Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (5)). For $s_0 \le \tau \le \frac\pi4$ the
  *tie state* $(\alpha(\tau), \frac45\tau)$, on the tie line, is admissible, and
  its label, its axial label and its side label all equal $\tau$
  (Proposition G.16 (3)).
- *The diagonal corner.* The diagonal $B = A$ meets the circle at the
  *diagonal corner* $(r_d, r_d)$, where $r_d = \sqrt{13/8} - \frac12$ and
  $0.77475 < r_d < 0.77476$. Its side label is
  $t_d = \frac\pi6 + \frac7{12} - \frac5{12}r_d$, and
  $\frac{18}{25} < t_d < \frac\pi4$. The *diagonal state*
  $(\delta(\tau), \delta(\tau))$ with $\delta(\tau) = \frac15(2\pi + 7 - 12\tau)$
  has side label $\tau$, and
  $\delta(t_d) = r_d$ ([Definition G.9](appendix-g.md#definition-g9-boundary-curves-and-special-states),
  [Lemma G.11](appendix-g.md#lemma-g11-the-diagonal-corner)).
- *The circle parametrized by the side label.* For $s_0 \le \tau \le t_d$ let
  $N = \frac{97}{144}$, $D(\tau) = \frac\pi6 + \frac{19}{24} - \tau$,
  $Z(\tau) = \sqrt{\frac{13}4N - D(\tau)^2}$,
  $X(\tau) = \frac1N\left(\frac34D + \frac13Z\right)$ and
  $Y(\tau) = \frac1N\left(-\frac13D + \frac34Z\right)$
  ([Definition G.13](appendix-g.md#definition-g13-the-circle-parametrized-by-the-side-label)). Then
  $X^2 + Y^2 = \frac{13}4$, $\frac34X - \frac13Y = D$ and
  $\frac13X + \frac34Y = Z$, so the state $(X(\tau) - \frac12, Y(\tau) - \frac12)$
  is on the circle and has side label $\tau$; it is the transition state at
  $\tau = s_0$ and the diagonal corner $(r_d, r_d)$ at $\tau = t_d$. On
  $[s_0, t_d]$ we have $\frac12 < D < 1$, $0 < Y_0 \le Y \le X$,
  $\frac54 < X \le X_0$ and $1 < Z < \frac75$, and $X' = -Y/Z$, $Y' = X/Z$,
  $Z' = D/Z$ ([Lemma G.14](appendix-g.md#lemma-g14-the-parametrization)).
- *Side segments.* For $s_0 \le \tau \le \frac\pi4$ the *top* of the side label
  $\tau$ is the state $(\hat a(\tau), \hat b(\tau))$, equal to
  $(X(\tau) - \frac12, Y(\tau) - \frac12)$ if $\tau \le t_d$ and to
  $(\delta(\tau), \delta(\tau))$ if $\tau > t_d$ (Definition G.13). It is
  admissible with side label $\tau$, and every admissible $(A, B)$ with side
  label $\tau$ lies on the *side segment* from the tie state to the top
  (Figure I.3): $\frac45\tau \le B \le \hat b(\tau)$ and
  $A = \alpha(\tau) + \frac49(B - \frac45\tau)$
  ([Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (2), (4)).
- *The axial boundary.* Let
  $\gamma(B) = \sqrt{\frac{13}4 - (B + \frac12)^2} - \frac12$ (the circle),
  $\lambda(B) = \frac19(2\pi + 7 - 11B)$ (the tie line) and
  $\chi(B) = \min(\gamma(B), \lambda(B))$ (Definition G.9). Every admissible
  $(A, B)$ with axial label has $A \le \chi(B)$
  ([Proposition G.15](appendix-g.md#proposition-g15-the-axial-region) (1)), and $\chi(B) = \gamma(B)$
  for $0 \le B \le b_0$, $\chi(B) = \lambda(B)$ for $b_0 \le B \le r_d$
  ([Lemma G.12](appendix-g.md#lemma-g12-the-circle-over-the-b-axis) (3)). Also $\lambda(\frac45\tau) = \alpha(\tau)$.

![Two copies of the side region of the (A, B)-plane, green, between the dashed tie line below, the circle on the right and the short diagonal at the top, with the axial region in blue below the tie line and the grey capped corner. In each copy a thick segment of slope 9/4 runs from the tie state on the tie line up to the top on the circle, four dashed orange level lines of the target support cross the region, and an orange arrow shows where the support grows. Left, for the source label pi/4: the level lines are less steep than the segment, and the tie state is ringed as the end where the support is least. Right, for the source label 2/5: the level lines are steeper than the segment, and the top is ringed. The left copy also names the transition state (a0, b0), the diagonal corner (rd, rd), the tie line and the circle.](figures/appendix-i/switch.svg)

*Figure I.3.* The side region of the $(A, B)$-plane between the tie line
(dashed), the circle and the diagonal, with the transition state $(a_0, b_0)$
and the diagonal corner $(r_d, r_d)$. The thick segment is the side segment of
label $\tau = 0.7$, from its tie state $(\alpha(\tau), \frac45\tau)$ to its top
$(\hat a(\tau), \hat b(\tau))$ on the circle; it has the direction $(4, 9)$, at
the angle $\omega$ to the $A$-axis. The dashed lines are level lines of the
target support $G_d$, of the direction $(\cos d, \sin d)$, and the arrow points
to where $G_d$ grows. Left: for the source label $\ell = \frac\pi4$,
$d = \frac\pi{12} + \tau < \omega$, and along the segment $G_d$ is least at
the tie state (ring). Right: for $\ell = \frac25$, $d > \omega$, and it is
least at the top. The least end changes at $\tau = \mathrm{sw}(\ell)$, where
$d = \omega$ and the level lines are parallel to the segment.

**The target support on the boundary.** For a source label $\ell$ and a target
label $\tau$ put $d = \frac\pi3 - \ell + \tau$ and

```math
G_d(A, B) = -\left(A - \tfrac12\right)\sin d + \left(B + \tfrac12\right)\cos d ,
```

the part of $\sigma_1(\frac\pi3)$ that depends on the target when $s = t = -1$
(§I.4). With $\zeta(\tau) = \frac12 + \frac45\tau$ and
$\xi(\tau) = \sqrt{\frac{13}4 - \zeta(\tau)^2} = \gamma(\frac45\tau) + \frac12$,
its values at the state $(\xi(\tau) - \frac12, \zeta(\tau) - \frac12)$ of axial
label $\tau \le s_0$ on the circle, at the tie state and at the top of the side
label $\tau$ are ([Definition G.21](appendix-g.md#definition-g21-targets-on-the-boundary))

```math
\begin{aligned}
C(\ell, \tau) &= -\left(\xi(\tau) - 1\right)\sin d + \zeta(\tau)\cos d, \\
L(\ell, \tau) &= -\left(\alpha(\tau) - \tfrac12\right)\sin d + \zeta(\tau)\cos d, \\
H(\ell, \tau) &= -\left(\hat a(\tau) - \tfrac12\right)\sin d + \left(\hat b(\tau) + \tfrac12\right)\cos d .
\end{aligned}
```

If $\frac25 \le \ell \le \frac\pi4$, then $\tau \mapsto C(\ell, \tau)$ is
nonincreasing on $[0, s_0]$, and ([Proposition G.23](appendix-g.md#proposition-g23-the-circular-piece))

```math
C(\ell, s_0) = L(\ell, s_0) = -\left(a_0 - \tfrac12\right)\sin\left(\tfrac\pi3 - \ell + s_0\right) + Y_0\cos\left(\tfrac\pi3 - \ell + s_0\right) .
```

- *The switch.* Let $\omega = \arctan\frac94$, so that $0 < \omega < \frac\pi2$
  and $\cos\omega = \frac49\sin\omega$; for $0 \le x \le \frac\pi2$,
  $\cos x - \frac49\sin x \ge 0$ if and only if $x \le \omega$
  ([Lemma G.24](appendix-g.md#lemma-g24-the-switch-angle)). The *switch label* of $\ell$ is
  $\mathrm{sw}(\ell) = \omega - \frac\pi3 + \ell$ (Definition G.21), so that
  $d \le \omega$ if and only if $\tau \le \mathrm{sw}(\ell)$. The side segments
  have the direction $(4, 9)$, at the angle $\omega$, and the level lines of
  $G_d$ have the direction $(\cos d, \sin d)$; so along a side segment $G_d$
  grows towards the top if $d < \omega$ and towards the tie state if
  $d > \omega$ (Figure I.3). If $\frac25 \le \ell \le \frac\pi4$,
  $s_0 \le \tau \le \frac\pi4$ and $\tau \le \mathrm{sw}(\ell)$, then
  $C(\ell, s_0) \le L(\ell, \tau)$
  ([Proposition G.25](appendix-g.md#proposition-g25-the-straight-piece)).
- *Two profiles.* If $(a, b)$ is admissible with side label $\ell \ge \frac25$,
  then ([Lemma G.18](appendix-g.md#lemma-g18-the-transition-profile) (4))

  ```math
  \tfrac12 - b + C(\ell, s_0) > 0 .
  \tag{I.4}
  ```

  For $\frac25 \le \ell \le \frac\pi4$ ([Lemma G.20](appendix-g.md#lemma-g20-the-diagonal-profile) (2)),

  ```math
  K(\ell) = \tfrac65\left(\tfrac\pi6 - \ell\right) + \tfrac{51}{40}\cos\left(\tfrac{7\pi}{12} - \ell\right) - \tfrac{11}{40}\sin\left(\tfrac{7\pi}{12} - \ell\right) > 0 .
  \tag{I.5}
  ```

## I.2 Target sign negative

In this section $t = -1$, and $s = 1$ or the label of $(a, b)$ is axial. The
turn is $e = s\ell + \ell' - \frac\pi6$. The frame of $T$ is turned against that
of $S$ by the relative phase $d = \frac\pi3 + s\ell + \ell' = \frac\pi2 + e$, so
$e = 0$ when $T$ is turned by a quarter turn, as when the top or bottom square
touches a side square (Figure I.1, left). Lemma I.1 bounds $\sigma_1$ below by
an expression in the target and the turn; Lemmas I.2 and I.3 treat an axial
target, Lemmas I.4 to I.6 a side target, and Proposition I.7 puts them
together (Figure I.8).

### Lemma I.1 (the support sum for target sign negative)

Let $(a, b)$ and $(A, B)$ be admissible states and $s \in \lbrace 1, -1\rbrace$,
and suppose that $s = 1$ or that the label of $(a, b)$ is axial. Let
$e = s\ell + \ell' - \frac\pi6$, and for real $x$ and $\rho$ put

```math
\beta(A, B; x, \rho) = \tfrac12 + \tfrac45\rho - \left(A - \tfrac12\right)\cos x - B\sin x + \tfrac12\lvert\sin x\rvert .
```

Then on the forward axis, for the signs $(s, -1)$,
$\sigma_1(\frac\pi3) \ge \beta(A, B; e, s\ell)$.

*Proof.* By (I.1) with $t = -1$ the direction is
$\frac{7\pi}6 - s\ell - \ell' = \pi - e$, and

```math
h(A, -B, \pi - e) = -A\cos e - B\sin e + \tfrac12\left(\lvert\cos e\rvert + \lvert\sin e\rvert\right) .
```

As $0 \le \ell, \ell' \le \frac\pi4$, the turn satisfies
$-\frac{5\pi}{12} \le e \le \frac\pi3$, so $\cos e \ge 0$ and

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 + sb - \left(A - \tfrac12\right)\cos e - B\sin e + \tfrac12\lvert\sin e\rvert .
```

It remains to show $sb \ge \frac45 s\ell$. If $s = 1$ this is
$\ell \le \mathrm{axial}(b) = \frac54b$. If $s = -1$, the label is axial, so
$\ell = \frac54b$ and $sb = \frac45 s\ell$. $\square$

*Lean:
[`Seven.forward_negative_target_lower`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L25),
[`Seven.rawTarget`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L22).*

### Lemma I.2 (an axial target at a negative turn)

Let $(A, B)$ be admissible with axial label, and $0 \le z \le \frac\pi2$. Then

```math
1 + \tfrac{2\pi}{15} - \tfrac45z + \cos z - \left(A + \tfrac12\right)\cos z - \left(B + \tfrac12\right)(1 - \sin z) > 0 .
```

![Two panels. Left: the plane of forces (p, q), with the shaded cone between the ray of the normal (X0, Y0) of the circle at the transition state, of slope about 0.49, and the ray of the normal (9, 11) of the tie line; the black arc of forces (cos z, 1 − sin z) runs inside the cone from (1, 1) at z = 0 to (root 3 over 2, 1/2) at z = pi/6, and dotted beyond it, leaving the cone near z = 0.66 and ending at the origin at z = pi/2. Right: the (A, B)-plane near the transition state, with the axial region (blue) below the dashed tie line and inside the circle, and the level lines through the transition state of the forms for z = 0 and z = pi/6 (orange), which leave the axial region on one side.](figures/appendix-i/transition-force.svg)

*Figure I.4.* Lemma I.2 for small turns. Left: for $0 \le z \le \frac\pi6$ the
force $(\cos z, 1 - \sin z)$ (black) lies in the cone (shaded) spanned by the
normal $(X_0, Y_0)$ of the circle and the normal $(9, 11)$ of the tie line at
the transition state. Right: so the level line of the form through the
transition state (orange, for $z = 0$ and $z = \frac\pi6$) has the states with
axial label (blue) on its lower side, and the form is largest at the transition
state $(a_0, b_0)$.

*Proof.* Put $X = A + \frac12$ and $Y = B + \frac12$, so that
$X^2 + Y^2 = \varphi(A, B) \le \frac{13}4$, and
$\Lambda(z) = 1 + \frac{2\pi}{15} - \frac45z + \cos z$. The claim is
$X\cos z + Y(1 - \sin z) < \Lambda(z)$: the linear form with the force
$(\cos z, 1 - \sin z)$ stays below $\Lambda(z)$ on the states with axial label.
The label is axial, so $9A + 11B \le 2\pi + 7$, that is

```math
9X + 11Y \le 2\pi + 17 .
\tag{I.6}
```

Let $\nu = \cos\frac z2 - \sin\frac z2$. As
$\sin z = 2\sin\frac z2\cos\frac z2$,

```math
\cos^2 z + (1 - \sin z)^2 = 2 - 2\sin z = 2\nu^2 ,
```

and $\nu \ge 0$ by [Lemma A.6](appendix-a.md#lemma-a6-sine-and-cosine-compared) (1), as $0 \le \frac z2 \le \frac\pi4$. So
the force has length $\sqrt2\,\nu$. For large turns the disk alone bounds the
form (step 3). For small turns it does not: at $z = 0$ the greatest value of
$X + Y$ on the disk is $\sqrt{13/2} > 2.5$, while
$\Lambda(0) = 2 + \frac{2\pi}{15} < 2.5$. On the states with axial label the
form is then largest at the transition state, where the tie line (I.6) meets
the circle (steps 1 and 2, Figure I.4). The two cases meet at $z = \frac\pi6$
(Figure I.5).

1. *Small turns: the transition state.* Let $0 \le z \le \frac\pi6$. Then
   $0 \le \sin z \le \frac12$ and $\cos z \ge \frac{\sqrt3}2 > \frac56$, as the
   sine increases and the cosine decreases on $[0, \frac\pi2]$, and
   $\sqrt3 > \frac53$. We show that the form is at most its value at the
   transition state,

   ```math
   X\cos z + Y(1 - \sin z) \le X_0\cos z + Y_0(1 - \sin z) .
   ```

   Let $P = 11\cos z - 9(1 - \sin z)$ and $Q = X_0(1 - \sin z) - Y_0\cos z$.
   Expanding shows

   ```math
   (11X_0 - 9Y_0)\bigl[(X_0 - X)\cos z + (Y_0 - Y)(1 - \sin z)\bigr]
   = P\left(X_0^2 + Y_0^2 - X_0X - Y_0Y\right) + Q\left(9X_0 + 11Y_0 - 9X - 11Y\right) .
   ```

   All factors on the right are nonnegative. First, $P > 11\cdot\frac56 - 9 > 0$,
   and $Q \ge \frac12X_0 - Y_0 > 0$, as $X_0 > \frac85$ and $Y_0 < \frac45$
   (§I.1). Next,
   $X_0X + Y_0Y \le \frac12(X_0^2 + Y_0^2 + X^2 + Y^2) \le \frac{13}4 = X_0^2 + Y_0^2$.
   Last, $9X + 11Y \le 2\pi + 17 = 9X_0 + 11Y_0$ by (I.6). As $11X_0 - 9Y_0 > 0$,
   the claim follows. In other words, the force is
   $\frac1{11X_0 - 9Y_0}\bigl(P\,(X_0, Y_0) + Q\,(9, 11)\bigr)$, a combination
   with nonnegative coefficients of the normals at the transition state of the
   circle and of the tie line.
2. *Small turns: the margin.* By step 1, it suffices that

   ```math
   f(z) = \Lambda(z) - X_0\cos z - Y_0(1 - \sin z) > 0 .
   ```

   Here
   $f''(z) = (X_0 - 1)\cos z - Y_0\sin z > \frac35\cdot\frac56 - \frac45\cdot\frac12 > 0$,
   as $X_0 - 1 = a_0 - \frac12 > \frac35$. By
   [Lemma A.2](appendix-a.md#lemma-a2-tangent-parabolas) with $t = 0$ and $\kappa = 0$, $f$ lies above
   its tangent at 0:

   ```math
   f(z) \ge f(0) + f'(0)\,z = \left(2 + \tfrac{2\pi}{15} - X_0 - Y_0\right) - \left(\tfrac45 - Y_0\right)z .
   ```

   By the bounds on $a_0$ and $b_0$ (§I.1) and $\pi > 3.1415$, the first
   bracket exceeds $2.4188 - 1.6198 - 0.79137 > 0.0076$ and the second is
   below $0.8 - 0.79136 < 0.0087$. As $z \le \frac\pi6 < 0.53$,
   $f(z) > 0.0076 - 0.0087\cdot 0.53 > 0$.
3. *Large turns: the disk alone.* Let $\frac\pi6 \le z \le \frac\pi2$. The force
   has squared length $2\nu^2$, and
   $\frac{13}4\cdot2\nu^2 \le (\frac{51}{20}\nu)^2$, as
   $\frac{13}2 < (\frac{51}{20})^2 = 6.5025$. So Cauchy–Schwarz on the
   disk ([Lemma G.3](appendix-g.md#lemma-g3-cauchyschwarz-on-the-disk)) gives $X\cos z + Y(1 - \sin z) \le \frac{51}{20}\nu$,
   and it suffices that

   ```math
   m_2(z) = \Lambda(z) - \tfrac{51}{20}\left(\cos\tfrac z2 - \sin\tfrac z2\right) > 0 .
   ```

   As $\cos z = \cos^2\frac z2 - \sin^2\frac z2$ is
   $\nu\,(\cos\frac z2 + \sin\frac z2)$, the second derivative factors:

   ```math
   m_2''(z) = -\cos z + \tfrac{51}{80}\nu = \nu\left(\tfrac{51}{80} - \cos\tfrac z2 - \sin\tfrac z2\right) \le 0 ,
   ```

   since $(\cos\frac z2 + \sin\frac z2)^2 = 1 + \sin z \ge 1$. So $m_2$ is
   concave on $[\frac\pi6, \frac\pi2]$, and by [Lemma A.4](appendix-a.md#lemma-a4-positivity-from-concavity) it suffices
   that it is positive at both ends. At $z = \frac\pi6$ the terms in $\pi$
   cancel, and $2\nu^2 = \cos^2\frac\pi6 + (1 - \sin\frac\pi6)^2 = 1$; so
   $\nu^2 = \frac12 < \frac{25}{49}$, $\nu < \frac57$ and

   ```math
   m_2\left(\tfrac\pi6\right) = 1 + \tfrac{\sqrt3}2 - \tfrac{51}{20}\nu > 1.865 - \tfrac{51}{28} > 0 .
   ```

   At $z = \frac\pi2$ the force vanishes, $\nu = 0$, and
   $m_2(\frac\pi2) = 1 - \frac{4\pi}{15}$, which is positive as
   $\pi < \frac{15}4$. $\square$

![Two panels. Left: graph over z from 0 to pi/2 of the least value of the left side of Lemma I.2 over the admissible states with axial label (blue), near 0.008 at z = 0, rising to about 0.17 and ending near 0.16; on [0, pi/6] it is the bound f, drawn over it in orange; on [pi/6, pi/2] the green bound m2, close below the blue curve, above its dashed chord; a dotted green continuation of m2 to the left of pi/6 reaches 0 near z = 0.32; a dotted box marks [0, pi/6] by [0, 0.07]. Right: that box magnified, with f and below it its dashed orange tangent at 0, falling from about 0.0077 to about 0.0032 at pi/6, where it is marked.](figures/appendix-i/axial-profile.svg)

*Figure I.5.* Lemma I.2. The left side of the lemma, minimized over the
admissible states with axial label (blue), and the lower bounds of the proof:
$f$ on $[0, \frac\pi6]$ (orange), which is the least value there, above its
tangent at 0 (dashed, right), and $m_2$ on $[\frac\pi6, \frac\pi2]$ (green),
concave and so above its chord (dashed). The right panel magnifies the dotted
box. Continued to the left of $\frac\pi6$, $m_2$ (dotted) becomes negative
below $z \approx 0.32$: there the disk alone does not suffice, and the tie line
(I.6) is needed.

*Lean:
[`Seven.axial_target_support`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L170),
[`Seven.small_turn_bounds`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L58),
[`Seven.axial_small_turn`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L72),
[`Seven.axial_large_turn`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L116),
[`dot_ge`](../../SquaresInCircles/Common/DiskSupport.lean#L30).*

### Lemma I.3 (an axial target)

Let $(A, B)$ be admissible with axial label $\ell'$, and let $e$, $\rho$ be
real numbers with $-\frac\pi2 \le e \le \frac\pi3$ and
$e = \rho + \ell' - \frac\pi6$. Then $\beta(A, B; e, \rho) > 0$.

*Proof.* As $\ell' = \frac54B$, we have $\rho = e - \ell' + \frac\pi6$ and
$\frac45\rho = \frac45e - B + \frac{2\pi}{15}$, so

```math
\beta(A, B; e, \rho) = \tfrac12 + \tfrac{2\pi}{15} + \tfrac45e - \left(A - \tfrac12\right)\cos e - B(1 + \sin e) + \tfrac12\lvert\sin e\rvert .
```

If $e \ge 0$, then $\sin e \ge 0$, as $e \le \frac\pi3$, and expanding shows

```math
\beta = \left(1 + \tfrac{2\pi}{15} - A - B\right) + \left(A - \tfrac12\right)(1 - \cos e) + \left(\tfrac{13}{20} - B\right)\sin e + \tfrac3{20}(e - \sin e) + \tfrac{13}{20}e .
```

The first term is positive by [Lemma 10.8](10-seven.md#lemma-108-side-and-axial-labels) (2). The others are
nonnegative, as $A \ge \frac12$, $B \le \frac\pi5 < \frac{13}{20}$ and
$0 \le \sin e \le e$.

If $e < 0$, let $z = -e$, so $0 < z \le \frac\pi2$, $\sin e = -\sin z \le 0$ and
$\lvert\sin e\rvert = \sin z$. Then

```math
\beta = 1 + \tfrac{2\pi}{15} - \tfrac45z + \cos z - \left(A + \tfrac12\right)\cos z - \left(B + \tfrac12\right)(1 - \sin z) ,
```

which is positive by Lemma I.2. $\square$

*Lean:
[`Seven.negative_target_axial_pos`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L285).*

### Lemma I.4 (the tangent at the transition state)

Let $(A, B)$ be admissible with side label. Then
$\frac{12}{25}(B - b_0) \le a_0 - A$.

*Proof.* Write $A + \frac12 = X_0 + (A - a_0)$ and
$B + \frac12 = Y_0 + (B - b_0)$. Since
$\varphi(A, B) \le \frac{13}4 = X_0^2 + Y_0^2$, expanding gives

```math
2X_0(A - a_0) + 2Y_0(B - b_0) \le -(A - a_0)^2 - (B - b_0)^2 \le 0 :
```

the state lies on the side of the tangent of the circle at the transition state
that contains the disk (Figure I.6). By
[Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (1), $B - b_0 \ge 0$. By the
bounds on $a_0$ and $b_0$ (§I.1),
$\frac{12}{25}X_0 < \frac{12}{25}\cdot\frac{13}8 = \frac{39}{50}$ and
$\frac{39}{50} < \frac{79}{100} < Y_0$. Hence
$\frac{12}{25}X_0(B - b_0) \le Y_0(B - b_0) \le X_0(a_0 - A)$, and we divide by
$X_0 > 0$. $\square$

![A magnified part of the (A, B)-plane around the transition state: the thin curved region of side labels (green) between the dashed tie line and the circle, above the horizontal line B = b0 and to the left of the vertical line A = a0, and the orange tangent of the circle at the transition state, with the region on its inner side.](figures/appendix-i/transition-tangent.svg)

*Figure I.6.* Lemma I.4. The states with side label (green) lie in the quarter
plane $B \ge b_0$, $A \le a_0$ and on the inner side of the tangent (orange) of
the circle at the transition state $(a_0, b_0)$. In that quarter plane the
tangent, of slope $-X_0/Y_0$, may be replaced by the slightly steeper line
$\frac{12}{25}(B - b_0) = a_0 - A$ of slope $-\frac{25}{12}$, which at this
scale cannot be told apart from it.

*Lean:
[`Seven.side_transition_trade`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L177).*

### Lemma I.5 (a side target at a nonnegative turn)

Let $(A, B)$ be admissible, and for real $e$ put

```math
\beta_{\mathrm{side}}(A, B; e) = \tfrac45e + \tfrac2{15}r(A, B) + \left(A - \tfrac12\right)(1 - \cos e) - B\sin e + \tfrac12\lvert\sin e\rvert .
```

If $0 \le e \le \frac\pi3$, then
$\beta_{\mathrm{side}}(A, B; e) \ge \frac{21}{40}e + \frac2{15}r(A, B)$.

*Proof.* Here $0 \le \sin e \le e$, and expanding shows

```math
\beta_{\mathrm{side}}(A, B; e) - \tfrac{21}{40}e - \tfrac2{15}r(A, B)
= \left(A - \tfrac12\right)(1 - \cos e) + \left(\tfrac{31}{40} - B\right)\sin e + \tfrac{11}{40}(e - \sin e) .
```

The three terms are nonnegative, since $A \ge \frac12$ and $B < \frac{31}{40}$
([Lemma 10.5](10-seven.md#lemma-105-admissible-states) (2)). $\square$

*Lean:
[`Seven.sideTarget`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L197),
[`Seven.sideTarget_positive_angle`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L201).*

### Lemma I.6 (a side target at a negative turn)

Let $(A, B)$ be admissible with side label, and $0 < z < 1$. Then
$\beta_{\mathrm{side}}(A, B; -z) > 0$.

*Proof.* As $0 < z < \pi$, $\lvert\sin(-z)\rvert = \sin z$. Substituting
$r(A, B) = 4 - 3A - 2B$ and expanding gives

```math
\beta_{\mathrm{side}}(A, B; -z) = E(A, B) := L_0(z) + \left(\tfrac35 - \cos z\right)\left(A + \tfrac12\right) + \left(\sin z - \tfrac4{15}\right)\left(B + \tfrac12\right),
\qquad L_0(z) = \cos z - \tfrac2{15} - \tfrac45z .
```

By [Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (1), $A \le a_0$ and $B \ge b_0$,
where $a_0 > \frac{11}{10}$ and $b_0 > \frac{29}{100}$. Let

```math
k(z) = \tfrac{12}{25}\left(\cos z - \tfrac35\right) + \sin z - \tfrac4{15} .
```

This is the rate of change of $E$ along the line
$a_0 - A = \frac{12}{25}(B - b_0)$ of Lemma I.4: moving the state from
$(a_0, b_0)$ along this line, so that $B$ grows by $t$, changes $E$ by
$k(z)\,t$. The function $k$ increases on $[0, 1]$, by
[Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative): there
$k'(y) = \cos y - \frac{12}{25}\sin y \ge \frac12 - \frac{12}{25} = \frac1{50}$,
as $\cos y \ge 1 - \frac{y^2}2 \ge \frac12$ and $\sin y \le 1$. At
$\frac1{10}$, by (I.2),

```math
k\left(\tfrac1{10}\right) \ge \tfrac{12}{25}\left(C_2\left(\tfrac1{10}\right) - \tfrac35\right) + S_3\left(\tfrac1{10}\right) - \tfrac4{15} > 0.48\cdot 0.395 + 0.0998 - 0.2667 > 0 .
```

So $k(z) > 0$ for $\frac1{10} \le z \le 1$. Every $z$ in $(0, 1)$ has
$z < \frac1{10}$, or $z \ge \frac1{10}$ and $\cos z \ge \frac35$, or
$\cos z < \frac35$, and we treat these three cases in turn (Figure I.7).

1. *If $z < \frac1{10}$: the disk alone.* Let

   ```math
   g(z) = \sin z - \tfrac45z - \tfrac{13}4(1 - \cos z) .
   ```

   Expanding and using $\sin^2 z + \cos^2 z = 1$,

   ```math
   E(A, B) = g(z) + \tfrac2{15}\left(\tfrac{13}4 - \varphi(A, B)\right) + \tfrac2{15}\left[\left(A - 1 + \tfrac{15}4(1 - \cos z)\right)^2 + \left(B - \tfrac12 + \tfrac{15}4\sin z\right)^2\right] .
   ```

   At $z = 0$ the bracket is the squared distance from $(A, B)$ to the side
   state $(1, \frac12)$, and the identity is $E(A, B) = \frac2{15}r(A, B)$ of
   [Lemma 10.5](10-seven.md#lemma-105-admissible-states) (1). As $\varphi(A, B) \le \frac{13}4$, we get
   $E(A, B) \ge g(z)$, and by (I.2)

   ```math
   g(z) \ge S_3(z) - \tfrac45z - \tfrac{13}8z^2 = z\left(\tfrac15 - \tfrac{13}8z - \tfrac{z^2}6\right) > z\left(\tfrac15 - 2z\right) > 0 .
   ```

2. *If $z \ge \frac1{10}$ and $\cos z \ge \frac35$: the transition state.*
   Expanding,

   ```math
   E(A, B) - E(a_0, b_0) = \left(\cos z - \tfrac35\right)\left[(a_0 - A) - \tfrac{12}{25}(B - b_0)\right] + k(z)\,(B - b_0) ,
   ```

   and both terms are nonnegative, by Lemma I.4, $k(z) > 0$ and $B \ge b_0$. It
   remains to show $E(a_0, b_0) > 0$. Written as $\beta_{\mathrm{side}}$,

   ```math
   E(a_0, b_0) = \tfrac2{15}r(a_0, b_0) + \left(a_0 - \tfrac12\right)(1 - \cos z) + \left(b_0 + \tfrac12\right)\sin z - \tfrac45z ,
   ```

   where $r(a_0, b_0) \ge 0$, as the transition state is admissible
   ([Lemma G.10](appendix-g.md#lemma-g10-the-transition-state)), $a_0 - \frac12 > \frac35$ and
   $b_0 + \frac12 > \frac45 - \frac1{100}$. With $\cos z \le C_4(z)$,
   $S_3(z) \le \sin z \le z$ from (I.2), and $z^4 \le z^2$, $z^3 \le z^2$ as
   $0 < z < 1$,

   ```math
   E(a_0, b_0) \ge \tfrac35(1 - \cos z) - \tfrac45(z - \sin z) - \tfrac1{100}\sin z
   \ge -\tfrac z{100} + \tfrac3{10}z^2 - \tfrac2{15}z^3 - \tfrac1{40}z^4
   > z\left(\tfrac z8 - \tfrac1{100}\right) ,
   ```

   as $\frac2{15} + \frac1{40} < \frac3{10} - \frac18$; and this is positive, as
   $z \ge \frac1{10}$.
3. *If $\cos z < \frac35$: the signs.* As $z < 1$,
   $\cos z \ge 1 - \frac{z^2}2 > \frac12$, so $\cos^2 z < \frac9{25}$ and
   $\sin z > \frac45$. Both coefficients $\frac35 - \cos z$ and
   $\sin z - \frac4{15}$ are positive, and as $A \ge \frac12$ and
   $B \ge b_0 > \frac{29}{100}$,

   ```math
   E(A, B) \ge L_0(z) + \left(\tfrac35 - \cos z\right) + \tfrac{79}{100}\left(\sin z - \tfrac4{15}\right)
   = \tfrac7{15} - \tfrac45z + \tfrac{79}{100}\left(\sin z - \tfrac4{15}\right)
   > \tfrac7{15} - \tfrac45 + \tfrac{79}{100}\cdot\tfrac8{15} > 0 . \qquad\square
   ```

![Two panels sharing the z-axis from 0 to 1, cut by vertical lines at z = 1/10 and at z = arccos 3/5; the three ranges are numbered 1, 2 and 3. Top: the least value of the expression of Lemma I.6 over the admissible states with side label (blue), from 0 at z = 0 up to about 0.16 at z = 1, with an inset magnifying z from 0 to 0.15: there the dashed green value at the transition state lies slightly above the blue curve up to z of about 0.076, where k = 0, and on it after, and the orange bound g of the disk alone is a small positive arch below the blue curve that falls to 0 near z = 0.12. Bottom: the purple curve k(z), increasing from about −0.075 at z = 0 through 0 near z = 0.076 to about 0.55 at z = 1.](figures/appendix-i/side-profile.svg)

*Figure I.7.* Lemma I.6. Top: the least value of
$\beta_{\mathrm{side}}(A, B; -z)$ over the admissible states with side label
(blue), with the small turns magnified. It tends to 0 as $z \to 0$, at the side
state $(1, \frac12)$, where the contact of Proposition I.7 sits. Bottom: the
rate $k(z)$, which changes sign before $z = \frac1{10}$. The three cases of the
proof, numbered at the top, are cut at $z = \frac1{10}$ and where
$\cos z = \frac35$. In case 1 the bound is $g(z)$, from the disk alone
(orange); it fails for $z$ above about $0.12$. Where $k \ge 0$, the least value
is the value at the transition state (dashed), with which case 2 compares.

*Lean:
[`Seven.sideTarget_negative_pos`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L234),
[`Seven.tangent_force_pos`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L217).*

### Proposition I.7 (target sign negative)

Let $(a, b)$ and $(A, B)$ be admissible states and $s \in \lbrace 1, -1\rbrace$.
Suppose that $s = 1$ or that the label of $(a, b)$ is axial, and that the label
of $(A, B)$ is axial or side. Then on the forward axis, for the signs $(s, -1)$,
$\sigma_1(\frac\pi3) \ge 0$. If $\sigma_1(\frac\pi3) = 0$, then $(a, b)$ is an
axial state and $(A, B) = (1, \frac12)$, so that the two states with these signs
form a contact.

*Proof.* Let $e = s\ell + \ell' - \frac\pi6$. By Lemma I.1,
$\sigma_1 \ge \beta(A, B; e, s\ell)$, and $-\frac{5\pi}{12} \le e \le \frac\pi3$
as $0 \le \ell, \ell' \le \frac\pi4$.

*Axial target.* Lemma I.3 with $\rho = s\ell$ gives $\sigma_1 \ge \beta > 0$.

*Side target.* By (I.3),
$\ell' = \mathrm{side}(A, B) = \frac\pi6 - \frac54(A - 1) - \frac16r(A, B)$,
so $s\ell = e - \ell' + \frac\pi6 = e + \frac54(A - 1) + \frac16r(A, B)$ and
$\frac45s\ell = \frac45e + A - 1 + \frac2{15}r(A, B)$. Substituting,
$\beta(A, B; e, s\ell) = \beta_{\mathrm{side}}(A, B; e)$.

If $e \ge 0$, Lemma I.5 gives
$\sigma_1 \ge \frac{21}{40}e + \frac2{15}r(A, B) \ge 0$. If moreover
$\sigma_1 = 0$, then $e = 0$ and $r(A, B) = 0$. So $(A, B) = (1, \frac12)$ and
$\ell' = \frac\pi6$, hence $s\ell = e - \ell' + \frac\pi6 = 0$, so
$\ell = 0$, $b = 0$, and $(a, b)$ is an axial state. With $t = -1$, the axial
state $(a, b)$ and the side state $(A, B)$ form a contact of kind (3)
([Definition 10.15](10-seven.md#definition-1015-contacts)).

If $e < 0$, let $z = -e > 0$. Since $\ell' > \frac9{25}$ and
$s\ell \ge -\frac\pi4$, we have $e > \frac9{25} - \frac{5\pi}{12} > -1$, as
$\frac{5\pi}{12} < \frac43 < 1 + \frac9{25}$. So $z < 1$, and Lemma I.6 gives
$\sigma_1 \ge \beta_{\mathrm{side}}(A, B; -z) > 0$. $\square$

*Lean:
[`Seven.fixed_gap_forward_negative_target`](../../SquaresInCircles/Seven/Pair/Forward/NegativeTarget.lean#L321).*

![Graph over the turn e from −5 pi/12 to pi/3 of the least value, over the admissible targets, of the lower bound of Lemma I.1: for axial targets (blue) and for side targets (dashed green, from e = 9/25 − 5 pi/12 on). For negative turns both decrease towards e = 0, and between about −0.66 and −0.08 they coincide; for positive turns both rise steeply, the side curve above the dotted line 21e/40. An inset magnifies the neighbourhood of e = 0: the blue curve stays at least 0.0077, while the green one touches 0 at e = 0, the contact.](figures/appendix-i/negative-target.svg)

*Figure I.8.* Proposition I.7: the least value of $\beta(A, B; e, s\ell)$ over the
admissible targets, as a function of the turn $e$, for axial targets (blue,
Lemmas I.2 and I.3) and side targets (dashed green, Lemmas I.5 and I.6; their
turns exceed $\frac9{25} - \frac{5\pi}{12}$). For
$-0.66 \le e \le -0.08$ both are attained at the transition state, which has
both labels. The side curve lies above $\frac{21}{40}e$ (dotted) for $e \ge 0$
and vanishes only at $e = 0$, at the side state $(1, \frac12)$, where the axial
source and the side target form a contact (inset); the axial curve is at least
$2 + \frac{2\pi}{15} - X_0 - Y_0 \approx 0.0077$.

## I.3 Opposite signs

In this section $s = -1$ and $t = 1$, and the turn is
$w = \ell + \ell' - \frac\pi3$. The frame of $T$ is turned against that of $S$
by the relative phase $d = \frac\pi3 - \ell - \ell' = -w$, so $w = 0$ when the
sides of $T$ are parallel to those of $S$, as for the two squares of a side
column (Figure I.1, middle). Lemma I.8 writes $\sigma_1$ in the turn;
Proposition I.10 treats two side labels with Cauchy–Schwarz on the disk
(Lemma I.9), Lemmas I.11 to I.15 the other labels, and Proposition I.16 puts
them together.

### Lemma I.8 (the support sum for opposite signs)

Let $(a, b)$ and $(A, B)$ be admissible, and $w = \ell + \ell' - \frac\pi3$.
Then $-\frac\pi3 \le w \le \frac\pi6$, and on the forward axis, for the signs
$(-1, 1)$,

```math
\sigma_1\left(\tfrac\pi3\right) = F(b, A, B; w), \qquad
F(b, A, B; w) = \tfrac12 - b + A\sin w - B\cos w + \tfrac12\left(\lvert\sin w\rvert + \cos w\right) .
```

*Proof.* The range of $w$ holds as $0 \le \ell, \ell' \le \frac\pi4$. By (I.1)
with $s = -1$ and $t = 1$ the direction is
$\frac{7\pi}6 + \ell + \ell' = \frac{3\pi}2 + w$, and

```math
h\left(A, B, \tfrac{3\pi}2 + w\right) = A\sin w - B\cos w + \tfrac12\left(\lvert\sin w\rvert + \lvert\cos w\rvert\right),
```

where $\cos w \ge 0$ as $\lvert w\rvert \le \frac\pi3$. $\square$

*Lean:
[`Seven.sideSideSupport`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L17),
[`Seven.forward_turn_range`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L21),
[`Seven.pairSupport_forward_opposite`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L28).*

### Lemma I.9 (the side margin)

For $-\frac\pi3 \le w \le \frac\pi6$ let

```math
M(w) = \tfrac{19}{20} + \cos w - \min(\sin w, 0) - \tfrac65w .
```

Then $M(w) > 0$, and if $w \ne 0$,

```math
M(w)^2 > \tfrac{13}4\left(\left(\sin w - \tfrac9{10}\right)^2 + \left(\tfrac25 - \cos w\right)^2\right) .
\tag{I.7}
```

At $w = 0$ both sides of (I.7) equal $(\frac{39}{20})^2$ (Figure I.9).

*Proof.* At $w = 0$, $M(0) = \frac{39}{20}$ and
$\frac{13}4(\frac{81}{100} + \frac9{25}) = \frac{13}4\cdot\frac{117}{100} = (\frac{39}{20})^2$.

*The case $0 \le w \le \frac\pi6$.* Here $w < \frac8{15}$, $\sin w \ge 0$ and
$\cos w > 0$, so
$M(w) = \frac{19}{20} + \cos w - \frac65w > \frac{19}{20} - \frac{16}{25} > 0$.

Let $w > 0$. Multiplying the difference of the two sides of (I.7) by 400 and
using $\sin^2 w + \cos^2 w = 1$,

```math
\begin{aligned}
400\left[M^2 - \tfrac{13}4\left(\left(\sin w - \tfrac9{10}\right)^2 + \left(\tfrac25 - \cos w\right)^2\right)\right]
&= (19 + 20\cos w - 24w)^2 - 13(197 - 180\sin w - 80\cos w) \\
&= 400\cos^2 w + (1800 - 960w)\cos w + 2340\sin w + 576w^2 - 912w - 2200 .
\end{aligned}
```

Since $0 \le \sin w \le w$, $\cos^2 w = 1 - \sin^2 w \ge 1 - w^2$. With
$\cos w \ge C_2(w)$, $w\cos w \le wC_4(w)$ and $\sin w \ge S_3(w)$ from (I.2),
the right side is at least

```math
400(1 - w^2) + 1800C_2(w) - 960wC_4(w) + 2340S_3(w) + 576w^2 - 912w - 2200
= w\left(468 - 724w + 90w^2 - 40w^4\right),
```

where $468 - 724w + 90w^2 - 40w^4 = (468 - 724w) + 10w^2(9 - 4w^2) > 0$, as
$0 < w < \frac8{15}$ gives $724w < 400$ and $4w^2 < 9$.

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

a sum of nonnegative terms by (I.2). Finally $z \le \frac\pi3 < \frac32$, so
$160z^2 < 360 < 636$ and $212 + z(636 - 160z^2) > 0$; hence $N(z) > 0$.
$\square$

*Lean:
[`Seven.sideSideL`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L46),
[`Seven.sideSideL_pos`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L49),
[`Seven.sideSide_margin_pos`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L68).*

![Graph over the turn w from −pi/3 to pi/6 of 400 times the margin of Lemma I.9 (blue), falling from about 1040 at −pi/3 to 0 at w = 0, where it has a corner, and rising to about 80 near pi/6, above its two polynomial lower bounds (dashed orange), which also vanish only at w = 0.](figures/appendix-i/side-margin.svg)

*Figure I.9.* Lemma I.9: 400 times
$M(w)^2 - \frac{13}4((\sin w - \frac9{10})^2 + (\frac25 - \cos w)^2)$ (blue) and
its lower bounds $w(468 - 724w + 90w^2 - 40w^4)$ for $w > 0$ and
$z(212 + 636z - 160z^3)$ for $w = -z < 0$ (dashed). The margin vanishes only at
$w = 0$.

### Proposition I.10 (two side labels)

Let $(a, b)$ and $(A, B)$ be admissible with side labels, and
$w = \ell + \ell' - \frac\pi3$. Then $F(b, A, B; w) \ge 0$, with equality only
if $(a, b) = (A, B) = (1, \frac12)$.

*Proof.* As both labels are side,

```math
w = \mathrm{side}(a, b) + \mathrm{side}(A, B) - \tfrac\pi3 = \tfrac13(b + B - 1) + \tfrac34(2 - a - A) .
```

Using this and $\lvert\sin w\rvert = \sin w - 2\min(\sin w, 0)$, expanding shows

```math
F(b, A, B; w) = \tfrac3{10}r(a, b) + U(w), \qquad
U(w) = M(w) + \left(\sin w - \tfrac9{10}\right)\left(A + \tfrac12\right) + \left(\tfrac25 - \cos w\right)\left(B + \tfrac12\right) .
\tag{I.8}
```

By Lemma I.9 and Cauchy–Schwarz on the disk with $p = \sin w - \frac9{10}$,
$q = \frac25 - \cos w$ and $c = M(w)$, $U(w) \ge 0$, and $U(w) > 0$ if
$w \ne 0$. As $r(a, b) \ge 0$, $F \ge 0$. If $F = 0$, then $w = 0$, and

```math
U(0) = \tfrac{39}{20} - \tfrac9{10}\left(A + \tfrac12\right) - \tfrac35\left(B + \tfrac12\right) = \tfrac3{10}r(A, B) ,
```

so $F = \frac3{10}(r(a, b) + r(A, B)) = 0$. Both remainders vanish, and both
states are $(1, \frac12)$ ([Lemma 10.16](10-seven.md#lemma-1016-contacts) (2)). $\square$

*Remark.* At $w = 0$ both terms of (I.8) are multiples of remainders, and
$r = 0$ is the tangent of the circle $\varphi = \frac{13}4$ at the side state.
For $w \ne 0$ the line $U(w) = 0$ in the $(A, B)$-plane misses the disk, by a
margin that vanishes only at $w = 0$ (Figure I.10).

![The (A, B)-plane with the admissible region outlined, its states with side label shaded green, and the dashed circle phi = 13/4; short pieces of the lines U(w) = 0 for w = 0.3, 0.15, 0, −0.15 and −0.3, in five colours named in a legend, each near its point closest to the disk. Only the line for w = 0 touches the circle, at the side state (1, 1/2); the others lie outside the disk.](figures/appendix-i/side-side.svg)

*Figure I.10.* Proposition I.10: the lines $U(w) = 0$ for turns $w$ that two
side labels can have. Each misses the disk $\varphi \le \frac{13}4$, so
$U(w) > 0$ on it, except the line for $w = 0$, the tangent $r(A, B) = 0$ at the
side state.

*Lean:
[`Seven.side_side_property`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L131),
[`Seven.side_side_zero`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L177).*

### Lemma I.11 (bounds in the turn)

1. For $0 \le w \le \frac\pi6$, $\sin w - \frac45w - \frac12(1 - \cos w) \ge 0$.
2. If $A \ge \frac12$, $B \ge 0$ and $0 \le w \le \frac\pi6$, then
   $F(b, A, B; w) \ge 1 - b - B + \sin w - \frac12(1 - \cos w)$.
3. If $(A, B)$ is admissible and $0 \le z \le \frac\pi3$, then
   $F(b, A, B; -z) \ge 1 - b - B - (A - \frac12)\sin z - \frac12(1 - \cos z)$.

*Proof.* (1) By (I.2) the left side is at least
$S_3(w) - \frac45w - \frac14w^2$, which is
$w(\frac15 - \frac w4 - \frac{w^2}6)$, and for
$0 \le w \le \frac\pi6 < \frac8{15}$ the bracket is at least
$\frac15 - \frac2{15} - \frac1{20} > 0$, as
$\frac{w^2}6 < \frac16\left(\frac8{15}\right)^2 < \frac1{20}$.

(2) Here $\sin w \ge 0$, and the difference of the two sides is
$(A - \frac12)\sin w + B(1 - \cos w) \ge 0$.

(3) Here $\lvert\sin(-z)\rvert = \sin z$, and the difference of the two sides is
$B(1 - \cos z) \ge 0$. $\square$

*Lean:
[`Seven.forward_turn_nonneg`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L186),
[`Seven.opposite_support_positive_turn`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L196),
[`Seven.opposite_support_negative_turn`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L208).*

### Lemma I.12 (two axial labels)

1. For $0 \le z \le \frac\pi3$,

   ```math
   1 - \tfrac{4\pi}{15} + \tfrac45z - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) > 0 .
   ```

2. If $(a, b)$ and $(A, B)$ are admissible with axial labels, then
   $F(b, A, B; w) > 0$ for $w = \ell + \ell' - \frac\pi3$.

*Proof.* (1) Let $\kappa = \sqrt3 - 1$, and let $f(z)$ be the left side. For
every real $x$, expanding and using $\cos^2 x + \sin^2 x = 1$,

```math
\left(\kappa\cos x + \tfrac12\sin x\right)^2 + \left(\kappa\sin x - \tfrac12\cos x\right)^2
= \kappa^2 + \tfrac14 = \tfrac{17}4 - 2\sqrt3 < 4.25 - 3.46 = 0.79 < \left(\tfrac9{10}\right)^2 ,
```

so $\kappa\cos x + \frac12\sin x < \frac9{10}$: by Cauchy–Schwarz, as the vector
$(\kappa, \frac12)$ is shorter than $\frac9{10}$. Hence
$g(x) = \frac9{10}x - \kappa\sin x - \frac12(1 - \cos x)$ has $g(0) = 0$ and
$g'(x) = \frac9{10} - \kappa\cos x - \frac12\sin x > 0$, so $g(z) \ge 0$ for
$z \ge 0$ ([Lemma A.1](appendix-a.md#lemma-a1-monotonicity-from-the-derivative) (3)). As
$f(z) = 1 - \frac{4\pi}{15} - \frac z{10} + g(z)$, the slope of $f$ stays above
$-\frac1{10}$, and for $0 \le z \le \frac\pi3$

```math
f(z) \ge 1 - \tfrac{4\pi}{15} - \tfrac z{10} \ge 1 - \tfrac{4\pi}{15} - \tfrac\pi{30} = 1 - \tfrac{3\pi}{10} > 0 ,
```

as $\pi < \frac{10}3$ (Figure I.12).

(2) Both labels are axial, so
$b + B = \frac45(\ell + \ell') = \frac45(\frac\pi3 + w)$. If $w \ge 0$, Lemma
I.11 (2) and (1) give

```math
F \ge 1 - \tfrac45\left(\tfrac\pi3 + w\right) + \sin w - \tfrac12(1 - \cos w) \ge 1 - \tfrac{4\pi}{15} > 0 .
```

If $w < 0$, let $z = -w$; then $0 < z \le \frac\pi3$, and Lemma I.11 (3),
$A - \frac12 \le \sqrt3 - 1$ and $\sin z \ge 0$ give

```math
F \ge 1 - \tfrac45\left(\tfrac\pi3 - z\right) - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) ,
```

which is positive by (1). $\square$

*Lean:
[`Seven.opposite_slope_lt`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L221),
[`Seven.opposite_axial_scalar`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L231),
[`Seven.opposite_axial_axial_pos`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L241).*

### Lemma I.13 (the mixed clearance)

1. Let $(A, B)$ be admissible with side label, and let $(a, b)$ be a state with
   $\ell(a, b) = \mathrm{axial}(b)$. Then, with
   $w = \ell + \ell' - \frac\pi3$, $1 - b - B \ge \frac1{70} - \frac45w$.
2. Let $(A, B)$ be admissible, $0 \le w \le \frac\pi6$ and
   $1 - b - B \ge \frac1{70} - \frac45w$. Then $F(b, A, B; w) > 0$.

*Proof.* (1) We have $\ell = \frac54b$ and $\ell' = \mathrm{side}(A, B)$, that
is, $\ell' = \frac\pi6 + \frac13(B - \frac12) + \frac34(1 - A)$. Expanding
gives

```math
1 - b - B + \tfrac45w = \tfrac{32}{15} - \tfrac{2\pi}{15} - \tfrac35\left(A + \tfrac12\right) - \tfrac{11}{15}\left(B + \tfrac12\right) .
```

As $B \le A$ and $A + B < \frac{31}{20}$ ([Lemma 10.5](10-seven.md#lemma-105-admissible-states) (2)),

```math
\tfrac35\left(A + \tfrac12\right) + \tfrac{11}{15}\left(B + \tfrac12\right) = \tfrac23(A + B + 1) - \tfrac1{15}(A - B) \le \tfrac23(A + B + 1) < \tfrac23\cdot\tfrac{51}{20} = \tfrac{17}{10} .
```

So the right side exceeds
$\frac{32}{15} - \frac{17}{10} - \frac{2\pi}{15} = \frac{13}{30} - \frac{2\pi}{15}$,
which is more than $\frac{13}{30} - \frac{44}{105} = \frac1{70}$. The first
bound is an equality on the diagonal $B = A$, and the second is nearly one at
the diagonal corner, where the clearance is least (Figure I.11).

(2) As $A \ge \frac12$ and $B \ge 0$, Lemma I.11 (2) and (1) give

```math
F \ge 1 - b - B + \sin w - \tfrac12(1 - \cos w) \ge \tfrac1{70} + \Bigl[\sin w - \tfrac45w - \tfrac12(1 - \cos w)\Bigr] \ge \tfrac1{70} . \qquad\square
```

*Lean:
[`Seven.mixed_clearance_bound`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L276),
[`Seven.mixed_positive_turn`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L286).*

![The (A, B)-plane near the states with side label (green), between the tie line, the dashed circle phi = 13/4 and the diagonal B = A, with the grey capped corner. The orange line, where the form 3/5 (A + 1/2) + 11/15 (B + 1/2) equals 17/10, and the dashed purple line A + B = 31/20 both cross the diagonal just beyond the diagonal corner (rd, rd); the green region lies below both.](figures/appendix-i/clearance.svg)

*Figure I.11.* Lemma I.13 (1). On the states with side label (green) the form
$\frac35(A + \frac12) + \frac{11}{15}(B + \frac12)$ stays below $\frac{17}{10}$
(orange line): it is at most $\frac23(A + B + 1)$, with equality on the diagonal
$B = A$, and $A + B < \frac{31}{20}$ (dashed). Both lines cross the diagonal at
$(\frac{31}{40}, \frac{31}{40})$, just beyond the diagonal corner
$(r_d, r_d)$, where the form is largest, $\frac43(r_d + \frac12) \approx 1.6997$.

### Lemma I.14 (an axial source and a side target)

Let $(a, b)$ and $(A, B)$ be admissible, the label of $(a, b)$ axial and that of
$(A, B)$ side. Then $F(b, A, B; w) > 0$ for $w = \ell + \ell' - \frac\pi3$.

*Proof.* By Lemma I.13 (1), $1 - b - B \ge \frac1{70} - \frac45w$. If
$w \ge 0$, Lemma I.13 (2) concludes. Let $w < 0$ and $z = -w$. As
$\ell' > \frac9{25}$ and $\ell \ge 0$,
$z = \frac\pi3 - \ell - \ell' < \frac\pi3 - \frac9{25} < 1.05 - 0.36 < \frac7{10}$.
As the label of $(A, B)$ is side, $A < \frac98$, so $0 \le A - \frac12 < \frac58$.
By Lemma I.11 (3), $0 \le \sin z \le z$ and $1 - \cos z \le \frac{z^2}2$,

```math
F \ge \tfrac1{70} + \tfrac45z - \tfrac58\sin z - \tfrac14z^2 \ge \tfrac1{70} + \tfrac7{40}z - \tfrac14z^2
= \tfrac1{70} + z\left(\tfrac7{40} - \tfrac z4\right) > 0 . \qquad\square
```

*Lean:
[`Seven.opposite_axial_side_pos`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L322).*

### Lemma I.15 (a side source and an axial target)

1. For $\frac25 \le z \le \frac7{10}$,

   ```math
   \Psi(z) = \tfrac12 - \tfrac\pi5 + \tfrac65z - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) > 0 .
   ```

2. If $(a, b)$ and $(A, B)$ are admissible, the label of $(a, b)$ side and that
   of $(A, B)$ axial, then $F(b, A, B; w) > 0$ for
   $w = \ell + \ell' - \frac\pi3$.

*Proof.* (1) On $[\frac25, \frac7{10}]$,

```math
\Psi'(x) = \tfrac65 - (\sqrt3 - 1)\cos x - \tfrac12\sin x \ge \tfrac65 - \tfrac{11}{15} - \tfrac12\cdot\tfrac7{10} = \tfrac7{60} > 0 ,
```

as $\cos x \le 1$, $\sin x \le x$ and $\sqrt3 - 1 < \frac{11}{15}$. So $\Psi$
increases there, and it suffices that $\Psi(\frac25) > 0$. With
$\pi < \frac{22}7$, $\sin\frac25 \le \frac25$ and
$1 - \cos\frac25 \le \frac2{25}$,

```math
\Psi\left(\tfrac25\right) > \tfrac12 - \tfrac{22}{35} + \tfrac{12}{25} - \tfrac{11}{15}\cdot\tfrac25 - \tfrac1{25} > 0.94 - 0.6286 - 0.2934 > 0 .
```

(2) Lemma I.13 (1), applied with the two states exchanged, gives
$1 - b - B \ge \frac1{70} - \frac45w$, since $w$ is symmetric in the two
labels. If $w \ge 0$, Lemma I.13 (2) concludes. Let $w < 0$ and $z = -w$; as
$\ell > \frac9{25}$ and $\ell' \ge 0$, $z < \frac7{10}$ as in Lemma I.14. By
Lemma I.11 (3), $A - \frac12 \le \sqrt3 - 1$ and $\sin z \ge 0$,

```math
F \ge 1 - b - B - (\sqrt3 - 1)\sin z - \tfrac12(1 - \cos z) .
\tag{I.9}
```

If $z \le \frac25$, then with $1 - b - B \ge \frac1{70} + \frac45z$,
$\sqrt3 - 1 < \frac{11}{15}$, $\sin z \le z$ and $1 - \cos z \le \frac{z^2}2$,

```math
F \ge \tfrac1{70} + \tfrac45z - \tfrac{11}{15}z - \tfrac14z^2 = \tfrac1{70} - \tfrac1{75} + \tfrac14\left(\tfrac25 - z\right)\left(z + \tfrac2{15}\right) > 0 .
```

If $z > \frac25$, we use the labels themselves. The side label of $(a, b)$ gives
$b \le \frac12 + \frac65(\ell - \frac\pi6)$, the axial label of $(A, B)$ gives
$B = \frac45\ell'$, and $\ell = \frac\pi3 - z - \ell'$. So

```math
1 - b - B \ge \tfrac12 - \tfrac65\left(\tfrac\pi6 - z - \ell'\right) - \tfrac45\ell' = \tfrac12 - \tfrac\pi5 + \tfrac65z + \tfrac25\ell' \ge \tfrac12 - \tfrac\pi5 + \tfrac65z ,
```

and (I.9) gives $F \ge \Psi(z) > 0$ by (1). $\square$

*Lean:
[`Seven.side_axial_far_profile`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L294),
[`Seven.opposite_side_axial_pos`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L353).*

### Proposition I.16 (opposite signs)

Let $(a, b)$ and $(A, B)$ be admissible states whose labels are axial or side.
Then on the forward axis, for the signs $(-1, 1)$, $\sigma_1(\frac\pi3) \ge 0$.
If $\sigma_1(\frac\pi3) = 0$, then $(a, b) = (A, B) = (1, \frac12)$, and the two
states with these signs form a contact.

*Proof.* By Lemma I.8, $\sigma_1 = F(b, A, B; w)$ with
$w = \ell + \ell' - \frac\pi3$. If both labels are side, Proposition I.10
gives $F \ge 0$, with equality only at two side states, which with the signs
$(-1, 1)$ form a contact of kind (1) ([Definition 10.15](10-seven.md#definition-1015-contacts)). Otherwise
$F > 0$: by Lemma I.12 if both labels are axial, by Lemma I.14 if the label of
$(a, b)$ is axial and that of $(A, B)$ side, and by Lemma I.15 if the label of
$(a, b)$ is side and that of $(A, B)$ axial. $\square$

![Graph over the turn w from −pi/3 to pi/6 of three lower bounds, named in a legend: for two axial labels (blue), between about 0.12 and 0.2, and below it for negative w a dashed blue line falling from 1 − 4pi/15 at w = 0 to about 0.06 at w = −pi/3; for an axial source and a side target (green), two low arches from 1/70 at w = −7/10 to 1/70 at w = 0 and beyond; for a side source and an axial target (dashed pink), falling from about 0.12 at w = −7/10 to about 0.03 at w = −2/5, then rising from nearly 0 at w = −2/5 in a low arch that joins the green curve at w = 0. Vertical lines at w = −7/10 and w = −2/5.](figures/appendix-i/opposite-profiles.svg)

*Figure I.12.* The lower bounds of Lemmas I.12, I.14 and I.15 for
$F(b, A, B; w)$, as functions of the turn $w$. For two axial labels and
$w = -z < 0$ the bound is the left side of Lemma I.12 (1); its slope in $z$
stays above $-\frac1{10}$, so it stays above the line
$1 - \frac{4\pi}{15} - \frac z{10}$ (dashed blue). For mixed labels the turn
exceeds $-\frac7{10}$. The bound for a side source and an axial target is
weakest at $w = -\frac25$, where Lemma I.15 changes its method.

*Lean:
[`Seven.fixed_gap_forward_opposite_active`](../../SquaresInCircles/Seven/Pair/Forward/Opposite.lean#L406).*

## I.4 Both signs negative

In this section $s = t = -1$ and the label of $(a, b)$ is side. The frame of $T$
is turned against that of $S$ by the relative phase
$d = \frac\pi3 - \ell + \ell'$, and no contact occurs: $\sigma_1(\frac\pi3) > 0$
throughout (Figure I.1, right). If $\ell \le \frac25$, a single point of the
marker arc of $T$ suffices (Lemma I.17). For larger $\ell$ we bound the support
of $T$ below over the whole label region of $(A, B)$. Up to a constant it is
the target support $G_d(A, B)$ of §I.1, which is affine along each segment of
constant label; so it is least at an end of the segment, and these ends make up
the boundary curves of Appendix G (Figure I.14): the circle, the tie line and
the diagonal for side labels, and the circle and the tie line for axial labels.
Along the circle the support is concave in the label (Lemma I.20), so there it
suffices to check the ends of that piece (Lemmas I.21 to I.23). Lemmas I.24 and
I.25 treat side and axial targets, and Proposition I.26 puts them together.

### Lemma I.17 (a small source label)

Let $(a, b)$ and $(A, B)$ be admissible, and suppose that the label of $(a, b)$
is side with $\ell \le \frac25$. Then on the forward axis, for the signs
$(-1, -1)$, $\sigma_1(\frac\pi3) > 0$.

*Proof.* By (I.1), $\sigma_1 = \frac12 - b + h(A, -B, z)$ with
$z = \frac{7\pi}6 + \ell - \ell'$. Let $x = -\ell' - \frac12$. Then
$\lvert x - (-1)\ell'\rvert = \frac12$, so by the marker arc
([Lemma 10.11](10-seven.md#lemma-1011-the-support-function) (2)), applied to $(A, B)$ with the sign $-1$,
$h(A, -B, z) \ge \cos(z - x)$. Let $\theta = \frac\pi3 - \ell - \frac12$. Then
$z - x = \frac{7\pi}6 + \ell + \frac12 = 2\pi - (\frac\pi2 + \theta)$, so

```math
\cos(z - x) = \cos\left(\tfrac\pi2 + \theta\right) = -\sin\theta .
```

As $\ell \le \frac25$, $\theta \ge \frac\pi3 - \frac9{10} > 0$, so
$\sin\theta \le \theta$, and
$\sigma_1 \ge \frac12 - b - \theta = 1 - b + \ell - \frac\pi3$. The label of
$(a, b)$ is side, so $b \le \frac12 + \frac65(\ell - \frac\pi6)$, and

```math
\sigma_1 \ge \tfrac12 - \tfrac15\ell - \tfrac{2\pi}{15} \ge \tfrac12 - \tfrac2{25} - \tfrac{2\pi}{15}
= \tfrac{21}{50} - \tfrac{2\pi}{15} > 0 ,
```

as $\pi < 3.15$. $\square$

*Remark.* In the chart of $S$ the argument reads as follows. The marker of $T$
is the direction $d - \ell' = \frac\pi3 - \ell$, and the point $u(\theta)$ of
the unit circle is $\frac12$ behind it, inside the marker arc of $T$, so it lies
in $\overline T$. Its height $\sin\theta$ is below the top $\frac12 - b$ of $S$
(Figure I.13).

![A canonical pair for the signs (−1, −1) in the chart of S: S = Q(a0, −b0) mostly below the horizontal axis and T above it, turned by about 69 degrees; the unit circle about o with the marker arc of T drawn thick inside T, and the point u(theta) at the lower end of the arc, at the angle theta above the horizontal axis. A magnified inset shows that the height sin theta of u(theta) is a little below the top edge of S at height 1/2 − b.](figures/appendix-i/marker-point.svg)

*Figure I.13.* Lemma I.17, for the source $(a_0, b_0)$, whose label $s_0$ is
below $\frac25$, and the target $(1, \frac12)$. The marker arc of $T$ (thick)
lies in $\overline T$, so its point $u(\theta)$, $\frac12$ behind the marker of
$T$, bounds how far $T$ reaches back along $n_1$. Its height $\sin\theta$ is
below the top $\frac12 - b$ of $S$ (inset), so the shadows of $S$ and $T$ on
$n_1$ overlap.

*Lean:
[`Seven.forward_negative_negative_small`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L275).*

For $\ell \ge \frac25$ we follow the segments of constant label (Figure I.14),
and first the circular piece of the upper ends of the side segments.

![The admissible region in the (A, B)-plane divided into segments of constant label: horizontal blue segments where the label is axial, green segments of slope 9/4 where it is side, from the tie line to the circle or the diagonal; the capped part is grey. Orange dots mark one end of each segment: the right end of every axial segment, the end on the tie line for the side segments below a dashed orange segment, and the upper end for those above it. The transition state and the diagonal corner are marked.](figures/appendix-i/segments.svg)

*Figure I.14.* The segments of constant label, along which the target support
$G_d(A, B)$ is affine, for the source label $\ell = 0.55$, so that
$\mathrm{sw}(\ell) \approx 0.655$. The orange dots mark the end where it is
least: the right end of an axial segment, on the circle below $b_0$ and on the
tie line above; the tie state of a side segment with
$\tau \le \mathrm{sw}(\ell)$; and the top of a side segment with
$\tau > \mathrm{sw}(\ell)$, on the circle or, beyond the corner $(r_d, r_d)$, on
the diagonal. The dashed segment has $\tau = \mathrm{sw}(\ell)$.

### Definition I.18 (the target support along the circle)

For real $\ell$ and $s_0 \le \tau \le t_d$, with
$d = \frac\pi3 - \ell + \tau$ and $X$, $Y$, $Z$, $D$ taken at $\tau$, let

```math
\begin{aligned}
H^{\mathrm{circ}}(\ell, \tau) &= -(X - 1)\sin d + Y\cos d, \\
H^{\mathrm{circ}}_1(\ell, \tau) &= \cos d + \left(\tfrac1Z - 1\right)\left(X\cos d + Y\sin d\right), \\
H^{\mathrm{circ}}_2(\ell, \tau) &= -\sin d - \frac{D}{Z^3}\left(X\cos d + Y\sin d\right) - \left(\tfrac1Z - 1\right)^2\left(Y\cos d - X\sin d\right) .
\end{aligned}
```

So $H^{\mathrm{circ}}(\ell, \tau) = G_d(X(\tau) - \frac12, Y(\tau) - \frac12)$
is the value of $G_d$ at the state of the circle with side label $\tau$, which
is the top $(\hat a(\tau), \hat b(\tau))$; hence
$H^{\mathrm{circ}}(\ell, \tau) = H(\ell, \tau)$ for $s_0 \le \tau \le t_d$.

*Lean:
[`Seven.Boundary.sideCircleTarget`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L17),
[`Seven.Boundary.sideCircleTargetD`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L19),
[`Seven.Boundary.sideCircleTargetDD`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L21).*

### Lemma I.19 (derivatives along the circle)

Let $\ell$ be real and $s_0 \le \tau \le t_d$. Then
$H^{\mathrm{circ}}(\ell, \cdot)$ is differentiable at $\tau$ with derivative
$H^{\mathrm{circ}}_1(\ell, \tau)$, and $H^{\mathrm{circ}}_1(\ell, \cdot)$ is
differentiable at $\tau$ with derivative $H^{\mathrm{circ}}_2(\ell, \tau)$.

*Proof.* On $[s_0, t_d]$ we have $Z > 1$, $X' = -Y/Z$, $Y' = X/Z$ and
$Z' = D/Z$ (§I.1), and $d' = 1$. So

```math
\frac{\partial}{\partial\tau}H^{\mathrm{circ}} = \frac YZ\sin d - (X - 1)\cos d + \frac XZ\cos d - Y\sin d
= \cos d + \left(\tfrac1Z - 1\right)\left(X\cos d + Y\sin d\right) .
```

Next, $(\frac1Z)' = -\frac{Z'}{Z^2} = -\frac D{Z^3}$, and

```math
\left(X\cos d + Y\sin d\right)' = -\frac YZ\cos d - X\sin d + \frac XZ\sin d + Y\cos d
= \left(1 - \tfrac1Z\right)\left(Y\cos d - X\sin d\right) .
```

Hence the derivative of $H^{\mathrm{circ}}_1$ is

```math
-\sin d - \frac D{Z^3}\left(X\cos d + Y\sin d\right) + \left(\tfrac1Z - 1\right)\left(1 - \tfrac1Z\right)\left(Y\cos d - X\sin d\right) = H^{\mathrm{circ}}_2(\ell, \tau) . \qquad\square
```

*Lean:
[`Seven.Boundary.sideTarget_derivatives`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L25).*

### Lemma I.20 (concavity along the circle)

Let $\frac25 \le \ell \le \frac\pi4$ and $s_0 \le \tau \le t_d$. Then
$H^{\mathrm{circ}}_2(\ell, \tau) \le 0$.

*Proof.* Let $d = \frac\pi3 - \ell + \tau$. Then $\frac\pi6 < d < \frac\pi2$,
since $d \ge \frac\pi3 - \frac\pi4 + s_0 = \frac\pi{12} + s_0$ with
$s_0 > \frac9{25} > \frac\pi{12}$, and
$d \le \frac\pi3 - \frac25 + \frac\pi4 < \frac\pi2$. So $\cos d \ge 0$, and
$\sin d > \sin\frac\pi6 = \frac12$, as the sine increases on
$[0, \frac\pi2]$.

Since $1 < Z < \frac75$ (§I.1), $-\frac27 < \frac1Z - 1 < 0$ and
$(\frac1Z - 1)^2 < \frac4{49}$. Since $X^2 + Y^2 = \frac{13}4$, Cauchy–Schwarz
gives $\lvert Y\cos d - X\sin d\rvert \le \frac{\sqrt{13}}2 < 2$. Finally
$X, Y > 0$, $D > 0$ and $Z > 0$, so the middle term of $H^{\mathrm{circ}}_2$ is
at most 0. Therefore (Figure I.15)

```math
H^{\mathrm{circ}}_2(\ell, \tau) \le -\sin d + 2\left(\tfrac1Z - 1\right)^2
< -\tfrac12 + \tfrac8{49} < 0 . \qquad\square
```

*Lean:
[`Seven.Boundary.sideTarget_concave_second`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L47).*

![Graph over the side label tau from s0 to td, for the source label pi/4, of three curves: the second derivative of the target support along the circle (blue), rising from about −1.74 to about −1.18; its main term minus sin d (dotted orange), falling from about −0.59 to about −0.87; and the bound of the proof of Lemma I.20 (dashed green), falling from about −0.56 to about −0.71. A dotted line at −0.34 lies above all three.](figures/appendix-i/circle-concave.svg)

*Figure I.15.* Lemma I.20 for the source label $\ell = \frac\pi4$, the
largest, where $d = \frac\pi{12} + \tau$ is smallest: the second derivative
$H^{\mathrm{circ}}_2(\ell, \tau)$ of the target support along the circle
(blue), the bound $-\sin d + 2(\frac1Z - 1)^2$ of the proof (dashed) and its
main term $-\sin d$ (dotted). As $d > \frac\pi6$, $\sin d > \frac12$ and the
bound is below $-\frac12 + \frac8{49} \approx -0.34$ (dotted line); for
smaller $\ell$, $d$ and $\sin d$ are larger.

### Lemma I.21 (the circular piece at the transition state)

For every real $\ell$, $H^{\mathrm{circ}}(\ell, s_0) = C(\ell, s_0)$.

*Proof.* $X(s_0) = a_0 + \frac12$ and $Y(s_0) = Y_0$
([Lemma G.14](appendix-g.md#lemma-g14-the-parametrization) (2)), so
$H^{\mathrm{circ}}(\ell, s_0) = -(a_0 - \frac12)\sin d + Y_0\cos d$ with
$d = \frac\pi3 - \ell + s_0$, which is $C(\ell, s_0)$
([Proposition G.23](appendix-g.md#proposition-g23-the-circular-piece)). $\square$

*Lean:
[`Seven.Boundary.sideTarget_at_transition`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L83).*

### Lemma I.22 (the diagonal piece)

Let $(a, b)$ be admissible with side label $\ell \ge \frac25$, let
$t_d \le \tau \le \frac\pi4$ and $d = \frac\pi3 - \ell + \tau$. Then

```math
\tfrac12 - b - \left(\delta(\tau) - \tfrac12\right)\sin d + \left(\delta(\tau) + \tfrac12\right)\cos d > 0 .
```

*Proof.* Let $d_1 = \frac{7\pi}{12} - \ell$. Then
$\frac\pi4 \le d \le d_1 < \frac\pi2$: first,
$d - \frac\pi4 = \tau - (\ell - \frac\pi{12})$ and
$\ell - \frac\pi{12} \le \frac\pi6 < \frac{18}{25} < t_d \le \tau$; next,
$d \le d_1$ as $\tau \le \frac\pi4$; and $d_1 < \frac\pi2$ as
$\ell \ge \frac25 > \frac\pi{12}$. So $\sin d \ge \cos d \ge 0$. As $\delta$
decreases, $\delta(\tau) \le \delta(t_d) = r_d < \frac{31}{40}$. Hence

```math
\begin{aligned}
-\left(\delta(\tau) - \tfrac12\right)\sin d + \left(\delta(\tau) + \tfrac12\right)\cos d
&= \tfrac12(\sin d + \cos d) - \delta(\tau)(\sin d - \cos d) \\
&\ge \tfrac12(\sin d + \cos d) - \tfrac{31}{40}(\sin d - \cos d)
= \tfrac{51}{40}\cos d - \tfrac{11}{40}\sin d
\ge \tfrac{51}{40}\cos d_1 - \tfrac{11}{40}\sin d_1 ,
\end{aligned}
```

as $\cos$ decreases and $\sin$ increases on $[0, \frac\pi2]$. With
$b \le \frac12 + \frac65(\ell - \frac\pi6)$, the left side of the claim is at
least $K(\ell)$, which is positive by (I.5). $\square$

*Lean:
[`Seven.Boundary.diagonal_target_pos`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L97).*

### Lemma I.23 (the top of a side segment)

Let $(a, b)$ be admissible with side label $\ell \ge \frac25$, and let
$s_0 \le \tau \le \frac\pi4$. Then $\frac12 - b + H(\ell, \tau) > 0$.

*Proof.* *The case $\tau > t_d$.* Then the top is
$(\hat a(\tau), \hat b(\tau)) = (\delta(\tau), \delta(\tau))$, and the claim is
Lemma I.22.

*The case $\tau \le t_d$.* Then
$H(\ell, \tau) = H^{\mathrm{circ}}(\ell, \tau)$. Let
$f(x) = \frac12 - b + H^{\mathrm{circ}}(\ell, x)$ for $s_0 \le x \le t_d$. By
Lemmas I.19 and I.20 the second derivative of $f$ is at most 0 on
$[s_0, t_d]$. So $f$ is concave, and it is positive on $[s_0, t_d]$ if it is
positive at both ends
([Lemma A.4](appendix-a.md#lemma-a4-positivity-from-concavity); Figure I.16). Both ends are
positive.

- *The left end.* $f(s_0) = \frac12 - b + C(\ell, s_0) > 0$ by Lemma I.21 and
  (I.4).
- *The right end.* $X(t_d) = Y(t_d) = r_d + \frac12$
  ([Lemma G.14](appendix-g.md#lemma-g14-the-parametrization) (2)) and $r_d = \delta(t_d)$, so
  $f(t_d)$ is the left side of Lemma I.22 at $\tau = t_d$, which is positive.

Hence $f(\tau) > 0$, which is the claim. $\square$

![Graph over the target label tau from 0 to pi/4, for the source label 0.5, of one half minus b plus the target support at the end of each segment of label tau where it is least: a blue curve for the states of axial label on the circle, decreasing from about 0.075 at 0 to about 0.024 at s0; beyond s0 a purple curve at the tie states and a green curve at the tops, both starting there, the lower drawn solid: the purple one rising up to the switch label sw(l), where they meet near 0.078, and the green one beyond it, concave and ending near 0.065. A dotted orange line at the level of (I.4) marks the least value, at s0, the transition state.](figures/appendix-i/circle-profile.svg)

*Figure I.16.* Lemmas I.21 to I.25 for the source label $\ell = 0.5$, with
$b = \hat b(0.5) \approx 0.471$, the largest $b$ of a state with side label
$0.5$: $\frac12 - b$ plus the target support at the end of each segment of
label $\tau$ where it is least (Figure I.14). Up to $s_0$ (blue) this is
$C(\ell, \tau)$, at the state of axial label $\tau$ on the circle, which
decreases to $C(\ell, s_0)$. Beyond $s_0$ it is the smaller of $L(\ell, \tau)$
at the tie state (purple) and $H(\ell, \tau)$ at the top (green), drawn solid;
they agree at $\tau = \mathrm{sw}(\ell)$, where $G_d$ is constant along the
segment (I.10). Below $\mathrm{sw}(\ell)$ the tie values stay above (I.4), the
value at the transition state (dotted). The top values start from that value at
$s_0$ and are concave up to $t_d$, just short of $\frac\pi4$; positive at both
ends, they are positive throughout (Lemma I.23). The least value over all
targets is at $s_0$, the transition state.

*Lean:
[`Seven.Boundary.upper_target_pos`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L136).*

### Lemma I.24 (the side segment of the target)

Let $(a, b)$ and $(A, B)$ be admissible, the label of $(a, b)$ side with
$\ell \ge \frac25$ and the label of $(A, B)$ side, and let
$d = \frac\pi3 - \ell + \ell'$. Then $\frac12 - b + G_d(A, B) > 0$.

*Proof.* Let $\tau = \ell'$. Then $s_0 \le \tau \le \frac\pi4$
([Proposition G.16](appendix-g.md#proposition-g16-segments-of-constant-side-label) (1)), so $0 < d < \frac\pi2$ as
in Lemma I.20. By Proposition G.16 (2),
$A = \alpha(\tau) + \frac49(B - \frac45\tau)$ with
$\frac45\tau \le B \le \hat b(\tau)$, and substituting,

```math
G_d(A, B) = L(\ell, \tau) + \left(B - \tfrac45\tau\right)\left(\cos d - \tfrac49\sin d\right) .
\tag{I.10}
```

So along the segment $G_d$ is affine in $B$, smallest at the tie state if
$\cos d - \frac49\sin d \ge 0$ and at the top otherwise.

If $\tau \le \mathrm{sw}(\ell)$, then $d \le \omega$ and
$\cos d - \frac49\sin d \ge 0$. So
$G_d(A, B) \ge L(\ell, \tau) \ge C(\ell, s_0)$
([Proposition G.25](appendix-g.md#proposition-g25-the-straight-piece)), and (I.4) concludes.

If $\tau > \mathrm{sw}(\ell)$, then $d > \omega$ and
$\cos d - \frac49\sin d \le 0$. The top $(\hat a(\tau), \hat b(\tau))$ also
has side label $\tau$ (Proposition G.16 (4)), so (I.10) holds for it too, with
$B = \hat b(\tau)$ and value $H(\ell, \tau)$. Subtracting,

```math
G_d(A, B) - H(\ell, \tau) = \bigl(\hat b(\tau) - B\bigr)\left(\tfrac49\sin d - \cos d\right) \ge 0 ,
```

and Lemma I.23 concludes. $\square$

*Lean:
[`Seven.Boundary.target_side_pos`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L172).*

### Lemma I.25 (the axial segment of the target)

Let $(a, b)$ and $(A, B)$ be admissible, the label of $(a, b)$ side with
$\ell \ge \frac25$ and the label of $(A, B)$ axial, and let
$d = \frac\pi3 - \ell + \ell'$. Then $\frac12 - b + G_d(A, B) > 0$.

*Proof.* Let $\tau = \ell' = \frac54B$, so $0 \le \tau \le \frac\pi4$ and
$\frac\pi{12} \le d < \frac\pi2$. As $\sin d \ge 0$, $G_d$ is nonincreasing in
$A$, and $A \le \chi(B)$ ([Proposition G.15](appendix-g.md#proposition-g15-the-axial-region) (1)).

If $\tau \le s_0$, then $B = \frac45\tau \le b_0$, so $\chi(B) = \gamma(B)$
([Lemma G.12](appendix-g.md#lemma-g12-the-circle-over-the-b-axis) (3)). As
$\gamma(\frac45\tau) + \frac12 = \xi(\tau)$, and as
$C(\ell, \cdot)$ is nonincreasing on $[0, s_0]$
([Proposition G.23](appendix-g.md#proposition-g23-the-circular-piece)),

```math
G_d(A, B) \ge G_d\bigl(\gamma(B), B\bigr) = C(\ell, \tau) \ge C(\ell, s_0) ,
```

and (I.4) concludes.

If $\tau > s_0$, then $b_0 < B \le \frac\pi5 < r_d$, so $\chi(B) = \lambda(B)$
(Lemma G.12 (3)), which is $\alpha(\tau)$ as $B = \frac45\tau$ (§I.1); hence
$G_d(A, B) \ge G_d(\alpha(\tau), \frac45\tau)$. The tie state is admissible
with side label $\tau$ (Proposition G.16 (3)), and Lemma I.24, applied to
$(a, b)$ and the tie state, gives
$\frac12 - b + G_d(\alpha(\tau), \frac45\tau) > 0$. $\square$

*Lean:
[`Seven.Boundary.target_axial_pos`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L222).*

### Proposition I.26 (both signs negative)

Let $(a, b)$ and $(A, B)$ be admissible, the label of $(a, b)$ side and the
label of $(A, B)$ axial or side. Then on the forward axis, for the signs
$(-1, -1)$, $\sigma_1(\frac\pi3) > 0$.

*Proof.* If $\ell \le \frac25$, this is Lemma I.17. Let $\ell \ge \frac25$ and
$d = \frac\pi3 - \ell + \ell'$. Then
$\frac\pi{12} \le d \le \frac{7\pi}{12} - \frac25 < \frac\pi2$, as
$\frac25 \le \ell \le \frac\pi4$ and $0 \le \ell' \le \frac\pi4$; so
$\sin d, \cos d \ge 0$. By (I.1) with $s = t = -1$ the direction is
$\frac{7\pi}6 + \ell - \ell' = \frac{3\pi}2 - d$, and

```math
h\left(A, -B, \tfrac{3\pi}2 - d\right) = -A\sin d + B\cos d + \tfrac12(\sin d + \cos d) .
```

Hence

```math
\sigma_1\left(\tfrac\pi3\right) = \tfrac12 - b + G_d(A, B) ,
```

which is positive by Lemma I.24 if the label of $(A, B)$ is side, and by Lemma
I.25 if it is axial (Figure I.17). $\square$

*Lean:
[`Seven.fixed_gap_forward_both_negative_side`](../../SquaresInCircles/Seven/Pair/Forward/BothNegative.lean#L304).*

![Graph over the source label from s0 to pi/4 of the least forward sum for the signs (−1, −1) over all targets with active labels, for the source at the top of its side segment (blue): it falls from about 0.068 at s0 to about 0.0008 near 0.72, marked by a dot, and rises steeply on the short last stretch after td. A dashed orange line, the bound of Lemma I.17, falls from about 0.008 at s0 to about 0.001 at 2/5, where a vertical line is drawn.](figures/appendix-i/both-negative.svg)

*Figure I.17.* Proposition I.26: the least value of $\sigma_1(\frac\pi3)$ for the
signs $(-1, -1)$ over the admissible targets with active labels, for a source
with side label $\ell$ at the top of its segment, $b = \hat b(\ell)$, where it
is smallest (blue). It is attained at the transition state, so it is the left
side of (I.4); its minimum is about $0.0008$, near $\ell = 0.72$. For
$\ell \le \frac25$ Lemma I.17 gives the cruder bound
$\frac12 - \frac15\ell - \frac{2\pi}{15}$ (dashed), still positive.

Together with the sector $(1, 1)$ of Appendix G, Propositions I.7, I.16 and I.26
give the gap property on the forward axis for all active labels: for the signs
$(1, -1)$ by Proposition I.7; for $(-1, 1)$ by Proposition I.16; and for
$(-1, -1)$ by Proposition I.7 if the label of $(a, b)$ is axial and by
Proposition I.26 if it is side. These are the forward cases of the assembly
([Proposition G.32](appendix-g.md#proposition-g32-active-labels)).
