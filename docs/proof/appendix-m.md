# Appendix M. Eight squares: the sharp terminal

[Contents](README.md) · [← Appendix L](appendix-l.md)

This appendix proves
[Theorem 11.36](11-eight.md#theorem-1136-the-sharp-terminal), the inequality
that gives the radius $q_*$, the circle duals behind the quartic tables of
[Proposition 11.35](11-eight.md#proposition-1135-owners-and-tilt-quartic-tables),
and the identity (11.18) of
[Proposition 11.38](11-eight.md#proposition-1138-the-original-squares-at-the-optimal-radius).
All three rest on one device, a weighted sum of corner constraints and
separations whose weights balance at every square, as in the stresses of
[§9.4](09-six.md#94-stresses).

Throughout, the seven exterior squares carry the roles
$H, G, A, B, T, D, E$ of
[Definition 11.27](11-eight.md#definition-1127-candidate-coordinates), the
frame of $A$ is turned by 0 and that of $G$ by $t$, and the frames of $B$,
$T$, $D$, $E$ and $H$ are turned by $a_B, a_T, a_D, a_E$ and $t + a_H$, up to
quarter turns; the *errors* $a_P$ are small. The five aligned differences
are $-a_B$, $a_T - a_B$, $a_D - a_T$, $a_E - a_D$ and $a_H$, and the mismatch
$\Delta$ is the sum of their absolute values. We write $e_t = (\cos t, \sin t)$,
$f_t = (-\sin t, \cos t)$, $e_0 = (1, 0)$, $f_0 = (0, 1)$ and $R(\phi)$ for the
rotation by $\phi$.

## M.1 The comparison chain at a free tilt

### Lemma M.1 (the comparison chain)

For every tilt $t$ with $\frac1{20} \le \tan\frac t2 \le \frac{81}{1000}$,
which includes $\frac1{10} \le t \le \frac4{25}$, there is exactly one
position $Y(t)$ in $[-\frac{937}{1000}, -\frac{179}{200}]$ with
$F_y(q_*, Y(t), t) = 0$, and

```math
F\left(q_*, Y(t), t\right) \ge \tfrac38(t - t_*)^2 . \tag{M.1}
```

The chain at $(q_*, Y(t), t)$ satisfies the hypotheses of
[Lemma J.6](appendix-j.md#lemma-j6-the-weights-of-the-chain).

*Proof.* By Lemma J.2 (1), $F_y(q_*, \cdot, t)$ increases strictly on the pose
interval; it is negative at the lower end and positive at the upper end, by
interval evaluation at the two ends for a fine grid of tilts, so it has
exactly one zero $Y(t)$, inside the interval. Let $m_1(t) = F(q_*, Y(t), t)$.
As $F_y = 0$ along the graph, $m_1'(t) = F_t$ and
$m_1''(t) = F_{tt} - F_{yt}^2/F_{yy}$, which exceeds $\frac34$ on the local
rectangle (§J.2). At $t_*$, $m_1(t_*) = 0$ and $m_1 \ge 0$ nearby, because
$m_1(t) \ge m(q_*) = 0$ by Proposition J.4; so $m_1'(t_*) = 0$, and Taylor's
formula gives (M.1). The signs required by Lemma J.6 hold on the local
rectangle by the bounds of Lemma J.1 and Proposition 11.4 (3). $\square$

*Lean:
[`Eight.ExactFamily.tiltBox`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L30),
[`Eight.ExactFamily.adaptive_position_exists`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L132),
[`Eight.ExactFamily.adaptive_chain`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L188),
[`Eight.ExactFamily.adaptive_weightDomain`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L191),
[`Eight.ExactFamily.adaptive_position_stationary`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L194),
[`Eight.ExactFamily.adaptive_curvature`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L198).*

The chain at $(q_*, Y(t), t)$ has four corners $P_A, P_B, P_D, P_E$ on the
circle of squared radius $q_*$ and the fifth corner $P_H = h_1 e_t + h_2 f_t$
at squared distance $q_* + F(q_*, Y(t), t)$, outside the circle unless
$t = t_*$. It is a comparison configuration, not a packing.

![The reduced defect F(q*, Y(t), t) against the tilt t over the terminal window from 1/10 to 4/25: a convex curve touching zero at t*, about 0.1236, and rising to about 0.0004 at 1/10 and about 0.0009 at 4/25, with the parabola 3/8 (t - t*)^2 drawn dashed below it](figures/appendix-m/envelope.svg)

*Figure M.1.* Lemma M.1: the defect of the comparison chain at the radius
$q_*$, with its position chosen to make $F_y = 0$, against the tilt (solid),
and the parabola $\frac38(t - t_*)^2$ (dashed) below it.

## M.2 Weights at a free tilt

### Lemma M.2 (weights)

For $t$ as in Lemma M.1, the weights $\mu_P(t)$ ($P = A, B, D, E, H$) and
$\lambda_e(t)$ ($e = AB, TB, DT, ED, HE, GA, HG$) of Lemma J.6 at the chain
$(q_*, Y(t), t)$ are positive, $\sum_P\mu_P = 1$, each $\lambda_e$ is less
than $\frac{4209}{5000}$, and the force identities (J.2) hold with these
corners. Write $\alpha = \lambda_{AB}$, $\beta = \lambda_{TB} = \lambda_{DT}$,
$\delta = \lambda_{ED}$, $\epsilon = \lambda_{HE}$ and
$\omega = \lambda_{GA} = \lambda_{HG}$.

*Proof.* Lemma J.6 applies by Lemma M.1. The bound on the edge weights is
interval evaluation of their formulas on the local rectangle. $\square$

*Lean:
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L120),
[`Eight.ExactFamily.Coordinates.WeightDomain.lam_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L139),
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_sum`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L123),
[`Eight.ExactFamily.Coordinates.force_balance`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L193),
[`Eight.ExactFamily.Coordinates.edgeAlpha`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L209),
[`Eight.ExactFamily.Coordinates.edgeBeta`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L210).*

The weights at $t$ are not those at $t_*$, and this matters: with the weights
frozen at $t_*$ the bound below would be
$q_* + K(\cos(t - t_*) - 1)$ for a constant $K > 0$, which is less than $q_*$
for $t \ne t_*$. Letting the weights follow the tilt replaces this by the
positive defect (M.1).

## M.3 The dual bound and the completed squares

Let seven unit squares be as in Theorem 11.36, with centres $p_P$. For an
anchored square $P$, let $o_P = R(a_P)\,o_P^0$ be the offset from its centre
to the vertex that corresponds to the corner $P_P$ of the chain, where

```math
o_A^0 = \left(\tfrac12, -\tfrac12\right), \quad o_B^0 = \left(\tfrac12, \tfrac12\right), \quad o_D^0 = \left(-\tfrac12, \tfrac12\right), \quad o_E^0 = \left(-\tfrac12, -\tfrac12\right), \quad o_H^0 = -\tfrac12 e_t - \tfrac12 f_t .
```

For each directed edge $i \to j$ of the cycle, let $n_e$ be the unit normal
of its separating axis, from the owner set (11.15), and
$g_e = \langle n_e, p_j - p_i\rangle - w_e \ge 0$ its gap, where $w_e$ is the
sum of the two half-widths along $n_e$. Let

```math
\mathcal D = \sum_{P = A, B, D, E, H}\mu_P\,|p_P + o_P|^2 - \sum_e \lambda_e\,g_e . \tag{M.2}
```

### Lemma M.3 (the dual bound)

1. $\mathcal D \le q$.
2. Let $F_P$ be the coefficient vector of $p_P$ in $-\sum_e\lambda_e g_e$, for
   each of the seven squares. Then

   ```math
   \mathcal D = \sum_{P = A, B, D, E, H}\mu_P\left|p_P + o_P + \frac{F_P}{2\mu_P}\right|^2 + \mathcal L, \qquad \mathcal L = -\sum_{P = A, B, D, E, H}\frac{|F_P|^2}{4\mu_P} + \sum_e\lambda_e w_e - \sum_{P = A, B, D, E, H}\langle F_P, o_P\rangle + \langle F_T, p_T\rangle + \langle F_G, p_G\rangle .
   ```

3. If all the errors vanish, then $F_P = -2\mu_P P_P$ for the anchored
   squares, $F_T = F_G = 0$, and $\mathcal L = q_* + \mu_H\,F(q_*, Y(t), t)$.

*Proof.* (1) The vertex $p_P + o_P$ lies in the disk, so
$|p_P + o_P|^2 \le q$; the weights $\mu_P$ add up to 1 and the $\lambda_e$ and
$g_e$ are nonnegative. (2) For each anchored square,
$\mu|p + o|^2 + \langle F, p\rangle = \mu|p + o + \frac F{2\mu}|^2 - \frac{|F|^2}{4\mu} - \langle F, o\rangle$,
and the remaining terms of $-\sum\lambda_e g_e$ are the constants
$\lambda_e w_e$ and the terms in $p_T$ and $p_G$. (3) With zero errors the
normals are those of the chain, the coefficients are, by (J.2),
$F_A = \alpha f_0 - \omega e_t = -2\mu_A P_A$ and likewise for the others, and
at $T$ and at $G$ the two incident weights are equal and the normals
opposite. At the comparison centres $p_P^0 = P_P - o_P^0$ all gaps vanish and
the completed squares vanish, so $\mathcal L$, which does not depend on the
centres when $F_T = F_G = 0$, equals $\mathcal D$ there, that is
$\sum_P\mu_P|P_P|^2 = q_* + \mu_H F(q_*, Y(t), t)$. $\square$

*Lean:
[`Eight.complete_center_square`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L33),
[`Eight.center_square_difference`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L41),
[`Eight.OriginalDual.value_le`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L158),
[`Eight.ExactFamily.Perturbation.zero_force`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L29),
[`Eight.ExactFamily.Perturbation.zero_offset`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L36),
[`Eight.ExactFamily.Perturbation.zero_gap`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L40),
[`Eight.ExactFamily.Perturbation.adaptive_zero_reduced`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L49).*

With the errors $b, u, v, d$ of the owners of $AB$, $TB$, $DT$ and $ED$, and
$n = R(a_H)e_t$ or $e_t$ as $H$ or $G$ owns $HG$, the coefficients are

```math
\begin{aligned}
F_A &= \alpha R(b)f_0 - \omega e_t, & F_B &= -\alpha R(b)f_0 - \beta R(u)e_0, & F_D &= \beta R(v)e_0 - \delta R(d)f_0, \\
F_E &= \delta R(d)f_0 - \epsilon R(a_H)f_t, & F_H &= \omega n + \epsilon R(a_H)f_t, & F_T &= \beta\left(R(u)e_0 - R(v)e_0\right), \quad F_G = \omega(e_t - n) .
\end{aligned}
```

The completed squares are nonnegative and at zero errors equal
$\mu_P|p_P - p_P^0|^2$: the theorem needs no estimate of how far the actual
centres are from the comparison centres. It remains to bound $\mathcal L$
from below as a function of the errors.

## M.4 The first-order term

### Lemma M.4 (automatic sliders)

Under the hypotheses of Theorem 11.36, the projections
$\zeta = \langle f_0, p_T\rangle$ and
$\eta = \langle f_t, p_G - p_H^0 - e_t\rangle$, where $p_H^0$ is the
comparison centre of $H$, satisfy

```math
\tfrac{557}{1000} < \zeta < \tfrac{1417}{1000}, \qquad -\tfrac{103}{200} < \eta < \tfrac{49}{125} .
```

*Proof.* Every exterior square has $0.55875 < a < 1.415$
([Corollary 11.11](11-eight.md#corollary-1111-exterior-squares)), and every
centre is within $\frac32$ of $o$, since the disk of radius $\frac12$ about it
lies in the disk of radius less than 2. The path $A \to B \to T$ of aligned
edges gives $|a_T| \le \Delta$, and $T$, one quarter turn ahead of $A$, has its
centre at $R(a_T)(\tau_T a_T', a_T')$ with $a_T'$ its first coordinate; so
$|\zeta - a_T'| \le \frac32\Delta$, which gives the first claim. The frame of
$G$ is exactly $t$ and $G$ is a quarter turn behind $A$, so its coordinate
along $f_t$ is $-a_G'$, and $\eta = -a_G' - h_2 - \frac12$; with
$-\frac{29}{20} < h_2 < -\frac75$ on the window of tilts this gives the second.
$\square$

*Lean:
[`Eight.Terminal.automatic_projections`](../../SquaresInCircles/Eight/TerminalEstimates.lean#L437),
[`Eight.Terminal.contained_center_bound`](../../SquaresInCircles/Eight/TerminalEstimates.lean#L423),
[`Eight.Candidate.center_amplitude`](../../SquaresInCircles/Eight/Candidate/Projection.lean#L96).*

### Lemma M.5 (the owner reserves)

Choose the sliders of the comparison configuration as $\zeta$ and $\eta$ of
Lemma M.4. Then for each of the 32 owner assignments allowed by (11.15),

```math
\mathcal L \ge q_* + \mu_H\,F(q_*, Y(t), t) + \rho\,\Delta - \text{(the remainder of Lemma M.6)}, \qquad \rho = \tfrac{56793}{5000000} = 0.0113586 .
```

*Proof.* At zero errors $\mathcal L$ has the value of Lemma M.3 (3). The
first variation of $\mathcal L$ in the five errors, including the cusps of the
half-widths $\frac12|\sin\Delta_e|$, is a sum of terms
$c_e\Delta_e + \frac12\lambda_e|\Delta_e|$ over the aligned differences; the
first variations
of $F_T$ and $F_G$ are parallel to $f_0$ and $f_t$, so with the sliders chosen
as the actual projections their products with the actual and the comparison
centres agree to first order. The coefficients are explicit functions of the
weights, the chain and the sliders, and for every owner assignment each
$\frac12\lambda_e - |c_e|$ is one of nine expressions; on the window of tilts
and the slider rectangle of Lemma M.4 their least values are

```math
0.01869, \quad 0.34656, \quad 0.3112575, \quad 0.3984975, \quad 0.0498319, \quad 0.0113586, \quad 0.021785, \quad 0.0160229, \quad 0.0395605 ,
```

by interval evaluation; the fifth, sixth, eighth and ninth depend on the
slider rectangle, through the terms $\beta(\frac12 \mp \zeta \mp J)$ and
$\omega(\frac12 \mp \eta) \mp N$ of the cusps of $T$ and $G$. The least is
$\rho$. $\square$

*Lean:
[`Eight.ExactFamily.Coordinates.ownerReserve`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L221),
[`Eight.ExactFamily.Coordinates.cut_identities`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L226),
[`Eight.ExactFamily.Perturbation.linear_variation_identity`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L92),
[`Eight.ExactFamily.Perturbation.adaptive_order_bounds`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L153).*

## M.5 The remainder

### Lemma M.6 (second order)

For $\Delta \le \frac1{1000}$, the part of $\mathcal L$ beyond its value and
its first-order terms at zero errors is at least
$-C_2\Delta^2 - C_3\Delta^3 > -9.3\,\Delta^2$, with

```math
C_2 = \frac{26453303561590200213}{2850910772000000000} < \frac{232}{25}, \qquad C_3 = \frac{5176729803}{3455440000} < \frac32 .
```

*Proof.* The function $\mathcal L$ has three parts.

*The force norms.* Up to constants, $-\sum_P\frac{|F_P|^2}{4\mu_P}$ is

```math
K_A\sin(t - b) - K_B\sin(u - b) + K_D\sin(v - d) + K_E\cos(t + h - d) + K_H\sin h ,
```

the last term only when $G$ owns $HG$, with
$K_A = \frac{\alpha\omega}{2\mu_A} = \frac{\alpha x_1}{\cos t}$,
$K_B = \frac{\alpha\beta}{2\mu_B} = \beta(y + 2)$,
$K_D = \frac{\beta\delta}{2\mu_D} = -\delta x_3$,
$K_E = \frac{\delta\epsilon}{2\mu_E} = -\frac{\delta x_4}{\sin t}$ and
$K_H = \frac{\omega\epsilon}{2\mu_H} = -\epsilon h_1$, all positive by the
force identities. The five errors are differences along a tree, so any two of
them differ by at most $\Delta$; with $|\sin x - x| \le \frac{|x|^3}6$ and
$0 \le 1 - \cos x \le \frac{x^2}2$, the remainder is at least
$-\frac{K_A\sin t + K_E}2\Delta^2 - \frac{K_A + K_B + K_D + K_H}6\Delta^3$.

*Supports and offsets.* For an aligned edge with difference $\Delta_e$, its
contribution to $\sum_e\lambda_e w_e - \sum_P\langle F_P, o_P\rangle$ divided
by $\lambda_e$ is
$c_0 + c_1\cos\Delta_e + c_2\sin\Delta_e + \frac12|\sin\Delta_e|$ with
$c_1 \le 1$ and $|c_2| \le \frac12$; beyond its value and first-order terms
it loses at most $\frac w2\Delta_e^2 + \frac w6|\Delta_e|^3$, with
$w = \frac{4209}{5000}$. For the mixed edge $HE$ the cosines of the support and
of the offsets cancel exactly, leaving $\epsilon(1 + \sin(t + a_H - a_E))$, which
loses at most $\frac{\epsilon\sin t}2\Delta^2 + \frac\epsilon6\Delta^3$; and $GA$
contributes the constant $\omega(\frac12 + \cos t)$.

*Sliders.* $\langle F_T, p_T\rangle = \beta X_T(\cos u - \cos v) + \beta\zeta(\sin u - \sin v)$
with $|X_T| \le \frac32$, which loses at most
$\frac{3\beta}4\Delta^2 + \frac\beta2\Delta^3$ beyond its linear term, and
$\langle F_G, p_G\rangle$ loses at most $\frac{3\omega}4\Delta^2 + \frac\omega4\Delta^3$
when $H$ owns $HG$, and nothing otherwise.

Bounding the coefficients by the rational upper bounds
$\frac{17649}{10000}$, $\frac{19049}{10000}$, $\frac{221}{200}$,
$\frac{6793}{5000}$, $\frac{14263}{10000}$ for $x_1$, $-x_4$, $y + 2$,
$-x_3$, $-h_1$ and by the range of $t$ gives the two constants, and
$C_2\Delta^2 + C_3\Delta^3 < (\frac{232}{25} + \frac3{2000})\Delta^2 < \frac{93}{10}\Delta^2$
for $\Delta \le \frac1{1000}$. $\square$

*Lean:
[`Eight.terminal_constants`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L63),
[`Eight.ExactFamily.Perturbation.force_term_lower`](../../SquaresInCircles/Eight/ExactFamily/PerturbationEstimates.lean#L211),
[`Eight.ExactFamily.Perturbation.support_term_rows`](../../SquaresInCircles/Eight/ExactFamily/PerturbationEstimates.lean#L407),
[`Eight.ExactFamily.Perturbation.aligned_row_remainder`](../../SquaresInCircles/Eight/ExactFamily/PerturbationEstimates.lean#L420),
[`Eight.ExactFamily.Perturbation.two_cosines_difference`](../../SquaresInCircles/Eight/ExactFamily/PerturbationEstimates.lean#L82),
[`Eight.Candidate.width_semiconvex`](../../SquaresInCircles/Eight/Candidate/Projection.lean#L210).*

## M.6 Proof of Theorem 11.36

*Proof of Theorem 11.36.* By Lemmas M.3 to M.6 and (M.1),

```math
q \ge \mathcal D \ge \sum_P\mu_P\left|p_P + o_P + \frac{F_P}{2\mu_P}\right|^2 + q_* + \tfrac38\mu_H(t - t_*)^2 + \rho\Delta - \tfrac{93}{10}\Delta^2 ,
```

and for $\Delta \le \frac1{1000}$,
$\rho\Delta - \frac{93}{10}\Delta^2 \ge (\frac{56793}{5000000} - \frac{93}{10000})\Delta = \frac{10293}{5000000}\Delta$.
This is (11.17). $\square$

*Lean:
[`Eight.ExactFamily.Perturbation.quantitative`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L184),
[`Eight.Terminal.boundary_quantitative`](../../SquaresInCircles/Eight/Terminal.lean#L33),
[`Eight.Terminal.boundary_rigid`](../../SquaresInCircles/Eight/Terminal.lean#L49).*

Equality in (11.17) at $q = q_*$ forces $\Delta = 0$, $t = t_*$ and all five
completed squares to vanish: the frames are those of the model, and at zero
errors the completed squares are the squared displacements of $A$, $B$, $D$,
$E$, $H$ from their places in the model.

## M.7 The circle duals of the quartic tables

The owner and tilt tables of Proposition 11.35 are built from the same
completion of squares, now with all fourteen coordinates of the seven states
as unknowns. Write $x = (a_0, \dots, a_6, b_0, \dots, b_6)$ for the states of
$H, G, A, B, T, D, E$, with signs $\sigma = (+, -, +, -, +, -, -)$ given by
Lemma 11.33 (3) and $\tau_E \le 0$.

### Lemma M.7 (nominal projections)

Let a cycle satisfy the hypotheses of Proposition 11.35 with
$\Delta \le \varepsilon$.

1. Each of the four projections of (11.5), before the threshold is subtracted,
   changes by at most $\frac32|v|$ when its angle changes by $v$, and
   $\tau$ is $\frac12$-Lipschitz with $\tau \ge 1$.
2. So a separation along an axis of an aligned edge implies the *nominal*
   inequality, with the angle $k_i\frac\pi2$ in place of $\varphi_i$,
   $f_i \cdot x \ge 1 - \frac32\varepsilon$, where $f_i \cdot x$ is linear in
   $x$: $b_H + b_G$, $b_A + b_B$, $b_T + b_D$ on the zero edges, and
   $a_T - b_B$ or $a_B - b_T$ on $B \to T$, $a_E - b_D$ or $a_D + b_E$ on
   $D \to E$.
3. On $G \to A$, whose angle is exactly $\frac\pi2 - t$, and on $E \to H$,
   whose angle differs from $\frac\pi2 + t$ by at most $\varepsilon$, a
   separation implies $f_i(t) \cdot x \ge \tau(t)$ and
   $f_i(t) \cdot x \ge \tau(t) - 2\varepsilon$ respectively, with coefficients
   in $\cos t$ and $\sin t$ (Table M.1).
4. The states satisfy the 35 linear inequalities
   $a_i \ge l_i$, $a_i \le u_i$, $b_i \ge r_i^- a_i$, $b_i \le r_i^+ a_i$ and
   $b_i \le \frac9{10}$, with $(l_i, u_i) = (\frac7{12}, \frac{349}{250})$ for
   $G$ and $T$ and $(\frac{447}{800}, \frac{283}{200})$ otherwise, and
   $r^- = (\frac12, \frac1{20}, 0, 0, \frac1{20}, \frac12, 0)$,
   $r^+ = (1, \frac45, 1, 1, \frac45, 1, 1)$.

| axis | $G \to A$ | $E \to H$ |
| :-: | --- | --- |
| 1 | $-b_G + a_A\cos t - b_A\sin t$ | $-b_E + a_H\cos t + b_H\sin t$ |
| 2 | $-a_G\sin t - b_G\cos t + a_A$ | $a_E\sin t - b_E\cos t + a_H$ |
| 3 | $a_G\cos t - b_G\sin t - b_A$ | $a_E\cos t + b_E\sin t - b_H$ |
| 4 | $a_G - a_A\sin t - b_A\cos t$ | $a_E + a_H\sin t - b_H\cos t$ |

*Table M.1.* The nominal projections of the mixed edges.

*Proof.* (1) Changing the angle turns one of the two centres in each
projection, and every centre is within $\frac32$ of $o$; the derivative of
$\tau$ has absolute value at most $\frac12$ on each quadrant. (2) and (3)
follow from (1) and (11.5) with the signs $\sigma$, and
$\varphi_{E \to H} = \frac\pi2 + t - \sum_{i \in I}d_i$. (4) The bounds on $a$
and $b$ are (11.3), strengthened for $G$ and $T$ by (11.9): if $a < \frac7{12}$
then $b \le \frac45 a < \frac12$ and the square would meet the core; and
$(a + \frac12)^2 + (\frac a{20} + \frac12)^2 > Q_0$ at $a = \frac{349}{250}$.
The ratio bounds are (11.9) and the signs. $\square$

*Lean:
[`Eight.Candidate.projection_amplitude`](../../SquaresInCircles/Eight/Candidate/Projection.lean#L125),
[`Eight.Candidate.sinusoid_lipschitz`](../../SquaresInCircles/Eight/Candidate/Projection.lean#L56),
[`Eight.Candidate.width_one_le`](../../SquaresInCircles/Eight/Candidate/Projection.lean#L137),
[`Eight.Candidate.nominal_projection_identity`](../../SquaresInCircles/Eight/Candidate/Nominal.lean#L236),
[`Eight.Candidate.TangentCuts.cones`](../../SquaresInCircles/Eight/Candidate/Nominal.lean#L90),
[`Eight.Candidate.Dual.ConeBounds`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L425),
[`Eight.Candidate.collapsed_projection`](../../SquaresInCircles/Eight/Candidate/Nominal.lean#L362).*

### Lemma M.8 (the circle dual)

Let $f_i \cdot x \ge w_i$ ($i = 0, \dots, 6$) be necessary inequalities as in
Lemma M.7 and $K_j \cdot x \ge v_j$ ($j < 35$) the inequalities of
Lemma M.7 (4). For weights $\lambda_i \ge 0$, $\kappa_j \ge 0$ and
$\mu_i > 0$, put $C = \sum_i\lambda_i f_i + \sum_j\kappa_j K_j$ and
$L = \sum_i\lambda_i w_i + \sum_j\kappa_j v_j + \frac12\sum_r C_r$. Then a
cycle at a level $q$ satisfies

```math
L \le q\sum_{i=0}^6\mu_i + \sum_{i=0}^6\frac{C_{a_i}^2 + C_{b_i}^2}{4\mu_i} .
```

*Proof.* Adding the inequalities gives $C \cdot x \ge L - \frac12\sum_r C_r$,
that is
$\sum_i (C_{a_i}, C_{b_i}) \cdot (a_i + \frac12, b_i + \frac12) \ge L$. For
each $i$, $\langle C_i, y\rangle \le \mu_i|y|^2 + \frac{|C_i|^2}{4\mu_i}$ for
every vector $y$, and $|(a_i + \frac12, b_i + \frac12)|^2 \le q$ by
[Lemma 3.4](03-tools.md#lemma-34-farthest-vertex). $\square$

*Lean:
[`Eight.Candidate.Dual.circle_linear_upper`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L38),
[`Eight.Candidate.Dual.circle_dual_necessary`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L53),
[`Eight.Candidate.Dual.Row.Valid.excludes`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L333),
[`Eight.Candidate.Dual.Row.Valid.excludes_original`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L449).*

With $z = \tan\frac t2$ and $D_z = 1 + z^2$, on a closed interval where $z$
has a fixed sign, $\sin t = \frac{2z}{D_z}$, $\cos t = \frac{1 - z^2}{D_z}$
and $|\sin t|$ are rational with numerators of degree at most 2; so
$D_z C$ and $D_z L$ have polynomial entries of degree at most 2, and the
reverse of Lemma M.8, multiplied by $D_z^2$, says that the quartic

```math
P(z) = D_z\,(D_z L) - q\,D_z^2\sum_i\mu_i - \sum_i\frac{(D_z C_{a_i})^2 + (D_z C_{b_i})^2}{4\mu_i}
```

is positive. A row of a quartic table gives an interval $[l, r]$, the weights
(with denominator $10^8$) and five positive lower bounds for the Bernstein
coefficients of $P$ on $[l, r]$, with denominator $10^{12}$; by
[Lemma L.5](appendix-l.md#lemma-l5-bernstein-coefficients) it proves
$P > 0$ on $[l, r]$, so no cycle with $z \in [l, r]$ has the alternative of
the row. The three tables are:

| table | level | $\varepsilon$ | alternatives | quartics | covers |
| --- | :-: | :-: | --- | --: | --- |
| quarter owners | $Q_0$ | $\frac3{200}$ | 48 owner patterns | 1,545 | $[-\frac38, \frac38]$ for each pattern |
| mixed owners | $Q_0$ | $\frac1{1000}$ | 15 owner patterns | 729 | $[-\frac38, \frac38]$ for each pattern |
| tilt | $Q_1$ | $\frac1{1000}$ | 21 error vertices | 1,239 | $[-\frac38, \frac{1001}{20000}] \cup [\frac2{25}, \frac38]$ |

*Table M.2.* The three quartic tables of Proposition 11.35.

For the tilt table the owners are known, and the nominal inequalities are
sharpened to second order. On an aligned edge, Taylor's formula and the bound
$\frac32$ on the second derivative of a projection, with the lower bound
$\tau(k\frac\pi2 + d) \ge 1 + \frac12|d| - (\frac14 + \frac\varepsilon{12})d^2$,
give

```math
f_i^0\cdot x - 1 \ge \tfrac12|d_i| - (f_i'\cdot x)\,d_i - \tfrac{1001}{1000}d_i^2 ,
```

where $f_i'\cdot x$ is the derivative of the projection at the nominal angle,
which depends on the owner of the edge ($a_G$ or $a_H$ on $H \to G$, $a_B$ or
$a_A$ on $A \to B$, $b_B$ or $a_T$ on $B \to T$, $a_D$ or $a_T$ on $T \to D$,
$b_D$ or $a_E$ on $D \to E$). On $E \to H$, the function
$\tau(\varphi) + \frac38\varphi^2$ is convex, since $\tau'' \ge -\frac{\sqrt2}2$
between the cusps and the cusps jump upward, which gives a supporting-line
bound with the loss $\frac98(\sum_{i \in I}d_i)^2$. Fixing one weight vector
$\lambda$ for the whole interval of $z$, the weighted sum is a linear form
$\sum_{i \in I}(c_i d_i - \frac{\lambda_i}2|d_i|)$ in the signed errors plus
terms independent of them, and

```math
\max_{\sum_{i \in I}|d_i| \le \varepsilon} \sum_{i \in I}\left(c_i d_i - \tfrac{\lambda_i}2|d_i|\right) = \varepsilon\max\left(0,\ \max_{i \in I}\left(|c_i| - \tfrac{\lambda_i}2\right)\right),
```

attained at $d = 0$ or at $d_i = \pm\varepsilon$ on a single edge. Only that
edge's owner enters $c_i$, so $1 + 5 \cdot 2 \cdot 2 = 21$ linear alternatives
cover all 32 owner assignments and all errors; each is excluded by a circle
dual. Choosing the weight vector before the alternative is what makes this
finite reduction valid.

*Lean:
[`Eight.Candidate.Dual.weighted_total_error`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L76),
[`Eight.Candidate.Dual.error_vertex_disjunction`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L89),
[`Eight.Candidate.Dual.Alternative`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L129),
[`Eight.Candidate.Dual.TiltBundle`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L413),
[`Eight.Candidate.tilt_weighted_necessary`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L296),
[`Eight.Candidate.tilt_bundle_excludes`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L364),
[`Eight.Candidate.tilt_window`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L412),
[`Eight.Candidate.aligned_second_order_projection`](../../SquaresInCircles/Eight/Candidate/GeometricOwners.lean#L110),
[`Eight.Candidate.mixed_E_second_order`](../../SquaresInCircles/Eight/Candidate/GeometricOwners.lean#L171).*

![The l1 ball of two of the five aligned errors, the shaded diamond |d1| + |d2| at most epsilon, with dotted level lines of the form (c1 d1 - lambda1 |d1|/2) + (c2 d2 - lambda2 |d2|/2) for c = (0.9, -0.3) and lambda/2 = (0.5, 0.5), which bend where they cross the axes; the centre and the four vertices, where all of the error sits on a single edge with either sign, are marked, and the maximum over the ball is at the vertex d1 = epsilon](figures/appendix-m/vertices.svg)

*Figure M.2.* The error alternatives of the tilt table, drawn for two of the
five aligned errors: the maximum of $\sum_i(c_i d_i - \frac{\lambda_i}2|d_i|)$
over $\sum|d_i| \le \varepsilon$ is at the centre or at a vertex
$d_i = \pm\varepsilon$ (dots), here at $d_1 = \varepsilon$; with five edges and
two owners each there are 21 such points.

## M.8 The identity at zero errors

### Lemma M.9 (the pullback identity)

At zero errors, with the frames of the model, let $p_P$ be any centres of
seven unit squares $A, B, D, E, H, T, G$, and let $g_e$ be the gaps on the
seven normals of the model, $f_0$ on $AB$ and $ED$, $e_0$ on $TB$ and $DT$,
$e$ on $GA$ and $HG$ and $f$ on $HE$, with the weights $\mu_P$, $\lambda_e$ of
the stationary solution. Then

```math
\sum_{P = A, B, D, E, H}\mu_P|p_P + o_P^0|^2 - \sum_e\lambda_e\,g_e = q_* + \sum_{P = A, B, D, E, H}\mu_P\left|p_P - p_P^0\right|^2 ,
```

where $p_P^0 = P_P - o_P^0$ are the centres of the model.

*Proof.* Both sides are polynomials of degree 2 in the centres with the same
quadratic part $\sum_P\mu_P|p_P|^2$. By Lemma M.3 (3) the coefficient of
$p_P$ in $-\sum_e\lambda_e g_e$ is $-2\mu_P(p_P^0 + o_P^0)$ for an anchored
square and 0 for $T$ and $G$, so the linear parts are both
$-2\sum_P\mu_P\langle p_P, p_P^0\rangle$. At $p = p^0$ the gaps vanish and
the left side is $\sum_P\mu_P|P_P|^2 = q_*$, as all five corners lie on the
circle at the stationary solution; so the constants agree. $\square$

*Lean:
[`Eight.OriginalDual.reference_gap`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L96),
[`Eight.OriginalDual.weighted_gap_difference`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L108),
[`Eight.OriginalDual.reference_value`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L116),
[`Eight.OriginalDual.exact_identity`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L125),
[`Eight.OriginalDual.original_centers_rigid`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L172),
[`Eight.OriginalDual.slider_coordinates`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L218).*
