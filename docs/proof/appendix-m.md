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
interval. In the notation of Lemma J.2, $a\ge6$ and $b-\frac35a\ge-0.53$,
so $b\ge3.07>0$. In the half-angle variable $z=\tan(t/2)$,
$F_{yz}=-2b/(1+z^2)<0$: the position derivative decreases with the tilt.
The circle equations give the signs at the extreme corners of the pose rectangle.
Write $u=-y$, $r=x_1$, $U=x_2$, $Y=y_3$, $v=2-Y$, $w=-x_4$,
$K=-h_1$, $H=-h_2$, $A=s+cu/r$, $p=(2-u)(3-U)/(UY)$ and $L=c+sv/w$.
Then $F_y=2(HpL-KA)$. At $(y,z)=(-0.937,1/20)$, short circle bounds give

```math
KA\ge1.354\cdot0.634>1.444\cdot0.58\cdot1.024\ge HpL.
```

At $(-0.895,81/1000)$ they give the reverse comparison:

```math
KA\le1.39\cdot0.662<1.408\cdot0.635\cdot1.034\le HpL.
```

Decrease in tilt extends the negative sign along the lower position face and the positive
sign along the upper face. The intermediate value theorem and strict increase give exactly
one zero $Y(t)$ inside the pose interval.

The height $h_2$ increases along these roots. Indeed, write $y(z)=Y(2\arctan z)$.
The bounds $6\le F_{yy}\le9$ and $-13\le F_{yz}\le-6$ imply, for $z_0\le z_1$,
$\frac23(z_1-z_0)\le y(z_1)-y(z_0)\le\frac{13}6(z_1-z_0)$, by comparing the position
equations at the two tilts. At fixed tilt the height has position derivative
between $-0.7$ and $0$, and at fixed position it has tilt derivative at least
$1.8$. The mean value theorem, first in position and then in tilt, gives

```math
h_2(q_*,y(z_1),z_1)-h_2(q_*,y(z_0),z_0)
\ge-0.7\bigl(y(z_1)-y(z_0)\bigr)+1.8(z_1-z_0)
\ge\frac{17}{60}(z_1-z_0)\ge0.
```

The stationary pose is already bounded by
$-0.920657\le y_*\le-0.920656$ and $0.061897\le z_*\le0.061898$.
Comparing its position equation with an endpoint root gives

```math
y(1/20)\le y_*-\tfrac23(z_*-1/20)\le-0.928,\qquad
y(81/1000)\ge y_*+\tfrac23(81/1000-z_*)\ge-0.908.
```

Thus the endpoint positions lie in $[-0.937,-0.928]$ and $[-0.908,-0.895]$.
The circle equations give, respectively,
$1.6632\le x_2\le1.6691$, $1.4589\le y_3\le1.4644$ and
$1.6414\le x_2\le1.6502$, $1.4386\le y_3\le1.4471$.
Substitution in $h_2=s(-x_4-1)+c(y_3-2)-1$, with the coarse bounds on $x_4$
and the exact endpoint half-angle frames, gives $-29/20\le h_2\le-7/5$ at both
roots. Monotonicity extends these geometric endpoint bounds to the whole family.

Let $m_1(t) = F(q_*, Y(t), t)$.
As $F_y = 0$ along the graph, $m_1'(t) = F_t$ and
$m_1''(t) = F_{tt} - F_{yt}^2/F_{yy}$, which exceeds $\frac34$ on the local
rectangle (§J.2). At $t_*$, $m_1(t_*) = 0$ and $m_1 \ge 0$ nearby, because
$m_1(t) \ge m(q_*) = 0$ by Proposition J.4; so $m_1'(t_*) = 0$, and Taylor's
formula gives (M.1). The signs required by Lemma J.6 hold on the local
rectangle by the bounds of Lemma J.1 and Proposition 11.4 (3). $\square$

*Lean:
[`Eight.ExactFamily.familyYZ_neg`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L320),
[`Eight.ExactFamily.familyY_antitone_z`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L457),
[`Eight.ExactFamily.Coordinates.lower_corner_position`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L579),
[`Eight.ExactFamily.Coordinates.upper_corner_position`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L625),
[`Eight.ExactFamily.extreme_corner_signs`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L39),
[`Eight.ExactFamily.adaptive_endpoint_signs`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L53),
[`Eight.ExactFamily.tiltBox`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L34),
[`Eight.ExactFamily.adaptive_position_exists`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L61),
[`Eight.ExactFamily.adaptive_chain`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L118),
[`Eight.ExactFamily.adaptive_weightDomain`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L121),
[`Eight.ExactFamily.adaptive_position_stationary`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L124),
[`Eight.ExactFamily.root_position_motion`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L529),
[`Eight.ExactFamily.adaptive_height_monotone`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L79),
[`Eight.ExactFamily.sharpPose_bounds`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L196),
[`Eight.ExactFamily.adaptive_position_from_sharp`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L98),
[`Eight.ExactFamily.Coordinates.lower_tilt_height`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L653),
[`Eight.ExactFamily.Coordinates.upper_tilt_height`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L670),
[`Eight.ExactFamily.adaptive_hTwo_bound`](../../SquaresInCircles/Eight/ExactFamily/AdaptiveBounds.lean#L41),
[`Eight.ExactFamily.adaptive_curvature`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L128).*

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

*Proof.* Lemma J.6 applies by Lemma M.1. Write $r=x_1$, $U=x_2$, $Y=y_3$,
$v=-y_4$, $w=-x_4$, $k_1=-h_1$ and $k_2=-h_2$, and put
$L=c+sv/w$. Since $c+sz=1$ for the half-angle frame,
$L=1+s(v/w-z)$. The coordinate and $h_2$ bounds give
$1.019\le L\le1.04$ and $1.4\le k_2\le1.45$.

Use a subscript $0$ for raw contact weights before normalization. The force balance at E gives
$\delta_0=\epsilon_0L=k_2L/k_1\ge1$. The coordinate bounds also give
$\alpha_0\le\beta_0\le\delta_0$ and $\epsilon_0\le\delta_0$, so every raw contact weight
is at most $\delta_0$. Writing $M$ for the sum of the five raw circle weights and combining the B and D
circle contributions before bounding them gives

```math
\frac{M}{\delta_0}=\frac{1+k_1c/r}{2k_2L}+\frac3{2UY}+\frac{s}{2wL}
\ge0.57+0.61+0.02=\frac65.
```

Every normalized contact weight is therefore at most $5/6<4209/5000$.
The three fractions are also at most $0.71$, $0.64$ and $0.05$, so
$M/\delta_0\le7/5$. As $L\le1.04$, this gives $\epsilon=\epsilon_0/M\ge2/3$.
Force balance and the coordinate bounds also give
$0.9\epsilon\le\beta\le0.99\epsilon$ and $\alpha\le0.7\epsilon$.
This uses the existing coordinate and $h_2$ bounds and requires no separate
contact-weight interval checks. $\square$

*Lean:
[`Eight.ExactFamily.Coordinates.WeightBounds`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L214),
[`Eight.ExactFamily.Coordinates.ContactBounds`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L232),
[`Eight.ExactFamily.Coordinates.WeightDomain.contact_bounds`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L286),
[`Eight.ExactFamily.Coordinates.WeightDomain.delta_force_balance`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L240),
[`Eight.ExactFamily.Coordinates.WeightDomain.contact_weight_bound`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L429),
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L123),
[`Eight.ExactFamily.Coordinates.WeightDomain.lam_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L142),
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_sum`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L126),
[`Eight.ExactFamily.Coordinates.force_balance`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L196),
[`Eight.ExactFamily.Coordinates.edgeAlpha`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L717),
[`Eight.ExactFamily.Coordinates.edgeBeta`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L718).*

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
[`Eight.complete_center_square`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L32),
[`Eight.center_square_difference`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L40),
[`Eight.OriginalDual.value_le`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L170),
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
[`Eight.Terminal.automatic_projections`](../../SquaresInCircles/Eight/Rigidity/Estimates.lean#L173),
[`Eight.Terminal.contained_center_bound`](../../SquaresInCircles/Eight/Rigidity/Estimates.lean#L163),
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
centres agree to first order. Write a choice between $x$ and $y$ as
$y + \varepsilon(x-y)$, with $\varepsilon \in \{0,1\}$. Regrouping the
first variation then gives the coefficients of the aligned differences in
one algebraic identity for all owner assignments. The coefficients are explicit
functions of the weights, the chain and the sliders, and for every owner assignment each
$\frac12\lambda_e - |c_e|$ is one of nine expressions. Number them from $0$ to $8$
in the order of `ownerReserve`. Put $E=c(w-1)+sv$. Force balance gives
$\beta J=-\epsilon E$ and $\alpha U=\beta(y+2)$, so five reserves become

```math
R_1=\epsilon E-\alpha(r-1),\quad R_2=\beta Y-\epsilon E,\quad
R_3=\epsilon E-\beta(Y-1),\quad R_4=\epsilon E-0.917\beta,\quad
R_6=\epsilon s v/w.
```

The bounds $0.93\le E\le1$, $0.28\le v/w\le0.296$ and the contact proportions
of Lemma M.2 give $R_j\ge1/80>\rho$ for all five. For the other reserves,
use the force ratio $\beta=\epsilon LV/Y$, where $V=-x_3$:

```math
R_0=\epsilon\left(\frac{LV}{Y}(y+2)-E\right),\qquad
R_5=\epsilon\left(1.057\frac{LV}{Y}-E\right).
```

The last two reserves share the unnormalized cut $N_0$. If $M$ is
the common circle-weight mass, put

```math
N_0=\epsilon_0\bigl(2-c(r+w-2)+s(-y-v)\bigr),\qquad
R_7=\frac{N_0-0.392}{M},\qquad R_8=\frac{0.485-N_0}{M}.
```

The factor in $R_5$ increases along the position roots. To see this, write
$m(q,y,z)=1.057LV/Y-E$. At fixed tilt, circle differentiation gives
$m_y\ge0.91$; at fixed position, the half-angle formulas give $m_z\ge-0.6$.
The lower root-motion bound in Lemma M.1 and the mean value theorem give

```math
m(q_*,y(z_1),z_1)-m(q_*,y(z_0),z_0)
\ge0.91\bigl(y(z_1)-y(z_0)\bigr)-0.6(z_1-z_0)
\ge\frac1{150}(z_1-z_0)\ge0.
```

At the lower tilt $z=1/20$, the frame is $c=399/401$, $s=40/401$.
The coarse circle bounds give $L\ge1.023$, $V/Y\ge0.9088$ and $E\le0.9564$.
Consequently the entire lower-tilt face satisfies

```math
m=1.057LV/Y-E\ge1.057\cdot1.023\cdot0.9088-0.9564\ge1/40.
```

Margin monotonicity extends this to every position root. As $\epsilon\ge2/3$,
$R_5\ge1/60>1/80>\rho$. Also
$R_0-R_5=\beta(y+2-1.057)\ge0$, since $y+2\ge1.063$.
These two reserve identities use the position equation through the E force balance.

It remains to bound $N_0$. Write $u=-y$, $K=-h_1$, $H=-h_2$,
$p=(2-u)V/(UY)$ and $A=s+cu/r$. Since $N_0=(H/K)(K-E)$, differentiation in
position gives

```math
(N_0)_y=pL(1-E/K)+(H/K)p(cv/w-s)-(H/K)AE/K.
```

The coarse circle bounds on the full pose rectangle give
$pL\le0.663$, $1-E/K\le0.34$, $0.96\le H/K\le1.12$,
$cv/w-s\le0.197$, $A\ge0.598$ and $E/K\ge0.65$. Hence

```math
(N_0)_y\le0.663\cdot0.34+1.12\cdot0.637\cdot0.197
             -0.96\cdot0.598\cdot0.65<0.
```

Thus the two extreme positions bound every intermediate position. At fixed position,
put $e=-E$ and $T=K_t$. The angle derivatives satisfy
$K_t=T$, $H_t=e$, $e_t=1-H$ and $T_t=2-K$. Differentiating $N_0$ twice and using
$1.3\le K\le1.5$, $1\le H\le1.5$, $|e|\le1$ and $|T|\le1.1$ gives
$|(N_0)_t|\le10/3$ and $|(N_0)_{tt}|\le15/2$.
The half-angle speed $g=2/(1+z^2)$ satisfies $|g|\le2$, $|g'|\le1/3$, so
$|(N_0)_{zz}|\le32<40$.

At the middle tilt $z_m=131/2000$, the exact frame is
$c=3982839/4017161$, $s=524000/4017161$. The circle bounds used in Lemma M.1
also bound $w$ by $[1.9047,1.905]$ on the left and $[1.8974,1.8976]$ on the right.
They give the following projection bounds; $T=s(r-1)-cy$.

| Position $y$ | $K$ | $H$ | $E$ | $T$ |
| --- | --- | --- | --- | --- |
| $-0.937$ | $[1.3855,1.3858]$ | $[1.4129,1.4135]$ | $[0.9668,0.9672]$ | $[1.0258,1.026]$ |
| $-0.895$ | $[1.3582,1.3586]$ | $[1.4392,1.4396]$ | $[0.9629,0.9632]$ | $[0.987,0.9872]$ |

Positive products and quotients in $N_0=(H/K)(K-E)$ give
$N_0(q,-0.937,z_m)\le0.428$ and $N_0(q,-0.895,z_m)\ge0.418$.
The same bounds give $0.34\le E^2-H(H-1)\le0.36$ on the left and
$0.29\le E^2-H(H-1)\le0.30$ on the right. Substitution in

```math
(N_0)_t=-E+\frac{E^2-H(H-1)}K+\frac{HET}{K^2}
```

gives absolute angle slopes at most $3/40$ and $1/40$, respectively.
The half-angle speed is at most $2$, so the absolute $z$-slopes are at most
$0.15$ at $y=-0.937$ and $0.05$ at $y=-0.895$.
Taylor's inequality with remainder $20(z-z_m)^2$, and $|z-z_m|\le0.0155$, give

```math
N_0(q,-0.895,z)\ge0.418-0.05\cdot0.0155-20\cdot0.0155^2\ge0.412,
```
```math
N_0(q,-0.937,z)\le0.428+0.15\cdot0.0155+20\cdot0.0155^2\le0.44.
```

Position monotonicity extends this to the entire pose rectangle. Along the roots,
$\omega=\epsilon K/H\ge(2/3)\cdot0.9=3/5$. Consequently
$R_7=\omega(N_0-0.392)\ge0.012>\rho$ and
$R_8=\omega(0.485-N_0)\ge0.027>\rho$.
The fifth, sixth, eighth and ninth reserves depend on the slider rectangle,
through the terms $\beta(\frac12 \mp \zeta \mp J)$ and
$\omega(\frac12 \mp \eta) \mp N$ of the cusps of $T$ and $G$. $\square$

*Lean:
[`Eight.ExactFamily.familyRawCut_bounds_of_midpoint`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L607),
[`Eight.ExactFamily.Coordinates.left_midpoint_cut`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L1013),
[`Eight.ExactFamily.Coordinates.right_midpoint_cut`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L1031),
[`Eight.ExactFamily.raw_cut_bound`](../../SquaresInCircles/Eight/ExactFamily/AdaptiveBounds.lean#L27),
[`Eight.ExactFamily.Coordinates.cut_owner_bounds`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L900),
[`Eight.ExactFamily.Coordinates.cut_expansions`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L798),
[`Eight.ExactFamily.Coordinates.cutJ_force_balance`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L771),
[`Eight.ExactFamily.root_position_lower`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L543),
[`Eight.ExactFamily.familyMargin_lower_tilt`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L923),
[`Eight.ExactFamily.adaptive_margin_monotone`](../../SquaresInCircles/Eight/ExactFamily/Adaptive.lean#L88),
[`Eight.ExactFamily.Coordinates.margin_owner_bounds`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L866),
[`Eight.ExactFamily.Coordinates.geometric_owner_bounds`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L813),
[`Eight.ExactFamily.Coordinates.ownerReserve`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L728),
[`Eight.ExactFamily.Coordinates.cut_identities`](../../SquaresInCircles/Eight/ExactFamily/Cuts.lean#L733),
[`Eight.ExactFamily.Perturbation.linear_variation_identity`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L92),
[`Eight.ExactFamily.Perturbation.adaptive_order_bounds`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L156).*

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
$-x_3$, $-h_1$ gives the two constants: put
$c_- = \frac{1-(81/1000)^2}{1+(81/1000)^2}$,
$s_- = \frac{2(1/20)}{1+(1/20)^2}$ and
$s_+ = \frac{2(81/1000)}{1+(81/1000)^2}$. The half-angle formulas give
$\cos t \ge c_-$ and $s_- \le \sin t \le s_+$ throughout the tilt interval.
Thus $K_A \le w\frac{17649}{10000}/c_-$ and
$K_E \le w\frac{19049}{10000}/s_-$; substituting these bounds and
$\epsilon \le w$ into the two remainder coefficients gives the stated rational values.
This calculation uses no separate interval checks of the remainders. Finally,
$C_2\Delta^2 + C_3\Delta^3 < (\frac{232}{25} + \frac3{2000})\Delta^2 < \frac{93}{10}\Delta^2$
for $\Delta \le \frac1{1000}$. $\square$

*Lean:
[`Eight.terminal_constants`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L74),
[`Eight.ExactFamily.Perturbation.remainder_bounds_of_coordinates`](../../SquaresInCircles/Eight/ExactFamily/PerturbationBounds.lean#L45),
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
[`Eight.ExactFamily.Perturbation.quantitative`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L187),
[`Eight.Terminal.boundary_quantitative`](../../SquaresInCircles/Eight/Rigidity/Terminal.lean#L33),
[`Eight.Terminal.boundary_rigid`](../../SquaresInCircles/Eight/Rigidity/Terminal.lean#L49).*

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
[`Eight.Candidate.Dual.ConeBounds`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L424),
[`Eight.Candidate.collapsed_projection`](../../SquaresInCircles/Eight/Candidate/Nominal.lean#L363).*

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
[`Eight.Candidate.Dual.Row.Valid.excludes`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L332),
[`Eight.Candidate.Dual.Row.Valid.excludes_original`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L448).*

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
[`Eight.Candidate.Dual.Alternative`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L128),
[`Eight.Candidate.Dual.TiltBundle`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L412),
[`Eight.Candidate.tilt_weighted_necessary`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L288),
[`Eight.Candidate.tilt_bundle_excludes`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L356),
[`Eight.Candidate.tilt_window`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L403),
[`Eight.Candidate.aligned_second_order_projection`](../../SquaresInCircles/Eight/Candidate/GeometricOwners.lean#L120),
[`Eight.Candidate.mixed_E_second_order`](../../SquaresInCircles/Eight/Candidate/GeometricOwners.lean#L187).*

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
[`Eight.OriginalDual.reference_gap`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L108),
[`Eight.OriginalDual.weighted_gap_difference`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L120),
[`Eight.OriginalDual.reference_value`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L128),
[`Eight.OriginalDual.exact_identity`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L137),
[`Eight.OriginalDual.original_centers_rigid`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L184),
[`Eight.OriginalDual.slider_coordinates`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L230).*
