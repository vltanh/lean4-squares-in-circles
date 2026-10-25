# Appendix J. Eight squares: the stationary system

[Contents](README.md) · [← Appendix I](appendix-i.md) · [Appendix K →](appendix-k.md)

This appendix studies the five-corner chain of
[Chapter 11](11-eight.md) and its stationary system. It proves that the system
has exactly one solution $d_*$, whose squared radius $q_*$ lies in an interval
of width $3 \cdot 10^{-16}$, with rational bounds for all its coordinates
(Proposition J.5), and it constructs the positive weights of the chain
(Lemma J.6), which [Appendix M](appendix-m.md) uses.

Existence and uniqueness are proved separately. For existence (§J.2, §J.3), on a
fixed rectangle of squared radii and poses the defect is strongly convex in the
pose and decreases with the radius at a rate between 3 and 4; so its minimum
over the pose is a continuous, strictly decreasing function of the radius,
positive at one end and negative at the other, and it vanishes exactly once, at
$q_*$. For uniqueness (§J.4), the defect is strictly convex in the position on
the whole domain of its radicals, its Hessian in the position and the tilt has a
positive determinant at every critical point, and its minimum over the
position, as a function of the tilt, has at most one critical point; this
leaves room for one solution only.

## J.1 The chain

Throughout, $z = \tan\frac t2$, $c = \frac{1 - z^2}{1 + z^2} = \cos t$,
$s = \frac{2z}{1 + z^2} = \sin t$, $e = (c, s)$ and $f = (-s, c)$. For a squared
radius $q$, a *position* $y$ and a *tilt* $t$, the *five-corner chain* is

```math
x_1 = \sqrt{q - y^2}, \quad x_2 = \sqrt{q - (y + 2)^2}, \quad x_3 = x_2 - 3, \quad y_3 = \sqrt{q - x_3^2}, \quad y_4 = y_3 - 2, \quad x_4 = -\sqrt{q - y_4^2},
```

```math
h_1 = c\,x_1 + s\,y - 2 - c, \qquad h_2 = -s\,x_4 + c\,y_4 - 1 - s, \qquad F = h_1^2 + h_2^2 - q .
```

Its corners $P_A = (x_1, y)$, $P_B = (x_2, y + 2)$, $P_D = (x_3, y_3)$ and
$P_E = (x_4, y_4)$ lie on the circle of squared radius $q$, and the fifth corner
$P_H = h_1 e + h_2 f$ lies at squared distance $q + F$ from $o$; $F$ is the
*defect*. In the optimal packing they are the lower right corner of $A$, the
upper right corner of $B$, the upper left corner of $D$, the lower left corner
of $E$ and the corner of $H$ that is lower left in its own frame $e$, $f$. The
*stationary system* asks for a chain with

```math
\left(\tfrac{79}{40}\right)^2 \le q \le \tfrac{9789}{2500}, \qquad -1 < y < y_4 < -\tfrac12, \qquad 0 < z < 1, \qquad \tfrac{2z}{1 - z^2} < \tfrac15, \qquad F = F_y = F_t = 0 ,
```

where $F_y$ and $F_t$ are the derivatives of $F$ in $y$ and $t$ (Lemma J.1). Its
unknowns are $(q, y, z, x_1, x_2, y_3, x_4)$: the square roots are replaced by
the four circle equations $x_1^2 + y^2 = q$, $x_2^2 + (y + 2)^2 = q$,
$x_3^2 + y_3^2 = q$, $x_4^2 + y_4^2 = q$ and the signs
$x_1, x_2, y_3 > 0 > x_4$.

*Lean:
[`Eight.Stationary.Coordinates`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L80),
[`Eight.Stationary.Coordinates.IsChain`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L110),
[`Eight.Stationary.Coordinates.defect`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L97),
[`Eight.Stationary.Coordinates.anchorPoints`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L219),
[`Eight.Stationary.Coordinates.anchor_circle`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L237),
[`Eight.Stationary.Coordinates.IsStationary`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L122).*

### Lemma J.1 (derivatives along the chain)

Where the four radicands $q - y^2$, $q - (y + 2)^2$, $q - x_3^2$ and
$q - y_4^2$ are positive, $x_1, \dots, x_4$, $y_3$, $y_4$, $h_1$, $h_2$ and $F$
are smooth functions of $(q, y, t)$. Their derivatives in $y$ are

```math
\frac{\partial x_1}{\partial y} = -\frac y{x_1}, \qquad \frac{\partial x_2}{\partial y} = -\frac{y + 2}{x_2}, \qquad \frac{\partial y_4}{\partial y} = \frac{\partial y_3}{\partial y} = \frac{x_3\,(y + 2)}{y_3\,x_2}, \qquad \frac{\partial x_4}{\partial y} = -\frac{y_4}{x_4}\,\frac{\partial y_4}{\partial y},
```

```math
\frac{\partial h_1}{\partial y} = s - \frac{c\,y}{x_1}, \qquad \frac{\partial h_2}{\partial y} = \left(c + \frac{s\,y_4}{x_4}\right)\frac{\partial y_4}{\partial y},
```

and in $t$, with $\frac{\partial c}{\partial t} = -s$ and
$\frac{\partial s}{\partial t} = c$,

```math
\frac{\partial h_1}{\partial t} = c\,y - s\,(x_1 - 1), \qquad \frac{\partial h_2}{\partial t} = -c\,(x_4 + 1) - s\,y_4, \qquad \frac{\partial^2 h_1}{\partial t^2} = -h_1 - 2, \qquad \frac{\partial^2 h_2}{\partial t^2} = -h_2 - 1 .
```

So
$F_y = \frac{\partial F}{\partial y} = 2h_1\frac{\partial h_1}{\partial y} + 2h_2\frac{\partial h_2}{\partial y}$,
$F_t = \frac{\partial F}{\partial t} = 2h_1\frac{\partial h_1}{\partial t} + 2h_2\frac{\partial h_2}{\partial t}$,
and $F_z = \frac{\partial F}{\partial z} = \frac2{1 + z^2}F_t$.

*Proof.* The square roots of positive smooth functions are smooth. The
derivatives follow from the circle equations,
$2x_1\partial x_1 + 2y = 0$, $2x_2\partial x_2 + 2(y + 2) = 0$,
$2x_3\partial x_2 + 2y_3\partial y_3 = 0$ and
$2x_4\partial x_4 + 2y_4\partial y_4 = 0$, from the formulas for $h_1$ and
$h_2$, and from $\frac{dt}{dz} = \frac2{1 + z^2}$. $\square$

*Lean:
[`Eight.Stationary.Coordinates.IsChain.radicals`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L140),
[`Eight.Stationary.Coordinates.y₄deriv`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L98),
[`Eight.Stationary.Coordinates.h₁deriv`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L100),
[`Eight.Stationary.Coordinates.h₂deriv`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L101),
[`Eight.Stationary.Coordinates.positionDerivative`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L103),
[`Eight.Stationary.Coordinates.tiltDerivative`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L105),
[`Eight.Stationary.radicalCoordinates`](../../SquaresInCircles/Eight/Stationary/System.lean#L1543),
[`Eight.Stationary.familyY_radical`](../../SquaresInCircles/Eight/Stationary/System.lean#L1619),
[`Eight.Stationary.familyZ_radical`](../../SquaresInCircles/Eight/Stationary/System.lean#L1634).*

The second derivatives used below are, with $\partial$ for $\partial/\partial y$,

```math
\tfrac12 F_{yy} = (\partial h_1)^2 + h_1\,\partial^2 h_1 + (\partial h_2)^2 + h_2\,\partial^2 h_2, \qquad \tfrac12 F_{tt} = \left(\tfrac{\partial h_1}{\partial t}\right)^2 + \left(\tfrac{\partial h_2}{\partial t}\right)^2 - h_1(h_1 + 2) - h_2(h_2 + 1),
```

with $\partial^2 h_1 = -c\,q/x_1^3$ and $\partial^2 h_2$ obtained in the same
way; all of them are explicit algebraic expressions in $q$, $y$, $z$ and the
four radicals. In the formal proof, $F$, its three first derivatives and its
second derivatives in $y$ and $z$ are trees of rational constants, sums,
products, powers, reciprocals and square roots in the variables $(q, y, z)$.
Each derivative is the symbolic derivative of the tree before it, an identity
of trees that the kernel checks, and wherever the radicands are positive and
the inverted values are nonzero, the symbolic derivative is the derivative.

*Lean:
[`Eight.Stationary.Formula`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L971),
[`Eight.Stationary.Formula.diff`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1056),
[`Eight.Stationary.Formula.hasDerivAt_partial`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1123),
[`Eight.Stationary.Generated.Fy_diff`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1170),
[`Eight.Stationary.Generated.Fyy_diff`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1172).*

## J.2 Convexity on the local rectangle

Let the *local rectangle* be the set $\mathcal R$ of the points $(q, y, z)$
with

```math
\tfrac{7831}{2000} \le q \le \tfrac{9789}{2500}, \qquad -\tfrac{937}{1000} \le y \le -\tfrac{179}{200}, \qquad \tfrac1{20} \le z \le \tfrac{81}{1000},
```

the *pose rectangle* the set of its poses $(y, z)$, and the *trial pose*
$P_0 = (y_0, z_0)$ with
$y_0 = -\frac{3682626712030424527}{4 \cdot 10^{18}} \approx -0.920657$ and
$z_0 = \frac{618974110076603597}{10^{19}} \approx 0.061897$. Let
$\ell_* = 3.91553413751747512652$ and $u_* = 3.91553413751747542652$.

### Lemma J.2 (bounds on the local rectangle)

On $\mathcal R$, with derivatives in $y$, $z$ and $q$,

1. $F_{yy} \ge 6$ and $(F_{yy} - \frac14)(F_{zz} - \frac14) - F_{yz}^2 \ge 10$;
2. $-4 \le F_q \le -3$;
3. at the trial pose, $|F_y| \le \frac1{5000}$ and $|F_z| \le \frac1{2500}$ for
   every $q$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$, and
   $|F_y|, |F_z| \le 10^{-15}$ for every $q$ in $[\ell_*, u_*]$;
4. at the trial pose, $F \ge \frac1{8000}$ for $q = \frac{7831}{2000}$,
   $F \le -\frac1{5000}$ for $q = \frac{9789}{2500}$, $F \ge 7 \cdot 10^{-16}$
   for $q = \ell_*$ and $F \le -3 \cdot 10^{-16}$ for $q = u_*$.

*Proof.* Each claim bounds an explicit algebraic expression on a box of
rationals, possibly reduced to a point in some coordinates, and is proved by
evaluating the expression once in fixed-point interval arithmetic
([§L.6](appendix-l.md#l6-interval-evaluation)): every number is an integer
multiple of $2^{-p}$, with $p$ between 80 and 200, every operation rounds
outwards, and a square root or a reciprocal is admitted only if the enclosure of
its argument is positive, which also shows that the expression is smooth on the
box. The bounds on $F_{yy}$ and $F_q$ hold on the whole of $\mathcal R$ in one
evaluation; the determinant of (1) lies in $[10, 100]$ on each cell of a
$4 \times 4$ grid of the pose rectangle, and the cells cover $\mathcal R$.
$\square$

*Lean:
[`Eight.Stationary.hessian_data`](../../SquaresInCircles/Eight/Stationary/System.lean#L102),
[`Eight.Stationary.Generated.fullFyy_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1634),
[`Eight.Stationary.Generated.determinant_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1776),
[`Eight.Stationary.Generated.determinant_cover`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1798),
[`Eight.Stationary.family_q_bound`](../../SquaresInCircles/Eight/Stationary/System.lean#L99),
[`Eight.Stationary.trial_gradients`](../../SquaresInCircles/Eight/Stationary/System.lean#L214),
[`Eight.Stationary.Generated.sharpTrialFy_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1944),
[`Eight.Stationary.Generated.sharpTrialFz_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1950),
[`Eight.Stationary.Generated.lowerTest_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1908),
[`Eight.Stationary.Generated.upperTest_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1914),
[`Eight.Stationary.Generated.sharpLowF_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1920),
[`Eight.Stationary.Generated.sharpHighF_bound`](../../SquaresInCircles/Eight/Stationary/Generated/LocalStationaryBounds.lean#L1938).*

### Lemma J.3 (strong convexity)

For every $q$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$ and all poses
$P = (y, z)$ and $P' = (y', z')$ in the pose rectangle,

```math
F(q, P') \ge F(q, P) + F_y(q, P)\,(y' - y) + F_z(q, P)\,(z' - z) + \tfrac18|P' - P|^2 . \tag{J.1}
```

*Proof.* For real $A \ge 6$, $B$, $C$ with
$(A - \frac14)(C - \frac14) > B^2$ and all real $u$, $v$,

```math
\left(A - \tfrac14\right)\left(A u^2 + 2Buv + Cv^2 - \tfrac14(u^2 + v^2)\right) = \left(\left(A - \tfrac14\right)u + Bv\right)^2 + \left(\left(A - \tfrac14\right)\left(C - \tfrac14\right) - B^2\right)v^2 \ge 0 ,
```

so the Hessian of $F(q, \cdot)$ satisfies
$F_{yy}u^2 + 2F_{yz}uv + F_{zz}v^2 \ge \frac14(u^2 + v^2)$ on the pose
rectangle, by Lemma J.2 (1). The pose rectangle is convex, so
$\phi(\lambda) = F(q, P + \lambda(P' - P))$ is defined for
$0 \le \lambda \le 1$, with $\phi'' \ge \frac14|P' - P|^2$. Integrating twice,
$\phi(1) \ge \phi(0) + \phi'(0) + \frac18|P' - P|^2$, which is (J.1). $\square$

*Lean:
[`Eight.Stationary.quadratic_form_bound`](../../SquaresInCircles/Eight/Stationary/System.lean#L113),
[`Eight.Stationary.family_segment_first`](../../SquaresInCircles/Eight/Stationary/System.lean#L143),
[`Eight.Stationary.family_segment_second`](../../SquaresInCircles/Eight/Stationary/System.lean#L153),
[`Eight.Stationary.family_strong_convex`](../../SquaresInCircles/Eight/Stationary/System.lean#L173).*

## J.3 The minimized defect

### Proposition J.4 (the minimized defect)

1. For each $q$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$, $F(q, \cdot)$
   attains its minimum $m(q)$ over the pose rectangle at a pose $P(q)$ within
   $\frac1{100}$ of the trial pose; $P(q)$ is interior, and
   $F_y = F_z = 0$ there.
2. $-4(r - q) \le m(r) - m(q) \le -3(r - q)$ for $q \le r$; so $m$ is
   continuous and strictly decreasing.
3. $m(\frac{7831}{2000}) > 0 > m(\frac{9789}{2500})$ and
   $m(\ell_*) > 0 > m(u_*)$. So there is exactly one $q_*$ in
   $[\frac{7831}{2000}, \frac{9789}{2500}]$ with $m(q_*) = 0$, and
   $\ell_* < q_* < u_*$.

*Proof.* (1) The rectangle is compact and $F$ continuous, so a minimum point
$P$ exists. Apply (J.1) with the trial pose $P_0$ in place of $P$ and $P$ in
place of $P'$: as $F(q, P) \le F(q, P_0)$,

```math
\tfrac18|P - P_0|^2 \le -F_y(q, P_0)\,(y - y_0) - F_z(q, P_0)\,(z - z_0) \le \left(\tfrac1{5000} + \tfrac1{2500}\right)|P - P_0| ,
```

so $|P - P_0| < \frac1{100}$, and $P$ is interior, as the trial pose is more
than $\frac1{100}$ from the sides of the rectangle. At an interior minimum
both partial derivatives vanish.

(2) For a fixed pose, Lemma J.2 (2) and the mean value theorem give
$-4(r - q) \le F(r, P) - F(q, P) \le -3(r - q)$. Apply it at $P(q)$ and at
$P(r)$, with $m(r) \le F(r, P(q))$ and $m(q) \le F(q, P(r))$.

(3) Minimizing the right side of (J.1) at $P = P_0$ over $P'$ gives
$m(q) \ge F(q, P_0) - 2F_y(q, P_0)^2 - 2F_z(q, P_0)^2$, and
$m(q) \le F(q, P_0)$. By Lemma J.2 (3) and (4),

```math
m\left(\tfrac{7831}{2000}\right) \ge \tfrac1{8000} - \tfrac2{5000^2} - \tfrac2{2500^2} = \tfrac{623}{5000000} > 0, \qquad m\left(\tfrac{9789}{2500}\right) \le -\tfrac1{5000},
```

and likewise $m(\ell_*) \ge 7 \cdot 10^{-16} - 4 \cdot 10^{-30} > 0$ and
$m(u_*) \le -3 \cdot 10^{-16}$. As $m$ is continuous and strictly decreasing,
the intermediate value theorem gives one zero $q_*$, between $\ell_*$ and $u_*$.
$\square$

*Lean:
[`Eight.Stationary.minimum_exists`](../../SquaresInCircles/Eight/Stationary/System.lean#L198),
[`Eight.Stationary.minimumValue`](../../SquaresInCircles/Eight/Stationary/System.lean#L205),
[`Eight.Stationary.minimum_interior`](../../SquaresInCircles/Eight/Stationary/System.lean#L227),
[`Eight.Stationary.minimizingPose_stationary`](../../SquaresInCircles/Eight/Stationary/System.lean#L292),
[`Eight.Stationary.family_radius_difference`](../../SquaresInCircles/Eight/Stationary/System.lean#L309),
[`Eight.Stationary.minimum_radius_difference`](../../SquaresInCircles/Eight/Stationary/System.lean#L334),
[`Eight.Stationary.minimum_continuous`](../../SquaresInCircles/Eight/Stationary/System.lean#L345),
[`Eight.Stationary.minimum_trial_lower`](../../SquaresInCircles/Eight/Stationary/System.lean#L360),
[`Eight.Stationary.minimum_endpoint_signs`](../../SquaresInCircles/Eight/Stationary/System.lean#L367),
[`Eight.Stationary.sharp_endpoint_signs`](../../SquaresInCircles/Eight/Stationary/System.lean#L1642),
[`Eight.Stationary.unique_minimum_zero`](../../SquaresInCircles/Eight/Stationary/System.lean#L382),
[`Eight.Stationary.qStar`](../../SquaresInCircles/Eight/Stationary/System.lean#L398),
[`Eight.Stationary.qStar_bracket`](../../SquaresInCircles/Eight/Stationary/System.lean#L1659).*

![The graph of the minimized defect m(q) against q over the radius interval from 7831/2000 to 9789/2500: a decreasing, nearly straight line from about 0.000126 to about -0.000243, crossing zero at q*, between two dashed lines of slopes -3 and -4 through the crossing. Beside it, an enlargement of the shaded bracket from l* to u*, of width 3 times 10 to the minus 16, in which m, computed to 60 digits and drawn in units of 10 to the minus 16, decreases from about 7.4 at l* to about -3.7 at u* and crosses zero at q*](figures/appendix-j/minimum.svg)

*Figure J.1.* The minimized defect $m(q)$ on
$[\frac{7831}{2000}, \frac{9789}{2500}]$ (solid), decreasing with a slope
between $-4$ and $-3$ (dashed lines through the zero); it vanishes at
$q_* \approx 3.9155341375$. Right: the bracket $[\ell_*, u_*]$ of
Proposition J.4 (3), of width $3 \cdot 10^{-16}$ (shaded), with $m$ computed in
60-digit arithmetic, in units of $10^{-16}$.

## J.4 The stationary solution

### Proposition J.5 (the stationary solution)

Let $d_*$ be the chain at $q_*$ and the pose $P(q_*) = (y_*, z_*)$ of
Proposition J.4.

1. $d_*$ solves the stationary system, and it is its only solution.
2. $\frac{7831}{2000} < \ell_* < q_* < u_* < \frac{1957767069}{500000000} < \frac{9789}{2500}$,
   and $|y_* - y_0|, |z_* - z_0| < 10^{-12}$.
3. $-0.92071 < y_* < -0.92059$, and the coordinates of $d_*$ satisfy

   ```math
   \begin{gathered}
   1.75152 \le x_1 \le 1.75159, \quad 1.65843 \le x_2 \le 1.65852, \quad 1.45455 \le y_3 \le 1.45464, \quad -1.90214 \le x_4 \le -1.90211, \\
   0.99231 \le c \le 0.99242, \quad 0.12327 \le s \le 0.12338, \quad -1.36797 \le h_1 \le -1.36748, \quad -1.43022 \le h_2 \le -1.42976 .
   \end{gathered}
   ```

*Proof of existence.* At $(q_*, P(q_*))$, $F = m(q_*) = 0$ and
$F_y = F_z = 0$ by Proposition J.4, hence $F_t = 0$ by Lemma J.1. Interval
evaluation on $\mathcal R$ gives $1.7428 \le x_1$, $1.6414 \le x_2$,
$1.4387 \le y_3 \le 1.4643$ and $x_4 \le -1.8974$, so the radicals have the
required signs, and $y_4 = y_3 - 2$ lies in $(-1, -\frac12)$, above
$y \le -\frac{179}{200}$; the rectangle also gives $-1 < y < -\frac12$,
$0 < z < 1$, $\frac{2z}{1 - z^2} < \frac15$ and
$q_* \ge \frac{7831}{2000} > (\frac{79}{40})^2$.

*Proof of uniqueness.* Write $u = -y$ for the downward position. The chain
becomes $r = \sqrt{q - u^2}$, $U = \sqrt{q - (2 - u)^2}$, $V = 3 - U$,
$Y = \sqrt{q - V^2}$, $v = 2 - Y$, $w = \sqrt{q - v^2}$, so that
$x_1 = r$, $x_2 = U$, $x_3 = -V$, $y_3 = Y$, $y_4 = -v$, $x_4 = -w$, and

```math
k_1 = -h_1 = 2 - c\,(r - 1) + s\,u, \qquad k_2 = -h_2 = 1 + c\,v - s\,(w - 1), \qquad F = k_1^2 + k_2^2 - q .
```

The *radical domain* of $q$ is the set of the $u \ge 0$ at which the four
radicands are nonnegative.

*Step 1: convexity in the position.* Let $q < 4$, $0 < c \le 1$ and
$0 \le s \le 1$. The function $x \mapsto \sqrt{q - x^2}$ is concave, and
decreasing for $x \ge 0$; a chord of the disk of squared radius $q$ lies in the
disk. Following the chain, the radical domain is an interval, $r$ is strictly
concave, $U$ is concave, $V$ is convex, $Y$ is concave, $v$ is convex and $w$ is
concave. So $k_1$ is strictly convex and $k_2$ is convex in $u$; both are
positive, so $F$ is strictly convex in $u$ on the radical domain and has at most
one minimum point there. As $q$ grows, $r$ and $w$ grow and $v$ shrinks, so
$k_1$ and $k_2$ decrease, and for $q_0 < q_1 < 4$

```math
F(q_1, u) < F(q_0, u) - (q_1 - q_0)
```

at every $u$ of the radical domain of $q_0$, which lies in that of $q_1$.

*Step 2: the envelope.* Let $(\frac{79}{40})^2 \le q \le \frac{9789}{2500}$ and
$0 \le t \le \arctan\frac15$. On the window
$\frac{87}{100} \le u \le \frac{11}{10}$ the radicals are positive
($r > \frac{41}{25}$, $U > \frac{1619}{1000}$, $Y > \frac{1411}{1000}$,
$w > \frac{1885}{1000}$), and $\frac12F_u$ is negative at $u = \frac{87}{100}$
and exceeds $\frac c4$ at $u = \frac{11}{10}$, by rational bounds on the
radicals at these two positions. So $F$ has a critical position in the window,
which by Step 1 is its minimum over the whole radical domain. Let $M(q, t)$ be
this minimum, the *envelope*. It is continuous in $t$, and
$M(q_1, t) < M(q_0, t) - (q_1 - q_0)$ for $q_0 < q_1$, by Step 1.

*Step 3: the Hessian at a critical point.* Let
$(\frac{79}{40})^2 \le q \le \frac{9789}{2500}$, $\frac{87}{100} \le u \le 1$
and $0 \le s/c \le \frac15$, and suppose $F_u = F_t = 0$. Then the vectors
$k = (k_1, k_2)$, $k_u$ and $k_t$ satisfy
$\langle k, k_u\rangle = \langle k, k_t\rangle = 0$, so $k_t = \kappa\,k_u$ for
a number $\kappa$, and

```math
F_{uu}F_{tt} - F_{ut}^2 = 4k_1^2\left(A\left(\sigma\kappa^2 - 2\tau\kappa + \nu\right) + \sigma\nu - \tau^2\right), \qquad A = \tfrac{|k_u|^2}{k_1}, \quad \sigma = \tfrac{\langle k, k_{uu}\rangle}{k_1}, \quad \tau = \tfrac{\langle k, k_{ut}\rangle}{k_1}, \quad \nu = \tfrac{\langle k, k_{tt}\rangle}{k_1} .
```

The circle equations bound the radicals on this strip, and these bounds give
$A > \frac{17}{50}$, $\kappa > \frac75$, $0 < \tau < \frac78$,
$\nu > \frac9{100}$, $\kappa\sigma > 3$ and $\sigma > \frac{27}{16}$; then the
bracket exceeds $\frac{237}{20000}$, and the determinant exceeds
$\frac{237}{5000}k_1^2 > 0$. On $1 \le u \le \frac{11}{10}$ the vectors $k_u$
and $k_t$ are never parallel, so the critical position of a critical point in
the window satisfies $u < 1$.

*Step 4: one critical tilt.* For $0 < t < \arctan\frac15$, the minimum point
$u(t)$ of Step 2 is a simple root of $F_u = 0$ ($F_{uu} > 0$, as $k_1$, $k_2$
and their second derivatives in $u$ are positive), so it is a twice
differentiable function of $t$, and $M(t) = F(u(t), t)$ has $M' = F_t$ and
$M'' = F_{tt} - F_{ut}^2/F_{uu}$. At a critical tilt, $(u(t), t)$ is a critical
point of $F$, with $u(t) < 1$, so $M'' = (F_{uu}F_{tt} - F_{ut}^2)/F_{uu} > 0$
by Step 3, and the critical tilt is a strict local minimum. Between two strict
local minima a continuous function has a local maximum, which would be a
critical tilt that is not a strict local minimum; so $M(q, \cdot)$ has at most
one critical tilt on $(0, \arctan\frac15)$, and it is the minimum of
$M(q, \cdot)$ on $[0, \arctan\frac15]$.

*Conclusion.* A solution of the stationary system has the tilt $t = 2\arctan z$,
with $0 < t < \arctan\frac15$ since $\tan t = \frac{2z}{1 - z^2}$, and its
position $u = -y$ is a critical position, so the minimum point of Step 2; hence
$M(q, t) = F = 0$ and $M'(t) = F_t = 0$, and by Step 4 $M(q, \cdot) \ge 0$ on
$[0, \arctan\frac15]$. If two solutions had squared radii $q_0 < q_1$ and tilts
$t_0$, $t_1$, Step 2 would give

```math
0 \le M(q_1, t_0) < M(q_0, t_0) - (q_1 - q_0) = -(q_1 - q_0) < 0 .
```

So two solutions have the same radius, then the same tilt (Step 4), then the
same position (Step 1), and the radicals are determined by $(q, y, z)$.

*Proof of the bounds.* (2) By Lemma J.2 (3) the gradient at the trial pose has
both components at most $10^{-15}$ for $q = q_*$, and (J.1) with $P = P_0$ and
$P' = P(q_*)$ gives
$\frac18|P(q_*) - P_0|^2 \le |\nabla F(q_*, P_0)|\,|P(q_*) - P_0|$, so
$|P(q_*) - P_0| \le 8\sqrt2 \cdot 10^{-15} < 10^{-12}$. (3) follows by
evaluating the radicals of the chain on the box
$[\ell_*, u_*] \times [y_0 - 10^{-12}, y_0 + 10^{-12}] \times [z_0 - 10^{-12}, z_0 + 10^{-12}]$.
$\square$

*Lean:
[`Eight.Stationary.sharpData`](../../SquaresInCircles/Eight/Stationary/System.lean#L1711),
[`Eight.Stationary.sharpData_stationary`](../../SquaresInCircles/Eight/Stationary/System.lean#L1713),
[`Eight.Stationary.radical_local_bounds`](../../SquaresInCircles/Eight/Stationary/System.lean#L1566),
[`Eight.Stationary.FiveCornerGeometry.coordinate_defect`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L409),
[`Eight.Stationary.FiveCornerGeometry.strictConvexOn_defect`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L342),
[`Eight.Stationary.FiveCornerGeometry.minimizer_unique`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L351),
[`Eight.Stationary.FiveCornerGeometry.defect_radius_decrease`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L495),
[`Eight.Stationary.FiveCornerGeometry.window_bounds`](../../SquaresInCircles/Eight/Stationary/System.lean#L779),
[`Eight.Stationary.FiveCornerGeometry.comparison_position_negative`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L757),
[`Eight.Stationary.FiveCornerGeometry.upper_position_positive`](../../SquaresInCircles/Eight/Stationary/System.lean#L872),
[`Eight.Stationary.FiveCornerGeometry.windowMinimizer_geometric`](../../SquaresInCircles/Eight/Stationary/System.lean#L993),
[`Eight.Stationary.FiveCornerGeometry.positionEnvelope`](../../SquaresInCircles/Eight/Stationary/System.lean#L1020),
[`Eight.Stationary.FiveCornerGeometry.positionEnvelope_radius_decrease`](../../SquaresInCircles/Eight/Stationary/System.lean#L1042),
[`Eight.Stationary.FiveCornerGeometry.StripCritical.normalized_hessian_identity`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L1775),
[`Eight.Stationary.FiveCornerGeometry.normalized_determinant_reserve`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L1786),
[`Eight.Stationary.FiveCornerGeometry.StripCritical.hessian_reserve`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L1804),
[`Eight.Stationary.FiveCornerGeometry.window_critical_below_one`](../../SquaresInCircles/Eight/Stationary/System.lean#L1157),
[`Eight.Stationary.FiveCornerGeometry.positionEnvelope_second_derivative`](../../SquaresInCircles/Eight/Stationary/System.lean#L1368),
[`Eight.Stationary.EnvelopeGeometry.critical_unique_of_strict_minimum`](../../SquaresInCircles/Eight/Stationary/System.lean#L584),
[`Eight.Stationary.FiveCornerGeometry.positionEnvelope_critical_unique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1401),
[`Eight.Stationary.FiveCornerGeometry.positionEnvelope_critical_global_minimum`](../../SquaresInCircles/Eight/Stationary/System.lean#L1408),
[`Eight.Stationary.FiveCornerGeometry.stationary_envelope_nonneg`](../../SquaresInCircles/Eight/Stationary/System.lean#L1480),
[`Eight.Stationary.FiveCornerGeometry.stationary_radius_eq`](../../SquaresInCircles/Eight/Stationary/System.lean#L1488),
[`Eight.Stationary.FiveCornerGeometry.stationary_chain_unique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1516),
[`Eight.Stationary.stationary_unique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1748),
[`Eight.Stationary.exact_stationary_existsUnique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1751),
[`Eight.Stationary.qStar_limits`](../../SquaresInCircles/Eight/Stationary/System.lean#L1671),
[`Eight.Stationary.sharpPose_close`](../../SquaresInCircles/Eight/Stationary/System.lean#L1679),
[`Eight.Stationary.sharpBox_mem`](../../SquaresInCircles/Eight/Stationary/System.lean#L1702),
[`Eight.Stationary.sharp_coordinates`](../../SquaresInCircles/Eight/Stationary/System.lean#L1754),
[`Eight.Stationary.sharp_y`](../../SquaresInCircles/Eight/Stationary/System.lean#L1789).*

![Two panels. Left: the envelope M(q, t), the least defect over the position, against the tilt t from 0 to arctan(1/5), for the squared radii q* - 0.012, q* - 0.006 and q*; each curve has one minimum, the curves for smaller radii lie higher, and the curve for q* stays above zero and touches it only at t*, about 0.1236, marked. Right: an enlargement near t*, from 0.109 to 0.139, of the curve for q*, touching zero at t*, and of the dashed curve for q* + 0.00006, whose minimum is about -0.0002, below zero](figures/appendix-j/envelope.svg)

*Figure J.2.* Steps 2 to 4 of the proof of Proposition J.5: the envelope
$M(q, \cdot)$ on $[0, \arctan\frac15]$ for three squared radii (left). Each has
one critical tilt, a minimum; at $q = q_*$ the minimum is $0$, at the tilt
$t_* = 2\arctan z_* \approx 0.1236$ of $d_*$. A larger radius lowers the whole
curve by more than the difference of the radii: already at
$q_* + 0.00006$, still below $\frac{9789}{2500}$, the minimum is negative
(right, enlarged near $t_*$), and the stationary system has no solution with
that radius.

The statement of [Theorem 11.1](11-eight.md#theorem-111-eight-squares) does
not mention the stationary system: it defines the optimal radius as the least
radius of a closed disk about $o$ that holds five corners with the prescribed
spans. Chapter 11 shows that this least radius is $\sqrt{q_*}$, and
[§M.3](appendix-m.md#m3-the-five-corner-problem) that the five corners of a
minimizer are those of $d_*$.

*Lean:
[`Eight.FiveCorner.radius_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L721),
[`Eight.FiveCorner.radius_sq_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L730),
[`Eight.FiveCorner.selected_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L876).*

## J.5 The weights

### Lemma J.6 (the weights of the chain)

Let a point of the chain have $x_1, x_2, y_3, c, s > 0$,
$x_3, x_4, h_1, h_2 < 0$ and $-2 < y < 0$. Put

```math
\begin{gathered}
\mu_A^0 = \frac c{2x_1}, \quad \alpha^0 = s - \frac{c\,y}{x_1}, \quad \mu_B^0 = \frac{\alpha^0}{2(y + 2)}, \quad \beta^0 = \frac{\alpha^0 x_2}{y + 2}, \quad \mu_D^0 = -\frac{\beta^0}{2x_3}, \\
\delta^0 = 2\mu_D^0 y_3, \quad \mu_H^0 = -\frac1{2h_1}, \quad \epsilon^0 = \frac{h_2}{h_1}, \quad \mu_E^0 = -\frac{s\,\epsilon^0}{2x_4},
\end{gathered}
```

$\omega = 1/(\mu_A^0 + \mu_B^0 + \mu_D^0 + \mu_E^0 + \mu_H^0)$, and
$\mu_P = \omega\mu_P^0$, $\lambda_{AB} = \omega\alpha^0$,
$\lambda_{TB} = \lambda_{DT} = \omega\beta^0$, $\lambda_{ED} = \omega\delta^0$,
$\lambda_{HE} = \omega\epsilon^0$ and $\lambda_{GA} = \lambda_{HG} = \omega$.
Then all twelve weights are positive and $\sum_P\mu_P = 1$. If moreover
$F_y = 0$, then, with $e_0 = (1, 0)$ and $f_0 = (0, 1)$,

```math
\begin{aligned}
2\mu_A P_A &= \omega\,e - \lambda_{AB}\,f_0, & 2\mu_B P_B &= \lambda_{TB}\,e_0 + \lambda_{AB}\,f_0, & 2\mu_D P_D &= -\lambda_{DT}\,e_0 + \lambda_{ED}\,f_0, \\
2\mu_E P_E &= \lambda_{HE}\,f - \lambda_{ED}\,f_0, & 2\mu_H P_H &= -\omega\,e - \lambda_{HE}\,f . &&
\end{aligned} \tag{J.2}
```

In particular $\sum_P \mu_P P_P = 0$.

*Proof.* Positivity follows from the signs: $\alpha^0 > 0$ as $y < 0$, and
each other weight is a product or quotient of positive numbers or of two
negative ones. Each component of (J.2) except the second component of the
equation for $E$ is the definition of a weight; for instance the first
component for $A$ reads $2\mu_A x_1 = \omega c$. For the second component for
$E$, write $y_4' = \frac{x_3(y + 2)}{y_3 x_2}$ for the derivative of
Lemma J.1. Then $\delta^0 = -\beta^0 y_3/x_3 = -\alpha^0/y_4'$, and
$2\mu_E^0 y_4 - c\,\epsilon^0 = -\epsilon^0(c + s\,y_4/x_4)$, so by Lemma J.1

```math
2\mu_E^0 y_4 + \delta^0 - c\,\epsilon^0 = -\frac1{y_4'}\left(\frac{\partial h_1}{\partial y} + \frac{h_2}{h_1}\frac{\partial h_2}{\partial y}\right) = -\frac{F_y}{2h_1\,y_4'} = 0 .
```

Adding the five equations of (J.2), the right sides cancel. $\square$

*Lean:
[`Eight.Stationary.Coordinates.WeightDomain`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L429),
[`Eight.Stationary.Coordinates.IsStationary.weightDomain`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L442),
[`Eight.Stationary.Coordinates.mu`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L420),
[`Eight.Stationary.Coordinates.lam`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L425),
[`Eight.Stationary.Coordinates.WeightDomain.mu_pos`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L501),
[`Eight.Stationary.Coordinates.WeightDomain.lam_pos`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L520),
[`Eight.Stationary.Coordinates.WeightDomain.mu_sum`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L504),
[`Eight.Stationary.Coordinates.last_force_residual`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L524),
[`Eight.Stationary.Coordinates.force_balance`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L574),
[`Eight.Stationary.Coordinates.slider_forces_zero`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L585).*

At the solution $d_*$ of the stationary system the weights are approximately
$\mu = (0.2097, 0.2212, 0.2734, 0.0251, 0.2706)$ for $A, B, D, E, H$ and
$\lambda = (0.4774, 0.7336, 0.7336, 0.7954, 0.7740, 0.7403, 0.7403)$ for
$AB, TB, DT, ED, HE, GA, HG$
([Figure M.1](appendix-m.md#m1-the-dual-at-arbitrary-centres)). The
equations (J.2) say that the forces $\lambda_e$ along the seven contacts and
the forces $-2\mu_P P_P$ at the five corners balance at every square: at $T$
the two contacts $TB$ and $DT$ have equal weights and opposite directions, and
at $G$ so do $GA$ and $HG$.
