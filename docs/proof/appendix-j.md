# Appendix J. Eight squares: the stationary system

[Contents](README.md) · [← Appendix I](appendix-i.md) · [Appendix K →](appendix-k.md)

This appendix proves
[Proposition 11.4](11-eight.md#proposition-114-the-stationary-zero): the
stationary system of Theorem 11.1 has exactly one solution, its first
coordinate $q_*$ lies in an interval of width $3 \cdot 10^{-16}$, and the
defect of the five-corner chain has, for each squared radius near $q_*$, a
unique minimum that decreases with the radius and vanishes at $q_*$. It also
proves Lemma J.6, the positive weights of the chain, which
[Proposition 11.7](11-eight.md#proposition-117-a-box-of-different-packings)
and [Appendix M](appendix-m.md) use.

The argument has two parts. On a fixed rectangle of squared radii and poses,
the defect is strongly convex in the pose and decreases with the radius at a
rate between 3 and 4; so its minimum over the pose is a continuous,
strictly decreasing function of the radius, positive at one end and negative
at the other, and it vanishes exactly once (§J.2, §J.3). Every solution of the
stationary system lies in that rectangle (§J.4), and there a stationary pose
with zero defect is the minimum at its radius, so the solution is unique.
Throughout, $c = \frac{1 - z^2}{1 + z^2}$, $s = \frac{2z}{1 + z^2}$ and
$t = 2\arctan z$, so that $c = \cos t$ and $s = \sin t$, and the chain is that
of [Definition 11.2](11-eight.md#definition-112-the-five-corner-chain).

## J.1 The chain

### Lemma J.1 (derivatives along the chain)

On the *initial box* of the points $(q, y, z)$ with
$(\frac{79}{40})^2 \le q \le \frac{9789}{2500}$, $-1 \le y \le -\frac12$ and
$0 \le z \le \frac1{10}$, the radicals $x_1$, $x_2$, $y_3$ and $-x_4$ of
Definition 11.2 are positive, and $x_1, \dots, x_4$, $y_3$, $y_4$, $h_1$,
$h_2$ and $F$ are smooth functions of $(q, y, z)$. Their derivatives in $y$ are

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

So the expressions $F_y$ and $F_t$ of Theorem 11.1 are
$\frac{\partial F}{\partial y} = 2h_1\frac{\partial h_1}{\partial y} + 2h_2\frac{\partial h_2}{\partial y}$
and $\frac{\partial F}{\partial t} = 2h_1\frac{\partial h_1}{\partial t} + 2h_2\frac{\partial h_2}{\partial t}$,
and $\frac{\partial F}{\partial z} = \frac2{1 + z^2}\frac{\partial F}{\partial t}$.

*Proof.* On the box, $q - y^2 \ge q - 1 > 0$ and
$q - (y + 2)^2 \ge q - \frac94 > 0$; then $x_2 \in (1.2, 1.8)$, so
$x_3 = x_2 - 3 \in (-1.8, -1.2)$ and $q - x_3^2 > 3.9 - 3.24 > 0$; and
$y_3 < \sqrt q < 2$ and $y_3 > \sqrt{3.9 - 3.24} > 0.8$, so
$y_4 = y_3 - 2 \in (-1.2, 0)$ and $q - y_4^2 > 0$. The square roots of
positive smooth functions are smooth. The derivatives follow from the circle
equations: $2x_1\partial x_1 + 2y = 0$, $2x_2\partial x_2 + 2(y + 2) = 0$,
$2x_3\partial x_2 + 2y_3\partial y_3 = 0$ and
$2x_4\partial x_4 + 2y_4\partial y_4 = 0$, and from the formulas for $h_1$
and $h_2$. $\square$

*Lean:
[`Eight.ExactFamily.Coordinates.IsChain.radicals`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L114),
[`Eight.ExactFamily.Coordinates.y₄deriv`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L72),
[`Eight.ExactFamily.Coordinates.h₁deriv`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L74),
[`Eight.ExactFamily.Coordinates.h₂deriv`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L75),
[`Eight.ExactFamily.Coordinates.positionDerivative`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L77),
[`Eight.ExactFamily.Coordinates.tiltDerivative`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L79),
[`Eight.ExactFamily.radicalCoordinates`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L26),
[`Eight.ExactFamily.familyY_radical`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L119),
[`Eight.ExactFamily.familyZ_radical`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L134).*

The second derivatives used below are, with $\partial$ for $\partial/\partial y$,

```math
\tfrac12 F_{yy} = (\partial h_1)^2 + h_1\,\partial^2 h_1 + (\partial h_2)^2 + h_2\,\partial^2 h_2, \qquad \tfrac12 F_{tt} = \left(\tfrac{\partial h_1}{\partial t}\right)^2 + \left(\tfrac{\partial h_2}{\partial t}\right)^2 - h_1(h_1 + 2) - h_2(h_2 + 1),
```

with $\partial^2 h_1 = -c\,q/x_1^3$ and $\partial^2 h_2$ obtained in the same
way; all of them are explicit algebraic expressions in $q$, $y$, $z$ and the
four radicals.

## J.2 Convexity on the local rectangle

Let the *local rectangle* be the set $\mathcal R$ of the points $(q, y, z)$
with

```math
\tfrac{7831}{2000} \le q \le \tfrac{9789}{2500}, \qquad -\tfrac{937}{1000} \le y \le -\tfrac{179}{200}, \qquad \tfrac1{20} \le z \le \tfrac{81}{1000},
```

and the *trial pose* $(y_0, z_0)$ with
$y_0 = -\frac{3682626712030424527}{4 \cdot 10^{18}} \approx -0.920657$ and
$z_0 = \frac{618974110076603597}{10^{19}} \approx 0.061897$.

### Lemma J.2 (bounds on the local rectangle)

On $\mathcal R$, with derivatives in $y$, $z$ and $q$,

1. $F_{yy} \ge 6$ and $(F_{yy} - \frac14)(F_{zz} - \frac14) - F_{yz}^2 > 0$;
2. $-4 \le F_q \le -3$;
3. at the trial pose, $|F_y| \le \frac1{5000}$ and $|F_z| \le \frac1{2500}$ for
   every $q$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$;
4. the minimum $m(q)$ of $F(q, \cdot, \cdot)$ over the pose rectangle
   satisfies $m(\frac{7831}{2000}) > 0 > m(\frac{9789}{2500})$, and
   $m(\ell_*) > 0 > m(u_*)$ for $\ell_* = 3.91553413751747512652$ and
   $u_* = 3.91553413751747542652$.

Each claim is an inequality between explicit algebraic expressions on a box,
and is proved by evaluating them in rational interval arithmetic: every
square root is enclosed by two rationals whose squares bracket the radicand,
and sums, products and quotients by their endpoint bounds. For (1) to (3) the
formal proof encloses each expression once on the whole of $\mathcal R$, by a
fixed list of nested rational enclosures; for (4) the lower bounds come from
Lemma J.3 at the trial pose and the upper bounds from the value of $F$ at a
rational pose. For instance the hand proof finds, on four sub-rectangles of
$\mathcal R$ that cover the graph of the minimum,
$6.723 < F_{yy} < 8.637$ and $-5.327 < F_{yt} < -4.23$ in the variables $y$
and $t$, and $F_{tt} - F_{yt}^2/F_{yy} > \frac34$; and at $q = \frac{7831}{2000}$
and the pose $(-0.9206, 0.0619)$ it finds $F > \frac1{8000}$,
$|F_y| < \frac1{2000}$ and $|F_t| < \frac1{4000}$, which gives

```math
m\left(\tfrac{7831}{2000}\right) > \tfrac1{8000} - \tfrac1{12 \cdot 2000^2} - \tfrac23\left(\tfrac1{4000} + \tfrac1{2000}\right)^2 = \tfrac{5981}{48000000} > 0 .
```

*Lean:
[`Eight.ExactFamily.hessian_data`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L80),
[`Eight.ExactFamily.family_q_bound`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L77),
[`Eight.ExactFamily.trial_gradients`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L192),
[`Eight.ExactFamily.minimum_endpoint_signs`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L345),
[`Eight.ExactFamily.sharp_endpoint_signs`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L142),
[`Eight.ExactFamily.Generated.fullFyy_bound`](../../SquaresInCircles/Eight/ExactFamily/Generated/LocalStationaryBounds.lean#L64),
[`Eight.ExactFamily.Generated.fullFq_bound`](../../SquaresInCircles/Eight/ExactFamily/Generated/LocalStationaryBounds.lean#L58).*

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
[`Eight.ExactFamily.quadratic_form_bound`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L91),
[`Eight.ExactFamily.family_segment_first`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L121),
[`Eight.ExactFamily.family_segment_second`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L131),
[`Eight.ExactFamily.family_strong_convex`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L151).*

## J.3 The minimized defect

### Proposition J.4 (the minimized defect)

1. For each $q$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$, $F(q, \cdot)$ has
   exactly one minimum point $P(q)$ in the pose rectangle; it lies within
   $\frac1{100}$ of the trial pose, so in the interior, and it is the only
   pose of the rectangle where $F_y = F_z = 0$.
2. The minimum value $m(q) = F(q, P(q))$ satisfies
   $-4(r - q) \le m(r) - m(q) \le -3(r - q)$ for $q \le r$; so it is
   continuous and strictly decreasing.
3. There is exactly one $q_*$ in $[\frac{7831}{2000}, \frac{9789}{2500}]$ with
   $m(q_*) = 0$, and $\ell_* < q_* < u_*$.

*Proof.* (1) The rectangle is compact and $F$ continuous, so a minimum point
$P$ exists. Apply (J.1) with the trial pose $P_0$ in place of $P$ and $P$ in
place of $P'$: as $F(q, P) \le F(q, P_0)$,

```math
\tfrac18|P - P_0|^2 \le -F_y(q, P_0)\,(y - y_0) - F_z(q, P_0)\,(z - z_0) \le \left(\tfrac1{5000} + \tfrac1{2500}\right)|P - P_0| ,
```

so $|P - P_0| < \frac1{100}$, and $P$ is interior, as the trial pose is more
than $\frac1{100}$ from the sides of the rectangle. At an interior minimum
both partial derivatives vanish. If two poses $P$, $P'$ have
$F_y = F_z = 0$, then (J.1) in both directions gives
$F(q, P') \ge F(q, P) + \frac18|P' - P|^2$ and
$F(q, P) \ge F(q, P') + \frac18|P - P'|^2$, so $P = P'$.

(2) For a fixed pose, Lemma J.2 (2) and the mean value theorem give
$-4(r - q) \le F(r, P) - F(q, P) \le -3(r - q)$. Apply it at $P(q)$ and at
$P(r)$, with $m(r) \le F(r, P(q))$ and $m(q) \le F(q, P(r))$.

(3) By (2) and Lemma J.2 (4), $m$ is continuous, strictly decreasing, positive
at $\frac{7831}{2000}$ and negative at $\frac{9789}{2500}$; the intermediate
value theorem gives one zero $q_*$, and $m(\ell_*) > 0 > m(u_*)$ places it
between $\ell_*$ and $u_*$. $\square$

*Lean:
[`Eight.ExactFamily.minimum_exists`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L176),
[`Eight.ExactFamily.minimum_interior`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L205),
[`Eight.ExactFamily.minimizingPose_stationary`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L270),
[`Eight.ExactFamily.FiveCornerGeometry.minimizer_unique`](../../SquaresInCircles/Eight/ExactFamily/Convexity.lean#L321),
[`Eight.ExactFamily.family_radius_difference`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L287),
[`Eight.ExactFamily.minimum_radius_difference`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L312),
[`Eight.ExactFamily.minimum_continuous`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L323),
[`Eight.ExactFamily.unique_minimum_zero`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L360),
[`Eight.ExactFamily.qStar_bracket`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L159).*

![The graph of the minimized defect m(q) against q over the radius interval from 7831/2000 to 9789/2500: a decreasing, nearly straight line from about 0.000126 to about -0.000243, crossing zero at q*, between two dashed lines of slopes -3 and -4 through the crossing. Beside it, an enlargement of the shaded bracket from l* to u*, of width 3 times 10 to the minus 16, in which m, computed to 60 digits and drawn in units of 10 to the minus 16, decreases from about 7.4 at l* to about -3.7 at u* and crosses zero at q*](figures/appendix-j/minimum.svg)

*Figure J.1.* The minimized defect $m(q)$ on
$[\frac{7831}{2000}, \frac{9789}{2500}]$ (solid), decreasing with a slope
between $-4$ and $-3$ (dashed lines through the zero); it vanishes at
$q_* \approx 3.9155341375$. Right: the bracket $[\ell_*, u_*]$ of
Proposition J.4 (3), of width $3 \cdot 10^{-16}$ (shaded), with $m$ computed in
60-digit arithmetic, in units of $10^{-16}$.

## J.4 Every solution lies in the local rectangle

### Proposition J.5 (localization)

Every solution $(q, y, z, x_1, x_2, y_3, x_4)$ of the stationary system has
$(q, y, z) \in \mathcal R$, and its other coordinates are the radicals of
Definition 11.2.

*Proof.* The circle equations and the signs of $x_1, x_2, y_3, x_4$ make these
the radicals of Definition 11.2. The system gives
$(\frac{79}{40})^2 \le q \le \frac{9789}{2500}$ and $-1 < y < -\frac12$;
and $0 < z < 1$ with $\frac{2z}{1 - z^2} < \frac15$ gives $2z < \frac15$, as
$1 - z^2 \le 1$, so $0 < z < \frac1{10}$. So $(q, y, z)$ lies in the initial
box of Lemma J.1 and is a common zero of $F$, $F_y$ and $F_z$, the last one
because $F_z = \frac2{1 + z^2}F_t$.

The formal proof follows the analytic argument below. $\square$

*Lean:
[`Eight.ExactFamily.FiveCornerGeometry.stationary_chain_unique`](../../SquaresInCircles/Eight/ExactFamily/Envelope.lean#L1114),
[`Eight.ExactFamily.FiveCornerGeometry.positionEnvelope_critical_unique`](../../SquaresInCircles/Eight/ExactFamily/Envelope.lean#L999),
[`Eight.ExactFamily.FiveCornerGeometry.strictConvexOn_defect`](../../SquaresInCircles/Eight/ExactFamily/Convexity.lean#L312),
[`Eight.ExactFamily.FiveCornerGeometry.defect_radius_decrease`](../../SquaresInCircles/Eight/ExactFamily/Convexity.lean#L465).*

The hand proof reaches the same conclusion analytically. It shows that, for
each squared radius in $[(\frac{79}{40})^2, \frac{9789}{2500}]$ and tilt in
$[0, \arctan\frac15]$, the defect is strictly convex in $y$ on the whole
radical domain, by concavity of the nested radicals, and that the reduced
curvature $F_{tt} - F_{yt}^2/F_{yy}$ is positive at every critical point of
the defect minimized over $y$ in this strip; so the minimized defect has a
single critical point at each radius. These are the statements that
Proposition J.5 replaces by a finite subdivision.

![The plane of y from -1 to -1/2 and z from 0 to 1/10 at q = q*, the section of the initial box, with z stretched: the curve where F_y vanishes and the curve where F_t vanishes, two nearly straight curves that cross at one point, the stationary pose (y*, z*), which lies in the shaded local rectangle; dotted level curves of F at 0.002, 0.01 and 0.04 surround the point, and F is positive on the rest of the section](figures/appendix-j/localization.svg)

*Figure J.2.* Proposition J.5 at $q = q_*$, in the $(y, z)$-section of the
initial box: the zero sets of $F_y$ and of $F_t$ (curves) cross only at the
stationary pose $(y_*, z_*)$, inside the local rectangle (shaded), where $F$
also vanishes; elsewhere on the section $F$ is positive (dotted: level curves
of $F$).

## J.5 Proof of Proposition 11.4

*Proof of Proposition 11.4.* (1) Let $q_*$ be the zero of Proposition J.4 (3)
and $(y_*, z_*) = P(q_*)$; then $F = F_y = F_z = 0$ there, hence $F_t = 0$.
The other conditions of the system hold at this point of $\mathcal R$: the
radicals are positive (Lemma J.1), $-1 < y_* < y_4 < -\frac12$ and
$\frac{2z_*}{1 - z_*^2} < \frac15$ follow from the bounds of (3) below, and
$q_* \ge (\frac{79}{40})^2$. So the system has a solution. Conversely, a
solution has $(q, y, z) \in \mathcal R$ by Proposition J.5, and its pose is
stationary for $F(q, \cdot)$, so by Proposition J.4 (1) it is the minimum
point, $F(q, P(q)) = m(q) = 0$, and $q = q_*$ by Proposition J.4 (3).

(2) is Proposition J.4 (3); then $q_- = 3.9155 < \ell_*$ and
$u_* < 3.915534138 = Q_1 < Q_0 = 3.9156$.

(3) At the solution, the pose lies within $10^{-12}$ of the trial pose: by
(J.1), $\frac18|P(q_*) - P_0|^2 \le |\nabla F(q_*, P_0)|\,|P(q_*) - P_0|$,
and at $q_*$ the trial gradient is smaller than $10^{-13}$, by interval
evaluation on the bracket of (2). The stated bounds then follow by evaluating
the radicals of Definition 11.2 on the box
$[\ell_*, u_*] \times [y_0 - 10^{-12}, y_0 + 10^{-12}] \times [z_0 - 10^{-12}, z_0 + 10^{-12}]$.

(4) is Proposition J.4 (1) to (3), since the pose rectangle in $z$ is the
interval $\frac1{20} \le \tan\frac t2 \le \frac{81}{1000}$. $\square$

*Lean:
[`Eight.ExactFamily.sharpData`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L211),
[`Eight.ExactFamily.sharpData_stationary`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L213),
[`Eight.ExactFamily.stationary_unique`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L248),
[`Eight.ExactFamily.exact_stationary_existsUnique`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L251),
[`Eight.ExactFamily.sharpPose_close`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L179),
[`Eight.ExactFamily.sharpBox_mem`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L202),
[`Eight.ExactFamily.sharp_coordinates`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L254),
[`Eight.ExactFamily.sharp_y`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L289),
[`Eight.ExactFamily.qStar_limits`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L171).*

The public statement defines the radius through the geometric five-corner
minimum. Its unique minimizer is the stationary configuration described here;
the proof also identifies the geometric angle and slider parameters with the
stationary chart. These bridges keep the statement independent of the table
representation.

*Lean:
[`Eight.FiveCorner.existsUnique_minimizer`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L868),
[`Eight.FiveCorner.selected_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L877),
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38).*

## J.6 The weights

### Lemma J.6 (the weights of the chain)

Let $(q, y, t)$ be a point of the chain with $x_1, x_2, y_3, c, s > 0$,
$x_3, x_4, h_1, h_2 < 0$, $y + 2 > 0$ and $F_y = 0$. Put

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
Then all twelve weights are positive, $\sum_P\mu_P = 1$, and with
$e_0 = (1, 0)$, $f_0 = (0, 1)$ and the corners $P_A = P_1, \dots, P_H = P_5$,

```math
\begin{aligned}
2\mu_A P_A &= \omega\,e_t - \lambda_{AB}\,f_0, & 2\mu_B P_B &= \lambda_{TB}\,e_0 + \lambda_{AB}\,f_0, & 2\mu_D P_D &= -\lambda_{DT}\,e_0 + \lambda_{ED}\,f_0, \\
2\mu_E P_E &= \lambda_{HE}\,f_t - \lambda_{ED}\,f_0, & 2\mu_H P_H &= -\omega\,e_t - \lambda_{HE}\,f_t . &&
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
[`Eight.ExactFamily.Coordinates.WeightDomain`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L47),
[`Eight.ExactFamily.Coordinates.IsStationary.weightDomain`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L60),
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L119),
[`Eight.ExactFamily.Coordinates.WeightDomain.lam_pos`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L138),
[`Eight.ExactFamily.Coordinates.WeightDomain.mu_sum`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L122),
[`Eight.ExactFamily.Coordinates.last_force_residual`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L142),
[`Eight.ExactFamily.Coordinates.force_balance`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L192),
[`Eight.ExactFamily.Coordinates.slider_forces_zero`](../../SquaresInCircles/Eight/ExactFamily/Weights.lean#L203).*

At the solution of the stationary system the weights are approximately
$\mu = (0.2097, 0.2212, 0.2734, 0.0251, 0.2706)$ for $A, B, D, E, H$ and
$\lambda = (0.4774, 0.7336, 0.7336, 0.7954, 0.7740, 0.7403, 0.7403)$ for
$AB, TB, DT, ED, HE, GA, HG$
([Figure 11.22](11-eight.md#theorem-1136-the-sharp-terminal)). The equations
(J.2) say that the forces $\lambda_e$ along the seven contacts and the forces
$-2\mu_P P_P$ at the five corners balance at every square: at $T$ the two
contacts $TB$ and $DT$ have equal weights and opposite directions, and at $G$
so do $GA$ and $HG$.
