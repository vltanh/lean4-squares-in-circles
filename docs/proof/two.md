# 5. Two squares

[Contents](README.md) · [← 4. One square](one.md) · [6. Three squares →](three.md)

This chapter proves the case $n = 2$ of the main theorem: the least radius of a
closed disk that holds two disjoint unit squares is $R_2 = \frac{\sqrt5}2$,
half the diagonal of a $2 \times 1$ rectangle, and in a closed disk of that
radius the two squares always form such a rectangle, centred at the centre of
the disk. Packings, models and congruence are as in
[Definitions 2.3](preliminaries.md#definition-23-packing) and
[2.6](preliminaries.md#definition-26-congruence-to-a-model).

The proof plays two facts against each other. The farthest-vertex bound
([Lemma 3.4](common.md#lemma-34-farthest-vertex)) keeps the centre of each
square within $\frac12$ of the disk centre $o$, while the centres of two
disjoint unit squares are at least 1 apart
([Lemma 3.10](common.md#lemma-310-centres-at-least-1-apart)). By the
parallelogram law both can hold only if both centres are exactly $\frac12$
from $o$, and then $o$ is the midpoint of an edge of each square. Each square
then holds the half of the circle of radius $\frac12$ about $o$ that lies on
its side of the line of that edge. Two disjoint open half circles are opposite
halves of the circle, so the two squares share their edge through $o$ and lie
on opposite sides of it: they form the rectangle.

## Theorem 5.1 (two squares)

Let $R_2 = \frac{\sqrt5}2$, and let the *rectangle* be the model
$Q(c_1), Q(c_2)$ with $c_1 = (-\frac12, 0)$ and $c_2 = (\frac12, 0)$.

1. The rectangle is a packing in the closed disk of radius $R_2$ about the
   origin.
2. If two unit squares form a packing in a closed disk of radius $R$, then
   $R \ge R_2$.
3. The packings of two unit squares in a closed disk of radius $R_2$ are
   exactly the configurations congruent to the rectangle.

![Two axis-parallel unit squares side by side forming a 2 by 1 rectangle centred at the disk centre o, with its four corners on the dashed circle of radius root 5 over 2 about o](figures/two.svg)

*Figure 5.1.* The rectangle placed at the disk centre $o$. The squares
$Q(c_1)$ and $Q(c_2)$ share an edge whose midpoint is $o$, and the four
corners of the $2 \times 1$ rectangle lie on the circle of radius $R_2$ about
$o$ (dashed).

*Lean: [`Two.model_packing`](../../SquaresInCircles/Two/Construction.lean#L18),
[`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L47),
[`Two.optimum`](../../SquaresInCircles/Two/Uniqueness.lean#L76).*

*Outline of the proof.* Part (1) is a direct check (Proposition 5.2, §5.1).
The substance of the theorem is uniqueness, Proposition 5.3: two unit squares
$S$ and $T$ that form a packing in a closed disk of radius $R_2$ about a point
$o$ are congruent to the rectangle. Its proof runs as follows.

1. Both centres are at distance exactly $\frac12$ from $o$ (Lemmas 5.4 and
   5.5, §5.2).
2. Hence $(a_S, b_S) = (a_T, b_T) = (\frac12, 0)$: the disk centre is the
   midpoint of an edge of each square (§5.3, step 1).
3. Each square holds the half of the circle $\Gamma_{1/2}$ about $o$ on its
   side of that edge, and two disjoint half circles have opposite centres
   (§5.3, steps 2 and 3).
4. So in one frame at $o$ the square $S$ sits at $c_2$ and $T$ at $c_1$, which
   is the congruence (§5.3, steps 4 and 5).

Parts (2) and (3) then follow from Propositions 5.2 and 5.3 by the scheme of
proof, [Corollary 2.10](preliminaries.md#corollary-210-the-scheme-of-proof)
(§5.4).

## 5.1 Construction

### Proposition 5.2 (construction)

The rectangle is a packing in the closed disk of radius $R_2$ about the origin:
$Q(c_1)$ and $Q(c_2)$ are disjoint, and their closed squares lie in
$\overline{D}(0, R_2)$.

![The rectangle of the two unit squares Q(c1) and Q(c2), centred at minus one half and one half on the x-axis, inside the dashed circle of radius R2 about o; a right triangle with legs 1 along the x-axis and one half upwards joins o to the corner (1, 1/2), which lies on the circle like the other three corners](figures/two-corners.svg)

*Figure 5.2.* The centres $c_1$ and $c_2$ differ by 1 in the first
coordinate, and the corner $(1, \frac12)$, at the end of the hypotenuse of the
right triangle with legs 1 and $\frac12$, is at distance
$\sqrt{1 + \frac14} = R_2$ from $o$; by symmetry, so are the other three
corners.

*Proof.* The centres $c_1 = (-\frac12, 0)$ and $c_2 = (\frac12, 0)$ differ by
1 in the first coordinate, and each of them, $(x, y) = (\mp\frac12, 0)$,
satisfies

```math
\left(|x| + \tfrac12\right)^2 + \left(|y| + \tfrac12\right)^2 = 1 + \tfrac14 = \tfrac54 = R_2^2 .
```

So [Lemma 2.8](preliminaries.md#lemma-28-axis-parallel-squares) (3)
applies. $\square$

*Lean: [`Two.model_packing`](../../SquaresInCircles/Two/Construction.lean#L18),
[`Two.model`](../../SquaresInCircles/Geometry.lean#L134),
[`Two.radius`](../../SquaresInCircles/Geometry.lean#L128),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L34).*

## 5.2 The centres

### Proposition 5.3 (uniqueness)

Let $o$ be a point of the plane, and let $S$ and $T$ be two unit squares that
form a packing in the closed disk $\overline{D}(o, R_2)$. Then the
configuration $S, T$ is congruent to the rectangle.

The proof occupies §5.2 and §5.3. This section shows that both centres are at
distance exactly $\frac12$ from $o$, and §5.3 locates the squares from there.
We first turn the farthest-vertex bound at radius $R_2$ into a bound on the
distance from the centre of a square to $o$ (Figure 5.3).

![A tilted unit square S inside the dashed circle of radius R2 about o, with its vertex farthest from o on that circle, joined to o by a segment of length R2; the centre c_S lies inside the orange dashed circle of radius one half about o](figures/two-near.svg)

*Figure 5.3.* A unit square $S$ whose closed square lies in the closed disk of
radius $R_2$ about $o$ (dashed), here with its farthest vertex on the circle.
By Lemma 3.4 and Lemma 5.4 its centre $c_S$ lies in the closed disk of radius
$\frac12$ about $o$ (orange).

### Lemma 5.4 (centres near the disk centre)

Let $a$ and $b$ be nonnegative real numbers with $\varphi(a, b) \le \frac54$.
Then $a^2 + b^2 \le \frac14$.

![The (a, b)-plane where a and b are at least 0: the region where phi is at most 5/4, bounded by an arc from (1/2, 0) to (0, 1/2), lies inside the dashed quarter circle of radius one half and meets it only at these two points; the diagonal a = b is drawn dotted](figures/two-ab-plane.svg)

*Figure 5.4.* Lemma 5.4 in the $(a, b)$-plane. For $a, b \ge 0$, the region
$\varphi(a, b) \le \frac54$ (blue) lies in the quarter disk
$a^2 + b^2 \le \frac14$, and meets the quarter circle $a^2 + b^2 = \frac14$
(dashed) only at $(\frac12, 0)$ and $(0, \frac12)$. Of these two points only
$(\frac12, 0)$ has $b \le a$; this is step 1 of the proof of
Proposition 5.3.

*Proof.* Expanding the squares,

```math
\varphi(a, b) = \left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 = (a^2 + b^2) + (a + b) + \tfrac12 . \tag{5.1}
```

Suppose that $a^2 + b^2 > \frac14$. As $a, b \ge 0$, we have
$(a + b)^2 = a^2 + b^2 + 2ab \ge a^2 + b^2 > \frac14$, and as $a + b \ge 0$,
also $a + b > \frac12$. Then (5.1) gives
$\varphi(a, b) > \frac14 + \frac12 + \frac12 = \frac54$, a contradiction.
$\square$

*Lean: [`Two.center_near`](../../SquaresInCircles/Two/Uniqueness.lean#L22).*

### Lemma 5.5 (both centres at distance one half)

Let $o$ be a point of the plane, and let $S$ and $T$ be disjoint unit squares
with $\varphi(a_S, b_S) \le \frac54$ and $\varphi(a_T, b_T) \le \frac54$. Then

```math
a_S^2 + b_S^2 = a_T^2 + b_T^2 = \tfrac14 ,
```

that is, both centres are at distance exactly $\frac12$ from $o$.

![Two centres c_S and c_T inside the dashed disk of radius one half about o, the parallelogram with vertices o, c_S, c_S plus c_T minus o, and c_T, and its two diagonals: the segment from c_S to c_T and the dashed segment from o](figures/parallelogram.svg)

*Figure 5.5.* The parallelogram spanned by $c_S - o$ and $c_T - o$. Its
squared diagonals add up to twice the squared sides from $o$, so if both
centres are within $\frac12$ of $o$, the diagonal from $c_S$ to $c_T$ is at
most 1.

*Proof.* Put $u = c_S - o$ and $v = c_T - o$.

**Step 1. Both centres are near the disk centre.** By Lemma 3.4,
$|u|^2 = a_S^2 + b_S^2$ and $|v|^2 = a_T^2 + b_T^2$. The numbers
$a_S, b_S, a_T, b_T$ are nonnegative
([Definition 3.1](common.md#definition-31-position-of-the-disk-centre)), so
Lemma 5.4 applies to the pairs $(a_S, b_S)$ and $(a_T, b_T)$, and gives
$|u|^2 \le \frac14$ and $|v|^2 \le \frac14$.

**Step 2. The parallelogram law.** The parallelogram with vertices $o$, $c_S$,
$c_S + c_T - o$ and $c_T$ (Figure 5.5) has the sides $u$ and $v$ at $o$, and
its diagonals are $u - v = c_S - c_T$ and $u + v = c_S + c_T - 2o$. Expanding
the inner products,

```math
|u - v|^2 + |u + v|^2 = \left(|u|^2 - 2\langle u, v\rangle + |v|^2\right) + \left(|u|^2 + 2\langle u, v\rangle + |v|^2\right) = 2|u|^2 + 2|v|^2 .
```

**Step 3. Equality throughout.** The squares are disjoint, so
$|c_S - c_T| \ge 1$ by
[Lemma 3.10](common.md#lemma-310-centres-at-least-1-apart). With steps 1
and 2,

```math
1 \le |c_S - c_T|^2 = 2|u|^2 + 2|v|^2 - |u + v|^2 \le 2|u|^2 + 2|v|^2 \le 2 \cdot \tfrac14 + 2 \cdot \tfrac14 = 1 .
```

So equality holds throughout; in particular $|u|^2 + |v|^2 = \frac12$. As
$|v|^2 \le \frac14$, this gives $|u|^2 = \frac12 - |v|^2 \ge \frac14$, hence
$|u|^2 = \frac14$, and in the same way $|v|^2 = \frac14$. By Lemma 3.4 these
are the claims $a_S^2 + b_S^2 = \frac14$ and $a_T^2 + b_T^2 = \frac14$.
$\square$

*Lean: [`Two.centers_at_half`](../../SquaresInCircles/Two/Uniqueness.lean#L36),
[`Two.normSq_parallelogram`](../../SquaresInCircles/Two/Uniqueness.lean#L28).*

*Remark.* Equality throughout also gives $u + v = 0$ and $|c_S - c_T| = 1$:
the disk centre is the midpoint of the two centres, which are exactly 1 apart,
as in the rectangle. The proof below does not need this.

## 5.3 The half circles

We now complete the proof of Proposition 5.3. By Lemma 5.5 both centres are at
distance $\frac12$ from $o$. Step 1 below shows that this places $o$ at the
midpoint of an edge of each square; the half circles of steps 2 and 3 then fix
the squares relative to each other, and steps 4 and 5 read off the rectangle.

*Proof of Proposition 5.3.* The closed squares of $S$ and $T$ lie in
$\overline{D}(o, R_2)$, so $\varphi(a_S, b_S) \le R_2^2 = \frac54$ and
$\varphi(a_T, b_T) \le \frac54$ by Lemma 3.4; and $S$ and $T$ are disjoint, as
the squares of a packing are
([Definition 2.3](preliminaries.md#definition-23-packing)). By Lemma 5.5,

```math
a_S^2 + b_S^2 = a_T^2 + b_T^2 = \tfrac14 .
```

**Step 1. The disk centre is the midpoint of an edge of each square.** We show
that $(a_S, b_S) = (\frac12, 0)$; the same argument gives
$(a_T, b_T) = (\frac12, 0)$. Write $a = a_S$ and $b = b_S$, so that
$a \ge b \ge 0$ (Definition 3.1) and $a^2 + b^2 = \frac14$. By (5.1),
$\varphi(a, b) = \frac14 + (a + b) + \frac12 \le \frac54$, so
$a + b \le \frac12$. On the other hand
$(a + b)^2 = a^2 + b^2 + 2ab \ge \frac14$ and $a + b \ge 0$, so
$a + b \ge \frac12$. Hence $a + b = \frac12$, and

```math
2ab = (a + b)^2 - \left(a^2 + b^2\right) = \tfrac14 - \tfrac14 = 0 .
```

So $a = 0$ or $b = 0$. If $a = 0$, then also $b = 0$, as $0 \le b \le a$,
which contradicts $a^2 + b^2 = \frac14$. Hence $b = 0$ and
$a = a + b = \frac12$. By Definition 3.1 the local coordinates of $o$ in the
frame of $S$ are then $(\pm\frac12, 0)$ or $(0, \pm\frac12)$: the point $o$ is
the midpoint of an edge of $S$, and likewise of an edge of $T$ (Figure 5.6).

![Two panels, each with a unit square whose centre c_S lies on the grey circle of radius one half about o, inside the dashed circle of radius R2 about o. Left: o is the midpoint of the thick edge of the square, and the two far corners lie on the dashed circle. Right: the centre lies diagonally from o, and the farthest vertex lies outside the dashed circle](figures/two-edge-midpoint.svg)

*Figure 5.6.* Step 1. Two unit squares with centres at distance $\frac12$
from $o$ (grey circle). Left, $(a_S, b_S) = (\frac12, 0)$: the point $o$ is
the midpoint of the thick edge, and the two far corners lie on the circle of
radius $R_2$ (dashed). Right, $a_S = b_S = \frac{\sqrt2}4$: the farthest
vertex is at squared distance
$\varphi(a_S, b_S) = \frac34 + \frac{\sqrt2}2 > \frac54$ from $o$, outside
that circle.

**Step 2. Each square holds a half circle.** Let $(\theta_S, \varepsilon_S)$
and $(\theta_T, \varepsilon_T)$ be charts of $S$ and $T$
([Lemma 3.21](common.md#lemma-321-charts)). We show that $S$ holds the arc of
$\Gamma_{1/2}$ with centre $\theta_S$ and half-width $\frac\pi2$
([Definitions 3.14](common.md#definition-314-circles-about-the-disk-centre)
and [3.15](common.md#definition-315-arc)), the open half of $\Gamma_{1/2}$
centred at $\theta_S$; in the same way $T$ holds the half of $\Gamma_{1/2}$
centred at $\theta_T$. By step 1, the condition of Lemma 3.21 (2) for $S$,
with $r = \frac12$, asks that the chart angles $t$ of an interval satisfy

```math
\left|\tfrac12\cos t - \tfrac12\right| < \tfrac12 \qquad\text{and}\qquad \left|\tfrac12\sin t - 0\right| < \tfrac12 .
```

Both hold for $-\frac\pi2 < t < \frac\pi2$: there $0 < \cos t \le 1$, so
$|\frac12\cos t - \frac12| = \frac12(1 - \cos t) < \frac12$, and
$\sin^2 t = 1 - \cos^2 t < 1$, so $|\frac12\sin t| < \frac12$. The interval
$(-\frac\pi2, \frac\pi2)$ has length $\pi \le 2\pi$, so by Lemma 3.21 (2) the
square $S$ holds an arc of $\Gamma_{1/2}$ with half-width $\frac\pi2$ and
centre $\theta_S + \varepsilon_S \cdot 0 = \theta_S$. This is the case
$r = \frac12$ of
[Lemma 3.24](common.md#lemma-324-arcs-of-an-exterior-square) (3). In the
chart, $S$ is the square $0 < x < 1$, $|y| < \frac12$, and its half circle is
the half of $\Gamma_{1/2}$ where $x > 0$, on the side of $S$ of the line of
the edge through $o$ (Figure 5.7).

![A unit square S in its chart, centred at (1/2, 0), with the disk centre o at the midpoint of its left edge, drawn thick; the circle of radius one half about o, whose right half, from chart angle minus pi/2 to pi/2, is highlighted inside the square; a point at chart angle t on it](figures/two-half-circle.svg)

*Figure 5.7.* Step 2: a square with $(a_S, b_S) = (\frac12, 0)$ in its chart.
The disk centre $o$ is the midpoint of the near edge (thick), and every point
of $\Gamma_{1/2}$ at a chart angle $t$ with $|t| < \frac\pi2$ lies in
$S^\circ$: the half of $\Gamma_{1/2}$ on the side of $S$ (blue), whose ends
are the two corners of that edge.

**Step 3. The half circles are opposite.** The open squares $S^\circ$ and
$T^\circ$ are disjoint, and by step 2 they hold arcs of the same circle
$\Gamma_{1/2}$ with centres $\theta_S$ and $\theta_T$ and half-widths
$\frac\pi2$. By
[Lemma 3.17](common.md#lemma-317-disjoint-arcs-have-separated-centres),
$d(\theta_S, \theta_T) \ge \frac\pi2 + \frac\pi2 = \pi$. The angle between two
directions is at most $\pi$ (§2.1), so $d(\theta_S, \theta_T) = \pi$.
Represent the direction $\theta_T - \theta_S$ by a number $\delta$ with
$-\pi < \delta \le \pi$; by the definition of the angle between two
directions, $d(\theta_S, \theta_T) = |\delta|$, so $\delta = \pi$ and
$\theta_T = \theta_S + \pi$ (Figure 5.8).

![Two panels with the circle of radius one half about o and two squares with o at the midpoint of an edge of each, holding the half circles centred at the directions theta S (blue) and theta T (green). Left: theta T is less than pi from theta S, the half circles share a point p, and the squares overlap. Right: theta T is opposite to theta S, the half circles are complementary, and the squares form the rectangle](figures/two-opposite.svg)

*Figure 5.8.* Step 3. Left: if the half circles held by $S$ (blue) and $T$
(green) had centres less than $\pi$ apart, they would share a point $p$ of
$\Gamma_{1/2}$, which would lie in both open squares. Right: for disjoint
squares the centres are opposite, $\theta_T = \theta_S + \pi$, and the squares
form the rectangle.

**Step 4. Both squares in one frame.** By
[Lemma 3.22](common.md#lemma-322-cartesian-form-of-a-chart) and step 1, $S$
sits at $(a_S, \varepsilon_S b_S) = (\frac12, 0) = c_2$ in the frame
$\theta_S$, and $T$ sits at $(a_T, \varepsilon_T b_T) = (\frac12, 0)$ in the
frame $\theta_T = \theta_S + \pi$. Since $u(\phi + \pi) = -u(\phi)$ for every
direction $\phi$, the definition of the frames
([Definition 2.4](preliminaries.md#definition-24-frames-at-the-disk-centre))
gives, for all real $x$ and $y$,

```math
F_{\theta_S + \pi}(x, y) = o + x\,u(\theta_S + \pi) + y\,u\left(\theta_S + \tfrac{3\pi}2\right) = o - x\,u(\theta_S) - y\,u\left(\theta_S + \tfrac\pi2\right) = F_{\theta_S}(-x, -y) .
```

Hence, for all real $x$ and $y$,

```math
F_{\theta_S}(x, y) \in T^\circ \iff F_{\theta_S + \pi}(-x, -y) \in T^\circ \iff \left|-x - \tfrac12\right| < \tfrac12 \ \text{and}\ |-y| < \tfrac12 \iff (x, y) \in Q(c_1)^\circ ,
```

because $|-x - \frac12| = |x - (-\frac12)|$ and $|-y| = |y|$. So $T$ sits at
$c_1 = (-\frac12, 0)$ in the frame $\theta_S$ (Figure 5.9). This is
[Lemma 3.30](common.md#lemma-330-sitting-at-a-centre) (2) with two quarter
turns.

![The rectangle of the squares S and T turned by the angle theta S about o, with the axes of the frame at o turned by theta S drawn solid and the axes of the opposite frame, turned by theta S plus pi, drawn dashed; the centre of S is at (1/2, 0) and the centre of T at (-1/2, 0) in the solid frame](figures/two-frame.svg)

*Figure 5.9.* Step 4. In the frame $\theta_S$ (solid axes) the square $S$
sits at $(\frac12, 0)$. In the opposite frame $\theta_S + \pi$ (dashed axes)
the square $T$ sits at $(\frac12, 0)$, which is the point $(-\frac12, 0)$ of
the frame $\theta_S$.

**Step 5. Congruence.** The squares $S$ and $T$ are disjoint, and in the
common frame $\theta_S$ the square $T$ sits at $c_1$ and $S$ at $c_2$. By
[Lemma 3.31](common.md#lemma-331-from-slots-to-congruence) the configuration
$S, T$ is congruent to the model $Q(c_1), Q(c_2)$, the rectangle, with the
relabelling that puts $T$ in the slot $c_1$ and $S$ in the slot $c_2$.
$\square$

*Lean: [`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L47),
[`SquareChart.half_arc`](../../SquaresInCircles/Common/Charts.lean#L193),
[`OpenArc.opposite`](../../SquaresInCircles/Common/Angles.lean#L31),
[`represents_quarter`](../../SquaresInCircles/Common/Angles.lean#L78).*

## 5.4 Proof of Theorem 5.1

*Proof of Theorem 5.1.* We apply
[Corollary 2.10](preliminaries.md#corollary-210-the-scheme-of-proof) with
$n = 2$, $R_2 = \frac{\sqrt5}2 > 0$ and
$\mathcal M = \lbrace\text{the rectangle}\rbrace$: (a) is Proposition 5.2; (b)
holds because the corner $(1, \frac12)$ of $\overline{Q(c_2)}$ is at distance
$\sqrt{1 + \frac14} = R_2$ from the origin (Figure 5.2); (c) is
Proposition 5.3. Parts (1), (2), (3) of the theorem are (a), (i) and (ii).
$\square$

*Lean: [`Two.optimum`](../../SquaresInCircles/Two/Uniqueness.lean#L76),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L47),
[`Optimum.isLeast`](../../SquaresInCircles/Common/Optimum.lean#L61),
[`Optimum.packing_iff`](../../SquaresInCircles/Common/Optimum.lean#L67).*
