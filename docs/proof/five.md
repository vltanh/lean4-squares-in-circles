# Five squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 5.** Let $R_5 = \sqrt{5/2}$, and let $c_1, \dots, c_5$ be the points
$(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$.

1. $Q(c_1), \dots, Q(c_5)$ form a packing in the closed disk of radius $R_5$
   about the origin: the plus, one square centred at the disk centre and its
   four side-neighbours.
2. A packing of five unit squares in a closed disk of radius $R$ forces
   $R \ge R_5$.
3. The packings of five unit squares in a closed disk of radius $R_5$ are
   exactly the configurations with the normal form of $c_1, \dots, c_5$.

![The plus in its dashed circle of radius root of 5/2, with the circle of radius 5/6 about the centre; each outer square holds a coloured arc of about 74 degrees, and the grey centre square holds none](figures/five.svg)

*The plus. Each outer square holds an arc of about 74° of the
circle $\Gamma_{5/6}$; the centre square (grey) holds none.*

*Sketch.* The work is in part 3; part 2 follows from it, since a corner of the
plus lies on the circle of radius $R_5$. Take a packing in the closed disk of
radius $R_5$, and draw the circle $\Gamma_{5/6}$ about the disk centre. Every
square that avoids the centre holds more than a fifth of it, and the radial
sweep of a square containing the centre holds a fifth, unless that square is
centred exactly at the disk centre. Five such arcs do not fit, so some square
is centred at the disk centre. The other four squares are then at distance
exactly 1 from it: the plus.

Unlike three and four squares, the argument here needs only the closed
contact polygon; the disk is not used after Step 1.

*Lean:
[`Five.model_packing`](../../SquaresInCircles/Five/Construction.lean#L29),
[`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L82),
[`Five.optimum`](../../SquaresInCircles/Five/Uniqueness.lean#L92),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48), in
[`SquaresInCircles/Five/`](../../SquaresInCircles/Five).*

## Construction

### Proposition 5.1 (attainment)

$Q(c_1), \dots, Q(c_5)$ are pairwise disjoint and lie in the closed disk of
radius $R_5$ about the origin.

*Proof.* Any two of the centres differ by at least 1 in one coordinate, and
every centre $(x, y)$ has
$(|x| + \frac12)^2 + (|y| + \frac12)^2 \le \frac94 + \frac14 = \frac52$. Apply
[Lemma 17](common.md#lemma-17-axis-parallel-squares). $\square$

The eight outer corners, $(\pm\frac32, \pm\frac12)$ and
$(\pm\frac12, \pm\frac32)$, lie on the circle.

*Lean:
[`Five.model_packing`](../../SquaresInCircles/Five/Construction.lean#L29),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## Uniqueness

### Proposition 5.2 (uniqueness)

If five pairwise disjoint unit squares lie in the closed disk of radius $R_5$
about $o$, the packing has the normal form of $c_1, \dots, c_5$.

The proof shows more: after Step 1 it needs only a contact polygon, not the
disk (Proposition 5.10). It takes four steps.

1. **The contact polygon.** The disk puts $(a_S, b_S)$ in a 12-gon $P_5$ for
   every square $S$.
2. **Exterior squares.** Each square that avoids $o$ holds more than a fifth
   of $\Gamma_{5/6}$.
3. **A centred square.** Unless it is centred at $o$, a square that contains
   $o$ holds a fifth of $\Gamma_{5/6}$ in its radial sweep. So some square is
   centred at $o$.
4. **The plus.** The 12-gon keeps every centre within 1 of $o$, so the other
   four squares are side-neighbours of the centred one.

*Lean: [`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L82).*

### Step 1. The contact polygon

#### Definition 5.3 (the 12-gon)

$P_5$ is the set of points $(a, b)$ with

```math
3a + b \le 3, \qquad a + 3b \le 3, \qquad a + b \le \sqrt5 - 1 .
```

The first two inequalities are the octagon $P_8$: the tangents to
$\varphi = \frac52$ at $(1, 0)$ and $(0, 1)$. The outer squares of the plus
have $(a_S, b_S) = (1, 0)$. The third is the tangent at
$(\frac{\sqrt5 - 1}2, \frac{\sqrt5 - 1}2)$, also on $\varphi = \frac52$. No
square of the plus touches it; Step 2 needs it.

![The part with a, b at least 0 of the 12-gon P5, around the disk where phi is at most 5/2, touching it at (1, 0), (0, 1) and (g, g)](figures/twelve-gon.svg)

*The 12-gon $P_5$ where $a, b \ge 0$, with $g = \frac{\sqrt5 - 1}2$. Its third
side cuts the corner off the octagon.*

*Lean: [`Five.P5`](../../SquaresInCircles/Five/Exterior.lean#L17).*

#### Lemma 5.4 (contact polygon)

If $\varphi(a, b) \le \frac52$, then $(a, b) \in P_5$.

*Proof.* [Lemma 2](common.md#lemma-2-tangent-lines) at the three points.
$\square$

From here on only the polygon and disjointness are used.

*Lean: [`Five.p5_of_phi`](../../SquaresInCircles/Five/Exterior.lean#L20).*

### Step 2. Exterior squares

#### Lemma 5.5 (an arcsine sum)

If $0 \le x \le \frac12$, $-\frac12 \le y \le \frac12$,
$x + y \le \frac{237}{1000}$ and $3x + y \le 1$, then

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 < \tfrac\pi{10} .
```

*Proof.* If $y \ge 0$, apply the cubic bound of
[Lemma 16](common.md#lemma-16-elementary-estimates) (3) to both terms. With
$s = x + y$ and $x^3 + y^3 \le s^3$,

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 \le \tfrac65 s + \tfrac{54}{125}s^3 < \tfrac{313}{1000} < \tfrac\pi{10} .
```

If $y < 0$, use $\arcsin\frac{6y}5 \le \frac{6y}5$ (Lemma 16 (2)) for the
second term, and bound $x^3$ directly when $x \le \frac{23}{60}$, or through
$3x + y \le 1$ when $x > \frac{23}{60}$. $\square$

*Lean: [`Five.arcsin_sum`](../../SquaresInCircles/Five/Exterior.lean#L35).*

#### Lemma 5.6 (exterior arcs)

Let $S$ be exterior with $(a_S, b_S) \in P_5$. Then $S$ holds an arc of
$\Gamma_{5/6}$ of half-width more than $\frac\pi5$.

*Idea.* On this larger circle the arc can reach past the far side of the cap,
so we use the whole arc of
[Lemma 12](common.md#lemma-12-arcs-of-an-exterior-square) (1), whose figure is
drawn on this circle. Its length is one of four sums of crossing angles, and
the 12-gon keeps each of them above $\frac{2\pi}5$.

*Proof.* Here $b_S \le a_S$, $a_S \ge \frac12$, and $a_S \le 1$ by the
octagon. Put $x = a_S - \frac12 \in [0, \frac12]$ and
$y = b_S - \frac12 \in [-\frac12, \frac12]$. Since
$a_S - \frac12 \le \frac12 < \frac56 < a_S + \frac12$, Lemma 12 (1) applies on
$\Gamma_{5/6}$, with the crossing angles
([Definition 16](common.md#definition-16-crossing-angles))

```math
A_S = \arccos\tfrac{6x}5, \qquad V_S = -\arcsin\tfrac{6y}5, \qquad U_S = \arcsin\tfrac{6(b_S + 1/2)}5 .
```

The arc has length $\min(A_S, U_S) + \min(A_S, V_S)$, which is one of
$2A_S$, $A_S + V_S$, $A_S + U_S$ and $U_S + V_S$. Each of these exceeds
$\frac{2\pi}5$.

- $2A_S$: $\frac{6x}5 \le \frac35 < \frac{401}{500} < \cos\frac\pi5$
  (Lemma 16 (5)), so $A_S > \frac\pi5$.
- $A_S + V_S = \frac\pi2 - \arcsin\frac{6x}5 - \arcsin\frac{6y}5$ exceeds
  $\frac{2\pi}5$ exactly when
  $\arcsin\frac{6x}5 + \arcsin\frac{6y}5 < \frac\pi{10}$. The polygon gives
  $x + y \le \sqrt5 - 2 < \frac{237}{1000}$ and $3x + y \le 1$, so Lemma 5.5
  applies.
- $A_S + U_S \ge \frac\pi2$, since $b_S + \frac12 \ge a_S - \frac12$ gives
  $U_S \ge \arcsin\frac{6x}5 = \frac\pi2 - A_S$.
- $U_S + V_S$: if $b_S + \frac12 \ge \frac56$, then $U_S = \frac\pi2 \ge A_S$,
  and the second bound applies. Otherwise
  $U_S + V_S = \arcsin\frac{6(b_S + 1/2)}5 + \arcsin\frac{6(1/2 - b_S)}5$,
  whose two arguments average $\frac35 > \sin\frac\pi5$, and Lemma 16 (4)
  gives more than $\frac{2\pi}5$. $\square$

*Lean: [`Five.arc_length`](../../SquaresInCircles/Five/Exterior.lean#L60),
[`Five.exterior_arc`](../../SquaresInCircles/Five/Exterior.lean#L102).*

### Step 3. A centred square

#### Lemma 5.7 (the sweep holds a fifth of the circle)

Let $S$ contain $o$, with $c_S \ne o$. Then $\widehat{S}$ holds an arc of
$\Gamma_{5/6}$ of half-width $\frac\pi5$.

*Idea.* Slide $S$ outward until its centre is at distance $\frac1{\sqrt2}$
from $o$. Its inscribed disk then covers a fifth of $\Gamma_{5/6}$, even when
$S$ itself does not reach the circle (see the figure in
[Definition 17](common.md#definition-17-radial-sweep)).

![A square containing o, slid outward along the ray from o through its centre until its centre c* is at distance 1 over root 2 from o; the inscribed disk of the slid square covers a highlighted fifth of the circle of radius 5/6](figures/slid-disk.svg)

*The slid copy of $S$, centred at $c^*$, and its inscribed disk. The disk covers
the arc of $\Gamma_{5/6}$ of half-width $\frac\pi5$ about the direction of
$c_S - o$.*

*Proof.* In the chart of $S$, its centre is
$(a_S, b_S) = \ell(\cos\delta, \sin\delta)$ with $\ell > 0$, since
$c_S \ne o$, and $\ell^2 = a_S^2 + b_S^2 < \frac12$, since
$a_S, b_S < \frac12$. Slide $S$ away from $o$ by
$m = \frac1{\sqrt2\,\ell} - 1 \ge 0$: in the chart its centre moves to
$c^* = \frac1{\sqrt2}(\cos\delta, \sin\delta)$
([Definition 15](common.md#definition-15-chart)). For
$|t - \delta| < \frac\pi5$, the chart point $\frac56(\cos t, \sin t)$ is at
squared distance

```math
\tfrac{25}{36} + \tfrac12 - \tfrac{5\sqrt2}6\cos(t - \delta)
< \tfrac{25}{36} + \tfrac12 - \tfrac53\cdot\tfrac{707}{1000}\cdot\tfrac{401}{500} < \tfrac14
```

from $c^*$, by Lemma 16 (5) and $\frac1{\sqrt2} > \frac{707}{1000}$. So both of
its coordinates are within $\frac12$ of those of $c^*$: the point lies in the
slid square, hence in $\widehat{S}$. These chart angles form an arc of
half-width $\frac\pi5$, centred at $\theta_S + \varepsilon_S\delta$, the
direction of $c_S - o$, as in [Lemma 10](common.md#lemma-10-charts) (2).
$\square$

A square centred at $o$ gets no arc from this lemma; the next proposition
deals with it.

*Lean: [`Five.containing_arc`](../../SquaresInCircles/Five/Containing.lean#L17),
[`SquareChart.ray_mem`](../../SquaresInCircles/Common/Charts.lean#L59),
[`arcFromChartInterval`](../../SquaresInCircles/Common/Charts.lean#L164).*

#### Proposition 5.8 (a centred square)

If five pairwise disjoint squares $S$ all have $(a_S, b_S) \in P_5$, one of
them is centred at $o$.

*Proof.* Suppose none is. Every $(a_S, b_S)$ lies in the octagon $P_8$.

- A containing square is not centred at $o$, so its sweep holds an arc of
  half-width $\frac\pi5$ (Lemma 5.7).
- Every exterior square holds more than that (Lemma 5.6).

This contradicts
[Proposition 15](common.md#proposition-15-budget-with-a-sweep) with $n = 5$
and $r = \frac56$. $\square$

*Lean:
[`Five.centered_square`](../../SquaresInCircles/Five/Uniqueness.lean#L42).*

### Step 4. The plus

*Idea.* The 12-gon keeps every centre within 1 of $o$, while disjointness
keeps the other centres at least 1 from the centred square. So they are
side-neighbours of it.

#### Lemma 5.9 (the 12-gon lies in the unit disk)

If $a, b \ge 0$ and $(a, b) \in P_5$, then $a^2 + b^2 \le 1$.

![The part with a, b at least 0 of the 12-gon P5, inside the quarter of the unit circle, touching it at (1, 0) and (0, 1)](figures/dodecagon-disk.svg)

*The 12-gon stays inside the unit circle $a^2 + b^2 = 1$ and touches it only at
$(1, 0)$ and $(0, 1)$.*

*Proof.* If $a + b \le 1$, then $a^2 + b^2 \le (a + b)^2 \le 1$. Otherwise
$s = a + b$ lies in $(1, \frac75)$, since $\sqrt5 - 1 < \frac75$, and the
octagon gives $|a - b| \le 3 - 2s$. Then

```math
2\left(a^2 + b^2\right) = s^2 + (a - b)^2 \le s^2 + (3 - 2s)^2 = 2 + (5s - 7)(s - 1) < 2 . \qquad \square
```

*Lean:
[`Five.dodecagon_norm_le`](../../SquaresInCircles/Five/Uniqueness.lean#L25).*

#### Proposition 5.10 (the 12-gon is rigid)

If five pairwise disjoint squares $S$ all have $(a_S, b_S) \in P_5$, they
have the normal form of $c_1, \dots, c_5$.

The statement mentions no disk, which makes it stronger than uniqueness for
the packing problem.

*Proof.*

1. **A centred square.** By Proposition 5.8 some square $S_0$ has
   $c_{S_0} = o$.
2. **Unit contacts.** By Lemma 5.9 and
   [Lemma 1](common.md#lemma-1-farthest-vertex), every centre is within 1 of
   $o$. By [Lemma 4](common.md#lemma-4-centres-at-least-1-apart) every other
   centre is at least 1 from $c_{S_0} = o$, so exactly 1. By
   [Lemma 6](common.md#lemma-6-squares-at-distance-1), each of the other four
   squares has sides parallel to those of $S_0$ and shares a full edge with
   it.
3. **The plus.** In the frame of $S_0$, the square $S_0$ sits at $(0, 0)$ and
   the other four at $(\pm1, 0)$ and $(0, \pm1)$
   ([Lemma 18](common.md#lemma-18-sitting-at-a-centre) (1)).
   [Lemma 19](common.md#lemma-19-from-slots-to-a-normal-form) gives the normal
   form. No angle has to be computed. $\square$

*Lean:
[`Five.polygon_uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L53).*

*Proof of Proposition 5.2.* By Lemma 1 and Lemma 5.4, $(a_S, b_S) \in P_5$ for
every square $S$; apply Proposition 5.10. $\square$

*Lean: [`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L82).*

Proposition 5.1 and [Lemma 21](common.md#lemma-21-normal-forms-of-a-packing)
give the converse: every configuration with this normal form is a packing in
the closed disk of radius $R_5$.

## The lower bound

### Corollary 5.11 (lower bound)

If five pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R \ge R_5$.

*Proof.* The corner $(\frac32, \frac12)$ of $Q(c_2)$ lies on the circle of
radius $R_5$ (Proposition 5.1). Proposition 5.2 and
[Lemma 22](common.md#lemma-22-the-lower-bound) give $R \ge R_5$. $\square$

*Lean: [`Five.optimum`](../../SquaresInCircles/Five/Uniqueness.lean#L92),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48).*