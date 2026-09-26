# Four squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 4.** Let $R_4 = \sqrt2$, and let $c_1, \dots, c_4$ be the points
$(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$,
$(\frac12, -\frac12)$.

1. $Q(c_1), \dots, Q(c_4)$ form a packing in the closed disk of radius $R_4$
   about the origin: the $2 \times 2$ block.
2. A packing of four unit squares in a closed disk of radius $R$ forces
   $R \ge R_4$.
3. The packings of four unit squares in a closed disk of radius $R_4$ are
   exactly the configurations with the normal form of $c_1, \dots, c_4$. In
   particular the disk centre is a vertex of every square.

![The 2 by 2 block in its dashed circle of radius root 2, with the circle of radius 1/2 about the centre divided into four coloured quarter arcs, one in each square](figures/four.svg)

*The block. The circle $\Gamma_{1/2}$ about the disk centre $o$
splits into four quarter circles, one in each square.*

*Sketch.* The work is in part 3; part 2 follows from it, since a corner of the
block lies on the circle of radius $\sqrt2$. Take a packing in the closed disk
of radius $\sqrt2$, and draw the circle $\Gamma_{1/2}$ about the disk centre.
Every square holds at least a quarter of it: a square whose closed square
contains the centre holds the quarter that faces its own centre, and a square
that avoids the centre holds more than a quarter unless the centre is one of
its vertices. Four such arcs fit only if the disk centre is a vertex of every
square, and then the four quarter circles form the block.

Unlike three and five squares, this case keeps the disk constraint
$\varphi(a_S, b_S) \le 2$ next to its contact polygon throughout: the exterior
arcs need it, and so does the equality case, because the polygon alone is not
rigid.

*Lean:
[`Four.model_packing`](../../SquaresInCircles/Four/Construction.lean#L28),
[`Four.uniqueness`](../../SquaresInCircles/Four/Uniqueness.lean#L69),
[`Four.optimum`](../../SquaresInCircles/Four/Uniqueness.lean#L117),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48), in
[`SquaresInCircles/Four/`](../../SquaresInCircles/Four).*

## Construction

### Proposition 4.1 (attainment)

$Q(c_1), \dots, Q(c_4)$ are pairwise disjoint and lie in the closed disk of
radius $\sqrt2$ about the origin.

*Proof.* Any two of the centres differ by 1 in one coordinate, and every
centre $(x, y)$ has $(|x| + \frac12)^2 + (|y| + \frac12)^2 = 1 + 1 = 2$. Apply
[Lemma 17](common.md#lemma-17-axis-parallel-squares). $\square$

The four outer corners, $(\pm1, \pm1)$, lie on the circle.

*Lean:
[`Four.model_packing`](../../SquaresInCircles/Four/Construction.lean#L28),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## Uniqueness

### Proposition 4.2 (uniqueness)

If four pairwise disjoint unit squares lie in the closed disk of radius
$\sqrt2$ about $o$, the packing has the normal form of $c_1, \dots, c_4$.

The proof takes three steps.

1. **The diamond.** The disk puts $(a_S, b_S)$ in the diamond $a + b \le 1$
   for every square $S$, on its edge only when $o$ is a vertex of $S$.
2. **Arcs of the squares.** Every square holds at least a quarter of
   $\Gamma_{1/2}$, and a square that avoids $o$ holds more unless $o$ is one of
   its vertices. So $o$ is a vertex of every square.
3. **The block.** The four quarter circles lie on a quarter grid of
   directions, and that gives the block.

*Lean: [`Four.uniqueness`](../../SquaresInCircles/Four/Uniqueness.lean#L69).*

### Step 1. The diamond

#### Lemma 4.3 (the diamond)

If $\varphi(a, b) \le 2$, then $a + b \le 1$, with equality only at
$a = b = \frac12$.

![The (a, b)-plane: the disk where phi is at most 2, inside the triangle a plus b at most 1, which touches it at (1/2, 1/2); dashed, the larger octagon](figures/diamond.svg)

*The diamond $a + b \le 1$, where $a, b \ge 0$: the tangent half-plane at
$(\frac12, \frac12)$, which touches the disk only there. Dashed, for
comparison, the octagon $P_8$ of five squares.*

*Proof.* In the block every square has $(a_S, b_S) = (\frac12, \frac12)$, on
$\varphi = 2$, and expanding gives

```math
\varphi(a, b) - 2 = 2(a + b - 1) + \left(a - \tfrac12\right)^2 + \left(b - \tfrac12\right)^2 ,
```

the identity of [Lemma 2](common.md#lemma-2-tangent-lines) at
$(\frac12, \frac12)$. So $a + b \le 1$, and $a + b = 1$ forces both squares to
vanish. $\square$

We call $a + b \le 1$ the *diamond*. A square with $a_S = b_S = \frac12$ has
$o$ as a vertex.

*Lean: [`Four.diamond`](../../SquaresInCircles/Four/Exterior.lean#L16).*

### Step 2. Arcs of the squares

#### Lemma 4.4 (exterior arcs)

Let $S$ be exterior with $\varphi(a_S, b_S) \le 2$. Then $S$ holds an arc of
$\Gamma_{1/2}$ of half-width at least $\frac\pi4$, and more than $\frac\pi4$
unless $a_S + b_S = 1$.

*Proof.* On $\Gamma_{1/2}$ the crossing angles of $S$
([Definition 16](common.md#definition-16-crossing-angles)) are

```math
A_S = \arccos(2a_S - 1), \qquad V_S = \arcsin(1 - 2b_S) .
```

If $a_S \ge \frac56$ then $\varphi(a_S, b_S) \ge (\frac43)^2 + \frac14 > 2$, so
$a_S < \frac56$ and $a_S - \frac12 < \frac12$. With
$b_S \le 1 - a_S \le \frac12$ (Lemma 4.3),
[Lemma 12](common.md#lemma-12-arcs-of-an-exterior-square) (2) applies: $S$
holds its cap, of half-width $\frac12(A_S + \min(A_S, V_S))$.

- $2a_S - 1 < \frac23 < \frac{\sqrt2}2 = \cos\frac\pi4$, so
  $A_S > \frac\pi4 > \frac\pi2 - A_S$.
- $a_S + b_S \le 1$ gives $2a_S - 1 \le 1 - 2b_S$, so
  $\frac\pi2 - A_S = \arcsin(2a_S - 1) \le V_S$, and strictly if
  $a_S + b_S < 1$.

So $\min(A_S, V_S) \ge \frac\pi2 - A_S$, and the half-width is at least
$\frac\pi4$, strictly if $a_S + b_S < 1$. $\square$

This is where the disk matters: the diamond alone allows $a_S$ up to 1, and at
$a_S = 1$ the cap shrinks to nothing.

*Lean: [`Four.exterior_arc`](../../SquaresInCircles/Four/Exterior.lean#L24).*

#### Lemma 4.5 (a quarter circle at the disk centre)

If $a_S \le \frac12$ and $b_S \le \frac12$, that is, if $o$ lies in the closed
square $\overline{S}$, then $S$ holds the arc of $\Gamma_{1/2}$ of half-width
$\frac\pi4$ centred at $\mu_S = \theta_S + \varepsilon_S\frac\pi4$.

![A tilted square with a vertex at o, the quarter of the circle of radius 1/2 between its two edges from o highlighted, and the bisecting direction mu_S dashed](figures/vertex-square.svg)

*A square with a vertex at $o$. Its two edges from $o$ point in the directions
$\mu_S \pm \frac\pi4$, and $S$ holds the quarter of $\Gamma_{1/2}$ between
them.*

*Proof.* For $0 < t < \frac\pi2$ both coordinates of the chart point
$(\frac12\cos t, \frac12\sin t)$ lie in $(0, \frac12)$, so they are within
$\frac12$ of $a_S$ and of $b_S$, which lie in $[0, \frac12]$. Apply
[Lemma 10](common.md#lemma-10-charts) (2). $\square$

*Lean: [`Four.quarter_arc`](../../SquaresInCircles/Four/Uniqueness.lean#L31),
[`Four.vertexMid`](../../SquaresInCircles/Four/Uniqueness.lean#L26).*

### Step 3. The block

#### Lemma 4.6 (a square with a vertex at the disk centre)

If $a_S = b_S = \frac12$, then $S$ sits at $(\frac12, \frac12)$ in the frame
$\mu_S - \frac\pi4$.

*Proof.* By [Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart), $S$
sits at $(\frac12, \varepsilon_S\frac12)$ in the frame $\theta_S$. If
$\varepsilon_S = 1$, this is the claim, since $\theta_S = \mu_S - \frac\pi4$.
If $\varepsilon_S = -1$, then $\theta_S = (\mu_S - \frac\pi4) + \frac\pi2$, and
a quarter turn ([Lemma 18](common.md#lemma-18-sitting-at-a-centre) (2)) moves
$(\frac12, -\frac12)$ to $(\frac12, \frac12)$ in the frame
$\mu_S - \frac\pi4$. $\square$

*Lean:
[`Four.vertex_represents`](../../SquaresInCircles/Four/Uniqueness.lean#L45).*

*Proof of Proposition 4.2.* Every square $S$ has $\varphi(a_S, b_S) \le 2$
([Lemma 1](common.md#lemma-1-farthest-vertex)).

1. **Every square holds at least a quarter circle.** A square that contains
   $o$ has $a_S, b_S < \frac12$, and holds a quarter of $\Gamma_{1/2}$ by
   Lemma 4.5. A square that avoids $o$ holds more than a quarter unless
   $a_S + b_S = 1$ (Lemma 4.4).
2. **The disk centre is a vertex of every exterior square.** By the angular
   budget ([Lemma 7](common.md#lemma-7-angular-budget)), no square holds more
   than a quarter. So every exterior square has $a_S + b_S = 1$, hence
   $a_S = b_S = \frac12$ (Lemma 4.3).
3. **No square contains $o$.** Some square $T$ is exterior, since two disjoint
   squares cannot both contain $o$. By step 2, $o$ is a vertex of $T$, so it
   lies in $\overline{T}$, and then in no other open square
   ([Lemma 5](common.md#lemma-5-supporting-line) (2)). It does not lie in
   $T^\circ$ either, since $T$ is exterior.
4. **The block.** So $o$ is a vertex of all four squares, and by Lemma 4.5
   each square $S$ holds the quarter arc of $\Gamma_{1/2}$ centred at $\mu_S$.
   These arcs are disjoint, so their centres are pairwise at least
   $\frac\pi2$ apart
   ([Lemma 8](common.md#lemma-8-disjoint-arcs-have-separated-centres)), and
   they are $\mu_0 + k\frac\pi2$ for some $\mu_0$
   ([Lemma 20](common.md#lemma-20-regular-polygons)). In the frame
   $\mu_0 - \frac\pi4$ each square sits at $(\frac12, \frac12)$ turned by its
   $k$ quarter turns (Lemmas 4.6 and 18 (2)), which is one of
   $c_1, \dots, c_4$.
   [Lemma 19](common.md#lemma-19-from-slots-to-a-normal-form) gives the
   normal form. $\square$

*Lean: [`Four.uniqueness`](../../SquaresInCircles/Four/Uniqueness.lean#L69),
[`exists_exterior`](../../SquaresInCircles/Common/ArcBudget.lean#L15),
[`closed_open_disjoint`](../../SquaresInCircles/Common/Support.lean#L108),
[`regular_polygon`](../../SquaresInCircles/Common/Angles.lean#L40),
[`represents_quarter`](../../SquaresInCircles/Common/Angles.lean#L78).*

Proposition 4.1 and [Lemma 21](common.md#lemma-21-normal-forms-of-a-packing)
give the converse: every configuration with this normal form is a packing in
the closed disk of radius $R_4$.

## The lower bound

### Corollary 4.7 (lower bound)

If four pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R \ge \sqrt2$.

*Proof.* The corner $(1, 1)$ of $Q(c_1)$ lies on the circle of radius
$\sqrt2$ (Proposition 4.1). Proposition 4.2 and
[Lemma 22](common.md#lemma-22-the-lower-bound) give $R \ge \sqrt2$. $\square$

*Lean: [`Four.optimum`](../../SquaresInCircles/Four/Uniqueness.lean#L117),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48).*