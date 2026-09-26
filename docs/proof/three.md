# Three squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 3.** Let $R_3 = \frac{5\sqrt{17}}{16}$, and let
$c_1 = (-\frac12, -\frac5{16})$, $c_2 = (\frac12, -\frac5{16})$,
$c_3 = (0, \frac{11}{16})$.

1. $Q(c_1), Q(c_2), Q(c_3)$ form a packing in the closed disk of radius $R_3$
   about the origin: the T, two squares side by side and a third centred on
   top of them.
2. A packing of three unit squares in a closed disk of radius $R$ forces
   $R \ge R_3$.
3. The packings of three unit squares in a closed disk of radius $R_3$ are
   exactly the configurations with the normal form of $c_1, c_2, c_3$.

![The T packing in its dashed circle of radius 5 root 17 over 16, with the small circle of radius 3/8 about the centre divided into three coloured arcs of 120 degrees, one in each square](figures/three.svg)

*The T. The small circle $\Gamma_{3/8}$ about the disk centre $o$
splits into three arcs of exactly 120°, one in each square.*

*Sketch.* The work is in part 3; part 2 follows from it, since a corner of the
T lies on the circle of radius $R_3$. Take a packing in the closed disk of
radius $R_3$, and draw the small circle $\Gamma_{3/8}$ about the disk centre.
Every square that avoids the centre holds at least a third of that circle, and
exactly a third only in the two positions of the squares of the T. A square
that contains the centre leaves too little room: its own arc is nearly a
third, a clipped arc of another square would more than make up the
difference, and two unclipped arcs belong to nearly axial squares that would
overlap. So all three arcs are exactly a third, and the angles between them
rebuild the T.

*Lean:
[`Three.model_packing`](../../SquaresInCircles/Three/Construction.lean#L31),
[`Three.uniqueness`](../../SquaresInCircles/Three/Uniqueness.lean#L121),
[`Three.optimum`](../../SquaresInCircles/Three/Uniqueness.lean#L194),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48), in
[`SquaresInCircles/Three/`](../../SquaresInCircles/Three).*

## Construction

### Proposition 3.1 (attainment)

$Q(c_1), Q(c_2), Q(c_3)$ are pairwise disjoint and lie in the closed disk of
radius $R_3$ about the origin.

*Proof.* Any two of the centres differ by at least 1 in one coordinate, and
every centre $(x, y)$ has
$(|x| + \frac12)^2 + (|y| + \frac12)^2 = R_3^2$:

```math
1 + \tfrac{169}{256} = \tfrac14 + \tfrac{361}{256} = \tfrac{425}{256} = R_3^2 .
```

Apply [Lemma 17](common.md#lemma-17-axis-parallel-squares). $\square$

The six outer corners, $(\pm1, -\frac{13}{16})$ and
$(\pm\frac12, \frac{19}{16})$, lie on the circle.

*Lean:
[`Three.model_packing`](../../SquaresInCircles/Three/Construction.lean#L31),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## Uniqueness

### Proposition 3.2 (uniqueness)

If three pairwise disjoint unit squares lie in the closed disk of radius $R_3$
about $o$, the packing has the normal form of $c_1, c_2, c_3$.

The proof takes four steps.

1. **The contact polygon.** The disk puts $(a_S, b_S)$ in a 16-gon $P_3$ for
   every square $S$.
2. **Exterior squares.** Each square that avoids $o$ holds a cap of at least a
   third of $\Gamma_{3/8}$, and exactly a third only in two positions, the
   positions of the squares of the T.
3. **The containing square.** A square that contains $o$ leaves the other two
   too little room, so all three squares are exterior.
4. **The T.** The three caps are exactly a third each. That leaves one square
   in the upper position of the T and two in the lower one, and the angles
   between the caps rebuild the T.

*Lean: [`Three.uniqueness`](../../SquaresInCircles/Three/Uniqueness.lean#L121).*

### Step 1. The contact polygon

#### Definition 3.3 (the 16-gon)

For $b \le a$, the point $(a, b)$ lies in $P_3$ if

```math
16a + 13b \le \tfrac{193}{16}, \qquad 19a + 8b \le \tfrac{209}{16} .
```

These are the tangent half-planes of $\varphi = \frac{425}{256}$ at
$(\frac12, \frac5{16})$ and at $(\frac{11}{16}, 0)$. In the T, the two lower
squares have $(a_S, b_S) = (\frac12, \frac5{16})$ and the upper one has
$(a_S, b_S) = (\frac{11}{16}, 0)$. Their mirror images in the diagonal
$a = b$ bound the part with $a \le b$, and restoring the signs of the two
local coordinates of $o$ turns these four lines into sixteen. The proofs only
meet points with $b_S \le a_S$.

![The part with a, b at least 0 of the 16-gon P3 in the (a, b)-plane, hugging the disk where phi is at most 425/256; the disk touches it at the points A, (11/16, 0) and (0, 11/16), and B, (1/2, 5/16) and (5/16, 1/2)](figures/sixteen-gon.svg)

*The 16-gon $P_3$ where $a, b \ge 0$. It touches the disk
$\lbrace \varphi \le \frac{425}{256} \rbrace$ at the positions of the squares of
the T, marked with their types (Lemma 3.5).*

*Lean: [`Three.P3`](../../SquaresInCircles/Three/Exterior.lean#L18), the two
inequalities.*

#### Lemma 3.4 (contact polygon)

If $b \le a$ and $\varphi(a, b) \le \frac{425}{256}$, then $(a, b) \in P_3$.
If moreover $a < \frac12$, then $16a + 13b < \frac{193}{16}$.

*Proof.* [Lemma 2](common.md#lemma-2-tangent-lines) at the two tangent
points, strictly at $(\frac12, \frac5{16})$ when $a \ne \frac12$. $\square$

From here on the proof uses only the polygon, this strict inequality and the
disjointness of the squares; the disk is not needed again.

*Lean: [`Three.p3_of_phi`](../../SquaresInCircles/Three/Exterior.lean#L21),
[`tangent_lt`](../../SquaresInCircles/Common/Tangents.lean#L26).*

### Step 2. Exterior squares

#### Lemma 3.5 (exterior caps)

Let $S$ be exterior with $(a_S, b_S) \in P_3$, and let $A_S$ and $V_S$ be its
crossing angles on $\Gamma_{3/8}$
([Definition 16](common.md#definition-16-crossing-angles)).

1. $\frac\pi3 \le A_S \le \frac\pi2$, and $A_S = \frac\pi3$ only at
   $(a_S, b_S) = (\frac{11}{16}, 0)$, *type A*: $o$ lies on an axis of $S$.
2. $A_S + V_S \ge \frac{2\pi}3$, and $A_S + V_S = \frac{2\pi}3$ only at
   $(a_S, b_S) = (\frac12, \frac5{16})$, *type B*: $o$ lies on the line of an
   edge of $S$.
3. $S$ holds its cap on $\Gamma_{3/8}$
   ([Lemma 12](common.md#lemma-12-arcs-of-an-exterior-square) (2)), of
   half-width $\frac12(A_S + \min(A_S, V_S)) \ge \frac\pi3$.

These are the two kinds of square in the T.

![Left: a type A square in its chart, centred on the axis through o, holding a third of the circle of radius 3/8. Right: a type B square with o on the line of its left edge, holding a third of that circle and half of the circle of radius 1/16](figures/contact-types.svg)

*The two tight cases, each in its chart. Each square holds exactly a third of
$\Gamma_{3/8}$. The type B square also holds half of $\Gamma_{1/16}$, which
Step 4 uses.*

*Idea.* The 16-gon keeps $S$ close enough to $o$ that its cap is long. The
two terms of the cap length are each at least $\frac{2\pi}3$, and each is
tight for one type.

*Proof.* Put

```math
u_S = \frac{a_S - \frac12}{3/8}, \qquad v_S = \frac{\frac12 - b_S}{3/8}, \qquad A_S = \arccos u_S, \qquad V_S = \arcsin v_S .
```

The polygon gives three facts:

- $19a + 8b \le \frac{209}{16}$ at $(a_S, b_S)$, with $b_S \ge 0$, gives
  $a_S \le \frac{11}{16}$, that is $u_S \le \frac12$;
- the facet $16a + 13b \le \frac{193}{16}$ at $(a_S, b_S)$ rewrites exactly as
  $v_S \ge \frac12 + \frac{16}{13}u_S$;
- the same facet with $a_S \ge \frac12$ gives $b_S \le \frac5{16}$.

(1) $0 \le u_S \le \frac12$ gives $\frac\pi3 \le A_S \le \frac\pi2$. If
$A_S = \frac\pi3$, then $u_S = \frac12$, so $a_S = \frac{11}{16}$, and the
facet $19a + 8b \le \frac{209}{16}$ leaves $b_S = 0$.

(2) $A_S + V_S \ge \frac{2\pi}3$ says $\arcsin v_S \ge \arcsin u_S + \frac\pi6$,
since $A_S = \frac\pi2 - \arcsin u_S$. This holds because

```math
\sin\left(\arcsin u_S + \tfrac\pi6\right) = \tfrac{\sqrt3}2\,u_S + \tfrac12\sqrt{1 - u_S^2}
\le \tfrac12 + u_S \le \tfrac12 + \tfrac{16}{13}u_S \le v_S .
```

If $A_S + V_S = \frac{2\pi}3$, the chain is tight. Its middle step
$u_S \le \frac{16}{13}u_S$ is tight only at $u_S = 0$, and then $v_S = \frac12$:
$(a_S, b_S) = (\frac12, \frac5{16})$.

(3) Here $a_S - \frac12 \le \frac3{16} < \frac38$ and
$b_S \le \frac5{16} < \frac12$, so Lemma 12 (2) applies with $r = \frac38$.
Its cap has half-width $\frac12(A_S + \min(A_S, V_S))$, at least $\frac\pi3$ by
(1) and (2). $\square$

*Lean: [`Three.truncated_gap`](../../SquaresInCircles/Three/Exterior.lean#L29),
[`Three.cap_bounds`](../../SquaresInCircles/Three/Exterior.lean#L63),
[`Three.exterior_cap`](../../SquaresInCircles/Three/Exterior.lean#L85).*

### Step 3. The containing square

This step rules out a square containing $o$. It is the hardest part of the
whole project; the radial sweep that handles five squares gives too short an
arc here.

*Idea.* The containing square $S$ holds a quarter of $\Gamma_{3/8}$ and a bit
more, less than $\frac1{12}$ short of a third. Each of the other two squares
holds at least a third. So the three arcs nearly fill the circle, and that
leaves no freedom:

- neither of the other caps can be clipped, or it would more than make up the
  deficit (Lemma 3.9);
- both caps are then symmetric about their squares' phases, and at most
  $\frac\pi3 + \frac1{24}$ in half-width, so both squares are nearly of type A;
- their phases are less than $\frac{2\pi}3 + \frac1{12}$ apart, but on the
  larger circle $\Gamma_{7/16}$ two nearly axial squares hold arcs too wide
  for that (Lemma 3.10).

Throughout this step, $S$ contains $o$, so $b_S \le a_S < \frac12$. Put

```math
P_S = \frac{\frac12 - a_S}{3/8}, \qquad Q_S = \frac{\frac12 - b_S}{3/8}, \qquad 0 < P_S \le Q_S .
```

(As in mathlib, $\arcsin x = \frac\pi2$ for $x \ge 1$.)

#### Lemma 3.6 (the arc of a containing square)

$S$ holds an arc of $\Gamma_{3/8}$ of length

```math
L_S = \tfrac\pi2 + \arcsin P_S + \arcsin Q_S .
```

![A square containing o in its chart, centred at (a_S, b_S), and the highlighted arc of the circle of radius 3/8 inside it, running from its lower edge round to its left edge](figures/containing-arc.svg)

*The arc of length $L_S$ runs from the lower edge of $S$ round to its left edge;
the far edges are out of reach.*

*Proof.* In the chart of $S$, the circle point at angle $t$ is
$(\frac38\cos t, \frac38\sin t)$. It lies in $S$ as soon as
$\cos t > -P_S$ and $\sin t > -Q_S$, because the far edges, at
$a_S + \frac12$ and $b_S + \frac12$, are out of reach. Both hold for
$-\arcsin Q_S < t < \frac\pi2 + \arcsin P_S$. For $t \le \frac\pi2$ the sine
increases, so $\sin t > -Q_S$, and for $t > \frac\pi2$ the sine is positive,
since $t < \frac\pi2 + \arcsin P_S \le \pi$. The cosine is the sine of
$\frac\pi2 - t$, which lies in the same kind of interval with $P_S$ and $Q_S$
exchanged. [Lemma 10](common.md#lemma-10-charts) (2) turns the interval into
an arc. $\square$

The arc is the quarter circle facing the centre of $S$, extended a little on
each side.

*Lean: [`Three.neg_lt_sin`](../../SquaresInCircles/Three/Containing.lean#L24),
[`Three.containing_mem`](../../SquaresInCircles/Three/Containing.lean#L36),
[`Three.containing_arc`](../../SquaresInCircles/Three/Containing.lean#L49).*

#### Lemma 3.7 (the radial gap)

Let $T$ be exterior and disjoint from $S$, with $b_T \le \frac12$. Then

```math
\tfrac12 - a_S \le a_T - \tfrac12 .
```

That is: the near edge of $T$ is at least as far from $o$ as the inscribed disk
of $S$ about $o$ reaches.

![A containing square S with the shaded disk of radius one half minus a_S about o inside it, and a square T to its right; below, the radius of the disk and the distance from o to the near edge of T are compared](figures/radial-gap.svg)

*The disk of radius $\frac12 - a_S$ about $o$ lies in $S$, and so does every
circle about $o$ inside it. The near edge of $T$, at distance $a_T - \frac12$
from $o$, cannot come closer.*

*Proof.* Suppose $a_T - \frac12 < \frac12 - a_S$, and let
$\rho = \frac12(a_T - a_S)$, which lies strictly between the two.

- $S$ holds an arc of $\Gamma_\rho$ of half-width $\pi$: in the chart of $S$,
  the point $(\rho\cos t, \rho\sin t)$ is within $\rho + a_S < \frac12$ of
  $(a_S, b_S)$ in both coordinates, since $b_S \le a_S$.
- $T$ holds a cap of $\Gamma_\rho$ of positive length (Lemma 12 (2)), since
  $a_T - \frac12 < \rho \le \frac12$ and $b_T \le \frac12$.
- Two disjoint arcs of half-widths $\pi$ and $w > 0$ would have centres more
  than $\pi$ apart
  ([Lemma 8](common.md#lemma-8-disjoint-arcs-have-separated-centres)), which
  is impossible. $\square$

*Lean:
[`Three.gap_from_containing`](../../SquaresInCircles/Three/Containing.lean#L64).*

#### Lemma 3.8 (an increasing difference)

The function

```math
f(t) = \arcsin\left(\tfrac12 + \tfrac{16}{13}t\right) - \arcsin t
```

is increasing on every interval $[t_0, t_1]$ with $t_0 \ge 0$ and
$\frac12 + \frac{16}{13}t_1 < 1$.

*Proof.* On such an interval $0 \le t < \frac12 + \frac{16}{13}t < 1$. So the
first square root below is the smaller one, and

```math
f'(t) = \frac{16/13}{\sqrt{1 - \left(\frac12 + \frac{16}{13}t\right)^2}} - \frac1{\sqrt{1 - t^2}} > 0 . \qquad \square
```

*Lean:
[`Three.asin_increment_mono`](../../SquaresInCircles/Three/Containing.lean#L89).*

#### Lemma 3.9 (compensation)

Let $0 \le P \le u$, $0 \le Q \le 1$ and $v < 1$, with

```math
\tfrac{16}{13}P + Q > \tfrac12, \qquad v \ge \tfrac12 + \tfrac{16}{13}u .
```

Then

```math
\arcsin v - \arcsin u + \arcsin P + \arcsin Q > \tfrac\pi3 .
```

*Proof.* Since $\frac12 + \frac{16}{13}u \le v < 1$, Lemma 3.8 applies on
$[P, u]$:

```math
\arcsin v - \arcsin u \ge \arcsin\left(\tfrac12 + \tfrac{16}{13}u\right) - \arcsin u \ge \arcsin\left(\tfrac12 + \tfrac{16}{13}P\right) - \arcsin P .
```

And $\arcsin(\frac12 + \frac{16}{13}P) + \arcsin Q > \frac\pi3$ by
[Lemma 16](common.md#lemma-16-elementary-estimates) (4) with
$\theta = \frac\pi6$, because the two arguments average more than
$\frac12 = \sin\frac\pi6$. $\square$

*Lean:
[`Three.compensation`](../../SquaresInCircles/Three/Containing.lean#L111).*

#### Lemma 3.10 (nearly axial squares)

1. $\cos(\frac\pi3 + \frac1{24}) > \frac9{20}$.
2. If $\frac12 \le a_T \le \frac{11}{16}$ and $b_T \le \frac1{16}$, then $T$
   holds an arc of $\Gamma_{7/16}$ of half-width more than
   $\frac\pi3 + \frac1{24}$, centred at its phase $\theta_T$.
3. Two disjoint squares $T$ and $U$ as in (2) have
   $d(\theta_T, \theta_U) > \frac{2\pi}3 + \frac1{12}$.

![Two squares T and U whose axes pass close to o, in directions an angle Delta apart; their overlap is shaded and contains the point z](figures/near-axis-overlap.svg)

*Two nearly axial squares whose phases are only a little over $\frac{2\pi}3$
apart overlap near $o$: the point $z$ lies in both.*

*Proof.* (1) With $\varepsilon = \frac1{24}$,

```math
\cos\left(\tfrac\pi3 + \varepsilon\right) = \tfrac12\cos\varepsilon - \tfrac{\sqrt3}2\sin\varepsilon \ge \tfrac12\left(1 - \tfrac{\varepsilon^2}2\right) - \varepsilon > \tfrac9{20} .
```

(2) On $\Gamma_{7/16}$ the lower edge is out of reach, since
$\frac12 - b_T \ge \frac7{16}$, so $V_T = \frac\pi2 \ge A_T$, and Lemma 12 (2)
gives a cap centred at $\theta_T$ of half-width
$A_T = \arccos\frac{a_T - 1/2}{7/16}$. Here
$\frac{a_T - 1/2}{7/16} \le \frac37 < \frac9{20}$, which is less than
$\cos(\frac\pi3 + \frac1{24})$ by (1), so $A_T > \frac\pi3 + \frac1{24}$.
(3) This is Lemma 8. $\square$

*Lean:
[`Three.cos_third_gt`](../../SquaresInCircles/Three/Containing.lean#L125),
[`Three.wide_arc`](../../SquaresInCircles/Three/Containing.lean#L135),
[`Three.axial_pair_impossible`](../../SquaresInCircles/Three/Containing.lean#L153).*

#### Proposition 3.11 (no square contains the disk centre)

If three pairwise disjoint squares $S$ all have
$\varphi(a_S, b_S) \le \frac{425}{256}$, none of them contains $o$.

*Proof.* Suppose $S$ contains $o$, and call the other two $T$ and $U$. They are
exterior, since two disjoint squares cannot both contain $o$. By Lemma 3.4 all
three have their pairs in $P_3$, and $16a_S + 13b_S < \frac{193}{16}$ since
$a_S < \frac12$; with $P = P_S$ and $Q = Q_S$ this reads

```math
\tfrac{16}{13}P + Q > \tfrac12 . \qquad (\ast)
```

Define $u_T, v_T$ for $T$ as in the proof of Lemma 3.5, and likewise for $U$.
By Lemma 3.5 the caps of $T$ and $U$ have half-widths $w_T, w_U \ge \frac\pi3$,
and by Lemma 3.6 the arc of $S$ has half-width $\frac12L_S$. The three-arc
budget ([Lemma 9](common.md#lemma-9-three-arcs)) gives

```math
\tfrac12L_S + w_T + w_U \le \pi . \qquad (\ast\ast)
```

**(a) The deficit is small.** By $(\ast\ast)$, $L_S \le \frac{2\pi}3$, so
$\arcsin Q < \frac\pi2$ and $Q < 1$. With $P \le Q$, $(\ast)$ gives
$P + Q > \frac{13}{29}$. Using $\arcsin x \ge x$ and $\pi < \frac{22}7$
(Lemma 16),

```math
L_S > \tfrac\pi2 + \tfrac{13}{29} > \tfrac{2\pi}3 - \tfrac1{12} .
```

**(b) No cap is clipped.** Suppose the cap of $T$ is clipped, $V_T < A_T$.
Then $v_T < 1$, and $2w_T = A_T + V_T = \frac\pi2 - \arcsin u_T + \arcsin v_T$.
By Lemma 3.7, which applies since $b_T \le \frac5{16}$ (proof of Lemma 3.5),
$u_T \ge P$, and the facet $16a + 13b \le \frac{193}{16}$ gives
$v_T \ge \frac12 + \frac{16}{13}u_T$. So Lemma 3.9 applies:

```math
2w_T + L_S = \pi + \left(\arcsin v_T - \arcsin u_T + \arcsin P + \arcsin Q\right) > \tfrac{4\pi}3 .
```

With $w_U \ge \frac\pi3$ this contradicts $(\ast\ast)$. So the cap of $T$ is
full: $w_T = A_T$, and it is centred at $\theta_T$ (Lemma 12 (2)). The same
holds for $U$.

**(c) Both squares are nearly of type A.** By $(\ast\ast)$ and (a),
$A_T \le \pi - \frac12L_S - \frac\pi3 < \frac\pi3 + \frac1{24}$. So
$u_T = \cos A_T > \cos(\frac\pi3 + \frac1{24}) > \frac9{20}$
(Lemma 3.10 (1)), that is
$a_T > \frac12 + \frac9{20}\cdot\frac38 = \frac{107}{160}$, and the facet
$19a + 8b \le \frac{209}{16}$ leaves $b_T < \frac{57}{1280} < \frac1{16}$.
Also $a_T \le \frac{11}{16}$. The same holds for $U$.

**(d) Their phases are close.** Lemma 9, with the arc of $S$ as the third arc,
and (a) give

```math
d(\theta_T, \theta_U) \le 2\pi - L_S - A_T - A_U \le \tfrac{4\pi}3 - L_S < \tfrac{2\pi}3 + \tfrac1{12} .
```

**(e) They overlap.** By (c), Lemma 3.10 (3) applies to $T$ and $U$ and
contradicts (d). $\square$

*Lean:
[`Three.no_containing`](../../SquaresInCircles/Three/Containing.lean#L168).*

### Step 4. The T

#### Lemma 3.12 (the two types)

Let $S$ be exterior with $(a_S, b_S) \in P_3$, and suppose its cap on
$\Gamma_{3/8}$ has half-width at most $\frac\pi3$. Then either $S$ is of
type A and its cap is centred at $\theta_S$, or $S$ is of type B and its cap
is centred at $\theta_S + \varepsilon_S\frac\pi6$.

*Proof.* If $A_S \le V_S$, the cap is full, of half-width $A_S \le \frac\pi3$,
so $A_S = \frac\pi3$ and $S$ is of type A by Lemma 3.5 (1); the cap is centred
at $\theta_S$. Otherwise its half-width $\frac12(A_S + V_S)$ is at most
$\frac\pi3$, so $A_S + V_S = \frac{2\pi}3$ and $S$ is of type B by
Lemma 3.5 (2). Then $A_S = \arccos 0 = \frac\pi2$ and $V_S = \frac\pi6$, so the
cap runs from the chart angle $-\frac\pi6$ to $\frac\pi2$, and its centre is
at $\frac\pi6$. $\square$

*Lean: [`Three.cap_types`](../../SquaresInCircles/Three/Uniqueness.lean#L27).*

#### Lemma 3.13 (the phases of the T)

Let $\phi, \psi, \chi$ be directions with $\psi = \phi + \pi$, and let
$\varepsilon, \varepsilon' = \pm1$. If the three directions
$\phi + \varepsilon\frac\pi6$, $\psi + \varepsilon'\frac\pi6$ and $\chi$ are
pairwise $\frac{2\pi}3$ apart, then $\varepsilon' = -\varepsilon$ and
$\chi = \phi - \varepsilon\frac\pi2$.

*Proof.* If $\varepsilon' = \varepsilon$, the first two directions are $\pi$
apart. So $\varepsilon' = -\varepsilon$, and with $\delta = \chi - \phi$ the
other two conditions read

```math
\tfrac{\sqrt3}2\cos\delta + \tfrac\varepsilon2\sin\delta = -\tfrac12, \qquad
-\tfrac{\sqrt3}2\cos\delta + \tfrac\varepsilon2\sin\delta = -\tfrac12 ,
```

since $\cos(\delta - \varepsilon\frac\pi6) = -\frac12$ and
$\cos(\delta - \pi + \varepsilon\frac\pi6) = -\frac12$. So $\cos\delta = 0$
and $\sin\delta = -\varepsilon$. $\square$

*Lean: [`Three.apex_phase`](../../SquaresInCircles/Three/Uniqueness.lean#L48),
[`cos_sub_distance`](../../SquaresInCircles/Common/ArcMetric.lean#L112),
[`cos_two_pi_thirds`](../../SquaresInCircles/Common/ArcMetric.lean#L118).*

#### Lemma 3.14 (where the squares sit)

1. A square $S$ of type A sits at $c_3 = (0, \frac{11}{16})$ in the frame
   $\theta_S - \frac\pi2$.
2. A square $S$ of type B sits, in the frame
   $\theta_S - \varepsilon_S\frac\pi2 - \frac\pi2$, at
   $c_1 = (-\frac12, -\frac5{16})$ if $\varepsilon_S = 1$ and at
   $c_2 = (\frac12, -\frac5{16})$ if $\varepsilon_S = -1$.

*Proof.* By [Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart), $S$
sits at $(a_S, \varepsilon_S b_S)$ in the frame $\theta_S$. (1) This is
$(\frac{11}{16}, 0)$, and in the frame turned back by a quarter turn it sits at
$(0, \frac{11}{16})$ ([Lemma 18](common.md#lemma-18-sitting-at-a-centre) (2)).
(2) This is $(\frac12, \varepsilon_S\frac5{16})$. If $\varepsilon_S = -1$ the
frame is $\theta_S$ itself, and $(\frac12, -\frac5{16}) = c_2$. If
$\varepsilon_S = 1$ the frame is $\theta_S - \pi$, and a half turn gives
$(-\frac12, -\frac5{16}) = c_1$. $\square$

*Lean:
[`Three.a_represents`](../../SquaresInCircles/Three/Uniqueness.lean#L113),
[`Three.b_represents`](../../SquaresInCircles/Three/Uniqueness.lean#L94),
[`chart_represents`](../../SquaresInCircles/Common/NormalForm.lean#L148),
[`represents_cardinal`](../../SquaresInCircles/Common/Angles.lean#L89).*

*Proof of Proposition 3.2.* Every square $S$ has $(a_S, b_S) \in P_3$
(Lemma 3.4), and by Proposition 3.11 none contains $o$. So all three are
exterior, and each holds its cap on $\Gamma_{3/8}$, of half-width at least
$\frac\pi3$ (Lemma 3.5).

1. **Every cap is exactly a third.** The half-widths add up to at most $\pi$
   ([Lemma 7](common.md#lemma-7-angular-budget)), so each is exactly
   $\frac\pi3$. By Lemma 3.12 each square is of type A or type B, with its cap
   centred as there, and by Lemma 9 the three centres are pairwise exactly
   $\frac{2\pi}3$ apart.
2. **Not two of type A.** Their caps would be centred at their phases,
   $\frac{2\pi}3$ apart, against Lemma 3.10 (3).
3. **Not three of type B.** Each would hold the half of $\Gamma_{1/16}$
   centred at its phase (Lemma 12 (3)), and three disjoint half circles break
   Lemma 9.
4. **The angles.** So one square, $S_3$, is of type A, and two, $S_1$ and
   $S_2$, are of type B; write $\theta_i = \theta_{S_i}$ and
   $\varepsilon_i = \varepsilon_{S_i}$. The half circles of $S_1$ and $S_2$ on
   $\Gamma_{1/16}$ are disjoint, so $\theta_2 = \theta_1 + \pi$ (Lemma 8). The
   caps are centred at $\theta_1 + \varepsilon_1\frac\pi6$,
   $\theta_2 + \varepsilon_2\frac\pi6$ and $\theta_3$, pairwise
   $\frac{2\pi}3$ apart, so Lemma 3.13 gives $\varepsilon_2 = -\varepsilon_1$
   and $\theta_3 = \theta_1 - \varepsilon_1\frac\pi2$.
5. **The T.** Take the frame $\theta_3 - \frac\pi2$. Since
   $\theta_i - \varepsilon_i\frac\pi2 = \theta_3$ for $i = 1, 2$, Lemma 3.14
   puts $S_3$ at $c_3$ and $S_1$ and $S_2$ at $c_1$ or $c_2$ in this frame:

   | square | phase | sits at |
   | --- | --- | --- |
   | $S_3$ (type A) | $\theta_3$ | $c_3$ |
   | $S_1$ (type B) | $\theta_3 + \varepsilon_1\frac\pi2$, sign $\varepsilon_1$ | $c_1$ if $\varepsilon_1 = 1$, $c_2$ if $\varepsilon_1 = -1$ |
   | $S_2$ (type B) | $\theta_3 - \varepsilon_1\frac\pi2$, sign $-\varepsilon_1$ | $c_2$ if $\varepsilon_1 = 1$, $c_1$ if $\varepsilon_1 = -1$ |

   [Lemma 19](common.md#lemma-19-from-slots-to-a-normal-form) gives the normal
   form. $\square$

*Lean: [`Three.uniqueness`](../../SquaresInCircles/Three/Uniqueness.lean#L121),
[`SquareChart.half_arc`](../../SquaresInCircles/Common/Charts.lean#L193),
[`OpenArc.opposite`](../../SquaresInCircles/Common/Angles.lean#L31),
[`normal_form_of_slots`](../../SquaresInCircles/Common/NormalForm.lean#L96).*

Proposition 3.1 and [Lemma 21](common.md#lemma-21-normal-forms-of-a-packing)
give the converse: every configuration with this normal form is a packing in
the closed disk of radius $R_3$.

## The lower bound

### Corollary 3.15 (lower bound)

If three pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R \ge R_3$.

*Proof.* The corner $(-1, -\frac{13}{16})$ of $Q(c_1)$ lies on the circle of
radius $R_3$ (Proposition 3.1). Proposition 3.2 and
[Lemma 22](common.md#lemma-22-the-lower-bound) give $R \ge R_3$. $\square$

*Lean: [`Three.optimum`](../../SquaresInCircles/Three/Uniqueness.lean#L194),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48).*

## The legacy certificate proof

The first formalization of this case is on the
[`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch, with its own README and axiom audit. It normalizes a packing into a
fixed angle triangle, extracts separating axes, eliminates directed-chain
patterns to leave 48 branches, and bounds a trigonometric polynomial on each
branch with 53 rational certificates checked by `decide +kernel`. Its
`Cert.optimality` proves the lower bound of Theorem 3, stated with that
branch's `Packing` for `Fin 3` and its constant `optimalRadius`.

The occupied-arc proof above replaced it as the main proof: one argument, with
no case enumeration and no certificate tables, proves uniqueness, and the
lower bound follows from it.
