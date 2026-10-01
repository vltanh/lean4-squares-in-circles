# 8. Five squares

[Contents](README.md) · [← 7. Four squares](four.md) · [9. Seven squares →](seven.md)

Five unit squares fit in a closed disk of radius $\sqrt{5/2}$ as a *plus*: one
square centred at the disk centre and its four side-neighbours. This chapter
proves that no smaller closed disk holds five unit squares, and that every
packing of five unit squares in a closed disk of radius $\sqrt{5/2}$ is
congruent to the plus.

The proof again measures arcs of a circle about the disk centre, now the
circle $\Gamma_{5/6}$ of radius $\frac56$. Every square that avoids the disk
centre holds more than a fifth of this circle. The square that contains the
disk centre, if there is one, may hold much less, but its radial sweep holds a
fifth unless the square is centred exactly at the disk centre. Five such arcs
do not fit on the circle, so some square is centred at the disk centre. The
other four have their centres within distance 1 of the disk centre and at
least 1 from the centred square, so they are its side-neighbours. Unlike the
cases of three and four squares, the argument uses the disk only through a
closed polygon of tangent lines, a 12-gon, and so it proves a stronger
rigidity statement, Proposition 8.6.

## Theorem 8.1 (five squares)

Let $R_5 = \sqrt{5/2}$, and let the *plus* be the model
$Q(c_1), \dots, Q(c_5)$ with $c_1 = (0, 0)$, $c_2 = (1, 0)$, $c_3 = (0, 1)$,
$c_4 = (-1, 0)$ and $c_5 = (0, -1)$.

1. The plus is a packing in the closed disk of radius $R_5$ about the origin.
2. If five unit squares form a packing in a closed disk of radius $R$, then
   $R \ge R_5$.
3. The packings of five unit squares in a closed disk of radius $R_5$ are
   exactly the configurations congruent to the plus.

![The plus in its dashed circle of radius root of 5/2, with the circle of radius 5/6 about the centre; each outer square holds a coloured arc of about 74 degrees, and the grey centre square holds none](figures/five.svg)

*Figure 8.1.* The plus in the circle of radius $R_5$ (dashed), with the circle
$\Gamma_{5/6}$ about the disk centre $o$. Each outer square holds an arc of
about 74° of $\Gamma_{5/6}$, a little more than a fifth of the circle; the
centre square (grey) holds none.

*Lean:
[`Five.model_packing`](../../SquaresInCircles/Five/Construction.lean#L21),
[`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L88),
[`Five.optimum`](../../SquaresInCircles/Five/Uniqueness.lean#L98).*

*Outline of the proof.* Part (1) is the construction, Proposition 8.2 (§8.1).
Parts (2) and (3) follow, by
[Corollary 2.10](preliminaries.md#corollary-210-the-scheme-of-proof) (§8.6),
from the uniqueness statement, Proposition 8.3: every packing of five unit
squares in a closed disk of radius $R_5$ is congruent to the plus. Its proof
takes four steps.

1. *The contact polygon* (§8.2). The disk puts the offsets $(a_S, b_S)$ of
   every square $S$ in a 12-gon $P_5$ (Lemma 8.5). From then on only the
   12-gon and the disjointness of the squares are used: Proposition 8.6 states
   that five disjoint squares with offsets in $P_5$ are congruent to the plus.
   The 12-gon keeps every centre within distance 1 of the disk centre
   (Lemma 8.7).
2. *Exterior squares* (§8.3). On the circle $\Gamma_{5/6}$, every square that
   avoids the disk centre holds an arc of more than a fifth of the circle
   (Lemma 8.10).
3. *A centred square* (§8.4). The radial sweep of a square that contains the
   disk centre holds a fifth of $\Gamma_{5/6}$, unless the square is centred at
   the disk centre (Lemma 8.11). The angular budget then forces some square to
   be centred at the disk centre (Proposition 8.12).
4. *The plus* (§8.5). The other centres are within distance 1 of the disk
   centre (Lemma 8.7), while disjointness keeps them at least 1 from the
   centred square. So they are at distance exactly 1 from it, and they are
   its side-neighbours.

## 8.1 Construction

### Proposition 8.2 (construction)

The plus is a packing in the closed disk of radius $R_5 = \sqrt{5/2}$ about the
origin.

*Proof.* Any two of the centres $c_1, \dots, c_5$ differ by at least 1 in one
coordinate. The centre $c_1 = (0, 0)$ has
$(0 + \frac12)^2 + (0 + \frac12)^2 = \frac12 \le \frac52$, and each of the
other four centres $(x, y)$ has

```math
\left(|x| + \tfrac12\right)^2 + \left(|y| + \tfrac12\right)^2 = \tfrac94 + \tfrac14 = \tfrac52 .
```

[Lemma 2.8](preliminaries.md#lemma-28-axis-parallel-squares) (3) applies.
$\square$

*Lean:
[`Five.model_packing`](../../SquaresInCircles/Five/Construction.lean#L21),
[`Five.model`](../../SquaresInCircles/Geometry.lean#L177),
[`Five.centers`](../../SquaresInCircles/Geometry.lean#L174),
[`Five.radius`](../../SquaresInCircles/Geometry.lean#L170).*

The eight outer corners, $(\pm\frac32, \pm\frac12)$ and
$(\pm\frac12, \pm\frac32)$, lie on the circle of radius $R_5$.

## 8.2 The 12-gon

The rest of the chapter, up to §8.6, proves that the optimal packing is unique.

### Proposition 8.3 (uniqueness)

Every packing of five unit squares in a closed disk of radius $R_5$ is
congruent to the plus.

The proof occupies §8.2 to §8.5. Throughout, $o$ is the disk centre, and for a
square $S$ the numbers $a_S \ge b_S \ge 0$ are the offsets of $o$ from $S$
([Definition 3.1](common.md#definition-31-position-of-the-disk-centre)). By
[Lemma 3.4](common.md#lemma-34-farthest-vertex), a square whose closed square
lies in the closed disk of radius $R_5$ about $o$ has
$\varphi(a_S, b_S) \le \frac52$. This section replaces this curved constraint
by a polygon, and reduces Proposition 8.3 to a statement about the polygon
alone, Proposition 8.6, which Lemma 8.7 and §8.3 to §8.5 prove.

### Definition 8.4 (the 12-gon)

$P_5$ is the set of points $(a, b)$ of the plane with

```math
3a + b \le 3, \qquad a + 3b \le 3, \qquad a + b \le \sqrt5 - 1 .
```

The first two inequalities are the tangent half-planes of the disk
$\lbrace\varphi \le \frac52\rbrace$ at $(1, 0)$ and $(0, 1)$
([Definition 3.5](common.md#definition-35-tangent-half-plane)): indeed
$\varphi(1, 0) = \frac94 + \frac14 = \frac52$, and at $(1, 0)$ the inequality
of Definition 3.5 reads $\frac32(a - 1) + \frac12 b \le 0$, that is
$3a + b \le 3$; the point $(0, 1)$ is its mirror image. The outer squares of
the plus have $(a_S, b_S) = (1, 0)$. The third is the
tangent half-plane at $(g, g)$, where $g = \frac{\sqrt5 - 1}2$ and
$\varphi(g, g) = 2(g + \frac12)^2 = \frac52$. No square of the plus has these
offsets, but §8.3 needs this side (Figure 8.7). The set $P_5$ is symmetric in
$a$ and $b$, and restoring the signs of the two local coordinates of $o$ turns
its three sides into twelve (Figure 8.3), hence the name.

![The part with a, b at least 0 of the 12-gon P5, around the disk where phi is at most 5/2, touching it at (1, 0), (0, 1) and (g, g)](figures/twelve-gon.svg)

*Figure 8.2.* The part of $P_5$ where $a, b \ge 0$, around the disk
$\lbrace\varphi \le \frac52\rbrace$, which it touches at $(1, 0)$, $(0, 1)$ and
$(g, g)$. Its third side cuts off the corner $(\frac34, \frac34)$ where the
first two meet.

![The plane of the local coordinates of o in the frame of a square S, with S drawn in grey at the centre: a blue rounded region where S fits in the disk of radius root of 5/2, inside an orange 12-gon with vertices at (1, 0), (0, 1), (-1, 0), (0, -1) and eight corners in between, inside the dashed octagon of the first two inequalities; dots mark the twelve points where the 12-gon touches the blue region](figures/five-twelve-gon-plane.svg)

*Figure 8.3.* The same constraints in the plane of the local coordinates
$(x_S(o), y_S(o))$ of the disk centre, with the square $S$ itself in grey. If
the closed square $\overline S$ lies in the closed disk of radius $R_5$ about
$o$, then $o$ lies in the blue region,
$\varphi(|x_S(o)|, |y_S(o)|) \le \frac52$. The 12-gon (orange) contains that
region; dashed, the octagon cut out by the first two inequalities alone.

*Lean: [`Five.P5`](../../SquaresInCircles/Five/Exterior.lean#L18),
[`Five.p5_swap`](../../SquaresInCircles/Five/Exterior.lean#L30).*

### Lemma 8.5 (contact polygon)

If $a$ and $b$ are real numbers with $\varphi(a, b) \le \frac52$, then
$(a, b) \in P_5$.

*Proof.* The points $(1, 0)$, $(0, 1)$ and $(g, g)$ satisfy
$\varphi = \frac52$, so [Lemma 3.6](common.md#lemma-36-tangent-lines) puts
$(a, b)$ in the tangent half-plane at each of them:

```math
\tfrac32(a - 1) + \tfrac12 b \le 0, \qquad \tfrac12 a + \tfrac32(b - 1) \le 0, \qquad \tfrac{\sqrt5}2\left(a + b - 2g\right) \le 0 ,
```

where the third uses $g + \frac12 = \frac{\sqrt5}2$. Multiplying by $2$, $2$
and $\frac2{\sqrt5}$ gives the three inequalities of $P_5$, since
$2g = \sqrt5 - 1$. $\square$

*Lean: [`Five.p5_of_phi`](../../SquaresInCircles/Five/Exterior.lean#L21).*

From here on only the polygon and the disjointness of the squares are used.

### Proposition 8.6 (the 12-gon is rigid)

Let $o$ be a point, and let $S_1, \dots, S_5$ be pairwise disjoint unit squares
such that $(a_{S_i}, b_{S_i}) \in P_5$ for every $i$, the offsets being those
of $o$. Then $S_1, \dots, S_5$, with disk centre $o$, are congruent to the
plus.

The statement mentions no disk. It gives Proposition 8.3 at once (see the end
of §8.5), and together with
[Lemma 2.7](preliminaries.md#lemma-27-congruent-configurations) and
Proposition 8.2 it shows that five disjoint squares with offsets in $P_5$ lie
in the closed disk of radius $R_5$ about $o$. Its proof occupies the rest of
this section and §8.3 to §8.5.

### Lemma 8.7 (the 12-gon lies in the unit disk)

If $a, b \ge 0$ and $(a, b) \in P_5$, then $a^2 + b^2 \le 1$. So every
square $S$ with $(a_S, b_S) \in P_5$ has its centre within distance 1 of $o$:
$|c_S - o|^2 = a_S^2 + b_S^2 \le 1$, by
[Lemma 3.4](common.md#lemma-34-farthest-vertex).

![The part with a, b at least 0 of the 12-gon P5, inside the quarter of the unit circle, touching it at (1, 0) and (0, 1)](figures/dodecagon-disk.svg)

*Figure 8.4.* The part of $P_5$ where $a, b \ge 0$ stays inside the unit
circle $a^2 + b^2 = 1$, and touches it only at $(1, 0)$ and $(0, 1)$. The
first two sides alone would not: they meet at $(\frac34, \frac34)$, where
$a^2 + b^2 = \frac98$.

*Proof.* Let $s = a + b$. If $s \le 1$, then
$a^2 + b^2 \le a^2 + b^2 + 2ab = s^2 \le 1$. Otherwise
$1 < s \le \sqrt5 - 1 < \frac75$, since $(\frac{12}5)^2 = \frac{144}{25} > 5$.
The first two inequalities of $P_5$ read $2s + (a - b) \le 3$ and
$2s - (a - b) \le 3$, so $|a - b| \le 3 - 2s$, where
$3 - 2s > 3 - \frac{14}5 > 0$. Hence

```math
2\left(a^2 + b^2\right) = s^2 + (a - b)^2 \le s^2 + (3 - 2s)^2 = 2 + (5s - 7)(s - 1) < 2 ,
```

because $s - 1 > 0 > 5s - 7$. $\square$

*Lean:
[`Five.dodecagon_norm_le`](../../SquaresInCircles/Five/Uniqueness.lean#L25),
[`Five.center_norm_le`](../../SquaresInCircles/Five/Uniqueness.lean#L43).*

## 8.3 Exterior squares

In this section and the next, $\Gamma_{5/6}$ is the circle of radius $\frac56$
about $o$, and the crossing angles of an exterior square $S$
([Definition 3.23](common.md#definition-323-crossing-angles)) are taken on it:

```math
A_S = \arccos\tfrac65\left(a_S - \tfrac12\right), \qquad V_S = \arcsin\tfrac65\left(\tfrac12 - b_S\right), \qquad U_S = \arcsin\tfrac65\left(b_S + \tfrac12\right) .
```

Recall that the arcsine is extended by $\frac\pi2$ above 1 and by
$-\frac\pi2$ below $-1$, and that $\arccos z = \frac\pi2 - \arcsin z$ (§2.1).
We first bound a sum of arcsines, then the length of the arc of an exterior
square.

### Lemma 8.8 (an arcsine sum)

Let $x$ and $y$ be real numbers with $0 \le x \le \frac12$,
$-\frac12 \le y \le \frac12$, $x + y \le \frac{237}{1000}$ and
$3x + y \le 1$. Then

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 < \tfrac\pi{10} .
```

![The (x, y)-plane with x from 0 to 1/2 and y from -1/2 to 1/2: the region of the lemma is a quadrilateral with vertices (0, -1/2), (1/2, -1/2), the crossing of the lines 3x + y = 1 and x + y = 237/1000, and (0, 237/1000). It is split into three shaded pieces, (i) where y is at least 0, (ii) where y is negative and x at most 23/60, and (iii) where y is negative and x more than 23/60; an orange curve, where the arcsine sum equals pi/10, runs just above the region](figures/five-arcsine-region.svg)

*Figure 8.5.* The region of Lemma 8.8 in the $(x, y)$-plane, split into the
three cases of the proof, and the curve (orange) on which
$\arcsin\frac{6x}5 + \arcsin\frac{6y}5 = \frac\pi{10}$. The region lies below
the curve. Case (iii) needs the side $3x + y \le 1$: without it the lemma
would fail near $x = \frac12$, where the curve passes below the line
$x + y = \frac{237}{1000}$ (dotted).

*Proof.* Since $\pi > 3.14$, we have $\frac\pi{10} > \frac{157}{500}$, and it
suffices to show that the sum is less than $\frac{157}{500}$. For
$0 \le z \le \frac12$ we have $0 \le \frac{6z}5 \le \frac35$, and
[Lemma 3.29](common.md#lemma-329-elementary-estimates) (3) gives

```math
\arcsin\tfrac{6z}5 \le \tfrac{6z}5 + \tfrac14\left(\tfrac{6z}5\right)^3 = \tfrac65 z + \tfrac{54}{125}z^3 . \tag{8.1}
```

We use (8.1) for $z = x$ and distinguish three cases.

(i) *$y \ge 0$.* Then (8.1) holds for $z = y$ as well. Put $s = x + y$, so
that $0 \le s \le \frac{237}{1000} < \frac14$. Since
$x^3 + y^3 = s^3 - 3xys \le s^3$,

```math
\begin{aligned}
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 &\le \tfrac65 s + \tfrac{54}{125}\left(x^3 + y^3\right) \le \tfrac65 s + \tfrac{54}{125}s^3 \\
&< \tfrac65\cdot\tfrac{237}{1000} + \tfrac{54}{125}\cdot\tfrac1{64} = \tfrac{711}{2500} + \tfrac{27}{4000} = \tfrac{5823}{20000} < \tfrac{157}{500} .
\end{aligned}
```

In the other two cases $y < 0$, so $-\frac35 \le \frac{6y}5 < 0$, and
Lemma 3.29 (2) gives $\arcsin\frac{6y}5 \le \frac{6y}5$. With (8.1) for
$z = x$,

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 \le \tfrac65(x + y) + \tfrac{54}{125}x^3 . \tag{8.2}
```

Let $q = \frac{23}{60}$, so that

```math
\tfrac{54}{125}q^3 = \tfrac{54}{125}\cdot\tfrac{12167}{216000} = \tfrac{12167}{500000} .
```

(ii) *$y < 0$ and $x \le q$.* By $x + y \le \frac{237}{1000}$ and
$x^3 \le q^3$, the right side of (8.2) is at most

```math
\tfrac{711}{2500} + \tfrac{12167}{500000} = \tfrac{154367}{500000} < \tfrac{157000}{500000} = \tfrac{157}{500} .
```

(iii) *$y < 0$ and $x > q$.* Now we use $3x + y \le 1$, that is,
$x + y \le 1 - 2x$: the right side of (8.2) is at most $h(x)$, where
$h(z) = \frac65(1 - 2z) + \frac{54}{125}z^3$. Factoring $x^3 - q^3$,

```math
h(q) - h(x) = \tfrac{12}5(x - q) - \tfrac{54}{125}\left(x^3 - q^3\right) = (x - q)\left(\tfrac{12}5 - \tfrac{54}{125}\left(x^2 + qx + q^2\right)\right) .
```

Both $x$ and $q$ lie in $(0, \frac12]$, so $x^2 + qx + q^2 \le \frac34$, and
the second factor is at least $\frac{12}5 - \frac{81}{250} > 0$. As $x > q$,
this gives $h(x) < h(q)$, and since $1 - 2q = \frac7{30}$,

```math
h(q) = \tfrac65\cdot\tfrac7{30} + \tfrac{12167}{500000} = \tfrac7{25} + \tfrac{12167}{500000} = \tfrac{152167}{500000} < \tfrac{157}{500} . \qquad \square
```

*Lean: [`Five.arcsin_sum`](../../SquaresInCircles/Five/Exterior.lean#L40),
[`Five.aux`](../../SquaresInCircles/Five/Exterior.lean#L33).*

### Lemma 8.9 (the arc length)

Let $a$ and $b$ be real numbers with $a \ge \frac12$, $0 \le b \le a$ and
$(a, b) \in P_5$, and put

```math
A = \arccos\tfrac65\left(a - \tfrac12\right), \qquad V = \arcsin\tfrac65\left(\tfrac12 - b\right), \qquad U = \arcsin\tfrac65\left(b + \tfrac12\right) .
```

Then

```math
\min(A, U) + \min(A, V) > \tfrac{2\pi}5 .
```

*Proof.* From $3a + b \le 3$ and $b \ge 0$ we get $a \le 1$. Put
$x = a - \frac12$ and $y = b - \frac12$. Then $0 \le x \le \frac12$ and, as
$0 \le b \le a \le 1$, $-\frac12 \le y \le \frac12$. Since
$\arccos z = \frac\pi2 - \arcsin z$ and the arcsine is odd,

```math
A = \tfrac\pi2 - \arcsin\tfrac{6x}5, \qquad V = -\arcsin\tfrac{6y}5 .
```

The number $\min(A, U) + \min(A, V)$ is one of the four sums $2A$, $A + V$,
$U + A$ and $U + V$. We show that each of them exceeds $\frac{2\pi}5$.

1. *$2A > \frac{2\pi}5$.* By
   [Lemma 3.29](common.md#lemma-329-elementary-estimates) (5),
   $0 \le \frac{6x}5 \le \frac35 < \frac{1 + \sqrt5}4 = \cos\frac\pi5$, the
   middle inequality because $\sqrt5 > \frac75$. The arccosine is strictly
   decreasing on $[-1, 1]$, so $A > \arccos(\cos\frac\pi5) = \frac\pi5$.
2. *$A + V > \frac{2\pi}5$.* Here
   $A + V = \frac\pi2 - (\arcsin\frac{6x}5 + \arcsin\frac{6y}5)$, and
   Lemma 8.8 applies: $x + y = a + b - 1 \le \sqrt5 - 2 < \frac{237}{1000}$ by
   the third side of $P_5$ (as $2237^2 = 5004169 > 5 \cdot 10^6$), and
   $3x + y = 3a + b - 2 \le 1$ by the first. So the sum of arcsines is less
   than $\frac\pi{10}$, and $A + V > \frac\pi2 - \frac\pi{10} = \frac{2\pi}5$.
3. *$A + U \ge \frac\pi2$.* As $a \le 1$, we have
   $b + \frac12 \ge \frac12 \ge a - \frac12$, and the arcsine is
   nondecreasing, so $U \ge \arcsin\frac65(a - \frac12) = \frac\pi2 - A$.
4. *$U + V > \frac{2\pi}5$.* If $b + \frac12 \ge \frac56$, then
   $\frac65(b + \frac12) \ge 1$ and $U = \frac\pi2$, while $A \le \frac\pi2$
   because $\frac{6x}5 \ge 0$; so $U + V \ge A + V > \frac{2\pi}5$ by step 2.
   Otherwise $b < \frac13$, and the numbers $u = \frac65(b + \frac12)$ and
   $v = \frac65(\frac12 - b)$ lie in $[0, 1]$, with
   $\frac{u + v}2 = \frac35 > \sin\frac\pi5$ (Lemma 3.29 (5)). Lemma 3.29 (4),
   with $\theta = \frac\pi5$, gives
   $\frac{2\pi}5 < \arcsin u + \arcsin v = U + V$. $\square$

*Lean: [`Five.arc_length`](../../SquaresInCircles/Five/Exterior.lean#L64).*

*Remark.* Only two of the four sums occur. Since $b \ge 0$ and $a \le 1$,

```math
V \le \arcsin\tfrac35 < \tfrac\pi4 < \arccos\tfrac35 \le A ,
```

because $\frac35 < \frac{\sqrt2}2$. So $\min(A, V) = V$, and the length is
$A + V$ or $U + V$, according as the circle leaves the square at the top
through the near edge or through the upper edge (Figure 8.6). Bounding all
four sums spares us deciding which.

![Two panels in chart coordinates, each with the circle of radius 5/6 about o and the dashed lines of the near, lower and upper edges of an exterior square. Left: the square centred at (0.8, 0.4); its highlighted arc runs from the lower edge at minus V to the near edge at A, and the upper edge is above the circle. Right: the square centred at (1, 0); its arc runs from the lower edge at minus V to the upper edge at U, and the near edge crossings at plus and minus A, in grey, lie beyond the arc](figures/five-arc-cases.svg)

*Figure 8.6.* The two cases that occur, in charts on $\Gamma_{5/6}$. Left,
$(a_S, b_S) = (0.8, 0.4)$: the upper edge is out of reach, so
$U_S = \frac\pi2$, and the arc runs from the lower edge at $-V_S$ to the near
edge at $A_S$; its length is $A_S + V_S$. Right, $(a_S, b_S) = (1, 0)$, an
outer square of the plus: the arc runs from $-V_S$ to the upper edge at $U_S$,
before the near edge is reached at $A_S$ (grey); its length is $U_S + V_S$.

### Lemma 8.10 (exterior arcs)

Let $S$ be an exterior square with $(a_S, b_S) \in P_5$. Then $S$ holds an arc
of $\Gamma_{5/6}$ of half-width greater than $\frac\pi5$.

*Proof.* As $S$ is exterior, $a_S \ge \frac12$
([Lemma 3.21](common.md#lemma-321-charts) (1)); moreover
$0 \le b_S \le a_S$, and $a_S \le 1$ by $3a_S + b_S \le 3$. So
$a_S - \frac12 \le \frac12 < \frac56 < 1 \le a_S + \frac12$, and
[Lemma 3.24](common.md#lemma-324-arcs-of-an-exterior-square) (1) applies on
$\Gamma_{5/6}$: $S$ holds an arc of $\Gamma_{5/6}$ of length
$\min(A_S, U_S) + \min(A_S, V_S)$, provided that this number is positive. The
crossing angles $A_S, V_S, U_S$ are the numbers $A, V, U$ of Lemma 8.9 for
$(a, b) = (a_S, b_S)$, so this length exceeds $\frac{2\pi}5$, and the arc has
half-width greater than $\frac\pi5$. $\square$

*Lean: [`Five.exterior_arc`](../../SquaresInCircles/Five/Exterior.lean#L111).*

Unlike the circle $\Gamma_{1/2}$ of Chapter 7, the circle $\Gamma_{5/6}$ can
leave an exterior square through its upper edge, so we use the general arc of
Lemma 3.24 (1) rather than the cap. The third side of $P_5$ is needed here. At
the point $(\frac34, \frac34)$, where the first two sides meet,
$A = \arccos\frac3{10}$,
$V = -\arcsin\frac3{10}$ and $U = \frac\pi2$, so the arc of Lemma 3.24 (1) has
length $\frac\pi2 - 2\arcsin\frac3{10}$, less than $\frac{2\pi}5$ because
$\arcsin\frac3{10} \ge \frac3{10} > \frac\pi{20}$ (Figure 8.7).

![Two panels in chart coordinates with the circle of radius 5/6 about o. Left: the square centred at (3/4, 3/4), whose arc on the circle, between the lines of its near and lower edges, spans about 55 degrees. Right: the square centred at the corner of the 12-gon, about (0.88, 0.35), whose arc spans about 72.8 degrees](figures/five-third-side.svg)

*Figure 8.7.* Why $P_5$ has a third side. Left: a square at
$(\frac34, \frac34)$, where the first two sides meet, holds only about 55° of
$\Gamma_{5/6}$,
less than a fifth of the circle. Right: at the corner of $P_5$, where
$3a + b = 3$ meets $a + b = \sqrt5 - 1$, it holds about 72.8°, just more than
a fifth.

## 8.4 A centred square

### Lemma 8.11 (the sweep holds a fifth of the circle)

Let $S$ be a square with $o \in S^\circ$ and $c_S \ne o$. Then the radial sweep
$\widehat S$ ([Definition 3.25](common.md#definition-325-radial-sweep)) holds
an arc of $\Gamma_{5/6}$ of half-width $\frac\pi5$.

*Idea of the proof.* Slide $S$ away from $o$ along the ray through its centre
until the centre is at distance $\frac1{\sqrt2}$ from $o$. The slid square lies
in $\widehat S$, and its inscribed disk covers a fifth of $\Gamma_{5/6}$, even
when $S$ itself does not reach the circle (see the figure of
Definition 3.25).

![A square containing o, slid outward along the ray from o through its centre until its centre c* is at distance 1 over root 2 from o; the inscribed disk of the slid square covers a highlighted fifth of the circle of radius 5/6](figures/slid-disk.svg)

*Figure 8.8.* The slid copy of $S$, centred at $c^*$, and its inscribed disk.
The disk covers the arc of $\Gamma_{5/6}$ of half-width $\frac\pi5$ about the
direction of $c_S - o$.

![Three panels in chart coordinates, each with a square containing o centred at (0.06, 0.035), (0.3, 0.12) and (0.44, 0.38) respectively, its radial sweep shaded as a band running away from o, a dashed slid copy centred at distance 1 over root 2 from o with its inscribed disk, and the circle of radius 5/6 with a highlighted arc of half-width pi/5 inside that disk](figures/five-sweep-positions.svg)

*Figure 8.9.* The construction for three positions of a containing square,
drawn in its chart, with the radial sweep shaded. However close $c_S$ is to
$o$, the slid copy (dashed) has its centre at distance $\frac1{\sqrt2}$ from
$o$, and its inscribed disk covers the fifth of $\Gamma_{5/6}$ about the
direction of $c_S$.

*Proof.* Fix a chart $(\theta_S, \varepsilon_S)$ of $S$
([Lemma 3.21](common.md#lemma-321-charts)).

1. *The centre in polar form.* As $o \in S^\circ$, $b_S \le a_S < \frac12$
   (Lemma 3.21 (1)). By [Lemma 3.4](common.md#lemma-34-farthest-vertex),
   $|c_S - o|^2 = a_S^2 + b_S^2$, which is positive since $c_S \ne o$. So
   $(a_S, b_S) = \ell(\cos\delta, \sin\delta)$ for
   $\ell = (a_S^2 + b_S^2)^{1/2}$ and some real $\delta$, and
   $0 < \ell^2 < \frac14 + \frac14 = \frac12$.
2. *Sliding.* Put $m = \frac1{\sqrt2\,\ell} - 1$, which is positive, so that
   $(1 + m)(a_S, b_S) = c^*$, where
   $c^* = \frac1{\sqrt2}(\cos\delta, \sin\delta)$. For a real $t$ let
   $p_t = \frac56(\cos t, \sin t)$. If both coordinates of $p_t - c^*$ are
   less than $\frac12$ in absolute value, then by the chart
   condition ([Definition 3.20](common.md#definition-320-chart)) with
   $r = \frac56$ and this $m$, the point
   $o + \frac56 u(\theta_S + \varepsilon_S t) - m(c_S - o)$ lies in $S^\circ$.
   Then the point $o + \frac56 u(\theta_S + \varepsilon_S t)$ of
   $\Gamma_{5/6}$ lies in $S^\circ + m(c_S - o)$, which is part of
   $\widehat S$.
3. *The estimate.* Let $|t - \delta| \le \frac\pi5$. Expanding, and using
   $\cos t\cos\delta + \sin t\sin\delta = \cos(t - \delta)$,

   ```math
   |p_t - c^*|^2 = \tfrac{25}{36} + \tfrac12 - 2\cdot\tfrac56\cdot\tfrac1{\sqrt2}\cos(t - \delta) = \tfrac{43}{36} - \tfrac53\cdot\tfrac1{\sqrt2}\cos(t - \delta) .
   ```

   The cosine is even and decreasing on $[0, \pi]$, so by
   [Lemma 3.29](common.md#lemma-329-elementary-estimates) (5),
   $\cos(t - \delta) \ge \cos\frac\pi5 = \frac{1 + \sqrt5}4$. Moreover
   $\frac1{\sqrt2}\cdot\frac{1 + \sqrt5}4 > \frac{17}{30}$, because both
   sides are positive and

   ```math
   \left(\tfrac1{\sqrt2}\cdot\tfrac{1 + \sqrt5}4\right)^2 = \tfrac{6 + 2\sqrt5}{32} = \tfrac{3 + \sqrt5}{16} > \tfrac{3 + 11/5}{16} = \tfrac{13}{40} > \tfrac{289}{900} = \left(\tfrac{17}{30}\right)^2 ,
   ```

   as $\sqrt5 > \frac{11}5$ and $13 \cdot 900 = 11700 > 11560 = 40 \cdot 289$.
   Hence

   ```math
   |p_t - c^*|^2 < \tfrac{43}{36} - \tfrac53\cdot\tfrac{17}{30} = \tfrac{43}{36} - \tfrac{17}{18} = \tfrac14 .
   ```

   So $|p_t - c^*| < \frac12$, both coordinates of $p_t - c^*$ are less than
   $\frac12$ in absolute value, and by step 2 the point of $\Gamma_{5/6}$ in
   the direction $\theta_S + \varepsilon_S t$ lies in $\widehat S$.
4. *The arc.* Let $\theta$ be a direction with
   $d(\theta, \theta_S + \varepsilon_S\delta) < \frac\pi5$. Then
   $\theta = \theta_S + \varepsilon_S\delta + s$ for a real $s$ with
   $|s| < \frac\pi5$, that is, $\theta = \theta_S + \varepsilon_S t$ with
   $t = \delta + \varepsilon_S s$ and $|t - \delta| < \frac\pi5$. By step 3,
   $o + \frac56 u(\theta)$ lies in $\widehat S$. So $\widehat S$ holds the arc
   of $\Gamma_{5/6}$ with centre $\theta_S + \varepsilon_S\delta$ and
   half-width $\frac\pi5$. (In the chart, the centre of $S$ is the point
   $(a_S, b_S)$ at the chart angle $\delta$, so this centre is the direction
   of $c_S - o$.) $\square$

*Lean: [`Five.containing_arc`](../../SquaresInCircles/Five/Containing.lean#L17),
[`SquareChart.ray_mem`](../../SquaresInCircles/Common/Charts.lean#L59),
[`arcFromChartInterval`](../../SquaresInCircles/Common/Charts.lean#L164).*

A square centred at $o$ gets no arc from this lemma, and none from its sweep
either: then $\widehat S = S^\circ$, which lies in the open disk of radius
$\frac{\sqrt2}2 < \frac56$ about $o$ and misses $\Gamma_{5/6}$. The next
proposition shows that five squares with offsets in $P_5$ must include such a
square.

### Proposition 8.12 (a centred square)

Let $o$ be a point, and let $S_1, \dots, S_5$ be pairwise disjoint unit squares
such that $(a_{S_i}, b_{S_i}) \in P_5$ for every $i$. Then one of them is
centred at $o$.

![Left: a circle with five coloured arcs laid end to end, four of more than 72 degrees and a fifth of 72 degrees drawn slightly outside, which overlaps the first; the overlap is marked. Right: the plus with the circle of radius 5/6 about o, the four outer squares holding coloured arcs, and the four short gaps between the arcs marked in black](figures/five-budget.svg)

*Figure 8.10.* Left: the contradiction in the proof. Four arcs of more than a
fifth of the circle and one of a fifth, laid end to end, overrun the circle, so
the five sets that hold them cannot be pairwise disjoint. Right: in the plus
the four outer squares hold arcs of about 73.7° each, and the four gaps between
them add up to about 65°, less than a fifth; the fifth square is centred at
$o$ and holds no arc.

*Proof.* Suppose that no $S_i$ is centred at $o$. Every $(a_{S_i}, b_{S_i})$
lies in $P_5$, so every centre is within distance 1 of $o$ (Lemma 8.7). At
most one of the squares contains $o$; if $S_i$ does, it is not centred at $o$,
so its sweep holds an arc of $\Gamma_{5/6}$ of half-width $\frac\pi5$
(Lemma 8.11). Every exterior square holds an arc of $\Gamma_{5/6}$ of
half-width greater than $\frac\pi5$ (Lemma 8.10). By
[Proposition 3.28](common.md#proposition-328-budget-with-a-sweep), with
$n = 5$ and $r = \frac56$, these two conditions cannot both hold, a
contradiction. $\square$

*Lean:
[`Five.centered_square`](../../SquaresInCircles/Five/Uniqueness.lean#L49).*

## 8.5 The plus

We now finish the proof of Proposition 8.6.

![Two panels around a grey square S_k centred at o, with the dashed unit circle about o. Left: a green square centred on the unit circle in a diagonal direction of S_k, turned to face o, overlaps S_k in a shaded triangle. Right: the plus turned by 20 degrees, its four outer squares centred on the unit circle and joined to o by radii](figures/five-unit-contacts.svg)

*Figure 8.11.* The last step of the proof of Proposition 8.6, around a square
$S_k$ centred at $o$, with the unit circle about $o$ dashed. Left: a square
whose centre is at distance 1 from $o$ but not on an axis of $S_k$ overlaps
$S_k$. Right: the squares at distance 1 that do not overlap $S_k$ are its
side-neighbours, and four of them form the plus.

*Proof of Proposition 8.6.* Let $S_1, \dots, S_5$ be as in the proposition.

1. *A centred square.* By Proposition 8.12, some square, say $S_k$, has
   $c_{S_k} = o$.
2. *Unit contacts.* Let $i \ne k$. By Lemma 8.7, $|c_{S_i} - o| \le 1$, and
   by [Lemma 3.10](common.md#lemma-310-centres-at-least-1-apart),
   $|c_{S_i} - c_{S_k}| \ge 1$. As $c_{S_k} = o$, this gives
   $|c_{S_i} - c_{S_k}| = 1$, and by
   [Lemma 3.13](common.md#lemma-313-squares-at-distance-1) the square $S_i$
   has its sides parallel to those of $S_k$, and $c_{S_i} - c_{S_k}$ is one of
   $\pm e^{S_k}_1$, $\pm e^{S_k}_2$ (Figure 8.11).
3. *The plus.* Let $\phi$ be the direction of $e^{S_k}_1$. By
   [Lemma 3.30](common.md#lemma-330-sitting-at-a-centre) (1), in the frame
   $\phi$ the square $S_k$ sits at the coordinates of $c_{S_k} - o = 0$ in
   the frame of $S_k$, that is, at $(0, 0) = c_1$; and every $S_i$ with
   $i \ne k$, whose sides are parallel to those of $S_k$, sits at the
   coordinates of $c_{S_i} - o$ in the frame of $S_k$. By step 2 these are
   $(1, 0)$, $(0, 1)$, $(-1, 0)$ or $(0, -1)$, that is, one of
   $c_2, \dots, c_5$. So each of the five squares sits at one of
   $c_1, \dots, c_5$ in the frame $\phi$, and
   [Lemma 3.31](common.md#lemma-331-from-slots-to-congruence), which uses only
   that the squares are pairwise disjoint, shows that they are congruent to the
   plus. No angle has to be computed. $\square$

*Lean:
[`Five.polygon_uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L61).*

*Proof of Proposition 8.3.* Let $S_1, \dots, S_5$ be a packing of five unit
squares in the closed disk of radius $R_5$ about $o$. The squares are pairwise
disjoint, and for every $i$, Lemma 3.4 gives
$\varphi(a_{S_i}, b_{S_i}) \le R_5^2 = \frac52$, so
$(a_{S_i}, b_{S_i}) \in P_5$ by Lemma 8.5. Proposition 8.6 applies. $\square$

*Lean: [`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L88).*

## 8.6 Proof of Theorem 8.1

*Proof of Theorem 8.1.* We apply
[Corollary 2.10](preliminaries.md#corollary-210-the-scheme-of-proof) with
$n = 5$, $R_5 = \sqrt{5/2}$ and $\mathcal M = \lbrace\text{the plus}\rbrace$:
(a) is Proposition 8.2; (b) the corner $(\frac32, \frac12)$ of $Q(c_2)$ has
$\frac94 + \frac14 = \frac52 = R_5^2$; (c) is Proposition 8.3. Parts (1),
(2), (3) of the theorem are (a), (i) and (ii). $\square$

*Lean: [`Five.optimum`](../../SquaresInCircles/Five/Uniqueness.lean#L98),
[`Optimum.isLeast`](../../SquaresInCircles/Common/Optimum.lean#L61),
[`Optimum.packing_iff`](../../SquaresInCircles/Common/Optimum.lean#L67).*
