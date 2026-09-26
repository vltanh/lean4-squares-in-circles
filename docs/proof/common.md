# Shared lemmas

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md)

This page is the toolkit shared by the cases. Each section defines its tools
and then proves the lemmas about them; the case pages cite both by number. The
setting (squares, packings, normal forms) is on the
[preliminaries page](preliminaries.md). Each result ends with the Lean
declarations it follows.

| section | definitions | lemmas | what it provides |
| --- | --- | --- | --- |
| [1. The disk centre seen from a square](#1-the-disk-centre-seen-from-a-square) | 6 to 8 | 1 | the disk constraint in terms of $(a_S, b_S)$ |
| [2. Contact polygons](#2-contact-polygons) | 9 to 11 | 2 | from the curved constraint to a polygon |
| [3. Two disjoint squares](#3-two-disjoint-squares) | 12 | 3 to 6 | inscribed disks, distance between centres, a separating line |
| [4. Arcs and the angular budget](#4-arcs-and-the-angular-budget) | 13, 14 | 7 to 9 | disjoint arcs share one circle |
| [5. Charts](#5-charts) | 15 | 10, 11 | a square in standard position as seen from $o$ |
| [6. Arcs of an exterior square](#6-arcs-of-an-exterior-square) | 16 | 12 | explicit arcs that an exterior square holds |
| [7. The radial sweep](#7-the-radial-sweep) | 17 | 13 to 15 | a longer arc for the square that contains $o$ |
| [8. Elementary estimates](#8-elementary-estimates) | | 16 | numerical bounds |
| [9. Axis-parallel squares](#9-axis-parallel-squares) | | 17 | checking the optimal packings |
| [10. Normal forms](#10-normal-forms) | | 18 to 22 | recognising the optimal packing; the converse and the lower bound |
| [11. One framework for every case](#11-one-framework-for-every-case) | | | the three parts of every theorem |

## 1. The disk centre seen from a square

From here on the disk centre $o$ is fixed. Whether a square fits in a disk
about $o$ depends only on where $o$ lies relative to the square, and two
numbers record that.

### Definition 6 (position of the disk centre)

For a square $S$, let

```math
a_S = \max\left(|x_S(o)|, |y_S(o)|\right), \qquad b_S = \min\left(|x_S(o)|, |y_S(o)|\right),
```

the offsets of $o$ from $c_S$ along the two axes of $S$, larger first. A
quarter turn of the frame changes neither $S$
([Definition 1](preliminaries.md#definition-1-unit-square)) nor these two
numbers, and one of the four turns puts $o$ in the closed first quadrant. We
draw squares in that frame: there both local coordinates of $o$ are
nonnegative, and they are $a_S$ and $b_S$ in some order.

![A square in its own frame, with its centre c and the disk centre o outside it, up and to the right. A path goes from c along the first axis for a distance a, then parallel to the second axis for a distance b, reaching o](figures/position.svg)

*A square in its own frame, turned so that $o$ lies in the first quadrant.
From the centre $c_S$, the disk centre $o$ is $a_S$ along one axis and $b_S$
along the other.*

*Lean: [`alpha`](../../SquaresInCircles/Common/Basic.lean#L81),
[`beta`](../../SquaresInCircles/Common/Basic.lean#L82), the two offsets in the
order of the frame. Every statement is symmetric in them, and the proofs sort
them with
[`SquareChart.transfer`](../../SquaresInCircles/Common/Charts.lean#L69).*

### Definition 7 (containing and exterior squares)

A square $S$ is *containing* if $o \in S^\circ$, that is if $a_S < \frac12$,
and *exterior* otherwise. Two disjoint squares cannot both be containing, so a
packing has at most one containing square.

![Left: a tilted square with the disk centre o inside it, labelled containing, a_S less than one half. Right: a tilted square with o outside it, labelled exterior, a_S at least one half](figures/containing-exterior.svg)

*Left, $o$ lies in $S^\circ$ and $a_S < \frac12$. Right, $o$ lies outside
$S^\circ$ and $a_S \ge \frac12$.*

*Lean: [`openSquare`](../../SquaresInCircles/Geometry.lean#L36), applied to the
disk centre;
[`exists_exterior`](../../SquaresInCircles/Common/ArcBudget.lean#L15), some
square of two or more disjoint squares is exterior.*

### Definition 8 (farthest-vertex function)

For real numbers $a$ and $b$, let

```math
\varphi(a, b) = \left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 .
```

For a square $S$, $\varphi(a_S, b_S)$ is the squared distance from $o$ to the
vertex of $S$ farthest from it
([Lemma 1](#lemma-1-farthest-vertex)).

*Lean: [`phi`](../../SquaresInCircles/Common/Basic.lean#L100).*

### Lemma 1 (farthest vertex)

For every square $S$, the vertex of $S$ farthest from $o$ is at squared
distance $\varphi(a_S, b_S)$ from $o$, and the centre is at squared distance
$a_S^2 + b_S^2$. In particular, if $\overline{S}$ lies in the closed disk of
radius $R$ about $o$, then

```math
\varphi(a_S, b_S) \le R^2 .
```

![The same square with a right triangle from o to the farthest vertex, the corner (-1/2, -1/2): a horizontal leg of length a plus one half, split where it crosses the vertical axis, a vertical leg of length b plus one half, split at the horizontal axis, and the hypotenuse of length the square root of phi(a, b)](figures/farthest-vertex.svg)

*The farthest vertex, $(-\frac12, -\frac12)$, is $a_S + \frac12$ across and
$b_S + \frac12$ down from $o$.*

*Proof.* Work in the frame of $S$ turned as in Definition 6 (figure above).
There $o = (x, y)$ with $x, y \ge 0$, and $x, y$ are $a_S, b_S$ in some
order. The vertices are $(\pm\frac12, \pm\frac12)$. The vertex
$(-\frac12, -\frac12)$, across both axes from $o$, is at squared distance
$(x + \frac12)^2 + (y + \frac12)^2 = \varphi(a_S, b_S)$, since $\varphi$ is
symmetric. No vertex is farther, because $|x \mp \frac12| \le x + \frac12$ and
$|y \mp \frac12| \le y + \frac12$. The centre is at squared distance
$x^2 + y^2 = a_S^2 + b_S^2$. $\square$

The case proofs use the disk only through this inequality, one for each
square. Every uniqueness proof starts from these inequalities and from then on
works only with the pairs $(a_S, b_S)$ and the disjointness of the squares.

*Lean: [`phi_le_of_contained`](../../SquaresInCircles/Common/Basic.lean#L109),
[`exists_signed`](../../SquaresInCircles/Common/Basic.lean#L103),
[`Packing.phi_le`](../../SquaresInCircles/Common/Basic.lean#L122),
[`local_center_norm`](../../SquaresInCircles/Common/Basic.lean#L95). The Lean
proof names the vertex across both axes by the signs of the local coordinates of
$o$ ([`exists_signed`](../../SquaresInCircles/Common/Basic.lean#L103)) instead
of turning the frame.*

## 2. Contact polygons

By Lemma 1, a packing in a disk of radius $R$ has $\varphi(a_S, b_S) \le R^2$
for every square $S$. Plot each square $S$ as the point $(a_S, b_S)$ of an
auxiliary plane with coordinates $a$ and $b$, the $(a, b)$-plane; it is not the
plane the squares lie in. There the constraint is curved: $\varphi(a, b)$ is
the squared distance from $(a, b)$ to $(-\frac12, -\frac12)$, so
$\lbrace \varphi \le K \rbrace$ is a disk. The proofs replace it by a polygon
of tangent lines.

### Definition 9 (tangent half-plane)

Let $\varphi(u, v) = K$. The *tangent half-plane* at $(u, v)$ is the side of
the tangent line to $\lbrace \varphi = K \rbrace$ at $(u, v)$ that contains
the disk $\lbrace \varphi \le K \rbrace$:

```math
\left(u + \tfrac12\right)(a - u) + \left(v + \tfrac12\right)(b - v) \le 0 .
```

![The (a, b)-plane with the disk where phi is at most K, centred at (-1/2, -1/2), a point (u, v) on its boundary circle, and the tangent line there; the shaded side of the line, which contains the disk, is the tangent half-plane](figures/tangent-half-plane.svg)

*The disk $\lbrace \varphi \le K \rbrace$ is centred at $(-\frac12, -\frac12)$.
The tangent half-plane at a boundary point $(u, v)$ contains it.*

*Lean: written out in
[`tangent_le`](../../SquaresInCircles/Common/Tangents.lean#L20) and
[`tangent_lt`](../../SquaresInCircles/Common/Tangents.lean#L26).*

### Lemma 2 (tangent lines)

For all real $a, b, u, v$,

```math
\varphi(a,b) - \varphi(u,v) = 2\left(u+\tfrac12\right)(a-u) + 2\left(v+\tfrac12\right)(b-v) + (a-u)^2 + (b-v)^2 .
```

So if $\varphi(u, v) = K$ and $\varphi(a, b) \le K$, then $(a, b)$ lies in
the tangent half-plane at $(u, v)$, and strictly inside it if $a \ne u$.

*Proof.* Expand. The last two terms are squares, hence nonnegative, and the
first of them is positive if $a \ne u$. $\square$

*Lean: [`tangent_identity`](../../SquaresInCircles/Common/Tangents.lean#L15),
[`tangent_le`](../../SquaresInCircles/Common/Tangents.lean#L20),
[`tangent_lt`](../../SquaresInCircles/Common/Tangents.lean#L26).*

### Definition 10 (contact polygon)

A *contact polygon* is an intersection of a few tangent half-planes. Each case
takes $K$ to be the square of its optimal radius, and takes the tangent points
from its optimal packing, together with their mirror images. The polygons
$P_3$ and $P_5$ of three and five squares are defined on their pages; four
squares use the single tangent half-plane at $(\frac12, \frac12)$, the diamond
$a + b \le 1$.

*Lean: [`Three.P3`](../../SquaresInCircles/Three/Exterior.lean#L18),
[`Five.P5`](../../SquaresInCircles/Five/Exterior.lean#L17),
[`Four.diamond`](../../SquaresInCircles/Four/Exterior.lean#L16).*

### Definition 11 (the octagon)

The *octagon* $P_8$ is cut out by the tangents to $\varphi = \frac52$ at
$(1, 0)$ and $(0, 1)$:

```math
P_8:\qquad 3a + b \le 3, \qquad a + 3b \le 3 .
```

Restoring the signs and the order of the two local coordinates of $o$ turns
these two lines into eight, hence the name. The 12-gon $P_5$ of five squares
lies inside it, and it keeps the radial sweep of Section 7 away from the other
squares.

![The (a, b)-plane: the disk where phi is at most 5/2, inside the octagon P8 cut out by the tangents at (1, 0) and (0, 1); a dotted third tangent cuts off the octagon corner](figures/contact-polygon.svg)

*The disk $\lbrace \varphi \le \frac52 \rbrace$ and the octagon $P_8$ (its part
with $a, b \ge 0$), cut out by the tangents at $(1, 0)$ and $(0, 1)$. The dotted
third tangent cuts off the corner; five squares add it.*

*Lean: [`P8`](../../SquaresInCircles/Common/Tangents.lean#L31).*

## 3. Two disjoint squares

### Lemma 3 (inscribed disks)

Let $S$ be a square.

1. The open disk of radius $\frac12$ about $c_S$ lies in $S^\circ$.
2. If $a_S \le \alpha$ and $b_S \le \alpha$ for some $\alpha < \frac12$, then
   the open disk of radius $\frac12 - \alpha$ about $o$ lies in $S^\circ$.

![A square with the dashed disk of radius one half about its centre c, and a smaller shaded disk of radius one half minus alpha about the point o](figures/inscribed-disks.svg)

*The disk of radius $\frac12$ about $c$, and the disk of radius
$\frac12 - \alpha$ about $o$, both inside $S$.*

*Proof.* (2) A point within $\frac12 - \alpha$ of $o$ has local coordinates
within $\frac12 - \alpha$ of those of $o$, which are at most $\alpha$ in
absolute value. (1) is (2) with $c_S$ in place of $o$, where both offsets are
0. $\square$

*Lean: [`inscribed_disk_mem`](../../SquaresInCircles/Common/Basic.lean#L128),
[`small_disk_in_openSquare`](../../SquaresInCircles/Common/Basic.lean#L144).*

### Lemma 4 (centres at least 1 apart)

If $S$ and $T$ are disjoint, then $|c_T - c_S| \ge 1$.

![Two overlapping tilted squares whose centres are less than 1 apart, with their inscribed disks and the midpoint m of the centres lying in both](figures/midpoint.svg)

*If the centres were less than 1 apart, the midpoint $m$ would lie in both
inscribed disks.*

*Proof.* Otherwise the midpoint of the two centres is within $\frac12$ of
both, and by Lemma 3 (1) it lies in both open squares. $\square$

*Lean:
[`centers_distance_sq_ge_one`](../../SquaresInCircles/Common/Contacts.lean#L74).*

### Definition 12 (width)

For a square $S$ and a vector $n$,

```math
w_S(n) = \tfrac12\left(|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle|\right) = \max_{p \in \overline{S}} \langle n,\ p - c_S\rangle ,
```

the half-width of $S$ in the direction $n$, measured in units of $|n|$.

![A tilted square, a unit direction n, and the distance from the centre c to the supporting line through the extreme vertex in that direction](figures/width.svg)

*For a unit vector $n$, the square reaches $w_S(n)$ beyond its centre in the
direction $n$.*

*Lean: [`width`](../../SquaresInCircles/Common/Separation.lean#L70).*

### Lemma 5 (supporting line)

Let $S$ and $T$ be disjoint.

1. There is a vector $n \ne 0$ with

   ```math
   w_S(n) + w_T(n) \le \langle n,\ c_T - c_S\rangle .
   ```

   In words: some line separates the two squares, and each square lies
   entirely on its own side.
2. No point of the closed square $\overline{S}$ lies in $T^\circ$.

![Two disjoint tilted squares, a dashed separating line between them, and their shadows on a line in direction n, which do not overlap](figures/shadows.svg)

*Disjoint squares have disjoint shadows in some direction $n$. Each shadow
reaches $w(n)$ on either side of the shadow of the centre.*

*Idea.* Hahn–Banach gives a separating line. Pushing test points out to the
vertices of each square shows that the line clears both squares by their full
half-widths.

*Proof.* The open squares are disjoint, open and convex, so the geometric
Hahn–Banach theorem gives a nonzero $n$ and a number $\kappa$ with

```math
\langle n, p\rangle < \kappa < \langle n, q\rangle \qquad \text{for all } p \in S^\circ,\ q \in T^\circ .
```

Fix $0 \le t < 1$. Go from $c_S$ a fraction $t$ of the way to the vertex of
$S$ that maximises $\langle n, \cdot\rangle$: this point is in $S^\circ$ and
has value $\langle n, c_S\rangle + t w_S(n)$. Do the same in $T$ with $-n$.
Then

```math
\langle n, c_S\rangle + t\,w_S(n) < \langle n, c_T\rangle - t\,w_T(n)
\qquad \text{for every } 0 \le t < 1,
```

and letting $t \to 1$ proves (1). For (2), every $p \in \overline{S}$ and
$q \in T^\circ$ satisfy

```math
\langle n, p\rangle \le \langle n, c_S\rangle + w_S(n) \le \langle n, c_T\rangle - w_T(n) < \langle n, q\rangle . \qquad \square
```

*Lean:
[`support_separator`](../../SquaresInCircles/Common/Separation.lean#L115),
[`closed_dot_bound`](../../SquaresInCircles/Common/Support.lean#L97),
[`closed_open_disjoint`](../../SquaresInCircles/Common/Support.lean#L108),
[`support_point`](../../SquaresInCircles/Common/Separation.lean#L80),
[`bound_from_shrinks`](../../SquaresInCircles/Common/Separation.lean#L104).*

### Lemma 6 (squares at distance 1)

If $S$ and $T$ are disjoint and $|c_T - c_S| = 1$, then $T$ has its sides
parallel to those of $S$ and shares a full edge with it: $c_T - c_S$ is one of
$\pm e^S_1, \pm e^S_2$.

![Two tilted squares sharing a full edge, with their centres joined by a segment of length 1](figures/edge-contact.svg)

*At distance exactly 1 the squares share a full edge.*

*Idea.* At distance exactly 1 every inequality in the separation argument
must be tight, and tightness pins down the directions.

*Proof.* Take $n$ from Lemma 5 and put $d = c_T - c_S$, a unit vector. Since
$|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle| \ge |n|$, and the same
for $T$, each width is at least $|n|/2$. Therefore

```math
|n| \le w_S(n) + w_T(n) \le \langle n, d\rangle \le |n|\,|d| = |n| ,
```

and all three inequalities are equalities.

- The last one is Cauchy–Schwarz, so $n$ is a positive multiple of $d$.
- The first one forces $|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle| = |n|$,
  and the same for $T$, which happens only when $n$ is parallel to a side.

So $d$ is parallel to a side of $S$ and to a side of $T$. $\square$

*Lean: [`unit_contact`](../../SquaresInCircles/Common/Contacts.lean#L105).*

## 4. Arcs and the angular budget

The main tool for three to five squares measures how much of a small circle
about $o$ each square covers. Disjoint squares cover disjoint parts of the
circle, and together they cannot cover more than all of it.

### Definition 13 (circles about the disk centre)

For $r > 0$, the circle of radius $r$ about $o$ is

```math
\Gamma_r = \lbrace o + r\,u(\theta) \rbrace ,
```

with its points labelled by directions. The *angle* $d(\theta, \theta')$
between two directions is their distance on the circle of directions, a number
in $[0, \pi]$.

![Two directions from o drawn as radii of the circle of radius r, the unit vector u(theta), and the angle d between the two directions](figures/directions.svg)

*Two directions $\theta, \theta'$ seen from $o$, the unit vector $u(\theta)$,
and the angle $d(\theta, \theta')$ between them.*

*Lean: [`circlePoint`](../../SquaresInCircles/Common/AngularBudget.lean#L22),
[`direction_dist`](../../SquaresInCircles/Common/AngularBudget.lean#L31).*

### Definition 14 (arc)

Let $U$ be a set in the plane. An *arc of $U$ on $\Gamma_r$*, with centre
$\theta_0$ and half-width $w \in (0, \pi]$, says that every point
$o + r u(\theta)$ with $d(\theta, \theta_0) < w$ lies in $U$. The arc need not
be all of $\Gamma_r \cap U$. When $U$ is an open square $S^\circ$, we say that
$S$ *holds* the arc.

![A circle about o and a square U; a thick arc of the circle inside U with centre direction theta zero and half-width w, and the rest of the circle inside U drawn thin](figures/arc.svg)

*An arc of $U$ with centre $\theta_0$ and half-width $w$ (thick). It need not
cover all of $\Gamma_r \cap U$ (thin).*

*Lean: [`OpenArc`](../../SquaresInCircles/Common/AngularBudget.lean#L39).*

![Four disjoint squares around the disk centre, each holding a coloured arc of the circle of radius r; the arcs do not overlap](figures/budget.svg)

*Disjoint squares hold disjoint arcs of the same circle, so the arcs
share its $2\pi$ of angle.*

### Lemma 7 (angular budget)

If the sets $U_1, \dots, U_n$ are pairwise disjoint and $U_i$ holds an arc of
half-width $w_i$ on a common circle $\Gamma_r$, then

```math
w_1 + \dots + w_n \le \pi .
```

In particular it cannot happen that every $w_i \ge \pi/n$ and one of them is
strictly larger.

*Proof.* Fix $0 \le t < 1$ and shrink every arc to half-width $t w_i$, closed.
The shrunk arcs are still pairwise disjoint, since a common direction would
put one point of $\Gamma_r$ in two of the $U_i$. Their lengths $2t w_i$ add
up to at most $2\pi$, the total length of the circle. So $t \sum w_i \le \pi$
for every $t < 1$. $\square$

Shrinking first means the proof never has to measure the endpoints of an open
arc.

*Lean:
[`open_arc_budget`](../../SquaresInCircles/Common/AngularBudget.lean#L66),
[`closed_arc_budget`](../../SquaresInCircles/Common/AngularBudget.lean#L49),
[`uniform_arc_excess`](../../SquaresInCircles/Common/AngularBudget.lean#L80).
The length is the Haar measure on $\mathbb{R}/2\pi\mathbb{Z}$.*

### Lemma 8 (disjoint arcs have separated centres)

If disjoint sets $U$ and $V$ hold arcs on the same circle with centres
$\theta_U, \theta_V$ and half-widths $w_U, w_V$, then

```math
d(\theta_U, \theta_V) \ge w_U + w_V .
```

In particular, disjoint half circles, with $w_U = w_V = \frac\pi2$, have
opposite centres: $\theta_V = \theta_U + \pi$.

![Two disjoint arcs U and V of a circle about o, with dashed radii to their centres and the angle between the centres marked as at least w_U + w_V](figures/arc-centres.svg)

*The centres of two disjoint arcs are at least $w_U + w_V$ apart.*

*Proof.* Suppose $d(\theta_U, \theta_V) < w_U + w_V$, and walk from
$\theta_U$ towards $\theta_V$ a fraction $\frac{w_U}{w_U + w_V}$ of the way.
The direction reached is less than $w_U$ from $\theta_U$ and less than $w_V$
from $\theta_V$, so its point on the circle lies in $U$ and in $V$. For half
circles this gives $d(\theta_U, \theta_V) \ge \pi$, and only opposite
directions are $\pi$ apart. $\square$

*Lean:
[`OpenArc.centers_separated`](../../SquaresInCircles/Common/ArcMetric.lean#L27),
[`OpenArc.opposite`](../../SquaresInCircles/Common/Angles.lean#L31),
[`antipodal_of_distance`](../../SquaresInCircles/Common/Angles.lean#L23).*

### Lemma 9 (three arcs)

If pairwise disjoint sets $U, V, W$ hold arcs on the same circle with centres
$\theta_U, \theta_V, \theta_W$ and half-widths $w_U, w_V, w_W$, then

```math
w_V + w_W \le d(\theta_V, \theta_W) \le 2\pi - 2w_U - w_V - w_W ,
```

and in particular $w_U + w_V + w_W \le \pi$.

![A circle about o with three disjoint coloured arcs U, V and W, dashed radii to their centres, and the angle between the centres of V and W marked](figures/three-arcs.svg)

*The short way from $\theta_V$ to $\theta_W$ crosses half of $V$ and half of
$W$. The long way crosses those halves and all of $U$.*

*Proof.* Three points on a circle of length $2\pi$ have pairwise distances
adding up to at most $2\pi$. Bound $d(\theta_U, \theta_V)$ and
$d(\theta_U, \theta_W)$ from below by Lemma 8. $\square$

This gives the budget for three sets without measure theory, and it also
locates the centres, which the uniqueness proofs use.

*Lean:
[`OpenArc.third_distance_bounds`](../../SquaresInCircles/Common/ArcMetric.lean#L92),
[`triple_arc_budget`](../../SquaresInCircles/Common/ArcMetric.lean#L105),
[`direction_triangle_perimeter`](../../SquaresInCircles/Common/ArcMetric.lean#L67).*

## 5. Charts

To find the arcs that a square holds, turn the picture about $o$, and reflect
it if needed, until the square sits in a standard position.

### Definition 15 (chart)

A *chart* of $S$ is a direction $\theta_S$ (the *phase*) and a sign
$\varepsilon_S = \pm 1$ such that for all real $r, t, m$

```math
o + r\,u(\theta_S + \varepsilon_S t) - m\,(c_S - o) \in S^\circ
\iff
\left|r\cos t - (1+m)a_S\right| < \tfrac12 \ \text{ and } \ \left|r\sin t - (1+m)b_S\right| < \tfrac12 .
```

Take $m = 0$ first. The condition says: measure angles from $o$ as
$\theta_S + \varepsilon_S t$ and use $t$ as the angle variable (the *chart
angle*); then $S$ is the axis-parallel unit square centred at $(a_S, b_S)$.
The parameter $m$ slides $S$ away from $o$ along the ray through its centre,
and moves the centre to $(1 + m)(a_S, b_S)$.
Lemma 10 below shows that every square has a chart.

![Left: a tilted square seen from o, with the phase direction and a point on the circle at chart angle t from it. Right: the same square turned into standard position, centred at (a, b), with the point at angle t](figures/chart-panels.svg)

*Left: a square seen from $o$. Right: its chart. Turning by $-\theta_S$ (and
reflecting when $\varepsilon_S = -1$) puts the square in standard position,
centred at $(a_S, b_S)$; the point at angle $\theta_S + \varepsilon_S t$ goes
to the point at chart angle $t$.*

*Lean: [`SquareChart`](../../SquaresInCircles/Common/Charts.lean#L46),
[`chartAngle`](../../SquaresInCircles/Common/Charts.lean#L35).*

### Lemma 10 (charts)

Every square $S$ has a chart $(\theta_S, \varepsilon_S)$, and:

1. $o \in S^\circ$ exactly when $a_S < \frac12$; an exterior square has
   $a_S \ge \frac12$.
2. Suppose every chart angle $t$ in an interval $(l, h)$ of length at most
   $2\pi$ gives a point of $S$ on $\Gamma_r$, that is
   $|r\cos t - a_S| < \frac12$ and $|r\sin t - b_S| < \frac12$. Then $S$
   holds an arc of $\Gamma_r$ with half-width $\frac{h - l}2$ and centre
   $\theta_S + \varepsilon_S\frac{l + h}2$.

*Idea.* Rotate so that an axis of $S$ points along $\theta_S$, then reflect
so that the centre of $S$ lands at $(a_S, b_S)$.

*Proof.* Let $\theta$ be the direction of $e^S_1$ and write
$c_S - o = X e^S_1 + Y e^S_2$. The point $o + r\,u(\theta + t) - m(c_S - o)$
has local coordinates $(r\cos t - (1 + m)X, r\sin t - (1 + m)Y)$, so the pair
$(\theta, 1)$ satisfies the chart condition with $(X, Y)$ in place of
$(a_S, b_S)$. Three changes keep the chart condition:

- reversing the orientation changes the sign of the second coordinate
  (substitute $-t$ for $t$);
- turning the phase by $\pi$ changes the signs of both (substitute
  $t + \pi$);
- turning the phase by $\varepsilon\frac\pi2$ and reversing the orientation
  exchanges the two coordinates (substitute $\frac\pi2 - t$).

A reversal, a half turn or both make the coordinates $|X|$ and $|Y|$, and an
exchange puts the larger first; these are $a_S$ and $b_S$.

Part 1 is the chart condition at $r = m = 0$, since $b_S \le a_S$. Part 2
holds because the directions within $\frac{h - l}2$ of
$\theta_S + \varepsilon_S\frac{l + h}2$ are exactly the
$\theta_S + \varepsilon_S t$ with $t \in (l, h)$. $\square$

*Lean: [`square_chart`](../../SquaresInCircles/Common/Charts.lean#L133),
[`sorted_square_chart`](../../SquaresInCircles/Common/Charts.lean#L146),
[`frame_chart`](../../SquaresInCircles/Common/Charts.lean#L91),
[`ChartCondition.reflect`](../../SquaresInCircles/Common/Charts.lean#L99),
[`ChartCondition.turn`](../../SquaresInCircles/Common/Charts.lean#L107),
[`ChartCondition.swap`](../../SquaresInCircles/Common/Charts.lean#L119),
[`SquareChart.origin`](../../SquaresInCircles/Common/Charts.lean#L154),
[`SquareChart.exterior`](../../SquaresInCircles/Common/Charts.lean#L158),
[`SquareChart.arc`](../../SquaresInCircles/Common/Charts.lean#L182).*

### Lemma 11 (Cartesian form of a chart)

If $(\theta_S, \varepsilon_S)$ is a chart of $S$, then $S$ sits at
$(a_S, \varepsilon_S b_S)$ in the frame $\theta_S$.

*Proof.* If $\varepsilon_S = -1$, reverse the orientation as in the proof of
Lemma 10: then $(\theta_S, 1)$ satisfies the chart condition with
$(a_S, \varepsilon_S b_S)$. Write a point in polar form $(r\cos t, r\sin t)$
in the frame $\theta_S$ and apply that condition with $m = 0$. $\square$

*Lean:
[`SquareChart.cartesian`](../../SquaresInCircles/Common/Coordinates.lean#L41),
[`SquareChart.unreversed`](../../SquaresInCircles/Common/Coordinates.lean#L34),
[`chart_represents`](../../SquaresInCircles/Common/NormalForm.lean#L148).*

## 6. Arcs of an exterior square

Throughout this section $S$ is exterior, so $a_S \ge \frac12$, and $\Gamma_r$
is a circle about $o$.

### Definition 16 (crossing angles)

Let $S$ be exterior, and let $r > 0$ with $a_S - \frac12 \le r$. Put

```math
A_S = \arccos\frac{a_S - \frac12}{r}, \qquad V_S = \arcsin\frac{\frac12 - b_S}{r}, \qquad U_S = \arcsin\frac{b_S + \frac12}{r} ,
```

where, as in mathlib, $\arcsin x = \frac\pi2$ for $x \ge 1$. In the chart, the
circle $\Gamma_r$ crosses the line of the near edge, $x = a_S - \frac12$, at
the chart angles $\pm A_S$, and the lines of the lower and upper edges,
$y = b_S \mp \frac12$, at $-V_S$ and $U_S$ if it reaches them. The radius $r$
is fixed by context and left out of the notation.

![An exterior square in its chart. The disk centre o is at the origin and the square is centred at (a, b). The circle of radius r crosses the dashed line of the near edge at the angles plus and minus A, and the dashed line of the lower edge at minus V. The cap, the part of the circle inside the square, is highlighted from minus V to A](figures/chart.svg)

*An exterior square in its chart, with $o$ at the origin. The circle
$\Gamma_r$ crosses the line of the near edge at the angles $\pm A_S$ and the
line of the lower edge at $-V_S$; it does not reach the upper edge. The part of
the circle inside the square is highlighted: here $V_S < A_S$, so the lower
edge clips it, and it runs from $-V_S$ to $A_S$.*

*Lean: [`capA`](../../SquaresInCircles/Common/RectangleArcs.lean#L20),
[`capV`](../../SquaresInCircles/Common/RectangleArcs.lean#L21),
[`capU`](../../SquaresInCircles/Common/RectangleArcs.lean#L22).*

### Lemma 12 (arcs of an exterior square)

Let $S$ be exterior, and let $a_S - \frac12 \le r < a_S + \frac12$, so that
$\Gamma_r$ does not reach the far edge.

1. Every chart angle $t$ with $-\min(A_S, V_S) < t < \min(A_S, U_S)$ gives a
   point of $S$ on $\Gamma_r$. So $S$ holds an arc of $\Gamma_r$ of length
   $\min(A_S, U_S) + \min(A_S, V_S)$, if that is positive.
2. *The cap.* If moreover $r \le \frac12$, $a_S - \frac12 < r$ and
   $b_S \le \frac12$, then $S$ holds the arc from $-\min(A_S, V_S)$ to $A_S$,
   of length $\min(2A_S, A_S + V_S)$. If $A_S \le V_S$ this cap is centred at
   the phase $\theta_S$ and has half-width $A_S$; if $V_S < A_S$ the lower edge
   clips it.
3. *Half circles.* If $a_S = \frac12$ and $b_S + r \le \frac12$, then $S$
   holds the half of $\Gamma_r$ centred at $\theta_S$.

![An exterior square in its chart with a circle of radius 5/6 about o; the highlighted arc runs from where the circle crosses the lower edge to where it crosses the upper edge, before the near edge](figures/rectangle-interval.svg)

*On a larger circle the arc can leave through the upper edge. Here the circle
meets the lines of the lower and the upper edge before the line of the near
edge (grey dot), and the arc runs from $-V_S$ to $U_S$.*

*Proof.* (1) The bound $|t| < A_S \le \frac\pi2$ keeps the point beyond the
near edge: $r\cos t > r\cos A_S = a_S - \frac12$. The far edge is out of reach:
$r\cos t \le r < a_S + \frac12$. The sine increases on
$[-\frac\pi2, \frac\pi2]$, so $t > -V_S$ gives $r\sin t > b_S - \frac12$, and
$t < U_S$ gives $r\sin t < b_S + \frac12$. Lemma 10 (2) turns the interval
into an arc. (2) The upper edge is out of reach, since
$b_S + \frac12 \ge \frac12 \ge r$, so $U_S = \frac\pi2 \ge A_S$, and the
interval of (1) runs from $-\min(A_S, V_S)$ to $A_S$. Its midpoint is 0 when
$A_S \le V_S$. (3) Here $A_S = \arccos 0 = \frac\pi2$, and
$V_S = \frac\pi2$ because $\frac12 - b_S \ge r$: by (2), a cap of half-width
$\frac\pi2$ centred at $\theta_S$. $\square$

*Lean: [`cap_mem`](../../SquaresInCircles/Common/RectangleArcs.lean#L26),
[`SquareChart.edge_arc`](../../SquaresInCircles/Common/RectangleArcs.lean#L53),
[`SquareChart.cap_arc`](../../SquaresInCircles/Common/RectangleArcs.lean#L71),
[`SquareChart.full_cap_arc`](../../SquaresInCircles/Common/RectangleArcs.lean#L87),
[`SquareChart.half_arc`](../../SquaresInCircles/Common/Charts.lean#L193).*

## 7. The radial sweep

The square that contains $o$, if there is one, may hold only a short arc of
the auxiliary circle, or none: a square centred at $o$ holds no point of a
circle of radius more than $\frac{\sqrt2}2$ about $o$. Five squares, whose
auxiliary circle has radius $\frac56$, enlarge it.

### Definition 17 (radial sweep)

The *radial sweep* of a square $S$ is

```math
\widehat{S} = \bigcup_{m \ge 0} \left( S^\circ + m\,(c_S - o) \right),
```

the region that $S^\circ$ covers as it slides away from $o$ along the ray
through its centre.

![A square containing the disk centre that does not reach the circle of radius r. Dotted copies of it slid away from the centre along the ray through its centre fill the radial sweep, which covers a long highlighted arc of the circle](figures/sweep.svg)

*The square $S$ contains $o$ but does not reach the circle
$\Gamma_r$. Sliding it away from $o$ along the ray through its centre (dotted
copies) sweeps out $\widehat{S}$, which covers the highlighted arc. Five
squares use exactly this
([Lemma 5.7](five.md#lemma-57-the-sweep-holds-a-fifth-of-the-circle)).*

*Lean: [`openRay`](../../SquaresInCircles/Common/Support.lean#L48).*

The sweep holds longer arcs than the square itself. The lemmas below show that
it still avoids every other square, as long as every square $S$ has
$(a_S, b_S)$ in the octagon $P_8$.

### Lemma 13 (octagon support)

If $(a_S, b_S) \in P_8$, then for every square $T$ and every vector $n$,

```math
|\langle n,\ c_S - o\rangle| \le w_S(n) + w_T(n) .
```

![The quadrilateral with vertices (0, 0), (1, 0), (3/4, 3/4) and (0, 1), dashed level lines of pa + qb, and the level line through the corner (3/4, 3/4), where the largest value is reached](figures/octagon-support.svg)

*Over the quadrilateral $P_8 \cap \lbrace a, b \ge 0 \rbrace$, $pa + qb$ is
largest at a vertex, here $(\frac34, \frac34)$.*

*Proof.* Let $p, q$ be the absolute components of $n$ in the frame of $S$, and
$u, v$ those in the frame of $T$, so that
$w_S(n) + w_T(n) = \frac{p+q}2 + \frac{u+v}2$ and
$p^2 + q^2 = u^2 + v^2 = |n|^2$. In the frame of $S$ the coordinates of
$c_S - o$ are $\pm a_S$ and $\pm b_S$ in some order, and $P_8$ is symmetric, so
$|\langle n, c_S - o\rangle| \le pa + qb$ for a point $(a, b)$ of $P_8$ with
$a, b \ge 0$. That region is the quadrilateral with vertices $(0,0)$, $(1,0)$,
$(\frac34, \frac34)$, $(0,1)$, and $pa + qb$ is largest at a vertex.
Explicitly: if $p \ge 3q$, then $pa + qb \le \frac p3(3a + b) \le p$; the case
$q \ge 3p$ is symmetric; otherwise both weights below are nonnegative and

```math
pa + qb = \frac{3p - q}{8}(3a + b) + \frac{3q - p}{8}(a + 3b) \le \frac34(p + q) .
```

Finally each of $p$ and $q$ is at most $|n| \le u + v$. That gives
$p \le \frac{p+q}2 + \frac{u+v}2$, the same for $q$, and
$\frac34(p+q) \le \frac{p+q}2 + \frac{u+v}2$ because $\frac{p+q}2 \le u + v$.
$\square$

*Lean: [`octagon_support`](../../SquaresInCircles/Common/Support.lean#L18),
[`dot_center_le`](../../SquaresInCircles/Common/Support.lean#L35).*

### Lemma 14 (the sweep is safe)

If $S$ and $T$ are disjoint and $(a_S, b_S)$ and $(a_T, b_T)$ both lie in
$P_8$, then the sweep $\widehat{S}$ does not meet $T^\circ$.

![Two disjoint squares S and T, a dashed separating line between them with n pointing towards T, and the radial sweep of S extending away from T along the ray from o through its centre](figures/safe-sweep.svg)

*The separating line between $S$ and $T$, with $n$ pointing towards $T$. The ray
from $o$ through $c_S$ points away from $T$, so the sweep of $S$ stays on its
side.*

*Idea.* Take the separating line of Lemma 5. The octagon forces the ray from
$o$ through $c_S$ to point away from $T$ across that line, so sliding $S$
along the ray only moves it further from $T$.

*Proof.* Take $n$ from Lemma 5 and write $W = w_S(n) + w_T(n)$.

1. *Where $o$ lies.* By Lemma 13, $|\langle n, c_S - o\rangle| \le W$ and
   $|\langle n, c_T - o\rangle| \le W$. The difference of the two is
   $\langle n, c_T - c_S\rangle \ge W$, which forces

   ```math
   \langle n,\ c_S - o\rangle \le 0 \le \langle n,\ c_T - o\rangle .
   ```

2. *Sliding.* For $q \in S^\circ$, $m \ge 0$ and $p \in T^\circ$,

   ```math
   \langle n,\ q + m(c_S - o)\rangle \le \langle n, q\rangle < \langle n, c_S\rangle + w_S(n)
   \le \langle n, c_T\rangle - w_T(n) < \langle n, p\rangle ,
   ```

   so no point of the sweep lies in $T^\circ$. $\square$

*Lean:
[`safe_openRay_of_disjoint`](../../SquaresInCircles/Common/Support.lean#L82),
[`Separation.center_signs`](../../SquaresInCircles/Common/Support.lean#L59).*

### Proposition 15 (budget with a sweep)

Let $n \ge 2$ pairwise disjoint squares all have $(a_S, b_S) \in P_8$, and fix
a circle $\Gamma_r$. The following cannot both hold:

- the sweep of the containing square, if there is one, holds an arc of
  half-width at least $\pi/n$;
- every exterior square holds an arc of half-width more than $\pi/n$.

*Proof.* Replace the containing square by its sweep. By Lemma 14 the $n$ sets
are still pairwise disjoint. At most one square contains $o$, so with $n \ge 2$
some square is exterior and gives the strict inequality that Lemma 7 needs.
$\square$

*Lean:
[`ray_budget_impossible`](../../SquaresInCircles/Common/ArcBudget.lean#L42),
[`rayRegions_disjoint`](../../SquaresInCircles/Common/ArcBudget.lean#L27),
[`exists_exterior`](../../SquaresInCircles/Common/ArcBudget.lean#L15).*

## 8. Elementary estimates

### Lemma 16 (elementary estimates)

1. $\pi < \frac{22}7$.
2. $\arcsin x \ge x$ for $0 \le x \le 1$, and so $\arcsin x \le x$ for
   $-1 \le x \le 0$.
3. $\arcsin x \le x + \frac{x^3}4$ for $0 \le x \le \frac35$.
4. If $0 \le \theta \le \frac\pi2$, $u, v \in [0, 1]$ and
   $\sin\theta < \frac{u+v}2$, then $2\theta < \arcsin u + \arcsin v$.
5. $\cos t > \frac{401}{500}$ for $|t| \le \frac\pi5$, and
   $\sin\frac\pi5 < \frac35$.

*Proof.*

1. This is mathlib's bound $\pi < 3.1416$.
2. $\sin y \le y$ for $y \ge 0$; the second bound follows, as the arcsine is
   odd.
3. Put $y = x + \frac{x^3}4$; then $y \le \frac{109}{100}x$, and
   $\sin y > y - \frac{y^3}6 \ge x$.
4. The sine is concave on $[0, \pi]$, so
   $\sin\frac{\arcsin u + \arcsin v}2 \ge \frac{u+v}2 > \sin\theta$. The sine
   increases on $[-\frac\pi2, \frac\pi2]$, so
   $\frac{\arcsin u + \arcsin v}2 > \theta$.
5. $\cos t \ge 1 - \frac{t^2}2$ and $|t| < \frac{22}{35}$. Then
   $\sin^2\frac\pi5 < 1 - (\frac{401}{500})^2 < \frac9{25}$. $\square$

*Lean:
[`pi_lt_22_over_7`](../../SquaresInCircles/Common/ElementaryTrig.lean#L16),
[`arcsin_ge_self`](../../SquaresInCircles/Common/ElementaryTrig.lean#L19),
[`arcsin_le_self_of_nonpos`](../../SquaresInCircles/Common/ElementaryTrig.lean#L22),
[`arcsin_le_cubic`](../../SquaresInCircles/Common/ElementaryTrig.lean#L29),
[`arcsin_sum_gt_of_sin_lt`](../../SquaresInCircles/Common/ElementaryTrig.lean#L41),
[`cos_gt_401_500`](../../SquaresInCircles/Common/ElementaryTrig.lean#L60),
[`sin_pi_fifth_lt_three_fifths`](../../SquaresInCircles/Common/ElementaryTrig.lean#L68).*

## 9. Axis-parallel squares

### Lemma 17 (axis-parallel squares)

1. $Q(p)$ and $Q(q)$ are disjoint as soon as $p$ and $q$ differ by at least 1
   in one coordinate.
2. $\overline{Q(c)}$, with $c = (x, y)$, lies in the closed disk of radius $R$
   about the origin as soon as
   $(|x| + \frac12)^2 + (|y| + \frac12)^2 \le R^2$.
3. Hence $Q(c_1), \dots, Q(c_n)$ form a packing in the closed disk of radius
   $R$ about the origin as soon as any two of the centres differ by at least 1
   in one coordinate and every centre satisfies (2).

![Two axis-parallel squares Q(p) and Q(q), inside a box of half-sides B and C centred at the origin, inside the dashed circle of radius root of B squared plus C squared](figures/axis-squares.svg)

*Every point of the two squares lies in the box $[-B, B] \times [-C, C]$, and so
in the disk of radius $\sqrt{B^2 + C^2}$, which passes through the corners of
the box.*

*Proof.* Two open unit intervals with centres at least 1 apart are disjoint.
A point $p$ of $\overline{Q(c)}$ has $|p_1| \le |x| + \frac12$ and
$|p_2| \le |y| + \frac12$, so
$|p|^2 \le (|x| + \frac12)^2 + (|y| + \frac12)^2$. $\square$

*Lean: [`axis_disjoint`](../../SquaresInCircles/Common/Constructions.lean#L26),
[`axis_packing`](../../SquaresInCircles/Common/Constructions.lean#L35).*

## 10. Normal forms

Each uniqueness proof ends the same way: find one frame at $o$ in which every
square sits at a model centre
([Definition 4](preliminaries.md#definition-4-frames-at-the-disk-centre)), then
apply Lemma 19. For four and seven squares Lemma 20 helps find that frame.
Lemma 21 gives the converse of uniqueness, and Lemma 22 turns uniqueness into
the lower bound.

### Lemma 18 (sitting at a centre)

1. Let $\phi$ be the direction of $e_1^S$. In the frame $\phi$, $S$ sits at the
   coordinates of $c_S - o$ in the frame of $S$. So does every square $T$ with
   sides parallel to those of $S$, at the coordinates of $c_T - o$.
2. If $S$ sits at $c$ in the frame $\phi + k\frac\pi2$, then in the frame
   $\phi$ it sits at $c$ turned by $k$ quarter turns.

![A square S and a square T with the same axes, and dashed axes at o parallel to their sides; a path from o along the first axis for c1, then along the second for c2, reaches the centre of T](figures/parallel-squares.svg)

*Part (1): in the frame at $o$ parallel to the sides of $S$, the square $T$ sits
at the coordinates $(c_1, c_2)$ of $c_T - o$.*

*Proof.* (1) In the frame $\phi$, the local coordinates of $T$ are the frame
coordinates minus those of $c_T - o$, possibly turned by a multiple of a
quarter turn, and a quarter turn maps the open square $(-\frac12, \frac12)^2$
to itself. (2) Turning the frame by $k\frac\pi2$ turns all coordinates by the
same angle. $\square$

*Lean: [`self_represents`](../../SquaresInCircles/Common/Contacts.lean#L67),
[`same_axes_represents`](../../SquaresInCircles/Common/Contacts.lean#L50),
[`represents_quarter`](../../SquaresInCircles/Common/Angles.lean#L78),
[`represents_cardinal`](../../SquaresInCircles/Common/Angles.lean#L89).*

### Lemma 19 (from slots to a normal form)

If the squares $S_1, \dots, S_n$ of a packing are pairwise disjoint and each
one sits at one of the points $c_1, \dots, c_n$ in a common frame $\phi$, then
the packing has the normal form of $c_1, \dots, c_n$.

*Proof.* Two squares that sit at the same $c_j$ would both contain the point
$F_\phi(c_j)$, so the squares take different slots; with $n$ squares and $n$
slots, the assignment is a relabelling. The closed squares follow, since a
closed square is the closure of the open one. $\square$

*Lean:
[`normal_form_of_slots`](../../SquaresInCircles/Common/NormalForm.lean#L96),
[`same_open_same_closed`](../../SquaresInCircles/Common/NormalForm.lean#L56).
Lean reaches a boundary point along the segment from the centre instead of
taking a closure.*

### Lemma 20 (regular polygons)

If $mg = 2\pi$, then $m$ directions pairwise at least $g$ apart are, in some
order, $\theta_0 + ig$ for $i = 0, \dots, m - 1$.

![Four radii of a circle about o in the directions theta0, theta0 plus pi/2, theta0 plus pi and theta0 plus 3pi/2](figures/four-directions.svg)

*Four directions pairwise at least $\frac\pi2$ apart: the only way is a quarter
grid.*

*Proof.* Represent the directions by angles $p_0 \le \dots \le p_{m-1}$ in
$(-\pi, \pi]$. Neighbours are at least $g$ apart, so $p_i - ig$ increases
with $i$. Going round from $p_{m-1}$ to $p_0 + 2\pi$ is also at least $g$, so
$p_{m-1} - (m - 1)g \le p_0$. Hence $p_i - ig$ is constant. $\square$

*Lean: [`regular_polygon`](../../SquaresInCircles/Common/Angles.lean#L40).*

### Lemma 21 (normal forms of a packing)

If $Q(c_1), \dots, Q(c_n)$ form a packing in the closed disk of radius $R$
about the origin, then every configuration with the normal form of
$c_1, \dots, c_n$ is a packing in the closed disk of radius $R$ about its
disk centre $o$.

*Proof.* The frame of the normal form is an isometry of the plane that takes
the origin to $o$ and each $Q(c_i)$, open and closed, onto a square of the
configuration. Isometries preserve distances and disjointness. $\square$

*Lean:
[`HasNormalForm.packing`](../../SquaresInCircles/Common/NormalForm.lean#L118),
[`frameEquiv_distance`](../../SquaresInCircles/Common/NormalForm.lean#L43).*

### Lemma 22 (the lower bound)

Let $L$ be a set of layouts $c = (c_1, \dots, c_n)$. Suppose that every
packing of $n$ unit squares in a closed disk of radius $R_n$ has the normal
form of a layout in $L$, and that every layout $c$ in $L$ reaches the circle of
radius $R_n$: some $\overline{Q(c_i)}$ has a point at distance at least $R_n$
from the origin. Then every packing of $n$ unit squares in a closed disk of
radius $R$ has $R \ge R_n$.

*Proof.* Suppose $R < R_n$. The packing then lies in the closed disk of radius
$R_n$ as well, so it has the normal form of some layout $c$ in $L$: in a frame
$F_\phi$ at $o$, and after a relabelling, the closed squares of the packing are
the images of the $\overline{Q(c_i)}$. Take $i$ and a point $p$ of
$\overline{Q(c_i)}$ with $|p| \ge R_n$. Since $F_\phi$ is an isometry that
takes the origin to $o$, the point $F_\phi(p)$ of a closed square of the
packing is at distance $|p| > R$ from $o$, outside the closed disk of radius
$R$. $\square$

*Lean: [`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48),
[`pointInDirection_norm`](../../SquaresInCircles/Common/Coordinates.lean#L19).*

## 11. One framework for every case

Theorem $n$ has the same three parts for every case, and each case proves two
things. Its construction, by Lemma 17, shows that the axis-parallel squares at
each optimal layout form a packing in the closed disk of radius $R_n$, with a
corner on the circle of radius $R_n$. Its uniqueness proposition, the real work
of the case, shows that every packing at the optimal radius has the normal
form of an optimal layout. The rest is shared: Lemma 22 turns uniqueness into
the lower bound, and Lemma 21 gives the converse of uniqueness, so the optimal
packings are exactly those normal forms. For $n \le 5$ there is one optimal
layout; for $n = 7$ there is a family, and each of its layouts has a corner on
the circle. In Lean each case bundles its layouts, their packings, those
corners and uniqueness as an `Optimum`, from which the lower bound, attainment,
the converse and uniqueness with an explicit isometry follow once for all
cases.

*Lean: [`Optimum`](../../SquaresInCircles/Common/Optimum.lean#L21),
[`Optimum.ofUnique`](../../SquaresInCircles/Common/Optimum.lean#L35),
[`Optimum.optimality`](../../SquaresInCircles/Common/Optimum.lean#L48),
[`Optimum.attainment`](../../SquaresInCircles/Common/Optimum.lean#L61),
[`Optimum.packing_iff`](../../SquaresInCircles/Common/Optimum.lean#L67),
[`Optimum.rigid_uniqueness`](../../SquaresInCircles/Common/Optimum.lean#L73).*