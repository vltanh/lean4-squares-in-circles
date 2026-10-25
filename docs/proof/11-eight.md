# 11. Eight squares

[Contents](README.md) · [← 10. Seven squares](10-seven.md) · [Appendix A →](appendix-a.md)

Eight unit squares fit in a closed disk of radius $R_8 \approx 1.97877$ as
Figure 11.1 shows. Two axis-parallel squares stand one on the other at the
right, two more at the left, and a fifth sits on top between the two columns;
at the bottom lie two squares turned by about $7.08°$, and an eighth square in
the middle holds the disk centre. Five squares touch the circle, each with one
corner. This chapter proves that no smaller closed disk holds eight unit
squares, and it finds every packing at the radius $R_8$. Unlike one to six
squares, the optimal packing is far from unique: the five squares on the circle
are fixed, but the top square can move up and down, one of the two turned
squares can slide along the other, and the middle square can move and turn in
the room the others leave. The optimal packings form a five-parameter family
(Figure 11.2).

The radius is the minimum of a smaller problem. Keep only the five corners on
the circle, one of each of the squares $A$, $B$, $D$, $E$ and $H$ of
Figure 11.1, and the room the ring of seven squares needs between them: two
heights, a width and two spans along the frame of the turned squares. The least
radius of a disk about the centre that holds five corners with this room is
$R_8$ (Theorem 11.1). It has no closed form: at the minimum, five corners of a
chain of squares lie on one circle, and the excess of the fifth one and its two
derivatives vanish together, so that $R_8^2 = q_*$ is the first coordinate of
the unique solution of an explicit system of equations (Propositions 11.4
and 11.5).

The proof has two halves. The first shows that the seven squares around the
central one carry the frames of Figure 11.1 and are separated along its
contacts: a square holds a small disk about the centre, the cycle of the seven
other squares is pushed out to two boundary curves, the frames are shown to
turn little against each other, the quarter turns between neighbours form a
word that leaves one arrangement, and on each of the seven pairs of neighbours
the axis that separates them is identified. Each step is a whole-cycle
inequality: one inequality for each pair of neighbours, with markers that
cancel round the cycle and lower bounds adding up to more than $2\pi$, or a
weighted sum of the separating inequalities and the circle constraints, a
stress in the sense of Chapter 9. The second half is the five-corner problem
itself, applied to the ring, and one identity of the stationary chain,
evaluated at the centres of the squares, which gives the radius and the five
fixed squares. The case analyses of the first half are large, and many of
their branches end in a polynomial inequality in one or two angles, which the
Lean kernel checks in exact arithmetic (§11.11 and
[Appendix L](appendix-l.md)). For each case analysis the chapter gives what is
split and on what, the inequality that closes each branch with its constants,
and one representative case in full.

## Theorem 11.1 (eight squares)

For an angle $\theta$ put $e_\theta = (\cos\theta, \sin\theta)$ and
$f_\theta = (-\sin\theta, \cos\theta)$. A *five-corner configuration* is an
angle $\theta$ and five points $P_1, \dots, P_5$ of the plane. It *spans* if

```math
0 \le \theta \le \tfrac\pi4, \qquad (P_2 - P_1)_y \ge 2, \qquad (P_2 - P_3)_x \ge 3, \qquad (P_3 - P_4)_y \ge 2, \qquad \langle f_\theta, P_4 - P_5\rangle \ge 1 + \sin\theta, \qquad \langle e_\theta, P_1 - P_5\rangle \ge 2 + \cos\theta ,
```

and it *fits* in the radius $R \ge 0$ if $|P_i| \le R$ for $i = 1, \dots, 5$. The
*optimal radius* is

```math
R_8 = \inf\lbrace R : \text{some spanning five-corner configuration fits in } R\rbrace .
```

For real numbers $q, y, z, x_1, x_2, y_3, x_4$ put

```math
c = \frac{1 - z^2}{1 + z^2}, \qquad s = \frac{2z}{1 + z^2}, \qquad x_3 = x_2 - 3, \qquad y_4 = y_3 - 2,
```

```math
h_1 = c\,x_1 + s\,y - 2 - c, \qquad h_2 = -s\,x_4 + c\,y_4 - 1 - s, \qquad F = h_1^2 + h_2^2 - q ,
```

and

```math
F_y = 2h_1\left(s - \frac{c\,y}{x_1}\right) + 2h_2\left(c + \frac{s\,y_4}{x_4}\right)\frac{x_3\,(y + 2)}{y_3\,x_2}, \qquad
F_t = 2h_1\big(c\,y - s\,(x_1 - 1)\big) - 2h_2\big(c\,(x_4 + 1) + s\,y_4\big) .
```

The *stationary system* consists of the conditions

```math
\begin{gathered}
x_1^2 + y^2 = q, \qquad x_2^2 + (y + 2)^2 = q, \qquad x_3^2 + y_3^2 = q, \qquad x_4^2 + y_4^2 = q, \qquad x_1,\ x_2,\ y_3 > 0 > x_4, \\
\left(\tfrac{79}{40}\right)^2 \le q \le \tfrac{9789}{2500}, \qquad -1 < y < y_4 < -\tfrac12, \qquad 0 < z < 1, \qquad \frac{2z}{1 - z^2} < \frac15, \\
F = 0, \qquad F_y = 0, \qquad F_t = 0 .
\end{gathered}
```

It has exactly one solution (Proposition 11.4). Write $q_*$, $y_*$ and $z_*$
for its first three coordinates, $c_*$, $s_*$, $x_1, \dots, h_2$ for the values
of the other quantities there, $t_* = 2\arctan z_*$, so that
$c_* = \cos t_*$ and $s_* = \sin t_*$, and $e = e_{t_*}$, $f = f_{t_*}$.
Numerically $q_* \approx 3.9155341375$, $\sqrt{q_*} \approx 1.9787709$,
$y_* \approx -0.92066$ and $t_* \approx 0.12364$, about $7.08°$.

*The models.* Let $(\theta^\circ, P^\circ_1, \dots, P^\circ_5)$ be a spanning
five-corner configuration that fits in $R_8$; by part (1) below there is exactly
one. For real numbers $x, y, \varphi, \zeta, \eta$ the *model*
$M(x, y, \varphi, \zeta, \eta)$ consists of the eight unit squares

```math
\begin{gathered}
A = Q\left(P^\circ_1 + \left(-\tfrac12, \tfrac12\right)\right), \quad B = Q\left(P^\circ_2 + \left(-\tfrac12, -\tfrac12\right)\right), \quad D = Q\left(P^\circ_3 + \left(\tfrac12, -\tfrac12\right)\right), \quad E = Q\left(P^\circ_4 + \left(\tfrac12, \tfrac12\right)\right), \\
T = Q\left((P^\circ_2)_x - \tfrac32,\ \zeta\right),
\end{gathered}
```

the squares $H$ and $G$ turned by $\theta^\circ$, with the centres

```math
p_H = P^\circ_5 + \tfrac12\left(e_{\theta^\circ} + f_{\theta^\circ}\right), \qquad p_G = p_H + e_{\theta^\circ} + \eta\,f_{\theta^\circ} ,
```

and the *central square* $K$, the unit square with the centre $(x, y)$ turned
by $\varphi$. So $P^\circ_1$, $P^\circ_2$, $P^\circ_3$, $P^\circ_4$ are the lower
right corner of $A$, the upper right corner of $B$, the upper left corner of
$D$ and the lower left corner of $E$, and $P^\circ_5$ is the corner of $H$ that
is the lower left one in its own frame; $T$ lies one unit to the left of $B$ at
the height $\zeta$, and $G$ lies next to $H$, moved by $\eta$ along the side of
$H$. The *optimal models* are the models that are packings in the closed disk
of radius $R_8$ about the origin, together with their mirror images in the
diagonal $y = x$.

1. $R_8 = \sqrt{q_*}$, and exactly one spanning five-corner configuration fits
   in $R_8$: the angle $t_*$ and the points
   $(x_1, y_*)$, $(x_2, y_* + 2)$, $(x_3, y_3)$, $(x_4, y_4)$, $h_1 e + h_2 f$.
2. There are optimal models, and each of them has a point of one of its squares
   on the circle of radius $R_8$.
3. If eight unit squares form a packing in a closed disk of radius $R$, then
   $R \ge R_8$.
4. The packings of eight unit squares in a closed disk of radius $R_8$ are
   exactly the configurations congruent to an optimal model.

![The optimal packing of eight unit squares in its dashed circle of radius about 1.9788 about the disk centre o: at the right the squares A below and B above, at the left D above and E below, the square T on top between B and D, and at the bottom the two squares H and G, turned by about 7 degrees; in the middle the grey central square K, turned by about 11 degrees, holds o and a small shaded disk of radius 1/12 about it. Five dots mark the corners P1 to P5 of A, B, D, E and H on the circle; thick segments mark the five contacts along sides, A with B, B with T, T with D, D with E and H with G, and two larger dots the corner contacts of E with H and of A with G](figures/11-eight/eight.svg)

*Figure 11.1.* The model with the parameters
$(x, y, \varphi, \zeta, \eta) = (0.14, 0, 2\arctan 0.1, 1.35, -0.32)$, the
centre of the box of Proposition 11.7, in its circle of radius $R_8$ (dashed);
$2\arctan 0.1 \approx 11.4°$. The corners $P_1, \dots, P_5$ of $A$, $B$, $D$,
$E$ and $H$ lie on the circle (dots), and the seven exterior squares touch in a
cycle: $A$ with $B$, $B$ with $T$, $T$ with $D$, $D$ with $E$ and $H$ with $G$
along segments of their sides (thick), $E$ with $H$ and $G$ with $A$ at a
corner of one square on a side of the other (large dots). The central square
$K$ (grey) holds the disk of radius $\frac1{12}$ about $o$ (shaded) and touches
none of the others.

*Lean: [`Eight.FiveCorner`](../../SquaresInCircles/Geometry.lean#L293),
[`Eight.FiveCorner.spans`](../../SquaresInCircles/Geometry.lean#L303),
[`Eight.FiveCorner.fits`](../../SquaresInCircles/Geometry.lean#L314),
[`Eight.feasibleRadii`](../../SquaresInCircles/Geometry.lean#L321),
[`Eight.radius`](../../SquaresInCircles/Geometry.lean#L325),
[`Eight.FiveCorner.IsMinimizer`](../../SquaresInCircles/Geometry.lean#L330),
[`Eight.FiveCorner.selected`](../../SquaresInCircles/Geometry.lean#L334),
[`Eight.FiveCorner.anchorCenter`](../../SquaresInCircles/Geometry.lean#L337),
[`Eight.FiveCorner.topCenter`](../../SquaresInCircles/Geometry.lean#L346),
[`Eight.FiveCorner.tiltedCenter`](../../SquaresInCircles/Geometry.lean#L351),
[`Eight.turnedSquare`](../../SquaresInCircles/Geometry.lean#L280),
[`Eight.Parameters`](../../SquaresInCircles/Geometry.lean#L359),
[`Eight.model`](../../SquaresInCircles/Geometry.lean#L367),
[`Eight.reflectSquare`](../../SquaresInCircles/Geometry.lean#L378),
[`Eight.models`](../../SquaresInCircles/Geometry.lean#L389),
[`Eight.Stationary.Coordinates.IsStationary`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L122),
[`Eight.Stationary.qStar`](../../SquaresInCircles/Eight/Stationary/System.lean#L398),
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62),
[`Eight.models_reach`](../../SquaresInCircles/Eight/Uniqueness.lean#L70),
[`Eight.optimum`](../../SquaresInCircles/Eight/Uniqueness.lean#L82).*

*Remarks.* (i) The spans say that the five corners leave room for the ring of
seven squares: $B$ stands on $A$, $D$, $T$ and $B$ stand side by side,
$D$ stands on $E$, a corner of $E$ rests on the upper side of $H$, and $G$ fits
between $H$ and $A$. The last two spans are measured in the frame of $H$: the
span $1 + \sin\theta$ is the width of $H$ along $f_\theta$ plus the projection
on $f_\theta$ of the lower side of $E$, and $2 + \cos\theta$ is the width of $H$
and of $G$ along $e_\theta$ plus the projection on $e_\theta$ of the lower side
of $A$ (Figure 11.4). In the Lean statement the parameters
$(x, y)$, $\varphi$, $\zeta$, $\eta$ are called `center`, `angle`, `top` and
`tilted`.

(ii) The optimum is not unique. The five squares $A$, $B$, $D$, $E$, $H$ that
touch the circle and the frames of all seven exterior squares are fixed. The
top square $T$ moves vertically, the square $G$ slides along $H$, and the
central square moves and turns; the room for each depends on the positions of
the others (Figures 11.2 and 11.6). Proposition 11.6 gives explicit conditions
on the parameters, the *admissible* parameters, under which the model is a
packing, and the proof of part (4) shows that every packing at the radius $R_8$
is congruent to the model of admissible parameters or to its mirror image.
Proposition 11.7 gives a box of admissible parameters, of side $0.002$ in each
of the five directions.

(iii) The model has no symmetry, so mirror images must be listed separately;
in the earlier chapters every optimal model was symmetric in a line through
the origin
([Definition 2.6](02-preliminaries.md#definition-26-congruence-to-a-model)).

(iv) Friedman's page ([§1.3](README.md#13-background)) lists a packing of
eight squares in a circle of radius $1.97877\ldots$, found by David W.
Cantrell in March 2002, as the best known one. Theorem 11.1 shows that it is
optimal and that the optimal packings are exactly the members of the family.

![Four optimal packings of eight unit squares, each in its dashed circle of radius R8: the five squares on the circle and the frames of the outer squares are the same in all four, while the top square T, the turned square G and the grey central square K sit at different places; in the first the central square is turned by about 11 degrees, in the second T is lowered and K moved down, in the third G is pushed along H towards the centre, and in the fourth T and G touch the circle and K is turned the other way, by about 33 degrees](figures/11-eight/family.svg)

*Figure 11.2.* Four optimal packings: the squares $A$, $B$, $D$, $E$, $H$ do
not move, while $T$, $G$ and the central square $K$ do. In the coordinates
$(x, y, w, \zeta, \eta)$ of Proposition 11.6, with $\varphi = 2\arctan w$, the
parameters are $(0.14, 0, 0.1, 1.35, -0.32)$,
$(0.17, -0.18, 0.07, 0.92, -0.32)$, $(0.14, 0.015, 0.08, 1.35, -0.1)$ and
$(-0.0475, -0.0325, -0.3, \zeta_+, \eta_-)$: the centre of the box of
Proposition 11.7, $T$ lowered, $G$ pushed towards the centre, and $T$ and $G$
on the circle with $K$ turned by about $-33°$. All four are admissible.

*Outline of the proof.* Part (1) is Propositions 11.4 and 11.5 (§11.1), and
part (2) is Propositions 11.6 and 11.7. Part (3) is Proposition 11.45
(§11.12): the lower bound is proved directly, not through uniqueness, since the
argument works below the radius $R_8$ as well. Part (4) is Proposition 11.47
(§11.13). The proof of the lower bound has eight steps.

1. *The central core* (§11.2). In a packing of eight squares in a disk of
   squared radius at most $Q_0 = \frac{9789}{2500}$, just above $q_*$, one
   square contains the closed disk of radius $\frac1{12}$ about the disk
   centre in its interior (Theorem 11.10). From then on only the seven other
   squares, the *exterior squares*, and their consecutive pairs are kept.
2. *A boundary cycle* (§11.3). Each exterior square can be translated, with
   its frame and one chosen separating axis on each consecutive pair kept,
   until it touches the circle or the core (Proposition 11.15). Its state
   then lies on one of two curves, $\mathcal O$ and $\mathcal C$.
3. *Radius levels* (§11.4). A packing of squared radius at most $q_*$ is
   viewed in the disk of squared radius $q_*$, and its boundary cycle is taken
   there. Pushing the squares on $\mathcal O$ outward keeps every separating
   axis (Lemma 11.17); this moves the cycle to the levels $Q_1$ and $Q_0$,
   where frames and words are read, and back.
4. *Frame concentration* (§11.5). The frames of the seven squares lie, modulo
   quarter turns, in an interval shorter than $\frac7{10}$
   (Theorem 11.23).
5. *The quarter word* (§11.6). The quarter turns between the frames of
   neighbours form a word of seven digits, and only the word $0101011$ of
   Figure 11.1 survives (Proposition 11.28).
6. *The owners* (§11.7 to §11.9). With the roles $H, G, A, B, T, D, E$ of
   Figure 11.1, each of the seven pairs of neighbours is separated only along
   its *normal owners*, at most two of the four axes of the pair
   (Proposition 11.34 for six pairs, Corollary 11.38 for the pair $G$, $A$).
7. *The hard axes and the stationary frames* (§11.10). The two axes that hold
   the ring together separate the pairs $G$, $A$ and $B$, $T$; then the frames
   align, the five corners of $A$, $B$, $D$, $E$, $H$ span, and the five-corner
   problem gives the frames of Figure 11.1 and the separating normals of its
   seven contacts (Theorem 11.43).
8. *The dual at the original centres* (§11.12, §11.13). The weights of the
   stationary chain, applied to the five corner constraints and the seven
   separations of the original squares, give $q \ge q_*$, and at $q = q_*$ they
   fix $A$, $B$, $D$, $E$, $H$ and put $T$ and $G$ on their slider lines
   (Theorem 11.44).

The longer proofs are in [Appendix J](appendix-j.md) (the stationary
system), [Appendix K](appendix-k.md) (the central core),
[Appendix L](appendix-l.md) (the exact polynomial checks) and
[Appendix M](appendix-m.md) (the dual at the original centres and the
equality).

## 11.1 Construction

### Definition 11.2 (the five-corner chain)

Let $q > 0$, and let $y$ and $t$ be real numbers. Put $c = \cos t$,
$s = \sin t$, $e_t = (c, s)$ and $f_t = (-s, c)$, and, where the square roots
are defined and positive,

```math
x_1 = \sqrt{q - y^2}, \quad x_2 = \sqrt{q - (y + 2)^2}, \quad x_3 = x_2 - 3, \quad y_3 = \sqrt{q - x_3^2}, \quad y_4 = y_3 - 2, \quad x_4 = -\sqrt{q - y_4^2} .
```

The *five corners* are

```math
P_1 = (x_1, y), \qquad P_2 = (x_2, y + 2), \qquad P_3 = (x_3, y_3), \qquad P_4 = (x_4, y_4), \qquad P_5 = h_1 e_t + h_2 f_t ,
```

with $h_1$, $h_2$ as in Theorem 11.1, and the *defect* is
$F(q, y, t) = |P_5|^2 - q = h_1^2 + h_2^2 - q$. The *chain* consists of the
axis-parallel squares $A$, $B$, $D$, $E$ with the corners $P_1$ (lower right),
$P_2$ (upper right), $P_3$ (upper left) and $P_4$ (lower left), of $H$ with
the frame $e_t$, $f_t$ and the corner $P_5 = p_H - \frac12 e_t - \frac12 f_t$,
of $G$ with $p_G = p_H + e_t + \eta f_t$, and of $T = Q(x_2 - \frac32, \zeta)$,
for real $\eta$ and $\zeta$. In the variable $z = \tan\frac t2$ the numbers
$c$, $s$, $h_1$, $h_2$ and $F$ are those of Theorem 11.1, and $F_y$ and $F_t$
are the derivatives of $F$ in $y$ and in $t$ (Lemma J.1).

*Lean:
[`Eight.Stationary.Coordinates`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L80),
[`Eight.Stationary.Coordinates.IsChain`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L110),
[`Eight.Stationary.Coordinates.defect`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L97),
[`Eight.Stationary.Coordinates.positionDerivative`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L103),
[`Eight.Stationary.Coordinates.tiltDerivative`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L105),
[`Eight.Stationary.Coordinates.anchorPoints`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L219),
[`Eight.Stationary.Coordinates.exteriorSquares`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L215).*

### Lemma 11.3 (the chain)

Let the square roots of Definition 11.2 be defined and positive, let
$0 \le t \le \frac\pi2$, and write
$\tau(t) = \frac12(1 + |\cos t| + |\sin t|) = \frac12(1 + c + s)$ for the
threshold of [Definition 9.9](09-six.md#definition-99-squares-in-a-frame).

1. $|P_1|^2 = |P_2|^2 = |P_3|^2 = |P_4|^2 = q$ and $|P_5|^2 = q + F(q, y, t)$.
2. The top side of $A$ and the bottom side of $B$ lie on the line of height
   $y + 1$; the bottom side of $D$ and the top side of $E$ lie on the line of
   height $y_3 - 1$; and the vertical lines $x = x_2 - 2$ and $x = x_2 - 1$
   carry the right side of $D$ and the left side of $T$, and the right side of
   $T$ and the left side of $B$.
3. For every $\eta$,

   ```math
   \langle e_t,\ p_G - p_H\rangle = 1, \qquad \langle e_t,\ p_A - p_G\rangle = \tau(t), \qquad \langle f_t,\ p_E - p_H\rangle = \tau(t) .
   ```

   So, in the sense of Lemma 9.11, $H$ and $G$ are separated along $e_t$, $G$
   and $A$ along $e_t$, and $H$ and $E$ along $f_t$, each with no room to
   spare.

*Proof.* (1) The first four are the definitions of $x_1$, $x_2$, $y_3$ and
$x_4$, and $|h_1 e_t + h_2 f_t|^2 = h_1^2 + h_2^2$. (2) The squares $A$ and
$B$ have the centres $(x_1 - \frac12, y + \frac12)$ and
$(x_2 - \frac12, y + \frac32)$, so they span the heights $[y, y + 1]$ and
$[y + 1, y + 2]$; likewise $D$ and $E$ span $[y_3 - 1, y_3]$ and
$[y_3 - 2, y_3 - 1]$, as $y_4 = y_3 - 2$. Across, $D$ spans
$[x_3, x_3 + 1] = [x_2 - 3, x_2 - 2]$, $T$ spans $[x_2 - 2, x_2 - 1]$ and $B$
spans $[x_2 - 1, x_2]$. (3) As $\langle e_t, f_t\rangle = 0$,
$\langle e_t, p_G - p_H\rangle = 1$. Next
$\langle e_t, p_A\rangle = c(x_1 - \frac12) + s(y + \frac12)$ and
$\langle e_t, p_G\rangle = h_1 + \frac32 = c\,x_1 + s\,y - c - \frac12$, whose
difference is $\frac12(1 + c + s)$. In the same way
$\langle f_t, p_E\rangle = -s(x_4 + \frac12) + c(y_4 + \frac12)$ and
$\langle f_t, p_H\rangle = h_2 + \frac12 = -s\,x_4 + c\,y_4 - s - \frac12$,
whose difference is again $\frac12(1 + c + s)$. Each of the three vectors is
an axis of $H$ or $G$, and the frames of $H$ and $G$ agree with each other and
make the angle $t$ with those of $A$ and $E$, so the thresholds of Lemma 9.11
are $\tau(0) = 1$ and $\tau(t)$. $\square$

*Lean:
[`Eight.Stationary.Coordinates.anchor_vertex`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L230),
[`Eight.Stationary.Coordinates.anchor_circle`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L237),
[`Eight.Stationary.Coordinates.standard_contacts`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L272),
[`Eight.Stationary.Coordinates.HG_contact`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L246),
[`Eight.Stationary.Coordinates.GA_contact`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L251),
[`Eight.Stationary.Coordinates.HE_contact`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L266),
[`Eight.Stationary.Coordinates.HA_contact`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L260).*

So the chain realizes the seven contacts of Figure 11.1 for every $q$, $y$
and $t$, and it closes, with all five corners on the circle of radius
$\sqrt q$, exactly when $F(q, y, t) = 0$ (Figure 11.3). Its five corners always
have the spans of Theorem 11.1 with equality: by Lemma 11.3 (2) and (3),
$(P_2 - P_1)_y = 2$, $(P_2 - P_3)_x = 3$, $(P_3 - P_4)_y = 2$,
$\langle f_t, P_4 - P_5\rangle = 1 + \sin t$ and
$\langle e_t, P_1 - P_5\rangle = 2 + \cos t$. So for $0 \le t \le \frac\pi4$ a
chain with $F(q, y, t) = 0$ is a spanning five-corner configuration that fits
in $\sqrt q$. For $q$ near $q_*$ the defect has a unique minimum in $(y, t)$,
which decreases as $q$ grows; the least $q$ at which the minimum reaches 0 is
$q_*$, and there the minimum is a simultaneous zero of $F$, $F_y$ and $F_t$.

*Lean:
[`Eight.FiveCorner.ofCoordinates`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L188),
[`Eight.FiveCorner.coordinate_contacts`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L202),
[`Eight.FiveCorner.ofCoordinates_spans`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L225),
[`Eight.FiveCorner.ofCoordinates_fits`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L235).*

![Two panels. Left: the five-corner chain at the squared radius q* for a position y and tilt t different from the optimal ones: the squares A, B, D, E and T in their columns with the corners P1 to P4 on the dashed circle, and the turned squares H and G at the bottom, whose corner P5 lies outside the circle. Right: the plane of y and t with the level curves of the defect F(q*, y, t), closed curves around one point (y*, t*), where F has its minimum 0; a red ring marks the pose of the left panel](figures/11-eight/chain.svg)

*Figure 11.3.* The chain at $q = q_*$. Left: for $(y, t) = (-0.64, 0)$
the corners $P_1, \dots, P_4$ lie on the circle (dashed) but $P_5$ lies
outside it, $F(q_*, -0.64, 0) > 0$; the squares $T$ and $G$, which the chain
does not use, are drawn in free positions. Right: level curves of
$F(q_*, \cdot, \cdot)$ at $0.005$, $0.02$, $0.05$, $0.1$, $0.2$ and $0.35$; the
defect is positive except at its minimum $(y_*, t_*)$, where it vanishes.

### Proposition 11.4 (the stationary zero)

1. The stationary system of Theorem 11.1 has exactly one solution.
2. Its first coordinate satisfies

   ```math
   3.91553413751747512652 < q_* < 3.91553413751747542652 ,
   ```

   so, with $q_- = \frac{7831}{2000}$, $Q_1 = \frac{1957767069}{500000000}$
   and $Q_0 = \frac{9789}{2500}$,

   ```math
   \tfrac52 < q_- < q_* < Q_1 < Q_0 < 4 . \tag{11.1}
   ```

3. At the solution $-0.92071 < y_* < -0.92059$, and

   ```math
   \begin{gathered}
   0.99231 \le c_* \le 0.99242, \quad 0.12327 \le s_* \le 0.12338, \quad 1.75152 \le x_1 \le 1.75159, \quad 1.65843 \le x_2 \le 1.65852, \\
   1.45455 \le y_3 \le 1.45464, \quad -1.90214 \le x_4 \le -1.90211, \quad -1.36797 \le h_1 \le -1.36748, \quad -1.43022 \le h_2 \le -1.42976 .
   \end{gathered}
   ```

4. For each $q$ with $q_- \le q \le Q_0$, the defect $F(q, \cdot, \cdot)$ has
   a unique minimum $m(q)$ over the rectangle
   $-\frac{937}{1000} \le y \le -\frac{179}{200}$,
   $\frac1{20} \le \tan\frac t2 \le \frac{81}{1000}$, attained at an interior
   point; $m$ is continuous and strictly decreasing, and $m(q_*) = 0$.

The proof is given in [Appendix J](appendix-j.md).

*Lean:
[`Eight.Stationary.sharpData`](../../SquaresInCircles/Eight/Stationary/System.lean#L1711),
[`Eight.Stationary.sharpData_stationary`](../../SquaresInCircles/Eight/Stationary/System.lean#L1713),
[`Eight.Stationary.stationary_unique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1748),
[`Eight.Stationary.exact_stationary_existsUnique`](../../SquaresInCircles/Eight/Stationary/System.lean#L1751),
[`Eight.Stationary.qStar_bracket`](../../SquaresInCircles/Eight/Stationary/System.lean#L1659),
[`Eight.Stationary.qStar_limits`](../../SquaresInCircles/Eight/Stationary/System.lean#L1671),
[`Eight.radius_levels`](../../SquaresInCircles/Eight/Model.lean#L36),
[`Eight.Stationary.sharp_coordinates`](../../SquaresInCircles/Eight/Stationary/System.lean#L1754),
[`Eight.Stationary.sharp_y`](../../SquaresInCircles/Eight/Stationary/System.lean#L1789),
[`Eight.Stationary.unique_minimum_zero`](../../SquaresInCircles/Eight/Stationary/System.lean#L382),
[`Eight.Stationary.minimum_radius_difference`](../../SquaresInCircles/Eight/Stationary/System.lean#L334).*

The numbers $q_-$, $Q_1$ and $Q_0$ are radius levels of the proof (§11.4).
The level $Q_0$ is a round number above $q_*$, at which the core and the cycle
of §11.2 to §11.6 are studied; $Q_1$ exceeds $q_*$ by less than
$5 \cdot 10^{-10}$, and below it the five-corner problem is localized; and
$q_-$, just below $q_*$, starts the interval of Proposition 11.4 (4).

### Proposition 11.5 (the five-corner problem)

1. If a spanning five-corner configuration $(\theta, P_1, \dots, P_5)$ fits in
   the radius $R$, then $R \ge \sqrt{q_*}$.
2. If it fits in $\sqrt{q_*}$, then $\theta = t_*$ and $P_1, \dots, P_5$ are the
   five corners of the solution of the stationary system,
   $(x_1, y_*)$, $(x_2, y_* + 2)$, $(x_3, y_3)$, $(x_4, y_4)$ and
   $h_1 e + h_2 f$.

Hence $R_8 = \sqrt{q_*}$, the infimum that defines $R_8$ is attained, and the
corners of the stationary solution, with the angle $t_*$, are the only spanning
five-corner configuration that fits in $R_8$.

*Proof.* (1) Suppose $R < \sqrt{q_*}$; then $R < 2$ by (11.1). Write
$q = R^2$, $c = \cos\theta$, $s = \sin\theta$, and $y = (P_1)_y$.

*Step 1: the chain below the corners.* The spans and the conditions
$|P_i|^2 \le q$ place the corners of the chain of Definition 11.2 at the
squared radius $q$, the position $y$ and the tilt $\theta$ outside the given
ones. First $(P_2)_y \ge y + 2$ and $(P_2)_y \le R < 2$ give $y < 0$, and the
radicals of Definition 11.2 are defined. Then $(P_1)_x \le x_1$ and, as
$0 < y + 2 \le (P_2)_y$, $(P_2)_x \le x_2$. Next
$(P_3)_x \le (P_2)_x - 3 \le x_3 < 0$, so $(P_3)_x^2 \ge x_3^2$ and
$(P_3)_y \le y_3$; then $(P_4)_y \le (P_3)_y - 2 \le y_4 < 0$, so
$(P_4)_y^2 \ge y_4^2$ and $(P_4)_x \ge x_4$. As $c, s \ge 0$, the last two
spans give

```math
\langle e_\theta, P_5\rangle \le \langle e_\theta, P_1\rangle - 2 - c \le c\,x_1 + s\,y - 2 - c = h_1, \qquad \langle f_\theta, P_5\rangle \le \langle f_\theta, P_4\rangle - 1 - s \le -s\,x_4 + c\,y_4 - 1 - s = h_2 ,
```

and $h_1$, $h_2$ are negative (proof of
[Proposition J.5](appendix-j.md#proposition-j5-the-stationary-solution),
Step 1). So $|P_5|^2 \ge h_1^2 + h_2^2$, that is,

```math
F(q, y, \theta) \le |P_5|^2 - q \le 0 .
```

*Step 2: the tilt.* Two weighted sums of the spans locate $\theta$. For weights
$a, b, d, \varepsilon \ge 0$, adding the five spans with the weights
$a, b, d, \varepsilon, 1$ gives

```math
2a + 3b + 2d + \varepsilon\,(1 + \sin\theta) + 2 + \cos\theta \le \sum_{i=1}^5 \langle F_i, P_i\rangle ,
```

with the forces $F_1 = (\cos\theta, \sin\theta - a)$, $F_2 = (b, a)$,
$F_3 = (-b, d)$, $F_4 = (-\varepsilon\sin\theta, \varepsilon\cos\theta - d)$ and
$F_5 = (\varepsilon\sin\theta - \cos\theta, -\varepsilon\cos\theta - \sin\theta)$.
If $\sin\theta \ge \frac3{10}$, take
$(a, b, d, \varepsilon) = (\frac{23}{30}, \frac{31}{32}, \frac9{10}, \frac67)$
and bound $\langle F_i, P_i\rangle \le R|F_i|$ with $R < \frac{4947}{2500}$: the
left side minus $\frac{4947}{2500}\sum_i|F_i|$ is a concave function
of $\theta$ on $[\arcsin\frac3{10}, \frac\pi4]$, positive at both ends, so
the inequality fails. If $\sin\theta \le \frac3{10}$, take the weights

```math
a = \tfrac{24}{41} + \tfrac{49}{100}s - \tfrac{s^2}{20}, \qquad b = 1 - \tfrac s{20} - \tfrac{s^2}6, \qquad d = \tfrac{36}{31} - \tfrac7{10}s - \tfrac{s^2}{16}, \qquad \varepsilon = \tfrac{36}{31} - s + \tfrac{11}{20}s^2
```

and complete the squares, $\langle F_i, P_i\rangle \le m_i q + |F_i|^2/(4m_i)$,
with the masses
$m_1 = \frac{12}{41}/(1 + \frac{13s}{60})$, $m_2 = \frac{12}{41}/(1 - \frac{9s}{50})$,
$m_3 = \frac{12}{31}/(1 + \frac{9s}{25})$, $m_4 = \frac{3s}{10}/(1 + \frac{4s}5)$
and $m_5 = \frac{12}{31}/(1 + \frac{49s}{100})$ (at $s = 0$, $m_4 = 0$ and
$F_4 = 0$). After rational majorants of the masses and of $1 - \cos\theta$, the
difference of the two sides is at least the quintic

```math
\tfrac{38726637}{9929687500} - \tfrac{79}{1250}s + \tfrac{51}{200}s^2 - \tfrac{s^3}{100} - \tfrac{27}{100}s^4 - \tfrac3{10}s^5 ,
```

which is decreasing and positive on $[0, \frac1{10}]$ and increasing and
positive on $[\frac{79}{500}, \frac3{10}]$. Hence
$\frac1{10} < \sin\theta < \frac{79}{500}$, and $0 < \tan\theta < \frac15$.

*Step 3: the envelope.* By the proof of
[Proposition J.5](appendix-j.md#proposition-j5-the-stationary-solution)
(Steps 1 to 4), at the squared radius $q_*$ the defect is nonnegative at every
position of its radical domain and every tilt in $[0, \arctan\frac15]$.

*Step 4: the radius.* For $q < q_* < 4$ the radical domain at $q$ lies in that
at $q_*$, and $F(q_*, y, \theta) < F(q, y, \theta) - (q_* - q)$ (Appendix J,
Step 1). By Step 1, $F(q_*, y, \theta) < 0$, against Step 3.

(2) If $R = \sqrt{q_*}$, Steps 1 and 2 still apply: $\theta$ lies in
$(0, \arctan\frac15)$, and $F(q_*, y, \theta) \le 0$. The envelope
$M(q_*, \cdot)$, the least defect over the positions, is nonnegative on
$[0, \arctan\frac15]$ by Step 3 and at most $F(q_*, y, \theta) \le 0$ at
$\theta$; so $\theta$ is an interior minimum of $M(q_*, \cdot)$, hence a
critical tilt, and $M(q_*, \cdot)$ has only one, $t_*$ (Appendix J, Step 4).
With $\theta = t_*$ the five points are fixed by the weighted identity of the
stationary chain at arbitrary points: the gaps of the identity are the excesses
of the five spans, which are nonnegative
([Appendix M](appendix-m.md)).

Finally, the corners of the stationary solution span and fit in $\sqrt{q_*}$, by
Lemma 11.3 and $F = 0$, so $R_8 = \sqrt{q_*}$. $\square$

*Lean:
[`Eight.FiveCorner.stationary_radius_le`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L697),
[`Eight.FiveCorner.scalar_reduction`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L244),
[`Eight.FiveCorner.defect_le_last_corner`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L268),
[`Eight.FiveCorner.weighted_spans`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L318),
[`Eight.FiveCorner.HighTilt.exclusion`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L582),
[`Eight.FiveCorner.Nominal.gap_nonpos_of_spans`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L712),
[`Eight.FiveCorner.Nominal.gap_ge_polynomial`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L929),
[`Eight.FiveCorner.Nominal.sine_localization`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L1004),
[`Eight.FiveCorner.Nominal.tilt_localization`](../../SquaresInCircles/Eight/Corners/Nominal.lean#L1024),
[`Eight.FiveCorner.stationary_defect_nonneg`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L253),
[`Eight.Stationary.FiveCornerGeometry.defect_radius_decrease`](../../SquaresInCircles/Eight/Stationary/CriticalHessian.lean#L495),
[`Eight.FiveCorner.stationary_angle_of_fits`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L751),
[`Eight.FiveCorner.stationary_points_of_fits`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L834),
[`Eight.FiveCorner.radius_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L721),
[`Eight.FiveCorner.existsUnique_minimizer`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L867),
[`Eight.FiveCorner.selected_eq_stationary`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L876).*

![The optimal packing with its five corners P1 to P5 on the dashed circle of radius R8 and the five spans drawn as dimension arrows: the height 2 from P1 up to P2 across A and B, the width 3 from P3 to P2 across D, T and B, the height 2 from P4 up to P3 across E and D, and in the frame of the turned squares the span 1 + sin t from P5 to the level of P4 along f, and the span 2 + cos t from P5 to the level of P1 along e, across H, G and the bottom of A](figures/11-eight/corners.svg)

*Figure 11.4.* The five-corner problem at its minimum. The corners
$P_1, \dots, P_5$ (dots) lie on the circle of radius $R_8$ (dashed), and each
span holds with equality: the heights $2$ across $A$ and $B$ and across $E$
and $D$, the width $3$ across $D$, $T$ and $B$, and, along the frame $e$, $f$
of $H$ and $G$, the spans $1 + \sin t_*$ from $P_5$ to $P_4$ and
$2 + \cos t_*$ from $P_5$ to $P_1$.

The squares of the model are now explicit. By Proposition 11.5,
$\theta^\circ = t_*$ and the corners $P^\circ_i$ are those of the stationary
solution, so

```math
A = Q\left(x_1 - \tfrac12,\ y_* + \tfrac12\right), \quad B = Q\left(x_2 - \tfrac12,\ y_* + \tfrac32\right), \quad D = Q\left(x_3 + \tfrac12,\ y_3 - \tfrac12\right), \quad E = Q\left(x_4 + \tfrac12,\ y_4 + \tfrac12\right), \quad T = Q\left(x_2 - \tfrac32,\ \zeta\right),
```

and, in the notation of
[Definition 9.9](09-six.md#definition-99-squares-in-a-frame),
$H = Q_{t_*}(h_1 + \frac12, h_2 + \frac12)$ and
$G = Q_{t_*}(h_1 + \frac32, h_2 + \frac12 + \eta)$. Put

```math
\zeta_+ = \sqrt{q_* - (x_2 - 1)^2} - \tfrac12, \qquad \eta_- = -h_2 - \sqrt{q_* - (h_1 + 2)^2}, \qquad \eta_+ = -h_2 - \tfrac{13}{12} ,
```

so that $\zeta_+ \approx 1.36600$, $\eta_- \approx -0.44505$ and
$\eta_+ \approx 0.34665$.

*Lean:
[`Eight.FiveCorner.selected_anchorCenter`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L186),
[`Eight.FiveCorner.selected_topCenter`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L195),
[`Eight.FiveCorner.selected_tiltedCenter`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L200),
[`Eight.FiveCorner.selected_exteriorSquare`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L229),
[`Eight.Stationary.Coordinates.zMax`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L205),
[`Eight.Stationary.Coordinates.etaMin`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L207),
[`Eight.Stationary.Coordinates.etaMax`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L209).*

### Proposition 11.6 (the five-parameter family)

Call the parameters $(x, y, \varphi, \zeta, \eta)$ *admissible* if

1. $-\frac\pi4 \le \varphi < \frac\pi4$;
2. $\zeta \ge \frac12$ and $s_*(h_1 + 2) + c_*(h_2 + 1 + \eta) \le 0$;
3. $\zeta \le \zeta_+$ and $\eta \ge \eta_-$;
4. $|\langle e_\varphi, (x, y)\rangle| < \frac12$ and
   $|\langle f_\varphi, (x, y)\rangle| < \frac12$;
5. for each exterior square $P$, with the centre $p_P$ and the turn
   $\theta_P$, equal to $t_*$ for $H$ and $G$ and to $0$ for the others,

   ```math
   \max\left(|\langle e_\varphi, v\rangle|,\ |\langle f_\varphi, v\rangle|,\ |\langle e_{\theta_P}, v\rangle|,\ |\langle f_{\theta_P}, v\rangle|\right) \ge \tfrac12\left(1 + |\cos(\varphi - \theta_P)| + |\sin(\varphi - \theta_P)|\right), \qquad v = p_P - (x, y) .
   ```

Condition (b) says that the lower side of $T$ lies at or above the horizontal
axis and the highest point of $G$ at or below it, (c) that $T$ and $G$ lie in the
closed disk of radius $R_8$, (d) that the origin lies in the open square $K$,
and (e), by [Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares),
that $K$ and $P$ have disjoint interiors.

1. If $\zeta \ge \frac12$ and the highest point of $G$ lies at or below the
   horizontal axis, the seven exterior squares have pairwise disjoint
   interiors. The squares $A$, $B$, $D$, $E$, $H$ lie in the closed disk of
   radius $R_8$ about the origin, with the corners $P_1, \dots, P_5$ on its
   circle; $T$ lies in it exactly when $\zeta \le \zeta_+$, and $G$ exactly
   when $\eta \ge \eta_-$, and they reach the circle exactly when
   $\zeta = \zeta_+$ and $\eta = \eta_-$.
2. For admissible parameters the model is a packing in the closed disk of
   radius $R_8$ about the origin, and so is its mirror image in the diagonal.
3. Let $-\frac\pi4 \le \varphi < \frac\pi4$, and let
   $w = \frac{\sin\varphi}{1 + \cos\varphi}$, so that $\varphi = 2\arctan w$,
   $C_w = \cos\varphi = \frac{1 - w^2}{1 + w^2}$ and
   $S_w = \sin\varphi = \frac{2w}{1 + w^2}$. The parameters are admissible if
   and only if

   ```math
   1 - \sqrt2 \le w < \sqrt2 - 1, \qquad \tfrac7{12} \le \zeta \le \zeta_+, \qquad \eta_- \le \eta \le \eta_+, \qquad |C_w x + S_w y| < \tfrac5{12}, \qquad |-S_w x + C_w y| < \tfrac5{12} ,
   ```

   and (e) holds. In particular, for admissible parameters $K$ contains the
   closed disk of radius $\frac1{12}$ about the origin in its interior.

We call $(x, y, w, \zeta, \eta)$ the *chart* of the family.

*Proof.* We use the bounds of Proposition 11.4 (3) throughout.

(1) *Containment.* By [Lemma 3.4](03-tools.md#lemma-34-farthest-vertex) a
square lies in the closed disk of radius $R_8$ exactly when its vertex farthest
from the origin does, and that vertex is the one across both axes of the square
from the origin. The centre of $A$ has a positive first and a negative second
coordinate, as $x_1 > \frac12$ and $y_* < -\frac12$, so its farthest vertex
is its lower right corner $P_1$; in the same way the farthest vertices of $B$,
$D$, $E$ are $P_2$, $P_3$, $P_4$, and that of $H$, whose coordinates
$h_1 + \frac12$ and $h_2 + \frac12$ in the frame $e$, $f$ are negative, is
$P_5 = h_1 e + h_2 f$. These five points are at squared distance $q_*$ by
Lemma 11.3 (1), since $F = 0$ at the solution. The centre of $T$ has the
coordinates $x_2 - \frac32 \in (0, \frac12)$ and $\zeta > 0$, so its farthest
vertex is $(x_2 - 1, \zeta + \frac12)$, at squared distance at most $q_*$
exactly when $\zeta \le \zeta_+$, with equality exactly when $\zeta = \zeta_+$.
In the frame $e$, $f$ the centre of $G$ has the coordinates
$h_1 + \frac32 \in (0, \frac12)$ and $h_2 + \frac12 + \eta < 0$, the latter as
$c_*(h_2 + 1 + \eta) \le -s_*(h_1 + 2) < 0$; so its farthest vertex is
$(h_1 + 2)e + (h_2 + \eta)f$, at squared distance
$(h_1 + 2)^2 + (h_2 + \eta)^2$, which is at most $q_*$ exactly when
$-h_2 - \eta \le \sqrt{q_* - (h_1 + 2)^2}$, that is, when $\eta \ge \eta_-$.

*The ten pairs among $A$, $B$, $D$, $E$, $T$.* As $x_1 > x_2$ and
$-x_4 > 3 - x_2$, the squares $D$ and $E$ lie left of the line
$x = x_2 - 2$, $T$ lies between it and the line $x = x_2 - 1$, and $A$ and
$B$ lie right of the latter (Lemma 11.3 (2)). Within the columns, $A$ and $B$
are separated by the line of height $y_* + 1$, and $D$ and $E$ by the line of
height $y_3 - 1$.

*Four pairs with $H$ or $G$.* By Lemma 11.3 (3) the pairs $H$, $G$; $G$, $A$;
$H$, $E$ are separated, and so is $H$, $A$, since
$\langle e, p_A - p_H\rangle = 1 + \tau(t_*) \ge \tau(t_*)$; none of these
uses $\eta$.

*$E$ and $G$.* The leftmost point of $G$ has the first coordinate
$c_*(h_1 + 1) - s_*(h_2 + 1 + \eta)$, and the second condition of (b) gives
$-s_*(h_2 + 1 + \eta) \ge \frac{s_*^2}{c_*}(h_1 + 2) > 0$, so this coordinate
exceeds $c_*(h_1 + 1) > -\frac12$, while the right side of $E$ is at
$x_4 + 1 < -\frac9{10}$.

*Six pairs across the horizontal axis.* The highest point of $H$ has the
height $s_*(h_1 + 1) + c_*(h_2 + 1) < 0$, and that of $G$ the height
$s_*(h_1 + 2) + c_*(h_2 + 1 + \eta) \le 0$ by (b). The lowest points of $B$,
$D$, $T$ have the heights $y_* + 1$, $y_3 - 1$ and $\zeta - \frac12 \ge 0$, so
the horizontal axis separates each of $H$, $G$ from each of $B$, $D$, $T$.

These are $10 + 4 + 1 + 6 = 21$ pairs, all the pairs of the seven squares.

(2) By (d) the origin lies in the open square $K$, so the vertex of $K$ farthest
from the origin is at squared distance less than $2(\frac12 + \frac12)^2 = 2$
([Lemma 3.4](03-tools.md#lemma-34-farthest-vertex)), while
$R_8^2 \ge \frac94$, as $P_2$ and $P_3$ lie in the disk and differ by at least 3
in the first coordinate; so $K$ lies in the disk. By (e) and Lemma 9.11, $K$ is
disjoint from each exterior square, and with (1) all 28 pairs are disjoint. A
reflection in a line through the origin preserves packings in the disk.

(3) The map $w \mapsto 2\arctan w$ is a bijection from
$[1 - \sqrt2, \sqrt2 - 1)$ onto $[-\frac\pi4, \frac\pi4)$, with inverse
$\varphi \mapsto \frac{\sin\varphi}{1 + \cos\varphi}$. Suppose the conditions of
(3) hold. Then $\zeta \ge \frac7{12} > \frac12$; the highest point of $G$ is at
the height $s_*(h_1 + 2) + c_*(h_2 + 1 + \eta) \le s_*(h_1 + 2) - \frac{c_*}{12} < 0$,
as $\eta \le \eta_+$; (c) holds, and $|C_w x + S_w y| < \frac5{12}$ and
$|-S_w x + C_w y| < \frac5{12}$ give (d), since $C_w x + S_w y$ and
$-S_w x + C_w y$ are the two projections of (d). So the parameters are
admissible.

Conversely, let the parameters be admissible. By (2) the model is a packing in a
disk of squared radius $q_* \le Q_0$, so by the one-twelfth core
(Theorem 11.10, §11.2) one of its squares contains the closed disk
$\overline D(o, \frac1{12})$ in its interior and the seven others are at
distance more than $\frac1{12}$ from $o$. The square containing the core contains
$o$, as does $K$ by (d), so it is $K$
(Proposition 11.9). The points at distance $\frac1{12}$ from $o$ along the axes
of $K$ lie in $K^\circ$, which gives $|C_w x + S_w y| < \frac5{12}$ and
$|-S_w x + C_w y| < \frac5{12}$. The point $(0, \zeta - \frac12)$ lies on the
lower side of $T$, as $|x_2 - \frac32| < \frac12$, so its distance
$\zeta - \frac12$ from $o$ exceeds $\frac1{12}$, and $\zeta > \frac7{12}$. In
the same way the point $(h_2 + 1 + \eta)f$ lies on the upper side of $G$, as
$|h_1 + \frac32| < \frac12$, and $h_2 + 1 + \eta \le 0$ by (b), so
$-(h_2 + 1 + \eta) > \frac1{12}$, that is, $\eta < \eta_+$. $\square$

*Lean:
[`Eight.Parameters.Admissible`](../../SquaresInCircles/Eight/Equality/Angles.lean#L104),
[`Eight.Parameters.AngleRepresentative`](../../SquaresInCircles/Eight/Equality/Angles.lean#L98),
[`Eight.GeometricModel.containmentCost`](../../SquaresInCircles/Eight/Equality/Angles.lean#L47),
[`Eight.GeometricModel.separationMargin`](../../SquaresInCircles/Eight/Equality/Angles.lean#L57),
[`Eight.GeometricModel.wide_exterior_separator`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L338),
[`Eight.GeometricModel.wide_exterior_disjoint`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L528),
[`Eight.Parameters.tilted_below_axis_iff`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L549),
[`Eight.Parameters.exterior_disjoint`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L561),
[`Eight.Parameters.exterior_contained`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L571),
[`Eight.Stationary.exterior_contained`](../../SquaresInCircles/Eight/Stationary/Family.lean#L276),
[`Eight.Stationary.sharp_exterior_bounds`](../../SquaresInCircles/Eight/Stationary/Family.lean#L67),
[`Eight.Stationary.axis_containment`](../../SquaresInCircles/Eight/Stationary/Family.lean#L261),
[`Eight.Stationary.tilted_containment`](../../SquaresInCircles/Eight/Stationary/Family.lean#L265),
[`Eight.Parameters.central_containment_automatic`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L268),
[`Eight.FiveCorner.radius_sq_ge_nine_quarters`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L240),
[`Eight.GeometricModel.square_disjoint_iff`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L148),
[`Eight.Parameters.model_packing`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L629),
[`Eight.GeometricModel.model_packing`](../../SquaresInCircles/Eight/Construction.lean#L58),
[`Eight.GeometricModel.halfToAngle`](../../SquaresInCircles/Eight/Equality/Angles.lean#L216),
[`Eight.GeometricModel.angleToHalf`](../../SquaresInCircles/Eight/Equality/Angles.lean#L215),
[`Eight.Parameters.toStationary`](../../SquaresInCircles/Eight/Equality/Angles.lean#L337),
[`Eight.Parameters.ofStationary`](../../SquaresInCircles/Eight/Equality/Angles.lean#L340),
[`Eight.Stationary.EqualityParameters.Admissible`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L323),
[`Eight.Stationary.sat_max_iff`](../../SquaresInCircles/Eight/Stationary/Family.lean#L139),
[`Eight.Stationary.central_axis_sat`](../../SquaresInCircles/Eight/Stationary/Family.lean#L237),
[`Eight.Stationary.central_tilted_sat`](../../SquaresInCircles/Eight/Stationary/Family.lean#L246),
[`Eight.Parameters.ofStationary_admissible`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L648),
[`Eight.Parameters.central_core_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L699),
[`Eight.Parameters.top_core_rail_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L718),
[`Eight.Parameters.tilted_core_rail_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L742),
[`Eight.Parameters.toStationary_admissible`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L779),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38).*

![The exterior squares of the model of Figure 11.1 with the ranges of its two moving squares: the top square T drawn dashed at its lowest position, its centre at height 7/12 and its lower side touching the disk of radius 1/12 about o, and at its highest position, at height zeta+, with a corner on the circle; the turned square G drawn dashed at its two extreme positions along H, at eta+ touching the disk of radius 1/12 with its upper side and at eta- touching the circle with a corner. Dotted segments show the paths of the two centres](figures/11-eight/sliders.svg)

*Figure 11.5.* The two exterior squares that move. $T$ moves vertically with
$\frac7{12} \le \zeta \le \zeta_+$, from touching the disk of radius
$\frac1{12}$ to touching the circle; $G$ slides along $H$ with
$\eta_- \le \eta \le \eta_+$, from the circle to the disk of radius
$\frac1{12}$ (dashed: the extreme positions; dotted: the paths of the
centres). The other five exterior squares are fixed.

The family is not a product of intervals. For instance $\zeta = \frac7{12}$
is not attained: then the lower side of $T$ is at height $\frac1{12}$ above
the disk centre, but $K$ contains a point above that height near the centre,
inside the column of $T$. Figure 11.6 shows a section.

![The plane of the centre (x, y) of the central square for the frame parameter w = 0.1 and the sliders zeta = 1.35, eta = -0.32: the admissible centres form a shaded pentagon, tall and narrow, about 0.07 wide and 0.24 high, bounded by five straight segments, on each of which the central square touches one of the exterior squares D, B, A, G and H, labelled in their colours; a tiny black box around (0.14, 0) is marked inside it](figures/11-eight/section.svg)

*Figure 11.6.* A section of the family: the centres $(x, y)$ admissible with
$w = 0.1$, $\zeta = 1.35$ and $\eta = -0.32$ (shaded). Each side of the region
is a contact of $K$ with an exterior square, labelled by that square; the
core conditions $|C_w x + S_w y| < \frac5{12}$, $|-S_w x + C_w y| < \frac5{12}$
are not active on this section. The small box is the section of the box of
Proposition 11.7.

### Proposition 11.7 (a box of admissible parameters)

Let $\mathcal B$ be the box of the chart with

```math
0.139 \le x \le 0.141, \qquad -0.001 \le y \le 0.001, \qquad 0.099 \le w \le 0.101, \qquad 1.349 \le \zeta \le 1.351, \qquad -0.321 \le \eta \le -0.319 .
```

Every point of $\mathcal B$ gives admissible parameters, and every inequality of
Proposition 11.6 (3) in which a parameter occurs holds with room to spare
uniformly on $\mathcal B$: the central square is separated from $A$, $B$, $D$,
$E$, $H$, $G$, $T$ along the unit normals $(1, 0)$, $(C_w, S_w)$, $(-S_w, C_w)$,
$(-1, 0)$, $(-C_w, -S_w)$, $(s_*, -c_*)$, $(0, 1)$, with the projected gaps of
the centres exceeding the thresholds by at least $\frac1{100}$;
$|C_w x + S_w y| \le 0.139$ and $|-S_w x + C_w y| \le 0.03$; and
$q_* - (x_2 - 1)^2 - (\zeta + \frac12)^2 \ge 0.055$ and
$q_* - (h_1 + 2)^2 - (h_2 + \eta)^2 \ge 0.448$.

*Proof.* Each listed quantity is a function of the five parameters and of the
coordinates of the stationary solution. Eighteen such quantities, these and
the cosine and sine of the frames, are bounded on $\mathcal B$ by interval
expressions with rational endpoints, evaluated exactly by the Lean kernel, with
the coordinates of the solution in their brackets (Appendix L, interval
evaluation). For instance, the gap for $B$ is
$C_w(x_2 - \frac12 - x) + S_w(y_* + \frac32 - y) - \frac12(1 + C_w + S_w)$,
with $C_w$ between $\frac{979}{1000}$ and $\frac{981}{1000}$ and $S_w$ between
$\frac{39}{200}$ and $\frac{201}{1000}$ on $\mathcal B$. On $\mathcal B$,
$c_* S_w - s_* C_w \ge \frac9{125} > 0$, so the absolute values of
Proposition 11.6 (e) for $H$ and $G$ have fixed signs. Each separation along
one of the listed normals implies the corresponding maximum condition, and the
last two numbers are the room left in the containment of $T$ and $G$.
$\square$

*Lean:
[`Eight.Stationary.EqualityParameters.InBox`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L342),
[`Eight.Stationary.box_data_bounds`](../../SquaresInCircles/Eight/Stationary/Family.lean#L865),
[`Eight.box_admissible`](../../SquaresInCircles/Eight/Stationary/Family.lean#L901),
[`Eight.sample_admissible`](../../SquaresInCircles/Eight/Stationary/Family.lean#L1002),
[`Eight.GeometricModel.attainingParameters_admissible`](../../SquaresInCircles/Eight/Construction.lean#L51),
[`Eight.GeometricModel.models_nonempty`](../../SquaresInCircles/Eight/Construction.lean#L55).*

So the optimal packings of eight squares form a family with five free
parameters: the admissible set contains a box of positive side in each of its
five coordinates. The family is large: in Figure 11.2 the square $T$ is lowered
by $0.43$ and $G$ is moved by $0.22$ from the box, and the frame of $K$ ranges
over angles of both signs. Every optimal model reaches the circle: its square
$A$ has the corner $P_1$ on it.

*Lean:
[`Eight.Parameters.model_reaches`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L75),
[`Eight.GeometricModel.model_reaches`](../../SquaresInCircles/Eight/Construction.lean#L67),
[`Eight.models_reach`](../../SquaresInCircles/Eight/Uniqueness.lean#L70).*

## 11.2 The central square and the one-twelfth core

From here to §11.12 we prove the lower bound. Throughout, a packing of eight
unit squares lies in a closed disk about $o$ of squared radius $q$, and the
squares are measured from $o$ as in Chapter 3. The first step is the analogue
of the containing square of Chapter 9, but it is proved with the total length
of the arcs on two circles at once.

### Lemma 11.8 (arcs on two circles)

For a unit square $S$ and $r > 0$, let $L_r(S)$ be the length of the set of
directions $\theta$ with $o + r\,u(\theta) \in \overline S$, the total length
of the one or more arcs of $\Gamma_r$
([Definition 3.14](03-tools.md#definition-314-circles-about-the-disk-centre))
in the closed square. If $\overline S$ lies in the closed disk of squared
radius $\frac{98}{25}$ about $o$ and $o \notin S^\circ$, then

```math
3L_1(S) + L_{5/4}(S) \ge \pi , \tag{11.2}
```

with equality only for the squares that a rotation about $o$, possibly
followed by a reflection, carries to $[\xi, \xi + 1] \times [-\frac12, \frac12]$
with $0 \le \xi \le \frac{\sqrt{21} - 4}4$; these have $L_1(S) = \frac\pi3$
and $L_{5/4}(S) = 0$.

The proof is given in [Appendix K](appendix-k.md).

*Lean: [`Eight.squareAngles`](../../SquaresInCircles/Eight/Exterior.lean#L64),
[`Eight.angularLength`](../../SquaresInCircles/Eight/Exterior.lean#L67),
[`Eight.one_square_two_circle_inequality`](../../SquaresInCircles/Eight/Exterior.lean#L1017).*

![The model of Figure 11.1 with the unit circle and the circle of radius 5/4 about o. Each of the seven exterior squares holds one arc of each circle, drawn thick in the colour of the square, and the arcs on each circle do not overlap; the grey central square K, which contains o, meets neither circle](figures/11-eight/measure.svg)

*Figure 11.7.* Lemma 11.8 in the optimal packing. On the unit circle
$\Gamma_1$ and on $\Gamma_{5/4}$ each exterior square holds an arc (thick), and
for each of them $3L_1 + L_{5/4} > \pi$; the smallest value, about $3.170$,
belongs to $H$, with $D$ close behind. Had the eighth square avoided $o$ as
well, the eight sums would add up to at least $8\pi$, as much as the two
circles hold in all.

### Proposition 11.9 (a central square)

In a packing of eight unit squares in a closed disk of squared radius at most
$\frac{98}{25}$ about $o$, exactly one square contains $o$ in its interior.

*Proof.* For each $r > 0$, the total lengths satisfy
$\sum_{i=1}^8 L_r(S_i) \le 2\pi$: two of the closed squares meet $\Gamma_r$
in common points only on their boundaries, which meet the circle in finitely
many points, a set of length zero (as in
[Lemma 3.16](03-tools.md#lemma-316-angular-budget), with lengths of sets of
directions in place of arcs). Suppose that no square
contains $o$ in its interior. Then Lemma 11.8 applies to all eight, and

```math
8\pi \le \sum_{i=1}^8 \left(3L_1(S_i) + L_{5/4}(S_i)\right) = 3\sum_i L_1(S_i) + \sum_i L_{5/4}(S_i) \le 3 \cdot 2\pi + 2\pi = 8\pi .
```

So every square attains equality in (11.2), hence has $L_1(S_i) = \frac\pi3$,
and $\sum_i L_1(S_i) = \frac{8\pi}3 > 2\pi$, a contradiction. Two disjoint
squares cannot both contain $o$ in their interiors. $\square$

*Lean:
[`Eight.angularLength_budget`](../../SquaresInCircles/Eight/Exterior.lean#L178),
[`Eight.central_exists_from_one_square_inequality`](../../SquaresInCircles/Eight/Exterior.lean#L263),
[`Eight.central_square_exists`](../../SquaresInCircles/Eight/Containing.lean#L39),
[`Eight.central_square_unique`](../../SquaresInCircles/Eight/Exterior.lean#L290).*

The square that contains $o$ is the *central square*. Proposition 11.9 holds
up to the squared radius $\frac{98}{25} = 3.92$, a little above $q_*$; the
next theorem uses this room to show that the central square holds a disk of a
fixed size.

### Theorem 11.10 (the one-twelfth core)

Let eight unit squares form a packing in a closed disk of squared radius
$q \le Q_0$ about $o$. Then the central square contains the closed disk
$\overline D(o, \frac1{12})$ in its interior, and every other closed square
is at distance more than $\frac1{12}$ from $o$.

The proof is given in [Appendix K](appendix-k.md). Its idea is the following.
Moving the disk centre to a nearest point of the boundary of the central
square would give a packing in a slightly larger disk with no central square;
so the boundary is at least $\frac1{1000}$ away from $o$. Then every other
square holds the segment $\lbrace (\frac{11}{12}, y) : |y| \le \frac7{20}\rbrace$
of its own centre direction, turned to the horizontal. If a side of the
central square came within $\frac1{12}$ of $o$, the square would block a whole
interval of directions, of length more than $\frac{347}{200}$, for these
segments, and the seven centre directions, which are pairwise more than
$\frac{19}{25}$ apart, would not fit in what is left of the circle.

*Lean:
[`Eight.central_core_and_exteriors`](../../SquaresInCircles/Eight/Containing.lean#L797),
[`Eight.centralDepth_gt_milli`](../../SquaresInCircles/Eight/Containing.lean#L435).*

The other seven squares are the *exterior squares*. For an exterior square
$S$ we use its state $(a_S, b_S)$, the offsets of $o$ from its centre along
its axes, larger first
([Definition 3.1](03-tools.md#definition-31-position-of-the-disk-centre)).

### Corollary 11.11 (exterior squares)

Under the hypotheses of Theorem 11.10, every exterior square $S$ has its
centre at a distance $r$ from $o$ with $\frac7{12} \le r < \frac{71}{50}$, and
its state $(a, b) = (a_S, b_S)$ satisfies

```math
\left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 \le q, \qquad \tfrac{447}{800} < \tfrac12 + \tfrac{\sqrt2}{24} \le a < \tfrac{283}{200}, \qquad 0 \le b < \tfrac9{10} . \tag{11.3}
```

*Proof.* The first inequality is
[Lemma 3.4](03-tools.md#lemma-34-farthest-vertex) (1). The open disk of radius
$\frac12$ about $c_S$ lies in $S^\circ$
([Lemma 3.9](03-tools.md#lemma-39-inscribed-disks)) and so misses
$D(o, \frac1{12})$, hence $r \ge \frac7{12}$. The vertex of $S$ farthest
from $o$ is at squared distance $r^2 + (a + b) + \frac12 \ge r^2 + r + \frac12$,
and $(\frac{71}{50})^2 + \frac{71}{50} + \frac12 - Q_0 = \frac{13}{625} > 0$,
so $r < \frac{71}{50}$. The distance from $o$ to $\overline S$ is
$\sqrt{(a - \frac12)_+^2 + (b - \frac12)_+^2} \le \sqrt2\,(a - \frac12)_+$, as
$b \le a$, and it exceeds $\frac1{12}$; so $a \ge \frac12 + \frac{\sqrt2}{24}$,
and $\sqrt2 > \frac{141}{100}$ gives $\frac12 + \frac{\sqrt2}{24} > \frac{447}{800}$.
Finally $(a + \frac12)^2 + \frac14 \le q$ fails at $a = \frac{283}{200}$, and
$2(b + \frac12)^2 \le q < \frac{98}{25}$ fails at $b = \frac9{10}$. $\square$

*Lean:
[`Eight.annular_center_radius_lower`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L92),
[`Eight.annular_center_radius_upper`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L116),
[`Eight.Candidate.canonical_bounds`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L239),
[`Eight.coreAvoiding_iff_distance`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L71).*

![The model of Figure 11.1 with the centres of the exterior squares marked: the grey central square K containing the shaded disk of radius 1/12 about o, the dotted circle of radius 7/12 about o, and the seven exterior squares, which stay outside the shaded disk and whose centres all lie outside the dotted circle](figures/11-eight/core.svg)

*Figure 11.8.* The core in the optimal packing. The central square $K$
contains $\overline D(o, \frac1{12})$ (shaded) in its interior; the exterior
squares avoid it, so their centres lie outside the circle of radius
$\frac7{12}$ (dotted).

## 11.3 The boundary neighbour cycle

From here on the central square plays no part except through the core, and
of the 21 pairs of exterior squares only the seven pairs of neighbours in the
order of their centre directions are kept. A contradiction for this larger
class of configurations is a contradiction for the packing.

### Definition 11.12 (neighbour cycles)

Let $\frac52 \le q \le Q_0$. A *neighbour cycle at level $q$* is a sequence
of unit squares $S_0, \dots, S_6$, indices taken modulo 7, with the
following properties.

1. Each $\overline{S_i}$ lies in the closed disk of squared radius $q$ about
   $o$ and misses the open disk $D(o, \frac1{12})$.
2. The centre directions $\beta_i$ are distinct and in counterclockwise
   order, and the *gaps* $\delta_i \in (0, 2\pi)$, the counterclockwise
   angles from $\beta_i$ to $\beta_{i+1}$, add up to $2\pi$.
3. For each $i$ a *witness* is fixed: a signed axis $n_i$ of $S_i$ or of
   $S_{i+1}$ along which the two are separated in the sense of
   [Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares),
   $\langle n_i, c_{S_{i+1}} - c_{S_i}\rangle \ge \tau(\delta)$, $\delta$
   the relative angle of their frames.

Nonconsecutive squares may overlap. By Theorem 11.10 and Lemma 9.11, the
exterior squares of a packing in a closed disk of squared radius
$q \le Q_1$, taken in the order of their centre directions and with any
choice of witnesses, form a neighbour cycle at level $\max(q, q_-)$:
two disjoint exterior squares cannot have the same centre direction, since
their centres would be at least 1 apart on one ray although both lie at
distances between $\frac7{12}$ and $\frac{71}{50}$.

*Lean: [`Eight.NeighborCycle`](../../SquaresInCircles/Eight/Model.lean#L159),
[`Eight.SignedAxis.Feasible`](../../SquaresInCircles/Eight/Model.lean#L136),
[`Eight.signed_axis_of_disjoint`](../../SquaresInCircles/Eight/Frames/SeparatingAxis.lean#L52),
[`Eight.OrderedExterior`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L636),
[`Eight.ordered_exterior_exists`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L649),
[`Eight.center_direction_separated`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L600).*

### Lemma 11.13 (gaps of a neighbour cycle)

In a neighbour cycle at level $q \le Q_0$, the angle between any two
consecutive centre directions exceeds $\frac35$, and

```math
\tfrac35 < \delta_i < \pi \qquad (i = 0, \dots, 6) .
```

*Proof.* By Corollary 11.11, whose proof uses only containment and the core,
the centre distances $r, r'$ of consecutive squares lie in
$[\frac7{12}, \frac{71}{50}]$; the centres are at least 1 apart
([Lemma 3.10](03-tools.md#lemma-310-centres-at-least-1-apart)). If $\gamma$ is
the angle between the two directions, the law of cosines gives

```math
\cos\gamma \le g(r, r') = \frac{r^2 + r'^2 - 1}{2rr'} .
```

For fixed $r'$, $\partial g/\partial r = \frac{r^2 - r'^2 + 1}{2r^2 r'}$ is
positive if $r' \le 1$, and otherwise changes sign at most once, from negative
to positive; so the maximum of $g$ over the square $[\frac7{12}, \frac{71}{50}]^2$
is at a corner. The corner values are $-\frac{23}{49}$, $\frac{17443}{21300}$
and $\frac{3791}{5041}$, so $\cos\gamma \le \frac{17443}{21300} < \frac{41}{50}$.
As $\cos\frac35 \ge 1 - \frac{9}{50} + \frac{27}{5000} - \frac{81}{1250000} > \frac{41}{50}$
(alternating series), $\gamma > \frac35$. Each gap is at least the angle
between its two directions. If a gap were at least $\pi$, the other six would
add up to more than $\frac{18}5 > \pi$, and all seven to more than $2\pi$.
$\square$

*Lean:
[`Eight.polar_gap_cosine_bound`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L607),
[`Eight.annular_cosine_quotient`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L145),
[`Eight.gap_gt_three_fifths`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L641),
[`Eight.seven_gaps_below_pi`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L649).*

### Definition 11.14 (canonical frames and the radial curves)

Let $S$ be an exterior square, with centre $c_S = r\,u(\beta_S)$. A
*canonical frame* of $S$ is one of the four frames $e$, $f$ of $S$ for which

```math
c_S = a\,e - \sigma b\,f, \qquad a \ge b \ge 0, \qquad \sigma \in \lbrace 1, -1\rbrace ;
```

that is, $e$ is an axis of $S$ within $\frac\pi4$ of its centre direction.
Then $(a, b) = (a_S, b_S)$ is the state of $S$, $\sigma$ its *sign*,
$\tau_S = \sigma b/a \in [-1, 1]$ its *signed tangent*, and
$\alpha_S = \arctan\tau_S \in [-\frac\pi4, \frac\pi4]$; the direction of $e$
is $\beta_S + \alpha_S$. At a tie, $a = b$ or $b = 0$, either choice is
allowed, and each argument below fixes one choice for each square.

The *radial curves* are the two curves of the half plane $0 \le b \le a$ of
the $(a, b)$-plane

```math
\begin{aligned}
\mathcal O_q &: \left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 = q, \\
\mathcal C &: a = \tfrac7{12}\ \left(0 \le b \le \tfrac12\right), \qquad \left(a - \tfrac12\right)^2 + \left(b - \tfrac12\right)^2 = \tfrac1{144}\ \left(\tfrac12 \le b \le \tfrac12 + \tfrac{\sqrt2}{24}\right).
\end{aligned}
```

A square with state on $\mathcal O_q$ touches the circle of squared radius
$q$ with a vertex, and one with state on $\mathcal C$ touches the closed disk
of radius $\frac1{12}$, along a side if $b/a \le \frac67$ (the *core side*)
and at a vertex otherwise (the *core corner*). A neighbour cycle at level $q$
is a *boundary cycle* if the state of every square lies on $\mathcal O_q$ or
on $\mathcal C$.

*Lean: [`Eight.RadialKind`](../../SquaresInCircles/Eight/Model.lean#L146),
[`Eight.BoundaryState`](../../SquaresInCircles/Eight/Model.lean#L150),
[`Eight.BoundaryCycle`](../../SquaresInCircles/Eight/Model.lean#L170),
[`Eight.BoundaryCycle.tangent`](../../SquaresInCircles/Eight/Model.lean#L189),
[`Eight.BoundaryCycle.alpha`](../../SquaresInCircles/Eight/Model.lean#L192),
[`Eight.BoundaryCycle.canonicalAngle`](../../SquaresInCircles/Eight/Model.lean#L195),
[`Eight.CanonicalSquare`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L775),
[`Eight.canonical_square_exists`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L788),
[`Eight.CanonicalSquare.boundary_kind`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L824).*

![The (a, b)-plane with 0 at most b at most a: the states allowed by containment and the core form a shaded strip between the core curve C, a vertical segment at a = 7/12 followed by a small quarter circle up to the diagonal, and the outer curve O, an arc of the circle about (-1/2, -1/2) of radius root q. The outer curve is divided at the lines b = a/4 and b = 3a/7 into the three types L, M and H, and the core curve at b = 6a/7 into its side and its corner. Dots mark the states of the seven exterior squares of the optimal packing, five on the outer curve and two inside the strip](figures/11-eight/radial.svg)

*Figure 11.9.* The radial curves at the level $Q_0$. The states allowed by
containment and the core (shaded) lie between $\mathcal C$ and $\mathcal O$.
The dots are the states of the exterior squares of Figure 11.1: $A$, $B$, $D$,
$E$, $H$ on $\mathcal O$, while $T$ and $G$ lie inside. The lines
$b = \frac a4$ and $b = \frac{3a}7$ divide $\mathcal O$ into the types
$\mathsf L$, $\mathsf M$, $\mathsf H$ of §11.5, and $b = \frac{6a}7$ divides
$\mathcal C$ into the core side and the core corner.

### Proposition 11.15 (boundary reduction)

Let $S_0, \dots, S_6$ be a neighbour cycle at level $q \le Q_0$. Then there is
a boundary cycle $S'_0, \dots, S'_6$ at level $q$ in which every $S'_i$ is a
translate of $S_i$, the centre directions are in the same cyclic order, and
each witness $n_i$ is still a witness for $S'_i$, $S'_{i+1}$.

*Proof.* We move the squares one at a time, each by a translation, keeping
all frames. Suppose $S_i$ is not yet on a boundary curve. With the other
centres fixed, its two witnesses are linear inequalities in its centre $p$:

```math
\langle -n_i,\ p\rangle \ge \tau_i - \langle n_i, c_{S_{i+1}}\rangle, \qquad \langle n_{i-1},\ p\rangle \ge \tau_{i-1} + \langle n_{i-1}, c_{S_{i-1}}\rangle ,
```

two closed half planes with inward unit normals $a_1 = -n_i$ and
$a_2 = n_{i-1}$. Let $d = a_1 + a_2$ if $a_1 + a_2 \ne 0$, and a unit vector
perpendicular to $a_1$ otherwise. Then
$\langle a_j, d\rangle = 1 + \langle a_1, a_2\rangle \ge 0$ for $j = 1, 2$,
so the ray $p + \lambda d$, $\lambda \ge 0$, stays in both half planes. The set
of centres for which the square with the frame of $S_i$ lies in the closed
disk is an intersection of four closed disks of radius $\sqrt q$, one for each
vertex, so it is compact, and the ray leaves it. Let $\lambda_0$ be the first
$\lambda$ at which the moved square touches the circle or the closed disk
$\overline D(o, \frac1{12})$; it exists, as both conditions are closed and the
starting square touches neither. At $\lambda_0$ the square is still in the
disk, still misses the open core, and still satisfies both witnesses.

During the motion the centre stays at distance at least $\frac7{12}$ from $o$,
so its direction moves continuously. By Lemma 11.13, applied at every moment
of the motion, two consecutive directions never meet and no gap reaches
$\pi$, so the cyclic order and the gaps' range $(\frac35, \pi)$ are kept.
Squares moved earlier are not touched again, so after at most seven moves
every square touches the circle or the core, that is, its state lies on
$\mathcal O_q$ or on $\mathcal C$. $\square$

*Lean:
[`Eight.boundary_reduction_exists`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L1029),
[`Eight.anchored_cycle_exists`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L1003),
[`Eight.vertex_motion_exists`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L428),
[`Eight.two_halfplanes_recession`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L188),
[`Eight.first_two_boundary_contact`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L289),
[`Eight.boundary_normalization_exists`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L737),
[`Eight.BoundaryNormalization.original_selected_feasible`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L760).*

![The model of Figure 11.1 with the moves of the boundary reduction for its two squares that touch neither boundary. For T, its two witnesses, the vertical lines through its sides shared with B and D, leave it free to move vertically, and it moves up until its corner meets the circle; for G, its two witnesses, the lines across H and A perpendicular to e, leave it free to move along f, and it moves outward until its corner meets the circle. The moved squares are dashed, and arrows show the directions of the moves](figures/11-eight/reduction.svg)

*Figure 11.10.* Proposition 11.15 for the exterior squares of Figure 11.1. The
witnesses of $T$ are the vertical lines it shares with $D$ and $B$; their
inward normals are opposite, so $T$ moves along the perpendicular, up to the
circle. The witnesses of $G$ are perpendicular to $e$; $G$ moves along $f$,
out to the circle. The other five squares already touch the circle.

## 11.4 Radius levels

The steps of the proof are carried out at a few fixed squared radii: the
levels of (11.1) and $q_{\mathrm{low}} = \frac{19577}{5000}$, so that

```math
\tfrac52 < q_{\mathrm{low}} < q_- < q_* < Q_1 < Q_0 < 4 .
```

A packing in a closed disk of squared radius $q \le q_*$ also lies in the disk
of squared radius $q_*$, and its boundary cycle is taken at that level. The
theorems on the core, the frames and the quarter words hold for every level up
to $Q_0$ and are proved at $Q_0$; the candidate frame of §11.7 is read at $Q_1$;
the owners and the hard axes of §11.8 to §11.10 are determined at every level
from $q_{\mathrm{low}}$ to $Q_0$, or to $q_*$; and the final inequality is applied at the
radius of the packing itself. Between the levels the boundary cycles are moved
by pushing the squares on $\mathcal O$ outward along their centre directions.

*Lean: [`Eight.qMinus`](../../SquaresInCircles/Eight/Model.lean#L31),
[`Eight.Q1`](../../SquaresInCircles/Eight/Model.lean#L32),
[`Eight.Q0`](../../SquaresInCircles/Eight/Model.lean#L33),
[`Eight.qLow`](../../SquaresInCircles/Eight/Owners/CircleGeometry.lean#L20),
[`Eight.qCap`](../../SquaresInCircles/Eight/Owners/CircleGeometry.lean#L22),
[`Eight.radius_levels`](../../SquaresInCircles/Eight/Model.lean#L36),
[`Eight.uniform_radius_order`](../../SquaresInCircles/Eight/Owners/CircleGeometry.lean#L28),
[`Eight.sourceLevel`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L588).*

### Lemma 11.16 (the outer radius)

Let $\frac52 \le q \le 4$ and $|\alpha| \le \frac\pi4$, and put
$B = \cos\alpha + |\sin\alpha| \in [1, \sqrt2]$. An exterior square whose
canonical axis makes the angle $\alpha$ with its centre direction has its
state on $\mathcal O_q$ exactly when its centre is at the distance
$r = r(q, B)$ from $o$ given by

```math
r^2 + B\,r + \tfrac12 = q , \qquad\text{and then}\qquad \tfrac45 < r < \tfrac32, \qquad \tfrac14 \le \frac{\partial r}{\partial q} = \frac1{\sqrt{B^2 + 4q - 2}} \le \tfrac13 .
```

A square with state on $\mathcal C$ has its centre at distance at most
$\frac{\sqrt2}2 + \frac1{12} < \frac45$ from $o$.

*Proof.* With $a = r\cos\alpha$ and $b = r|\sin\alpha|$, the equation of
$\mathcal O_q$ reads $r^2 + r(\cos\alpha + |\sin\alpha|) + \frac12 = q$. Its
left side increases with $r \ge 0$; at $r = \frac45$ it is less than
$\frac{16}{25} + \frac65 + \frac12 = \frac{117}{50} < \frac52$, and at
$r = \frac32$ it is at least $\frac94 + \frac32 + \frac12 = \frac{17}4 > 4$.
Differentiating, $\partial r/\partial q = 1/(2r + B)$, and
$(2r + B)^2 = B^2 + 4q - 2$ lies between $9$ and $16$. A square on $\mathcal C$
touches $\overline D(o, \frac1{12})$, so its centre is a point of the closed
unit square about the origin plus a vector of length $\frac1{12}$. $\square$

*Lean:
[`Eight.RadiusTransfer.outerRadius`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L38),
[`Eight.RadiusTransfer.outerRadius_equation`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L76),
[`Eight.RadiusTransfer.outerRadius_bounds`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L84),
[`Eight.BoundaryCycle.core_radius_bound`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L353).*

### Lemma 11.17 (expansion)

Let $S_0, \dots, S_6$ be a boundary cycle at level $q_a$, and
$\frac52 \le q_a \le q_b \le 4$. Move each square with state on
$\mathcal O_{q_a}$ along its centre direction, keeping its frame, until its
state lies on $\mathcal O_{q_b}$, and keep the squares on $\mathcal C$ fixed.
The result is a boundary cycle at level $q_b$ with the same frames, centre
directions, gaps, signs, signed tangents and radial curves, and every signed
axis along which two consecutive squares were separated, not only the
witness, still separates them.

*Proof.* The centre directions and frames do not change, so neither do the
gaps, the canonical frames and the signed tangents; the moved squares lie on
$\mathcal O_{q_b}$ by construction, and moving a square away from $o$ along
its centre direction does not bring it nearer to $o$, as its state grows in
both coordinates. Fix a consecutive pair and a signed axis $n$ that separates
them, with threshold $\tau \ge 1$, and let $P(q)$ be the projection
$\langle n, c_{S_{i+1}} - c_{S_i}\rangle$ when the outer squares are at the
level $q$. By Lemma 11.16 the radii of the outer centres grow with
derivatives between $\frac14$ and $\frac13$, the core centres are fixed, and
$P$ is linear in the radii with fixed coefficients of absolute value at most
1. We show that $P'(q) > 0$ whenever $P(q) \ge \tau$; then $P - \tau$ cannot
become negative as $q$ grows.

If both squares are outer, $P = u\,r + v\,r'$ with $|u|, |v| \le 1$. If
$u, v \ge 0$, then $\frac32(u + v) > P \ge 1$ gives $u + v > \frac23$ and
$P' \ge \frac14(u + v) > \frac16$. Both coefficients cannot be negative, as
$P > 0$. Otherwise write $P = u\,r - w\,r'$ with $u, w \ge 0$; from
$P \ge 1$ and $\frac45 < r, r' < \frac32$ we get $u > \frac23 + \frac{8w}{15}$
and $w\,r' \le u\,r - 1 < \frac12$, so $w < \frac58$, and

```math
P' \ge \tfrac14 u - \tfrac13 w > \tfrac16 - \tfrac w5 > \tfrac1{24} .
```

If one square is outer and one on $\mathcal C$, then $P = u\,r + v\,r_0$ with
$r_0 < \frac45$ fixed, so $u\,r > \frac15$, $u > \frac2{15}$ and
$P' > \frac1{30}$. If both are on $\mathcal C$, nothing moves. $\square$

*Lean:
[`Eight.RadiusTransfer.every_feasible_projection_preserved`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L258),
[`Eight.BoundaryCycle.expand_spec`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L580),
[`Eight.RadiusExpansion`](../../SquaresInCircles/Eight/Model.lean#L212),
[`Eight.radialSquare_core`](../../SquaresInCircles/Eight/Boundary/Reduction.lean#L231).*

The lemma is used in two ways. A boundary cycle at the level $q_*$ is
expanded to $Q_1$ or $Q_0$, and every conclusion about frames, tangents, gaps or
words transfers back unchanged, since these do not move. And a conclusion of
the form "every separating axis of this pair belongs to a given set", proved at
the higher level, applies to the axes of the original cycle, since each of them
still separates after the expansion. No converse, that inward motion keeps
separations, is needed.

![Two graphs. Left: against q from 5/2 to 4, the distance r(q, B) from o of a centre whose state lies on the outer curve, for B = 1, rising from 1 to about 1.44, and for B = √2, rising from about 0.87 to about 1.29, with q* marked by a dashed vertical line. Right: against q from 3.2 to 4, the margins of the seven witnesses of the boundary cycle of Figure 11.10 when its squares are moved to the level q: seven nearly coincident increasing lines, one in the colour of each square, all crossing 0 at q*](figures/11-eight/expansion.svg)

*Figure 11.11.* Lemmas 11.16 and 11.17. Left: the outer radius $r(q, B)$
for the extreme values $B = 1$ (centre on the canonical axis) and
$B = \sqrt2$ (centre on the diagonal); both rise with slopes between
$\frac14$ and $\frac13$. Right: the seven witness margins of the boundary
cycle of Figure 11.10 when its squares are moved along their centre directions
to the level $q$. They all vanish at $q_*$, where every witness is a contact,
and increase with $q$, as in the proof of Lemma 11.17.

## 11.5 Frame concentration

The frames of the exterior squares are now shown to lie close together
modulo quarter turns. The proof sums one inequality for each consecutive
pair, so that the terms belonging to the squares cancel round the cycle.

### Lemma 11.18 (a common point)

Let $S$ be a unit square in the closed disk of squared radius $Q_0$ about $o$
that misses $D(o, \frac1{12})$, and let $\psi$ be a direction within
$\frac{19}{50}$ of the centre direction of $S$. Then
$o + \frac{41}{40}u(\psi) \in S^\circ$. Consequently, in a neighbour cycle at
a level $q \le Q_0$,

```math
\tfrac{19}{25} < \delta_i < 2\pi - 6 \cdot \tfrac{19}{25} = 2\pi - \tfrac{114}{25} < \tfrac{3\pi}4 \qquad (i = 0, \dots, 6) . \tag{11.4}
```

*Proof.* The first claim is Lemma K.4 (3) of
[Appendix K](appendix-k.md), whose hypothesis $a_S \ge \frac{107}{200}$ holds
by Corollary 11.11. If two consecutive centre directions were at most
$\frac{19}{25}$ apart, the direction $\psi$ halfway between them would be
within $\frac{19}{50}$ of both, and the point $o + \frac{41}{40}u(\psi)$ would
lie in both open squares. So every gap exceeds $\frac{19}{25}$, and each gap
is less than $2\pi$ minus the other six. Finally
$2\pi - \frac{114}{25} < \frac{3\pi}4$ as $\pi < \frac{456}{125}$. $\square$

*Lean:
[`Eight.exterior_pair_gap`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L122),
[`Eight.boundary_gap_lower`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L168),
[`Eight.boundary_gap_upper`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L192),
[`Eight.seven_gaps_three_quarters`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L177),
[`Eight.CentralBand.RayData.common_point_B`](../../SquaresInCircles/Eight/Containing.lean#L618).*

![Four exterior squares that miss the core disk and lie in the disk of squared radius Q0, part of whose circle is dashed: two with their states on the outer curve, at b = 0 and at a = b, and two on the core curve, at its corner point (7/12, 1/2) and on its diagonal, each with its centre direction turned by 19/50 to one side of the horizontal axis through o. The wedge of half-angle 19/50 about the axis is shaded, and all four squares contain the point at distance 41/40 from o on the axis, marked by a red dot](figures/11-eight/common-point.svg)

*Figure 11.12.* Lemma 11.18: squares that miss the core, lie in the disk and
have their centre directions within $\frac{19}{50}$ of a direction $\psi$
(shaded wedge) all contain the point $o + \frac{41}{40}u(\psi)$ (dot). Drawn,
for $\psi$ horizontal, are four squares at extremes of the states and
directions: the states of $\mathcal O_{Q_0}$ with $b = 0$ and with $a = b$, and
the corner point $(\frac7{12}, \frac12)$ and the diagonal point of
$\mathcal C$, each turned by $\frac{19}{50}$ to one side.

From now on, for two consecutive squares $S_i$ and $S_{i+1}$ of a cycle with
chosen canonical frames, we call $S_i$ the *source* and $S_{i+1}$ the
*target*, write $(a, b)$, $\sigma$ and $(a', b')$, $\sigma'$ for their
states and signs, and $\varphi$ for a real angle from the canonical axis of
the source to that of the target. In the canonical frame of the source, the
source has its centre at $(a, -\sigma b)$, and the target is
$Q_\varphi(a', -\sigma'b')$
([Definition 9.9](09-six.md#definition-99-squares-in-a-frame)). By
Lemma 9.11 the two are separated along one of eight signed axes. The next
lemma removes four of them.

### Lemma 11.19 (four forward axes)

Let $S$ and $S'$ be consecutive squares of a neighbour cycle at a level
$q \le Q_0$, as above. Then neither square is separated from the other along
$+e$ of the source, $-e$ of the target, $-f$ of the source or $-f$ of the
target. The four other signed axes, *source $+f$*, *target $+e$*,
*target $+f$* and *source $-e$*, numbered 1 to 4, separate exactly when the
*margins*

```math
\begin{aligned}
M_1 &= \sigma b + a'\sin\varphi - \sigma' b'\cos\varphi - \tau(\varphi), & M_2 &= a' - a\cos\varphi + \sigma b\sin\varphi - \tau(\varphi), \\
M_3 &= a\sin\varphi + \sigma b\cos\varphi - \sigma' b' - \tau(\varphi), & M_4 &= a - a'\cos\varphi - \sigma' b'\sin\varphi - \tau(\varphi)
\end{aligned} \tag{11.5}
```

are nonnegative, where
$\tau(\varphi) = \frac12(1 + |\sin\varphi| + |\cos\varphi|)$.

*Proof.* The margins are the projections of the difference of the centres on
the four signed axes, minus the threshold of Lemma 9.11, by the coordinate
formulas of that lemma. Suppose the source is separated from the target along
its own $+e$. Then the whole target lies beyond the line
$\langle e, x\rangle = a + \frac12$, at distance $a + \frac12 > \frac{11}{12}$
from $o$, as $a > \frac{447}{800} > \frac5{12}$ by (11.3). A unit square
beyond a line at distance $d \ge 0$ from $o$, with the unit normal $n$, has a
vertex at squared distance at least $(d + 1)^2 + \frac14$ from $o$: choose the
frame $e'$, $f'$ of the square with $c' = \langle n, e'\rangle \ge s' = \langle n, f'\rangle \ge 0$;
the midpoint $m$ of its side farthest along $e'$ has
$\langle n, m\rangle \ge d + c' + \frac{s'}2 \ge d + 1$, as
$(c' + \frac{s'}2)^2 = 1 + c's' - \frac34 s'^2 \ge 1$, and the two ends
$m \pm \frac12 f'$ of that side have the mean squared distance
$|m|^2 + \frac14$ from $o$, so one of them is at least that far. As
$(\frac{23}{12})^2 + \frac14 = \frac{565}{144} > Q_0$, this is a contradiction. The
target's $-e$ is the same with the roles exchanged. For $-f$ of the source,
write the centres as $r\,u(\beta)$ and $r'u(\beta + \delta)$ with
$0 < \delta < \frac{3\pi}4$ (Lemma 11.18) and the source axis at the angle
$\alpha$ from its centre direction, $|\alpha| \le \frac\pi4$. The projection
of $c' - c$ on $-f$ is $-r'\sin(\delta - \alpha) - r\sin\alpha$. If
$\delta \ge \alpha$, the first term is at most 0 and the second at most
$r|\sin\alpha| = b < \sqrt2 - \frac12 < 1$ by (11.3); if $\delta < \alpha$,
then $0 < \delta < \alpha$ and the projection is less than
$(r' - r)\sin\alpha < 1$, as both radii lie in $(\frac12, \frac32)$. Either
way it is less than $1 \le \tau$. The target's $-f$ is the same. $\square$

*Lean:
[`Eight.boundary_forward_complete`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L273),
[`Eight.backward_sine_lower`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L262),
[`Eight.BoundaryCycle.minus_source_y_projection`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L216),
[`Eight.BoundaryCycle.minus_target_y_projection`](../../SquaresInCircles/Eight/Boundary/Realization.lean#L239),
[`Eight.forwardMargin`](../../SquaresInCircles/Eight/Frames/SeparatingAxis.lean#L200),
[`Eight.canonical_margin_identity`](../../SquaresInCircles/Eight/Frames/SeparatingAxis.lean#L223).*

![The pair B, T of the optimal packing drawn in the canonical frame of B, the source: B to the right of o, its canonical axis horizontal, and the target T above it and to the left, touching B along a short piece of their common vertical side. At each centre four signed axes are drawn as arrows: the four retained ones, numbered 1 to 4 (source +f upwards at B, target +e upwards at T, target +f to the left at T, source -e to the left at B), solid, and the other four dashed and faded. The dashed red vertical line through the far side of B, at distance a + 1/2 > 11/12 from o, cuts off a cap of the disk, shaded, too thin for a unit square](figures/11-eight/axes.svg)

*Figure 11.13.* Lemma 11.19 for the pair $B$, $T$ of Figure 11.1, drawn in the
canonical frame of $B$. Of the eight signed axes only the four numbered ones
can separate a consecutive pair: beyond the far side of the source (dashed
line) the disk leaves a cap too thin for a unit square (shaded), and the
negative secondary axes point backwards round the cycle. Here axes 3 and 4
separate, with margin 0.

### Definition 11.20 (types, markers and costs)

Let $S_0, \dots, S_6$ be a boundary cycle at the level $Q_0$, with chosen
canonical frames. A square on $\mathcal O$ has the *type* $\mathsf L$,
$\mathsf M$ or $\mathsf H$ as $b/a$ lies in $[0, \frac14]$,
$[\frac14, \frac37]$ or $[\frac37, 1]$, and a square on $\mathcal C$ has the
type $\mathsf C$; a square on two pieces is given one of them. With
$a_0 = \sqrt{Q_0 - \frac14} - \frac12$ and $c_0 = \sqrt{Q_0/2} - \frac12$, the
*labels* of the types are

```math
\begin{aligned}
L_{\mathsf C}(a, b) &= 7.506931\left(\tfrac7{12} - a\right) + 1.077372\,b, & L_{\mathsf L}(a, b) &= 0.403875\,(a - a_0) + 1.089065\,b, \\
L_{\mathsf M}(a, b) &= -2.143075 + 1.489593\,a + 1.580219\,b, & L_{\mathsf H}(a, b) &= \tfrac\pi4 - 0.569472\,(a - c_0) + 0.390886\,(b - c_0),
\end{aligned}
```

all decimals being exact. The *marker* of $S_i$ is
$\ell_i = \sigma_i L_{X_i}(a_i, b_i)$, $X_i$ its type. For the pair $S_i$,
$S_{i+1}$ let $\varphi_i$ be the real angle from the canonical axis of $S_i$
to that of $S_{i+1}$ for which $\delta_i = \varphi_i + \alpha_i - \alpha_{i+1}$,
and let

```math
\chi(\varphi) = \tfrac12\left(|\sin\varphi| + |\cos\varphi| - 1\right) = \tau(\varphi) - 1
```

be the *frame charge*. The *cost* of the pair is
$\varphi_i - \frac9{50}\chi(\varphi_i) + \ell_i - \ell_{i+1}$.

The frame charge is 0 exactly when the two frames agree modulo quarter turns,
and it grows to $\frac{\sqrt2 - 1}2$ as they move apart to $\frac\pi4$. The
markers telescope round the cycle:

```math
\sum_{i=0}^6 \left(\varphi_i + \ell_i - \ell_{i+1}\right) = \sum_{i=0}^6 \varphi_i = \sum_{i=0}^6 \left(\delta_i - \alpha_i + \alpha_{i+1}\right) = 2\pi . \tag{11.6}
```

So a lower bound $\gamma_i$ for each cost gives
$2\pi - \frac9{50}\sum_i\chi(\varphi_i) > \sum_i\gamma_i$, whatever the
markers are, provided each square uses one marker on both of its edges.

*Lean: [`Eight.handGamma`](../../SquaresInCircles/Eight/Frames/Basic.lean#L78),
[`Eight.frameCost`](../../SquaresInCircles/Eight/Frames/Basic.lean#L131),
[`Eight.periodicFrameCost`](../../SquaresInCircles/Eight/Frames/Basic.lean#L135),
[`Eight.cyclic_markers_cancel`](../../SquaresInCircles/Eight/Frames/Basic.lean#L63),
[`Eight.FramePair.Branch`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L31),
[`Eight.FramePair.label`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L70),
[`Eight.FramePair.TypeMem`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L77),
[`Eight.FramePair.State`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L84),
[`Eight.FramePair.State.cost`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L98),
[`Eight.FramePair.branchOf`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L194),
[`Eight.FramePair.stateOf`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L267),
[`Eight.FramePair.pairAngle`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L291),
[`Eight.FramePair.pairAngle_gap`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L294).*

### Proposition 11.21 (pair costs of the four types)

For two consecutive squares of a boundary cycle at the level $Q_0$, of types
$X$ and $Y$, and for each of the four margins of (11.5) that is nonnegative,

```math
\varphi - \tfrac9{50}\chi(\varphi) + \sigma L_X(a, b) - \sigma' L_Y(a', b') > \Gamma_{XY}, \qquad
\Gamma = \begin{pmatrix} .9200 & .9100 & .9005 & .8833 \\ .9100 & .9100 & .9005 & .8833 \\ .9005 & .9005 & .8912 & .8926 \\ .8833 & .8833 & .8926 & .9099 \end{pmatrix}
```

in the order $\mathsf C, \mathsf L, \mathsf M, \mathsf H$ of the rows and the
columns.

*Proof.* The proposition is a family of continuous inequalities, one for each
ordered pair of types, signs and retained axis, each on the whole range of the
two states and of the angle. Two remarks reduce it. First, a separation along
a target axis is a separation along a source axis of the reversed pair, read
in the frame of the target, with both signs changed; the axes 2 and 3 become
the axes 4 and 1, and the cost does not change. So for each orientation of each
pair of types it suffices to treat the axes 1 and 4. Second, the angle is
$\varphi = \delta + \alpha' - \alpha$ with $\delta > \frac{19}{25}$ by (11.4)
and $|\alpha|, |\alpha'| \le \frac\pi4$, which bounds $\varphi$ from below;
for large $\varphi$ the cost exceeds $\Gamma_{XY}$ by the bounds
$\chi < \frac{21}{100}$ and the ranges of the labels alone.

In every remaining case the margin $M_j \ge 0$ is multiplied by a weight
$\lambda \ge 0$, a constant or a function of $\varphi$, and the cost is bounded
below by the cost minus $\lambda M_j$. For fixed $\varphi$ this is a sum of a
function of the source state and one of the target state, each a linear form
plus a label, and each state is replaced by its worst point on its arc, by one
of three supports:

* *the full circle*: on the outer curve
  $(a + \frac12)^2 + (b + \frac12)^2 = Q_0$,
  $p\,a + q\,b \ge -\sqrt{Q_0}\sqrt{p^2 + q^2} - \frac12(p + q)$ for all $p$,
  $q$ (Cauchy–Schwarz);
* *the ends of an arc*: along the outer curve $a$ is a concave function of
  $b$, so $p\,a + q\,b$ with $p \ge 0$ takes its least value on an arc at an
  end of the arc;
* *the core*: affine supports of the core corner at its diagonal point
  $(\frac12 + \frac{\sqrt2}{24}, \frac12 + \frac{\sqrt2}{24})$, and the side
  $a = \frac7{12}$ directly.

What remains is a function of $\varphi$ alone, shown to exceed $\Gamma_{XY}$
on intervals of $\varphi$ by concavity or monotonicity, from the signs of its
derivatives: for the full-circle support the norm
$N(\varphi) = \sqrt{p(\varphi)^2 + q(\varphi)^2}$ of a force that turns with
$\varphi$ satisfies $N'' + \frac14 N = (A^2 - B^2 - C^2)/(4N^3)$ for explicit
$A$, $B$, $C$, which gives its curvature, and the sines and cosines are bounded
at the ends of the intervals by Taylor polynomials. No other estimate enters;
in particular no case of this proposition needs a computation by the kernel.

The case analysis has sixteen families, one for each ordered pair of types
up to the reversal: core–core, where the two centres lie within $\frac45$ of
$o$ and 1 apart, so the gap exceeds $\frac43$ and the cost exceeds
$\frac{979}{1000} - \frac9{50} \cdot \frac{21}{100} > \frac{23}{25}$ outright;
the six families of a core and an outer square; the outer families
$\mathsf L\mathsf L$, $\mathsf L\mathsf M$, $\mathsf M\mathsf L$,
$\mathsf L\mathsf H$, $\mathsf H\mathsf L$ and $\mathsf M\mathsf M$; and the
families $\mathsf M\mathsf H$, $\mathsf H\mathsf M$, $\mathsf H\mathsf H$,
treated in the diagonal coordinates $d = a - b$, $a + b$, in which the outer
curve is the graph of the concave function $a + b = \sqrt{2Q_0 - d^2} - 1$ and,
for angles up to a quarter turn, only one of the axes 1 and 4 can separate.

*A representative case: two low squares* ($\Gamma_{\mathsf L\mathsf L} = \frac{91}{100}$).
On the low arc $a = A(b) = \sqrt{Q_0 - (b + \frac12)^2} - \frac12$ with
$0 \le b \le b_1$, where $b_1 = \frac{a_1}4$ and $(a_1, b_1)$ lies on the
circle. The label $L(b) = u\,(A(b) - a_0) + v\,b$, with
$u = \frac{3231}{8000}$ and $v = \frac{217813}{200000}$, is increasing, with
$0 \le L(b) \le b$ and $L(b) \le L_1 = L(b_1) < 0.30683$, since the slope
$(b + \frac12)/(A(b) + \frac12)$ of the arc lies in $(\frac{13}{50}, \frac{23}{50})$;
the angle offsets satisfy $|\arctan\frac ba| < \frac14$. The gap gives
$\varphi > \frac{19}{25} - \frac12 > 0$. For $\varphi \ge \frac\pi2$ the cost
is at least $\frac\pi2 - \frac9{50} \cdot \frac{21}{100} - 2L_1 > \frac{91}{100}$.
For $0 \le \varphi \le \frac\pi2$ the cost is
$\varphi - \frac9{100}(\cos\varphi + \sin\varphi - 1) + \sigma L(b) - \sigma' L(B)$
and $\tau(\varphi) = \frac12(1 + \sin\varphi + \cos\varphi)$.

*Axis 1, positive target.* Take $\lambda = \frac{189}{200}$ if $\sigma = +1$
and $\lambda = 1$ if $\sigma = -1$; the source then contributes
$\sigma(L(b) - \lambda b) \ge -\varepsilon$, with $\varepsilon = \frac1{50000}$
or $0$ (by concavity of $L - \lambda b$ along the arc and its value at $b_1$,
or by $L \le b$). Up to the cut $\varphi \le \frac{24}{25}$, respectively
$\frac{11}{10}$, the full-circle support on the target gives the bound
$G(\varphi) = \varphi + \frac9{100} + u\,a_0 + \frac12(u + v + \lambda) - \varepsilon + (\lambda - \frac9{100})\sin\varphi - \frac9{100}\cos\varphi - \sqrt{Q_0}\,N(\varphi)$
with $N(\varphi)^2 = (u + \lambda\sin\varphi)^2 + (\lambda\cos\varphi - v)^2$.
Taylor polynomials of the sine and cosine give a polynomial $T \le G - \frac{91}{100} + \sqrt{Q_0}N$
and a polynomial $\bar N^2 \ge N^2$, and $T^2 - Q_0\bar N^2$ is a polynomial of
degree 8 that is concave on the interval and positive at both ends; so
$T > \sqrt{Q_0}\,N$ and $G > \frac{91}{100}$. Beyond the cut the target term decreases in $B$, so $B = b_1$, and the
resulting function $E(\varphi)$ has $E > \frac{459}{500}$ and
$E' > -\frac3{50}$ at the cut and $E'' > \frac14$, so
$E \ge \frac{459}{500} - \frac3{50}x + \frac18x^2 > \frac{91}{100}$, $x$ the
distance from the cut.

*Axis 1, negative target.* With $\lambda = \frac{24}{25}$ the source gives
$\sigma(L(b) - \frac{24}{25}b) \ge -\frac{13}{1000}$, and the target term is
concave or monotone in $B$, so its least value is at $B = 0$ or $B = b_1$. At
$B = 0$ the bound is
$\frac{557}{1000} + \varphi + \frac{39}{100}\cos\varphi - (\frac{24}{25}a_0 - \frac{39}{100})\sin\varphi > \frac{91}{100}$,
and at $B = b_1$ an increasing function of $\varphi$ whose value at 0 exceeds
$\frac{91}{100}$.

*Axis 4.* With a positive target the margin is negative up to
$\varphi = \frac{13}{10}$; beyond, with $\lambda = \frac9{10}$, both terms
decrease along the arc, both states go to $b_1$, and the bound
$\varphi - 2L_1 + \frac{27}{50} - \frac9{10}a_1 + (\frac9{25} + \frac9{10}a_1)\cos\varphi + (\frac9{25} + \frac9{10}b_1)\sin\varphi$
exceeds $\frac{91}{100}$ on $[\frac{13}{10}, \frac\pi2]$, by concavity. With a
negative target, $\lambda = \frac54$ up to $\frac{13}{10}$ leaves two concave
endpoint functions above $\frac{91}{100}$, and beyond $\frac{13}{10}$ the cost
exceeds $\varphi - \frac9{50} \cdot \frac{21}{100} - L_1 > \frac{91}{100}$.
$\square$

*Lean:
[`Eight.FrameAllPairs.forward_pair`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L41),
[`Eight.FrameAllPairs.original_axis_pair`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L72),
[`Eight.FrameAllPairs.all_pair`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L81),
[`Eight.FrameAllPairs.continuous_pair_bound`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L86),
[`Eight.FramePair.State.target_primary_reverse`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L178),
[`Eight.FramePair.State.target_secondary_reverse`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L184),
[`Eight.FrameCircleArc.circle_linear_lower`](../../SquaresInCircles/Eight/Frames/CircleArc.lean#L142),
[`Eight.CircularNorm.curvature_identity`](../../SquaresInCircles/Eight/Owners/CircularNorm.lean#L75),
[`Eight.FramePair.core_cycle_pair`](../../SquaresInCircles/Eight/Frames/Pair/Domain.lean#L363),
[`Eight.FrameCoreLowPair.core_low_cycle_pair`](../../SquaresInCircles/Eight/Frames/Core/LowPair.lean#L1461),
[`Eight.FrameCoreMidPair.core_mid_cycle_pair`](../../SquaresInCircles/Eight/Frames/Core/MidPair.lean#L1036),
[`Eight.FrameCoreHighPair.core_high_cycle_pair`](../../SquaresInCircles/Eight/Frames/Core/HighPair.lean#L771),
[`Eight.FrameLowPair.low_cycle_pair`](../../SquaresInCircles/Eight/Frames/Low/Pair.lean#L1130),
[`Eight.FrameLowMidPair.low_mid_cycle_pair`](../../SquaresInCircles/Eight/Frames/Low/MidPair.lean#L1274),
[`Eight.FrameLowHighPair.low_high_cycle_pair`](../../SquaresInCircles/Eight/Frames/Low/HighPair.lean#L126),
[`Eight.FrameMidMidPair.middle_cycle_pair`](../../SquaresInCircles/Eight/Frames/Mid/HighQuarterStrip.lean#L1598),
[`Eight.FrameDiagonalPair.middle_high_cycle_pair`](../../SquaresInCircles/Eight/Frames/Diagonal/Pair.lean#L177),
[`Eight.FrameDiagonalPair.high_high_cycle_pair`](../../SquaresInCircles/Eight/Frames/Diagonal/Pair.lean#L193),
[`Eight.FrameLowPair.secondary_positive`](../../SquaresInCircles/Eight/Frames/Low/Pair.lean#L745),
[`Eight.FrameLowPair.full_circle_support`](../../SquaresInCircles/Eight/Frames/Low/Pair.lean#L657),
[`Eight.FrameLowPair.endpoint_support`](../../SquaresInCircles/Eight/Frames/Low/Pair.lean#L731),
[`Eight.four_type_cycle_budget`](../../SquaresInCircles/Eight/Frames/Basic.lean#L119).*

![Against the angle phi, for two low squares, the least value of the cost over the two low arcs and the four pairs of signs, for each axis, drawn only where that axis can separate and the gap exceeds 19/25: a blue curve for the axes 1 and 3, from phi about 0.44 to the right end of the graph, with a long flat bottom between 0.92 and 0.93 for phi from 0.8 to 1.4, and an orange curve for the axes 2 and 4, from phi about 1.14 on, falling to about 0.99 at pi/2 and rising again; both above the dashed horizontal line at 91/100, the bound Gamma_LL](figures/11-eight/pair.svg)

*Figure 11.14.* Proposition 11.21 for two low squares. For each angle
$\varphi$ and each axis, the least cost over the states of the two low arcs
and the signs for which that axis separates (curves), against the bound
$\Gamma_{\mathsf L\mathsf L} = \frac{91}{100}$ (dashed). Reversing the pair
exchanges the axes 1 and 3, and 2 and 4, and keeps both squares low, so the
four curves coincide in pairs. The curves are computed on a fine grid of
states; the proof bounds them from below by the supports above.

### Lemma 11.22 (closed walks)

For every sequence of types $X_0, \dots, X_6, X_7 = X_0$,

```math
\sum_{i=0}^6 \Gamma_{X_i X_{i+1}} \ge 7 \cdot 0.8833 + 0.0265 = \tfrac{3881}{625} .
```

*Proof.* Multiply by $10^4$, so that the entries of $\Gamma$ are integers. Let
$\Gamma^{(2)}(X, Z) = \min_Y\left(\Gamma_{XY} + \Gamma_{YZ}\right)$ be the least
weight of a walk of two steps from $X$ to $Z$, the min-plus square of $\Gamma$.
The walk of seven steps splits into the three walks
$X_0X_1X_2$, $X_2X_3X_4$, $X_4X_5X_6$ of two steps and the step $X_6X_0$, so
its weight is at least
$\Gamma^{(2)}(X_0, X_2) + \Gamma^{(2)}(X_2, X_4) + \Gamma^{(2)}(X_4, X_6) + \Gamma_{X_6X_0}$.
The $4^3$ inequalities defining $\Gamma^{(2)}$ and the $4^4$ inequalities
saying that this sum is at least $62096$ for all $X_0, X_2, X_4, X_6$ are
finite checks on integers, decided by the Lean kernel. $\square$

The bound is attained: the walk
$\mathsf C\mathsf M\mathsf H\mathsf C\mathsf H\mathsf C\mathsf H$, back to
$\mathsf C$, weighs $0.9005 + 0.8926 + 5 \cdot 0.8833 = 6.2096$
(Figure 11.15).

*Lean:
[`Eight.four_type_seven_walk`](../../SquaresInCircles/Eight/Frames/Basic.lean#L109),
[`Eight.four_type_seven_walk_numerator`](../../SquaresInCircles/Eight/Frames/Basic.lean#L92).*

![The four types C, L, M and H drawn as the corners of a square, joined by six edges and with a loop at each corner, each labelled with its entry of Gamma minus 0.8833: the loop at M has the smallest residual, 0.0079, the edges from M to C and to L have 0.0172, the edge from M to H 0.0093, the loops at C, L and H 0.0367, 0.0267 and 0.0266, and the edges from H to C and to L have residual 0. A closed walk of length seven, C, M, H, C, H, C, H and back to C, is highlighted along the edges from C to M, from M to H and from H to C](figures/11-eight/walks.svg)

*Figure 11.15.* Lemma 11.22. The residuals $\Gamma_{XY} - 0.8833$ on the
loops and edges of the four types; every closed walk of length seven picks up
at least $0.0265$ of them. The highlighted walk
$\mathsf{C}\mathsf{M}\mathsf{H}\mathsf{C}\mathsf{H}\mathsf{C}\mathsf{H}$
(back to $\mathsf C$) attains $0.0172 + 0.0093 = 0.0265$: the bound is the
least weight of a closed walk.

### Theorem 11.23 (frame concentration)

Let eight unit squares form a packing in a closed disk of squared radius
$q \le Q_1$ about $o$. Then the frames of the seven exterior squares,
taken modulo $\frac\pi2$, have real representatives $\theta_0, \dots, \theta_6$
that lie in an interval of length less than $\frac7{10}$.

*Proof.* By Theorem 11.10 the exterior squares, in the order of their centre
directions and with any witnesses, form a neighbour cycle; by
Proposition 11.15 there is a boundary cycle with the same frames, at the
level $\max(q, q_-)$, and by Lemma 11.17 it can be expanded to the level
$Q_0$, again with the same frames and with each witness still separating. By
Lemma 11.19 each witness is one of the four retained axes, so
Proposition 11.21 applies to every pair. Summing it round the cycle, with
(11.6), Lemma 11.22 and $2\pi < \frac{710}{113}$,

```math
2\pi - \tfrac9{50}U > \tfrac{3881}{625}, \qquad U = \sum_{i=0}^6 \chi(\varphi_i) < \tfrac{50}9\left(\tfrac{710}{113} - \tfrac{3881}{625}\right) = \tfrac{10394}{25425} . \tag{11.7}
```

The charge $\chi$ has the period $\frac\pi2$ and is even, and on
$[0, \frac\pi4]$ it equals $g(x) = \frac12(\cos x + \sin x - 1)$, which is
increasing and concave with $g(0) = 0$ and $g(\frac\pi4) = \frac{\sqrt2 - 1}2$.
So $\chi(\varphi_i) = g(|x_i|)$, where $x_i \in [-\frac\pi4, \frac\pi4]$ is the
shortest signed angle from the frame of $S_i$ to that of $S_{i+1}$ modulo
$\frac\pi2$. The lower Taylor polynomials of sine and cosine give
$2g(\frac7{10}) > \frac{2945220061}{7200000000} > \frac{10394}{25425}$; hence
$U < 2g(\frac7{10}) < 2g(\frac\pi4) = \sqrt2 - 1$. By concavity,
$g(x) \ge \frac{g(\pi/4)}{\pi/4}\,x$ on $[0, \frac\pi4]$, so

```math
\sum_i |x_i| \le \frac{\pi/4}{g(\pi/4)}\,U < \frac{\pi/4}{(\sqrt2 - 1)/2}\,(\sqrt2 - 1) = \frac\pi2 .
```

The sum of the $x_i$ is a multiple of $\frac\pi2$, since the walk returns to
the frame it started from, and it is smaller than $\frac\pi2$ in absolute
value, so it is 0. Choose a real representative $\theta_0$ of the frame of
$S_0$ and put $\theta_{i+1} = \theta_i + x_i$; then $\theta_i$ represents the
frame of $S_i$, and $\theta_7 = \theta_0$. Let $D$ be their range; then $D \le \frac12\sum|x_i| < \frac\pi4$.
On the circle of circumference $\frac\pi2$, $g$ of the shorter distance is a
metric (for two distances adding up to at most $\frac\pi4$ the triangle
inequality is the subadditivity of the concave $g$ with $g(0) = 0$, and for
larger sums the linear lower bound above gives it). The closed walk goes from
a lowest to a highest representative and back, and the shorter distance
between those two frames is $D$; so $U \ge 2g(D)$. As
$2g(D) \le U < 2g(\frac7{10})$ and $g$ increases, $D < \frac7{10}$. The frames
of the boundary cycle are those of the packing. $\square$

*Lean:
[`Eight.FrameConcentration.charged_cycle_budget`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L118),
[`Eight.FrameConcentration.charge_budget`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L126),
[`Eight.FrameConcentration.quarter_lift`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L131),
[`Eight.FramePhysicalTransport.quarter_lift`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L178),
[`Eight.quarterLift_of_cost`](../../SquaresInCircles/Eight/Boundary/CycleActions.lean#L497),
[`Eight.physical_frame_lift_of_cost`](../../SquaresInCircles/Eight/Frames/Basic.lean#L420),
[`Eight.frameCost_concave`](../../SquaresInCircles/Eight/Frames/Basic.lean#L219),
[`Eight.frameCost_monotone`](../../SquaresInCircles/Eight/Frames/Basic.lean#L154),
[`Eight.frameCost_triangle`](../../SquaresInCircles/Eight/Frames/Basic.lean#L265),
[`Eight.frameCost_seven_tenths`](../../SquaresInCircles/Eight/Frames/Basic.lean#L295),
[`Eight.closed_walk_range_bound`](../../SquaresInCircles/Eight/Frames/Basic.lean#L172),
[`Eight.Arithmetic.two_pi_lt_710_over_113`](../../SquaresInCircles/Eight/Arithmetic/Taylor.lean#L34).*

The bound $\frac7{10}$ is about $40°$; in the optimal packing the range is
$t_* \approx 7.08°$ (Figure 11.16). The theorem says that the exterior squares
cannot turn far from one another; it does not yet say which quarter turns
separate their frames.

![The circle of frame directions modulo a quarter turn, of circumference pi/2, drawn as a circle: the frames of the five axis-parallel exterior squares A, B, T, D, E sit at one point, those of H and G at another point 7.08 degrees further; an arc of length 7/10 starting at the first point is marked as the bound of Theorem 11.23. Beside it, the graph of the frame charge chi on [0, pi/4], increasing and concave from 0 to (root 2 - 1)/2, with its chord and its value at t* marked](figures/11-eight/frames.svg)

*Figure 11.16.* Left: the frames of the exterior squares of Figure 11.1 on
the circle of directions modulo $\frac\pi2$; they span $t_*$, far less than
the bound $\frac7{10}$ of Theorem 11.23 (arc). Right: the frame charge
$\chi = g$ on $[0, \frac\pi4]$ and its chord, the linear lower bound of the
proof.

## 11.6 Quarter words

Theorem 11.23 puts the frames of the exterior squares close together modulo
quarter turns. Going round the cycle, the canonical frame of each square is
then a whole number of quarter turns ahead of that of the previous one, up to
a small error, and these numbers form a word.

### Definition 11.24 (quarter words)

Let $S_0, \dots, S_6$ be a neighbour cycle, with real representatives
$\theta_i$ of the frames in an interval of length $D < \frac7{10}$, extended by
$\theta_{i+7} = \theta_i$, and with real centre directions $\beta_i$ increasing
by the gaps, $\beta_{i+1} = \beta_i + \delta_i$, so that
$\beta_{i+7} = \beta_i + 2\pi$. A choice of canonical frames gives integers
$m_i$ with

```math
\beta_i + \alpha_i = \theta_i + m_i\tfrac\pi2, \qquad m_{i+7} = m_i + 4,
```

where $\alpha_i \in [-\frac\pi4, \frac\pi4]$ is as in Definition 11.14. The
*quarter word* of the cycle is $k = (k_0, \dots, k_6)$, $k_i = m_{i+1} - m_i$.
With $d_i = \theta_{i+1} - \theta_i$,

```math
\varphi_i = k_i\tfrac\pi2 + d_i, \qquad \delta_i = \varphi_i + \alpha_i - \alpha_{i+1}, \qquad \sum_{i=0}^6 k_i = 4 . \tag{11.8}
```

*Lean:
[`Eight.QuarterLift`](../../SquaresInCircles/Eight/Words/Basic.lean#L164),
[`Eight.QuarterLift.word`](../../SquaresInCircles/Eight/Words/Basic.lean#L263),
[`Eight.QuarterLift.edge_identity`](../../SquaresInCircles/Eight/Words/Basic.lean#L180),
[`Eight.integerQuarterIncrement_sum`](../../SquaresInCircles/Eight/Words/Basic.lean#L157).*

The words are read up to the symmetries of the cycle: a cyclic shift of the
indices, and a reflection of the plane, which reverses the order of the
centres and so reverses the word.

### Lemma 11.25 (seven words)

In a neighbour cycle at a level $q \le Q_0$ with frames as in
Definition 11.24, every $k_i$ is 0, 1 or 2, the word has no three
consecutive zeros (cyclically), and at most one 2. Up to the symmetries of
the cycle it is one of the seven words

```math
0010012, \quad 0010102, \quad 0010201, \quad 0011002, \quad 0010111, \quad 0011011, \quad 0101011 .
```

*Proof.* By (11.8), $|d_i| \le D < \frac7{10}$ and
$|\alpha_i - \alpha_{i+1}| \le \frac\pi2$. If $k_i \le -1$, then
$\delta_i \le -\frac\pi2 + D + \frac\pi2 < \frac7{10}$, against (11.4). If
$k_i \ge 3$, then $\delta_i \ge \frac{3\pi}2 - D - \frac\pi2 > \pi - \frac7{10}$,
which exceeds $2\pi - \frac{114}{25}$ since $\pi < \frac{193}{50}$, again
against (11.4). If $k_i = k_{i+1} = k_{i+2} = 0$, then

```math
\delta_i + \delta_{i+1} + \delta_{i+2} = \theta_{i+3} - \theta_i + \alpha_i - \alpha_{i+3} < \tfrac7{10} + \tfrac\pi2 < \tfrac{57}{25} = 3 \cdot \tfrac{19}{25} ,
```

against (11.4). Two digits 2 would leave five zeros among the other five
digits, which, cut by the two 2s into two cyclic runs, would include a run of
three zeros.

The words with no 2 have four 1s and three 0s; the runs of zeros in the four
gaps between the 1s have lengths at most two and add up to three, so their
lengths are $1, 1, 1, 0$ or $2, 1, 0, 0$ in some order. The first gives one
word up to symmetry, $0101011$, and the second two, as the runs of lengths 2
and 1 are adjacent or not: $0010111$ and $0011011$. The words with one 2 have
two 1s and four 0s in three runs, of lengths $2, 2, 0$ or $2, 1, 1$; in either
case the exceptional run may lie between the two 1s or next to the 2, and the
two positions next to the 2 are exchanged by the reflection. This gives the
four words $0010012$, $0010102$, $0010201$ and $0011002$. $\square$

*Lean:
[`Eight.QuarterLift.digit_range`](../../SquaresInCircles/Eight/Words/Basic.lean#L216),
[`Eight.QuarterLift.no_three_zero_increments`](../../SquaresInCircles/Eight/Words/Basic.lean#L243),
[`Eight.QuarterLift.word_admissible`](../../SquaresInCircles/Eight/Words/Basic.lean#L273),
[`Eight.quarter_word_complete_classification`](../../SquaresInCircles/Eight/Words/Basic.lean#L130).*

![Top: the seven quarter words of Lemma 11.25 drawn as necklaces of seven beads, the digits 0, 1 and 2 shown as white, light and dark beads, with the last one, 0101011, highlighted. Below: the exterior squares of the optimal packing with the canonical axis of each square drawn as an arrow near its centre direction; the arrows of H and G, A and B, T and D, and E point in the directions minus a quarter turn, 0, a quarter turn and a half turn from the frame of A, and each edge of the cycle is labelled with its digit 0 or 1](figures/11-eight/words.svg)

*Figure 11.17.* Top: the seven words of Lemma 11.25 as necklaces (white 0,
light 1, dark 2). Below: the word of Figure 11.1. The canonical axes
(arrows) of $H, G, A, B, T, D, E$ are $-1, -1, 0, 0, 1, 1, 2$ quarter turns
ahead of that of $A$, up to the small tilt of $H$ and $G$, so the word,
starting at $H$, is $0101011$.

### Lemma 11.26 (a boosted edge)

Let $S_0, \dots, S_6$ be a boundary cycle at the level $Q_0$, with frames as in
Definition 11.24, the markers $\ell_i$ of Definition 11.20 and the frame steps
$d_i = \theta_{i+1} - \theta_i$. Then no edge $i$ has

```math
\varphi_i + \ell_i - \ell_{i+1} + \tfrac9{50}\chi(d_i) > \tfrac{197}{200} .
```

*Proof.* By Proposition 11.21 and Lemma 11.19, every other edge $k$ has
$\varphi_k + \ell_k - \ell_{k+1} - \frac9{50}\chi(d_k) > \Gamma \ge 0.8833$, where
$\chi(\varphi_k) = \chi(d_k)$ as $\chi$ has the period $\frac\pi2$. The steps
return, $\sum_k d_k = 0$, and they are shorter than $\frac7{10} < \frac\pi4$, so
$|d_i| \le \sum_{k \ne i}|d_k|$ and, as $\chi = g(|\cdot|)$ there with $g$
increasing and subadditive (Theorem 11.23), $\chi(d_i) \le \sum_{k \ne i}\chi(d_k)$.
Summing all seven costs, by (11.6),

```math
2\pi = \sum_k \left(\varphi_k + \ell_k - \ell_{k+1}\right) > \tfrac{197}{200} - \tfrac9{50}\chi(d_i) + 6 \cdot 0.8833 + \tfrac9{50}\sum_{k \ne i}\chi(d_k) \ge \tfrac{197}{200} + 5.2998 = 6.2848 ,
```

which exceeds $\frac{710}{113} > 2\pi$. $\square$

*Lean:
[`Eight.ZeroPrimary.no_primary_of_return_pair_costs`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L844),
[`Eight.GlobalZeroSign.closed_boost_impossible`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L43),
[`Eight.ZeroPrimary.frame_edge_le_return`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L808),
[`Eight.ZeroPrimary.handGamma_lower`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L838),
[`Eight.QuarterWordGeometry.marker_budget`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L274).*

A single edge whose cost, with its frame charge added back, exceeds
$\frac{197}{200}$ is therefore impossible: the six other edges cost at least
$0.8833$ each, and the closed tour of the frames pays the charge of the special
edge. This lemma is used for the digit-0 edges below and for the quarter edges
of §11.8.

### Lemma 11.27 (edges with the digit 0)

Let $S_0, \dots, S_6$ be a boundary cycle at a level $\frac52 \le q \le Q_0$,
with frames as in Definition 11.24, and let the edge $i$ have the digit
$k_i = 0$. Then each retained axis that separates $S_i$ from $S_{i+1}$ is the
axis 1, and then $\tau_i > 0$, or the axis 3, and then $\tau_{i+1} < 0$.

*Proof.* By Lemma 11.17 we may expand the cycle to $Q_0$: the frames, digits and
tangents do not change and every separating axis still separates. Here
$\varphi_i = d_i$, and the gap is $\delta_i = d_i + \alpha_i - \alpha_{i+1} > \frac{19}{25}$.

*Axes 2 and 4.* If the axis 2 separates, then $M_2 \ge 0$ and the gap force
$\frac9{20} < d_i \le \frac7{10}$, a positive source with $b_i > 0$ and an outer
target with $a_{i+1} > 1$. Subtracting $\lambda M_2 \ge 0$ from the cost,
with $\lambda = m/\sin d_i$, where $m = \frac45$ for an outer source and
$m = \frac{107}{100}$ for a core source, and bounding the target marker by its
supports, gives
$\varphi_i + \ell_i - \ell_{i+1} + \frac9{50}\chi(d_i) > \frac{197}{200}$: in the
variable $\tan\frac{d_i}2$ the difference is a polynomial of degree 8 whose
coefficients are nonnegative after a shift of the variable. Lemma 11.26
excludes this. The axis 4 is the axis 2 of the reversed pair.

*Signs.* If the axis 1 separates and $\tau_i \le 0$, the margin $M_1 \ge 0$
forces $\frac{29}{100} < d_i \le \frac7{10}$, a negative target and
$b_i < \frac12$. Subtract $\frac{111}{100}M_1$, bound the unsigned labels by
$\frac45 b$ from below and, as $b_i < \frac12$, by $\frac{111}{100}b_i$ from
above, and replace the target by its circle support: the cost plus the charge
is at least

```math
d + \tfrac{13}{200} + \tfrac65\left(\sin d + \cos d\right) - \sqrt{Q_0}\sqrt{K - M\cos d}, \qquad K = \tfrac{18721}{10000}, \quad M = \tfrac{222}{125},
```

which exceeds 1 on $[\frac{29}{100}, \frac7{10}]$: it is concave there and
exceeds 1 at both ends. Lemma 11.26 excludes this. The axis 3 with
$\tau_{i+1} \ge 0$ is the reflected case. $\square$

*Lean:
[`Eight.GlobalZeroSign.classify`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L173),
[`Eight.GlobalZeroSign.secondary`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L158),
[`Eight.GlobalZeroSign.source_positive`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L129),
[`Eight.GlobalZeroSign.target_negative`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L144),
[`Eight.ZeroPrimary.original_zero_secondary`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L891),
[`Eight.ZeroPrimary.target_primary_domain`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L68),
[`Eight.ZeroPrimary.target_primary_boost`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L688),
[`Eight.ZeroPrimary.actual_boost`](../../SquaresInCircles/Eight/Words/Zero/PrimaryCycle.lean#L743),
[`Eight.GlobalZeroSign.source_secondary_domain`](../../SquaresInCircles/Eight/Owners/Zero/SignSupport.lean#L245),
[`Eight.GlobalZeroSign.source_secondary_boost`](../../SquaresInCircles/Eight/Owners/Zero/SignSupport.lean#L311),
[`Eight.GlobalZeroSign.scalar_gt_one`](../../SquaresInCircles/Eight/Owners/Zero/SignSupport.lean#L146).*

### Proposition 11.28 (only the word 0101011)

In a boundary cycle at a level $q \le Q_0$ whose frames lie in an interval of
length less than $\frac7{10}$, the quarter word is $0101011$ up to the
symmetries of the cycle.

*Proof.* Expand the cycle to the level $Q_0$ (Lemma 11.17); its word does not
change. A rotation of the indices or a reflection of the plane, which reverses
the cycle, turns the word into one of the seven words of Lemma 11.25 literally,
and each of the six other words is excluded by a whole-cycle bound: markers
$\ell_i$, one per square, a function of its state, sign and radial curve, and
lower bounds $\gamma_i$ for the costs $\varphi_i + \ell_i - \ell_{i+1}$ of the
seven pairs, valid for every separating retained axis (Lemma 11.19), all
states on $\mathcal O$ and $\mathcal C$, all signs and all angles allowed by
(11.4) and Definition 11.24, with $\sum_i\gamma_i > 2\pi$, against (11.6).

*The four words with a 2.* One pair of markers serves all four words:

```math
L_{\mathcal O}(a, b) = -\tfrac9{100} + \tfrac{13}{200}a + \tfrac{203}{200}b, \qquad L_{\mathcal C}(a, b) = \tfrac{73}{10}\left(\tfrac7{12} - a\right) + \tfrac{291}{250}b ,
```

$\ell_i = \sigma_i L_{\mathcal O}$ or $\sigma_i L_{\mathcal C}$ as $S_i$ is on
$\mathcal O$ or on $\mathcal C$. The cost of a pair exceeds $\frac{391}{400}$,
$\frac{157}{200}$, $\frac{163}{200}$ when its digit is 0, 1, 2. A word with
one 2, two 1s and four 0s therefore has costs adding up to more than
$4 \cdot \frac{391}{400} + 2 \cdot \frac{157}{200} + \frac{163}{200} = \frac{1259}{200}$,
which exceeds $\frac{44}7 > 2\pi$.

*The word 0010111.* The markers are affine, $c + p\,a + \sigma q\,b$, with
coefficients that depend on the role of the square in the word, its sign and
its radial curve. The costs exceed $\frac{359}{400}$ on the third edge and
$\frac{17953}{20000}$ on the six others, in all more than
$\frac{31417}{5000} = 6.2834$, which exceeds $2\pi$.

*The word 0011011.* The markers are quadratic,
$\sigma(c + p\,a + q\,b + r\,b^2 + s\,ab)$, with coefficients that depend on the
role, the sign and the radial curve. The costs exceed $\frac{17953}{20000}$ on
every edge, in all more than $\frac{125671}{20000} = 6.28355$, which exceeds
$2\pi$. $\square$

*Lean:
[`Eight.QuarterWordGeometry.quarter_word_candidate`](../../SquaresInCircles/Eight/Words/QuarterWordSelection.lean#L19),
[`Eight.QuarterWordGeometry.three_binary_classes`](../../SquaresInCircles/Eight/Words/FirstNegativeOutsideEntry.lean#L523),
[`Eight.QuarterWordGeometry.no_double`](../../SquaresInCircles/Eight/Words/FirstNegativeOutsideEntry.lean#L487),
[`Eight.QuarterWordGeometry.common_pair`](../../SquaresInCircles/Eight/Words/FirstNegativeOutsideEntry.lean#L470),
[`Eight.QuarterWordGeometry.commonMarker`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L253),
[`Eight.WordProblems.commonGamma`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L58),
[`Eight.double_word_cost_numerator`](../../SquaresInCircles/Eight/Words/Basic.lean#L301),
[`Eight.no_double_word_of_cost_bound`](../../SquaresInCircles/Eight/Words/Basic.lean#L315),
[`Eight.ShortWord.not_dihedral`](../../SquaresInCircles/Eight/Words/Short/WordExclusion.lean#L56),
[`Eight.ShortWord.excluded`](../../SquaresInCircles/Eight/Words/Short/WordExclusion.lean#L44),
[`Eight.ShortWord.actual_edge`](../../SquaresInCircles/Eight/Words/Short/WordExclusion.lean#L24),
[`Eight.ShortWord.threshold_total`](../../SquaresInCircles/Eight/Words/Short/WordExclusion.lean#L38),
[`Eight.SecondWord.not_dihedral`](../../SquaresInCircles/Eight/Words/Second/WordExclusion.lean#L246),
[`Eight.SecondWord.actual_edge`](../../SquaresInCircles/Eight/Words/Second/WordExclusion.lean#L201),
[`Eight.QuarterWordGeometry.wrongMarker`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L270),
[`Eight.WordProblems.wrongGamma`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L98),
[`Eight.QuarterWordGeometry.normalize_word`](../../SquaresInCircles/Eight/Words/QuarterWordGeometry.lean#L353).*

The three cost bounds are families of continuous inequalities, one for each
digit or edge, each pair of radial curves, each pair of signs and each
retained axis, on the whole range of the states and of the angle. Their proofs
follow the pattern of Proposition 11.21, and the structure of the case analysis
is the following.

*Reductions.* A target axis is a source axis of the reversed pair, so only the
axes 1 and 4 are treated for each orientation; the angle is written
$\varphi = k\frac\pi2 \pm x$ with $0 \le x \le \frac7{10}$, and the two halves
are treated separately. The signs are not all free. On an edge with digit 0,
(11.8) gives $\delta_i = d_i + \alpha_i - \alpha_{i+1}$, so
$\alpha_i \le 0 \le \alpha_{i+1}$ would make $\delta_i < \frac7{10}$; and both
wrong binary words begin with two edges of digit 0, along which
$\alpha_0 - \alpha_2 > 2 \cdot \frac{19}{25} - \frac7{10} = \frac{41}{50}$, so the
first square has $\alpha_0 > 0$ and the third $\alpha_2 < 0$. This leaves 19
combinations of an edge and a pair of signs for each of the two words. On the
edges with digit 0, Lemma 11.27 leaves the axes 1 and 3 only.

*Branches.* The common bound splits by the digit and then by the axis and the
signs; the two wrong words split by the digit of the edge, by the radial
curves of the two squares (outer–outer, mixed, core–core), by the pair of signs
and by the axis. Each branch is closed in the manner of Proposition 11.21: the
margin is multiplied by a weight, constant or optimized, the two states are
replaced by their worst points by circle supports, completed squares or the
ends of their arcs, and the resulting function of the angle is shown to exceed
its bound by concavity, monotonicity or a compact minimum on a contact curve,
with Taylor polynomials at the ends. Two core squares have centres within
$\frac45$ of $o$, so their gap exceeds $\frac{27}{20}$, and their branches close
by the bounds of the markers. In four branches of the two wrong words the final
inequality is a polynomial inequality in one variable, of degree up to 26,
which the kernel checks (§11.11).

*A representative case.* Edge 5 of the word $0010111$, with digit 1, a source of
sign $-1$ and a target of sign $+1$, both outer, separated along the axis 1, on
the upper half $\varphi = \frac\pi2 + x$, $0 \le x \le \frac7{10}$. The claim is
that the cost exceeds $\frac{8981}{10000}$, more than the bound
$\frac{17953}{20000}$:

```math
\tfrac\pi2 + x + c + p\,a - q\,b - P A - t B > \tfrac{8981}{10000}, \qquad (c, p, q, P, t) = \left(\tfrac{50283}{10^5}, -\tfrac{20967}{10^5}, \tfrac{83048}{10^5}, \tfrac{21826}{10^5}, \tfrac{83472}{10^5}\right),
```

where $(a, b)$ and $(A, B)$ are the source and target states and the left side
is $\varphi + \ell_5 - \ell_6$ for the markers of the word. The separation reads
$\frac12(1 + \cos x + \sin x) \le -b + A\cos x + B\sin x$. Multiply it by
$l \ge 0$ and add. For an outer state and $m > 0$, the circle equation gives
$X(a + \frac12) + Y(b + \frac12) \ge -m\,Q_0 - \frac{X^2 + Y^2}{4m}$, a completed
square; apply it to the source with $m = \frac{11}{200}$ and to the target with
$m = \frac{41}{125}$. This leaves a quadratic function of $l$,

```math
\text{cost} \ge \tfrac\pi2 + x + k_0 + \beta(x)\,l - \alpha\,l^2, \qquad \alpha = \tfrac{9575}{1804}, \quad \beta(x) = \tfrac{q}{2\mu} + \left(1 - \tfrac P{2\nu}\right)\cos x + \left(1 - \tfrac t{2\nu}\right)\sin x > 0 ,
```

with $\mu = \frac{11}{200}$, $\nu = \frac{41}{125}$ and an explicit constant
$k_0$, and the best weight $l = \beta/(2\alpha)$ gives the bound
$V(x) = \frac\pi2 + x + k_0 + \beta(x)^2/(4\alpha)$. Its derivative is
$1 + \beta\beta'/(2\alpha)$, and with $X = \tan\frac x2 \in [0, \frac38)$ the
product $(1 + X^2)^2\,V'(x)$ is a quartic polynomial $Q(X)$ with rational
coefficients. The kernel checks that the coefficients of
$Q(X) - \Lambda(X)$, with
$\Lambda(X) = \frac{789}{1000} - \frac{1047}{1000}X + \frac{1051}{500}X^2 - \frac{899}{1000}X^3 + \frac{1173}{1000}X^4$,
are positive in degree 0 and nonnegative in degrees 1 to 4, so $Q > \Lambda$
for $X \ge 0$, and $\Lambda > \frac{17}{50}$ on $[0, \frac38]$. So $V$ is
increasing, and $V(0) > \frac{8981}{10000}$.

*Lean:
[`Eight.ShortOuterOne.OppositeFive.UpperSecondary.original`](../../SquaresInCircles/Eight/Words/Short/Outer/One/OppositePrimaryUpperOneDiagonal.lean#L453),
[`Eight.ShortOuterOne.OppositeFive.UpperSecondary.quartic`](../../SquaresInCircles/Eight/Words/Short/Outer/One/OppositePrimaryUpperOneDiagonal.lean#L343),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L308),
[`Eight.ShortWord.Zero.actual`](../../SquaresInCircles/Eight/Words/Short/WordZero.lean#L56),
[`Eight.ShortWord.OuterQuarter.actual`](../../SquaresInCircles/Eight/Words/Short/Outer/Quarter.lean#L58),
[`Eight.ShortWord.MixedQuarter.actual`](../../SquaresInCircles/Eight/Words/Short/Mixed/Quarter.lean#L874),
[`Eight.WrongWordCore.actual_core_pair`](../../SquaresInCircles/Eight/Words/Wrong/ZeroOriginalOwners.lean#L280),
[`Eight.SecondWord.OuterQuarter.actual`](../../SquaresInCircles/Eight/Words/Second/Outer/Quarter.lean#L54),
[`Eight.SecondWord.OuterZero.actual`](../../SquaresInCircles/Eight/Words/Second/Outer/Opposite/ZeroCycle.lean#L1310),
[`Eight.SecondWord.MixedQuarter.actual`](../../SquaresInCircles/Eight/Words/Second/Mixed/Quarter.lean#L205),
[`Eight.SecondWord.MixedZero.actual`](../../SquaresInCircles/Eight/Words/Second/Mixed/Zero.lean#L154),
[`Eight.SecondWord.CoreCore.actual`](../../SquaresInCircles/Eight/Words/Second/WordExclusion.lean#L152),
[`Eight.CommonQuarter.actual_zero`](../../SquaresInCircles/Eight/Words/Common/Zero.lean#L298),
[`Eight.CommonQuarter.actual_one`](../../SquaresInCircles/Eight/Words/Common/One.lean#L612),
[`Eight.CommonQuarter.actual_jump_two`](../../SquaresInCircles/Eight/Words/Common/JumpTwo.lean#L596),
[`Eight.WrongZeroOriginalOwners.original`](../../SquaresInCircles/Eight/Words/Wrong/ZeroOriginalOwners.lean#L342).*

## 11.7 The candidate frame and the signed cycle

From now on the word is $0101011$, and the squares get the roles of
Figure 11.1. This section fixes the coordinates of the rest of the proof.

### Definition 11.29 (candidate frames)

Let $S_0, \dots, S_6$ be a boundary cycle at a level $q \le Q_0$ with the quarter
word $0101011$, indexed so that $k = (0, 1, 0, 1, 0, 1, 1)$, and name the
squares

```math
(S_0, \dots, S_6) = (H, G, A, B, T, D, E) .
```

The edges $H \to G$, $A \to B$ and $T \to D$ have the digit 0, and
$G \to A$, $B \to T$, $D \to E$ and $E \to H$ the digit 1. A *candidate frame*
of the cycle is a choice of real representatives $\theta_H, \dots, \theta_E$ of
the frames with $\theta_A = 0$ and $|\theta_i - \theta_j| < \frac7{10}$, such
that the canonical axis of $S_i$ points in the direction
$\theta_i + m_i\frac\pi2$, with the *offsets*

```math
(m_H, m_G, m_A, m_B, m_T, m_D, m_E) = (-1, -1, 0, 0, 1, 1, 2) .
```

The *frame steps* are $d_i = \theta_{i+1} - \theta_i$, and the angles of
Definition 11.20 are $\varphi_i = k_i\frac\pi2 + d_i$. The cycle with its
candidate frame is *normalized* if moreover $\tau_E \le 0$. In the optimal
packing $\theta_H = \theta_G = t_*$ and the other five representatives vanish.

*Lean:
[`Eight.Candidate.word`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L51),
[`Eight.Candidate.offsets`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L52),
[`Eight.Candidate.Frame`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L80),
[`Eight.Candidate.Frame.physical_angle`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L93),
[`Eight.Candidate.delta`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L55),
[`Eight.Candidate.phi`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L56),
[`Eight.Candidate.EHalf`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L107).*

### Lemma 11.30 (normalization)

Let a boundary cycle at the level $Q_1$ have its frames in an interval of length
less than $\frac7{10}$ and the word $0101011$ up to the symmetries of the cycle.
After a renumbering of its squares, a rotation of the plane about $o$ and
possibly a reflection, it is normalized, with a candidate frame.

*Proof.* A rotation of the indices, or a reflection of the plane followed by a
reversal of the order, turns the word into $0101011$ itself, and a rotation of
the plane about $o$ makes $\theta_A = 0$. Reflecting the plane in a line through
$o$ and renumbering the squares by $i \mapsto 5 - i$ modulo 7 restores the cyclic
order and keeps the word, since $k_{4 - i} = k_i$ for the word $0101011$ read
from $H$; it sends the roles $(H, G, A, B, T, D, E)$ to $(D, T, B, A, G, H, E)$
and fixes $E$. A reflection exchanges the two sides of each centre direction,
so it changes the sign of every signed tangent; one of the two orientations has
$\tau_E \le 0$. $\square$

*Lean:
[`Eight.boundary_candidate_normalization`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L462),
[`Eight.candidate_normalization_of_word`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L430),
[`Eight.candidateFrameOfWordAction`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L388),
[`Eight.CycleAction.candidateMirror`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L344),
[`Eight.CycleAction.candidateMirror_E`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L355),
[`Eight.candidate_word_mirror`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L370),
[`Eight.CandidateNormalization`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L422).*

The motions of the lemma act on the whole packing at once: the renumbering, the
rotation and the reflection are applied to the eight squares, to their
boundary cycle and to its expansions, which keeps every square, every frame and
every separating axis (§11.12).

### Definition 11.31 (signed cycles)

For a boundary cycle with a candidate frame, the *signed point* of the square
$S_i$ is $(a_i, y_i)$ with $y_i = \sigma_i b_i$, so that $|y_i| \le a_i$, $y_i$
has the sign of the signed tangent $\tau_i = y_i/a_i$, and the centre of $S_i$
is $a_i e_i - y_i f_i$ in its canonical frame $e_i$, $f_i$. The *signed cycle*
is the list of the seven signed points with the representatives $\theta_i$.
With $(a, y) = (a_i, y_i)$, $(a', y') = (a_{i+1}, y_{i+1})$ and $d = d_i$, the
margins (11.5) of the pair $S_i$, $S_{i+1}$ read, on an edge with the digit 0,

```math
\begin{aligned}
M_1 &= y + a'\sin d - y'\cos d - \tau(d), & M_2 &= a' - a\cos d + y\sin d - \tau(d), \\
M_3 &= a\sin d + y\cos d - y' - \tau(d), & M_4 &= a - a'\cos d - y'\sin d - \tau(d),
\end{aligned}
```

and on an edge with the digit 1

```math
\begin{aligned}
M_1 &= y + a'\cos d + y'\sin d - \tau(d), & M_2 &= a' + a\sin d + y\cos d - \tau(d), \\
M_3 &= a\cos d - y\sin d - y' - \tau(d), & M_4 &= a + a'\sin d - y'\cos d - \tau(d),
\end{aligned}
```

with $\tau(d) = \frac12(1 + |\sin d| + |\cos d|)$. The axis $j$ *separates* the
pair if $M_j \ge 0$. The point $(a, y)$ lies on the circle of squared radius $q$
if $(a + \frac12)^2 + (|y| + \frac12)^2 = q$, inside its disk if the left side is
at most $q$, and on the core if
$\max(a - \frac12, 0)^2 + \max(|y| - \frac12, 0)^2 = \frac1{144}$. More
generally, a *signed cycle at the level $q$* is any list of seven points
$(a_i, y_i)$ with $|y_i| \le a_i$, inside the disk of squared radius $q$ and
outside the open core disk, and of seven representatives $\theta_i$ within
$\frac7{10}$ of each other; its separations are the conditions $M_j \ge 0$ on
its edges.

A signed cycle records only the seven separations of consecutive pairs. The
later steps move one or two of its squares and keep these seven separations,
the containment and the core, but not the separations of other pairs; the
squares of a moved cycle need not form a packing.

*Lean:
[`Eight.SignedPoint`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L32),
[`Eight.SignedPoint.circle`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L39),
[`Eight.SignedPoint.Contained`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L47),
[`Eight.SignedPoint.AvoidsCore`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L49),
[`Eight.SignedPoint.Outer`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L51),
[`Eight.SignedPoint.Core`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L53),
[`Eight.SignedCycle`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L217),
[`Eight.SignedCycle.atFrame`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L233),
[`Eight.zeroProjection`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L150),
[`Eight.quarterProjection`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L156),
[`Eight.SignedCycle.slack`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L228),
[`Eight.SignedCycle.Feasible`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L231),
[`Eight.SignedCycle.atFrame_slack`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L238),
[`Eight.SignedCycle.atFrame_feasible`](../../SquaresInCircles/Eight/Frames/Signed/Coordinates.lean#L246),
[`Eight.SignedCycle.Necessary`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L47).*

### Definition 11.32 (owners)

The *normal owners* of the seven edges $H \to G$, $G \to A$, $A \to B$,
$B \to T$, $T \to D$, $D \to E$, $E \to H$ are the sets of axes

```math
\lbrace 1, 3\rbrace, \quad \lbrace 1, 2\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 1, 2\rbrace ,
```

and the *terminal owners* are

```math
\lbrace 1, 3\rbrace, \quad \lbrace 1\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 2\rbrace .
```

A cycle satisfies the *owner restriction* to a family of sets if every axis
that separates the pair of an edge belongs to the set of that edge. On every
edge the axes 1 and 2 are the *low* axes and the axes 3 and 4 the *high* axes.
The axis 1 on $G \to A$ and the axis 3 on $B \to T$ are the *hard axes*.

The terminal owners are the axes along which the squares of the optimal
packing are separated, each with margin 0 (Figure 11.18): on the five edges
between squares with the same frame two squares share a side, and two axes
separate; on $G \to A$ a corner of $A$ rests on the side of $G$, and the axis
of $G$ separates; on $E \to H$ a corner of $E$ rests on the side of $H$, and the
axis of $H$ separates. The normal owners add the axes of $A$ and of $E$ on the
last two edges, which the optimal packing does not use. The hard axes hold the
two halves of the ring together: in Figure 11.1, $G$ presses on $A$ along the
axis 1 of the pair $G$, $A$, and $T$ on $B$ along the axis 3 of the pair $B$,
$T$, which is the side of $B$ that $T$ shares.

*Lean:
[`Eight.SignedCycle.normalOwners`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L59),
[`Eight.Candidate.terminalOwners`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L110),
[`Eight.Candidate.OwnerRestriction`](../../SquaresInCircles/Eight/Boundary/Candidate/Geometry.lean#L113),
[`Eight.SignedCycle.HardOwners`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L119),
[`Eight.forwardAxis`](../../SquaresInCircles/Eight/Frames/SeparatingAxis.lean#L194),
[`Eight.forwardMargin`](../../SquaresInCircles/Eight/Frames/SeparatingAxis.lean#L200).*

In the Lean files the axes $1, 2, 3, 4$ are `forwardAxis 0`, …,
`forwardAxis 3`.

![The exterior squares of the optimal packing with the dashed separating line of each of the seven contacts; each edge of the cycle H, G, A, B, T, D, E is labelled with its set of normal owners, the terminal owners in bold: {1, 3} on H to G, {1, 2} with 1 bold on G to A, {1, 3} on A to B, {3, 4} on B to T, {1, 3} on T to D, {3, 4} on D to E, and {1, 2} with 2 bold on E to H; the two hard axes, 1 on G to A and 3 on B to T, are marked by short arrows across their contacts](figures/11-eight/owners.svg)

*Figure 11.18.* The owners in the optimal packing. Each contact line (dashed)
is a side of one square or of both; the label of each edge is its set of normal
owners, with the terminal owners, the axes that separate here, in bold. On the
five edges between squares with the same frame the two squares share a side, so
two axes separate; on $G \to A$ and $E \to H$ a corner rests on a side. The two
arrows mark the hard axes.

## 11.8 The owners of six edges

This section proves the owner restriction on the six edges other than
$G \to A$, by the boosted edges of Lemma 11.26: on the wrong axis, or with the
wrong sign, one edge costs so much that the six other edges, each costing at
least $0.8833$ by Proposition 11.21, push the total over $2\pi$. The edges with
the digit 0 are settled by Lemma 11.27.

### Lemma 11.33 (edges with the digit 1)

Let a boundary cycle at a level $\frac52 \le q \le Q_0$ have a candidate frame,
and let the edge $i$ have the digit 1. If the axis 1 or 2 separates the pair,
then $\tau_{i+1} > 0$ and $S_{i+1}$ lies on $\mathcal O$; if the axis 3 or 4
separates it, then $\tau_i < 0$ and $S_i$ lies on $\mathcal O$.

*Proof.* By Lemma 11.17 we work at the level $Q_0$; here
$\varphi_i = \frac\pi2 + d_i$ with $|d_i| < \frac7{10}$. Suppose that the axis 1
or 2 separates and $\tau_{i+1} \le 0$. In each case the separation gives
$\varphi_i + \ell_i - \ell_{i+1} + \frac9{50}\chi(d_i) > 1$, which
Lemma 11.26 excludes; the axes 3 and 4 with $\tau_i \ge 0$ are the reflected
cases. We give the case of the axis 1 with a source of sign $-1$ in full; the
other three combinations of an axis and a source sign are treated in the same
way, with the weights $\frac45$ and Taylor bounds of the trigonometric terms.

With $\sigma_i = -1$ and $y_{i+1} = -b_{i+1} \le 0$, the separation reads

```math
\tfrac12\left(1 + \cos d + |\sin d|\right) \le -b + a'\cos d - b'\sin d ,
```

with $d = d_i$, $(a, b)$ and $(a', b')$ the two states. As
$a'\cos d - b'\sin d < \frac{283}{200}$, the projection of a centre of a square
in the disk, the source has $b < \frac12$, so its unsigned label is at most
$\frac{111}{100}b$, while the unsigned label of the target is at least
$\frac45 b'$; the cost is
$\frac\pi2 + d - u + u' + \frac9{50}\chi(d)$, where $u$ and $u'$ are the unsigned
labels. Add $\frac{111}{100}$ times the separation. The terms in $b'$ have the
coefficient $\frac45 + \frac{111}{100}\sin d \ge 0$, and $a' < \frac{283}{200}$,
so

```math
\varphi_i + \ell_i - \ell_{i+1} + \tfrac9{50}\chi(d) \ge \tfrac\pi2 + d + \tfrac{93}{200} - \tfrac{18513}{20000}\cos d + \tfrac{129}{200}|\sin d| ,
```

and the right side exceeds 1 for $|d| \le \frac7{10}$: for $d \ge 0$ at once, and
for $d < 0$ by Taylor bounds. With a source of sign $+1$ the weight $\frac45$
gives $\frac\pi2 + d + \frac{31}{100} - \frac{321}{500}\cos d + \frac{49}{100}|\sin d| > 1$.

*The radial curves.* Every edge with the digit 1 is next to an edge with the
digit 0. If the square that the separation designates, the target for the axes
1 and 2 and the source for the axes 3 and 4, lay on the core, the cost of the
two edges together, with their charges, would exceed what the five other
edges, at least $0.8833$ each, leave of $2\pi$; this is proved like the bound
above, for each of the four placements of the two edges in the word. $\square$

*Lean:
[`Eight.GlobalQuarterSign.classify`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L406),
[`Eight.GlobalQuarterSign.of_frame`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L428),
[`Eight.GlobalQuarterSign.target_nonpos_boost`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L262),
[`Eight.GlobalQuarterSign.source_nonneg_boost`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L284),
[`Eight.GlobalQuarterSign.zero_negative_boost`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L60),
[`Eight.GlobalQuarterSign.zero_positive_boost`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L85),
[`Eight.GlobalQuarterSign.secondary_negative_scalar`](../../SquaresInCircles/Eight/Owners/Quarter/SignScalar.lean#L178),
[`Eight.GlobalQuarterSign.secondary_positive_scalar`](../../SquaresInCircles/Eight/Owners/Quarter/SignScalar.lean#L219),
[`Eight.GlobalQuarterSign.rotated_projection_lt`](../../SquaresInCircles/Eight/Owners/Quarter/SignScalar.lean#L47),
[`Eight.GlobalZeroSign.marker_lower`](../../SquaresInCircles/Eight/Owners/Zero/SignSupport.lean#L193),
[`Eight.GlobalZeroSign.marker_small_upper`](../../SquaresInCircles/Eight/Owners/Zero/SignSupport.lean#L200),
[`Eight.GlobalQuarterOuter.frame_classify`](../../SquaresInCircles/Eight/Owners/Quarter/OuterBridge.lean#L580),
[`Eight.GlobalQuarterOuter.frame_high_anchor`](../../SquaresInCircles/Eight/Owners/Quarter/OuterBridge.lean#L589).*

### Proposition 11.34 (the owners of six edges)

Let a boundary cycle at a level $\frac52 \le q \le Q_0$ have a candidate frame,
with $\tau_E \le 0$. Then every axis that separates $H$ from $G$, $A$ from $B$ or
$T$ from $D$ is the axis 1 or 3; every axis that separates $B$ from $T$ or $D$
from $E$ is the axis 3 or 4; and every axis that separates $E$ from $H$ is the
axis 1 or 2. Moreover $H$, $B$ and $D$ lie on $\mathcal O$, with $\tau_H > 0$
and $\tau_B, \tau_D < 0$.

*Proof.* *The edges with the digit 0* are Lemma 11.27. *The edge $D \to E$* is
Lemma 11.33: as $\tau_E \le 0$, the axes 1 and 2 are impossible, and each axis
3 or 4 gives $\tau_D < 0$ with $D$ on $\mathcal O$.

*The edge $B \to T$.* Here the axes 1 and 2 are excluded by a split of the
cycle into two paths. Let $\kappa = \frac{49}{50}$, and let $u_E$ be the
unsigned label of $E$. The *return* $\pi + d_E + d_H + d_G - \kappa b_A - u_E$
of the three edges from $E$ back to $A$ and the *tail*
$\pi + d_A + d_B + d_T + d_D + \kappa b_A + u_E$ of the four edges from $A$ to
$E$ add up to $2\pi$. The pair bounds of the three return edges, the
projections of their separations and the bound of the label give the return
more than $\frac{103}{40}$, whatever the axes of $E \to H$ and $G \to A$, when
$\tau_E \le 0$ and $\tau_A \ge 0$; so the tail is less than
$\frac{710}{113} - \frac{103}{40} = \frac{16761}{4520}$. A low axis on $B \to T$
puts $T$ on $\mathcal O$ with $\tau_T > 0$ (Lemma 11.33) and gives
$\tau_A > 0$, by a charge of the two edges $A \to B \to T$ of the same kind,
and each branch then proves the tail larger than $\frac{16761}{4520}$: the
separations of the four tail edges are added with explicit weights, $\kappa$ on
$B \to T$, a weight between $\frac35$ and $\kappa$ on $T \to D$, and
$\frac{9449}{10000}$, $\frac{797}{1000}$ or $\frac{16}{25}$ on $D \to E$ as $E$ is
core or low, middle or high; $T$ and $D$ are replaced by their circle supports;
the negative frame steps of the tail, which add up to at most $\frac7{10}$ by
the frame concentration, are concentrated into one variable; and the resulting
functions of one angle are positive by the polynomial checks of §11.11. The
branches split by the axis (1 or 2), the signs of the frame steps $d_A$ and
$d_B$, the axis of $A \to B$, the axis of $D \to E$ and the radial curve of $E$.

*The edge $E \to H$.* Let the axis 3 or 4 separate $E$ from $H$. By
Lemma 11.33, $E$ is outer with $\tau_E < 0$, so the axis of $B \to T$ is 3 or 4
by the previous step, and the axis of $D \to E$ is 3 or 4. A high axis on
$E \to H$ also makes every axis of $G \to A$ high: with a low axis on
$G \to A$, the three edges $E \to H \to G \to A$ have a combined charge above
$\frac{11}4$, and the four other edges, each above $0.8833$, bring the total to
$\frac{11}4 + 4 \cdot 0.8833 = 6.2832 > \frac{710}{113}$. So all four edges with
the digit 1 are separated along their axes 3 or 4. This last configuration is
excluded by a whole-cycle bound with markers built from the potential
$\kappa a + \rho\,(L_{\mathsf H}(a, b) - u)$ of an outer state, where
$\kappa = \frac{103}{100}$, $\rho = \frac{11}{10}$, $u$ is the unsigned label and
$L_{\mathsf H}$ the label of the high type, extended to the whole outer curve:
each of the three quarter edges $E \to H$, $G \to A$, $B \to T$ costs at least
$\frac\pi2 + \kappa$, the three zero edges together at least
$3\kappa(1 - 2c_0) - \frac7{1000}$, with $c_0 = \sqrt{Q_0/2} - \frac12$, and
$D \to E$ more than $\frac{957}{1000}$. These add up to more than $2\pi$, since
$\frac\pi2 < 6\kappa(1 - c_0) + \frac{19}{20}$.

*The anchors.* The selected axis of $E \to H$ is low, so by Lemma 11.33 $H$ is
outer with $\tau_H > 0$; the selected axes of $B \to T$ and $D \to E$ are high,
so $B$ and $D$ are outer with negative tangents. $\square$

*Lean:
[`Eight.GlobalOriginalOwners.frame_other_owners`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L285),
[`Eight.GlobalZeroSign.of_frame`](../../SquaresInCircles/Eight/Owners/Zero/SignBridge.lean#L211),
[`Eight.GlobalQuarterSign.frame_DE`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L456),
[`Eight.GlobalQuarterSign.frame_target_nonpos`](../../SquaresInCircles/Eight/Owners/Quarter/SignCycle.lean#L440),
[`Eight.GlobalBT.frame_BT_high`](../../SquaresInCircles/Eight/Owners/BT/Exclusion.lean#L901),
[`Eight.GlobalBT.frame_BT0_false`](../../SquaresInCircles/Eight/Owners/BT/ZeroExclusion.lean#L838),
[`Eight.GlobalBT.frame_BT1_false`](../../SquaresInCircles/Eight/Owners/BT/Exclusion.lean#L889),
[`Eight.GlobalBT.returnCharge`](../../SquaresInCircles/Eight/Owners/BT/CoreDE3Support.lean#L355),
[`Eight.GlobalBT.tailCharge`](../../SquaresInCircles/Eight/Owners/BT/CoreDE3Support.lean#L358),
[`Eight.GlobalBT.return_tail_sum`](../../SquaresInCircles/Eight/Owners/BT/CoreDE3Support.lean#L362),
[`Eight.GlobalBT.frame_return`](../../SquaresInCircles/Eight/Owners/BT/CoreDE3Support.lean#L393),
[`Eight.GlobalEH.frame_EH_low`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L231),
[`Eight.GlobalEH.frame_high_EH_high_BT_false`](../../SquaresInCircles/Eight/Owners/EH/HighRestriction.lean#L605),
[`Eight.GlobalAllHigh.frame_all_high_false`](../../SquaresInCircles/Eight/Owners/All/HighCycle.lean#L504),
[`Eight.GlobalOriginalOwners.atFrame_anchors`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L312),
[`Eight.GlobalOriginalOwners.frame_H_anchor`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L251),
[`Eight.GlobalOriginalOwners.frame_B_anchor`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L264),
[`Eight.GlobalOriginalOwners.frame_D_anchor`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L273).*

![Against the frame step d from -7/10 to 7/10, the two lower bounds of the boosted cost of the edge D to E when the axis 1 separates and the target E has a nonpositive tangent: the curve pi/2 + d + 93/200 - (18513/20000) cos d + (129/200)|sin d| for a source of sign -1 and the curve pi/2 + d + 31/100 - (321/500) cos d + (49/100)|sin d| for a source of sign +1, both above the dashed horizontal line at 1, with the bound 197/200 of Lemma 11.26 dotted below it](figures/11-eight/boost.svg)

*Figure 11.19.* Lemma 11.33 on the edge $D \to E$ with $\tau_E \le 0$: the two
lower bounds of the boosted cost when the axis 1 separates, for a source of sign
$-1$ and of sign $+1$, against the frame step $d$. Both exceed 1, above the bound
$\frac{197}{200}$ of Lemma 11.26 (dotted), so the axis 1 never separates $D$
from $E$.

## 11.9 The high axes of the pair G, A

On the edge $G \to A$ the high axes 3 and 4 remain (Figure 11.20). They are
excluded by moving $T$ until the hard axis 3 separates $B$ from $T$, and then
by stresses, weighted sums of the seven separations, whose weights depend on
which axes separate and on the signs of the frame steps. This is the largest
case analysis of the proof.

![The pair G, A of the optimal packing: the turned square G at the lower left and the axis-parallel square A at the upper right, with a corner of A resting on the right side of G, marked by a dot, and part of the dashed circle below them. At the centre of each square its two retained axes are drawn as arrows: the low axis 1 at G and the low axis 2 at A point to the right, from G towards A, and the high axis 4 at G and the high axis 3 at A point upwards](figures/11-eight/ga-axes.svg)

*Figure 11.20.* The four retained axes of the pair $G$, $A$ in the optimal
packing, each drawn at the centre of the square it belongs to. Only the low
axis 1 separates, with margin 0, as a corner of $A$ (dot) rests on the side of
$G$; the margins of the axes 2, 3 and 4 are about $-0.09$, $-0.25$ and
$-0.38$. A high GA source would separate $G$ from $A$ along the axis 3 or 4.

The two edges at each of the squares $A$, $T$ and $E$ have one axis of the
middle square itself, the *secondary* axis of that edge at the square, and one
axis of the neighbour, the *primary* axis: at $A$ the secondary axes are 3 on
$G \to A$ and 1 on $A \to B$, and the primary axes 4 on $G \to A$ and 3 on
$A \to B$; at $T$ they are 3 on $B \to T$, 1 on $T \to D$ and 4, 3; at $E$, 3 on
$D \to E$, 1 on $E \to H$ and 4, 2. A secondary axis is perpendicular to the
middle square and its margin does not depend on the frame step at the first
order; the margin of a primary axis does, through the coordinate of the middle
square times the frame step. With secondary axes on both edges and equal
weights, the forces of a stress on the middle square cancel.

### Definition 11.35 (high GA sources)

A signed cycle at a level $q$ is a *high GA source* if one axis is chosen on each
edge, separating its pair, in the normal owners on the six edges other than
$G \to A$ and equal to 3 or 4 on $G \to A$, and

1. the gaps between consecutive centre directions, computed from the signed
   points and the frames, are positive and less than $\pi$, and the
   representatives lie within less than $\frac7{10}$ of each other;
2. the positive frame steps add up to less than $\frac7{10}$, and so do the
   negative ones;
3. every point lies on the circle of squared radius $q$ or on the core, and
   $H$, $G$, $B$, $D$ on the circle;
4. $y_H > 0$, $y_G < 0$, $y_B < 0$, $y_D < 0$, $y_E \le 0$, $y_A < \frac12$,
   $A$ lies on the circle if $y_A \le 0$, and $|y| < a$ at $G$, $A$, $B$, $T$, $E$.

A normalized cycle at a level $\frac52 \le q \le Q_0$ in which a high axis
separates $G$ from $A$ gives a high GA source at the same level, its signed
cycle with that axis on $G \to A$ and the selected axes elsewhere: the owners
are those of Proposition 11.34; $H$, $B$, $D$ and, by Lemma 11.33, $G$ lie on
the circle with the stated signs; the bounds on the frame steps follow from the
charge budget of Theorem 11.23, as the charge $g$ lies above its chord; and the
bounds at $A$ and the strict inequalities $|y| < a$ are proved like
Lemma 11.33, the last because a square on its diagonal, read with its other
nearest axis, would change the word into a wrong one (Proposition 11.28).

*Lean:
[`Eight.GlobalGA.SourceDomain`](../../SquaresInCircles/Eight/Owners/GA/EZero.lean#L41),
[`Eight.GlobalGA.sourceDomain`](../../SquaresInCircles/Eight/Owners/GA/EZero.lean#L104),
[`Eight.GlobalGA.highGAOwners`](../../SquaresInCircles/Eight/Owners/GA/Owners.lean#L27),
[`Eight.SignedCycle.Ordered`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L55),
[`Eight.positiveVariation`](../../SquaresInCircles/Eight/Owners/Variation.lean#L23),
[`Eight.negativeVariation`](../../SquaresInCircles/Eight/Owners/Variation.lean#L24),
[`Eight.FramePhysicalTransport.candidate_variations`](../../SquaresInCircles/Eight/Frames/PhysicalTransport.lean#L214),
[`Eight.GlobalGA.Target.frame_target_small`](../../SquaresInCircles/Eight/Owners/GA/Target/SmallTangent.lean#L155),
[`Eight.GlobalZeroSourceOuter.frame_nonpositive_source_outer`](../../SquaresInCircles/Eight/Owners/Zero/SourceOuter.lean#L601),
[`Eight.BinaryDiagonalExclusion.of_frame`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L149),
[`Eight.EDiagonalExclusion.of_frame`](../../SquaresInCircles/Eight/Owners/E/DiagonalExclusion.lean#L90).*

### Lemma 11.36 (moving T)

For every high GA source at a level $q_{\mathrm{low}} \le q \le Q_0$ there is a
high GA source at the same level that differs from it only in the point and the
frame of $T$, in which the axis 3 separates $B$ from $T$.

*Proof.* If the axis 3 separates $B$ from $T$, nothing moves. Otherwise the
axis 4 does, and $T$ is moved, with $B$, $D$ and all the other squares fixed, in
one of three ways, according to the axis of $T \to D$ and the signs of the frame
steps $d_B$, $d_T$ and of $y_T$: it slides along the flat side $a = \frac7{12}$ of
the core, strictly inside the circle, its frame turning to $\theta_B$ or
$\theta_D$; or it moves on the circle of squared radius $q$, its frame between
$\theta_B$ and $\theta_D$, to the minimum of a continuous function over a
compact set of positions and frames on which both separations of $T$ hold; or
it jumps to the point $(\frac7{12}, a_B - 1)$
of the flat side with the frame $\theta_B$, where the axes 3 and 4 of
$B \to T$ both separate. The motion stops when the axis 3 separates, which
happens in particular when the frame of $T$ reaches $\theta_B$, since there the
axes 3 and 4 tie. It can also stop with the frame of $T$ at $\theta_D$ and
$d_B > 0$, or at $\theta_D$ with $d_B < 0$ and $y_T > 0$, or with $T$ on its
diagonal. The diagonal is excluded by Proposition 11.28: read with its other
nearest axis, $T$ would turn the word into a wrong one. The two other stops are
excluded by stresses of the kind used in Proposition 11.37.

The moved square stays in the disk of squared radius $q$ and outside the open
core, on the circle or on the core, and its frame stays between the frames of
its neighbours, so the frames stay within $\frac7{10}$ of each other and the
sums of the positive and of the negative frame steps do not grow. The
separations of the other five edges and all the other signed points are
unchanged. The order of the centre directions is proved anew: each moved gap is
larger than $-\frac{19}{25}$ by the local bounds of the motion, and two squares
separated from each other, outside the core and inside the disk of squared
radius at most $Q_0$, have centre directions more than $\frac{19}{25}$ apart
(Lemma 11.18). $\square$

*Lean:
[`Eight.GlobalGA.TTransport.reduce_secondary`](../../SquaresInCircles/Eight/Owners/GA/Transport/TSecondary.lean#L82),
[`Eight.GlobalGA.TTransport.reduce`](../../SquaresInCircles/Eight/Owners/GA/Transport/T.lean#L396),
[`Eight.GlobalGA.TTransport.reduce_complete`](../../SquaresInCircles/Eight/Owners/GA/Transport/TSecondary.lean#L40),
[`Eight.GlobalGA.TTransport.domain`](../../SquaresInCircles/Eight/Owners/GA/Transport/T.lean#L296),
[`Eight.GlobalGA.TTransport.ordered`](../../SquaresInCircles/Eight/Owners/GA/Transport/T.lean#L131),
[`Eight.TPairOutput`](../../SquaresInCircles/Eight/Owners/Primary/PairClassification.lean#L563),
[`Eight.GlobalGA.NonpositiveT.Source.aligned_has_BT2`](../../SquaresInCircles/Eight/Owners/GA/Nonpositive/TSource.lean#L456),
[`Eight.GlobalGA.PositiveT.Source.original_false`](../../SquaresInCircles/Eight/Owners/GA/Positive/TSource.lean#L263),
[`Eight.SignedCycle.nearest_axis_tie_locations`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L175).*

### Proposition 11.37 (no high GA source with the hard axis on BT)

No high GA source at a level $q_{\mathrm{low}} \le q \le Q_0$ has its pair $B$,
$T$ separated along the axis 3.

*Proof.* *Normal forms.* Before the stresses, the square $A$ and, if it lies on
the core, the square $E$ are put into normal forms by further motions that keep
the level and the separations of the other edges. Call the *total* at $A$ the
sum of the frame steps $d_G$ and $d_A$ over the edges at $A$ whose chosen axis
is primary, and likewise at $E$. If a primary axis has a nonpositive frame step
and the secondary axis of the same edge also separates, the secondary axis is
chosen instead; for an outer $E$ this is always possible. Otherwise $A$ is
moved along the flat side of the core, its frame turning to $\theta_G$ or
$\theta_B$, until the total at $A$ is nonnegative or $A$ lies on the flat side
with a single negative primary step,
$-\frac14 < d_G < 0$ on $G \to A$ or $-\frac{19}{50} < d_A < 0$ on $A \to B$.
A square $E$ on the core is moved along the core in the same way, and an outer
$E$ keeps its point; at the end the total at $E$ is nonnegative or $E$ lies on
the flat side with a single negative primary step. A cycle with a moved $A$ is
used only as a signed cycle.

*The case tree.* The cases are split by the radial curve of $E$, by the sign of
the total at $A$ and which of its primary axes carries a negative step, by
whether $T \to D$ is separated along the axis 3 with $d_T > 0$, by the normal
form of $E$ and, when $E \to H$ is separated along the axis 2, by whether the
axis 1 separates it as well. Each of the fourteen kinds of leaves is closed by
a stress, the same in all of its sub-cases up to the choice of the axis of
$H \to G$.

*The stresses.* A stress takes weights $w_i \ge 0$ on the seven edges, with a
factor $1/\cos d_i$ on an edge whose chosen primary axis has a negative step,
and adds the separations: since each chosen axis separates,

```math
S = \sum_i w_i\left(\tau(d_i) - p_i\right) \le 0 ,
```

where $p_i$ is the projection on the chosen axis of the difference of the
centres. An exact identity writes $S$ as a constant, the *baseline*, plus four
*blocks*, one for each of the squares $H$, $G$, $B$, $D$ on the circle, each a
function of the two frame steps at that square and of its signed point, plus
terms in the totals and in the negative primary steps, plus nonnegative
reserves. Each block is bounded below by the support of the disk in the
direction of the force on its square; the bounds are concave in the positive
and in the negative frame steps, which add up to at most $\frac7{10}$ each, so
the worst case puts all the positive steps in one block and all the negative
steps in one block. What remains are functions of one or two total angles,
with weights that are polynomials in these angles, and their positivity is a
polynomial inequality on an interval, a triangle or a rectangle, checked by the
kernel (§11.11). So $S > 0$, a contradiction.

*A representative leaf.* Let $E$ be outer, the total at $A$ negative, and $T \to D$
not separated along the axis 3 with $d_T > 0$; after the normal forms the
chosen axes are 1 or 3 on $H \to G$, 4 or 3 on $G \to A$, 3 or 1 on $A \to B$,
3 on $B \to T$, 3 or 1 on $T \to D$, 4 or 3 on $D \to E$ and 2 or 1 on $E \to H$,
every chosen primary axis at $A$ or at $T$ has a nonpositive step, and the total
at $E$ is nonnegative. Take the weights

```math
\left(w_{HG}, w_{GA}, w_{AB}, w_{BT}, w_{TD}, w_{DE}, w_{EH}\right) = \left(k,\ l,\ l,\ 2,\ 2,\ 1,\ 1\right), \qquad k = \tfrac{31}{40}, \quad l = \tfrac{31}{20} ,
```

with the factor $1/\cos d$ on $w_{GA}$ or $w_{AB}$ when the primary axis is
chosen there. Their sum, the demand, is $\frac{79}8$. At zero frame steps the
forces on $A$, $T$ and $E$ vanish, and the forces on $H$, $G$, $B$, $D$ are
$(1, k)$, $(l, k)$, $(2, l)$ and $(1, 2)$ in their frames. With
$R = \sqrt{Q_0}$ and the support $V(f, g) = R\sqrt{f^2 + g^2} - \frac12(f + g)$
of a force $(f, g)$ on a square of the disk, the baseline is

```math
\tfrac{79}8 - V(1, k) - V(l, k) - V(2, l) - 3\left(\sqrt{Q_0/2} - \tfrac12\right) > \tfrac{627}{10000} ,
```

the last term coming from the force $(1, 2)$ on $D$, whose support is taken
over the part $|y_D| \le a_D$ of the disk. The block of $G$ is at least $-\frac{576}{10000}$
and that of $B$ at least $-\frac{44}{10000}$ at every corner of the frame
steps, by concavity, and the blocks of $H$ and $D$ are nonnegative; with the
axis 3 on $H \to G$ the block of $H$ is at least $-\frac{22}{10000}$ and that of $G$
nonnegative. The terms in the negative primary steps at $A$ and $T$ are at
least $\frac{71983}{10^6}$ times the steps at $A$ and $\frac{83}{700}$ times the
step at $T$, in absolute value, and the terms in the total at $E$ are at least
$\frac{29}{1000}$ times that total. So
$S > \frac{627 - 576 - 44}{10000} = \frac7{10000} > 0$. $\square$

*Lean:
[`Eight.high_GA_BT2_exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L213),
[`Eight.HighGABT2Exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L123),
[`Eight.HighGABT2.A_normalize`](../../SquaresInCircles/Eight/Owners/GA/High/BT2CoreEFirstNonpositiveT.lean#L139),
[`Eight.GlobalGA.NegativeANormalForm.cycle_reduce`](../../SquaresInCircles/Eight/Owners/GA/Negative/ACycle.lean#L308),
[`Eight.GlobalGA.OuterE.select`](../../SquaresInCircles/Eight/Owners/GA/OuterESelection.lean#L277),
[`Eight.GlobalGA.CoreENormalForm.reduce`](../../SquaresInCircles/Eight/Owners/GA/OuterESelection.lean#L174),
[`Eight.HighGABT2.reduced_nonnegative_A_outer_E_false`](../../SquaresInCircles/Eight/Owners/GA/High/BT2ReducedANegativeOuterE.lean#L761),
[`Eight.HighGABT2.negative_A_outer_E_all_T_false`](../../SquaresInCircles/Eight/Owners/GA/High/BT2ReducedANegativeOuterE.lean#L855),
[`Eight.HighGABT2.core_E_all_T_false`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L42),
[`Eight.GlobalGA.NonnegativeTotals.Source.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Nonnegative/TotalsSource.lean#L62),
[`Eight.GlobalGA.NegativeA.ShortE.original`](../../SquaresInCircles/Eight/Owners/GA/Negative/EHBT3HighScalar.lean#L367),
[`Eight.GlobalGA.NegativeA.LongE.original`](../../SquaresInCircles/Eight/Owners/GA/Negative/ALongESource.lean#L440),
[`Eight.GlobalGA.NegativeDEPositiveTD.Source.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/DETD2Source.lean#L445),
[`Eight.GlobalGA.NegativeEHPositiveTD.Source.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/EHTD2Source.lean#L503),
[`Eight.GlobalGA.NegativeELowA.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/ELowAStress.lean#L1546),
[`Eight.GlobalGA.NegativeELargeA.Source.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/ELargeAStress.lean#L1031),
[`Eight.GlobalGA.JointNegativeAETD2.original`](../../SquaresInCircles/Eight/Owners/GA/Joint/NegativeAEBT3Source.lean#L1280),
[`Eight.GlobalGA.NegativeAPositiveTD.Source.original`](../../SquaresInCircles/Eight/Owners/GA/Negative/ATD2Source.lean#L1230),
[`Eight.GlobalGA.CoreENegativeTotal.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/EHTD2SmallHigh.lean#L553),
[`Eight.GlobalGA.NegativeFlatE.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Negative/Flat/EExclusion.lean#L1020),
[`Eight.GlobalGA.PairedE.Negative.actual_false`](../../SquaresInCircles/Eight/Owners/GA/Paired/ENegativeSource.lean#L178),
[`Eight.GlobalGA.PairedE.Negative.decomposition`](../../SquaresInCircles/Eight/Owners/GA/Paired/ENegativeSource.lean#L50).*

### Corollary 11.38 (the normal owners)

A normalized cycle at a level $q_{\mathrm{low}} \le q \le Q_0$ satisfies the owner
restriction to the normal owners.

*Proof.* Proposition 11.34 gives the six edges other than $G \to A$. If a high
axis separated $G$ from $A$, Definition 11.35 would give a high GA source at the
level $q$, Lemma 11.36 one with the axis 3 on $B \to T$, and Proposition 11.37
excludes it. $\square$

*Lean:
[`Eight.original_GA_low_of_BT2_exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L138),
[`Eight.original_normal_owners_of_BT2_exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L159),
[`Eight.GlobalOriginalOwners.normal_owners_of_GA_low`](../../SquaresInCircles/Eight/Owners/GA/EZero.lean#L164),
[`Eight.high_GA_source_false_of_BT2_exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L129).*

## 11.10 The hard axes and the stationary frames

With the normal owners known, two facts remain: the hard axes separate, and
then the frames are those of Figure 11.1. Both rest on the five-corner problem.
Seven squares whose frames have the pattern of Figure 11.1 and which are
separated along the contacts of Figure 11.1 have five corners with the spans of
Theorem 11.1, so their disk has radius at least $\sqrt{q_*}$
(Lemma 11.39). A configuration that departs from the pattern is moved, at the
same squared radius $q$, towards the pattern, and every departure costs one of
the five squares $A$, $B$, $D$, $E$, $H$ room against the circle; at the end the
pattern holds and the five squares touch the circle of squared radius
$q_* \ge q$, so no room was lost, and there was no departure.

### Lemma 11.39 (the five corners of a ring)

Let $0 \le t \le \frac\pi4$, let $K_H, K_G, K_A, K_B, K_T, K_D, K_E$ be unit squares
with centres $c_H, \dots, c_E$, of which $K_H$ and $K_G$ are turned by $t$ and the
others are axis-parallel, and let the seven *gaps*

```math
\begin{gathered}
g_{HG} = \langle e_t, c_G - c_H\rangle - 1, \quad g_{GA} = \langle e_t, c_A - c_G\rangle - w, \quad g_{AB} = (c_B - c_A)_y - 1, \quad g_{BT} = (c_B - c_T)_x - 1, \\
g_{TD} = (c_T - c_D)_x - 1, \quad g_{DE} = (c_D - c_E)_y - 1, \quad g_{EH} = \langle f_t, c_E - c_H\rangle - w ,
\end{gathered}
```

with $w = \frac12(1 + \cos t + \sin t)$, be nonnegative. Put

```math
P_1 = c_A + \left(\tfrac12, -\tfrac12\right), \quad P_2 = c_B + \left(\tfrac12, \tfrac12\right), \quad P_3 = c_D + \left(-\tfrac12, \tfrac12\right), \quad P_4 = c_E + \left(-\tfrac12, -\tfrac12\right), \quad P_5 = c_H - \tfrac12\left(e_t + f_t\right) .
```

1. The configuration $(t, P_1, \dots, P_5)$ spans, and the excesses of its five
   spans over their bounds are $g_{AB}$, $g_{BT} + g_{TD}$, $g_{DE}$, $g_{EH}$
   and $g_{HG} + g_{GA}$.
2. If the seven squares lie in the closed disk of radius $R$, then
   $R \ge \sqrt{q_*}$.
3. If they lie in the closed disk of radius $\sqrt{q_*}$, then $t = t_*$,
   $K_A$, $K_B$, $K_D$, $K_E$, $K_H$ are the squares $A$, $B$, $D$, $E$, $H$ of the
   models, all seven gaps vanish, and $c_T = (x_2 - \frac32, \zeta)$ and
   $c_G = p_H + e + \eta f$ for some $\zeta$ and $\eta$.

*Proof.* (1) The excess of the first span is
$(P_2 - P_1)_y - 2 = (c_B - c_A)_y - 1 = g_{AB}$, and in the same way the
second is $(c_B - c_D)_x - 2 = g_{BT} + g_{TD}$ and the third $g_{DE}$. For the
fourth, $\langle f_t, P_4 - P_5\rangle - 1 - \sin t
= \langle f_t, c_E - c_H\rangle + \frac12(\sin t - \cos t) + \frac12 - 1 - \sin t = g_{EH}$,
and the fifth is
$\langle e_t, P_1 - P_5\rangle - 2 - \cos t = \langle e_t, c_A - c_H\rangle - 1 - w = g_{HG} + g_{GA}$.
(2) With these frames each $P_i$ is a vertex of its square, so it lies in the
disk: the configuration spans and fits in $R$, and $R \ge R_8 = \sqrt{q_*}$ by the
definition of $R_8$ and Proposition 11.5. (3) The configuration then fits in
$R_8$, so by Proposition 11.5 (2) it is the stationary one: $t = t_*$, the five
corners are those of the stationary solution, and so the centres of the five
squares are those of the models. The five excesses vanish, and as they are
sums of nonnegative gaps, all seven gaps vanish; $g_{BT} = 0$ and $g_{HG} = 0$
put $c_T$ and $c_G$ on the two slider lines. $\square$

*Lean:
[`Eight.OriginalFiveCorner.PhysicalFrames`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L324),
[`Eight.OriginalFiveCorner.gap`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L333),
[`Eight.OriginalFiveCorner.chain`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L343),
[`Eight.OriginalFiveCorner.residual_identity`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L399),
[`Eight.OriginalFiveCorner.corner_is_original_vertex`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L388),
[`Eight.OriginalFiveCorner.chain_spans`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L409),
[`Eight.OriginalFiveCorner.chain_fits`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L419),
[`Eight.OriginalFiveCorner.radius_lower_bound`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L433),
[`Eight.OriginalFiveCorner.original_anchor_centers`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L443),
[`Eight.OriginalFiveCorner.all_original_contacts_tight`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L454),
[`Eight.OriginalFiveCorner.original_sliders`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L493),
[`Eight.AlignedEndpoint.sharp_rigidity`](../../SquaresInCircles/Eight/Owners/Hard/Rigidity.lean#L185).*

![The seven exterior squares of the optimal packing, with their frames, moved apart so that neighbours no longer touch; each gap of Lemma 11.39 is drawn as a short red double arrow between neighbours: g_AB between A and B, g_BT and g_TD on either side of T, g_DE between D and E, g_HG between H and G, g_GA from G to the corner of A, and g_EH from H to the corner of E. The five corners P1 to P5 of A, B, D, E and H are marked by dots, and the dashed circle about o of radius about 2.22 holds the seven squares, with the corner P2 on it](figures/11-eight/ring.svg)

*Figure 11.21.* Lemma 11.39: seven squares with the frames of Figure 11.1,
separated from their neighbours by the gaps $g$, here between $0.04$ and
$0.14$. The five corners $P_1, \dots, P_5$ (dots) span as in Theorem 11.1, each
span exceeding its bound by the sum of the gaps along it (compare
Figure 11.4). The least disk about $o$ that holds the squares (dashed) has
radius about $2.22 > \sqrt{q_*}$; by part (3) of the lemma no disk of radius
$\sqrt{q_*}$ holds them, as some gap is positive.

### Definition 11.40 (hard cycles and anchor losses)

A *hard cycle* at the level $q$ is a signed cycle at the level $q$ with
$y_H \ge 0$, $y_A \ge 0$, $y_B \le 0$, $y_D \le 0$ and $y_E \le 0$, with one axis
chosen on each edge in its normal owners and separating its pair, with the hard
axes 1 on $G \to A$ and 3 on $B \to T$ separating, with $y_G < 0$ if the chosen
axis of $H \to G$ is 3 and $y_T > 0$ if that of $T \to D$ is 1, and with
$a_E \le \frac7{12}$ or $|y_H|, |y_D| \le a_E$. Its anchors need not lie on the
circle, and its centre directions need not be in order.

For two signed cycles $C$ and $C'$, write $c(P) = (a_P + \frac12)^2 + (|y_P| + \frac12)^2$
for the squared distance from $o$ of the farthest vertex of the square $P$ of
$C$, and $c'(P)$ for that of $C'$. Then $C'$ has *no larger anchors* than $C$ if
$c'(P) \le c(P)$ for the five *anchors* $P = H, A, B, D, E$, and a *strict loss*
if moreover one of these inequalities is strict. If the anchors of $C$ lie in
the disk of squared radius $q$ and those of $C'$ on its circle, then $C'$ has no
strict loss against $C$: $c'(P) < c(P) \le q = c'(P)$ is impossible.

*Lean:
[`Eight.SignedCycle.HardInput`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L106),
[`Eight.SignedCycle.NormalAnchors`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L68),
[`Eight.SignedCycle.ZeroSignImplications`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L76),
[`Eight.SignedCycle.Witnesses`](../../SquaresInCircles/Eight/Owners/NecessaryCycle.lean#L63),
[`Eight.anchorVertices`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L23),
[`Eight.AnchorNonincrease`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L25),
[`Eight.StrictAnchorLoss`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L28),
[`Eight.AllAnchorsOn`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L34),
[`Eight.no_strict_loss_to_on_circle`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L67),
[`Eight.anchors_tight_before`](../../SquaresInCircles/Eight/Owners/LossLedger.lean#L75).*

### Proposition 11.41 (sharp hard cycles)

Let a hard cycle lie at a level $q_{\mathrm{low}} \le q \le q_*$. Then $q = q_*$;
$\theta_A = \theta_B = \theta_T = \theta_D = \theta_E$ and $\theta_G = \theta_H$,
with $\theta_H - \theta_D = t_*$; $y_A - y_B = 1$; the five anchors lie on the
circle of squared radius $q_*$; and every terminal owner of every edge
separates its pair with margin 0.

*Proof.* *The canonical case.* Suppose that the frames have the pattern
$\theta_G = \theta_H$, $\theta_A = \theta_B = \theta_T = \theta_D = \theta_E$ and
$\theta_D \le \theta_H$, and that the axis 2 separates $E$ from $H$. Then
$t = \theta_H - \theta_D$ lies in $[0, \frac7{10}] \subset [0, \frac\pi4]$, and
turning the plane by $-\theta_D$ gives seven squares as in Lemma 11.39. On each
edge between squares with the same frame the two normal owners have the same
normal, which is the normal of the corresponding gap of Lemma 11.39, with the
threshold 1; on $G \to A$ the hard axis 1 and on $E \to H$ the axis 2 have the
normals $e_t$ and $-f_t$, with the threshold $w$; and on $B \to T$ the hard axis
3 has the normal $(-1, 0)$. So the chosen separations make the seven gaps
nonnegative, and Lemma 11.39 gives $q = q_*$, $t = t_*$, the anchors on the
circle and all gaps 0, which is the claim.

*The general case.* A sequence of moves of the signed cycle at the same level
$q$, each giving a hard cycle with no larger anchors, leads to the canonical
case; each move that is needed because the source departs from the pattern
gives a strict loss at one of the anchors. At the end the anchors lie on the
circle of squared radius $q_* \ge q$, by the canonical case, so no move had a
strict loss, and the cycle had the pattern from the start. The moves come in
this order.

1. *The middle.* $A$ and $B$ are given a common frame and the gap $y_A - y_B = 1$,
   and $\theta_T \le \theta_A \le \theta_G$; a defect gives $A$ or $B$ a strict
   loss.
2. *The outer order* $\theta_A \le \theta_H$ and $\theta_D \le \theta_B$. A crossed
   order is excluded by a clamp of $G$, $A$, $B$ to a common frame, which gives
   the middle anchors a strict loss; the side with the larger tangent,
   $y_A \ge \frac12$ or $-y_B \ge \frac12$, is ordered first, and its bound puts
   the other tangent in $[\frac{67}{200}, \frac12]$, where the crossed case of
   the other side is excluded in the same way.
3. *The signs* $y_G < 0$ and $y_T > 0$: a wrong sign on the larger of the two
   middle tangents is excluded by an envelope of the opposite pair, and a
   small wrong sign by the budget of the edges with mixed frames.
4. $\theta_G \le \theta_H$ and $\theta_D \le \theta_T$: otherwise $H$ is aligned
   with $G$, or $D$ with $T$, with a strict loss at $A$ or $B$; and the chosen
   axes of $H \to G$ and $T \to D$ become 1 and 3.
5. $\theta_E = \theta_D$: $E$ moves on its own circle, its tangent decreasing,
   and turns to the frame of $D$.
6. $\theta_G = \theta_H$ and $\theta_B = \theta_T = \theta_D$: the remaining
   reductions end in a weighted dual with the weights of the stationary chain at
   the tilt of the cycle, which bounds $q$ below by $q_*$ plus nonnegative losses
   of the centres, of the circles and of the frames; at $q \le q_*$ all of them
   vanish. One endpoint, at which $G \to A$ and $D \to E$ would be tight
   together, is excluded by a five-anchor stress whose weights are polynomials in
   the tilt, checked by the kernel (§11.11).

In the end the pattern holds, and the canonical case applies. $\square$

*Lean:
[`Eight.SignedCycle.HardInput.hard_sharp`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L312),
[`Eight.SignedCycle.HardInput.hard_middle`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L280),
[`Eight.SignedCycle.HardInput.canonicalize_middle`](../../SquaresInCircles/Eight/Owners/Hard/Rigidity.lean#L41),
[`Eight.SignedCycle.HardInput.canonical_hard_sharp`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L260),
[`Eight.SignedCycle.HardInput.canonical_hard_outer_order`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L228),
[`Eight.SignedCycle.HardInput.common_frame_entry_impossible`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L153),
[`Eight.SignedCycle.HardInput.ordered_hard_sharp`](../../SquaresInCircles/Eight/Owners/Ordered/HardSharp.lean#L620),
[`Eight.SignedCycle.HardInput.ordered_normal_sharp`](../../SquaresInCircles/Eight/Owners/Ordered/HardSharp.lean#L524),
[`Eight.SignedCycle.HardInput.nonpositive_owner_sharp`](../../SquaresInCircles/Eight/Owners/Nonpositive/OuterSharp.lean#L125),
[`Eight.SignedCycle.HardInput.nonpositive_sharp`](../../SquaresInCircles/Eight/Owners/Nonpositive/HardSharp.lean#L182),
[`Eight.StationaryTerminal.stationary_rigidity`](../../SquaresInCircles/Eight/Owners/Stationary/CanonicalRigidity.lean#L414),
[`Eight.SignedCycle.HardInput.canonical_tilt`](../../SquaresInCircles/Eight/Owners/Canonical/NegativeCycle.lean#L112),
[`Eight.SignedCycle.HardInput.canonical_lower_bound`](../../SquaresInCircles/Eight/Owners/Canonical/NegativeCycle.lean#L121),
[`Eight.SignedCycle.HardInput.canonical_sharp`](../../SquaresInCircles/Eight/Owners/Canonical/NegativeCycle.lean#L137),
[`Eight.SignedCycle.HardInput.all_anchors_on`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L350).*

### Proposition 11.42 (the hard axes)

Let a normalized boundary cycle at a level $q_{\mathrm{low}} \le q \le q_*$ satisfy
the owner restriction to the normal owners. Then the hard axes separate: the
axis 1 separates $G$ from $A$, and the axis 3 separates $B$ from $T$.

*Proof.* *Moving $G$ and $T$.* If the axis 1 does not separate $G$ from $A$, the
normal owner 2 does, and $G$ is moved, with all the other squares fixed, by the
mirror image of the motion of $T$ in Lemma 11.36: along the flat side of the
core, on the circle of squared radius $q$ with its frame between $\theta_H$ and
$\theta_A$, or to the point $(\frac7{12}, 1 - a_A)$ of the flat side with the
frame $\theta_A$. The same is done with $T$ if the axis 3 does not separate $B$
from $T$. The result $J$ is a signed cycle at the level $q$ with the same anchors,
the same separations on the other edges and its centre directions in order; its
pair $G$, $A$ is in one of three *terminal states*: the axis 1 separates
($G_0$); the axis 2 separates, $H \to G$ along the axis 3, and $d_G > 0$
($G_+$); or the axis 2 separates, $\theta_G = \theta_H$, $d_G < 0$ and $y_G < 0$
($G_-$). The pair $B$, $T$ is likewise in the state $T_0$ (axis 3), $T_+$ (axis 4,
$T \to D$ along the axis 1, $d_B > 0$) or $T_-$ (axis 4, $\theta_T = \theta_D$,
$d_B < 0$, $y_T > 0$). The motion could also stop with $G$ or $T$ on its
diagonal; read with its other nearest axis, that square would turn the word
$0101011$ into one of the two wrong binary words, which Proposition 11.28
excludes.

*The terminal matrix.* In the state $(G_0, T_0)$ the hard axes separate in $J$.
The other eight states are impossible:

| | $T_0$ | $T_+$ | $T_-$ |
| --- | --- | --- | --- |
| $G_0$ | hard axes | stresses, by reflection | strict loss at $D$ |
| $G_+$ | stresses | stresses | stresses |
| $G_-$ | strict loss at $H$ | stresses, by reflection | strict losses at $H$ and $D$ |

A state $G_+$ is excluded by stresses, after the square $E$ is put into a
normal form, with weights that are polynomials in the positive frame step and
positivity checked by the kernel; a state $T_+$ is the state $G_+$ of the
reflected cycle. In a negative state the square $H$, or $D$, is turned together
with $G$, or $T$, towards the frame of $A$, or $B$, which gives a hard cycle with a
strict loss at $H$, or $D$; by Proposition 11.41 the anchors of that hard cycle
lie on the circle of squared radius $q_*$, which a strict loss forbids.

*Back to the original cycle.* So $J$ is a hard cycle, and by Proposition 11.41
its frames satisfy $\theta_A \le \theta_G = \theta_H$ and
$\theta_D = \theta_T \le \theta_B$, with its chosen axes on $H \to G$ and
$T \to D$ tight. The anchors and their frames did not move, so
$\theta_A \le \theta_H$ and $\theta_D \le \theta_B$ hold in the original cycle as
well. If the original cycle lacked the axis 1 on $G \to A$, the motion of $G$
would have produced it only with $\theta_A - \theta_H > 0$ or with a positive
margin on $H \to G$, and neither holds; so the original cycle had the axis 1,
and in the same way the axis 3 on $B \to T$. $\square$

*A representative case: the state $(G_-, T_0)$, with $E \to H$ separated along
the axis 1.* Here $\theta_G = \theta_H$, $t = \theta_H - \theta_A > 0$,
$y_G \le 0$, the axis 2 separates $G$ from $A$ but the axis 1 does not, and the
axis 3 separates $B$ from $T$. A stress gives the span
$\theta_H - \theta_D < \frac{11}{50}$, and the separations give the cuts
$a_G \ge \frac7{12}$, $\frac1{10} < -y_G < \frac{39}{250}$,
$\frac{211}{250} < y_H$, $a_H < 1$ and $t < \frac9{100}$. First $G$ is moved to
the flat side of the core where the axis 2 of $G \to A$ is tight, and $H$ along
its own circle until the axis 1 of $H \to G$ is tight; the separation of
$E \to H$ along the axis 1 is kept. Then $H$ and $G$ are turned together, with
the common frame $\theta_A + x$, $H$ on its circle and $G$ on the curve where the
axis 2 of $G \to A$ stays tight. Let $L(x)$ be the margin of $E \to H$ along the
axis 1, and $S$ the compact set of the $x \in [l, t]$, $l = \max(0, \theta_E - \theta_A)$,
with $L(x) \ge L(t) + \frac3{100}(t - x)$. At its least point $m$ the axis 1
separates $G$ from $A$: otherwise $L' < -\frac3{50}$ there, and $S$ would contain
smaller points. So $m < t$ and $L(m) > 0$. Now move $H$ inward to
$(a_H - \eta, y_H)$ with $\eta = \min(\frac12(a_H - y_H), \frac12(a_H - \frac7{12}), \frac12 L(m))$:
the separations of $H \to G$ and $E \to H$ still hold, $H$ stays outside the
core, and $c(H)$ decreases strictly. The result is a hard cycle with a strict
loss at $H$, against Proposition 11.41.

*Lean:
[`Eight.SignedCycle.NormalizedBoundaryInput.original_hard_owners`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L43),
[`Eight.SignedCycle.BoundaryInput.g_source_output`](../../SquaresInCircles/Eight/Boundary/SourcePrimaryRecovery.lean#L601),
[`Eight.preprocess_G_pair_with_source`](../../SquaresInCircles/Eight/Boundary/SourcePrimaryRecovery.lean#L389),
[`Eight.GPairOutput`](../../SquaresInCircles/Eight/Owners/Primary/PairClassification.lean#L196),
[`Eight.GPairSourceOutput`](../../SquaresInCircles/Eight/Boundary/SourcePrimaryRecovery.lean#L265),
[`Eight.SignedCycle.NormalizedBoundaryInput.pairDescendant`](../../SquaresInCircles/Eight/Boundary/SourceRecovery.lean#L136),
[`Eight.PairTerminalMatrix.GState`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L40),
[`Eight.PairTerminalMatrix.TState`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L45),
[`Eight.PairTerminalMatrix.hard`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L146),
[`Eight.PairTerminalMatrix.positive_G_false`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L87),
[`Eight.PairTerminalMatrix.positive_T_false`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L132),
[`Eight.PositiveGAAllTExclusion.original_boundary_false`](../../SquaresInCircles/Eight/Owners/Positive/GAAllTExclusion.lean#L124),
[`Eight.DirectNegativeT.negative_t_impossible`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L403),
[`Eight.AlignedNegative.negative_g_impossible`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L373),
[`Eight.AlignedNegative.both_negative_impossible`](../../SquaresInCircles/Eight/Owners/Negative/TerminalSharp.lean#L218),
[`Eight.AlignedNegative.aligned_negative_span`](../../SquaresInCircles/Eight/Owners/TD2Span.lean#L174),
[`Eight.AlignedNegative.NegativeGEntry.false_at_sharp`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L362),
[`Eight.SignedCycle.BoundaryInput.G_negative_not_diagonal`](../../SquaresInCircles/Eight/Owners/OriginalOwners.lean#L201),
[`Eight.PairTerminalDescendant.hard`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L275),
[`Eight.PairTerminalDescendant.source_recovery`](../../SquaresInCircles/Eight/Frames/Pair/TerminalRecovery.lean#L292),
[`Eight.SignedCycle.NormalizedBoundaryInput.pair_source_recovery`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L430),
[`Eight.SignedCycle.BoundaryInput.original_hard_of_pair_contacts`](../../SquaresInCircles/Eight/Boundary/SourcePrimaryRecovery.lean#L761).*

### Theorem 11.43 (the stationary frames)

Let eight unit squares form a packing in a closed disk of squared radius
$q \le q_*$ about $o$. View it in the disk of squared radius $q_*$, take its
boundary cycle at the level $q_*$ with separating axes chosen on the packing,
and normalize it (Lemma 11.30). Then the seven exterior squares of the packing
have the frames of the models of Theorem 11.1, up to quarter turns: $A$, $B$,
$T$, $D$, $E$ axis-parallel and $H$, $G$ turned by $t_*$. Each chosen axis has
the normal of the corresponding contact of the models:

```math
e \ \text{on}\ H \to G \ \text{and}\ G \to A, \qquad (0, 1)\ \text{on}\ A \to B, \qquad (-1, 0)\ \text{on}\ B \to T\ \text{and}\ T \to D, \qquad (0, -1)\ \text{on}\ D \to E, \qquad -f\ \text{on}\ E \to H .
```

*Proof.* The boundary cycle lies at the level $q_*$, between $q_{\mathrm{low}}$
and $Q_0$. By Corollary 11.38 it satisfies the owner restriction to the normal
owners, and by Proposition 11.42 the hard axes separate. With the normal
owners, Lemma 11.33 puts $H$, $A$, $B$, $D$ on the circle with $y_H, y_A > 0$ and
$y_B, y_D < 0$, so its signed cycle is a hard cycle, and by
Proposition 11.41 its frames have the pattern of Figure 11.1 with
$\theta_H - \theta_D = t_*$; as $\theta_A = 0$, the canonical frames are those of
the models. The two squares of an edge between squares with the same frame have
the same normal on both normal owners. On $G \to A$ the normal owner 2, an axis
of $A$, does not separate in the stationary configuration, as $a_G > \frac{447}{800}$
leaves a strict reserve; so the chosen axis is 1, with the normal $e$. On $E \to H$
the normal owner 1, an axis of $E$, does not separate either, so the chosen
axis is 2, with the normal $-f$. The boundary cycle has the frames and the
chosen axes of the original squares (Proposition 11.15 and Lemma 11.17), which
proves the theorem. $\square$

*Lean:
[`Eight.SharpSourceEntry`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L107),
[`Eight.sharp_source_entry`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L238),
[`Eight.sharp_source_entry_of_BT2_exclusion`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L170),
[`Eight.source_witnesses_of_normal_owners`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L75),
[`Eight.boundary_source_rigidity_of_normal_input`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L55),
[`Eight.boundary_source_rigidity_of_hard`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L471),
[`Eight.boundary_source_rigidity_of_canonical`](../../SquaresInCircles/Eight/Boundary/UniversalSourceRecovery.lean#L48),
[`Eight.NormalizationBridge.normalizedInput`](../../SquaresInCircles/Eight/Owners/NormalizationBridge.lean#L44),
[`Eight.NormalizationBridge.recoveredFrame`](../../SquaresInCircles/Eight/Owners/NormalizationBridge.lean#L25),
[`Eight.GlobalOuterAnchor.normal_anchors`](../../SquaresInCircles/Eight/Owners/Outer/AnchorBridge.lean#L478),
[`Eight.StationaryFrames`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L568),
[`Eight.stationaryNormal`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L572),
[`Eight.stationary_ga1_not_feasible`](../../SquaresInCircles/Eight/Owners/Stationary/SourceOwners.lean#L89),
[`Eight.stationary_eh0_not_feasible`](../../SquaresInCircles/Eight/Owners/Stationary/SourceOwners.lean#L156),
[`Eight.terminal_owners_after_source_equality`](../../SquaresInCircles/Eight/Owners/Stationary/SourceOwners.lean#L207).*

## 11.11 The exact polynomial checks

Many branches of §11.8 to §11.10, and four of §11.6, end in an inequality
between explicit functions of one angle, or of two, on an interval, a triangle,
a rectangle or a trapezoid. Sines and cosines are replaced there by Taylor
polynomials with signed remainders, square roots by rational majorants or by
squaring, and denominators are cleared, so that the inequality says that a
polynomial $p$ with rational coefficients exceeds a rational reserve $\rho$ on
the domain. Such a positivity is proved by a *check*. An affine map takes the
interval to $[-1, 1]$, and a polynomial map takes the triangle, the rectangle or
the trapezoid to the square $[-1, 1]^2$; the polynomial is expanded in the
Chebyshev polynomials $T_j$, or in the products $T_j(x)T_k(y)$; and the constant
coefficient minus the sum of the absolute values of all the other coefficients
is compared with $\rho$. Since $|T_j| \le 1$ on $[-1, 1]$, the inequality
$\rho < c_0 - \sum_{j \ge 1}|c_j|$ for the coefficients $c_j$ gives $p > \rho$ on
the whole domain, with no subdivision and no sampling. When the degree is low
and the margin is not too small, no check is needed: on an interval $[a, b]$
the polynomial minus the reserve is a combination with nonnegative coefficients
of the Bernstein products $(x - a)^i (b - x)^{n - i}$, possibly with one added
square, and an ordinary linear argument proves the bound.

The identity between the polynomial and its expansion, the coefficients and
the final comparison are computations with integers, carried out by the Lean
kernel itself (`decide +kernel`); the polynomial is represented by a list of
integers with a common denominator, built along the formula that defines it,
and a lemma for each arithmetic operation shows that the list represents the
formula. No floating-point number and no external program enters. The checks
are used in these places:

* the endpoint functions of the stresses of Lemma 11.36 and
  Proposition 11.37, in one variable and, on triangles and rectangles of two
  frame steps, in two;
* the tail of the edge $B \to T$ and the configuration with all high axes in
  Proposition 11.34;
* the stresses of the positive states and the anchor stresses of
  Propositions 11.41 and 11.42;
* four branches of the wrong words in Proposition 11.28.

Besides these, the kernel evaluates interval expressions with rational
endpoints for the stationary solution (Proposition 11.4 and
[Appendix J](appendix-j.md)) and for the box of Proposition 11.7, and it
enumerates the finite cases of Lemma 11.22 and of the quarter words. No check
enters Proposition 11.21 or Lemmas 11.26, 11.27 and 11.33.

[Appendix L](appendix-l.md) describes the bound by Chebyshev coefficients,
the integer representation that the kernel computes on, the two-variable checks
and their restrictions to the sides of a triangle, the Taylor polynomials,
rational majorants of roots and Taylor models, and a worked example; it also
counts the checks of the proof.

*Lean:
[`Eight.WholeIntervalPolynomial.positive_on_interval`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L101),
[`Eight.WholeIntervalPolynomial.interval_bounds`](../../SquaresInCircles/Eight/Arithmetic/WholeIntervalPolynomial.lean#L75),
[`Eight.WholeIntervalPolynomial.Certificate.Scaled`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L308),
[`Eight.WholeIntervalPolynomial.Certificate.lowerOn_eq_of_rep`](../../SquaresInCircles/Eight/Arithmetic/PolynomialCertificates.lean#L686),
[`Eight.TensorWholeIntervalPolynomial.positive_on_square`](../../SquaresInCircles/Eight/Arithmetic/TensorWholeIntervalPolynomial.lean#L119),
[`Eight.TwoVariablePolynomial.square_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L166),
[`Eight.TwoVariablePolynomial.rectangle_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L186),
[`Eight.TwoVariablePolynomial.triangle_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L201),
[`Eight.TwoVariablePolynomial.trapezoid_bounds`](../../SquaresInCircles/Eight/Arithmetic/TwoVariablePolynomial.lean#L230),
[`Eight.BivariateCertificate.XM.lower_certificate`](../../SquaresInCircles/Eight/Arithmetic/BivariateCertificates.lean#L2624),
[`Eight.PackedModels.check_lt`](../../SquaresInCircles/Eight/Arithmetic/PackedModels.lean#L3317),
[`Eight.HighOrderTaylor.S11_le_sin`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L30),
[`Eight.HighOrderTaylor.C14_le_cos`](../../SquaresInCircles/Eight/Arithmetic/HighOrderTaylor.lean#L60),
[`Eight.Stationary.FixedEval.bounded_sound`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L1512).*

## 11.12 The lower bound

The lower bound now follows from one identity, applied to the original squares.
By Theorem 11.43 the seven exterior squares of a packing of squared radius
$q \le q_*$ have the frames of the models and are separated along the normals
of the seven contacts. The weights $\mu_P$ of the five corners and $\lambda_e$ of
the seven contacts of the stationary chain
([Lemma J.6](appendix-j.md#lemma-j6-the-weights-of-the-chain)) balance at
every square, and the weighted sum of the five corner constraints and the seven
separations is then exactly $q_*$ plus a sum of squares. Nothing is assumed
about how close the squares are to the optimal ones.

### Theorem 11.44 (the dual at the original centres)

Let $p_H, p_G, p_A, p_B, p_T, p_D, p_E$ be seven points of the plane, and let the
gaps $g$ of Lemma 11.39 be formed with these points as centres and $t = t_*$.
With the corner offsets $o_A = (\frac12, -\frac12)$, $o_B = (\frac12, \frac12)$,
$o_D = (-\frac12, \frac12)$, $o_E = (-\frac12, -\frac12)$,
$o_H = -\frac12(e + f)$ and the centres $p^0_P$ of the squares $A$, $B$, $D$, $E$,
$H$ of the models,

```math
\sum_{P = A, B, D, E, H}\mu_P\,|p_P + o_P|^2 - \sum_e \lambda_e\,g_e = q_* + \sum_{P = A, B, D, E, H}\mu_P\,|p_P - p^0_P|^2 . \tag{11.9}
```

So if the five points $p_P + o_P$ lie in the closed disk of squared radius $q$ and
the seven gaps are nonnegative, then

```math
q_* + \sum_{P = A, B, D, E, H}\mu_P\,|p_P - p^0_P|^2 \le q ;
```

and if moreover $q \le q_*$, then $q = q_*$, $p_P = p^0_P$ for
$P = A, B, D, E, H$, every gap vanishes, and $p_T = (x_2 - \frac32, \zeta)$ and
$p_G = p_H + e + \eta f$ for some $\zeta$ and $\eta$.

The proof is given in [Appendix M](appendix-m.md). Both sides of (11.9) are
quadratic in the seven points; the coefficients of the points $p_T$ and $p_G$
vanish, as the two contacts at each of the sliders have equal weights and
opposite normals, and completing the square at the five other points leaves
$q_*$, by the balance of the forces of Lemma J.6.

*Lean:
[`Eight.OriginalDual.Positions`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L641),
[`Eight.OriginalDual.gap`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L649),
[`Eight.OriginalDual.exact_identity`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L691),
[`Eight.OriginalDual.value_le`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L724),
[`Eight.OriginalDual.original_centers_rigid`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L738),
[`Eight.OriginalDual.slider_coordinates`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L784),
[`Eight.GeometricModel.original_dual_quantitative`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L160),
[`Eight.GeometricModel.original_dual_radius_lower`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L172),
[`Eight.GeometricModel.original_radius_and_centers`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L188),
[`Eight.GeometricModel.sharp_original_radius_and_centers`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L207).*

![The stationary weights of the optimal packing: the seven contacts drawn as thin lines between the centres of touching squares, labelled with their weights lambda, between 0.48 and 0.80, and the five corner forces drawn as thick arrows that start at the corners P1 to P5 of A, B, D, E and H on the circle and point outward along the radii, labelled with the weights mu: 0.210 for A, 0.221 for B, 0.273 for D, 0.025 for E and 0.271 for H. T and G carry no corner force](figures/11-eight/stress.svg)

*Figure 11.22.* The stationary weights: the contact weights $\lambda$ on the
seven contacts (thin) and the corner forces $2\mu_P P_P$ along the radii to the
corners on the circle (thick). At each of the seven squares the forces balance;
at $T$ and $G$ the two contact forces cancel. With these weights the sum of the
corner constraints and the separations is exactly $q_*$ plus squares,
identity (11.9).

### Proposition 11.45 (the lower bound)

If eight unit squares form a packing in a closed disk of squared radius $q$,
then $q \ge q_*$.

*Proof.* Translate the packing so that the disk centre is $o$, and suppose
$q \le q_*$. The packing also lies in the disk of squared radius $q_*$, which is
below $Q_1$. By Theorem 11.10 it has a central square and seven exterior
squares; take a separating axis on each consecutive pair. By
Proposition 11.15 the exterior squares give a boundary cycle at the level
$\max(q_*, q_-) = q_*$ with the same frames and axes, and by Lemma 11.17 its
expansions to $Q_1$ and $Q_0$; by Theorem 11.23 and Proposition 11.28 the word is
$0101011$, and by Lemma 11.30 a renumbering, a rotation and possibly a
reflection, applied to the whole packing, normalize the cycle. The moved packing
still lies in the disk of squared radius $q$. By Theorem 11.43 its exterior
squares have the frames of the models and the chosen axes have the normals of
the seven contacts.

With these frames the vertex $p_P + o_P$ of each of the squares $A$, $B$, $D$,
$E$, $H$ is a point of the square, so it lies in the disk of squared radius $q$,
and each chosen separation says that the corresponding gap of Theorem 11.44,
formed with the centres of the original squares, is nonnegative. By
Theorem 11.44, $q_* \le q$. $\square$

*Lean:
[`Eight.GeometricModel.stationary_normalization_exists`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L90),
[`Eight.GlobalNormalization`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L49),
[`Eight.boundary_normalization_exists`](../../SquaresInCircles/Eight/Boundary/RadiusTransfer.lean#L737),
[`Eight.GeometricModel.normalized_at_original_radius`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L78),
[`Eight.GeometricModel.originalPositions`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L128),
[`Eight.GeometricModel.source_contained_at_original_radius`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L132),
[`Eight.vertices_at_original_radius`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L656),
[`Eight.gaps_of_retained_normals`](../../SquaresInCircles/Eight/Boundary/SourceEquality.lean#L622),
[`Eight.GeometricModel.sharp_rigidity_of_original_witnesses`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L222),
[`Eight.sharp_source_entry_original_rigidity`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L116),
[`Eight.sharp_original_rigidity`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L243),
[`Eight.GeometricModel.origin_sharp_rigidity`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L39),
[`Eight.GeometricModel.origin_sharp_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L56),
[`Eight.GeometricModel.sharp_squared_radius_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L63),
[`Eight.GeometricModel.sharp_radius_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L74),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55).*

The boundary cycle is used only to find the frames and the separating axes;
the radius comes from (11.9) applied to the original squares, which needs no
estimate of how far a square moved in the reduction. The same argument at the
radius $q_*$ itself proves more.

## 11.13 The packings at the optimal radius

### Proposition 11.46 (the exterior squares at the optimal radius)

Let eight unit squares form a packing in a closed disk of radius $\sqrt{q_*}$
about $o$. Then, after a renumbering, a rotation about $o$ and possibly a
reflection in a line through $o$, the seven exterior squares are the squares
$A$, $B$, $D$, $E$, $H$ of the models and the squares $T$ and $G$ of the models
for some $\zeta$ and $\eta$, with $\frac7{12} \le \zeta \le \zeta_+$ and
$\eta_- \le \eta \le \eta_+$, and the central square contains the closed disk
$\overline D(o, \frac1{12})$ in its interior.

*Proof.* Run the proof of Proposition 11.45 with $q = q_*$. By Theorem 11.44 the
centres of $A$, $B$, $D$, $E$, $H$ are those of the models, every gap vanishes,
and the centres of $T$ and $G$ are $(x_2 - \frac32, \zeta)$ and
$p_H + e + \eta f$. A unit square is determined by its centre and its frame up
to quarter turns, so with the frames of Theorem 11.43 the seven squares are those
of the models. The order of the centre directions puts the centre of $T$ in the
sector from $B$ to $D$, and two consecutive gaps add up to less than $\pi$ by
(11.4), so $\zeta > 0$; the centre of $G$ lies in the sector from $H$ to $A$,
which gives $h_2 + \frac12 + \eta < 0$. Both squares avoid the closed disk
$\overline D(o, \frac1{12})$ by Theorem 11.10: the point $(0, \zeta - \frac12)$ of
the lower side of $T$ gives $\zeta \ge \frac7{12}$, and the point
$(h_2 + 1 + \eta)f$ of the upper side of $G$ gives $\eta \le \eta_+$. Containment
gives $\zeta \le \zeta_+$ and $\eta \ge \eta_-$ (Proposition 11.6 (1)), and the
central square contains the core disk by Theorem 11.10. $\square$

*Lean:
[`Eight.GeometricModel.source_centers_of_original_anchors`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L83),
[`Eight.sameSquare_of_physical_center`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L84),
[`Eight.GeometricModel.source_squares_of_original_centers`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L107),
[`Eight.GlobalNormalization.original_slider_sectors`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L560),
[`Eight.two_successive_gaps_lt_pi`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L483),
[`Eight.polarOrder_positive_three`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L528),
[`Eight.core_primary_of_small_secondary`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L542).*

### Proposition 11.47 (uniqueness)

Every packing of eight unit squares in a closed disk of radius $R_8$ is
congruent to the model of admissible parameters or to its mirror image in the
diagonal; in particular it is congruent to an optimal model.

*Proof.* Translate the packing so that the disk centre is the origin; the
translation is a congruence. By Proposition 11.46, after a rotation about the
origin, possibly a reflection, and a renumbering, the exterior squares are
those of the models for some $\zeta$ and $\eta$ with $\frac7{12} \le \zeta \le \zeta_+$
and $\eta_- \le \eta \le \eta_+$, and the central square $K$ contains the closed
disk of radius $\frac1{12}$ about the origin in its interior. One of the four
frames of $K$ makes an angle $\varphi \in [-\frac\pi4, \frac\pi4)$ with the
horizontal, and $w = \frac{\sin\varphi}{1 + \cos\varphi}$ lies in
$[1 - \sqrt2, \sqrt2 - 1)$; let $(x, y)$ be the centre of $K$. The packing is the
model of $(x, y, \varphi, \zeta, \eta)$, and it is a packing in the closed disk
of radius $R_8$; so the conditions of Proposition 11.6 (3) hold: the frame and
the sliders by construction, the core conditions because $K$ contains the core
disk, and the separations because $K$ is disjoint from the seven exterior
squares. By Proposition 11.6 (3) the parameters are admissible, and the packing
is the model of these parameters, or its mirror image if a reflection was used.
Admissible models and their mirror images are packings in the closed disk of
radius $R_8$ (Proposition 11.6 (2)), so they are optimal models. $\square$

*Lean:
[`Eight.GeometricModel.origin_sharp_uniqueness`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L139),
[`Eight.GeometricModel.sharp_uniqueness`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L202),
[`Eight.Stationary.central_parameters_exist`](../../SquaresInCircles/Eight/Stationary/FixedEval.lean#L923),
[`Eight.admissible_of_original_geometry`](../../SquaresInCircles/Eight/Stationary/Family.lean#L1038),
[`Eight.containsCore_center_bounds`](../../SquaresInCircles/Eight/Stationary/Family.lean#L1005),
[`Eight.stationaryModels`](../../SquaresInCircles/Eight/Stationary/Family.lean#L1104),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38),
[`Eight.admissibleModels_subset`](../../SquaresInCircles/Eight/Uniqueness.lean#L45),
[`Eight.model_eq`](../../SquaresInCircles/Eight/Uniqueness.lean#L37),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62).*

*Proof of Theorem 11.1.* Part (1) is Proposition 11.5. Part (2): by
Proposition 11.7 there are admissible parameters, whose models are packings in
the closed disk of radius $R_8$ by Proposition 11.6 (2), and every model has the
corner $P_1$ of its square $A$ on the circle, as does its mirror image. Part (3):
by Proposition 11.45, $R^2 \ge q_* = R_8^2$. Part (4): by Proposition 11.47 every
packing in a closed disk of radius $R_8$ is congruent to an optimal model, and
conversely a configuration congruent to an optimal model is a packing in a
closed disk of radius $R_8$, by the definition of the optimal models and
[Lemma 2.7](02-preliminaries.md#lemma-27-congruent-configurations). $\square$

*Lean:
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.GeometricModel.models_nonempty`](../../SquaresInCircles/Eight/Construction.lean#L55),
[`Eight.GeometricModel.model_packing`](../../SquaresInCircles/Eight/Construction.lean#L58),
[`Eight.models_reach`](../../SquaresInCircles/Eight/Uniqueness.lean#L70),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62),
[`Eight.optimum`](../../SquaresInCircles/Eight/Uniqueness.lean#L82).*

The theorem fits the scheme of
[Corollary 2.10](02-preliminaries.md#corollary-210-the-scheme-of-proof), with
the optimal models as the set $\mathcal M$: they are packings in the disk, they
reach the circle at the corner $P_1$ of $A$, and every packing at the radius
$R_8$ is congruent to one of them. Here, unlike in the earlier chapters, the
lower bound is also proved directly, by Proposition 11.45.
