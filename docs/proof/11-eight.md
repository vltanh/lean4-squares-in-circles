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

The radius has no closed form. Five corners on one circle and seven contacts
between the squares leave, for each radius, a chain of squares with two free
numbers, a position and a tilt; the fifth corner of the chain may stick out of
the circle, and $R_8^2 = q_*$ is the least squared radius at which it does not.
At that radius the excess of the fifth corner and its two derivatives vanish
together, and $q_*$ is the first coordinate of the unique solution of an
explicit system of equations (Theorem 11.1, Proposition 11.4).

The proof differs from those of the earlier chapters in one respect. Its steps
are continuous arguments: a square holding a small disk about the centre, a
cycle of the seven other squares pushed out to two boundary curves, a bound on
how far their frames can turn against each other, a word in the quarter turns
between neighbours that leaves one arrangement, and a final weighted inequality
that gives the radius $q_*$ exactly, in the spirit of the stresses of
Chapter 9. Between the word and the final inequality, however, the proof pins
the frames of the seven squares to those of Figure 11.1 by finite tables of
explicit inequalities: 660,370 rows in ten affine-arc tables, 3,513 quartic
polynomials for the separating axes and the tilt, and the tables that exclude
the wrong words. Each row is a statement about a whole interval of angles and
two whole arcs of states, proved by a fixed polynomial identity. This chapter
gives the continuous argument in full, says what each row proves and how the
rows are checked, and gives the size and the role of each table; it does not
print the tables. The formalization checks every row in Lean.

## Theorem 11.1 (eight squares)

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
$c_* = \cos t_*$ and $s_* = \sin t_*$, and $R_8 = \sqrt{q_*}$. Numerically
$q_* \approx 3.9155341375$, $R_8 \approx 1.9787709$, $y_* \approx -0.92066$
and $t_* \approx 0.12364$, about $7.08°$.

Let $e = (c_*, s_*)$ and $f = (-s_*, c_*)$. For real numbers
$x, y, w, \zeta, \eta$, the *model* $M(x, y, w, \zeta, \eta)$ consists of
the eight unit squares

```math
A = Q\left(x_1 - \tfrac12,\ y_* + \tfrac12\right), \quad B = Q\left(x_2 - \tfrac12,\ y_* + \tfrac32\right), \quad D = Q\left(x_3 + \tfrac12,\ y_3 - \tfrac12\right), \quad E = Q\left(x_4 + \tfrac12,\ y_4 + \tfrac12\right), \quad T = Q\left(x_2 - \tfrac32,\ \zeta\right),
```

the squares $H$ and $G$ with the frame $e$, $f$ and the centres

```math
p_H = \left(h_1 + \tfrac12\right)e + \left(h_2 + \tfrac12\right)f, \qquad p_G = \left(h_1 + \tfrac32\right)e + \left(h_2 + \tfrac12 + \eta\right)f ,
```

and the *central square* $K$ with the centre $(x, y)$ and the frame
$(C_w, S_w)$, $(-S_w, C_w)$, where $C_w = \frac{1 - w^2}{1 + w^2}$ and
$S_w = \frac{2w}{1 + w^2}$; in the notation of
[Definition 9.9](09-six.md#definition-99-squares-in-a-frame),
$H = Q_{t_*}(h_1 + \frac12, h_2 + \frac12)$ and
$G = Q_{t_*}(h_1 + \frac32, h_2 + \frac12 + \eta)$. Put

```math
\zeta_+ = \sqrt{q_* - (x_2 - 1)^2} - \tfrac12, \qquad \eta_- = -h_2 - \sqrt{q_* - (h_1 + 2)^2}, \qquad \eta_+ = -h_2 - \tfrac{13}{12} ,
```

so that $\zeta_+ \approx 1.36600$, $\eta_- \approx -0.44505$ and
$\eta_+ \approx 0.34665$, and for a vector $v = (v_1, v_2)$ let

```math
\begin{aligned}
M_0(v) &= \max\left(|v_1|,\ |v_2|,\ |C_w v_1 + S_w v_2|,\ |-S_w v_1 + C_w v_2|\right), & W_0 &= \tfrac12\left(1 + C_w + |S_w|\right), \\
M_*(v) &= \max\left(|c_* v_1 + s_* v_2|,\ |-s_* v_1 + c_* v_2|,\ |C_w v_1 + S_w v_2|,\ |-S_w v_1 + C_w v_2|\right), & W_* &= \tfrac12\left(1 + c_* C_w + s_* S_w + |c_* S_w - s_* C_w|\right).
\end{aligned}
```

The parameters are *admissible* if

```math
\begin{gathered}
1 - \sqrt2 \le w < \sqrt2 - 1, \qquad \tfrac7{12} \le \zeta \le \zeta_+, \qquad \eta_- \le \eta \le \eta_+, \\
|C_w x + S_w y| < \tfrac5{12}, \qquad |-S_w x + C_w y| < \tfrac5{12}, \\
M_0\left(p_P - (x, y)\right) \ge W_0 \quad (P = A, B, D, E, T), \qquad M_*\left(p_P - (x, y)\right) \ge W_* \quad (P = H, G),
\end{gathered}
```

where $p_P$ is the centre of the square $P$ of the model.

1. For admissible parameters the model is a packing in the closed disk of
   radius $R_8$ about the origin, and so is its mirror image in the diagonal
   $y = x$.
2. If eight unit squares form a packing in a closed disk of radius $R$, then
   $R \ge R_8$.
3. The packings of eight unit squares in a closed disk of radius $R_8$ are
   exactly the configurations congruent to the model of admissible parameters
   or to its mirror image in the diagonal.

![The optimal packing of eight unit squares in its dashed circle of radius about 1.9788 about the disk centre o: at the right the squares A below and B above, at the left D above and E below, the square T on top between B and D, and at the bottom the two squares H and G, turned by about 7 degrees; in the middle the grey central square K, turned by about 11 degrees, holds o and a small shaded disk of radius 1/12 about it. Five dots mark the corners P1 to P5 of A, B, D, E and H on the circle; thick segments mark the five contacts along sides, A with B, B with T, T with D, D with E and H with G, and two larger dots the corner contacts of E with H and of A with G](figures/11-eight/eight.svg)

*Figure 11.1.* The model with the parameters
$(x, y, w, \zeta, \eta) = (0.14, 0, 0.1, 1.35, -0.32)$, the centre of the box
of Proposition 11.7, in its circle of radius $R_8$ (dashed). The corners
$P_1, \dots, P_5$ of $A$, $B$, $D$, $E$ and $H$ lie on the circle (dots), and
the seven exterior squares touch in a cycle: $A$ with $B$, $B$ with $T$,
$T$ with $D$, $D$ with $E$ and $H$ with $G$ along segments of their sides
(thick), $E$ with $H$ and $G$ with $A$ at a corner of one square on a side of
the other (large dots).
The central square $K$ (grey) holds the disk of radius $\frac1{12}$ about $o$
(shaded) and touches none of the others.

*Lean: [`Eight.FiveCorner`](../../SquaresInCircles/Geometry.lean#L293),
[`Eight.FiveCorner.spans`](../../SquaresInCircles/Geometry.lean#L303),
[`Eight.FiveCorner.selected`](../../SquaresInCircles/Geometry.lean#L334),
[`Eight.radius`](../../SquaresInCircles/Geometry.lean#L325),
[`Eight.Parameters`](../../SquaresInCircles/Geometry.lean#L359),
[`Eight.model`](../../SquaresInCircles/Geometry.lean#L367),
[`Eight.models`](../../SquaresInCircles/Geometry.lean#L389),
[`Eight.ExactFamily.Coordinates`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L54),
[`Eight.ExactFamily.Coordinates.IsStationary`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L96),
[`Eight.ExactFamily.EqualityParameters.Admissible`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L297),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62),
[`Eight.optimum`](../../SquaresInCircles/Eight/Uniqueness.lean#L82),
[`Eight.equality_iff_parameters`](../../SquaresInCircles/Eight/Uniqueness.lean#L107).*

*Remarks.* (i) In the stationary chart used by the proof, the parameters $\zeta$ and
$\eta$ are called z and eta. The public geometric parameters call them top
and tilted, and use the central angle $\theta=2\arctan w$ directly. The conditions on the parameters say the following. The first
line takes one frame of $K$ out of the four quarter turns of each (the angle
$2\arctan w$ lies in $[-\frac\pi4, \frac\pi4)$) and bounds the positions of
$T$ and $G$. The second line says that the closed disk of radius $\frac1{12}$
about the origin lies in the open square $K$: the local coordinates of the
origin in $K$ are less than $\frac5{12}$ in absolute value. The last line says
that $K$ is separated from each of the seven other squares along one of the
eight axes of the pair, the separating-axis theorem of
[Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares) with its
threshold $\tau$ written out (Proposition 11.6).

(ii) The optimum is not unique. The five squares $A$, $B$, $D$, $E$, $H$ that
touch the circle and the frames of all seven exterior squares are fixed. The
top square $T$ moves vertically, the square $G$ slides along $H$, and the
central square moves and turns; the room for each depends on the positions of
the others (Figures 11.2 and 11.5). Proposition 11.7 gives a box of
parameters, of side $0.002$ in each of the five directions, whose points are
all admissible and give pairwise non-congruent packings, even when reflections
are allowed.

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
not move, while $T$, $G$ and the central square $K$ do. The parameters
$(x, y, w, \zeta, \eta)$ are $(0.14, 0, 0.1, 1.35, -0.32)$,
$(0.17, -0.18, 0.07, 0.92, -0.32)$, $(0.14, 0.015, 0.08, 1.35, -0.1)$ and
$(-0.0475, -0.0325, -0.3, \zeta_+, \eta_-)$: the centre of the box of
Proposition 11.7, $T$ lowered, $G$ pushed towards the centre, and $T$ and $G$
on the circle with $K$ turned by about $-33°$. All four are admissible.

*Outline of the proof.* Part (1) is Proposition 11.6 (§11.1). Part (2) is
Proposition 11.37 (§11.11): the lower bound is proved directly, not through
uniqueness, since the argument works below the radius $R_8$ as well. Part (3)
is Proposition 11.39 (§11.12). The proof of the lower bound has eight steps.

1. *The central core* (§11.2). In a packing of eight squares in a disk of
   squared radius at most $Q_0 = \frac{9789}{2500}$, just above $q_*$, one
   square contains the closed disk of radius $\frac1{12}$ about the disk
   centre in its interior (Theorem 11.10). From then on only the seven other
   squares, the *exterior squares*, and their consecutive pairs are kept.
2. *A boundary cycle* (§11.3). Each exterior square can be translated, with
   its frame and one chosen separating axis on each consecutive pair kept,
   until it touches the circle or the core (Proposition 11.15). Its state
   then lies on one of two curves, $\mathcal O$ and $\mathcal C$.
3. *Three radius levels* (§11.4). Pushing the squares on $\mathcal O$ outward
   keeps every separating axis (Lemma 11.17). This moves a cycle from the
   actual radius to the fixed levels $Q_1$ and $Q_0$ at which the tables are
   computed, and back.
4. *Frame concentration* (§11.5). The frames of the seven squares lie, modulo
   quarter turns, in an interval shorter than $\frac7{10}$
   (Theorem 11.23).
5. *The quarter word* (§11.6). The quarter turns between the frames of
   neighbours form a word of seven digits, and only the word $0101011$ of
   Figure 11.1 survives (Proposition 11.26).
6. *Candidate coordinates* (§11.7, §11.8). Six affine-arc tables bound the
   positions of four squares (Proposition 11.29).
7. *The mismatch chain* (§11.9). Four more affine-arc tables shrink the
   angles between the frames of aligned neighbours, the *mismatch*, from
   $\frac{13}{50}$ to $\frac1{1000}$ (Proposition 11.34).
8. *The sharp terminal* (§11.10, §11.11). Quartic tables fix the separating
   axes and the tilt (Proposition 11.35), and a weighted sum of the
   seven contacts and five corner constraints, with the weights of the
   stationary chain, gives $q \ge q_*$ (Theorem 11.36). Applied to the
   original squares at $q = q_*$, the same weighted sum fixes the five squares
   on the circle (Proposition 11.38).

The longer proofs are in [Appendix J](appendix-j.md) (the stationary
system), [Appendix K](appendix-k.md) (the central core),
[Appendix L](appendix-l.md) (what a table row proves) and
[Appendix M](appendix-m.md) (the sharp terminal).

The public statement in `Geometry.lean` defines the radius directly as the
least radius holding five corners with the required spans, and describes the
family by the central square's centre and angle and the two slider positions.
The stationary coordinates below give an equivalent chart used by the table
proof. `FiveCorner.existsUnique_minimizer` identifies the five fixed corners,
`radius_eq_stationary` identifies the radii, and `models_eq_stationary`
identifies the admissible families, including their reflections.

*Lean:
[`Eight.FiveCorner.existsUnique_minimizer`](../../SquaresInCircles/Eight/Corners/GeometricStationaryExistence.lean#L868),
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38).*

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
[`Eight.ExactFamily.Coordinates`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L54),
[`Eight.ExactFamily.Coordinates.IsChain`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L84),
[`Eight.ExactFamily.Coordinates.defect`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L71),
[`Eight.ExactFamily.Coordinates.positionDerivative`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L77),
[`Eight.ExactFamily.Coordinates.tiltDerivative`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L79),
[`Eight.ExactFamily.Coordinates.anchorPoints`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L193),
[`Eight.ExactFamily.Coordinates.exteriorSquares`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L189).*

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
[`Eight.ExactFamily.Coordinates.anchor_vertex`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L204),
[`Eight.ExactFamily.Coordinates.anchor_circle`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L211),
[`Eight.ExactFamily.Coordinates.standard_contacts`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L246),
[`Eight.ExactFamily.Coordinates.HG_contact`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L220),
[`Eight.ExactFamily.Coordinates.GA_contact`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L225),
[`Eight.ExactFamily.Coordinates.HE_contact`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L240),
[`Eight.ExactFamily.Coordinates.HA_contact`](../../SquaresInCircles/Eight/ExactFamily/Coordinates.lean#L234).*

So the chain realizes the seven contacts of Figure 11.1 for every $q$, $y$
and $t$, and it closes, with all five corners on the circle of radius
$\sqrt q$, exactly when $F(q, y, t) = 0$ (Figure 11.3). For $q$ near $q_*$
the defect has a unique minimum in $(y, t)$, which decreases as $q$ grows; the
least $q$ at which the minimum reaches 0 is $q_*$, and there the minimum is a
simultaneous zero of $F$, $F_y$ and $F_t$.

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
[`Eight.ExactFamily.exact_stationary_existsUnique`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L251),
[`Eight.ExactFamily.qStar_bracket`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L159),
[`Eight.ExactFamily.qStar_limits`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L171),
[`Eight.radius_levels`](../../SquaresInCircles/Eight/Model.lean#L38),
[`Eight.ExactFamily.sharp_coordinates`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L254),
[`Eight.ExactFamily.sharp_y`](../../SquaresInCircles/Eight/ExactFamily/Stationary.lean#L289),
[`Eight.ExactFamily.unique_minimum_zero`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L360),
[`Eight.ExactFamily.minimum_radius_difference`](../../SquaresInCircles/Eight/ExactFamily/Analysis.lean#L312).*

The three numbers $q_-$, $Q_1$ and $Q_0$ are the *radius levels* of the
proof (§11.4). The level $Q_0$ is a round number above $q_*$; $Q_1$ exceeds
$q_*$ by less than $5 \cdot 10^{-10}$; and $q_- < q_*$ is used to start the
lower bound.

### Proposition 11.5 (the seven exterior squares)

Let $\frac7{12} \le \zeta \le \zeta_+$ and $\eta_- \le \eta \le \eta_+$. Then
the seven squares $A$, $B$, $D$, $E$, $H$, $T$, $G$ of the model are pairwise
disjoint and lie in the closed disk of radius $R_8$ about the origin, and the
corners $P_1, \dots, P_5$ of $A$, $B$, $D$, $E$, $H$ lie on its circle. The
square $T$ reaches the circle exactly when $\zeta = \zeta_+$, and $G$ exactly
when $\eta = \eta_-$.

*Proof.* We use the bounds of Proposition 11.4 (3) throughout.

*Containment.* By [Lemma 3.4](03-tools.md#lemma-34-farthest-vertex) a square
lies in the closed disk of radius $R_8$ exactly when its vertex farthest from
the origin does, and that vertex is the one across both axes of the square
from the origin. The centre of $A$ has a positive first and a negative second
coordinate, as $x_1 > \frac12$ and $y_* < -\frac12$, so its farthest vertex
is its lower right corner $P_1$; in the same way the farthest vertices of $B$,
$D$, $E$ are $P_2$, $P_3$, $P_4$, and that of $H$, whose coordinates
$h_1 + \frac12$ and $h_2 + \frac12$ in the frame $e$, $f$ are negative, is
$P_5 = h_1 e + h_2 f$. These five points are at squared distance $q_*$ by
Lemma 11.3 (1), since $F = 0$ at the solution. The centre of $T$ has the
coordinates $x_2 - \frac32 \in (0, \frac12)$ and $\zeta > 0$, so its farthest
vertex is $(x_2 - 1, \zeta + \frac12)$, at squared distance at most $q_*$
exactly when $\zeta \le \zeta_+$. In the frame $e$, $f$ the centre of $G$ has
the coordinates $h_1 + \frac32 \in (0, \frac12)$ and
$h_2 + \frac12 + \eta \le -\frac7{12}$, as $\eta \le \eta_+$; so its farthest
vertex is $(h_1 + 2)e + (h_2 + \eta)f$, at squared distance
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
$\langle (1, 0), p_G\rangle - \frac12(c_* + s_*)$, which decreases as $\eta$
grows, and at $\eta = \eta_+$ equals
$c_*(h_1 + 1) + \frac{s_*}{12} > -0.355$, while the right side of $E$ is at
$x_4 + 1 < -0.902$.

*Six pairs across the horizontal axis.* The highest point of $H$ has the
height $s_*(h_1 + 1) + c_*(h_2 + 1) < 0$, and that of $G$ is
$s_*(h_1 + 2) + c_*(h_2 + 1 + \eta) \le s_*(h_1 + 2) - \frac{c_*}{12} < -0.004$.
The lowest points of $B$, $D$, $T$ have the heights $y_* + 1$, $y_3 - 1$ and
$\zeta - \frac12 \ge \frac1{12}$, all positive. So the horizontal axis
separates each of $H$, $G$ from each of $B$, $D$, $T$.

These are $10 + 4 + 1 + 6 = 21$ pairs, all the pairs of the seven squares.
$\square$

*Lean:
[`Eight.ExactFamily.exterior_contained`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L258),
[`Eight.ExactFamily.exterior_disjoint`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L544),
[`Eight.ExactFamily.sharp_exterior_bounds`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L49),
[`Eight.ExactFamily.axis_containment`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L243),
[`Eight.ExactFamily.tilted_containment`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L247).*

![The exterior squares of the model of Figure 11.1 with the ranges of its two moving squares: the top square T drawn dashed at its lowest position, its centre at height 7/12 and its lower side touching the disk of radius 1/12 about o, and at its highest position, at height zeta+, with a corner on the circle; the turned square G drawn dashed at its two extreme positions along H, at eta+ touching the disk of radius 1/12 with its upper side and at eta- touching the circle with a corner. Dotted segments show the paths of the two centres](figures/11-eight/sliders.svg)

*Figure 11.4.* The two exterior squares that move. $T$ moves vertically with
$\frac7{12} \le \zeta \le \zeta_+$, from touching the disk of radius
$\frac1{12}$ to touching the circle; $G$ slides along $H$ with
$\eta_- \le \eta \le \eta_+$, from the circle to the disk of radius
$\frac1{12}$ (dashed: the extreme positions; dotted: the paths of the
centres). The other five exterior squares are fixed.

### Proposition 11.6 (the five-parameter family)

1. For admissible parameters, the model is a packing in the closed disk of
   radius $R_8$ about the origin; its central square $K$ contains the closed
   disk of radius $\frac1{12}$ about the origin in its interior; and the
   corners $P_1, \dots, P_5$ lie on the circle.
2. Conversely, let $\frac7{12} \le \zeta \le \zeta_+$ and
   $\eta_- \le \eta \le \eta_+$, and let $K$ be a unit square with centre
   $(x, y)$ whose frame is turned by $2\arctan w$ with
   $1 - \sqrt2 \le w < \sqrt2 - 1$. If $K$ contains the closed disk of radius
   $\frac1{12}$ about the origin in its interior and is disjoint from the
   seven exterior squares of the model with these $\zeta$ and $\eta$, then
   $(x, y, w, \zeta, \eta)$ is admissible.

*Proof.* The local coordinates of the origin in $K$ are
$-(C_w x + S_w y)$ and $-(-S_w x + C_w y)$. So the second line of the
admissibility conditions says that both are less than $\frac5{12}$ in absolute
value, and by [Lemma 3.9](03-tools.md#lemma-39-inscribed-disks) (2), with
$\alpha = \frac5{12}$, the open disk of radius $\frac1{12}$ about the origin
lies in $K^\circ$; as the inequalities are strict, a slightly larger
$\alpha$ still works, and the closed disk lies in $K^\circ$. Conversely, if
the closed disk lies in $K^\circ$, the point at distance $\frac1{12}$ from
the origin along each axis of $K$ lies in $K^\circ$, which gives the two
strict inequalities. The vertex of $K$ farthest from the origin is at squared
distance less than $2(\frac5{12} + \frac12)^2 = \frac{121}{72} < q_*$
([Lemma 3.4](03-tools.md#lemma-34-farthest-vertex)), so $K$ lies in the disk.

Let $P$ be one of the seven exterior squares and $v = p_P - (x, y)$. If $P$
has the frame $(1, 0)$, $(0, 1)$, the relative angle of $K$ and $P$ is
$\delta = 2\arctan w$, with $\cos\delta = C_w > 0$ and $\sin\delta = S_w$, so
the threshold of [Lemma 9.11](09-six.md#lemma-911-separating-axes-of-two-squares)
is $\tau(\delta) = W_0$, and the eight vectors $\pm n$ of that lemma give the
eight numbers $\pm\langle n, v\rangle$ whose largest value is $M_0(v)$. If $P$
is $H$ or $G$, the relative angle is $\delta = 2\arctan w - t_*$, with
$|\delta| < \frac\pi2$, $\cos\delta = c_* C_w + s_* S_w > 0$ and
$\sin\delta = c_* S_w - s_* C_w$, so $\tau(\delta) = W_*$ and the largest of
the eight numbers is $M_*(v)$. By Lemma 9.11, $K$ and $P$ are disjoint
exactly when this largest number is at least the threshold. With
Proposition 11.5 this proves (1), and the corners are on the circle by
Proposition 11.5. For (2), the frame condition and the slider ranges are
hypotheses, the second line is the core, and the last line is disjointness
from the seven squares. $\square$

*Lean:
[`Eight.ExactFamily.model_sqPacking`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L558),
[`Eight.ExactFamily.sat_max_iff`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L121),
[`Eight.ExactFamily.central_axis_sat`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L219),
[`Eight.ExactFamily.central_tilted_sat`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L228),
[`Eight.ExactFamily.frame_parameter_bounds`](../../SquaresInCircles/Eight/ExactFamily/EqualityGeometry.lean#L191),
[`Eight.model_packing`](../../SquaresInCircles/Eight/Equality.lean#L242),
[`Eight.model_reaches`](../../SquaresInCircles/Eight/Equality.lean#L258),
[`Eight.containsCore_center_bounds`](../../SquaresInCircles/Eight/Equality.lean#L135).*

The family is not a product of intervals. For instance $\zeta = \frac7{12}$
is not attained: then the lower side of $T$ is at height $\frac1{12}$ above
the disk centre, but $K$ contains a point above that height near the centre,
inside the column of $T$. Figure 11.5 shows a section.

![The plane of the centre (x, y) of the central square for the frame parameter w = 0.1 and the sliders zeta = 1.35, eta = -0.32: the admissible centres form a shaded pentagon, tall and narrow, about 0.07 wide and 0.24 high, bounded by five straight segments, on each of which the central square touches one of the exterior squares D, B, A, G and H, labelled in their colours; a tiny black box around (0.14, 0) is marked inside it](figures/11-eight/section.svg)

*Figure 11.5.* A section of the family: the centres $(x, y)$ admissible with
$w = 0.1$, $\zeta = 1.35$ and $\eta = -0.32$ (shaded). Each side of the region
is a contact of $K$ with an exterior square, labelled by that square; the
core condition $|C_w x + S_w y|, |-S_w x + C_w y| \le \frac5{12}$ is not
active on this section. The small box is the section of the box of
Proposition 11.7.

### Proposition 11.7 (a box of different packings)

Let $\mathcal B$ be the box of the parameters with

```math
0.139 \le x \le 0.141, \qquad -0.001 \le y \le 0.001, \qquad 0.099 \le w \le 0.101, \qquad 1.349 \le \zeta \le 1.351, \qquad -0.321 \le \eta \le -0.319 .
```

1. Every point of $\mathcal B$ is admissible, and every inequality of the
   admissibility conditions in which $x$, $y$, $w$, $\zeta$ or $\eta$ occurs
   holds with room to spare uniformly on $\mathcal B$: the central square is
   separated from $A$, $B$, $D$, $E$, $H$, $G$, $T$ along the unit normals
   $(1, 0)$, $(C_w, S_w)$, $(-S_w, C_w)$, $(-1, 0)$, $(-C_w, -S_w)$,
   $(s_*, -c_*)$, $(0, 1)$ with the projected gaps of the centres exceeding
   the thresholds by more than $0.020$, $0.020$, $0.036$, $0.450$, $0.031$,
   $0.192$, $0.257$; $|C_w x + S_w y| < 0.139$ and $|-S_w x + C_w y| < 0.030$;
   and $q_* - (x_2 - 1)^2 - (\zeta + \frac12)^2 > 0.055$ and
   $q_* - (h_1 + 2)^2 - (h_2 + \eta)^2 > 0.448$.
2. If two points of $\mathcal B$ give models that are congruent, even by an
   isometry of the plane that reflects, with a relabelling of the squares,
   then the two points are equal.

*Proof.* (1) Each listed quantity is a function of the five parameters and of
the constants of Proposition 11.4 (3), monotone or rational in each
parameter; bounding it with the endpoints of $\mathcal B$ and of those brackets
is a finite rational computation. For instance, the gap for $B$ is
$C_w(x_2 - \frac12 - x) + S_w(y_* + \frac32 - y) - \frac12(1 + C_w + S_w)$,
with $C_w$ between $\frac{1 - 0.101^2}{1 + 0.101^2}$ and
$\frac{1 - 0.099^2}{1 + 0.099^2}$ and $S_w$ between
$\frac{2 \cdot 0.099}{1 + 0.099^2}$ and $\frac{2 \cdot 0.101}{1 + 0.101^2}$.
On $\mathcal B$, $c_* S_w - s_* C_w > 0$, so the absolute value in $W_*$ has a
fixed sign. Each separation implies the corresponding maximum condition, and
the last two numbers are the room in the containment of $T$ and $G$ of
Proposition 11.5.

(2) Let the isometry $\Phi$ carry the model of $p \in \mathcal B$ onto the
model of $p' \in \mathcal B$, square by square up to a relabelling.

*The centre.* Let $\mu_A, \mu_B, \mu_D, \mu_E, \mu_H > 0$ be the weights of
Lemma J.6, with $\sum \mu_P = 1$ and $\sum \mu_P P_P = 0$, where
$P_A = P_1, \dots, P_H = P_5$ are the five corners on the circle. If all
eight squares of a model lie in a closed disk of radius $R_8$ about a point
$o'$, then

```math
q_* \ge \sum_P \mu_P |P_P - o'|^2 = \sum_P \mu_P |P_P|^2 - 2\left\langle \sum_P \mu_P P_P,\ o'\right\rangle + |o'|^2 = q_* + |o'|^2 ,
```

so $o'$ is the origin. As $\Phi$ maps the disk of radius $R_8$ about the
origin, which holds the model of $p$, onto a disk of radius $R_8$ about
$\Phi(0)$ holding the model of $p'$, $\Phi(0) = 0$, and $\Phi$ is linear.

*Two fixed centres.* On $\mathcal B$ the distances of the eight centres from
the origin lie in eight pairwise disjoint intervals, the same for $p$ and
$p'$ (for the fixed squares they do not depend on the parameters). As $\Phi$
preserves these distances, it maps each square to the square of the same name.
In particular it fixes $p_A$ and $p_E$, which are linearly independent, so
$\Phi$ is the identity.

*The parameters.* Then the two models are equal square by square: $T$ gives
$\zeta = \zeta'$, $G$ gives $\eta = \eta'$, $K$ gives $(x, y) = (x', y')$, and
the frame of $K$, determined modulo quarter turns, gives $w = w'$ since
$2\arctan w$ and $2\arctan w'$ lie in an interval of length less than
$\frac\pi2$. $\square$

*Lean: [`Eight.box_admissible`](../../SquaresInCircles/Eight/Equality.lean#L31),
[`Eight.whole_box_packing`](../../SquaresInCircles/Eight/Equality.lean#L268),
[`Eight.full_dimensional_equality_box`](../../SquaresInCircles/Eight/TableProof.lean#L559),
[`Eight.ExactFamily.box_data_bounds`](../../SquaresInCircles/Eight/ExactFamily/EqualityBox.lean#L232),
[`Eight.ExactFamily.BoxRigidity.enclosing_center_unique`](../../SquaresInCircles/Eight/ExactFamily/BoxRigidity.lean#L191),
[`Eight.ExactFamily.BoxRigidity.anchor_barycenter`](../../SquaresInCircles/Eight/ExactFamily/BoxRigidity.lean#L138),
[`Eight.ExactFamily.BoxRigidity.center_band`](../../SquaresInCircles/Eight/ExactFamily/BoxRigidity.lean#L217),
[`Eight.ExactFamily.BoxRigidity.box_rigidlyCongruent_iff`](../../SquaresInCircles/Eight/ExactFamily/BoxRigidity.lean#L429).*

So the optimal packings of eight squares form a family with five independent
parameters, and infinitely many of them are pairwise not congruent. The
family is large: in Figure 11.2 the square $T$ is lowered by $0.43$ and $G$ is
moved by $0.22$ from the box, and the frame of $K$ ranges over angles of both
signs.

## 11.2 The central square and the one-twelfth core

From here to §11.11 we prove the lower bound. Throughout, a packing of eight
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

*Lean:
[`Eight.squareAngles`](../../SquaresInCircles/Eight/CentralCore.lean#L79),
[`Eight.angularLength`](../../SquaresInCircles/Eight/CentralCore.lean#L82),
[`Eight.one_square_two_circle_inequality`](../../SquaresInCircles/Eight/CentralCore.lean#L1030).*

![The model of Figure 11.1 with the unit circle and the circle of radius 5/4 about o. Each of the seven exterior squares holds one arc of each circle, drawn thick in the colour of the square, and the arcs on each circle do not overlap; the grey central square K, which contains o, meets neither circle](figures/11-eight/measure.svg)

*Figure 11.6.* Lemma 11.8 in the optimal packing. On the unit circle
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
[`Eight.angularLength_budget`](../../SquaresInCircles/Eight/CentralCore.lean#L193),
[`Eight.central_exists_from_one_square_inequality`](../../SquaresInCircles/Eight/CentralCore.lean#L278),
[`Eight.central_square_exists`](../../SquaresInCircles/Eight/CentralCore.lean#L1080),
[`Eight.central_square_unique`](../../SquaresInCircles/Eight/CentralCore.lean#L305).*

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
[`Eight.central_core_and_exteriors`](../../SquaresInCircles/Eight/CentralCore.lean#L1837),
[`Eight.centralDepth_gt_milli`](../../SquaresInCircles/Eight/CentralCore.lean#L1475).*

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
[`Eight.annular_center_radius_lower`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L92),
[`Eight.annular_center_radius_upper`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L116),
[`Eight.Candidate.canonical_bounds`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L51),
[`Eight.coreAvoiding_iff_distance`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L71).*

![The model of Figure 11.1 with the centres of the exterior squares marked: the grey central square K containing the shaded disk of radius 1/12 about o, the dotted circle of radius 7/12 about o, and the seven exterior squares, which stay outside the shaded disk and whose centres all lie outside the dotted circle](figures/11-eight/core.svg)

*Figure 11.7.* The core in the optimal packing. The central square $K$
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
$q \le Q_0$, taken in the order of their centre directions and with any
choice of witnesses, form a neighbour cycle at level $\max(q, \frac52)$:
two disjoint exterior squares cannot have the same centre direction, since
their centres would be at least 1 apart on one ray although both lie at
distances between $\frac7{12}$ and $\frac{71}{50}$.

*Lean: [`Eight.NeighborCycle`](../../SquaresInCircles/Eight/Model.lean#L161),
[`Eight.SignedAxis.Feasible`](../../SquaresInCircles/Eight/Model.lean#L138),
[`Eight.signed_axis_of_disjoint`](../../SquaresInCircles/Eight/SeparatingAxis.lean#L53),
[`Eight.OrderedExterior`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L633),
[`Eight.ordered_exterior_exists`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L646),
[`Eight.center_direction_separated`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L597).*

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
[`Eight.polar_gap_cosine_bound`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L607),
[`Eight.annular_cosine_quotient`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L145),
[`Eight.gap_gt_three_fifths`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L641),
[`Eight.seven_gaps_below_pi`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L649).*

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

*Lean: [`Eight.RadialKind`](../../SquaresInCircles/Eight/Model.lean#L148),
[`Eight.BoundaryState`](../../SquaresInCircles/Eight/Model.lean#L152),
[`Eight.BoundaryCycle`](../../SquaresInCircles/Eight/Model.lean#L172),
[`Eight.BoundaryCycle.tangent`](../../SquaresInCircles/Eight/Model.lean#L191),
[`Eight.BoundaryCycle.alpha`](../../SquaresInCircles/Eight/Model.lean#L194),
[`Eight.BoundaryCycle.canonicalAngle`](../../SquaresInCircles/Eight/Model.lean#L197),
[`Eight.CanonicalSquare`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L775),
[`Eight.canonical_square_exists`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L788),
[`Eight.CanonicalSquare.boundary_kind`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L824).*

![The (a, b)-plane with 0 at most b at most a: the states allowed by containment and the core form a shaded strip between the core curve C, a vertical segment at a = 7/12 followed by a small quarter circle up to the diagonal, and the outer curve O, an arc of the circle about (-1/2, -1/2) of radius root q. The outer curve is divided at the lines b = a/4 and b = 3a/7 into the three types L, M and H, and the core curve at b = 6a/7 into its side and its corner. Dots mark the states of the seven exterior squares of the optimal packing, five on the outer curve and two inside the strip](figures/11-eight/radial.svg)

*Figure 11.8.* The radial curves at the level $Q_0$. The states allowed by
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
[`Eight.boundary_reduction_exists`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L1029),
[`Eight.anchored_cycle_exists`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L1003),
[`Eight.vertex_motion_exists`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L428),
[`Eight.two_halfplanes_recession`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L188),
[`Eight.first_two_boundary_contact`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L289),
[`Eight.boundary_normalization_exists`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L734),
[`Eight.BoundaryNormalization.original_selected_feasible`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L757).*

![The model of Figure 11.1 with the moves of the boundary reduction for its two squares that touch neither boundary. For T, its two witnesses, the vertical lines through its sides shared with B and D, leave it free to move vertically, and it moves up until its corner meets the circle; for G, its two witnesses, the lines across H and A perpendicular to e, leave it free to move along f, and it moves outward until its corner meets the circle. The moved squares are dashed, and arrows show the directions of the moves](figures/11-eight/reduction.svg)

*Figure 11.9.* Proposition 11.15 for the exterior squares of Figure 11.1. The
witnesses of $T$ are the vertical lines it shares with $D$ and $B$; their
inward normals are opposite, so $T$ moves along the perpendicular, up to the
circle. The witnesses of $G$ are perpendicular to $e$; $G$ moves along $f$,
out to the circle. The other five squares already touch the circle.

## 11.4 Three radius levels

The steps of the proof are carried out at three squared radii, the levels of
(11.1). The theorems on the core, the frames and the quarter words hold for
every level up to $Q_0$; the tables of §11.7 to §11.10 are computed once, at
the fixed level $Q_1$; and the final inequality is applied at the radius of
the packing itself. Between the levels the boundary cycles are moved by
pushing the squares on $\mathcal O$ outward along their centre directions.

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
[`Eight.RadiusTransfer.outerRadius`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L40),
[`Eight.RadiusTransfer.outerRadius_equation`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L78),
[`Eight.RadiusTransfer.outerRadius_bounds`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L86),
[`Eight.BoundaryCycle.core_radius_bound`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L350).*

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
[`Eight.RadiusTransfer.every_feasible_projection_preserved`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L255),
[`Eight.BoundaryCycle.expand_spec`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L577),
[`Eight.RadiusExpansion`](../../SquaresInCircles/Eight/Model.lean#L214),
[`Eight.radialSquare_core`](../../SquaresInCircles/Eight/BoundaryReduction.lean#L231).*

The lemma is used in two ways. A boundary cycle at the radius of a packing is
expanded to the level of a table, and every conclusion about frames, tangents,
gaps or words transfers back unchanged, since these do not move. And a
conclusion of the form "every separating axis of this pair belongs to a given
set", proved at the higher level, applies to the axes of the original cycle,
since each of them still separates after the expansion. No converse, that
inward motion keeps separations, is needed.

![Two graphs. Left: against q from 5/2 to 4, the distance r(q, B) from o of a centre whose state lies on the outer curve, for B = 1, rising from 1 to about 1.44, and for B = √2, rising from about 0.87 to about 1.29, with q* marked by a dashed vertical line. Right: against q from 3.2 to 4, the margins of the seven witnesses of the boundary cycle of Figure 11.9 when its squares are moved to the level q: seven nearly coincident increasing lines, one in the colour of each square, all crossing 0 at q*](figures/11-eight/expansion.svg)

*Figure 11.10.* Lemmas 11.16 and 11.17. Left: the outer radius $r(q, B)$
for the extreme values $B = 1$ (centre on the canonical axis) and
$B = \sqrt2$ (centre on the diagonal); both rise with slopes between
$\frac14$ and $\frac13$. Right: the seven witness margins of the boundary
cycle of Figure 11.9 when its squares are moved along their centre directions
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
[`Eight.exterior_pair_gap`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L103),
[`Eight.boundary_gap_lower`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L149),
[`Eight.boundary_gap_upper`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L173),
[`Eight.seven_gaps_three_quarters`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L158),
[`Eight.CentralBand.RayData.common_point_B`](../../SquaresInCircles/Eight/CentralCore.lean#L1658).*

![Four exterior squares that miss the core disk and lie in the disk of squared radius Q0, part of whose circle is dashed: two with their states on the outer curve, at b = 0 and at a = b, and two on the core curve, at its corner point (7/12, 1/2) and on its diagonal, each with its centre direction turned by 19/50 to one side of the horizontal axis through o. The wedge of half-angle 19/50 about the axis is shaded, and all four squares contain the point at distance 41/40 from o on the axis, marked by a red dot](figures/11-eight/common-point.svg)

*Figure 11.11.* Lemma 11.18: squares that miss the core, lie in the disk and
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
in the disk beyond a line at distance $d \ge 0$ from $o$ has a vertex at
squared distance at least $(d + 1)^2 + \frac14$ (Lemma K.7), and
$(\frac{23}{12})^2 + \frac14 = \frac{565}{144} > Q_0$, a contradiction. The
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
[`Eight.boundary_forward_complete`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L254),
[`Eight.backward_sine_lower`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L243),
[`Eight.BoundaryCycle.minus_source_y_projection`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L197),
[`Eight.BoundaryCycle.minus_target_y_projection`](../../SquaresInCircles/Eight/BoundaryGeometry.lean#L220),
[`Eight.forwardMargin`](../../SquaresInCircles/Eight/SeparatingAxis.lean#L201),
[`Eight.canonical_margin_identity`](../../SquaresInCircles/Eight/SeparatingAxis.lean#L224).*

![The pair B, T of the optimal packing drawn in the canonical frame of B, the source: B to the right of o, its canonical axis horizontal, and the target T above it and to the left, touching B along a short piece of their common vertical side. At each centre four signed axes are drawn as arrows: the four retained ones, numbered 1 to 4 (source +f upwards at B, target +e upwards at T, target +f to the left at T, source -e to the left at B), solid, and the other four dashed and faded. The dashed red vertical line through the far side of B, at distance a + 1/2 > 11/12 from o, cuts off a cap of the disk, shaded, too thin for a unit square](figures/11-eight/axes.svg)

*Figure 11.12.* Lemma 11.19 for the pair $B$, $T$ of Figure 11.1, drawn in the
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

*Lean: [`Eight.handGamma`](../../SquaresInCircles/Eight/Frames.lean#L80),
[`Eight.frameCost`](../../SquaresInCircles/Eight/Frames.lean#L145),
[`Eight.periodicFrameCost`](../../SquaresInCircles/Eight/Frames.lean#L149),
[`Eight.cyclic_markers_cancel`](../../SquaresInCircles/Eight/Frames.lean#L65),
[`Eight.Arithmetic.FourType.label`](../../SquaresInCircles/Eight/Arithmetic/FourTypePairs.lean#L66),
[`Eight.Arithmetic.FourType.TypeMem`](../../SquaresInCircles/Eight/Arithmetic/FourTypePairs.lean#L76).*

### Proposition 11.21 (pair costs of the four types; a finite table)

For two consecutive squares of a boundary cycle at the level $Q_0$, of types
$X$ and $Y$, and for each of the four margins of (11.5) that is nonnegative,

```math
\varphi - \tfrac9{50}\chi(\varphi) + \sigma L_X(a, b) - \sigma' L_Y(a', b') > \Gamma_{XY}, \qquad
\Gamma = \begin{pmatrix} .9200 & .9100 & .9005 & .8833 \\ .9100 & .9100 & .9005 & .8833 \\ .9005 & .9005 & .8912 & .8926 \\ .8833 & .8833 & .8926 & .9099 \end{pmatrix}
```

in the order $\mathsf C, \mathsf L, \mathsf M, \mathsf H$ of the rows and the
columns.

The proposition is a finite collection of continuous inequalities, one for
each ordered pair of types, signs and retained axis. The hand proof treats
the ten unordered pairs of types in ten whole-pair arguments, each a chain of
circle supports, monotonicity in the angle and fixed polynomial comparisons;
reflection followed by reversal of the cycle turns the target axes 2 and 3
into the source axes 4 and 1. The formal proof proves the 200 cases, one for
each ordered pair of charts (the core curve split into its side and its
corner), signs and source axis, as the problems of 25 pair tables
(Appendix L.7): on each of six halves of $\varphi \in [-1, 4]$ a tree splits
the box of the two tangents $b/a$, $b'/a'$ and the angle, and every leaf either
violates the gap of (11.4) or is covered by an affine row that proves the cost
greater than $\Gamma_{XY}$; 1,069 rows in all.

*Lean:
[`Eight.Arithmetic.FourType.fourTypeProblem`](../../SquaresInCircles/Eight/Arithmetic/FourTypeProblems.lean#L94),
[`Eight.Arithmetic.FourType.fourTypeTable_holds`](../../SquaresInCircles/Eight/Arithmetic/FourTypePairs.lean#L213),
[`Eight.Arithmetic.FourType.source_pair`](../../SquaresInCircles/Eight/Arithmetic/FourTypePairs.lean#L338),
[`Eight.four_type_cycle_budget`](../../SquaresInCircles/Eight/Frames.lean#L121).*

### Lemma 11.22 (closed walks)

For every sequence of types $X_0, \dots, X_6, X_7 = X_0$,

```math
\sum_{i=0}^6 \Gamma_{X_i X_{i+1}} \ge 7 \cdot 0.8833 + 0.0265 = \tfrac{3881}{625} .
```

*Proof.* Subtract $0.8833$ from every entry of $\Gamma$; the residuals are
nonnegative. The four triangles of distinct types have residual sums
$0.0611$, $0.0267$, $0.0265$, $0.0265$, all at least $p = 0.0265$. Every loop
$\Gamma_{XX}$ other than $\mathsf M$ has residual at least $p$; the loop at
$\mathsf M$ has residual $0.0079$, and every edge from $\mathsf M$ to another
type has residual at least $0.0093$. A closed walk of odd length on four
vertices contains a loop or a triangle as a closed subwalk, by the usual
argument for odd closed walks. If the walk is $\mathsf M$ seven times, its
residual is $7 \cdot 0.0079 > p$. If it uses the loop at $\mathsf M$ and some
other vertex, it enters and leaves $\mathsf M$, at a cost of at least
$0.0079 + 2 \cdot 0.0093 = p$. Otherwise it contains a loop of residual at
least $p$ or a triangle. The other residuals are nonnegative. $\square$

*Lean:
[`Eight.four_type_seven_walk`](../../SquaresInCircles/Eight/Frames.lean#L111),
[`Eight.four_type_seven_walk_numerator`](../../SquaresInCircles/Eight/Frames.lean#L94).*

![The four types C, L, M and H drawn as the corners of a square, joined by six edges and with a loop at each corner, each labelled with its entry of Gamma minus 0.8833: the loop at M has the smallest residual, 0.0079, the edges from M to C and to L have 0.0172, the edge from M to H 0.0093, the loops at C, L and H 0.0367, 0.0267 and 0.0266, and the edges from H to C and to L have residual 0. A closed walk of length seven, C, M, H, C, H, C, H and back to C, is highlighted along the edges from C to M, from M to H and from H to C](figures/11-eight/walks.svg)

*Figure 11.13.* Lemma 11.22. The residuals $\Gamma_{XY} - 0.8833$ on the
loops and edges of the four types; every closed walk of length seven picks up
at least $0.0265$ of them. The highlighted walk
$\mathsf{C}\mathsf{M}\mathsf{H}\mathsf{C}\mathsf{H}\mathsf{C}\mathsf{H}$
(back to $\mathsf C$) attains $0.0172 + 0.0093 = 0.0265$: the bound is the
least weight of a closed walk.

### Theorem 11.23 (frame concentration)

Let eight unit squares form a packing in a closed disk of squared radius
$q \le Q_0$ about $o$. Then the frames of the seven exterior squares,
taken modulo $\frac\pi2$, have real representatives $\theta_0, \dots, \theta_6$
that lie in an interval of length less than $\frac7{10}$.

*Proof.* By Theorem 11.10 the exterior squares, in the order of their centre
directions and with any witnesses, form a neighbour cycle; by
Proposition 11.15 there is a boundary cycle with the same frames, at the
level $\max(q, \frac52)$, and by Lemma 11.17 it can be expanded to the level
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
[`Eight.physical_cycle_width_bound`](../../SquaresInCircles/Eight/Frames.lean#L133),
[`Eight.physical_frame_lift_of_cost`](../../SquaresInCircles/Eight/Frames.lean#L434),
[`Eight.frameCost_concave`](../../SquaresInCircles/Eight/Frames.lean#L233),
[`Eight.frameCost_monotone`](../../SquaresInCircles/Eight/Frames.lean#L168),
[`Eight.frameCost_triangle`](../../SquaresInCircles/Eight/Frames.lean#L279),
[`Eight.frameCost_seven_tenths`](../../SquaresInCircles/Eight/Frames.lean#L309),
[`Eight.closed_walk_range_bound`](../../SquaresInCircles/Eight/Frames.lean#L186),
[`Eight.Arithmetic.two_pi_lt_710_over_113`](../../SquaresInCircles/Eight/Arithmetic/Taylor.lean#L33).*

The bound $\frac7{10}$ is about $40°$; in the optimal packing the range is
$t_* \approx 7.08°$ (Figure 11.14). The theorem says that the exterior squares
cannot turn far from one another; it does not yet say which quarter turns
separate their frames.

![The circle of frame directions modulo a quarter turn, of circumference pi/2, drawn as a circle: the frames of the five axis-parallel exterior squares A, B, T, D, E sit at one point, those of H and G at another point 7.08 degrees further; an arc of length 7/10 starting at the first point is marked as the bound of Theorem 11.23. Beside it, the graph of the frame charge chi on [0, pi/4], increasing and concave from 0 to (root 2 - 1)/2, with its chord and its value at t* marked](figures/11-eight/frames.svg)

*Figure 11.14.* Left: the frames of the exterior squares of Figure 11.1 on
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
[`Eight.QuarterLift`](../../SquaresInCircles/Eight/QuarterWords.lean#L156),
[`Eight.QuarterLift.word`](../../SquaresInCircles/Eight/QuarterWords.lean#L255),
[`Eight.QuarterLift.edge_identity`](../../SquaresInCircles/Eight/QuarterWords.lean#L172),
[`Eight.integerQuarterIncrement_sum`](../../SquaresInCircles/Eight/QuarterWords.lean#L149).*

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
[`Eight.QuarterLift.digit_range`](../../SquaresInCircles/Eight/QuarterWords.lean#L208),
[`Eight.QuarterLift.no_three_zero_increments`](../../SquaresInCircles/Eight/QuarterWords.lean#L235),
[`Eight.QuarterLift.word_admissible`](../../SquaresInCircles/Eight/QuarterWords.lean#L265),
[`Eight.quarter_word_complete_classification`](../../SquaresInCircles/Eight/QuarterWords.lean#L130).*

![Top: the seven quarter words of Lemma 11.25 drawn as necklaces of seven beads, the digits 0, 1 and 2 shown as white, light and dark beads, with the last one, 0101011, highlighted. Below: the exterior squares of the optimal packing with the canonical axis of each square drawn as an arrow near its centre direction; the arrows of H and G, A and B, T and D, and E point in the directions minus a quarter turn, 0, a quarter turn and a half turn from the frame of A, and each edge of the cycle is labelled with its digit 0 or 1](figures/11-eight/words.svg)

*Figure 11.15.* Top: the seven words of Lemma 11.25 as necklaces (white 0,
light 1, dark 2). Below: the word of Figure 11.1. The canonical axes
(arrows) of $H, G, A, B, T, D, E$ are $-1, -1, 0, 0, 1, 1, 2$ quarter turns
ahead of that of $A$, up to the small tilt of $H$ and $G$, so the word,
starting at $H$, is $0101011$.

### Proposition 11.26 (only the word 0101011; finite tables)

In a boundary cycle at a level $q \le Q_0$ whose frames lie in an interval of
length less than $\frac7{10}$, the quarter word is $0101011$ up to the
symmetries of the cycle.

*Proof.* Expand the cycle to the level $Q_0$ (Lemma 11.17); its word does not
change. Each of the six other words of Lemma 11.25 is excluded by a whole-cycle
bound: markers $\ell_i$ of the states, one per square, and lower bounds
$\gamma_i$ for the costs $\varphi_i + \ell_i - \ell_{i+1}$ of the seven pairs,
valid for every feasible retained axis (Lemma 11.19), all states on
$\mathcal O$ and $\mathcal C$, all signs and all angles allowed by (11.4) and
Definition 11.24, with $\sum_i\gamma_i > 2\pi$, which contradicts (11.6).

*The four words with a 2.* One pair of markers serves all four words:

```math
L_{\mathcal O}(a, b) = -\tfrac9{100} + \tfrac{13}{200}a + \tfrac{203}{200}b, \qquad L_{\mathcal C}(a, b) = \tfrac{73}{10}\left(\tfrac7{12} - a\right) + \tfrac{291}{250}b ,
```

$\ell_i = \sigma_i L_{\mathcal O}$ or $\sigma_i L_{\mathcal C}$ as $S_i$ is on
$\mathcal O$ or on $\mathcal C$. The cost of a pair exceeds $\frac{391}{400}$,
$\frac{157}{200}$, $\frac{163}{200}$ when its digit is 0, 1, 2.
Count occupied positions, those with a nonzero digit. Every cyclic triple
contains an occupied position; summing over the seven triples counts each
occupied position three times, so there are at least three. The total digit
sum is four, and a digit 2 contributes one extra beyond being occupied.
Thus a word with a 2 has exactly three occupied positions and exactly one 2:
one 2, two 1s and four 0s. Its costs therefore add up to more than
$4 \cdot \frac{391}{400} + 2 \cdot \frac{157}{200} + \frac{163}{200} = \frac{1259}{200}$,
which exceeds $\frac{44}7 > 2\pi$ by $\frac{13}{1400}$.

*The word 0010111.* Markers that depend on the role of the square in the word
give costs above $\frac{359}{400}$ on the third edge and above
$\frac{17953}{20000}$ on the six others, in all more than
$\frac{31417}{5000}$, which exceeds $\frac{710}{113}$ by $\frac{121}{565000}$.

*The word 0011011.* Markers quadratic in the state give costs above
$\frac{17953}{20000}$ on every edge, in all more than
$\frac{125671}{20000}$, which exceeds $\frac{710}{113}$ by
$\frac{823}{2260000}$. $\square$

*Lean:
[`Eight.double_word_cost_numerator`](../../SquaresInCircles/Eight/QuarterWords.lean#L296),
[`Eight.WordGeometry.no_double`](../../SquaresInCircles/Eight/WordGeometry.lean#L506),
[`Eight.WordGeometry.wrong_word_impossible`](../../SquaresInCircles/Eight/WordGeometry.lean#L602),
[`Eight.WordGeometry.six_exclusions`](../../SquaresInCircles/Eight/WordGeometry.lean#L657),
[`Eight.quarter_word_candidate`](../../SquaresInCircles/Eight/WordGeometry.lean#L686),
[`Eight.candidate_word_after_six_exclusions`](../../SquaresInCircles/Eight/QuarterWords.lean#L357),
[`Eight.WordGeometry.commonPairProblem`](../../SquaresInCircles/Eight/Arithmetic/WordProblems.lean#L190),
[`Eight.WordGeometry.wrongPairProblem`](../../SquaresInCircles/Eight/Arithmetic/WordProblems.lean#L197),
[`Eight.WordGeometry.word_pair`](../../SquaresInCircles/Eight/WordGeometry.lean#L389).*

The three cost bounds are finite tables of continuous inequalities, one for
each digit or edge, each pair of radial curves, each pair of signs and each
retained axis. In the hand proof they are whole-pair arguments of the kind of
§11.8: the common table is three lemmas, one for each digit; the exclusion of
$0010111$ assembles 304 cases of retained axes, closing its hardest edge with
six neighbourhoods of contacts and 140 scalar regimes; and that of $0011011$
assembles 76 cases of radial curves and signs (39 up to reflection), again
with 304 cases of axes. The formal proof proves the same inequalities as the
problems of pair tables (Appendix L.7), with the core curve split into side and
corner: $3 \cdot 9 \cdot 4 \cdot 4 = 432$ problems for the common table, and for
each of the two words 684 problems, 19 combinations of an edge and a pair of
signs times 9 pairs of curves times 4 axes; 1,800 problems in all, each on the
two halves of the frame difference $|d| \le \frac7{10}$, with 8,375 rows. A leaf
of a tree is closed either by the gap of (11.4) or by a row proving the cost
bound; the quadratic markers of $0011011$ are bounded on each arc by affine
labels. The signs are not all free
in the two words. On an edge with digit 0, (11.8) gives
$\delta_i = d_i + \alpha_i - \alpha_{i+1}$, so $\alpha_i \le 0 \le \alpha_{i+1}$
would make $\delta_i < \frac7{10}$; and both words begin with two edges of
digit 0, along which $\alpha_0 - \alpha_2 > 2 \cdot \frac{19}{25} - \frac7{10} = \frac{41}{50}$,
so the first square has $\alpha_0 > 0$ and the third $\alpha_2 < 0$. This
leaves 19 combinations of an edge and a pair of signs.

## 11.7 Candidate coordinates and the tangent exclusions

From now on the word is $0101011$, and the proof works with the roles of the
squares in Figure 11.1.

### Definition 11.27 (candidate coordinates)

Let $S_0, \dots, S_6$ be a boundary cycle with the quarter word $0101011$,
indexed so that $k = (0, 1, 0, 1, 0, 1, 1)$, and name the squares

```math
(S_0, \dots, S_6) = (H, G, A, B, T, D, E) .
```

Relative to the canonical frame of $A$, the canonical frames are
$-1, -1, 0, 0, 1, 1, 2$ quarter turns ahead. The five *aligned* edges are
$H \to G$, $A \to B$, $B \to T$, $T \to D$, $D \to E$ (indices
$I = \lbrace 0, 2, 3, 4, 5\rbrace$), and the two *mixed* edges are $G \to A$ and
$E \to H$. Take the real frame representatives with $\theta_A = 0$, and call
$t = \theta_G$ the *tilt* and

```math
\Delta = \sum_{i \in I} |d_i| = |\theta_G - \theta_H| + |\theta_B| + |\theta_T - \theta_B| + |\theta_D - \theta_T| + |\theta_E - \theta_D|
```

the *mismatch*. Then $\varphi_{G \to A} = \frac\pi2 - t$ and
$\varphi_{E \to H} = \frac\pi2 + t - \sum_{i \in I} d_i$. In the optimal
packing $\Delta = 0$ and $t = t_*$.

*Lean:
[`Eight.Candidate.word`](../../SquaresInCircles/Eight/Candidate/Model.lean#L36),
[`Eight.Candidate.offsets`](../../SquaresInCircles/Eight/Candidate/Model.lean#L37),
[`Eight.Candidate.charged`](../../SquaresInCircles/Eight/Candidate/Model.lean#L38),
[`Eight.Candidate.mixedEdges`](../../SquaresInCircles/Eight/Candidate/Model.lean#L41),
[`Eight.Candidate.delta`](../../SquaresInCircles/Eight/Candidate/Model.lean#L43),
[`Eight.Candidate.phi`](../../SquaresInCircles/Eight/Candidate/Model.lean#L44),
[`Eight.Candidate.mismatch`](../../SquaresInCircles/Eight/Candidate/Model.lean#L45),
[`Eight.Candidate.tilt`](../../SquaresInCircles/Eight/Candidate/Model.lean#L46),
[`Eight.Candidate.Frame`](../../SquaresInCircles/Eight/Candidate/Model.lean#L90).*

### Lemma 11.28 (normalization)

Reflecting the plane in a line through $o$ and renumbering the squares by
$i \mapsto 5 - i$ modulo 7 turns a boundary cycle with the word $0101011$ into
another one, with the roles $(D, T, B, A, G, H, E)$ in place of
$(H, G, A, B, T, D, E)$ and the same word; it changes the sign of every
signed tangent and fixes $E$. So we may assume $\tau_E \le 0$.

*Proof.* The reflection keeps containment, the core, the frames up to
reflection, the separations and the gaps, and reverses the cyclic order, which
the renumbering restores. Under it the edge $i$ becomes the edge $4 - i$, and
$k_{4 - i} = k_i$ for the word $0101011$ read from $H$. A reflection exchanges
the two sides of each centre direction, so it changes the sign $\sigma$ of
every square and keeps $(a, b)$. The square $S_6 = E$ is sent to
$S_{5 - 6} = S_6$. $\square$

*Lean:
[`Eight.boundary_candidate_normalization`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L464),
[`Eight.candidate_word_mirror`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L372),
[`Eight.CycleAction.candidateMirror`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L346),
[`Eight.CycleAction.candidateMirror_E`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L357),
[`Eight.Candidate.EHalf`](../../SquaresInCircles/Eight/Candidate/Model.lean#L121).*

### Proposition 11.29 (six tangent exclusions; six affine-arc tables)

Let a boundary cycle at the level $Q_1$ have the word $0101011$, frames in an
interval of length less than $\frac7{10}$, and $\tau_E \le 0$. Then

```math
-\tfrac45 < \tau_G < -\tfrac1{20}, \qquad \tfrac1{20} < \tau_T < \tfrac45, \qquad \tau_H > \tfrac12, \qquad \tau_D < -\tfrac12 . \tag{11.9}
```

*Proof.* Each of the six closed domains of Table 11.1 is excluded, in the
order of the table, by a whole-cycle bound as in Proposition 11.26: the table
gives markers, one per arc of states, and for every pair a lower bound
$\gamma_i$ of the cost $\varphi_i + \ell_i - \ell_{i+1}$ for every feasible
retained axis, with $\sum_i\gamma_i > \frac{710}{113} > 2\pi$, against (11.6).
The rows of each table and their meaning are explained in §11.8. $\square$

| excluded domain | earlier hypotheses | rows | arcs | $\sum_i \gamma_i$ | reserve over $\frac{710}{113}$ |
| --- | --- | --: | --: | :-: | :-: |
| $\tau_G \le -\frac45$ | $\tau_E \le 0$ | 9,087 | 114 | $\frac{62839}{10000}$ | $\frac{807}{1130000}$ |
| $\tau_G \ge -\frac1{20}$ | $\tau_E \le 0$ | 9,796 | 122 | $\frac{62839}{10000}$ | $\frac{807}{1130000}$ |
| $\tau_T \ge \frac45$ | $\tau_G \in [-\frac45, -\frac1{20}]$, $\tau_E \le 0$ | 7,078 | 102 | $\frac{62839}{10000}$ | $\frac{807}{1130000}$ |
| $\tau_T \le \frac1{20}$ | $\tau_G \in [-\frac45, -\frac1{20}]$, $\tau_E \le 0$ | 49,971 | 303 | $\frac{3927}{625}$ | $\frac1{70625}$ |
| $\tau_H \le \frac12$ | $\tau_G$, $\tau_T$ as in (11.9), $\tau_E \le 0$ | 48,050 | 279 | $\frac{62839}{10000}$ | $\frac{807}{1130000}$ |
| $\tau_D \ge -\frac12$ | $\tau_G$, $\tau_T$ as in (11.9), $\tau_E \le 0$ | 24,197 | 199 | $\frac{125671}{20000}$ | $\frac{823}{2260000}$ |

*Table 11.1.* The six tangent exclusions at the level $Q_1$. Each table
covers both radial curves at every square, all four margins of (11.5) on
every edge and the whole range of angles allowed by (11.4) and
Theorem 11.23; no separating axis is chosen in advance.

*Lean:
[`Eight.Candidate.Tables.g_lower_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L67),
[`Eight.Candidate.Tables.g_upper_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L116),
[`Eight.Candidate.Tables.t_upper_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L217),
[`Eight.Candidate.Tables.t_lower_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L166),
[`Eight.Candidate.Tables.h_lower_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L326),
[`Eight.Candidate.Tables.d_upper_excluded`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L381),
[`Eight.Candidate.Tables.g_cut`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L435),
[`Eight.Candidate.Tables.t_cut`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L441),
[`Eight.Candidate.Tables.hd_cut`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L447).*

![The exterior squares of the optimal packing, each with a shaded fan of the centre directions that its signed tangent allows after Proposition 11.29, drawn about its canonical axis: narrow fans on one side for G and T, the outer parts of the fans for H and D, the half fan on the side of negative tangents for E, and full fans for A and B, which share their axis; the actual centre direction of each square lies in its fan](figures/11-eight/tangents.svg)

*Figure 11.16.* The bounds (11.9) in the optimal packing. For each exterior
square, the shaded fan is the set of centre directions $\beta = \theta - \alpha$
allowed by its signed tangent, about its canonical axis (arrow); the centre
directions (dots) lie inside. The fans of $A$, $B$ and $E$ are not restricted
at this stage, beyond $\tau_E \le 0$.

## 11.8 What an affine-arc table row proves

The ten largest tables of the proof, the six of Table 11.1 and the four of
the mismatch chain (§11.9), are *affine-arc tables*. This section describes
them and the continuous argument that makes them a proof; the details are in
[Appendix L](appendix-l.md).

### Definition 11.30 (arcs, rows and covers)

An *affine-arc table* at a level $Q$ consists of the following data, all
rational.

1. *Arcs.* For each role and each sign, a finite list of closed arcs of the
   radial curves $\mathcal O_Q$ and $\mathcal C$, given by intervals of the
   unsigned tangent $b/a$ with rational ends; the core curve is cut at
   $b/a = \frac67$ into its side and its corner. Each arc carries an affine
   *label* $L(a, b) = c + p\,a + q\,b$.
2. *Rows.* A row names an edge $i$, a source arc and a target arc, an angle
   interval $\varphi \in k_i\frac\pi2 \pm [u_0, u_1]$ with
   $0 \le u_0 \le u_1 \le \frac7{10}$, one of the four margins $M_j$ of
   (11.5), a multiplier $\lambda \ge 0$, and a rule for the support of the
   target arc (§L.2).
3. *Covers.* For each role and sign the arcs cover the curve; for each edge,
   pair of arcs and margin, the angle intervals of the rows form a closed
   chain covering the range of $\varphi$ allowed by (11.4), by
   Theorem 11.23 and by any earlier bound on the mismatch.
4. *Constants.* The edge constants $\gamma_i$ and the charge $\beta_i \ge 0$,
   zero for the tangent tables and on the mixed edges.

A row is *valid* if the following inequality holds for all states $(a, b)$
on the source arc and $(a', b')$ on the target arc and all $\varphi$ in its
angle interval:

```math
\varphi - \beta_i\,\chi(\varphi) + L_s(a, b) - L_t(a', b') - \gamma_i - \lambda\,M_j > 0 . \tag{11.10}
```

*Lean:
[`Eight.Arithmetic.ArcData`](../../SquaresInCircles/Eight/Arithmetic/AffineTableData.lean#L35),
[`Eight.Arithmetic.AffineTableRow`](../../SquaresInCircles/Eight/Arithmetic/AffineTableData.lean#L76),
[`Eight.Arithmetic.AffineTableRow.Claim`](../../SquaresInCircles/Eight/Arithmetic/AffineTableData.lean#L107),
[`Eight.Arithmetic.AffineTableMeta`](../../SquaresInCircles/Eight/Arithmetic/AffineTableData.lean#L63),
[`Eight.Arithmetic.AffineCover`](../../SquaresInCircles/Eight/Arithmetic/AffineCoverage.lean#L143),
[`Eight.Arithmetic.chargedCost`](../../SquaresInCircles/Eight/Arithmetic/AffineArc.lean#L87).*

Where the margin $M_j$ is nonnegative, that is, where the axis $j$
separates, (11.10) gives the charged cost bound
$\varphi - \beta_i\chi(\varphi) + L_s - L_t > \gamma_i$. Where it is negative,
the axis does not separate and (11.10) holds trivially once $\lambda$ is
large; the multiplier lets a single smooth inequality cover both regions.

### Proposition 11.31 (rows and tables)

1. *A row is checked by finitely many rational comparisons.* Subtracting
   $\lambda M_j$ separates the source and the target: the left side of
   (11.10) is a constant plus a linear function of $(a, b)$ with fixed
   coefficients plus a linear function of $(a', b')$ whose coefficients are
   trigonometric in $\varphi$. Its minimum over a source arc is bounded below
   by an endpoint value or by the support of the whole circle, its minimum
   over the target arc likewise, with one radical removed by a fixed
   polynomial majorant; then sine and cosine are replaced by their Taylor
   polynomials with interval remainders, and the resulting polynomial in the
   angle is shown positive by the signs of its coefficients in a Bernstein
   basis. Every step is a valid inequality, so positive coefficients prove
   (11.10) on the whole row.
2. *A valid table gives a cyclic bound.* Let every row of an affine-arc table
   be valid and its covers complete. Then for every boundary cycle at the
   level $Q$ whose states, signs and angles lie in the declared domains,

   ```math
   2\pi > \sum_{i=0}^6 \gamma_i + \sum_{i=0}^6 \beta_i\,\chi(\varphi_i) . \tag{11.11}
   ```

The proof of (1) is given in [Appendix L](appendix-l.md). For (2), give each
square one arc containing its state, and so one label; on each edge choose a
feasible retained axis $j$ (Lemma 11.19). The covers provide a row for the
edge, the two arcs and $j$, whose angle interval contains $\varphi_i$, and as
$M_j \ge 0$ the row gives
$\varphi_i - \beta_i\chi(\varphi_i) + \ell_i - \ell_{i+1} > \gamma_i$, with
the labels as markers. Summing and using (11.6) gives (11.11).

*Lean:
[`Eight.Arithmetic.CoreRow.sound_of_positive`](../../SquaresInCircles/Eight/Arithmetic/CoreRow.lean#L79),
[`Eight.Arithmetic.PreparedRow.claim_of_positive`](../../SquaresInCircles/Eight/Arithmetic/PreparedRow.lean#L136),
[`Eight.Arithmetic.checkRow_claim`](../../SquaresInCircles/Eight/Arithmetic/RowCheck.lean#L1277),
[`Eight.Arithmetic.coverBlocks_sound`](../../SquaresInCircles/Eight/Arithmetic/RowCover.lean#L532),
[`Eight.Arithmetic.StateChains.covers`](../../SquaresInCircles/Eight/Arithmetic/StateCoverage.lean#L159),
[`Eight.Arithmetic.ClosedChain.covers`](../../SquaresInCircles/Eight/Arithmetic/ClosedCover.lean#L40),
[`Eight.Candidate.ChargedBound.cyclic`](../../SquaresInCircles/Eight/Candidate/Model.lean#L163).*

Nothing in a row is a sample: each row is a statement about a product of two
whole arcs and a whole interval of angles, its arithmetic is a fixed list of
rational coefficients, and the covers are checked separately from the rows,
by comparing rational endpoints. The arcs, rows and covers of the ten tables
are listed in Table 11.2. In the formal proof each table is a data file read
by Lean; the rational root brackets of the arc endpoints, the arctangent
bounds of the angle endpoints and the coverage chains are recomputed and
checked in Lean, and each row's Bernstein coefficients are checked as an
identity of rational polynomials.

| table | proves | arcs | rows | $\beta$ | $\gamma_i$ |
| --- | --- | --: | --: | :-: | --- |
| $\tau_G \le -\frac45$ | excluded | 114 | 9,087 | 0 | Table 11.1 |
| $\tau_G \ge -\frac1{20}$ | excluded | 122 | 9,796 | 0 | Table 11.1 |
| $\tau_T \ge \frac45$ | excluded | 102 | 7,078 | 0 | Table 11.1 |
| $\tau_T \le \frac1{20}$ | excluded | 303 | 49,971 | 0 | Table 11.1 |
| $\tau_H \le \frac12$ | excluded | 279 | 48,050 | 0 | Table 11.1 |
| $\tau_D \ge -\frac12$ | excluded | 199 | 24,197 | 0 | Table 11.1 |
| coarse mismatch | $\Delta < \frac{13}{50}$ | 462 | 129,031 | $\frac{99}{5000}$ | $0.89727$ |
| M1 | $\Delta \le \frac{13}{50} \Rightarrow \Delta < \frac1{10}$ | 401 | 131,255 | $\frac1{400}$ | $0.897582$ |
| intermediate | $\Delta \le \frac1{10} \Rightarrow \Delta < \frac3{200}$ | 335 | 107,196 | $\frac1{200}$ | (11.13) |
| M2 | $\Delta \le \frac3{200} \Rightarrow \Delta < \frac1{1000}$ | 456 | 144,709 | $\frac1{20}$ | (11.14) |
| total | | 2,773 | 660,370 | | |

*Table 11.2.* The ten affine-arc tables. The six tangent tables are at the
level $Q_1$ without a charge; the four mismatch tables, also at $Q_1$, charge
the five aligned edges with $\beta$.

![Two panels for one row of the table that excludes tau_G at most -4/5, on the edge from H to G. Left: the (a, b)-plane with the region between the core curve and the outer curve shaded; the source arc of H, the states of the outer curve with b/a between 0 and 1/8, and the target arc of G, those with b/a between 7/8 and 1, are drawn thick. Right: against the angle phi = u from 0 to 0.7, the least value over the two arcs of the left side of (11.10) for the margin M1 with the multiplier about 7.57, a positive convex curve whose least value, about 0.072, is near u = 0.55, and the lower bound of the support rules, dashed, which coincides with it to drawing accuracy](figures/11-eight/row.svg)

*Figure 11.17.* One row of the table that excludes $\tau_G \le -\frac45$: the
edge $H \to G$, the source arc of $H$, the states of $\mathcal O_{Q_1}$ with
$b/a \in [0, \frac18]$, and the target arc of $G$, those with
$b/a \in [\frac78, 1]$, both with the sign $-1$ (left, thick); the margin
$M_1$, the angles $0 \le \varphi \le \frac7{10}$ and the multiplier
$\lambda \approx 7.57$. Right: the least value over the two arcs of the left
side of (11.10) (solid) and the bound of Proposition 11.31 (1), with the
upper-endpoint rule of Lemma L.1 (3) for the target (dashed), coincide to
drawing accuracy; both stay above $0.072$.

![For the same pair of arcs and the edge from H to G, the four margins drawn as four horizontal bars over the angles from -0.0254 to 0.7: each bar is a chain of closed angle intervals, one for each row, consecutive intervals meeting at common endpoints, labelled by the support rule the row uses for the target arc, and each chain covers the grey band of angles allowed by the gap and frame bounds. The bars of margins 1, 2 and 4 have two rows each, one for the negative angles and one for the rest; the bar of margin 3 has nine](figures/11-eight/chains.svg)

*Figure 11.18.* The angle chains of the table of Figure 11.17 for the same
pair of arcs: for each of the four margins, the rows' closed intervals
(alternately shaded) meet at common rational endpoints and cover the whole
range $-0.0254 \le \varphi \le \frac7{10}$ allowed by the gap and frame bounds
(grey band). Each interval is labelled by the rule of Lemma L.1 that its row
uses for the target arc: both endpoints (e), the lower or the upper endpoint
(l, u), or the circle (c). These are all 15 rows of the pair.

## 11.9 The mismatch chain

The tangent exclusions leave the frames free within the bound $\frac7{10}$
of Theorem 11.23. Four charged tables now shrink the mismatch $\Delta$, the
total turn between the frames of aligned neighbours, in four steps. Each table
proves a cyclic bound (11.11) with a positive charge $\beta$ on the aligned
edges, and a lemma about the frame charge converts it into a bound on
$\Delta$.

### Lemma 11.32 (contraction)

Let a boundary cycle with the word $0101011$ satisfy (11.11) with
$\beta_i = \beta > 0$ on the aligned edges and $\beta_i = 0$ on the mixed ones,
and let every aligned $|d_i|$ be at most $\frac7{10}$.

1. $\chi(\varphi_i) = g(|d_i|)$ on every aligned edge, where
   $g(x) = \frac12(\cos x + \sin x - 1)$ is increasing and concave on
   $[0, \frac7{10}]$, and
   $g(x) \ge P_7(x) = \frac x2 - \frac{x^2}4 - \frac{x^3}{12} + \frac{x^4}{48} + \frac{x^5}{240} - \frac{x^6}{1440} - \frac{x^7}{10080}$
   for $x \ge 0$.
2. If $\sum_i\gamma_i + \beta\kappa\Delta_0 \ge \frac{710}{113}$ for numbers
   $\kappa \le g(\frac7{10})/\frac7{10}$ and $\Delta_0 > 0$, then
   $\Delta < \Delta_0$.
3. If $\Delta \le \frac7{10}$ and $\sum_i\gamma_i + \beta\,g(\Delta_0) \ge \frac{710}{113}$
   for a number $0 < \Delta_0 \le \frac7{10}$, then $\Delta < \Delta_0$.

*Proof.* (1) On an aligned edge $\varphi_i = k_i\frac\pi2 + d_i$, and $\chi$
has the period $\frac\pi2$ and is even. On $[0, \frac\pi4]$,
$g' = \frac12(\cos x - \sin x) \ge 0$ and $g'' = -\frac12(\sin x + \cos x) < 0$.
The bound $g \ge P_7$ is the sum of the lower Taylor bounds
$\cos x \ge 1 - \frac{x^2}2 + \frac{x^4}{24} - \frac{x^6}{720}$ and
$\sin x \ge x - \frac{x^3}6 + \frac{x^5}{120} - \frac{x^7}{5040}$. (2) By
concavity and $g(0) = 0$, $g(x) \ge \kappa x$ on $[0, \frac7{10}]$, so
$\sum_{i \in I}\chi(\varphi_i) \ge \kappa\Delta$; if $\Delta \ge \Delta_0$,
(11.11) would give $2\pi > \frac{710}{113}$. (3) A concave function with
$g(0) = 0$ is subadditive, so $\sum_{i \in I} g(|d_i|) \ge g(\Delta)$, and if
$\Delta \ge \Delta_0$ this is at least $g(\Delta_0)$. $\square$

*Lean:
[`Eight.Candidate.h_monotone`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L37),
[`Eight.Candidate.h_concave`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L44),
[`Eight.Candidate.hLower7_le`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L85),
[`Eight.Candidate.h_cubic_lower`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L93),
[`Eight.Candidate.hSum_ge_chord`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L107),
[`Eight.Candidate.hSum_ge_h_mismatch`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L115),
[`Eight.Candidate.mismatch_contract`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L129).*

### Lemma 11.33 (owners and signs at small mismatch)

Let a boundary cycle at a level $q \le Q_0$ have the word $0101011$ and
frames in an interval of length less than $\frac7{10}$.

1. Every exterior square has $0.55875 < a < 1.415$ and $b < 0.9$.
2. If $\Delta \le \frac25$, then on the three edges $H \to G$, $A \to B$,
   $T \to D$, whose digit is 0, the margins $M_2$ and $M_4$ are negative: only
   the axes 1 and 3 can separate.
3. If $\Delta \le \frac1{10}$, then
   $\tau_H > 0 > \tau_G$, $\tau_A > 0 > \tau_B$ and $\tau_T > 0 > \tau_D$.

*Proof.* (1) is (11.3). (2) On a zero edge $\varphi = d$ with
$x = |d| \le \frac25$, and as $b \le a$, $b' \le a'$ and
$\cos x - \sin x > 0$, both $M_2$ and $M_4$ are at most

```math
1.415 - 0.55875(\cos x - \sin x) - \tfrac12(1 + \sin x + \cos x) = 0.915 - 1.05875\cos x + 0.05875\sin x \le -\tfrac{711}{20000}
```

by $\cos x \ge 1 - \frac{x^2}2 \ge 0.92$ and $\sin x \le x \le 0.4$.
(3) Now $x \le \frac1{10}$ and only $M_1$ and $M_3$ remain. If the source has
$\sigma b \le 0$, then
$M_1 \le 1.415\sin x + 0.9\cos x - \tau \le 0.915 \cdot 0.1 + 0.4 - 0.5 < 0$
and $M_3 \le 0.9 + 1.415\sin x - \tau \le 0.4 + 0.0915 - \frac12(1 - \frac{0.01}2) < 0$;
if the target has $\sigma'b' \ge 0$, the same two bounds hold with the roles
of $M_1$ and $M_3$ exchanged. So a separating zero edge has
$\tau_{\mathrm{source}} > 0 > \tau_{\mathrm{target}}$. $\square$

*Lean:
[`Eight.Candidate.canonical_bounds`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L51),
[`Eight.Candidate.primary_margin_negative`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L129),
[`Eight.Candidate.zero_edge_primary_excluded`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L144),
[`Eight.Candidate.zero_owners_of_mismatch`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L173),
[`Eight.Candidate.secondary_margins_source_nonpos`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L186),
[`Eight.Candidate.secondary_margins_target_nonneg`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L204),
[`Eight.Candidate.zero_edge_signs`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L222),
[`Eight.Candidate.signs_of_mismatch`](../../SquaresInCircles/Eight/Candidate/Geometry.lean#L258).*

### Proposition 11.34 (the mismatch chain; four affine-arc tables)

Let a boundary cycle at the level $Q_1$ have the word $0101011$, frames in an
interval of length less than $\frac7{10}$, $\tau_E \le 0$ and the bounds
(11.9). Then

```math
\Delta < \tfrac{13}{50} \ \Longrightarrow\ \Delta < \tfrac1{10} \ \Longrightarrow\ \Delta < \tfrac3{200} \ \Longrightarrow\ \Delta < \tfrac1{1000}, \tag{11.12}
```

and the first bound holds. More precisely, the following four steps are
proved in this order.

1. *Coarse step.* With $|d_i| < \frac7{10}$ only, the coarse table (462 arcs,
   129,031 rows, covering 121,808 required angle chains) gives (11.11) with
   $\beta = \frac{99}{5000}$ and every $\gamma_i = 0.89727$. With
   $\kappa = \frac{29}{100}$, Lemma 11.32 (2) and

   ```math
   7 \cdot 0.89727 + \tfrac{99}{5000} \cdot \tfrac{29}{100} \cdot \tfrac25 - \tfrac{710}{113} = \tfrac{271}{282500000} > 0
   ```

   give $\Delta < \frac25$. The same rows prove the cost bounds with the seven
   constants raised by $(15, 13, 18, 12, 15, 23, 6) \cdot 10^{-6}$, in all by
   $\frac{51}{500000}$, since each raise is below the least reserve of the rows
   of its edge; then Lemma 11.32 (3) and

   ```math
   7 \cdot 0.89727 + \tfrac{51}{500000} + \tfrac{99}{5000}\,P_7\!\left(\tfrac{13}{50}\right) - \tfrac{710}{113} = \tfrac{9154605884982919}{494375000000000000000} > 0
   ```

   give $\Delta < \frac{13}{50}$.
2. *M1.* Assume $\Delta \le \frac{13}{50}$ and the closed ranges
   $\tau_H \in [\frac12, 1]$, $\tau_G \in [-\frac45, -\frac1{20}]$,
   $\tau_T \in [\frac1{20}, \frac45]$, $\tau_D \in [-1, -\frac12]$,
   $\tau_E \in [-1, 0]$, with $\tau_A$, $\tau_B$ free, the aligned $d_i$ in
   $[-\frac{13}{50}, \frac{13}{50}]$ and the mixed ones in
   $[-\frac7{10}, \frac7{10}]$, all four margins on every edge. The table M1
   (401 arcs, 131,255 rows, 123,168 required chains) gives (11.11) with
   $\beta = \frac1{400}$ and every $\gamma_i = 0.897582$, and

   ```math
   7 \cdot 0.897582 + \tfrac1{400}\left(\tfrac{0.1}2 - \tfrac{0.1^2}4 - \tfrac{0.1^3}{12}\right) - \tfrac{710}{113} = \tfrac{18173}{2712000000} > 0
   ```

   gives $\Delta < \frac1{10}$ by Lemma 11.32 (3), the cubic being a lower
   bound for $g$.
3. *Intermediate step.* Now Lemma 11.33 (3) gives the signs. Assume
   $\Delta \le \frac1{10}$, $\tau_H, \tau_A \in [0, 1]$,
   $\tau_G \in [-\frac45, -\frac1{20}]$, $\tau_B, \tau_D, \tau_E \in [-1, 0]$,
   $\tau_T \in [\frac1{20}, \frac45]$, all four margins and the mixed angles in
   $[-\frac7{10}, \frac7{10}]$. The intermediate table (335 arcs, 107,196 rows,
   101,280 chains) gives (11.11) with $\beta = \frac1{200}$ and

   ```math
   \gamma = (0.8975928,\ 0.8975928,\ 0.8975928,\ 0.8975928,\ 0.8975928,\ 0.89759275,\ 0.8975917), \qquad \textstyle\sum_i \gamma_i = \tfrac{125662969}{20000000}, \tag{11.13}
   ```

   and $g(\frac3{200}) > \frac{238191}{32000000}$, $2\pi < 6.28318531$ and
   $\frac{125662969}{20000000} + \frac1{200} \cdot \frac{238191}{32000000} - 6.28318531 = \frac{2287}{6400000000} > 0$
   give $\Delta < \frac3{200}$.
4. *M2.* Assume $\Delta \le \frac3{200}$, the ranges of step 2 with
   $\tau_A \in [0, 1]$ and $\tau_B \in [-1, 0]$, only the axes 1 and 3 on
   $H \to G$, $A \to B$, $T \to D$ (Lemma 11.33 (2)) and only the axes 3 and 4
   on $B \to T$, $D \to E$ (Proposition 11.35 (1)), and all four margins on
   the two mixed edges, whose angles are not restricted by $\Delta$. The
   table M2 (456 arcs, 144,709 rows, 129,368 chains) gives (11.11) with
   $\beta = \frac1{20}$ and

   ```math
   \gamma = (0.897595,\ 0.897595,\ 0.897595,\ 0.897595,\ 0.897595,\ 0.897595,\ 0.8975925), \qquad \textstyle\sum_i \gamma_i = \tfrac{502653}{80000}, \tag{11.14}
   ```

   and $g(\frac1{1000}) > \frac{5996999}{12000000000}$ and
   $\frac{502653}{80000} + \frac1{20} \cdot \frac{5996999}{12000000000} - 6.28318531 = \frac{522599}{240000000000} > 0$
   give $\Delta < \frac1{1000}$.

*Proof.* Each step is Proposition 11.31 (2) for its table, whose declared
domain contains the cycle by the hypotheses and the earlier steps, followed by
Lemma 11.32 and the displayed rational comparison; the bounds
$2\pi < \frac{710}{113}$ and $2\pi < 6.28318531$ follow from Machin's formula
$\frac\pi4 = 4\arctan\frac15 - \arctan\frac1{239}$ and the alternating series
of the arctangent. No step uses a conclusion it is meant to prove: the owners
of step 4 come from Lemma 11.33 at $\Delta \le \frac25$ and from
Proposition 11.35 at $\Delta \le \frac3{200}$, both available after step 3.
$\square$

*Lean:
[`Eight.Candidate.coarse_first_contraction`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L159),
[`Eight.Candidate.coarse_enhanced_contraction`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L169),
[`Eight.Candidate.contraction_026_to_01`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L180),
[`Eight.Candidate.contraction_01_to_015`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L188),
[`Eight.Candidate.contraction_015_to_001`](../../SquaresInCircles/Eight/Candidate/Mismatch.lean#L200),
[`Eight.Candidate.Tables.coarse_bound`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L455),
[`Eight.Candidate.Tables.enhanced_bound`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L709),
[`Eight.Candidate.Tables.middle_bound`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L475),
[`Eight.Candidate.Tables.intermediate_bound`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L547),
[`Eight.Candidate.Tables.final_bound`](../../SquaresInCircles/Eight/Generated/AffineBudgets.lean#L624),
[`Eight.Arithmetic.pi_hand_enclosure`](../../SquaresInCircles/Eight/Arithmetic/Taylor.lean#L28).*

![The contraction steps as graphs against the mismatch Delta on a logarithmic axis from 10 to the minus 4 to 1: for each step, its charge term, beta times its lower bound for the frame charge, divided by the deficit of its constants, the bound on 2 pi minus the sum of the gamma_i. The first bound of the coarse step uses the chord 0.29 Delta (dashed curve), the others g(Delta). Each curve increases and passes the level 1, a dashed horizontal line, just before the threshold of its step, 2/5, 13/50, 1/10, 3/200 and 1/1000, where a dot marks its value above 1](figures/11-eight/mismatch.svg)

*Figure 11.19.* The mismatch chain. For each step, the charge term
$\beta\,g(\Delta)$ (for the first bound of the coarse step the chord
$\beta\kappa\Delta$, dashed) divided by the deficit of the constants,
$\frac{710}{113} - \sum_i\gamma_i$ or $6.28318531 - \sum_i\gamma_i$, against
$\Delta$ on a logarithmic axis. Where the ratio exceeds 1 the cyclic bound
(11.11) fails, so such a mismatch is impossible; at the thresholds
$\frac25$, $\frac{13}{50}$, $\frac1{10}$, $\frac3{200}$ and $\frac1{1000}$
(dots) the ratio already exceeds 1. The proof uses the polynomial lower bounds
of Lemma 11.32 (1) in place of $g$ at the thresholds.

## 11.10 Owners, tilt and the sharp terminal

At $\Delta < \frac1{1000}$ the frames are nearly those of Figure 11.1. Two
more tables, of quartic polynomials in the half-angle tangent of the tilt,
decide the separating axes and the tilt, and then a single inequality gives
the radius.

### Proposition 11.35 (owners and tilt; quartic tables)

Let a boundary cycle at a level $q \le Q_0$ have the word $0101011$, frames in
an interval of length less than $\frac7{10}$, $\tau_E \le 0$, the bounds
(11.9) and the signs of Lemma 11.33 (3).

1. If $\Delta \le \frac3{200}$, every separating retained axis on $B \to T$
   and on $D \to E$ is the axis 3 or 4 (1,545 quartics).
2. If $\Delta \le \frac1{1000}$, every separating retained axis on $G \to A$
   is the axis 1, and on $E \to H$ the axis 2 (729 quartics).
3. If $\Delta \le \frac1{1000}$ and $q \le Q_1$, then
   $\frac{1001}{20000} < \tan\frac t2 < \frac2{25}$, hence
   $\frac1{10} < t < \frac4{25}$ (1,239 quartics).

So at $\Delta \le \frac1{1000}$ the separating axes of the seven edges, in the
order $H \to G, \dots, E \to H$, lie in the *owner sets*

```math
\lbrace 1, 3\rbrace, \quad \lbrace 1\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 1, 3\rbrace, \quad \lbrace 3, 4\rbrace, \quad \lbrace 2\rbrace . \tag{11.15}
```

*Proof.* Each claim excludes a finite list of alternatives. For (1), these are
the *owner patterns*, one retained axis on each edge, with axis 1 or 3 on the
zero edges (Lemma 11.33 (2)), any axis on the mixed edges, and a forbidden axis
on $B \to T$ or $D \to E$; on an aligned edge the two possible nominal
projections are the same, which leaves 48 patterns. For (2) they are the 15
patterns with a forbidden axis on a mixed edge, and for (3) the tilt outside
the stated window. Each alternative is excluded by a *circle dual*
(Lemma M.8): replacing every aligned angle $\varphi_i$ by $k_i\frac\pi2$ changes
each projection by at most $\frac32|d_i|$, since every centre is within
$\frac32$ of $o$, so the separations give linear inequalities
$f_i(t) \cdot x \ge w_i(t) - \frac32\varepsilon$ in the 14 coordinates
$x = (a_0, \dots, a_6, b_0, \dots, b_6)$, with coefficients rational in
$z = \tan\frac t2$; adding them with weights $\lambda_i \ge 0$ and 35 linear
bounds on the coordinates with weights $\kappa_j \ge 0$, and completing the
square in each $(a_i + \frac12, b_i + \frac12)$, whose squared length is at
most $q$, gives with weights $\mu_i > 0$ the necessary inequality

```math
L(z) \le q\sum_i \mu_i + \sum_i \frac{C_{a_i}(z)^2 + C_{b_i}(z)^2}{4\mu_i} . \tag{11.16}
```

Multiplied by $(1 + z^2)^2$, the reverse of (11.16) is a quartic polynomial in
$z$. Each row of the tables gives an alternative, a closed interval
$[l, r]$ of $z$, rational weights and five positive lower bounds for the
coefficients of that quartic in the Bernstein basis of $[l, r]$; so it proves
the quartic positive on $[l, r]$ and excludes the alternative there. For (1)
and (2) the intervals of each pattern cover $[-\frac38, \frac38]$, which
contains every $z$, as $|t| < \frac7{10} < \arctan\frac38$. For (3), with the
owners (11.15) known, the projections are expanded to second order in the
signed errors $d_i$, one weight vector is fixed for each interval of $z$, and
the maximum of the first-order error term over
$\sum_{i \in I}|d_i| \le \frac1{1000}$ is attained at 0 or at
$\pm\frac1{1000}$ on one edge, with one of
its two owners: $1 + 5 \cdot 2 \cdot 2 = 21$ alternatives; 59 intervals with 21
quartics each cover $[-\frac38, \frac{1001}{20000}] \cup [\frac2{25}, \frac38]$.
Finally $2(\frac{1001}{20000} - \frac13(\frac{1001}{20000})^3) > \frac1{10}$
and $2\arctan\frac2{25} < \frac4{25}$. The details are in
[Appendix M](appendix-m.md). $\square$

*Lean:
[`Eight.Candidate.Dual.circle_dual_necessary`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L53),
[`Eight.Candidate.Dual.error_vertex_disjunction`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L89),
[`Eight.Candidate.Dual.Row.Valid.excludes`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L332),
[`Eight.Candidate.Dual.OwnerTable`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L389),
[`Eight.Candidate.Dual.TiltBundle`](../../SquaresInCircles/Eight/Candidate/Dual.lean#L412),
[`Eight.Candidate.quarter_owners`](../../SquaresInCircles/Eight/Candidate/GeometricOwnersQuarterComplete.lean#L335),
[`Eight.Candidate.mixed_owners`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L194),
[`Eight.Candidate.tilt_window`](../../SquaresInCircles/Eight/Candidate/DualApplication.lean#L403),
[`Eight.Candidate.terminalOwners`](../../SquaresInCircles/Eight/Candidate/Model.lean#L138).*

The three quartic tables have 1,545, 729 and 1,239 rows, 3,513 in all, with
17,565 positive Bernstein coefficients. In the formal proof each row carries
its interval, its weights and its quartic, and Lean checks that the quartic is
the stated combination, that its Bernstein coefficients are positive, and that
the intervals of each alternative chain together to cover the required range.

![The separating axes of the seven contacts in the optimal packing: for each pair of neighbours the separating line is drawn dashed through the contact, and each edge is labelled with its owner set, 1 or 3 on H to G, 1 on G to A, 1 or 3 on A to B, 3 or 4 on B to T, 1 or 3 on T to D, 3 or 4 on D to E and 2 on E to H](figures/11-eight/owners.svg)

*Figure 11.20.* The owner sets (11.15) in the optimal packing. Each contact
line (dashed) is a side of one square or of both: on the five aligned edges
the two squares share the side, so two retained axes separate, and on the
mixed edges $G \to A$ and $E \to H$ one square's side touches the other's
corner.

![The tilt window: the half-angle tangent z = tan(t/2) on a line from -3/8 to 3/8, with the two intervals excluded by the tilt table, from -3/8 to 1001/20000 and from 2/25 to 3/8, shaded, and between them the open window from about 0.05 to 0.08, enlarged below, containing the value z* of the optimal packing](figures/11-eight/tilt.svg)

*Figure 11.21.* Proposition 11.35 (3). The 59 intervals of the tilt table
cover the two shaded parts of $[-\frac38, \frac38]$ in $z = \tan\frac t2$; the
tilt of a cycle at $\Delta \le \frac1{1000}$ lies in the window between them,
which contains $z_* \approx 0.0619$ (enlarged below).

### Theorem 11.36 (the sharp terminal)

Let seven unit squares $H, G, A, B, T, D, E$ each lie in the closed disk of
squared radius $q \le Q_0$ about $o$ and miss $D(o, \frac1{12})$, with
canonical frames $-1, -1, 0, 0, 1, 1, 2$ quarter turns ahead of that of $A$,
frame representatives with $\theta_A = 0$ and $t = \theta_G$,

```math
\tfrac1{10} \le t \le \tfrac4{25}, \qquad \Delta \le \tfrac1{1000},
```

and on each of the seven edges a separating axis in the owner set (11.15).
Then, with the weights $\mu_P > 0$ ($P = A, B, D, E, H$, $\sum_P\mu_P = 1$) of
Lemma M.2, the corner offsets $o_P$ and the forces $F_P$ of §M.3,

```math
q \ \ge\ q_* + \frac{3\mu_H}8(t - t_*)^2 + \sum_{P = A, B, D, E, H} \mu_P \left|p_P + o_P + \frac{F_P}{2\mu_P}\right|^2 + \frac{10293}{5000000}\,\Delta \ \ge\ q_* . \tag{11.17}
```

The proof is given in [Appendix M](appendix-m.md). No bound on the centres is
assumed beyond containment and the core; the theorem holds for the original
centres of a packing as well as for a boundary cycle.

*Lean:
[`Eight.Terminal.boundary_quantitative`](../../SquaresInCircles/Eight/Terminal.lean#L33),
[`Eight.Terminal.boundary_rigid`](../../SquaresInCircles/Eight/Terminal.lean#L49),
[`Eight.ExactFamily.Perturbation.quantitative`](../../SquaresInCircles/Eight/ExactFamily/Perturbation.lean#L184),
[`Eight.terminal_constants`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L62),
[`Eight.Terminal.automatic_projections`](../../SquaresInCircles/Eight/TerminalEstimates.lean#L437),
[`Eight.Arithmetic.positive_energy_rigid`](../../SquaresInCircles/Eight/Arithmetic/PositiveEnergy.lean#L22).*

The idea is that of the stresses of Chapter 9. At the tilt $t$ of the cycle,
the chain of Definition 11.2 at the radius $q_*$, with its position chosen to
minimize the defect, carries positive weights on its seven contacts and five
corners that balance at every square (Figure 11.22). The weighted sum of the
five corner constraints $|v_P|^2 \le q$ and the seven separations is a
quadratic function of the actual centres; completing the square in each
anchored centre leaves $q_*$ plus the defect of the chain, at least
$\frac38(t - t_*)^2$ by Proposition 11.4, plus terms in the frame errors that
are positive to first order, by the owner sets, and at most $9.3\Delta^2$ to
second order.

![The exterior squares of the optimal packing with the seven contacts drawn as thin lines between the centres of touching squares, labelled with their weights lambda, between 0.48 and 0.80, and the five corner forces drawn as thick arrows that start at the corners P1 to P5 of A, B, D, E and H on the circle and point outward along the radii, labelled with the weights mu: 0.210 for A, 0.221 for B, 0.273 for D, 0.025 for E and 0.271 for H. T and G carry no corner force](figures/11-eight/stress.svg)

*Figure 11.22.* The stationary weights at $t = t_*$: the contact weights
$\lambda$ on the seven contacts (thin) and the corner forces $2\mu_P P_P$ along
the radii to the corners on the circle (thick). At each of the seven squares
the forces balance; at $T$ and $G$ the two contact forces cancel. With these
weights the sum of the corner constraints and the contacts is exactly $q_*$
plus squares (Proposition 11.38).

## 11.11 The unrestricted lower bound and the pullback

### Proposition 11.37 (the lower bound)

If eight unit squares form a packing in a closed disk of squared radius $q$,
then $q \ge q_*$.

*Proof.* Suppose $q < q_*$, and enlarge the disk, without moving the squares,
to the squared radius $\bar q = \max(q, q_-)$; by (11.1),
$\frac52 < \bar q < q_* < Q_1$. By Theorem 11.10 the squares have a central
square and seven exterior squares; choose a witness on each consecutive pair.
By Proposition 11.15 there is a boundary cycle $\mathcal Z$ at the level
$\bar q$ with the same frames and witnesses, and by Lemma 11.17 its expansion
$\mathcal Z_1$ to the level $Q_1$, with the same frames, centre directions,
signed tangents and words, in which every witness still separates.

For the frames and the word, expand further to $Q_0$: Theorem 11.23 and
Proposition 11.26 give frames in an interval of length less than $\frac7{10}$
and the word $0101011$, and these are properties of the unchanged frames, so
they hold for $\mathcal Z_1$ and $\mathcal Z$. After the normalization of
Lemma 11.28, Proposition 11.29 gives (11.9) for $\mathcal Z_1$, Proposition
11.34 gives $\Delta < \frac1{1000}$, Lemma 11.33 and Proposition 11.35 give
the owner sets (11.15) for every separating axis of $\mathcal Z_1$ and the
tilt window. These conclusions are about frames, tangents and directions,
which $\mathcal Z$ shares, except the owner sets, which concern axes; but each
witness of $\mathcal Z$ separates in $\mathcal Z_1$, so it lies in its owner
set. So $\mathcal Z$, a boundary cycle at the level $\bar q$, satisfies the
hypotheses of Theorem 11.36, which gives $\bar q \ge q_*$, a contradiction.
$\square$

*Lean:
[`Eight.squared_radius_lower_bound`](../../SquaresInCircles/Eight/TableProof.lean#L435),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55),
[`Eight.global_normalization_exists`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L490),
[`Eight.GlobalNormalization`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L51),
[`Eight.GlobalNormalization.radius_rigid`](../../SquaresInCircles/Eight/TableProof.lean#L144),
[`Eight.Candidate.capture`](../../SquaresInCircles/Eight/Candidate/Capture.lean#L35),
[`Eight.Candidate.Captured.pullback`](../../SquaresInCircles/Eight/Candidate/Capture.lean#L75),
[`Eight.sourceLevel`](../../SquaresInCircles/Eight/RadiusTransfer.lean#L585).*

The detour through $Q_1$ is needed because the tables are computed at one
level, and it costs nothing: the expansion keeps every separating axis, and
only the frames, directions and tangents, which it does not move, are carried
back. The same argument at the radius $q_*$ itself proves more.

### Proposition 11.38 (the original squares at the optimal radius)

Let eight unit squares form a packing in a closed disk of radius $R_8$ about
$o$. Then, after a rotation about $o$ and possibly a reflection, and a
relabelling, the seven exterior squares are the squares $A$, $B$, $D$, $E$,
$H$ of the model and the squares $T$ and $G$ of the model for some $\zeta$ and
$\eta$, with the same frames, and $\frac7{12} \le \zeta \le \zeta_+$ and
$\eta_- \le \eta \le \eta_+$.

*Proof.* Run the proof of Proposition 11.37 with $\bar q = q_*$. Theorem 11.36
applied to the boundary cycle $\mathcal Z$ at the level $q_*$ gives equality in
(11.17), so $\Delta = 0$ and $t = t_*$: the frames of the boundary cycle, which
are the frames of the original squares, are those of the model, up to a
rotation, and the reflection of Lemma 11.28.

Now apply the stationary weights a second time, to the original centres $p_P$.
The seven original witnesses lie in the owner sets (11.15), and at zero frame
errors either owner of an aligned edge gives the same normal, the normal of
the model; so the original gaps $g_e$ on these normals are nonnegative. As in
Theorem 11.36, the weighted sum is an exact identity (Lemma M.9):

```math
\sum_{P = A, B, D, E, H}\mu_P|p_P + o_P|^2 - \sum_e \lambda_e\,g_e = q_* + \sum_{P = A, B, D, E, H}\mu_P\left|p_P - p_P^0\right|^2 , \tag{11.18}
```

where $p_P^0$ are the centres of the model. Containment gives
$|p_P + o_P|^2 \le q_*$, so the left side is at most $q_*$. Hence every
$p_P = p_P^0$ and, as every $\lambda_e > 0$, every $g_e = 0$. The contacts
$D \to T$ and $T \to B$ along the horizontal normal fix the first coordinate
of $p_T$ at $x_2 - \frac32$, and the contact $H \to G$ along $e$ fixes
$\langle e, p_G - p_H\rangle = 1$; so $p_T = (x_2 - \frac32, \zeta)$ and
$p_G = p_H + e + \eta f$ for some $\zeta$ and $\eta$. The cyclic order puts the
centre of $T$ in the sector from $B$ to $D$, in the upper half plane, so
$\zeta > 0$, and as the first coordinate of $p_T$ lies in $(0, \frac12)$, the
distance from $o$ to $T$ is $\zeta - \frac12$, at least $\frac1{12}$ by
Theorem 11.10; so $\zeta \ge \frac7{12}$. In the same way $G$ lies in the
sector from $H$ to $A$, its coordinate along $f$ is negative, its coordinate
$h_1 + \frac32$ along $e$ lies in $(0, \frac12)$, and the core gives
$h_2 + \frac12 + \eta \le -\frac7{12}$, that is, $\eta \le \eta_+$.
Containment gives $\zeta \le \zeta_+$ and $\eta \ge \eta_-$ as in
Proposition 11.5. $\square$

*Lean:
[`Eight.GlobalNormalization.original_frames`](../../SquaresInCircles/Eight/TableProof.lean#L151),
[`Eight.GlobalNormalization.original_gaps`](../../SquaresInCircles/Eight/TableProof.lean#L223),
[`Eight.GlobalNormalization.original_centers`](../../SquaresInCircles/Eight/TableProof.lean#L388),
[`Eight.GlobalNormalization.original_slider_sectors`](../../SquaresInCircles/Eight/GlobalNormalization.lean#L594),
[`Eight.Terminal.original_pullback`](../../SquaresInCircles/Eight/Terminal.lean#L69),
[`Eight.OriginalDual.original_centers_rigid`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L171),
[`Eight.OriginalDual.exact_identity`](../../SquaresInCircles/Eight/ExactFamily/CenterCompletion.lean#L124).*

The boundary cycle is used only to transfer the frames and the witnesses; the
positions come from (11.18) applied to the original squares, which needs no
estimate of how far a square moved in the reduction.

## 11.12 The equality domain

### Proposition 11.39 (uniqueness)

Every packing of eight unit squares in a closed disk of radius $R_8$ is
congruent to the model of admissible parameters or to its mirror image in the
diagonal.

*Proof.* By Proposition 11.38, after a rotation, possibly a reflection in the
diagonal, and a relabelling, the exterior squares are those of the model for
some admissible $\zeta$ and $\eta$. The central square contains the closed
disk of radius $\frac1{12}$ about $o$ in its interior (Theorem 11.10). One of
the four frames of the central square makes an angle in $[-\frac\pi4, \frac\pi4)$
with the horizontal; it is $2\arctan w$ for exactly one $w$ in
$[1 - \sqrt2, \sqrt2 - 1)$, namely $w = \frac{S}{1 + C}$ for that frame
$(C, S)$. Let $(x, y)$ be its centre. By Proposition 11.6 (2) the parameters
$(x, y, w, \zeta, \eta)$ are admissible, and the packing is the model of these
parameters, or its mirror image if a reflection was used. $\square$

*Lean:
[`Eight.origin_equality_classification`](../../SquaresInCircles/Eight/TableProof.lean#L455),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62),
[`Eight.ExactFamily.central_parameters_exist`](../../SquaresInCircles/Eight/ExactFamily/CentralParameters.lean#L141),
[`Eight.ExactFamily.halfAngle_recover`](../../SquaresInCircles/Eight/ExactFamily/CentralParameters.lean#L87),
[`Eight.admissible_of_original_geometry`](../../SquaresInCircles/Eight/Equality.lean#L168).*

*Proof of Theorem 11.1.* Part (1) is Proposition 11.6 (1); a reflection
preserves packings. Part (2): by Proposition 11.37, $R^2 \ge q_*$. Part (3):
by Proposition 11.39 every packing in a closed disk of radius $R_8$ is
congruent to an admissible model or its mirror image, and conversely such a
configuration is a packing in a closed disk of radius $R_8$ by part (1) and
[Lemma 2.7](02-preliminaries.md#lemma-27-congruent-configurations). The
radius is attained, for instance by the point $(0.14, 0, 0.1, 1.35, -0.32)$
of the box of Proposition 11.7. $\square$

*Lean: [`Eight.optimum`](../../SquaresInCircles/Eight/Uniqueness.lean#L82),
[`Eight.isLeast`](../../SquaresInCircles/Eight/Uniqueness.lean#L98),
[`Eight.packing_iff`](../../SquaresInCircles/Eight/Uniqueness.lean#L102),
[`Eight.equality_iff_parameters`](../../SquaresInCircles/Eight/Uniqueness.lean#L107),
[`Eight.models_nonempty`](../../SquaresInCircles/Eight/Equality.lean#L239),
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L38).*

The theorem fits the scheme of
[Corollary 2.10](02-preliminaries.md#corollary-210-the-scheme-of-proof), with
the admissible models and their mirror images as the set $\mathcal M$: they
are packings in the disk, they reach the circle at the corner $P_1$ of $A$,
and every packing at the radius $R_8$ is congruent to one of them. Here,
unlike in the earlier chapters, the lower bound is also proved directly, by
Proposition 11.37.
