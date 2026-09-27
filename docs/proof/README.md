# Packing unit squares in a disk

**Optimal packings of one to five and seven unit squares, with a Lean 4
formalization**

A companion text to the Lean 4 formalization in this repository
([lean4-squares-in-circles](https://github.com/vltanh/lean4-squares-in-circles));
for its authorship see [Contributors](../contributors.md).

**Abstract.** For $n = 1, \dots, 5$ and $n = 7$ we determine the least radius
$R_n$ of a closed disk that holds $n$ non-overlapping unit squares, and every
packing that attains it: $R_1 = \frac{\sqrt2}2$, $R_2 = \frac{\sqrt5}2$,
$R_3 = \frac{5\sqrt{17}}{16}$, $R_4 = \sqrt2$, $R_5 = \sqrt{5/2}$ and
$R_7 = \frac{\sqrt{13}}2$. For $n \le 5$ the optimal packing is unique up to a
rotation about the disk centre and a relabelling of the squares. For $n = 7$
the optimal packings form a three-parameter family: two columns of two squares
are fixed, and each of the three squares of the middle column can move along
it on its own. Every case is proved in the same way. An analysis of the
packings at the optimal radius shows that they are all congruent to the
optimal models, and the lower bound follows because every optimal model
reaches the circle. For three to five squares the analysis measures the arcs
of a small circle about the disk centre that the squares occupy; for seven
squares it attaches to each square a direction, its marker, and shows that the
markers of two disjoint squares are at least $\frac\pi3$ apart. Every result
is proved in Lean 4 with mathlib, and each numbered statement names the
declarations that prove it.

## Contents

- [1. Introduction](#1-introduction)
  - [1.1 The problem](#11-the-problem)
  - [1.2 The main theorem](#12-the-main-theorem)
  - [1.3 Background](#13-background)
  - [1.4 Outline of the proof](#14-outline-of-the-proof)
  - [1.5 This text and the formalization](#15-this-text-and-the-formalization)
- [2. Preliminaries](preliminaries.md)
  - [2.1 Conventions](preliminaries.md#21-conventions)
  - [2.2 Unit squares](preliminaries.md#22-unit-squares)
  - [2.3 Packings](preliminaries.md#23-packings)
  - [2.4 Frames and congruence](preliminaries.md#24-frames-and-congruence)
  - [2.5 Models of axis-parallel squares](preliminaries.md#25-models-of-axis-parallel-squares)
  - [2.6 Reduction to uniqueness](preliminaries.md#26-reduction-to-uniqueness)
- [3. Tools](common.md)
  - [3.1 The disk centre seen from a square](common.md#31-the-disk-centre-seen-from-a-square)
  - [3.2 Contact polygons](common.md#32-contact-polygons)
  - [3.3 Two disjoint squares](common.md#33-two-disjoint-squares)
  - [3.4 Arcs and the angular budget](common.md#34-arcs-and-the-angular-budget)
  - [3.5 Charts](common.md#35-charts)
  - [3.6 Arcs of an exterior square](common.md#36-arcs-of-an-exterior-square)
  - [3.7 The radial sweep](common.md#37-the-radial-sweep)
  - [3.8 Elementary estimates](common.md#38-elementary-estimates)
  - [3.9 Recognising a model](common.md#39-recognising-a-model)
- [4. One square](one.md)
  - [4.1 Construction](one.md#41-construction)
  - [4.2 Uniqueness](one.md#42-uniqueness)
  - [4.3 Proof of Theorem 4.1](one.md#43-proof-of-theorem-41)
- [5. Two squares](two.md)
  - [5.1 Construction](two.md#51-construction)
  - [5.2 The centres](two.md#52-the-centres)
  - [5.3 The half circles](two.md#53-the-half-circles)
  - [5.4 Proof of Theorem 5.1](two.md#54-proof-of-theorem-51)
- [6. Three squares](three.md)
  - [6.1 Construction](three.md#61-construction)
  - [6.2 The contact polygon](three.md#62-the-contact-polygon)
  - [6.3 Exterior squares](three.md#63-exterior-squares)
  - [6.4 The containing square](three.md#64-the-containing-square)
  - [6.5 The T](three.md#65-the-t)
  - [6.6 Proof of Theorem 6.1](three.md#66-proof-of-theorem-61)
- [7. Four squares](four.md)
  - [7.1 Construction](four.md#71-construction)
  - [7.2 The diamond](four.md#72-the-diamond)
  - [7.3 Arcs of the squares](four.md#73-arcs-of-the-squares)
  - [7.4 The block](four.md#74-the-block)
  - [7.5 Proof of Theorem 7.1](four.md#75-proof-of-theorem-71)
- [8. Five squares](five.md)
  - [8.1 Construction](five.md#81-construction)
  - [8.2 The 12-gon](five.md#82-the-12-gon)
  - [8.3 Exterior squares](five.md#83-exterior-squares)
  - [8.4 A centred square](five.md#84-a-centred-square)
  - [8.5 The plus](five.md#85-the-plus)
  - [8.6 Proof of Theorem 8.1](five.md#86-proof-of-theorem-81)
- [9. Seven squares](seven.md)
  - [9.1 Construction](seven.md#91-construction)
  - [9.2 States, labels and markers](seven.md#92-states-labels-and-markers)
  - [9.3 The canonical pair](seven.md#93-the-canonical-pair)
  - [9.4 Contacts and the critical gap](seven.md#94-contacts-and-the-critical-gap)
  - [9.5 Marker separation](seven.md#95-marker-separation)
  - [9.6 The ring](seven.md#96-the-ring)
  - [9.7 The middle column](seven.md#97-the-middle-column)
  - [9.8 Proof of Theorem 9.1](seven.md#98-proof-of-theorem-91)
- [Appendix A. One-variable estimates and the marker arc](appendix-a.md)
  - [A.1 Monotonicity and concavity](appendix-a.md#a1-monotonicity-and-concavity)
  - [A.2 Sine and cosine](appendix-a.md#a2-sine-and-cosine)
  - [A.3 The Bernstein criterion](appendix-a.md#a3-the-bernstein-criterion)
  - [A.4 Proof of Lemma 9.9](appendix-a.md#a4-proof-of-lemma-99)
- [Appendix B. The critical gap: set-up and the easy axes](appendix-b.md)
  - [B.1 The plan](appendix-b.md#b1-the-plan)
  - [B.2 Support sums in closed form](appendix-b.md#b2-support-sums-in-closed-form)
  - [B.3 The label regions and their boundary](appendix-b.md#b3-the-label-regions-and-their-boundary)
  - [B.4 Segments of constant label](appendix-b.md#b4-segments-of-constant-label)
  - [B.5 Profiles along the boundary](appendix-b.md#b5-profiles-along-the-boundary)
  - [B.6 The target support on the axial boundary](appendix-b.md#b6-the-target-support-on-the-axial-boundary)
  - [B.7 The easy sectors](appendix-b.md#b7-the-easy-sectors)
  - [B.8 The capped labels](appendix-b.md#b8-the-capped-labels)
  - [B.9 Proof of Proposition 9.17](appendix-b.md#b9-proof-of-proposition-917)
- [Appendix C. The critical gap: the inward axis](appendix-c.md)
  - [C.1 The inward support sum](appendix-c.md#c1-the-inward-support-sum)
  - [C.2 Two profiles of the turn](appendix-c.md#c2-two-profiles-of-the-turn)
  - [C.3 Signs (+, +) with an axial target](appendix-c.md#c3-signs---with-an-axial-target)
  - [C.4 Signs (+, +) with a side target](appendix-c.md#c4-signs---with-a-side-target)
  - [C.5 Signs (+, −): the closed form and a nonpositive turn](appendix-c.md#c5-signs---the-closed-form-and-a-nonpositive-turn)
  - [C.6 The boundary of the label regions](appendix-c.md#c6-the-boundary-of-the-label-regions)
  - [C.7 Two circles](appendix-c.md#c7-two-circles)
  - [C.8 Minima on the boundary](appendix-c.md#c8-minima-on-the-boundary)
  - [C.9 Signs (+, −) with active labels](appendix-c.md#c9-signs---with-active-labels)
- [Appendix D. The critical gap: the forward axis](appendix-d.md)
  - [D.1 The forward support sum and the tools](appendix-d.md#d1-the-forward-support-sum-and-the-tools)
  - [D.2 Target sign negative](appendix-d.md#d2-target-sign-negative)
  - [D.3 Opposite signs](appendix-d.md#d3-opposite-signs)
  - [D.4 Both signs negative](appendix-d.md#d4-both-signs-negative)

## 1. Introduction

### 1.1 The problem

A *packing* of $n$ unit squares in a disk places $n$ squares of side 1 in a
closed disk so that no two of them overlap: they may touch, but their
interiors are disjoint. The squares are placed and turned independently of one
another. Let $R_n$ be the least radius of a disk that holds a packing of $n$
unit squares. We ask for $R_n$, and for all the packings that attain it.

Both questions are harder than they look. Turning a square changes how far it
reaches in every direction at once, so the space of packings is curved and
large, and the optimal packings found by search are often rigid only in part.
The best packings known for small $n$ are collected on Erich Friedman's
*Squares in Circles* page [1]. We prove that six of them are optimal, and find
all optimal packings in those six cases.

### 1.2 The main theorem

The precise definitions of a packing, of a model and of congruence to a model
are Definitions 2.3 and 2.6. A *model* is a configuration of unit squares
placed about the origin, and a packing is *congruent* to it if one rotation
about the disk centre and one relabelling of the squares carry the model,
placed at the disk centre, onto the packing. Write $Q(c)$ for the
axis-parallel unit square centred at $c$ (Definition 2.2).

| $n$ | $R_n$ | $R_n \approx$ | centres $c_1, \dots, c_n$ of the optimal models | the optimal packing |
| :-: | :-: | :-: | --- | --- |
| 1 | $\frac{\sqrt2}2$ | 0.7071 | $(0, 0)$ | the square |
| 2 | $\frac{\sqrt5}2$ | 1.1180 | $(-\frac12, 0)$, $(\frac12, 0)$ | the $2 \times 1$ rectangle |
| 3 | $\frac{5\sqrt{17}}{16}$ | 1.2885 | $(-\frac12, -\frac5{16})$, $(\frac12, -\frac5{16})$, $(0, \frac{11}{16})$ | the T |
| 4 | $\sqrt2$ | 1.4142 | $(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$, $(\frac12, -\frac12)$ | the $2 \times 2$ block |
| 5 | $\sqrt{5/2}$ | 1.5811 | $(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$ | the plus |
| 7 | $\frac{\sqrt{13}}2$ | 1.8028 | $(1, -\frac12)$, $(1, \frac12)$, $(-1, -\frac12)$, $(-1, \frac12)$, $(0, y_1)$, $(0, y_2)$, $(0, y_3)$ | the column packings |

*Table 1.1.* The optimal radii and the optimal models $Q(c_1), \dots, Q(c_n)$.
For $n \le 5$ there is one optimal model. For $n = 7$ the optimal models are
the *column packings*, one for each choice of heights with
$y_1 + 1 \le y_2$, $y_2 + 1 \le y_3$ and
$-(\sqrt3 - \frac12) \le y_1$, $y_3 \le \sqrt3 - \frac12$.

![The six optimal packings side by side at a common scale, each in its dashed circle of radius R_n: one square; two squares forming a 2 by 1 rectangle; the T of three squares; the 2 by 2 block of four; the plus of five; and seven squares, two columns of two beside a column of three. Dots mark the corners that lie on the circles](figures/front-optimal.svg)

*Figure 1.1.* The optimal packings of $n = 1, 2, 3, 4, 5$ and $7$ unit
squares, each in its circle of radius $R_n$, at a common scale. Dots mark the
corners on the circle.

#### Theorem 1.1 (main theorem)

Let $n \in \lbrace 1, 2, 3, 4, 5, 7 \rbrace$, and let $R_n$ and the optimal
models be as in Table 1.1.

1. $R_n$ is the least radius of a closed disk that holds a packing of $n$ unit
   squares.
2. The packings of $n$ unit squares in a closed disk of radius $R_n$ are
   exactly the configurations congruent to an optimal model.

*Proof.* For $n = 1, 2, 3, 4, 5, 7$ this is Theorem 4.1, 5.1, 6.1, 7.1, 8.1
and 9.1 respectively: parts (1) and (2) of each give the attainment and the
lower bound of (1) here, and part (3) gives (2). $\square$

*Lean: [`optimal_radius`](../../SquaresInCircles.lean#L49),
[`optimal_packings`](../../SquaresInCircles.lean#L55),
[`optimal_packings_rigid`](../../SquaresInCircles.lean#L63),
[`optimalRadius`](../../SquaresInCircles/Geometry.lean#L220),
[`optimalPackings`](../../SquaresInCircles/Geometry.lean#L233).*

*Remarks.* (i) For $n \le 5$ the theorem says that the optimal packing is
unique up to a rotation about the disk centre and a relabelling of the
squares. Reflections are not needed, since every optimal model is symmetric
under a reflection in a line through the origin. (ii) For $n = 7$ the optimum
is not unique. The four side squares are fixed, but each of the three middle
squares can move along the middle column on its own, as long as their centres
stay at least 1 apart and within $\sqrt3 - \frac12$ of the disk centre; the
total slack is $2\sqrt3 - 3 \approx 0.464$. So the optimal packings form a
three-parameter family, and infinitely many of them are pairwise not
congruent (Figure 1.2). (iii) The case $n = 6$ and the cases $n \ge 8$ are
not treated here.

![Four optimal packings of seven unit squares in the circle of radius root 13 over 2. In each, the four side squares are the same, and the three middle squares sit at different heights along the dotted middle column: centred at -1, 0, 1; pushed to the bottom; with only the bottom square moved down; and with the middle square moved up and the top square at the top of its range](figures/front-columns.svg)

*Figure 1.2.* Four optimal packings of seven squares, with middle heights
$(-1, 0, 1)$, $(\frac12 - \sqrt3, \frac32 - \sqrt3, 1)$, $(-1.2, 0, 1)$ and
$(-1, 0.2, 1.23)$. The side squares are fixed; each middle square moves on its
own along the dotted column $[-\frac12, \frac12] \times [-\sqrt3, \sqrt3]$.

### 1.3 Background

The packings of Table 1.1 are listed on Friedman's page [1], which has
collected the best known packings of squares in a circle since 1997; the
packings of three, five and seven squares were found by Friedman in 1997. One
and two squares are folklore, listed there as trivial. For three squares,
Montanher, Neumaier, Markót, Domes and Schichl [2] enclosed the optimal radius
in an interval of width $6 \cdot 10^{-14}$ that contains
$\frac{5\sqrt{17}}{16}$, and every optimal arrangement in small boxes near the
T, by a computer-assisted interval branch-and-bound search; their enclosure
does not determine the radius exactly and does not show that the T itself is
optimal. Four squares are reported on Friedman's page as proved at the
International Math Summer Camp in 2026; we found no publication. We found no
earlier proof for five or seven squares, where the packings of Table 1.1 are
listed only as the best known ones.

Proof assistants have verified packing theorems in other settings: the Kepler
conjecture [3] and the optimal sphere packing in dimension 8 [4]. We found no
earlier formal proof of an optimal packing of squares or circles in a circle
or a square. A more detailed review is on the
[prior work](../prior-work.md) page.

### 1.4 Outline of the proof

**The reduction.** For each $n$, Corollary 2.10 reduces Theorem 1.1 to three
facts about the set of optimal models: (a) each optimal model is a packing in
the closed disk of radius $R_n$; (b) each optimal model reaches the circle of
radius $R_n$; (c) every packing of $n$ unit squares in a closed disk of radius
$R_n$ is congruent to an optimal model. Facts (a) and (b) are direct
computations. The lower bound is not proved separately: a packing in a smaller
disk would also be a packing at the radius $R_n$, so by (c) it would be an
optimal packing, and by (b) it would not fit in the smaller disk
(Proposition 2.9, Figure 1.3). All the work is in (c), uniqueness at the
optimal radius.

![The plus of five squares turned about the disk centre o inside its dashed circle of radius R_5, with a smaller solid circle of radius R about o; the eight outer corners lie on the dashed circle, and the parts of the squares outside the smaller circle are highlighted in red](figures/front-reduction.svg)

*Figure 1.3.* The plus, turned about $o$, reaches its circle of radius $R_5$
at eight corners, so it does not fit in a smaller disk: the parts highlighted
in red stick out. Every packing at the radius $R_5$ is a copy of it, so no packing
fits in a smaller disk.

**The disk constraint.** Seen from the disk centre $o$, a square $S$ is
described by two numbers $a_S \ge b_S \ge 0$, the offsets of $o$ from the
centre of $S$ along its axes (Definition 3.1), and $S$ lies in the closed disk
of radius $R$ about $o$ only if its farthest vertex does:
$\varphi(a_S, b_S) = (a_S + \frac12)^2 + (b_S + \frac12)^2 \le R^2$
(Lemma 3.4). Every uniqueness proof uses the disk only through these
inequalities, one for each square.

**One and two squares** (Chapters 4 and 5). At the radius $R_1$ the
inequality forces $a_S = b_S = 0$: the square is centred at the disk centre.
At the radius $R_2$ it keeps both centres within $\frac12$ of the disk centre,
while the centres of disjoint squares are at least 1 apart; so both centres are
exactly $\frac12$ away, and each square holds the half of a small circle about
the disk centre that faces it. Disjoint half circles are opposite, and that is
the rectangle.

**Three to five squares** (Chapters 6 to 8). These cases share one method,
run once at the optimal radius. Take a packing in the closed disk of radius
$R_n$.

1. *The contact polygon.* The inequality $\varphi(a_S, b_S) \le R_n^2$ is
   curved. The tangent lines of the circle $\varphi = R_n^2$ at the positions
   of the squares of the optimal packing turn it into a polygon
   (Lemma 3.6). From here on the disk is forgotten, except for four squares.
2. *Exterior squares.* On a small auxiliary circle about the disk centre,
   every square that does not contain the centre holds an arc of at least
   $\frac{2\pi}n$, and for three and four squares exactly $\frac{2\pi}n$ only
   in the positions of the optimal packing.
3. *The containing square.* At most one square contains the disk centre. Its
   own arc can be short, and each case deals with it separately.
4. *The budget.* The arcs of disjoint squares cannot take up more than the
   whole circle (Lemma 3.16). For three and four squares every arc is then as
   short as it can be, and those positions rebuild the optimal packing. For
   five squares the budget leaves only a square centred at the disk centre,
   and that forces the plus.

![Two panels, each with a square in the dashed circle of radius root 2 and the circle of radius 1/2 about the disk centre o. Left: a square outside o, without a vertex at o, holds a highlighted arc of more than 90 degrees of the small circle. Right: a square containing o holds the highlighted quarter of the small circle that faces its centre](figures/front-arc-method.svg)

*Figure 1.4.* The method of arcs for four squares and the circle
$\Gamma_{1/2}$. A square that avoids $o$, without a vertex at $o$, holds more
than a quarter of the circle; a square containing $o$ holds the quarter facing
its centre. Four disjoint arcs of at least a quarter are exact quarters, and
that gives the block.

| | three squares | four squares | five squares |
| --- | --- | --- | --- |
| $R_n^2$ | $\frac{425}{256}$ | $2$ | $\frac52$ |
| **1.** tangent points | $(\frac12, \frac5{16})$, $(\frac{11}{16}, 0)$ and mirrors | $(\frac12, \frac12)$ | $(1, 0)$, $(0, 1)$, $(\frac{\sqrt5-1}2, \frac{\sqrt5-1}2)$ |
| **1.** polygon | the 16-gon $P_3$ | the diamond $a + b \le 1$ | the 12-gon $P_5$ |
| **1.** disk used afterwards | no | yes, $\varphi \le 2$ | no |
| **2.** auxiliary radius | $\frac38$ | $\frac12$ | $\frac56$ |
| **2.** exterior arc | a cap of at least 120°, exactly 120° only in two positions | a cap of at least 90°, exactly 90° only with a vertex at the centre | an arc longer than 72° |
| **3.** containing square | impossible: its own arc, no clipped cap, and nearly axial caps too wide on $\Gamma_{7/16}$ | the quarter circle facing its centre | its radial sweep holds 72°, unless it is centred at the disk centre |
| **4.** budget | three caps of exactly 120° (Lemmas 3.16, 3.18) | four quarter circles (Lemma 3.16) | the sweep (Proposition 3.28): a square centred at the disk centre |
| rebuilt from | the angles between the caps | a quarter grid of arc centres | unit contacts with the centred square |

*Table 1.2.* How the method of arcs runs for three, four and five squares.

**Seven squares** (Chapter 9 and Appendices A to D). This case compares pairs
of squares rather than arcs of one circle. Take a packing in the closed disk
of radius $R_7$.

1. *Markers.* Each square that avoids the disk centre gets a marker, a
   direction from the disk centre computed from the position of the centre
   relative to the square, and holds an arc of the unit circle about its
   marker.
2. *The pair theorem.* Two disjoint such squares have markers at least
   $\frac\pi3$ apart, and exactly $\frac\pi3$ apart only if they touch as in
   an optimal packing. The proof puts the pair in a normal position, writes
   the overlaps of their shadows on the four edge directions in closed form,
   and shows that they are positive for every gap below $\frac\pi3$ and
   vanish at $\frac\pi3$ only at those contacts. The case analysis at the gap
   $\frac\pi3$ fills Appendices B to D.
3. *The ring.* Seven markers do not fit, so some square contains the disk
   centre. The markers of the other six form a regular hexagon, and going
   round it each square touches the next as in an optimal packing: two side
   columns, one square above the centre and one below.
4. *The middle column.* The side columns pin the square that contains the
   centre to the middle column. The three squares of that column need only
   stay 1 apart, so each can move along it on its own.

![Markers of seven squares: two touching squares, a side square and the top square, with their markers drawn as directions from the disk centre exactly pi/3 apart; the same pair turned so that their markers are closer, where the squares overlap; and a column packing whose six exterior squares have markers forming a regular hexagon](figures/front-markers.svg)

*Figure 1.5.* Markers of seven squares. A side square and the top square that
touch as in an optimal packing have markers exactly $\frac\pi3$ apart; turned
closer, the squares overlap. In every column packing the six markers form a
regular hexagon.

### 1.5 This text and the formalization

Chapters 2 and 3 contain the definitions and the tools shared by several
cases; each of Chapters 4 to 9 proves one case, and the appendices hold the
long computations of the seven-square case. Definitions, lemmas,
propositions, theorems and corollaries are numbered together within each
chapter; figures and tagged equations are numbered separately. Sections are
cited as §3.4. Proofs end with $\square$.

Every numbered statement ends with a line *Lean: …* naming the Lean 4
declarations [5, 6] that state it, linked to their source. The proofs in this
text follow the formal proofs, but are written for a human reader: where a
formal proof closes an inequality by an automatic procedure, the text gives an
explicit identity, sum of squares or certificate that can be checked by hand
or with a computer algebra system. The formal proofs themselves are checked by
the Lean kernel; the [verification](../verification.md) page explains how to
build them and audit their axioms. The figures are computed from the same
geometry by the scripts in [`scripts/`](../../scripts).

### References

1. E. Friedman. Squares in Circles. Erich's Packing Center,
   <https://erich-friedman.github.io/packing/squincir/> (accessed September
   2026).
2. T. Montanher, A. Neumaier, M. C. Markót, F. Domes, H. Schichl. Rigorous
   packing of unit squares into a circle. *J. Global Optim.* 73 (2019)
   547–565. [doi:10.1007/s10898-018-0711-5](https://doi.org/10.1007/s10898-018-0711-5)
3. T. Hales et al. A formal proof of the Kepler conjecture.
   *Forum Math. Pi* 5 (2017) e2.
4. S. Hariharan, C. Birkbeck, S. Lee, H. K. G. Ma, B. Mehta, A. Poiroux,
   M. Viazovska. A milestone in formalization: the sphere packing problem in
   dimension 8. [arXiv:2604.23468](https://arxiv.org/abs/2604.23468) (2026).
5. The mathlib Community. The Lean mathematical library. In *Proceedings of
   the 9th ACM SIGPLAN International Conference on Certified Programs and
   Proofs (CPP 2020)*, 367–381.
6. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
   language. In *Automated Deduction – CADE 28*, Lecture Notes in Computer
   Science 12699 (2021), 625–635.
