# Packing unit squares in a disk

**Optimal packings of one to seven unit squares, with a Lean 4
formalization**

A companion text to the Lean 4 formalization in this repository
([lean4-squares-in-circles](https://github.com/vltanh/lean4-squares-in-circles));
for its authorship see [Contributors](../contributors.md).

**Abstract.** For $n = 1, \dots, 7$ we determine the least radius $R_n$ of a
closed disk that holds $n$ non-overlapping unit squares, and every packing
that attains it: $R_1 = \frac{\sqrt2}2$, $R_2 = \frac{\sqrt5}2$,
$R_3 = \frac{5\sqrt{17}}{16}$, $R_4 = \sqrt2$, $R_5 = \sqrt{5/2}$,
$R_6 \approx 1.68854$, whose square is a root of an explicit quartic, and
$R_7 = \frac{\sqrt{13}}2$. For $n \le 6$ the optimal packing is unique up to
a rotation about the disk centre and a relabelling of the squares; for $n = 6$
one of its squares is turned by $\frac\pi4$. For $n = 7$
the optimal packings form a three-parameter family: two columns of two squares
are fixed, and each of the three squares of the middle column can move along
it on its own. Every case is proved in the same way. An analysis of the
packings at the optimal radius shows that they are all congruent to the
optimal models, and the lower bound follows because every optimal model
reaches the circle. For three to five squares the analysis measures the arcs
of a small circle about the disk centre that the squares hold. For six squares
the arcs find the square that contains the disk centre and five fixed points
label the others; then a weighted sum of separating inequalities, whose
weights balance at the optimal packing, bounds the radius, with estimates
uniform over whole intervals of the angles of the squares. For seven squares
the analysis attaches to each square that avoids the disk centre a direction,
its marker, and shows that the markers of two disjoint squares are at least
$\frac\pi3$ apart. Every result is proved in Lean 4 with mathlib, and each
numbered statement names the declarations that prove it.

## Contents

- [1. Introduction](#1-introduction)
  - [1.1 The problem](#11-the-problem)
  - [1.2 The main theorem](#12-the-main-theorem)
  - [1.3 Background](#13-background)
  - [1.4 Outline of the proof](#14-outline-of-the-proof)
  - [1.5 This text and the formalization](#15-this-text-and-the-formalization)
- [2. Preliminaries](02-preliminaries.md)
  - [2.1 Conventions](02-preliminaries.md#21-conventions)
  - [2.2 Unit squares](02-preliminaries.md#22-unit-squares)
  - [2.3 Packings](02-preliminaries.md#23-packings)
  - [2.4 Frames and congruence](02-preliminaries.md#24-frames-and-congruence)
  - [2.5 Models of axis-parallel squares](02-preliminaries.md#25-models-of-axis-parallel-squares)
  - [2.6 Reduction to uniqueness](02-preliminaries.md#26-reduction-to-uniqueness)
- [3. Tools](03-tools.md)
  - [3.1 The disk centre seen from a square](03-tools.md#31-the-disk-centre-seen-from-a-square)
  - [3.2 Contact polygons](03-tools.md#32-contact-polygons)
  - [3.3 Two disjoint squares](03-tools.md#33-two-disjoint-squares)
  - [3.4 Arcs and the angular budget](03-tools.md#34-arcs-and-the-angular-budget)
  - [3.5 Charts](03-tools.md#35-charts)
  - [3.6 Arcs of an exterior square](03-tools.md#36-arcs-of-an-exterior-square)
  - [3.7 The radial sweep](03-tools.md#37-the-radial-sweep)
  - [3.8 Elementary estimates](03-tools.md#38-elementary-estimates)
  - [3.9 Recognizing a model](03-tools.md#39-recognizing-a-model)
- [4. One square](04-one.md)
  - [Theorem 4.1 (one square)](04-one.md#theorem-41-one-square)
  - [4.1 Construction](04-one.md#41-construction)
  - [4.2 Uniqueness](04-one.md#42-uniqueness)
  - [4.3 Proof of Theorem 4.1](04-one.md#43-proof-of-theorem-41)
- [5. Two squares](05-two.md)
  - [Theorem 5.1 (two squares)](05-two.md#theorem-51-two-squares)
  - [5.1 Construction](05-two.md#51-construction)
  - [5.2 The centres](05-two.md#52-the-centres)
  - [5.3 The shared edge](05-two.md#53-the-shared-edge)
  - [5.4 Proof of Theorem 5.1](05-two.md#54-proof-of-theorem-51)
- [6. Three squares](06-three.md)
  - [Theorem 6.1 (three squares)](06-three.md#theorem-61-three-squares)
  - [6.1 Construction](06-three.md#61-construction)
  - [6.2 The contact polygon](06-three.md#62-the-contact-polygon)
  - [6.3 Exterior squares](06-three.md#63-exterior-squares)
  - [6.4 The containing square](06-three.md#64-the-containing-square)
  - [6.5 The T](06-three.md#65-the-t)
  - [6.6 Proof of Theorem 6.1](06-three.md#66-proof-of-theorem-61)
- [7. Four squares](07-four.md)
  - [Theorem 7.1 (four squares)](07-four.md#theorem-71-four-squares)
  - [7.1 Construction](07-four.md#71-construction)
  - [7.2 The diamond](07-four.md#72-the-diamond)
  - [7.3 Arcs of the squares](07-four.md#73-arcs-of-the-squares)
  - [7.4 The block](07-four.md#74-the-block)
  - [7.5 Proof of Theorem 7.1](07-four.md#75-proof-of-theorem-71)
- [8. Five squares](08-five.md)
  - [Theorem 8.1 (five squares)](08-five.md#theorem-81-five-squares)
  - [8.1 Construction](08-five.md#81-construction)
  - [8.2 The 12-gon](08-five.md#82-the-12-gon)
  - [8.3 Exterior squares](08-five.md#83-exterior-squares)
  - [8.4 A centred square](08-five.md#84-a-centred-square)
  - [8.5 The plus](08-five.md#85-the-plus)
  - [8.6 Proof of Theorem 8.1](08-five.md#86-proof-of-theorem-81)
- [9. Six squares](09-six.md)
  - [Theorem 9.1 (six squares)](09-six.md#theorem-91-six-squares)
  - [9.1 Construction](09-six.md#91-construction)
  - [9.2 The containing square](09-six.md#92-the-containing-square)
  - [9.3 Pins and labels](09-six.md#93-pins-and-labels)
  - [9.4 Stresses](09-six.md#94-stresses)
  - [9.5 Normalized packings](09-six.md#95-normalized-packings)
  - [9.6 The separators of neighbours](09-six.md#96-the-separators-of-neighbours)
  - [9.7 The tails](09-six.md#97-the-tails)
  - [9.8 The stress of the model](09-six.md#98-the-stress-of-the-model)
  - [9.9 The eight contacts](09-six.md#99-the-eight-contacts)
  - [9.10 Proof of Theorem 9.1](09-six.md#910-proof-of-theorem-91)
- [10. Seven squares](10-seven.md)
  - [Theorem 10.1 (seven squares)](10-seven.md#theorem-101-seven-squares)
  - [10.1 Construction](10-seven.md#101-construction)
  - [10.2 States, labels and markers](10-seven.md#102-states-labels-and-markers)
  - [10.3 The canonical pair](10-seven.md#103-the-canonical-pair)
  - [10.4 Contacts and the critical gap](10-seven.md#104-contacts-and-the-critical-gap)
  - [10.5 Marker separation](10-seven.md#105-marker-separation)
  - [10.6 The ring](10-seven.md#106-the-ring)
  - [10.7 The middle column](10-seven.md#107-the-middle-column)
  - [10.8 Proof of Theorem 10.1](10-seven.md#108-proof-of-theorem-101)
- [Appendix A. One-variable estimates](appendix-a.md)
  - [A.1 Monotonicity and concavity](appendix-a.md#a1-monotonicity-and-concavity)
  - [A.2 Sine and cosine](appendix-a.md#a2-sine-and-cosine)
  - [A.3 A peak](appendix-a.md#a3-a-peak)
  - [A.4 Concave functions and harmonics](appendix-a.md#a4-concave-functions-and-harmonics)
- [Appendix B. Six squares: the normalization](appendix-b.md)
  - [B.1 Proof of Lemma 9.14](appendix-b.md#b1-proof-of-lemma-914)
  - [B.2 Proof of Lemma 9.17](appendix-b.md#b2-proof-of-lemma-917)
  - [B.3 Proof of Lemma 9.20](appendix-b.md#b3-proof-of-lemma-920)
  - [B.4 Proof of Lemma 9.26](appendix-b.md#b4-proof-of-lemma-926)
  - [B.5 Proof of Proposition 9.33](appendix-b.md#b5-proof-of-proposition-933)
- [Appendix C. Six squares: the separators](appendix-c.md)
  - [C.1 Proof of Lemma 9.37](appendix-c.md#c1-proof-of-lemma-937)
  - [C.2 Proof of Lemma 9.38](appendix-c.md#c2-proof-of-lemma-938)
  - [C.3 Proof of Proposition 9.39](appendix-c.md#c3-proof-of-proposition-939)
  - [C.4 Proof of Lemma 9.40](appendix-c.md#c4-proof-of-lemma-940)
  - [C.5 Proof of Proposition 9.41](appendix-c.md#c5-proof-of-proposition-941)
  - [C.6 Proof of Lemma 9.42](appendix-c.md#c6-proof-of-lemma-942)
  - [C.7 Proof of Lemma 9.43](appendix-c.md#c7-proof-of-lemma-943)
- [Appendix D. Six squares: the wings](appendix-d.md)
  - [D.1 The wings in coordinates](appendix-d.md#d1-the-wings-in-coordinates)
  - [D.2 The chord term](appendix-d.md#d2-the-chord-term)
  - [D.3 The gap of W and D](appendix-d.md#d3-the-gap-of-w-and-d)
  - [D.4 The range of a missing west wing](appendix-d.md#d4-the-range-of-a-missing-west-wing)
  - [D.5 W on the west side of C](appendix-d.md#d5-w-on-the-west-side-of-c)
  - [D.6 W on its own axis, S on the south side of C](appendix-d.md#d6-w-on-its-own-axis-s-on-the-south-side-of-c)
  - [D.7 Own wings, S turned at least as far as W](appendix-d.md#d7-own-wings-s-turned-at-least-as-far-as-w)
  - [D.8 Own wings, W turned at least as far as S](appendix-d.md#d8-own-wings-w-turned-at-least-as-far-as-s)
  - [D.9 A missing west wing with W on its own axis](appendix-d.md#d9-a-missing-west-wing-with-w-on-its-own-axis)
  - [D.10 Proof of Proposition 9.46](appendix-d.md#d10-proof-of-proposition-946)
- [Appendix E. Six squares: the tails and the stress of the model](appendix-e.md)
  - [E.1 Proof of Proposition 9.47](appendix-e.md#e1-proof-of-proposition-947)
  - [E.2 Proof of Proposition 9.50](appendix-e.md#e2-proof-of-proposition-950)
  - [E.3 Proof of Proposition 9.53](appendix-e.md#e3-proof-of-proposition-953)
- [Appendix F. Seven squares: the marker arc](appendix-f.md)
  - [F.1 Proof of Lemma 10.9](appendix-f.md#f1-proof-of-lemma-109)
- [Appendix G. Seven squares: the critical gap, set-up and the easy axes](appendix-g.md)
  - [G.1 The plan](appendix-g.md#g1-the-plan)
  - [G.2 Support sums in closed form](appendix-g.md#g2-support-sums-in-closed-form)
  - [G.3 The label regions and their boundary](appendix-g.md#g3-the-label-regions-and-their-boundary)
  - [G.4 Segments of constant label](appendix-g.md#g4-segments-of-constant-label)
  - [G.5 Profiles along the boundary](appendix-g.md#g5-profiles-along-the-boundary)
  - [G.6 The target support on the axial boundary](appendix-g.md#g6-the-target-support-on-the-axial-boundary)
  - [G.7 The easy sectors](appendix-g.md#g7-the-easy-sectors)
  - [G.8 The capped labels](appendix-g.md#g8-the-capped-labels)
  - [G.9 Proof of Proposition 10.17](appendix-g.md#g9-proof-of-proposition-1017)
- [Appendix H. Seven squares: the critical gap, the inward axis](appendix-h.md)
  - [H.1 The inward support sum](appendix-h.md#h1-the-inward-support-sum)
  - [H.2 Two profiles of the turn](appendix-h.md#h2-two-profiles-of-the-turn)
  - [H.3 Signs (+, +) with an axial target](appendix-h.md#h3-signs---with-an-axial-target)
  - [H.4 Signs (+, +) with a side target](appendix-h.md#h4-signs---with-a-side-target)
  - [H.5 Signs (+, −): the closed form and a nonpositive turn](appendix-h.md#h5-signs---the-closed-form-and-a-nonpositive-turn)
  - [H.6 The boundary of the label regions](appendix-h.md#h6-the-boundary-of-the-label-regions)
  - [H.7 Two circles](appendix-h.md#h7-two-circles)
  - [H.8 Minima on the boundary](appendix-h.md#h8-minima-on-the-boundary)
  - [H.9 Signs (+, −) with active labels](appendix-h.md#h9-signs---with-active-labels)
- [Appendix I. Seven squares: the critical gap, the forward axis](appendix-i.md)
  - [I.1 The forward support sum and the tools](appendix-i.md#i1-the-forward-support-sum-and-the-tools)
  - [I.2 Target sign negative](appendix-i.md#i2-target-sign-negative)
  - [I.3 Opposite signs](appendix-i.md#i3-opposite-signs)
  - [I.4 Both signs negative](appendix-i.md#i4-both-signs-negative)

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
*Squares in Circles* page [1]. We prove that seven of them are optimal, and
find all optimal packings in those seven cases.

### 1.2 The main theorem

The precise definitions of a packing, of a model and of congruence to a model
are Definitions 2.3 and 2.6. A *model* is a configuration of unit squares
placed about the origin, and a packing is *congruent* to it if one rotation
about the disk centre and one relabelling of the squares carry the model,
placed at the disk centre, onto the packing. Write $Q(c)$ for the
axis-parallel unit square centred at $c$ (Definition 2.2), and $Q^\diamond(c)$
for the unit square centred at $c$ and turned by $\frac\pi4$. Table 1.1 lists
the optimal radii and models, and Figure 1.1 draws them.

| $n$ | $R_n$ | $R_n \approx$ | centres $c_1, \dots, c_n$ of the optimal models | the optimal packing |
| :-: | :-: | :-: | --- | --- |
| 1 | $\frac{\sqrt2}2$ | 0.7071 | $(0, 0)$ | the square |
| 2 | $\frac{\sqrt5}2$ | 1.1180 | $(-\frac12, 0)$, $(\frac12, 0)$ | the $2 \times 1$ rectangle |
| 3 | $\frac{5\sqrt{17}}{16}$ | 1.2885 | $(-\frac12, -\frac5{16})$, $(\frac12, -\frac5{16})$, $(0, \frac{11}{16})$ | the T |
| 4 | $\sqrt2$ | 1.4142 | $(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$, $(\frac12, -\frac12)$ | the $2 \times 2$ block |
| 5 | $\sqrt{5/2}$ | 1.5811 | $(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$ | the plus |
| 6 | $\sqrt{q_*}$ | 1.6885 | $(s_*, s_*)$, $(s_*, s_* + 1)$, $(s_* + 1, s_*)$, $(s_* - 1, t_*)$, $(t_*, s_* - 1)$, $(-d_*, -d_*)$ | a square with four neighbours, two of them pushed along its sides, and a turned square between those two |
| 7 | $\frac{\sqrt{13}}2$ | 1.8028 | $(1, -\frac12)$, $(1, \frac12)$, $(-1, -\frac12)$, $(-1, \frac12)$, $(0, y_1)$, $(0, y_2)$, $(0, y_3)$ | the column packings |

*Table 1.1.* The optimal radii and the optimal models $Q(c_1), \dots, Q(c_n)$.
For $n \le 6$ there is one optimal model; for $n = 6$ its sixth square is the
turned square $Q^\diamond(-d_*, -d_*)$, and the numbers $s_* \approx 0.0842$,
$t_* \approx 0.4202$, $d_* \approx 0.7869$ and $q_* \approx 2.8512$ are given
in closed form in Theorem 9.1. For $n = 7$ the optimal models are the *column
packings*, one for each choice of heights with $y_1 + 1 \le y_2$,
$y_2 + 1 \le y_3$ and $-(\sqrt3 - \frac12) \le y_1$, $y_3 \le \sqrt3 - \frac12$.

![The seven optimal packings side by side at a common scale, each in its dashed circle of radius R_n: one square; two squares forming a 2 by 1 rectangle; the T of three squares; the 2 by 2 block of four; the plus of five; six squares, a square with four neighbours, two of them pushed along its sides, and a square turned by 45 degrees between those two; and seven squares, two columns of two beside a column of three. Dots mark the corners that lie on the circles](figures/01-introduction/optimal.svg)

*Figure 1.1.* The optimal packings of $n = 1, \dots, 7$ unit squares, each in
its circle of radius $R_n$, at a common scale; for $n = 7$ the column packing
with the heights $(-1, 0, 1)$. Dots mark the corners on the circle; for
$n = 6$ two of them are vertices of the turned square.

#### Theorem 1.1 (main theorem)

Let $1 \le n \le 7$, and let $R_n$ and the optimal models be as in
Table 1.1.

1. $R_n$ is the least radius of a closed disk that holds a packing of $n$ unit
   squares.
2. The packings of $n$ unit squares in a closed disk of radius $R_n$ are
   exactly the configurations congruent to an optimal model.

*Proof.* For $n = 1, \dots, 7$ this is Theorem 4.1, 5.1, 6.1, 7.1, 8.1, 9.1
and 10.1 respectively: parts (1) and (2) of each give the attainment and the
lower bound of (1) here, and part (3) gives (2). $\square$

*Lean: [`optimal_radius`](../../SquaresInCircles.lean#L51),
[`optimal_packings`](../../SquaresInCircles.lean#L57),
[`optimal_packings_rigid`](../../SquaresInCircles.lean#L65),
[`optimalRadius`](../../SquaresInCircles/Geometry.lean#L272),
[`optimalPackings`](../../SquaresInCircles/Geometry.lean#L286).*

*Remarks.* (i) For $n \le 6$ the theorem says that the optimal packing is
unique up to a rotation about the disk centre and a relabelling of the
squares. Reflections are not needed, since every optimal model is symmetric
under a reflection in a line through the origin; for $n = 6$ it is the
diagonal $y = x$. (ii) For $n = 7$ the optimum is not unique. The four side
squares are fixed, but each of the three middle squares can move along the
middle column on its own, as long as their centres stay at least 1 apart and
within $\sqrt3 - \frac12$ of the disk centre; the total slack is
$2\sqrt3 - 3 \approx 0.464$. So the optimal packings form a three-parameter
family, and infinitely many of them are pairwise not congruent (Figure 1.2).
(iii) The cases $n \ge 8$ are not treated here.

![Four optimal packings of seven unit squares in the circle of radius root 13 over 2 about o. In each, the four side squares are the same, and the three middle squares sit at different heights along the dotted middle column: centred at -1, 0, 1; with the lower two pushed to the bottom; with only the bottom square moved down; and with the middle square moved up and the top square near the top of its range](figures/01-introduction/columns.svg)

*Figure 1.2.* Four optimal packings of seven squares, with middle heights
$(-1, 0, 1)$, $(\frac12 - \sqrt3, \frac32 - \sqrt3, 1)$, $(-1.2, 0, 1)$ and
$(-1, 0.2, 1.23)$. The side squares are fixed; each middle square moves on its
own along the dotted column $[-\frac12, \frac12] \times [-\sqrt3, \sqrt3]$.

### 1.3 Background

The packings of Table 1.1 are listed on Friedman's page [1], which has collected
the best known packings of squares in a circle since 1997; the packings of
three, five, six and seven squares were found by Friedman in 1997, and the
exact radius of the packing of six squares by David Ellsworth in 2023. One and
two squares are folklore, listed there as trivial. For three squares, Montanher,
Neumaier, Markót, Domes and Schichl [2] enclosed the optimal radius in an
interval of width $6 \cdot 10^{-14}$ that contains $\frac{5\sqrt{17}}{16}$, and
every optimal arrangement in small boxes near the T, by a computer-assisted
interval branch-and-bound search; their enclosure does not determine the radius
exactly and does not show that the T itself is optimal. Four squares were
Problem 6 of the 4th International Mathematics Summer Camp (IMSC 2026), whose
official solution [7] proves the radius; an unpublished note by Wei Zhao [8]
also proves that the block is the only optimal packing, by the argument of
[Chapter 7](07-four.md). The argument here was reached without the note, but
both came out of work with Claude, so the two may not be independent. We found
no earlier proof for five, six or seven squares, whose packings in Table 1.1
were listed only as the best known ones.

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
disk would also be a packing at the radius $R_n$, so by (c) it would be
congruent to an optimal model, and by (b) it would not fit in the smaller disk
(Proposition 2.9, Figure 1.3). All the work is in (c), uniqueness at the
optimal radius.

![The plus of five squares turned about the disk centre o inside its dashed circle of radius R_5, with a smaller solid circle of radius R about o; the eight outer corners lie on the dashed circle, and the parts of the squares outside the smaller circle are highlighted in red](figures/01-introduction/reduction.svg)

*Figure 1.3.* The plus, turned about $o$, reaches its circle of radius $R_5$
at eight corners, so it does not fit in a smaller disk: the parts highlighted
in red stick out. Every packing at the radius $R_5$ is a copy of it, so no
packing fits in a smaller disk.

**The disk constraint.** Whether a square $S$ fits in a disk about $o$
depends only on two numbers $a_S \ge b_S \ge 0$, the offsets of $o$ from the
centre of $S$ along the axes of $S$ (Definition 3.1): $S$ lies in the closed
disk of radius $R$ about $o$ exactly when its vertex farthest from $o$ does,
that is, when
$\varphi(a_S, b_S) = (a_S + \frac12)^2 + (b_S + \frac12)^2 \le R^2$
(Lemma 3.4, Figure 1.4). Every uniqueness proof uses the disk only through
these inequalities, one for each square.

![Left: a square S in the dashed circle of radius R = root 2 about o; from the centre c_S of S, the disk centre o is a_S along one axis of S and b_S along the other, and a dashed segment of length root phi(a_S, b_S) joins o to the vertex of S farthest from it. Right: the (a, b)-plane with the part, where a and b are nonnegative, of the disk phi at most 2, the dotted diagonal a = b, the point (a_S, b_S) below the diagonal inside the disk, and the dashed tangent line a + b = 1 touching the disk at (1/2, 1/2)](figures/01-introduction/disk-constraint.svg)

*Figure 1.4.* The disk constraint at the radius $R = \sqrt2$ of four squares,
for a square with $(a_S, b_S) = (0.62, 0.25)$. Left: from the centre $c_S$,
the disk centre $o$ is $a_S$ along one axis of $S$ and $b_S$ along the other;
the vertex of $S$ farthest from $o$ (dot) is at distance
$\sqrt{\varphi(a_S, b_S)} \le \sqrt2$. Right: in the $(a, b)$-plane the
constraint puts $(a_S, b_S)$ in the disk $\lbrace \varphi \le 2 \rbrace$ of
radius $\sqrt2$ about $(-\frac12, -\frac12)$ (blue). Its tangent $a + b = 1$
at $(\frac12, \frac12)$ (dashed) bounds the contact polygon of four squares,
the diamond $a + b \le 1$ (Table 1.2).

**One and two squares** (Chapters 4 and 5). At the radius $R_1$ the
inequality forces $a_S = b_S = 0$: the square is centred at the disk centre.
At the radius $R_2$ it keeps both centres within $\frac12$ of the disk centre,
while the centres of disjoint squares are at least 1 apart; so the centres are
exactly 1 apart, with the disk centre as their midpoint. Disjoint squares
whose centres are 1 apart share a full edge (Lemma 3.13), and that is the
rectangle (Figure 1.5).

![Two squares S and T forming a 2 by 1 rectangle in the dashed circle of radius R_2 about o. Their centres c_S and c_T lie on the dashed circle of radius 1/2 about o, at the ends of a horizontal diameter of length 1, and the edge the two squares share, through o, is drawn thick](figures/01-introduction/two.svg)

*Figure 1.5.* Two squares at the radius $R_2$. Both centres lie within
$\frac12$ of $o$ and at least 1 apart, so they are exactly 1 apart, at the
ends of a diameter of the circle $\Gamma_{1/2}$ of radius $\frac12$ about $o$.
Squares whose centres are 1 apart share a full edge (thick), so the squares
form the rectangle.

**Three to five squares** (Chapters 6 to 8). These cases share one method,
run once at the optimal radius. Take a packing in the closed disk of radius
$R_n$.

1. *The contact polygon.* The inequality $\varphi(a_S, b_S) \le R_n^2$ is
   curved. The tangent lines of the circle $\varphi = R_n^2$ at the pairs
   $(a_S, b_S)$ of the optimal packing, and for five squares at one more
   point, turn it into a polygon (Lemma 3.6, Figure 1.4). From here on the
   disk is forgotten, except for four squares.
2. *Exterior squares.* On a small auxiliary circle about the disk centre,
   every square that does not contain the centre holds an arc of at least
   $\frac{2\pi}n$, and for three and four squares exactly $\frac{2\pi}n$ only
   in the positions of the optimal packing (Figure 1.6).
3. *The containing square.* At most one square contains the disk centre. Its
   own arc can be short, and each case deals with it separately.
4. *The budget.* The arcs of disjoint squares cannot take up more than the
   whole circle (Lemma 3.16). For three and four squares every arc is then as
   short as it can be, and those positions rebuild the optimal packing. For
   five squares the budget leaves only a square centred at the disk centre,
   and that forces the plus.

![Two panels, each with a square in the dashed circle of radius root 2 and the circle of radius 1/2 about the disk centre o. Left: a square that avoids o, without a vertex at o, holds a highlighted arc of more than 90 degrees of the small circle, labelled Gamma 1/2. Right: a square containing o holds the highlighted quarter of the small circle that faces its centre](figures/01-introduction/arc-method.svg)

*Figure 1.6.* The method of arcs for four squares and the circle
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

**Six squares** (Chapter 9 and Appendices B to E). The optimal packing has a
square turned by $\frac\pi4$, and the arcs only start the proof; the rest adds
separating inequalities. Take a packing in a closed disk of radius $R_6$.

1. *The containing square.* On the circle $\Gamma_{9/10}$ every square that
   avoids the disk centre holds an arc of more than a sixth of the circle, so
   one square contains the disk centre (Figure 1.7); read in its frame, its
   centre lies in a small box.
2. *Pins.* Five fixed points at distance $\frac9{10}$ from the disk centre,
   the *pins*, label the other squares $E$, $N$, $W$, $D$, $S$ in
   counterclockwise order. Each holds its pin, points in a window of
   directions, and is separated from the containing square only along its own
   axis or along a side of the containing square that faces its pin.
3. *Stresses.* A weighted sum of separating inequalities is a sum of works of
   forces on the centres, and the disk bounds each work. In the optimal
   packing eight pairs of squares touch, and weights on these contacts
   balance: the forces cancel on the containing square, push $E$, $N$, $W$
   and $S$ along the radii to their corners on the circle and push the turned
   square $D$ along the diagonal (Figure 1.8).
4. *The separators.* Further stresses, with estimates uniform over whole
   intervals of the angles of the squares, show that the turned square is
   separated from the containing square along its own axis and from its two
   neighbours as in the optimal packing, and bound the angles of the squares.
   These estimates fill Appendices B to E.
5. *Equality.* With these separators the stress of the optimal packing leaves
   no room at the radius $R_6$: every square is turned as in the optimal
   packing, the eight contacts hold, and they fix every centre.

![The optimal packing of six squares with the dotted circle of radius 9/10 about o. The grey central square C contains o and misses the circle; each of the five other squares, N, E, S, D and W, holds a thick arc of the circle, of more than 60 degrees, and the five pins, drawn as dots on the circle, lie one in each of these arcs](figures/01-introduction/pins.svg)

*Figure 1.7.* Steps 1 and 2 in the optimal packing. On $\Gamma_{9/10}$
(dotted) each square that avoids $o$ holds an arc of more than a sixth of the
circle (thick). Six such arcs do not fit, so one square, $C$ (grey), contains
$o$. The five pins (dots) lie one in each of the other squares and name them
$E$, $N$, $W$, $D$, $S$.

![The six-square model in its dashed circle with the eight edges of its stress drawn as thin arrows between the centres, labelled with their weights, and the forces as thick arrows: none on the central square, the forces on its four axis-parallel neighbours parallel to the dotted radii to their corners on the circle, and the force on the turned square pointing along the diagonal, away from the disk centre](figures/09-six/stress.svg)

*Figure 1.8.* The stress of the optimal packing of six squares: its eight
edges (thin arrows) with their weights $1$, $r_*$ and $m_*$, and the forces
(thick arrows). The forces cancel on the central square $C$, push $E$, $N$,
$W$ and $S$ along the radii to their corners on the circle (dotted) and push
$D$ along the diagonal, midway between its two vertices on the circle. The disk bounds the
work of each force, and these bounds add up exactly to the weighted sum of the
thresholds.

**Seven squares** (Chapter 10 and Appendices F to I). This case compares pairs
of squares rather than arcs of one circle. Take a packing in the closed disk
of radius $R_7$.

1. *Markers.* Each square that avoids the disk centre gets a marker, a
   direction from the disk centre computed from the position of the disk
   centre relative to the square. The closed square contains the arc of the
   unit circle of half-width $\frac12$ about its marker.
2. *Marker separation.* Two disjoint such squares have markers at least
   $\frac\pi3$ apart, and exactly $\frac\pi3$ apart only if they touch as in
   an optimal packing (Figure 1.9). The proof reads the pair in the frame of
   one square, writes the overlaps of their shadows on the edge directions in
   closed form, and shows that these are positive for every gap below
   $\frac\pi3$ and vanish at $\frac\pi3$ only at those contacts. The case
   analysis at the gap $\frac\pi3$ fills Appendices G to I.
3. *The ring.* Seven markers do not fit, so some square contains the disk
   centre. The markers of the other six form a regular hexagon, and going
   round it each square touches the next as in an optimal packing: two side
   columns, one square above the centre and one below.
4. *The middle column.* The side columns pin the square that contains the
   centre to the middle column. The three squares of that column need only
   stay 1 apart, so each can move along it on its own.

![Markers of seven squares, on the unit circle about the disk centre. Left: two touching squares, a side square and the top square, with their markers drawn as directions from the disk centre exactly pi/3 apart and, about each marker, a thick arc of the unit circle inside its square. Middle: the same pair turned so that their markers are closer, where the squares and their arcs overlap. Right: a column packing whose six exterior squares have markers forming a regular hexagon](figures/01-introduction/markers.svg)

*Figure 1.9.* Markers of seven squares. A side square and the top square that
touch as in an optimal packing have markers exactly $\frac\pi3$ apart, and
each contains the arc of half-width $\frac12$ of the unit circle about its
marker (thick); turned closer, the squares overlap. In every column packing
the six markers form a regular hexagon.

### 1.5 This text and the formalization

Chapters 2 and 3 contain the definitions and the tools shared by several cases;
each of Chapters 4 to 10 proves one case, and the appendices hold the long
computations: Appendix A the one-variable estimates, Appendices B to E those of
six squares and Appendices F to I those of seven squares. Definitions, lemmas,
propositions, theorems and corollaries are numbered together within each
chapter; figures, tables and tagged equations are numbered separately.
Sections are cited as §3.4. Proofs end with $\square$.

Every numbered statement ends with a line *Lean: …* naming the Lean 4
declarations [5, 6] that state and prove it, linked to their source. The proofs
in this text follow the formal proofs, but are written for a human reader:
where a formal proof closes an inequality by an automatic procedure, the text
gives an explicit identity, sum of squares or chain of elementary estimates
that can be checked by hand or with a computer algebra system. The formal
proofs themselves are checked by the Lean kernel; the
[verification](../verification.md) page explains how to build them and audit
their axioms. The figures are computed from the same geometry by the scripts
in [`scripts/figures/`](../../scripts/figures).

### References

1. E. Friedman. Squares in Circles. Erich's Packing Center,
   <https://erich-friedman.github.io/packing/squincir/> (accessed September
   2026).
2. T. Montanher, A. Neumaier, M. C. Markót, F. Domes, H. Schichl. Rigorous
   packing of unit squares into a circle. *J. Global Optim.* 73 (2019)
   547–565. [doi:10.1007/s10898-018-0711-5](https://doi.org/10.1007/s10898-018-0711-5)
3. T. Hales et al. A formal proof of the Kepler conjecture.
   *Forum Math. Pi* 5 (2017) e2. [doi:10.1017/fmp.2017.1](https://doi.org/10.1017/fmp.2017.1)
4. S. Hariharan, C. Birkbeck, S. Lee, H. K. G. Ma, B. Mehta, A. Poiroux,
   M. Viazovska. Progress in formalizing sphere packing in dimension 8.
   [arXiv:2604.23468](https://arxiv.org/abs/2604.23468) (2026).
5. The mathlib Community. The Lean mathematical library. In *Proceedings of
   the 9th ACM SIGPLAN International Conference on Certified Programs and
   Proofs (CPP 2020)*, 367–381. [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824)
6. L. de Moura, S. Ullrich. The Lean 4 theorem prover and programming
   language. In *Automated Deduction – CADE 28*, Lecture Notes in Computer
   Science 12699 (2021), 625–635. [doi:10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37)
7. The 4th International Mathematics Summer Camp (IMSC 2026). *Marking Schemes
   and Solutions*, Day 2, Problem 6. July 2026. Not public.
8. W. Zhao. Four congruent squares in a unit disk: an elementary proof that
   $s_{\max} = \frac{\sqrt2}{2}$. Unpublished note, 6 July 2026, shared with us
   by E. Friedman.
