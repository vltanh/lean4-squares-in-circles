# The proof

[Back to the README](../../README.md)

These pages give the Lean proofs as ordinary mathematics. The setting comes
first, in [preliminaries.md](preliminaries.md). The tools that several cases
share are defined and proved once in [common.md](common.md), and each case has
its own page. Every result is stated before it is proved, and ends with a link
to the Lean declarations it follows.

**How to read them.** Start with the plan below, then open a case page. Each
case page begins with a picture of the optimal packing and a sketch of the
whole argument, and each longer proof begins with its idea in a few
sentences. Look up a shared lemma or a definition only when a proof cites it;
the [notation table](preliminaries.md#notation-at-a-glance) lists every
symbol. The figures are drawn from the same geometry by
[`scripts/proof_figures.py`](../../scripts/proof_figures.py).

| page | contents |
| --- | --- |
| [preliminaries.md](preliminaries.md) | the setting: notation, conventions, and Definitions 1 to 5 (squares, packings, normal forms) |
| [common.md](common.md) | the shared toolkit: Definitions 6 to 17 and statements 1 to 22, each tool defined where it is first used |
| [one.md](one.md) | Theorem 1, one square |
| [two.md](two.md) | Theorem 2, two squares |
| [three.md](three.md) | Theorem 3, three squares |
| [four.md](four.md) | Theorem 4, four squares |
| [five.md](five.md) | Theorem 5, five squares |
| [seven.md](seven.md) | Theorem 7, seven squares |

## The main theorem

*Lean: [`optimality`](../../SquaresInCircles.lean#L71),
[`attainment`](../../SquaresInCircles.lean#L76),
[`uniqueness`](../../SquaresInCircles.lean#L88),
[`packing_iff`](../../SquaresInCircles.lean#L82),
[`optimum`](../../SquaresInCircles.lean#L55), in
[`SquaresInCircles.lean`](../../SquaresInCircles.lean).*

For $1 \le n \le 5$ and $n = 7$ let $R_n$ and $c_1, \dots, c_n$ be given by the
table.

| $n$ | $R_n$ | $c_1, \dots, c_n$ | packing |
| :-: | :-: | --- | --- |
| 1 | $\frac{\sqrt2}2$ | $(0, 0)$ | the square |
| 2 | $\frac{\sqrt5}2$ | $(-\frac12, 0)$, $(\frac12, 0)$ | the $2 \times 1$ rectangle |
| 3 | $\frac{5\sqrt{17}}{16}$ | $(-\frac12, -\frac5{16})$, $(\frac12, -\frac5{16})$, $(0, \frac{11}{16})$ | the T |
| 4 | $\sqrt2$ | $(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$, $(\frac12, -\frac12)$ | the $2 \times 2$ block |
| 5 | $\sqrt{5/2}$ | $(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$ | the plus |
| 7 | $\frac{\sqrt{13}}2$ | $(1, -\frac12)$, $(1, \frac12)$, $(-1, -\frac12)$, $(-1, \frac12)$, $(0, -1)$, $(0, 0)$, $(0, 1)$ | two columns of two beside a column of three |

**Theorem.** Let $1 \le n \le 5$ or $n = 7$.

1. *Attainment.* The axis-parallel squares $Q(c_1), \dots, Q(c_n)$ form a
   packing in the closed disk of radius $R_n$ about the origin
   (Definitions 2 and 3).
2. *Optimality.* If $n$ unit squares form a packing in a closed disk of
   radius $R$, then $R \ge R_n$.
3. *Uniqueness.* The packings of $n$ unit squares in a closed disk of radius
   $R_n$ are exactly the configurations with the normal form of an optimal
   layout (Definition 5): one rotation about the disk centre and one
   relabelling carry the layout onto them. For $n \le 5$ the only optimal
   layout is $c_1, \dots, c_n$. For $n = 7$ the optimal layouts are
   $c_1, \dots, c_4$ with $(0, y_1), (0, y_2), (0, y_3)$ for any heights that
   are at least 1 apart and within $\sqrt3 - \frac12$ of 0: the middle column
   can slide.

The case $n$ is Theorem $n$ on the page for that case. Every case proves its
three parts the same way: part 1 by an explicit construction, part 3 by its
own argument, and part 2 and the converse half of part 3 follow from these by
shared lemmas ([one framework](common.md#11-one-framework-for-every-case)).

## One and two squares

The farthest-vertex bound of
[Lemma 1](common.md#lemma-1-farthest-vertex) settles one square at once: at
radius $R_1$ it forces $\varphi(a_S, b_S) = \frac12$, so the square is centred
at the disk centre. For two squares at radius $R_2$ it keeps both centres
within $\frac12$ of the disk centre, while centres of disjoint squares are at
least 1 apart; by the parallelogram law both centres are exactly $\frac12$
away, and each square holds the half of a small circle facing it. Disjoint half
circles are opposite, and that is the rectangle. In both cases the lower bound
follows by [Lemma 22](common.md#lemma-22-the-lower-bound).

## Three to five squares

Three, four and five squares are proved by one method, run once, at the
optimal radius: it shows that every packing in the closed disk of radius $R_n$
is the optimal packing, and the lower bound follows by
[Lemma 22](common.md#lemma-22-the-lower-bound). Take such a packing.

1. **The contact polygon.** Lemma 1 gives $\varphi(a_S, b_S) \le R_n^2$ for
   every square, and the tangent half-planes of
   [Lemma 2](common.md#lemma-2-tangent-lines) at the positions of the squares
   of the optimal packing turn this curved constraint into a polygon. From here
   on the disk is forgotten, except for four squares.
2. **Exterior squares.** On a small auxiliary circle about the disk centre,
   every square that does not contain the centre holds an arc of at least
   $\frac{2\pi}n$, and for three and four squares exactly $\frac{2\pi}n$ only
   in the positions of the optimal packing.
3. **The containing square.** At most one square contains the disk centre.
   Its own arc can be short, and each case handles it separately.
4. **The budget.** The arcs of disjoint squares cannot take up more than the
   whole circle ([Lemma 7](common.md#lemma-7-angular-budget)). For three and
   four squares every arc is then as short as it can be, and those positions
   rebuild the optimal packing. For five squares the budget leaves only a
   square centred at the disk centre, and that forces the plus.

### Where the cases differ

| | three | four | five |
| --- | --- | --- | --- |
| $R_n^2$ | $\frac{425}{256}$ | $2$ | $\frac52$ |
| **1.** tangent points | $(\frac12, \frac5{16})$, $(\frac{11}{16}, 0)$ and mirrors | $(\frac12, \frac12)$ | $(1, 0)$, $(0, 1)$, $(\frac{\sqrt5-1}2, \frac{\sqrt5-1}2)$ |
| **1.** polygon | the 16-gon $P_3$ | the diamond $a + b \le 1$ | the 12-gon $P_5$ |
| **1.** disk used afterwards | no | yes, $\varphi \le 2$ | no |
| **2.** auxiliary radius | $\frac38$ | $\frac12$ | $\frac56$ |
| **2.** exterior arc | a cap of at least 120°, exactly 120° only in two positions | a cap of at least 90°, exactly 90° only with a vertex at the centre | an arc longer than 72° |
| **3.** containing square | impossible: its own arc, no clipped cap, and nearly axial caps too wide on $\Gamma_{7/16}$ | the quarter circle facing its centre | its radial sweep holds 72°, unless it is centred at the disk centre |
| **4.** budget | three caps of exactly 120° (Lemmas 7, 9) | four quarter circles (Lemma 7) | the sweep ([Proposition 15](common.md#proposition-15-budget-with-a-sweep)): a square centred at the disk centre |
| rebuilt from | angles between the caps | a quarter grid of arc centres | unit contacts with the centred square |

## Seven squares

Seven squares also run one argument at the optimal radius, but it compares
pairs of squares rather than arcs on one circle. Take a packing in the closed
disk of radius $R_7$.

1. **Markers.** Each square that avoids the disk centre gets a marker, a
   direction from the disk centre computed from the position of the centre
   relative to the square.
2. **The pair theorem.** Two disjoint such squares have markers at least
   $\frac\pi3$ apart, and exactly $\frac\pi3$ apart only if they touch as in
   the optimal packing. The proof puts the pair in a normal position, writes
   the overlaps of their shadows on the four edge directions in closed form,
   and shows that they are positive for every gap below $\frac\pi3$ and
   vanish at $\frac\pi3$ only at those contacts.
3. **The ring.** Seven markers do not fit, so some square contains the disk
   centre. The markers of the other six form a regular hexagon
   ([Lemma 20](common.md#lemma-20-regular-polygons)), and going round it each
   square touches the next as in the optimal packing: two side columns, and
   one square above the centre and one below.
4. **The middle column.** The side columns pin the square that contains the
   centre to the middle column, where it can slide with the squares above and
   below it.

The lower bound follows by [Lemma 22](common.md#lemma-22-the-lower-bound), as
for every case.

## Shared lemmas by case

The cells list the lemmas of [common.md](common.md) that each case depends
on, including those used only inside other shared lemmas. Every case also uses
Lemma 17 for its construction, Lemma 21 for the converse of uniqueness and
Lemma 22 for its lower bound, so the table lists what its uniqueness proof
uses.

| section of common.md | 1 | 2 | 3 | 4 | 5 | 7 |
| --- | :-: | :-: | :-: | :-: | :-: | :-: |
| 1. the disk centre seen from a square | 1 | 1 | 1 | 1 | 1 | 1 |
| 2. contact polygons | | | 2 | | 2 | |
| 3. two disjoint squares | | 3, 4 | | 5 | 3 to 6 | 5 |
| 4. arcs and the angular budget | | 8 | 7 to 9 | 7, 8 | 7 | 7 |
| 5. charts | 10, 11 | 10, 11 | 10, 11 | 10, 11 | 10 | 10, 11 |
| 6. arcs of an exterior square | | 12 | 12 | 12 | 12 | |
| 7. the radial sweep | | | | | 13 to 15 | |
| 8. elementary estimates | | | 16 | | 16 | 16 |
| 10. normal forms | 19 | 18, 19 | 18, 19 | 18 to 20 | 18, 19 | 18 to 20 |

## The legacy proof of three squares

The first formalization of three squares was a certificate proof by case
enumeration, kept on the `legacy` branch. It is described at the end of
[three.md](three.md#the-legacy-certificate-proof).
