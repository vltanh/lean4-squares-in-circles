# Nine squares in a circle: table-free geometric core

**Status (2026-10-22): a proved *conditional* hand theorem, not an unrestricted n=9 proof.** 
The proof below is elementary and uses no numerical search, finite interval-cover
tables, certificate generators, or Lean elaboration. The remaining obstruction is
to remove the horizontal-layer/common-frame hypothesis. In particular, this
document does **not** claim that every nine-square packing can be layered.

## 1. Target, model, and geometric meaning

Let \(q=R^2\). The record construction for nine freely rotatable unit
squares uses

\[
 q_*=\frac{1105}{256},\qquad R_*=\frac{\sqrt{1105}}{16}.
\]

The disk center is the origin. The following nine axis-parallel unit squares,
specified by their centers, fit the disk of squared radius \(q_*\):

\[
\begin{array}{c|c|c}
 \text{group} & \text{horizontal centers }x&\text{height }y\\ \hline
 T\;(2)&-1/2,\;1/2&17/16\\
 M\;(4)&-3/2,\;-1/2,\;1/2,\;3/2&1/16\\
 B\;(3)&-1,\;0,\;1&-15/16 .
\end{array}
\tag{1}
\]

In any single group, horizontal center gaps are at least 1. Between groups,
the vertical center gaps are exactly 1, so square interiors never overlap.
For an axis-parallel unit square with center \((x,y)\), the largest squared
distance of a corner from the origin is

\[
 F(x,y)=\bigl(|x|+\tfrac12\bigr)^2+
              \bigl(|y|+\tfrac12\bigr)^2. \tag{2}
\]

The maximum in each group is

\[
 F_T=1+(25/16)^2=\frac{881}{256},\quad
 F_M=4+(9/16)^2=\frac{1105}{256},\quad
 F_B=(3/2)^2+(23/16)^2=\frac{1105}{256}. \tag{3}
\]

Thus (1) is an exact construction. Rotating/translating the entire
construction changes nothing.

The familiar record picture is a tilted *global* copy of (1), not evidence
that the nine individual orientations are forced to agree. Compare
[Erich Friedman's record](https://erich-friedman.github.io/packing/squincir/)
and the repository's unrestricted
[packing definition](../../SquaresInCircles/Geometry.lean).

## 2. Terminology; precise scope

All squares in the elementary lemmas below are axis-parallel in *one common
orthonormal frame*. A set \(A\) of squares is **horizontally separated** if
the interiors of their projections onto the horizontal axis are pairwise
disjoint. Equivalently, the centers of distinct members of \(A\) satisfy
\(|x_i-x_j|\ge1\).

For groups \(A,B\), write \(A\prec B\) if **every** center of \(B\) is at
least 1 above **every** center of \(A\):

\[
    y_b-y_a\ge1\qquad(a\in A,\ b\in B). \tag{4}
\]

This suffices for disjoint interiors between the two groups.

A **horizontally stratified packing** consists of nonempty, disjoint groups
\(L_1,\ldots,L_k\), partitioning the squares, such that each group is
horizontally separated and \(L_i\prec L_{i+1}\). Neither equal heights
within a group nor actual edge contacts are assumed. By transitivity,
\[
 y_b-y_a\ge j-i\quad
 (a\in L_i,\ b\in L_j,\ i<j). \tag{5}
\]
This is a significant *hypothesis*, not an automatic consequence of
pairwise nonoverlap.

## 3. The four elementary capacity bounds

**Lemma 3.1 (horizontal witnesses).**
Suppose \(m\) axis-parallel unit squares are horizontally separated and
lie in a disk centered at 0 with squared radius \(q\). Then one of their
centers \((x,y)\) satisfies

\[
 |x|\ge\frac{m-1}{2},\qquad
 q\ge \frac{m^2}{4}+
                   \bigl(|y|+\tfrac12\bigr)^2. \tag{6}
\]

*Proof.* Order their center coordinates
\(x_1\le\cdots\le x_m\). All consecutive differences are at least 1,
so \(x_m-x_1\ge m-1\). Thus
\(\max(|x_1|,|x_m|)\ge(m-1)/2\). Apply (2) to that endpoint.
\(\square\)

**Corollary 3.2 (capacity bands at the proposed radius).**
If \(q\le q_*=1105/256\), then:

1. Every square center satisfies \(|y|<25/16\).
2. Every horizontally separated group contains at most four squares.
3. A group of at least two squares has a witness with \(|y|<11/8\).
4. A group of at least three has a witness with \(|y|\le15/16\).
5. A group of four has a witness with \(|y|\le1/16\).

*Proof.* For one square,
\[
 (|y|+1/2)^2\le q_*-1/4=1041/256<(33/16)^2,
\]
so \(|y|<25/16\). A horizontally separated group of five would
force \(q\ge(5/2)^2+(1/2)^2=13/2>q_*\).
For a group of two, (6) gives
\[
 (|y|+1/2)^2\le q_*-1=849/256<(30/16)^2
\]
and hence \(|y|<22/16=11/8\). For three and four, respectively,
\[
 (|y|+1/2)^2\le q_*-9/4=529/256=(23/16)^2,
\]
\[
 (|y|+1/2)^2\le q_*-4=81/256=(9/16)^2.
\]
Subtract \(1/2\) in each case. \(\square\)

The numerical constants here are exact fractions explained by a single
corner equation; none comes from an interval search.

## 4. The decisive 4-over-3 obstruction

**Theorem 4.1 (seven-anchor obstruction).**
Suppose seven of the squares of any packing share one orientation.
Four form a horizontally separated group \(M\), three form a
horizontally separated group \(B\), and \(B\prec M\) in their common frame.
Then the containing disk has

\[
                         R^2\ge\frac{1105}{256}. \tag{7}
\]

Any *other* squares in the packing are unrestricted, including their
orientations. No equal-height assumption is made on the seven anchors.

*Proof.* If \(q>q_*\), there is nothing to prove, so assume \(q\le q_*\).
Choose a witness \(b\in B\) from Corollary 3.2(4):
\(|y_b|\le15/16\), so \(y_b\ge-15/16\).
Since \(B\prec M\), **every** \(m\in M\) obeys
\[
                    y_m\ge y_b+1\ge1/16. \tag{8}
\]
Choose a witness \(m_0\in M\) from Corollary 3.2(5):
\(|y_{m_0}|\le1/16\). Combined with (8), this gives
\(y_{m_0}=1/16\), and equality must also hold
\(y_b=-15/16\).

For this witness, \(|x_{m_0}|\ge3/2\), hence the outer corner of
its square gives
\[
 q\ge (2)^2+(1/16+1/2)^2
   =4+(9/16)^2=q_*.
\]
If \(q<q_*\) this is a contradiction; if \(q=q_*\) all
identified bounds are sharp. \(\square\)

Reflection across the horizontal axis gives the identical **3-over-4**
statement.

**Why this is useful.** We have an exact, *locally robust* obstruction:
the third square in \(B\) and the fourth in \(M\) may be staggered at
different vertical heights, and the remaining two squares of a
nine-square packing may turn freely. The theorem needs only one common
frame for these seven anchors and the indicated separating directions.

## 5. Complete classification of the stratified case

**Theorem 5.1 (sharp stratified n=9 theorem).**
Every packing of nine axis-parallel unit squares that admits a
horizontal stratification has
\[
                 R\ge\frac{\sqrt{1105}}{16}. \tag{9}
\]
Construction (1) attains equality. Moreover, at equality every such
stratification has exactly three layers. From bottom to top, the layer
sizes are either \((3,4,2)\) or \((2,4,3)\), and the middle and three-square
layers contain the pinned anchors described in Theorem 6.1 below.

*Proof.* Suppose \(q\le q_*\) and a stratification has
nonempty layers \(L_1,\ldots,L_k\), of sizes \(m_i\), summing to nine.
Corollary 3.2 implies \(m_i\le4\).

- **One or two layers:** at most \(4+4=8\) squares.
- **At least five layers:** by (5), any first-layer and last-layer
  centers have vertical difference at least 4. But every center lies
  strictly between \(-25/16\) and \(25/16\), so their difference is
  strictly less than \(50/16<4\).
- **Four layers:** by (5), every first-layer center has
  \(y<25/16-3=-23/16\), and every last-layer center has
  \(y>-25/16+3=23/16\). Since \(23/16>11/8\), the two extreme
  layers cannot have two squares; by Corollary 3.2(3), each has
  exactly one. Every center in the second layer has
  \(y<25/16-2=-7/16\), and every center in the third layer has
  \(y>-25/16+2=7/16\). Neither middle layer can contain four
  squares, by Corollary 3.2(5). Total capacity is at most
  \(1+3+3+1=8\).
- **Three layers, with no layer of four:** nine squares require
  exactly \((3,3,3)\). Choose the Corollary 3.2(4) witnesses in
  the first and last layers. Both lie within vertical distance
  \(15/16\) of the origin, but (5) separates their heights by
  at least 2. Impossible, since \(30/16<2\).
- **Three layers, with a layer of four at either end:** choose its
  witness \(|y|\le1/16\). Every center in the opposite end
  layer lies at height at least 2 above it, or at least 2 below it.
  Such a center must have \(|y|\ge2-1/16=31/16>25/16\),
  contradicting Corollary 3.2(1).
- **Three layers, with the middle layer of four:** the other
  two layers contain five squares total, and individually at
  most three. Thus their sizes are 2 and 3. The middle and the
  three-square layers form a 4-over-3 or 3-over-4 pair, so
  Theorem 4.1 forces \(q\ge q_*\).

This exhaustive analysis uses only the number of layers and their
capacities, not an enumeration of geometric states. At \(q=q_*\),
every contradiction above persists, leaving precisely the two stated
size orders. Construction (1) proves attainability. \(\square\)

**Important boundary of the theorem:** this does not establish that an
arbitrary axis-parallel nine-square packing admits a stratification.
Staggered chains of overlapping vertical projections need not admit
this partition. Nor does it establish global optimality when each
square may rotate independently.

## 6. Exact rigidity of the seven anchors at equality

**Theorem 6.1 (pinned outer anchors and available sliders).**
Under the assumptions of Theorem 4.1, if \(q=q_*\), the seven
squares necessarily have these **horizontal** center coordinates:
\[
 \{x_m:m\in M\}=\{-3/2,-1/2,1/2,3/2\},\qquad
 \{x_b:b\in B\}=\{-1,0,1\}. \tag{10}
\]
Both extreme squares of the four-group have height exactly \(1/16\);
both extreme squares of the three-group have height exactly \(-15/16\).
The two interior four-group squares have heights at least \(1/16\);
the middle three-group square has height at most \(-15/16\).
All such remaining heights are constrained further by disk containment
and cross-group separation; they are *not* asserted to be free without
these conditions.

*Proof.* Theorem 4.1 supplies a \(b\in B\) at height \(-15/16\)
and \(m\in M\) at height \(1/16\). Consequently, every four-group
center has \(y\ge1/16\), and every three-group center has
\(y\le-15/16\).

By (2) and \(q=q_*\), every four-group center has
\[
 (|x|+1/2)^2\le q_*-(9/16)^2=4,
 \quad\text{so } |x|\le3/2. \tag{11}
\]
Four horizontal centers spaced at least one unit in
\([-3/2,3/2]\) must be exactly the four coordinates in (10).
At \(x=\pm3/2\), (11) is sharp, forcing \(y=1/16\).

Similarly, each three-group center obeys
\[
 (|x|+1/2)^2\le q_*-(23/16)^2=9/4,
 \quad\text{so } |x|\le1. \tag{12}
\]
Three horizontally separated centers in \([-1,1]\)
must be \(-1,0,1\), and the two extremes have
\(y=-15/16\). The inequalities for the interior squares
come from the vertical ordering. \(\square\)

This is the correct rigidity statement *within the restricted contact
pattern*. It leaves genuine potential sliding freedoms and makes no
unrestricted equality-classification claim. It also does not require
the other two squares, when present, to have the anchor orientation.

## 7. What remains for the unrestricted n=9 theorem

An unrestricted hand proof must start from the repository's
\(\mathrm{Packing}\) predicate, which allows every square to rotate
independently and imposes no row structure. The sharp obstruction
here applies only **after** a common-frame seven-anchor pattern
has been justified.

The following is the relevant dependency frontier, not a claim
that the listed statements already hold.

1. **Geometric normalization / contact-pattern dichotomy.** At
   \(q<q_*\), find a small, analytically describable set of possible
   separating-axis contact patterns. Determine whether an arbitrary
   packing can be reduced to a layered obstruction, a controlled
   perturbation of it, or another analytic contradiction. A
   universal assumption that all nine squares are parallel is
   unjustified (the two nonanchor squares may be flexible).
2. **Orientation-stable anchor inequality.** Replace the common-frame
   hypothesis of Theorem 4.1 by a geometric supporting-line or
   dual-stress inequality for independent square frames. The
   parallel case must emerge as the equality case. This is the
   main analytic target; a numerical near-parallel search alone is
   insufficient.
3. **Exclude unlayered contact patterns.** Provide a human-sized
   structural classification, not a grid subdivision of position,
   angle, and contact parameters. The stratification theorem can
   be used as a terminal lemma for the layered branch.
4. **Complete equality family.** Recover the four pinned boundary
   anchors while permitting internal vertical sliders and two
   additional nonanchor squares to translate or rotate whenever
   containment and nonoverlap allow. Do not assert uniqueness of a
   single rigid pose.

No Lean sources were changed by this document. No Lean build, CI,
or proof replay is claimed. The only unconditional assertion about
the fully unrestricted problem in this document is that construction
(1) gives the **upper** bound \(R_9\le R_*\).

## 8. A compact exact certificate to carry into Lean

The entire arithmetic of the proved core consists of

\[
\begin{aligned}
q_* &=1105/256,\\
q_*-1/4 &=1041/256 <(33/16)^2,\\
q_*-1 &=849/256 <(30/16)^2,\\
q_*-9/4 &=529/256 =(23/16)^2,\\
q_*-4 &=81/256 =(9/16)^2,\\
30/16&<2,\qquad50/16<4,\\
23/16&>11/8,\qquad31/16>25/16.
\end{aligned}
\tag{13}
\]

All other steps are ordered-coordinate, absolute-value, and
finite-layer arguments. This should be formalizable using elementary
real inequalities and finite combinatorial reasoning, without
generated tables or external certificates.
