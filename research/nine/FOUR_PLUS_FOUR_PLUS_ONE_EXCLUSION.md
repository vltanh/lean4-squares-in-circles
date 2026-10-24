# n=9 C3.3: eliminate the complete (4,1) two-stack complement

**Status (2026-10-22): CLOSED by a table-free hand proof.** This
proves the sharp **strict** impossibility of an entire structural
class, not a sampled family.

**Theorem.** Nine independently oriented unit squares cannot
all lie inside a disk of squared radius
\(q\le Q=1105/256\) and be pairwise coordinate-separable
in one orthonormal frame if **four** of them have pairwise
disjoint horizontal projections, **four disjoint others** have
pairwise disjoint vertical projections, and a **ninth** square
is left over.

No alignment assumption is made on any of the nine side frames.
In particular, this completely closes the residual
C3.3 / C4.3c **(4,1)** vertical-stack complement.
The eight-square crossed-chain configuration in
[CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md](CROSSED_FOUR_CHAINS_EIGHT_WITNESS.md)
is compatible with this theorem: **the ninth square is essential**.

## 1. Necessary center inequalities

Put \(\rho=61/40\), and translate the disk center to \(0\).
The exact unit-square farthest-corner inequality gives for every
center \(c\),
\[
q\ge |c|^2+\tfrac12+|c|.
\]
Since \(\rho^2+\rho+1/2=6961/1600>Q\),
\[
                         |c|<\rho. \tag{1}
\]

If each pair of squares is separated in either the horizontal
or vertical projection, the coordinate projection halfwidth of
each square is at least \(1/2\), so distinct centers satisfy
\[
      |x_i-x_j|\ge1\quad\text{or}\quad |y_i-y_j|\ge1.
      \tag{2}
\]
This is a **necessary** condition, used only inside the
coordinate-separable branch. Arbitrary physically disjoint
rotated squares do *not* always satisfy (2).

Let the four horizontally ordered chain centers be
\(M_1,\ldots,M_4\), and let the four vertically ordered
chain centers be \(V_1,\ldots,V_4\). By hypothesis all
eight are different. The ninth center is \(F\).
Consecutive x-gaps in M and y-gaps in V are at least 1.

Combining these gaps with (1) gives the exact bands
\[
\begin{aligned}
x_{M_1}&\in(-61/40,-59/40),&
x_{M_2}&\in(-21/40,-19/40),\\
x_{M_3}&\in( 19/40, 21/40),&
x_{M_4}&\in( 59/40, 61/40),\\
y_{V_1}&\in(-61/40,-59/40),&
y_{V_2}&\in(-21/40,-19/40),\\
y_{V_3}&\in( 19/40, 21/40),&
y_{V_4}&\in( 59/40, 61/40).
\end{aligned}\tag{3}
\]

Moreover, the two outer M centers obey
\(|y_{M_1}|,|y_{M_4}|<2/5\), and the two
outer V centers obey
\(|x_{V_1}|,|x_{V_4}|<2/5\). Indeed, if
\(|x|>59/40\) and \(|y|\ge2/5\),
then
\[
 |c|^2>(59/40)^2+(2/5)^2
       =3737/1600> (61/40)^2,
\]
contradicting (1). The vertical counterpart is identical.

## 2. The four inner centers lie in a tiny central square

**Lemma 2.1.** All four middle-chain centers
\[
                  M_2,M_3,V_2,V_3
\]
lie in the open box
\[
                 (-21/40,21/40)^2. \tag{4}
\]

*Proof.* Consider \(M_2\), whose x-coordinate is in
\((-21/40,-19/40)\). Both outer V centers have
\(|x_{V_1}|,|x_{V_4}|<16/40\), so
\[
 |x_{M_2}-x_{V_1}|<37/40<1,\qquad
 |x_{M_2}-x_{V_4}|<37/40<1.
\]
By (2) these pairs must be separated vertically.

For the *sign* of each separation, first note
\(|y_{M_2}|<59/40\): otherwise (1) would fail since
\[
 (19/40)^2+(59/40)^2
            =3842/1600>(61/40)^2.
\]
Thus \(y_{V_1}<-59/40<y_{M_2}
<59/40<y_{V_4}\).
The vertical separation inequalities yield
\[
 y_{M_2}\ge y_{V_1}+1>-21/40,\qquad
 y_{M_2}\le y_{V_4}-1<21/40.
\]
The same argument applies to \(M_3\).

For \(V_2,V_3\), interchange x and y, using
the horizontally extreme chain centers \(M_1,M_4\).
Their y-coordinates already belong to the central interval
by (3), so (4) follows. \(\square\)

## 3. A four-point quadrant lemma

**Lemma 3.1 (unit-separated central cross).**
Suppose four points lie in \((-a,a)^2\), with
\(a=21/40<1\), and every pair satisfies (2).
Then exactly one point belongs to each quadrant
(of a deterministic division assigning the axes to
the nonnegative side), and every point obeys
\[
            19/40<|x|,|y|<21/40. \tag{5}
\]

*Proof.* A quadrant within \((-a,a)^2\) has
both coordinate widths at most \(a<1\).
Hence two points from the same quadrant cannot
satisfy (2). Four points in four quadrants
must therefore occupy each quadrant exactly once.

Fix a point \(P\). The other quadrant with
the *same* x sign and opposite y sign has a point Q.
Since \(|x_P-x_Q|<a<1\), (2) forces
\(|y_P-y_Q|\ge1\). Both y-coordinates have
opposite signs and absolute values \(<a\),
so \(|y_P|>1-a=19/40\).
Similarly the point sharing the y sign but
opposite x sign forces \(|x_P|>19/40\).
Both upper bounds follow from the box. \(\square\)

Apply Lemma 3.1 to \(M_2,M_3,V_2,V_3\) by
Lemma 2.1. We have proved something much stronger
than the old rank-grid statement: the **four physical
middle-chain centers** occupy all four nearly rigid
central quadrant boxes around \((\pm1/2,\pm1/2)\).
This requires no case table and no equality assumption.

## 4. The ninth center cannot avoid the outer four

**Lemma 4.1 (strict outer-strip bounds).**
Every other square center \(F=(x_F,y_F)\)
obeying (1)--(2) with the four outer chain
centers \(M_1,M_4,V_1,V_4\) must satisfy
\[
                  |x_F|<7/5,\qquad |y_F|<7/5.
                  \tag{6}
\]

*Proof.* If \(x_F\ge7/5=56/40\),
then by (1)
\[
 |y_F|^2<(61/40)^2-(56/40)^2
                     =585/1600,
\]
hence \(|y_F|<61/100\), since
\(585/1600<(61/100)^2\).

For \(M_4\), (3) gives \(x_{M_4}\in
(59/40,61/40)\) and the sharper bound
\[
 |y_{M_4}|^2<(61/40)^2-(59/40)^2
        =3/20<(39/100)^2.
\]
Consequently
\[
 |x_F-x_{M_4}|<5/40<1,\qquad
 |y_F-y_{M_4}|<61/100+39/100=1,
\]
contradicting (2). Similarly \(x_F\le-7/5\)
contradicts separation from \(M_1\).
Interchange x and y for \(y_F\ge7/5\)
or \(y_F\le-7/5\), using \(V_4,V_1\).
Thus (6) holds. \(\square\)

## 5. The central four cover all ninth-center possibilities

**Theorem 5.1 (the 4+4+1 obstruction).**
The nine-square configuration assumed in the theorem
statement cannot exist at \(q\le Q\).

*Proof.* By Lemma 4.1 the ninth center F has both
coordinate absolute values \(<7/5=56/40\).

By Lemma 3.1 exactly one central center
\(C\in\{M_2,M_3,V_2,V_3\}\) has the same sign
of *both* coordinates as F. (At zero choose
the nonnegative sign.)

For either coordinate \(z=x,y\), the matching
signs, \(|z_F|<56/40\), and
\(19/40<|z_C|<21/40\) give
\[
 |z_F-z_C|
  =\bigl||z_F|-|z_C|\bigr|
  <\max\{21/40,(56-19)/40\}
  =37/40<1.
\]
Thus both coordinate differences between F and C
are strictly less than one, contradicting the
necessary pairwise separation condition (2).
No ninth square exists. \(\square\)

## 6. Exact gate impact and limitations

- **G2.C3.3 (4,1) vertical-stack branch: CLOSED** by
  a one-page structural contradiction, without any
  assumption that the independently oriented squares
  are aligned. Every proposed physical 9-square packing
  in that branch is excluded at \(q\le Q\).
- **G2.C3.3 (3,2) branch: STILL OPEN** and **attained
  at \(q=Q\)** by [TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md).
  Its required theorem must be *sharp*, not an
  exclusion of all equality poses.
- **G2.O unrestricted oblique branch: STILL OPEN.**
  The essential use of (2) depends on **common-coordinate
  separability**, which the known exact rotated witness
  disproves globally. Do not invoke this theorem with
  actual physical disjointness alone.
- **No Lean, CI or independent full proof replay** was
  run for this hand argument.

The numerical relaxed-center search that suggested the
lemma is not a premise of the proof: Sections 1–5 give
a short exact derivation using only the circle-center
bound and a four-quadrant covering.
