# n=9 G2.C4.1 — four-chain shadow barrier and incidence compression

**Status: completed, exact, table-free structural hand proof.**
This holds for **any** packing of freely rotated unit squares with
\(q\le1105/256\) that happens to contain four squares with pairwise
disjoint projections in some direction. It does NOT assume that all
other square pairs are separable along a common coordinate frame.

It is a global geometric statement about the four-chain *conditional
on the existence of that chain*. The existence of a four-chain
from unrestricted Packing is still OPEN (G2.O2).

## 1. A four-chain almost tiles the full projection of the circle

Let \(R\ge0\), \(R^2\le1105/256\), and fix an orthonormal
frame (e,f). Let four independently rotated unit squares
\(M_1,M_2,M_3,M_4\) lie in the closed disk of radius R,
with pairwise disjoint open e-projections. Order their
closed projected intervals
\[
  I_1<I_2<I_3<I_4,\qquad I_i=[a_i,b_i],
 \quad b_i\le a_{i+1}. \tag{1}
\]
For square S with side axes u,v, its e-projection length is
\[
       w(S)=|u\cdot e|+|v\cdot e|,
       \qquad 1\le w(S)\le\sqrt2<2. \tag{2}
\]
The lower bound is the L1/L2 comparison for the orthonormal
coordinates of e. The upper bound is Cauchy--Schwarz.

Since all four projection intervals lie inside [-R,R] and
their open interiors are disjoint,
\[
 \sum_{i=1}^4 |I_i|\ge4,\qquad
 \sum_{i=1}^4|I_i|\le2R.
 \tag{3}
\]
But \(R<17/8\), since
\[
 1105/256< (17/8)^2=1156/256.
\]
Consequently
\[
       0\le 2R-\sum_i|I_i|<\frac14. \tag{4}
\]
This expression is exactly the total length of the five
complementary projection gaps: the left and right margins
inside [-R,R] and the three gaps between consecutive I_i.
In particular **every gap has length less than 1/4**.

These are exact symbolic inequalities; no numerical
angle, position or mesh threshold is involved.

## 2. All other squares must overlap the chain

**Theorem 2.1 (four-chain shadow barrier).**
Under (1)--(4), let T be **any** other independently
oriented unit square fitting inside the same disk.
Then the open e-projection of T intersects the open
projection of at least one M_i.

*Proof.* T's projection interval \(J\subset[-R,R]\)
is connected, has length \(w(T)\ge1\), and has nonempty
interior. If it did not intersect the interior of
any I_i, its interior would lie in a connected
component of the complement of the union of
the interiors of the I_i, hence in one of the
five gaps (up to finitely many endpoints).
Each gap has length <1/4 by (4), contradicting
\(|J|\ge1\). \(\square\)

This theorem does not assume T and M_i have the
same orientation or that the *physical* squares
overlap: it is only a fact about their projected
intervals. In an actual packing they do not
have overlapping **two-dimensional interiors**.

**Theorem 2.2 (consecutive-block incidence).**
For any T as above, the set
\[
 \mathcal I(T)=
 \{i\in\{1,2,3,4\}:
       \operatorname{int}(J)\cap\operatorname{int}(I_i)
       \ne\varnothing\} \tag{5}
\]
is a nonempty consecutive subset of the four
indices and contains at most **three** indices.

*Proof.* Nonemptiness is Theorem 2.1.
If J overlaps I_i and I_k with i<k,
then the interval J spans every I_j with
i<j<k, so its interior meets each such
I_j: the index set is consecutive.

If J overlapped both I_1 and I_4,
the interval J would contain I_2 and I_3
between two of its interior points.
In particular its length would exceed
\[
                  |I_2|+|I_3|\ge2.
\]
But (2) gives |J|≤sqrt2<2. Contradiction.
Thus it cannot meet all four and has
at most three consecutive indices. \(\square\)

Therefore every remaining square has one
of exactly nine *possible* nonempty
projection-incidence blocks:
\[
\{1\},\{2\},\{3\},\{4\},
\{1,2\},\{2,3\},\{3,4\},
\{1,2,3\},\{2,3,4\}.
\tag{6}
\]
This is a nine-element list of **types**, not
an instruction to enumerate \(9^5\) assignments.
The proof of the next G2 gate must derive a
global obstruction from their interval-order
structure, not brute-force all assignments.

## 3. Orthogonally separable branch: a vertical-sign dichotomy

Now additionally assume the nine squares are pairwise
coordinate-separated in the frame (e,f), in the sense of
ORTHOGONAL_RANK_DICHOTOMY.md.

For each nonchain square T and each index i in
\(\mathcal I(T)\), the e-projections overlap in
their interiors. Hence disjointness along the
chosen coordinate axes forces the *vertical*
projection intervals of T and M_i to have
disjoint interiors. In particular T is
entirely above or entirely below M_i.

**Lemma 3.1 (switching sides requires a large zigzag).**
If T lies above one M_i in its incidence block
and below another M_j in that block, then
\[
                   |y_{M_i}-y_{M_j}|\ge2. \tag{7}
\]

*Proof.* Write \(h_S\ge1/2\) for the vertical
projection halfwidth of S. If T lies above M_i
and below M_j, then
\[
 y_T-h_T\ge y_{M_i}+h_{M_i},\qquad
 y_{M_j}-h_{M_j}\ge y_T+h_T .
\]
Adding,
\[
 y_{M_j}-y_{M_i}
    \ge h_{M_i}+2h_T+h_{M_j}
    \ge \frac12+1+\frac12=2.
\]
The opposite order gives the absolute-value form.
\(\square\)

**Corollary 3.2 (coherent-sign or zigzag dichotomy).**
Either the vertical centers of the four chain
squares have diameter at least 2, **or**
every nonchain square lies consistently on one
vertical side of *all chain squares whose horizontal
projections it overlaps*.

This does not mean that all nonchain squares
lie on one side of the entire four-chain,
nor that the configuration admits a horizontal
stratification; neither assertion follows.

## 4. Exact remaining C4 tasks

**C4.1 CLOSED:** four-chain full shadow barrier,
nine allowed incidence blocks and the coherent-sign
or large-zigzag dichotomy (this document).

**C4.2 OPEN: large-zigzag exclusion or terminal stress.**
If two horizontally separated chain squares have
vertical center gap ≥2, show that all nine-square
packings in this branch satisfy q≥q_* by a
*global counting/support argument*, or derive a
different sharp terminal pattern. Do not exclude
only a tiny height interval.

**C4.3 OPEN: coherent-sign completion.**
If each remaining T is consistently above/below
the chain squares it meets, prove that the five
nonchain squares either force a long/short
four-anchor certificate, a four-corner grid
stress, or another finite analytic obstruction.
The index-block description (6) is a
combinatorial vocabulary, not completed
case analysis.

**C4.4 OPEN:** combine both branches to close
the entire coordinate-separable n=9 class.

**G2.O2 remains OPEN** because the existence of
a four-chain itself is unproved for arbitrarily
oblique configurations.

No user-facing global optimality claim, Lean,
CI, or external proof oracle is made here.
