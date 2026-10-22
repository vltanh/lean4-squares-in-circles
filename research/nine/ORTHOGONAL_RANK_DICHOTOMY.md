# n=9: rank-grid dichotomy for orthogonally separable packings

**Status: proved structural hand theorem under a precisely stated
global-axis separability hypothesis.** The nine square frames may
rotate independently. This is a genuine G2 reduction of the entire
coordinate-separable class, not a reduction of arbitrary unrestricted
packings. The latter remain OPEN because rotated disjoint squares can
overlap in both projections along a chosen fixed frame.

The key is an elementary injection of nine squares into a product of
two longest-chain rank sets, followed by the new strict
[grid stress](GRID_FOUR_CORNER_STRESS.md).

## 1. Exact coordinate-separation definition

Fix any orthonormal frame \((e,f)\). For each unit square S with
center \((x_S,y_S)\), put
\[
 h_S=\tfrac12\bigl(|e\cdot u_S|+|e\cdot v_S|\bigr)
     =\tfrac12\bigl(|f\cdot u_S|+|f\cdot v_S|\bigr)
     \ge\tfrac12.
\]

Define two strict partial orders (non-overlapping *open*
projection intervals):
\[
\begin{aligned}
 S\prec_x T&\iff x_T-x_S\ge h_S+h_T,\\
 S\prec_y T&\iff y_T-y_S\ge h_S+h_T.
\end{aligned}
\tag{1}
\]
These relations are transitive: for example,
\(x_U-x_S\ge h_S+2h_T+h_U\ge h_S+h_U\)
whenever \(S\prec_x T\prec_x U\).
They are irreflexive because all \(h_S>0\).

A finite family is **orthogonally separable in this frame** if
every two distinct squares are comparable (in either order)
under \(\prec_x\) or under \(\prec_y\).
This property implies interior disjointness regardless of each
square's orientation. It is **not automatic** for arbitrary
rotated interior-disjoint squares: a true separating axis may
be oblique to both e and f.

Write \(a\) for the maximum cardinality of a chain in
\(\prec_x\) and \(b\) for that in \(\prec_y\).

## 2. Universal chain-product lemma

**Lemma 2.1 (two-order product injection).** For any finite
orthogonally separable family of n squares,
\[
                            n\le ab. \tag{2}
\]
More precisely, associate to each square S the ranks
\[
 \rho_x(S)=\max\{k:\exists S_1\prec_x\cdots
       \prec_x S_k=S\},\quad
 \rho_y(S)=\max\{k:\exists T_1\prec_y\cdots
       \prec_y T_k=S\}.
\]
Then the map \(S\mapsto(\rho_x(S),\rho_y(S))\)
is an injection into \(\{1,\dots,a\}\times\{1,\dots,b\}\).

*Proof.* If \(S\prec_x T\), append T to a longest
x-chain ending at S; hence
\(\rho_x(T)\ge\rho_x(S)+1\).
The same holds for y. If two distinct squares shared
both ranks, neither could be comparable in x
nor y, contrary to orthogonal separability.
Thus rank pairs are distinct and the injection follows.
\(\square\)

No disk constraint is used in this combinatorial lemma.

## 3. When a=b=3, the grid certificate is forced

**Lemma 3.1 (rank grid supplies four corners).**
Suppose nine independently oriented, orthogonally separable
unit squares satisfy \(a\le3,b\le3\). Then \(a=b=3\);
the ranks take *all* nine values in the 3×3 product,
and the four squares occupying the rank corners
\((1,3),(3,3),(1,1),(3,1)\), labelled
\(TL,TR,BL,BR\), satisfy every span
of [GRID_FOUR_CORNER_STRESS.md](GRID_FOUR_CORNER_STRESS.md),
equation (1).

*Proof.* Lemma 2.1 gives \(9\le ab\le9\),
so \(a=b=3\) and the rank injection is a bijection.
For each fixed y-rank j, the three squares with
x-ranks 1,2,3 have **equal y-rank**. They
therefore cannot be y-comparable; orthogonal
separability makes every pair x-comparable.
Moreover x-comparability must go in increasing
x-rank order. Consequently, if they are
\(S_{1j},S_{2j},S_{3j}\),
\[
\begin{aligned}
 x_{3j}-x_{1j}
 &\ge (h_{1j}+h_{2j})+(h_{2j}+h_{3j})\\
 &=h_{1j}+h_{3j}+2h_{2j}\\
 &\ge1+h_{1j}+h_{3j}.
\end{aligned}
\tag{3}
\]
Apply (3) to y-ranks j=3 and j=1; these are
the top and bottom horizontal spans.

Symmetrically, for each fixed x-rank i,
the three squares \(S_{i1},S_{i2},S_{i3}\)
have equal x-rank and must be y-comparable
in increasing y-rank order. Thus
\[
 y_{i3}-y_{i1}\ge1+h_{i1}+h_{i3}.
 \tag{4}
\]
Apply (4) to x-ranks i=1 and i=3;
these are the left and right vertical spans.

The four corner squares satisfy all four
required inequalities, without imposing any
orientation equality. \(\square\)

**Corollary 3.2 (strict obstruction for a 3×3 rank grid).**
Under the hypotheses of Lemma 3.1, any
containing disk must satisfy
\[
                         q=R^2\ge9/2. \tag{5}
\]

*Proof.* Apply the independently oriented
four-corner stress theorem to (3)--(4). \(\square\)

This is a strong *global* conclusion for all
orthogonally separable nine-square arrangements
with both longest chains at most three. It is
not a special numerical perturbation of a grid
configuration.

## 4. At the n=9 candidate radius a four-chain is forced

**Lemma 4.1 (no five-square projection chain).**
In any packing of unit squares inside a disk with
\[
                   q\le q_*:=1105/256,
\]
no horizontal or vertical projection-disjoint
chain can contain five squares, for any choice
of fixed coordinate frame and arbitrary square
orientations.

*Proof.* Let \(r_S=\|c_S\|\).
Since the farthest corner of a square has squared norm
\[
 \|c_S\|^2+\tfrac12+
 |c_S\cdot u_S|+|c_S\cdot v_S|
 \ge r_S^2+\tfrac12+r_S,
\]
we must have \(r_S<25/16\): otherwise
\(q\ge (25/16)^2+1/2+25/16
=1153/256>1105/256\).
If five squares were ordered by disjoint
horizontal projection intervals, successive
center gaps would each be at least one, so
the two extreme centers would differ by at
least four in their x-coordinates. But their
center norm bound gives
\(|x_{\max}-x_{\min}|<50/16<4\).
Contradiction. The vertical case is identical.
\(\square\)

**Theorem 4.2 (sharp-radius four-chain extraction in the
coordinate-separable class).** Suppose nine independently
oriented unit squares fit in a disk with
\(q\le1105/256\), and in some orthonormal frame
each pair is separated along at least one of the
two coordinate projections. Then **in that frame**
there exist four squares with pairwise disjoint
horizontal projection interiors, or four squares
with pairwise disjoint vertical projection interiors.

*Proof.* Lemma 4.1 gives \(a,b\le4\).
If \(a,b\le3\), Corollary 3.2 forces
\(q\ge9/2>1105/256\), contradiction.
So at least one of \(a,b\) equals four.
The corresponding chain of four squares
has pairwise disjoint projected interiors
by transitivity. \(\square\)

The theorem extracts a *four-chain*, **not**
the fully ordered 4+3 seven-anchor pattern nor
the four-anchor stress pattern. The other
five squares may be positioned irregularly.

## 5. G2 implications and next obstruction

We have proved the following exact dichotomy for
**all** orthogonally separable nine-square packings:
\[
 \boxed{
 \text{four-square x/y projection chain}\quad
 \text{or}\quad q\ge9/2 .
 }
 \tag{6}
\]

At the candidate radius the second branch is
impossible. This means a prospective G2 argument
can begin from four *genuinely disjoint*
projections, without assuming they belong to
a complete 2--4--3 horizontal stratification.

The remaining substantial tasks are:

1. **Coordinate-separable four-chain completion: OPEN.**
   Given a four-chain at \(q\le q_*\) and five other
   arbitrary squares, force either the long/short
   four-anchor stress certificate or a new global
   terminal contradiction. Without this, theorem
   (6) alone does not prove the n=9 bound.
2. **Oblique-pair branch: OPEN.** If no common
   coordinate frame separates every pair along x/y,
   the x/y rank injection is unavailable. Any
   proposed normalization must handle genuine
   oblique separating axes; individual square
   orientations alone do not imply that x/y
   separation fails, as shown by the rotated
   record-radius example.

Theorem 4.2 is an exact *structural*
reduction of a broad class, rather than
enumeration of a particular finite alignment,
but it is not yet the unrestricted G2 coverage
theorem.

## 6. Verification boundary

All proofs use elementary poset ranks, exact
support widths and the previously established
four-corner stress. No state enumeration,
optimizer, Lean kernel proof, CI or external
certificate is used. The n=9 unrestricted
optimality theorem remains open.
