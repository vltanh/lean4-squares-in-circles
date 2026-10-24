# n=9: COMPLETE SHARP THEOREM FOR THE COMMON-COORDINATE-SEPARABLE CLASS

**Status (2026-10-22): unrestricted within this explicitly stated
common-frame class, proved by a table-free hand argument.**
Every square may have an **independent arbitrary orientation**.
The complete arbitrary-oblique-pair problem **remains OPEN**:
some legitimate record-radius packings admit *no* common
separating orthogonal coordinate frame.

The theorem closes **ALL of G2.C**, including the previously
unresolved five-square **(3,2)** two-stack complement.
There is no computational interval cover, finite
orientation grid or optimizer premise.

## 1. Sharp statement

Write \(Q=1105/256\).
Let nine independently oriented unit squares be
contained in a disk of squared radius q.
Assume there exists **one common orthonormal frame**
\((e,f)\) such that every pair of distinct squares
has disjoint interiors of its projections along
at least one of e and f.

**Theorem (sharp common-frame n=9).**
Then
\[
                          \boxed{q\ge Q}. \tag{T}
\]

Moreover, if \(q=Q\), **some choice among the two
coordinate directions** admits **two disjoint
projection-separated chains of lengths four and
three**, whose corresponding outer endpoint pairs
have disjoint perpendicular projections.
Consequently the seven chain squares have exactly
the signed matched-anchor normal form, up to
quarter-turn of the chosen frame, relabeling and
the distinct endpoint signs. The other two squares
may turn freely subject to physical containment
and pairwise disjointness.

The converse existence within this class is
provided by the record 2–4–3 construction and
[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md).

The second conclusion is structural **necessity
within the common-coordinate class**, not global
necessity from the original unrestricted Packing
predicate.

## 2. The geometric predecessor/successor lemma

Use the frame as x/y coordinates and let
\(h_S\ge1/2\) be a square's horizontal projection
halfwidth. Write \(S\prec_x T\) when their
horizontal open projection interiors are
disjoint with S to the left of T:
\[
 x_T-x_S\ge h_S+h_T\ge1. \tag{1}
\]
This is a strict partial order. Its antichains
are exactly families whose **open horizontal
projection intervals overlap pairwise**.
In the common-frame class, members of an
antichain have pairwise disjoint **vertical**
projection interiors.

The case \(q>Q\) is immediate; hence assume
\(q\le Q\). Every center \(c\) satisfies
\[
 \|c\|<\rho:=61/40, \tag{2}
\]
using the exact corner bound
\(q\ge\|c\|^2+\|c\|+1/2\).

From [ORTHOGONAL_RANK_DICHOTOMY.md](ORTHOGONAL_RANK_DICHOTOMY.md)
and the strict four-corner grid stress, a nine-square
packing with \(q\le Q\) admits a horizontal or vertical
projection-disjoint chain of four. Swap frame axes
if needed, and call that chain
\[
                    M_1\prec_x M_2\prec_x M_3\prec_x M_4 .
\]
As in [FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md](FOUR_CHAIN_ZIGZAG_NORMAL_FORM.md),
its centers obey
\[
\begin{aligned}
x_{M_1}&\in(-61/40,-59/40),\\
x_{M_2}&\in(-21/40,-19/40),\\
x_{M_3}&\in( 19/40, 21/40),\\
x_{M_4}&\in( 59/40, 61/40),
\end{aligned}\tag{3}
\]
and the two extreme centers have
\(|y_{M_1}|,|y_{M_4}|<2/5\).

**Lemma 2.1 (outer-strip constraint).**
Every *other* square T has center
\[
                         -7/5<x_T<7/5. \tag{4}
\]

*Proof.* If \(x_T\ge7/5\), (2) gives
\(|y_T|<61/100\), because
\(\rho^2-(7/5)^2=585/1600<(61/100)^2\).
By (3), \(x_{M_4}>59/40\) and
\(|y_{M_4}|<39/100\), because
\(\rho^2-(59/40)^2=3/20<(39/100)^2\).
Thus \(|x_T-x_{M_4}|<5/40<1\) and
\(|y_T-y_{M_4}|<1\).
Both coordinate center separations are too
small to separate the pair's projections,
contradicting the common-frame hypothesis.
The case \(x_T\le-7/5\) is symmetric using
\(M_1\). \(\square\)

**Lemma 2.2 (canonical anchor overlap by
horizontal order).** Let T be any nonchain
square and let horizontal order be (1).

1. If T has *any successor* among the
   nonchain squares, then T's horizontal
   open projection intersects that of \(M_2\).
2. If T has *any predecessor* among the
   nonchain squares, then T's horizontal
   open projection intersects that of \(M_3\).

*Proof.* For (1), suppose T has a
successor T', but its horizontal projection
does not overlap that of \(M_2\).
It lies either entirely to the left
or entirely to the right.

If T is left of \(M_2\), then
\[
 x_T\le x_{M_2}-h_T-h_{M_2}
    \le x_{M_2}-1<-59/40<-7/5,
\]
contradicting (4).
If T is right of \(M_2\), then
\(x_T\ge x_{M_2}+1>19/40\).
Its successor obeys
\[
 x_{T'}\ge x_T+1>59/40>7/5,
\]
again contradicting (4).
Hence T overlaps \(M_2\).

For (2), if T is entirely to the right
of \(M_3\), then
\(x_T\ge x_{M_3}+1>59/40>7/5\).
If T is entirely to its left, then
\(x_T\le x_{M_3}-1<-19/40\).
Its predecessor T' would satisfy
\(x_{T'}\le x_T-1<-59/40<-7/5\).
Both contradict (4). \(\square\)

This is the key frame-switch mechanism:
**all left endpoints of genuine x-order
edges overlap the left middle anchor,
and all right endpoints overlap the
right middle anchor**, regardless of
individual square rotations.

## 3. The easy x-triple case

Let E be the five squares not in M.
If E contains an x-chain of length three,
then the two disjoint x-chains M (length4)
and B (length3) are a signed matched-chain
terminal of
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md),
Theorem 3.1. It gives
\[
                              q=Q
\]
under our temporary assumption \(q\le Q\),
with its complete equality-anchor conditions.

Hence assume that E has x-poset **height at
most two**. This was the only residual
coordinate-separable branch.

## 4. Exclude four mutually overlapping E intervals

If E has an x-antichain of four,
those four squares have pairwise overlapping
horizontal projections. By the common-frame
hypothesis, their vertical projections are
pairwise disjoint: they form a **vertical
four-chain**.

This chain is disjoint from the horizontal
four-chain M, leaving a ninth square.
The fully proved
[FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md](FOUR_PLUS_FOUR_PLUS_ONE_EXCLUSION.md)
rules out exactly this entire configuration
at \(q\le Q\).

Therefore E has x-poset **width at most
three**. No general poset decomposition theorem is
needed to find the final signed chains: a
five-element argument gives the required
two disjoint comparable pairs directly.

**Lemma 4.1 (elementary five-element matching).**
If a strict finite partial order has five elements,
no chain of length three and no antichain of
length four, then its elements can be written
\[
                L_1\prec_x R_1,\qquad
                L_2\prec_x R_2,\qquad
                \{F\}, \tag{5}
\]
where the two \(L\)'s are incomparable and
the two \(R\)'s are incomparable.

*Proof.* Partition the five elements into
\(L\), those with **no predecessor**, and
\(R\), those with some predecessor.
Every R has a predecessor in L, since
otherwise there would be a chain of three.
The set L is an antichain by definition,
and R is an antichain because \(r\prec r'\)
together with a predecessor of r would
give a length-three chain.

Neither class can contain four elements,
so their sizes are (3,2) or (2,3).

- If \((|L|,|R|)=(3,2)\), let \(R_1,R_2\)
  be the R elements. They each have a
  predecessor in L. They must have
  **distinct** possible predecessors:
  otherwise only one L element could
  precede either R, and the other two
  L elements together with \(R_1,R_2\)
  would be an antichain of four.
  Choose distinct predecessors \(L_1,L_2\).
- If \((|L|,|R|)=(2,3)\), both L elements
  have a successor in R: an L element
  with no successor would be incomparable
  with all three R elements and produce
  an antichain of four. The union of the
  two successor sets contains at least
  two different R elements, since each
  of the three R elements has *some*
  predecessor in L. For two nonempty
  successor sets whose union has size
  at least two, choose distinct
  representatives \(R_1,R_2\).

The one element not in the chosen two
comparable pairs is F. Since L and R
are antichains, the selected L pair and
R pair are each incomparable. \(\square\)

Apply Lemma 4.1 to the horizontal
interval order on E. It yields (5)
with exactly the incomparabilities
required in Section 5.

## 5. Complete the (3,2) two-stack class by one finite singleton split

The fifth element F of (5) cannot possess
both an x-predecessor and an x-successor:
that would create an x-chain of length three.

There are exactly three structural cases,
with no geometric numerical subdivisions.

### Case A: F has a successor

Then F is x-incomparable with both \(L_1,L_2\):

- If \(F\prec_x L_i\), then \(F\prec_x L_i\prec_x R_i\)
  would be a length-three chain.
- If \(L_i\prec_x F\), append any successor of F
  to get a length-three chain.

Thus \(A=\{L_1,L_2,F\}\) is an x-antichain
of three and \(B=\{R_1,R_2\}\) is an
x-antichain of two.

Each member of A has a successor in E,
so Lemma 2.2(1) says **every member of A
overlaps \(M_2\) in horizontal projection**.
Each member of B has a predecessor, so
every member of B overlaps \(M_3\).

### Case B: F has a predecessor

Similarly, F is incomparable with
both \(R_1,R_2\):
an \(R_i\prec_x F\) would extend
\(L_i\prec_x R_i\), and an \(F\prec_x R_i\)
would extend its own predecessor.

Thus \(A=\{L_1,L_2\}\) is an x-antichain
of two and \(B=\{R_1,R_2,F\}\) is an
x-antichain of three. All members of A
overlap \(M_2\), and all members of B
overlap \(M_3\), again by Lemma 2.2.

### Case C: F has neither predecessor nor successor

Then F is x-incomparable with **all four**
other E elements. The oblique-safe
[INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md)
says F overlaps \(M_2\) or \(M_3\)
horizontally.

If it overlaps \(M_2\), put
\[
   A=\{L_1,L_2,F\},\qquad B=\{R_1,R_2\}.
\]
Otherwise it overlaps \(M_3\), so put
\[
   A=\{L_1,L_2\},\qquad B=\{R_1,R_2,F\}.
\]
Either way A,B are x-antichains
of sizes (3,2) or (2,3);
every A-square overlaps \(M_2\),
and every B-square overlaps \(M_3\).

**These three cases exhaust all choices of F.**
In all of them, we obtain two *disjoint*
x-antichains A,B, partitioning E,
such that
\[
\begin{aligned}
 |A|+|B|&=5,&\{|A|,|B|\}&=\{2,3\},\\
 J_S\cap J_{M_2}&\ne\varnothing \quad(S\in A),\\
 J_S\cap J_{M_3}&\ne\varnothing \quad(S\in B),
\end{aligned}\tag{6}
\]
where \(J\) denotes open horizontal projections.

## 6. The perpendicular 4+3 stress finishes the sharp radius

An x-antichain consists of squares with
pairwise **overlapping horizontal projections**.
Because the packing is common-coordinate-separable,
their vertical projections must have disjoint
interiors.

Thus the squares in A are vertically
projection-disjoint from each other, and
each is vertically projection-disjoint
from \(M_2\), by (6). The union
\[
                              A\cup\{M_2\}
\]
is a genuine **vertical chain of size
\(|A|+1\in\{3,4\}\)**.

Likewise \(B\cup\{M_3\}\) is a genuine
**vertical chain of size \(|B|+1\in\{4,3\}\)**.
The chains are disjoint as square sets,
because A and B partition E and
\(M_2\ne M_3\).

Together they form **two disjoint
vertical projection-separated chains of
four and three squares**.
Exchange the x and y axes. Every pair
is still separable by one of the two
coordinate projections; therefore
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md),
Theorem 3.1, applies again and gives
\[
                              q=Q.
\]

We have excluded \(q<Q\) in every
common-coordinate-separable branch, which
proves Theorem (T). The sharp construction
achieves q=Q, and the signed theorem
provides the corresponding necessary
equality skeletons for this class. \(\square\)

## 7. Implications and remaining unrestricted gate

**CLOSED:**
- The whole coordinate-separable G2.C theorem.
- The entire formerly open C3.3 / C4.3c **(3,2)**
  branch, now with a necessary **perpendicular
  signed 4+3** sharp terminal rather than
  an invalid blanket exclusion.
- Every coordinate-separable q=Q packing
  belongs to some signed matched-chain
  equality skeleton. The conditional full
  parameter domain of that skeleton is
  [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md).
- The (4,1) residual case remains strictly
  excluded by the independent quadrant-cover
  theorem.
- No large positional or tilt case table
  appears in the hand proof.

**OPEN:** The original nine-square Packing
predicate permits pairs separated *only*
on oblique axes belonging to their own frames.
[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md)
contains an exact record-radius example with
this property. Nothing in the proof above
establishes that an arbitrary unrestricted
packing admits any common-coordinate frame.
This is the distinct **G2.O3–O5** global
structural/stress problem. Unrestricted n=9
optimality and global equality necessity
remain unproved.

## 8. Verification boundary

This is a complete *hand proof* with an elementary five-element matching lemma and exact geometric
inequalities. It has not undergone independent
full mathematical audit, and no Lean
compilation, kernel proof or CI run occurred.
The computational exploratory solver that
motivated the approach is not a premise
of any lemma above.
