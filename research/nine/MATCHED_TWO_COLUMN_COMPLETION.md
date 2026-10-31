# n=9 C3.3 (3,2): matched-column completion and exhaustive residual types

**Status (2026-10-22): CLOSED as a sharp, table-free hand terminal for
the entire *matched-column* structural class.**
The general (3,2) two-stack complement is still OPEN, but every
configuration outside three precisely defined residual types
is already handled by the existing signed 4+3 stress.
All nine unit squares may rotate independently.

## 1. Input class and notation

Fix a common orthonormal frame (x,y) in which every
pair of nine freely oriented squares has disjoint
open projections along x or along y.
Let \(M_1,M_2,M_3,M_4\) be four squares with
pairwise disjoint x-projection interiors, in
left-to-right order. Let the remaining five
squares \(E\) have horizontal longest-chain
length at most two, so that the rank reduction
[TWO_COLUMN_COMPLEMENT_REDUCTION.md](TWO_COLUMN_COMPLEMENT_REDUCTION.md)
partitions \(E=U\sqcup V\), where:

- \(U=\{U_1,U_2,U_3\}\) has **three** pairwise
  disjoint vertical projection interiors;
- \(V=\{V_1,V_2\}\) has **two** pairwise
  disjoint vertical projection interiors;
- inside either group the horizontal
  projection intervals pairwise overlap,
  and therefore have a **nonempty common
  open intersection** (interval Helly).

The known record-radius (3,2) example satisfies
these conditions in its original frame.

Write \(I_2,I_3\) for the open horizontal
projections of the two middle chain squares,
and \(J_S\) for the open horizontal projection
of any complementary square \(S\).

From [INNER_PAIR_SHADOW_DOMINATION.md](INNER_PAIR_SHADOW_DOMINATION.md),
every complementary \(J_S\) meets at least
one of \(I_2,I_3\). Define the **common-anchor
overlap sets**
\[
\begin{aligned}
A_U&=\{i\in\{2,3\}:
         J_S\cap I_i\ne\varnothing
         \text{ for every }S\in U\},\\
A_V&=\{i\in\{2,3\}:
         J_S\cap I_i\ne\varnothing
         \text{ for every }S\in V\}.
\end{aligned}\tag{1}
\]

These are finite geometric data, not angle
or coordinate discretizations.

## 2. The matched-anchor terminal is globally sharp

**Theorem 2.1 (two complementary columns completed
by two different middle anchors).**
Suppose there exist **distinct**
\(i,j\in\{2,3\}\) such that
\[
                    i\in A_U,\qquad j\in A_V.
                    \tag{2}
\]
Then every containing disk satisfies
\[
                         q\ge Q:=1105/256.
\]
If in addition \(q\le Q\), then \(q=Q\)
and its stressed boundary anchors belong
to the signed matched-chain equality family
in [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md),
after interchanging the horizontal and
vertical coordinate directions.

*Proof.* For each \(S\in U\), condition
\(i\in A_U\) means that the open horizontal
projection of S overlaps that of \(M_i\).
Because every pair is coordinate-separable,
their vertical projections must have
disjoint interiors. The vertical
projections of the three U-squares
are already pairwise disjoint.
Thus
\[
                       U\cup\{M_i\}
\]
is a **vertical projection-disjoint
chain of four squares**.

Similarly \(V\cup\{M_j\}\) is a
**vertical projection-disjoint
chain of three squares**.
The two chains are disjoint as sets of squares,
because U and V are disjoint and i≠j.
The common coordinate-separability hypothesis
is preserved by exchanging the frame axes.
Apply Theorem 3.1 of
[SIGNED_MATCHED_CHAIN_STRESS.md](SIGNED_MATCHED_CHAIN_STRESS.md)
in that exchanged frame. It yields \(q\ge Q\)
with its equality rigidity. \(\square\)

**The theorem covers every individual orientation
and every vertical sign pattern.** It does not
assume that U and V occupy globally ordered
layers or have fixed center heights.

## 3. A complete finite trichotomy for the remaining class

The pair of sets \(A_U,A_V\) has at most four
possible elements each (empty, {2}, {3}, {2,3}).
The following **three** residual structural
types, along with the sharp matched type,
are exhaustive:

**R1 (triple gap bridge):**
\(A_U=\varnothing\).

**R2 (pair gap bridge):**
\(A_V=\varnothing\).

**R3 (single-anchor collision):**
\(A_U=A_V=\{2\}\), or
\(A_U=A_V=\{3\}\).

Otherwise **there exist distinct representatives
\(i\in A_U\), \(j\in A_V\)**, and
Theorem 2.1 applies.

*Proof of exhaustiveness.* If both sets are
nonempty and have no distinct representatives,
their union has cardinality one; consequently
each is the same singleton. This is R3.
If either is empty, R1 or R2 applies.
No further possibilities exist. \(\square\)

## 4. Both gap-bridge types lie in one sharply bounded slit

Let \((a,b)\) be the **closed** horizontal gap
between consecutive middle chain projections
\(I_2\) and \(I_3\); its length is \(g_2\ge0\).
The exact [SHARP_FOUR_CHAIN_PROJECTION_BUDGET.md](SHARP_FOUR_CHAIN_PROJECTION_BUDGET.md)
gives, whenever \(q\le Q\),
\[
              0\le g_2\le g_1+g_2+g_3
                  \le17/512. \tag{3}
\]

**Lemma 4.1 (forced common slit transversal).**
If R1 holds, the common horizontal open
intersection of the **three** U projection
intervals lies inside the slit \((a,b)\).
If R2 holds, the common intersection of the
**two** V projection intervals lies inside
the same slit. In particular **either bridge
type forces \(g_2>0\)**.

*Proof.* Suppose \(A_U=\varnothing\).
Some \(J_L\) in U misses \(I_2\),
and some **different** \(J_R\) misses \(I_3\).
By inner-pair shadow domination,
\(J_L\) must overlap \(I_3\) and
\(J_R\) must overlap \(I_2\).

For intervals in the ordered x-direction,
missing \(I_2\) while overlapping \(I_3\)
forces the left endpoint of \(J_L\)
to lie on or to the **right** of the
right endpoint \(a\) of \(I_2\).
Similarly, missing \(I_3\) while overlapping
\(I_2\) forces the right endpoint of \(J_R\)
to lie on or to the **left** of the
left endpoint \(b\) of \(I_3\).

Their open intersection, and hence the
common open intersection of the entire
group U, must lie inside \((a,b)\).
This interval must therefore be nonempty,
so \(g_2>0\). The proof for R2 is identical.
\(\square\)

Thus the only configurations not already
under Theorem 2.1 have either a **common
vertical line through a narrow genuine gap**
meeting an entire triple/pair, or two
complementary stacks that can only be
attached to the *same* inner chain anchor.
This is a **global structural reduction** of
the (3,2) class, not a small numerical
boundary push.

## 5. The remaining quantified obstruction

**OPEN C3.3.c:** Given original physical
coordinate-separable Packing at \(q\le Q\),
prove a sharp lower bound for **each of
R1, R2 and R3**, including exact equality
conditions. A successful proof may:
- eliminate a residual type entirely by
  an orientation-uniform inequality;
- route it to another signed matched
  chain in a *different* frame; or
- exhibit a new sparse terminal stress.

The known exact (3,2) record witness belongs
to the matched type in the **perpendicular
frame** and is retained by Theorem 2.1.
It does not prove any of the residual
R1–R3 types impossible.

**No claim is made** that slit length \(\le17/512\)
alone excludes R1/R2. It is an exact
uniform structural reserve. No optimizer,
MILP output, generated rational table,
Lean build or kernel verification is
a premise of Theorem 2.1 or Lemma 4.1.
