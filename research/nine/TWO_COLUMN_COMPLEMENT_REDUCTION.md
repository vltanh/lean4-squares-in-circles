# n=9 C4.3c: exact two-column reduction for the residual five squares

**Status (2026-10-22): proved finite combinatorial reduction,
NOT an exclusion of the residual branch.**

After SIGNED_MATCHED_CHAIN_STRESS.md, the coordinate-separable n=9
lower-bound problem reduces to this one structural possibility:
a four-square horizontal projection chain M and five complementary
squares E **without any horizontal projection-disjoint triple**.
The lemma below classifies the entire complement into two canonical
vertical stacks. No angle or position grid is used.

## 1. Canonical two-column partition

Fix a perpendicular frame (e,f) in which every pair of squares
is separated in at least one of the two coordinate projections.
Define the horizontal partial order

\[
   S\prec_x T\ \Longleftrightarrow\
     \sup\operatorname{proj}_x(S)
        \le\inf\operatorname{proj}_x(T).
\tag{1}
\]

For the five complementary squares E, suppose no \(\prec_x\)-chain
has length three. Assign to every S in E its **longest-chain rank**
\(r_x(S)\in\{1,2\}\), counting S itself.

**Lemma 1.1 (two vertical stacks).** The rank-one squares form
one vertical projection-separated chain and the rank-two squares
form a second. The open horizontal projection intervals of all
squares of *each* rank class have a common intersection point
on a vertical line. Neither rank class has five squares. Thus
the two nonempty sizes, sorted in decreasing order, are exactly

\[
                    (3,2)\quad\text{or}\quad(4,1).
\tag{2}
\]

*Proof.* If S and T had the same horizontal longest-chain rank
and their open horizontal projections were disjoint, then
one would precede the other in (1), forcing their ranks to
be strictly ordered. Therefore all open horizontal intervals
within each rank class overlap pairwise.

An elementary Helly property of intervals says that finitely
many pairwise overlapping **open** intervals have a common
interior point. At this x-coordinate all squares in the
same class have overlapping horizontal projections; common
coordinate-separability forces every pair of their vertical
projection intervals to have disjoint interiors. Thus their
vertical intervals can be strictly ordered into a chain.

A vertical chain of five unit squares cannot fit the disk
\(q\le1105/256\), because each vertical center gap is at
least one, so the extreme center separation would be at
least four, while all center norms are less than
\(61/40\) and the total vertical center span is less
than \(122/40<4\).

Both rank classes must be nonempty: if E had no horizontal
comparable pair, it would itself form a vertical chain of
five. With five total squares and each size at most four,
the only unordered two-class sizes are (4,1) and (3,2).
\(\square\)

This is a **canonical graph reduction** from infinitely
many geometric arrangements to two stack-size patterns;
the vertical line piercing each class need not be the
same line for the two classes.

## 2. A forced center-line interaction

**Lemma 2.1 (middle square in a vertical triple).**
Any vertical projection-separated chain \(T_1,T_2,T_3\)
of three unit squares inside \(q\le1105/256\) has
\[
                      |y_{T_2}|<21/40.
\tag{3}
\]
Indeed \(y_{T_3}-y_{T_2}\ge1\) and
\(y_{T_2}-y_{T_1}\ge1\), while all center heights
lie strictly in \((-61/40,61/40)\).

**Lemma 2.2 (displaced inner chain square).**
Let M1,...,M4 be a horizontal projection-separated chain,
and let T be any other square whose center satisfies
\(|y_T|<21/40\). Assume common-coordinate separability.
Then **at least one** of M2,M3 has its center height
satisfying
\[
                      |y_{M_i}|>19/40.
\tag{4}
\]

*Proof.* INNER_PAIR_SHADOW_DOMINATION.md proves,
without any common-frame assumption for other squares,
that the open horizontal projection of T overlaps the
open projection of M2 or M3. Call that square M_i.

By common-coordinate separability, their vertical
open projections must be disjoint. The two vertical
projection halfwidths are each at least 1/2, hence
\[
                    |y_T-y_{M_i}|\ge1.
\]
Using (3), \(|y_{M_i}|\ge1-|y_T|>19/40\).
\(\square\)

**Corollary 2.3.** Every coordinate-separable
nine-square packing with a four-horizontal chain
whose five-square complement has horizontal longest
chain ≤2 must have an inner four-chain square
displaced in height by more than \(19/40\) from
the disk center. This conclusion holds for both
stack-size cases (3,2) and (4,1).

*Proof.* Lemma 1.1 supplies a vertical three-chain;
its middle member satisfies (3) by Lemma 2.1.
Apply Lemma 2.2. \(\square\)

## 3. Exact next terminal obligation

The full coordinate-separable branch G2.C4.3c is now one
finite structural class with two stack-size patterns:

- **C4.3c-I: 4+1 vertical-stack complement.** Four E
  squares have vertical-disjoint projections with
  their x projections meeting one common vertical line.
  There is one additional E square.
- **C4.3c-II: 3+2 vertical-stack complement.** The five
  E squares split into two similarly defined vertical
  stacks, with at least one middle member crossing the
  center-height band. At least one inner M-chain
  square must be displaced by (4).

**OPEN:** Prove an entire-branch stress exclusion or derive
a new invariant that handles both possibilities without
enumerating minute height/tilt intervals.

No assumption is made that the columns share a coordinate
x, that their squares have equal orientations, or that the
outer four-chain squares are a flat row. The old zigzag
branch (a center-height gap ≥2 inside M) is already
excluded separately; the remaining center displacements
can still be substantial.

There is no proof here that no such n=9 packing exists.
The unrestricted oblique branch remains an additional
global obligation even if the two-column class is
eventually closed.
