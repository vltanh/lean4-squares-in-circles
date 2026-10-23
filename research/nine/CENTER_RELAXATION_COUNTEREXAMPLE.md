# n=9: center-only packing bounds cannot close G2

**Status (2026-10-22): exact counterexample to an invalid proof strategy.**
The example below consists of **nine center points**, not nine
disjoint squares. It shows that the two necessary inequalities

\[
   \|c_i\|<61/40,\qquad
   |x_i-x_j|\ge1\quad\text{or}\quad |y_i-y_j|\ge1
   \tag{1}
\]

alone cannot exclude configurations possessing horizontal and
vertical four-chains. Any proof relying only on (1), without
retaining actual square projection widths and corner-support
bounds, is incomplete.

## 1. Exact nine-point witness

Consider the nine points

\[
\begin{array}{c|c}
 y & x\text{ values}\\ \hline
 -3/2 &0\\
 -1/2 &-1/2,\ 1/2\\
 0    &-3/2,\ 3/2\\
 1/2  &0\\
 1    &-1,\ 1\\
 3/2  &0 .
\end{array}
\tag{2}
\]

Every point has squared Euclidean norm at most \(9/4\), since
the other nontrivial outer corners \((\pm1,1)\) have squared
norm 2. Therefore
\[
                 \|c\|\le3/2<61/40.\tag{3}
\]

These nine points are pairwise 1-separated in the L-infinity
norm. To verify this without a pair table, note that points
whose y-coordinates differ by at least one need no x check.
The only adjacent y-levels with difference less than one are

\[
 (-1/2,0),\ (0,1/2),\ (1/2,1),\ (1,3/2).
\]

Across each such pair of levels, all their displayed x-values
differ by **at least one**. On the same y-level the two x-values,
when there are two, also differ by at least one.
Hence (1) holds for every distinct pair.

There is a horizontal four-chain
\[
 (-3/2,0),\quad(-1/2,-1/2),\quad
 (1/2,-1/2),\quad(3/2,0)
 \tag{4}
\]
and a vertical four-chain
\[
 (0,-3/2),\quad(-1/2,-1/2),\quad
 (0,1/2),\quad(0,3/2).
 \tag{5}
\]

Thus (1) does not imply that at most eight points fit,
nor does it exclude the existence of perpendicular
four-chains at the target squared circle radius.

## 2. Where the true square geometry enters

For an independently oriented unit square, the exact
required squared radius for a center c and side frame
(u,v) is
\[
       f(c,u,v)=\|c\|^2+\tfrac12+
                |c\cdot u|+|c\cdot v|.\tag{6}
\]
Its projection halfwidth in direction e is
\(h(e)=(|e\cdot u|+|e\cdot v|)/2\).

A center-only relaxation replaces (6) with
\(\|c\|^2+\tfrac12+\|c\|\le q\), and
replaces the true SAT conditions
\(|(c_i-c_j)\cdot e|\ge h_i(e)+h_j(e)\)
with the weaker center inequalities (1).

At every point of (2), the relaxed radial expression
is at most
\[
            (3/2)^2+\tfrac12+3/2
                 =17/4=4.25
                 <q_*=\frac{1105}{256}.
\tag{7}
\]
Thus even imposing the *strongest orientation-independent
radial lower bound* does not refute this nine-point
configuration. The contradiction requires the actual
coupling of orientations, projection widths, and
the support function of the containing circle.

This witness deliberately does not claim the nine points
are centers of physically compatible unit squares.
For example the two upper points \((\pm1,1)\) have
axis-aligned corner radius \(\sqrt{9/2}>R_*\),
while rotating their own frames to reduce radial
support changes the widths needed in pair separation.

## 3. Strategic consequence

G2.C4.3 and the oblique G2.O2/O3 gates cannot be
closed by a purely L-infinity center-capacity
theorem using (1) and a uniform center radius.
Use one of the **exact** stress arguments:

- PAIRED_FOUR_ANCHOR_STRESS.md for long/short endpoint
  pairs and aggregate vertical order;
- GRID_FOUR_CORNER_STRESS.md for crossed grid spans;
- SEPARATOR_GRAPH_CONVEX_DUAL.md for arbitrary chosen
  SAT owner graphs and independently rotating frames.

Any future numerical center-only MILP search can be a
**necessary-condition relaxation**, not a formal
impossibility proof for the true square constraints
unless it is itself infeasible.
