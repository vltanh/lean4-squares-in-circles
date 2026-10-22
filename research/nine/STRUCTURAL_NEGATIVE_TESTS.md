# n=9: mandatory negative tests for structural reductions

These are exact configurations, not numerical counterexamples to the **radius conjecture**.
They disprove tempting *intermediate assumptions* and must be checked
before closing any proposed global-normalization gate.

## N1. The record packing need not contain a central square

Use the nine-square construction in [HAND_PROOF.md](HAND_PROOF.md),
with four middle squares centered at
\[
 (-3/2,1/16),\quad(-1/2,1/16),\quad
 (1/2,1/16),\quad(3/2,1/16).
\]
Their vertical interiors contain \(y=0\), but the two whose
horizontal projections touch the origin have respective horizontal
interiors \((-1,0)\) and \((0,1)\). Thus the origin lies on their **shared
boundary**, not in the open interior of either.

Every other square is strictly away from the origin in at least one
coordinate. Consequently **no square contains the disk center in its
open interior** in this record-radius packing.

A proof that universally asserts a central square, a unique central
square, or a positive-radius central core for all packings with
\(q\le1105/256\) is false. In particular the \(n=8\) central-core
entry theorem cannot be copied unchanged into \(n=9\).

A theorem limited to \(q<1105/256\) is not directly refuted by this
equality configuration, but an equality classification must still
handle the boundary-center state.

## N2. Disjoint axis-parallel squares do not automatically stratify

Consider the three **axis-parallel** unit squares with centers
\[
 A=(-1,-1/2),\qquad B=(-1,1/2),\qquad C=(1,0).
\]
They have disjoint open interiors: \(A,B\) touch along the horizontal
line \(y=0\), and \(C\) is horizontally separated from both.

All three fit in the disk
\[
                    x^2+y^2\le13/4<1105/256,
\]
as the maximum corner squared norm is \(13/4\) for \(A,B\)
and \(5/2\) for \(C\).

Nevertheless there is **no horizontal stratification in the displayed
frame** in the sense of [HAND_PROOF.md](HAND_PROOF.md), §2:

* \(A,B\) have identical horizontal center coordinates and hence
  cannot occupy the same horizontally separated layer.
* Any stratification must put \(A\) below \(B\).
* If \(C\) is in a layer at or below \(A\), full vertical separation
  from \(B\) fails, since \(y_B-y_C=1/2\). If it is in a layer at or
  above \(B\), full vertical separation from \(A\) fails, since
  \(y_C-y_A=1/2\). If it is in an intermediate layer, both gaps
  are only \(1/2\).

This counterexample refutes a *general stratification principle*, not
the possibility that an additional special theorem may hold for
**nine** squares in sufficiently tight circles, nor a theorem that
allows a different frame. Either special assertion needs proof.

## N3. The nine squares are not forced to share one orientation

[NONRIGID_WITNESS.md](NONRIGID_WITNESS.md) gives an exact
record-radius packing with seven fixed parallel anchors, one
axis-parallel additional square, and one genuinely rotated additional
square. Its strict clearance inequalities are verified by rational
identities. Thus an equality theorem asserting that all nine squares
are parallel is false.

## N4. Independent square frames matter in separating-axis tests

For each square \(S\) with center \(c_S\) and orthonormal
unit side vectors \(u_S,v_S\), let
\[
 h_S(e):=\tfrac12\left(|e\cdot u_S|+|e\cdot v_S|\right).
\]
Its projection onto the direction \(e\) is exactly
\([c_S\cdot e-h_S(e),\,c_S\cdot e+h_S(e)]\).

Two square interiors are disjoint if and only if there exists
an edge-normal direction in
\(\{\pm u_S,\pm v_S,\pm u_T,\pm v_T\}\) for which their
projection intervals have disjoint interiors. This is the
separating-axis theorem for convex polygons, specialized to squares.
The direction can come from **either** square, not necessarily
from a common global frame.

For disk containment, the exact constraint is
\[
 \max_{p\in S}\|p\|^2
 =\|c_S\|^2+\tfrac12+
  |c_S\cdot u_S|+|c_S\cdot v_S|\le q.
\]
These are the correct starting formulas for an orientation-stable
analytic argument.

**Usage:** Before replacing the unrestricted Packing hypothesis by
a row/sector/separator model, state a precise implication, test it
against N1--N3, and prove it for all nine freely oriented squares.
If it fails, exhibit an exact counterexample and revise the
structural classification rather than splitting a false assertion
into hundreds of numerical subcases.
