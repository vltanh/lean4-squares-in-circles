# n=9: an exact, all-parallel record-radius packing with no horizontal stratification in ANY frame

**Status: complete exact hand counterexample to global
stratification, including the all-axis-aligned subclass.**
This strengthens the rotated-pair counterexample in
[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md).

The configuration here is the nine **genuine axis-aligned**
unit squares in
[TWO_STACK_SHARP_EQUALITY_WITNESS.md](TWO_STACK_SHARP_EQUALITY_WITNESS.md).
Its exact disk containment and physical nonoverlap are
verified there. In particular, it packs a disk of squared
radius \(Q=1105/256\).

## 1. Why any stratifying frame would have to be the original axes

Two of its squares, \(M_1,M_2\), have centers
\[
 (-97/64,0),\qquad (-33/64,1/2),
\]
so their center difference is exactly
\((1,1/2)\). Both are axis-aligned; their
open interiors are disjoint and their
closed boundaries touch along a
positive-length vertical edge segment.

If a unit direction e=(a,b) is a projection-separating
direction for these squares, each square's projected
halfwidth is \((|a|+|b|)/2\), so necessarily
\[
   |a+b/2|\ge |a|+|b|. \tag{1}
\]
But
\[
   |a+b/2|\le |a|+|b|/2
                         <|a|+|b|\quad\text{if }b\ne0.
\]
Thus (1) forces \(b=0\): the separating direction must
be horizontal. A horizontal stratification makes every
pair coordinate-separable along its common perpendicular
frame (same-layer squares separate along the frame's
horizontal axis; different layers along its vertical axis).
Hence any putative stratifying frame must include the
original horizontal direction among its two axes, so it
is one of the **two original axis choices, up to signs**.

## 2. No stratification with the original x axis horizontal

For axis-aligned unit squares, if two center heights
differ by **strictly less than 1**, those squares
cannot belong to *different* vertically ordered layers:
complete separation of distinct layers requires
a center-height difference of at least 1.

Consider the following sequence of squares, each consecutive
pair having vertical center-height difference \(1/2\):
\[
\begin{array}{c|rrrrrrr}
\text{square}&E_1&E_4&E_2&M_1&M_2&E_5&E_3\\
y&-3/2&-1&-1/2&0&1/2&1&3/2.
\end{array}
\tag{2}
\]
Every member of this connected sequence must therefore
belong to **one and the same horizontal layer**.
However, \(E_2\) and \(M_2\) have the **same x center**
\(-33/64\), so their horizontal projection interiors
overlap. They cannot lie in a single horizontally
projection-separated layer. Contradiction.

## 3. No stratification after a quarter-turn

After swapping the original x and y directions, the new
vertical coordinate is the original x. Consider
\[
\begin{array}{c|rrrrr}
\text{square}&M_2&E_1&M_3&E_4&M_4\\
x&-33/64&-1/16&31/64&15/16&95/64.
\end{array}\tag{3}
\]
Successive coordinate differences are
\(29/64,\ 35/64,\ 29/64,\ 35/64\), all
**strictly less than one**. Thus all five
squares must lie in the same new horizontal
layer of any proposed stratification.

But \(M_3\) and \(M_4\) both have original
y-coordinate **zero**, so their **new horizontal**
projection interiors overlap. This contradicts
the same-layer horizontal projection-disjointness.

Together with Section 1, the two axis cases exhaust
all possible frames. Therefore:

> **Theorem.** The nine axis-aligned unit squares of
> TWO_STACK_SHARP_EQUALITY_WITNESS.md fit exactly in
> the disk \(q=1105/256\), but admit **no horizontal
> stratification in any orthonormal frame**.

## 4. Consequences

1. **Rejected:** even assuming all nine squares have
   common orientation, it is FALSE that every packing
   at the record radius can be decomposed into fully
   vertically ordered, horizontally projection-disjoint layers.
2. **G5.S is a proper subfamily** not only because
   rotated free squares can be obliquely separated,
   but already within completely **axis-aligned** packings.
3. **The correct terminal equality structure is broader:**
   [SIGNED_MATCHED_EQUALITY_FAMILY.md](SIGNED_MATCHED_EQUALITY_FAMILY.md)
   contains this nine-square example through a perpendicular
   signed 4+3-chain stress, without full stratification.
4. **G2.C3.3 remains open:** this is an exact equality
   configuration in its two-stack residual class.
   Prove a sharp whole-class inequality without forcing
   row stratification, or else the resulting theorem
   would omit a verified equality case.

The proof is exact and table-free; no n=9 Lean compilation,
CI, or global sharp-radius theorem is claimed.
