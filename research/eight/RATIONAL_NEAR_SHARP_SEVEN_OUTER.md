# A rational eight-square packing with seven outer centers almost at the Cantrell radius

**Status: exact construction, not a lower bound.** Eight unit squares
with pairwise disjoint **closed** sets fit in a disk of squared radius
`979/250=3.916`. The central square contains the origin in its open
interior, and all seven other square centers have norm greater than one.
Every coordinate, frame, vertex-distance bound, and separating-axis
test below is rational. No numerical optimizer output is a proof premise.

The result sharpens the earlier all-outer-center witness at squared
radius `397/100`. It does not improve the known tilted eight-square
upper bound: `979/250` is strictly **greater** than the candidate
squared radius `3.9155341375...`.

## 1. Eight rational frames and centers

Let `D=1000000`. For each row `(X_i,Y_i,H_i)`, set

    p_i=(X_i/D,Y_i/D),    h_i=H_i/D,
    e_i=((1-h_i^2)/(1+h_i^2), 2*h_i/(1+h_i^2)),
    f_i=(-e_i.y,e_i.x).

Thus `e_i,f_i` are exactly orthonormal rational vectors.
Square `S_i` consists of the four-vertex convex hull

    p_i+(eps*e_i+eta*f_i)/2,  eps,eta in {-1,1}.

| i | X_i | Y_i | H_i |
|---:|---:|---:|---:|
| 0 | 28753 | -60997 | 364707 |
| 1 | 1312318 | -30626 | -68449 |
| 2 | 710413 | 1113765 | -123759 |
| 3 | -283043 | 1263639 | -123759 |
| 4 | -1097483 | 437234 | -123759 |
| 5 | -1129784 | -585777 | -123759 |
| 6 | -244778 | -1379092 | -68449 |
| 7 | 820590 | -972428 | -68449 |

The center norms, computed as integer sums of squares divided
by `D^2`, satisfy

    |p_0|^2<1/100,   min_(1<=i<=7) |p_i|^2>139/100.

Because every unit square contains its center-radius-1/2
open disk, `|p_0|<1/10<1/2` puts the disk origin
strictly inside S_0. Every other center is outer.

## 2. Exact disk-containment certificate

For a unit square with center p and frame (e,f), the
largest vertex squared norm is exactly

    Q(p;e,f)=|p|^2+1/2+|p dot e|+|p dot f|.               (1)

The frame formula above turns (1) into a rational
number. Direct fraction substitution and clearing
positive denominators `D^2*(D^2+H_i^2)` gives
the following **strict upper** integer bounds:

| i | Integer U_i such that 100000 Q_i<U_i |
|---:|---:|
| 0 | 58701 |
| 1 | 367585 |
| 2 | 391597 |
| 3 | 391597 |
| 4 | 322310 |
| 5 | 391597 |
| 6 | 391598 |
| 7 | 391597 |

All `U_i<=391598<391600=100000*(979/250)`.
Every vertex is therefore strictly inside the proposed disk.
By convexity the whole square is contained.

## 3. All 28 pair separations, by exact support axes

For a pair `i<j` and one of the four unoriented frame
axes `n in {e_i,f_i,e_j,f_j}`, define the exact margin

    G_ij(n)=|n dot(p_j-p_i)|
      -[|n dot e_i|+|n dot f_i|
        +|n dot e_j|+|n dot f_j|]/2.                    (2)

If `G_ij(n)>0`, the corresponding separating line
strictly separates the two closed squares. The
absolute values in (2) are absolute values of
**rational numbers**.

The seven successive outer pairs, in the actual
cyclic order `1,2,3,4,5,6,7`, have the following
strict rational witnesses:

| Pair | Axis n | Strict lower bound on 10^6 G_ij(n) |
|---|---|---:|
| 1,2 | f_1 | 19 |
| 2,3 | e_2 | 19 |
| 3,4 | f_3 | 19 |
| 4,5 | f_4 | 19 |
| 5,6 | e_5 | 19 |
| 6,7 | e_6 | 19 |
| 1,7 | f_1 | 19 |

The remaining 21 pairs have substantially larger gaps.
For each row below, direct rational substitution into
(2) gives `G_ij(n)>1/1000`. The following is a
complete list of axis witnesses; each can be checked
independently by clearing its positive denominators.

| Pair | Axis | Pair | Axis | Pair | Axis |
|---|---|---|---|---|---|
| 0,1 | e_1 | 0,2 | f_2 | 0,3 | f_0 |
| 0,4 | e_4 | 0,5 | e_0 | 0,6 | f_6 |
| 0,7 | f_0 | 1,3 | e_3 | 1,4 | e_4 |
| 1,5 | e_1 | 1,6 | f_1 | 2,4 | e_2 |
| 2,5 | f_2 | 2,6 | f_2 | 2,7 | f_7 |
| 3,5 | f_3 | 3,6 | f_6 | 3,7 | f_7 |
| 4,6 | f_6 | 4,7 | e_4 | 5,7 | e_5 |

This checks `7+21=28` unordered pairs, with **strict
positive** gaps throughout. The separating-axis
theorem therefore proves that all eight closed
squares are mutually disjoint.

Every asserted bound is a finite rational comparison
with fully specified operands. The certificate
uses no floating-point inequality or interval-box
cover: numerical experimentation only located a
candidate that was subsequently replaced by the
exact rational coordinates above.

## 4. Consequence for the n=8 proof strategy

A packing with the entire set of seven exterior
centers outer exists at squared radius `3.916`,
only about `0.000466` above the conjectured sharp
eight-square squared radius. The claim that seven
outer centers force a radius of (say) `1.99`
or even `sqrt(3.92)` is therefore false.
In particular a coarse exclusion of the
seven-outer-center case cannot close the
Cantrell-radius conjecture.

This witness has strict pair separations; it
does **not** make the seven outer squares an
actual-contact cycle and does not assert
local minimality. The needed global theorem is
still the unrestricted inequality
`R_8>=R_hat`. The exact construction here
does not establish it.
