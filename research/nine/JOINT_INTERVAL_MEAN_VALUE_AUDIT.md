# Independent audit of the joint interval mean-value method

This audit checks the interval method used for the joint five-square dual.
It is independent of the producer's search and does not assert that an
unfinished cover is complete. The physical dual was reviewed separately;
the focus here is the exact arithmetic, derivatives at branch changes,
moving orientation candidates, and coverage replay.

**Result: passed.** The arithmetic and mean-value arguments below apply to
the complete four outer scalar tables and the central transfer table used
by `UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`. Each table has a
separate complete independent replay. This audit addresses the numerical
inequality method; the physical reduction and analytic leaves are proved
in the cited hand manuscripts.

## 1. Reviewed canonical components

The executable components are in `computer_assisted`.

| Independent component | SHA-256 |
|---|---|
| `verify_joint_five_dyadic.py` | `e9a077c6ed871e402f5e43604137a011428ffe9f0d5dcf18d2e1651dd1290c1f` |
| `verify_joint_five_fraction.py` | `148ae2fa1a26ddb1e288f6345255f3ce2ea564ac1bcda07ad7f20d470d469413` |
| `interval_fraction.py` | `8e33d71d00f5fbee9e6a255a3d0d69dd9fcc721d4f4472b11405129222d1e26d` |
| `verify_E_variable_k_linear.py` | `3ded159b3db0288ee1a00ad549061ea151e9f2d540e3fb7988cd02091ec3be8c` |
| `verify_outer_scalar_family.py` | `a03dd5b29c7b92b677aa9c3248625b7899ba9e111cc0520c550b27611abdaa81` |
| `verify_central_linear_transfer.py` | `503dfe9d519d47c61bb62aee799e573c0823e93944f721f911f07f11804001b8` |

The directed-integer core is standalone and imports no producer or shared
interval arithmetic. The Fraction core imports only the separate
`interval_fraction.py` implementation. The scalar and central wrappers
independently reconstruct their mathematical expressions and domains.

## 2. Arithmetic and elementary automatic differentiation

The producer uses integers divided by `2^96`. Addition is exact at that
scale; products round the least product down and the greatest product up.
For positive denominator intervals, division takes outward bounds over
all four endpoint quotients. Squaring correctly uses zero as the lower
bound whenever the interval contains zero. Its square-root implementation
uses integer square roots, increasing the upper endpoint exactly when the
upper radicand is not a square.

The primary independent replay applies the same outward integer principles
at scale `2^64`, using its own implementation of every arithmetic operation.
The second replay uses exact `Fraction` endpoints for arithmetic. Its radical
lower bound is the integer square root of the scaled lower radicand;
its upper bound adds one dyadic unit to the corresponding upper integer
square root. The latter may overestimate an exact square by one unit,
which is conservative. Both interval constructors reject inverted bounds.

The ordinary sum, product and quotient derivative rules are correct. The
two implementations use algebraically different quotient derivatives;
both enclose the same derivative. At an absolute-value sign change the
derivative hull is the symmetric hull of the input derivative. For a
Euclidean norm, the ordinary derivative is intersected with

\[
\left|\partial_j |v|\right|\le |\partial_jv|.
\]

At a possible zero of the vector, only this Lipschitz bound is used. All
intersections therefore combine independently valid derivative bounds.

For a minimum of finitely many enclosed branches, a branch is excluded
from the derivative hull only if its lower value exceeds the smallest
available upper value. Such a branch cannot minimize anywhere in the
box. Maxima are handled by negating minima. Hulls at unresolved branch
changes include every potentially active branch.

## 3. Minimum support over a fixed orientation set

Let

\[
M(t)=\min_{\theta\in I}\sum_iH_\theta(v_i(t)),
\]

where the orientation set `I` is fixed: either a full quarter turn or the
endpoint interval `[-atan(7/100),atan(7/100)]`. On each interval between
alignments the support sum has nonpositive second derivative in the
orientation variable. Hence its minimum is attained at an alignment or,
for the restricted interval, at a boundary frame.

The implementations keep the fixed boundary frames. An alignment of
`(x,y)` is discarded in the endpoint case only when both

\[
|y|>\tfrac7{100}|x|,
\qquad
|x|>\tfrac7{100}|y|
\]

hold throughout the complete parameter box. This proves that neither
the direction nor its quarter turn lies in the allowed interval.
Every alignment that could be admissible at any point is retained.

Some retained alignments may be outside the allowed interval on part of
the box. This does not invalidate either part of the enclosure:

1. Their addition can only lower the candidate minimum used for a lower
   value bound. A fixed boundary frame still supplies the upper bound.
2. At every parameter value, every actual minimizing alignment or
   boundary is among the retained branches. Adding extra derivative
   intervals only enlarges the hull. The subsequent active-branch test
   uses the boundary upper bound, so it cannot discard a true minimizer.

The returned value enclosure and derivative enclosure describe the true
function `M`, rather than a chosen minimum over inadmissible candidates.
This distinction is essential to interpreting the subsequent automatic
differentiation correctly.

If a candidate vector is identically zero on the box, it contributes no
support and its alignment is unnecessary. If it is identically horizontal
or vertical, its alignment is a fixed frame, including when its signed
length crosses zero. Otherwise a possibly zero candidate marks the entire
orientation minimum as singular: the candidate-based lower value is
replaced by zero and the derivative uses the uniform Lipschitz bound.
The universal bound

\[
M\ge\frac12\sum_i|v_i|
\]

is still valid and is used to raise the lower value. For the derivative,
the square circumradius is less than one, so uniformly in every frame,

\[
|\partial_jH_\theta(v_i)|\le|\partial_jv_i|,
\qquad
|\partial_jM|\le\sum_i|\partial_jv_i|.
\]

The implementation's derivative intersection with this bound is valid,
including at changes of active frame. A vector that happens to vanish at
the midpoint causes no problem: the midpoint computation contributes
only its value to the mean-value enclosure, not its derivatives.

## 4. Exact center support and its changing branch

In a known square frame let `A>=B>=0` be the absolute components of the
center-support direction, and let `r=sqrt(Q)` and
`rho=sqrt(Q-1/4)-1/2`. The two exact branches are

\[
C=\rho A\quad\text{if }A^2\ge(4Q-1)B^2,
\qquad
C=r\sqrt{A^2+B^2}-\frac{A+B}{2}\quad\text{otherwise}.
\]

At a positive transition point, the second branch's partial derivatives
in `(A,B)` are exactly `(rho,0)`, agreeing with the first branch. At the
origin the norm and absolute-value Lipschitz derivative bounds apply.
When an interval does not decide the transition, the implementation takes
the hull of both values and derivatives. It never discards a potentially
active branch.

The known frame is always `(1,±w)` normalized. Its angular derivative is
`±w'/(1+w^2)`. The center region is a rotation of a fixed compact subset
of the radius-`rho` disk. Its support therefore obeys

\[
|\partial_jC(v,\theta)|
\le\rho\bigl(|\partial_jv|+|v|\,|\partial_j\theta|\bigr).
\]

This proves the additional derivative intersection used in both programs.
The box-face multipliers are fixed nonnegative rationals in each row;
their shifts and constant penalties add no missing derivatives.

## 5. Mean-value enclosure

Each actual scalar dual obtained from fixed row multipliers is continuous
and locally Lipschitz in the four slope variables. Its formulas are
piecewise algebraic, and all the preceding rules bound its derivatives
on every differentiable piece, including the appropriate limiting hulls
at switches. Along a segment, integration gives

\[
F(t)-F(m)=\int_0^1\nabla F(m+s(t-m))\cdot(t-m)\,ds.
\]

Consequently the interval

\[
F(m)+\sum_j\partial_jF(B)(B_j-m_j)
\]

encloses all values on the box `B`. Degenerate midpoint intervals are
used only for `F(m)`. Taking the smaller of this upper endpoint and the
ordinary interval upper endpoint is valid because each separately bounds
the same true dual.

## 6. Complete-cover replay

Each wrapper reconstructs its initial roots from exact rational constants.
The R-owned scalar covers have three roots, the complement of the hand
rectangle `|w|,t<=1/80` in `[-2/3,6] x [0,6]`. Each E-owned scalar cover
has the single root `[1/16,6]`, adjoining the complete hand interval.
The central cover has the three quadrant roots `[-6,0]^2`,
`[-6,0] x [0,6]` and `[0,6]^2`; symmetry interchanges the central slopes
and covers the fourth quadrant.

Every internal node must use the exact midpoint and retain both children.
A node cannot be reused; each child box must equal its reconstructed
expected box; every supplied node must be reached. Completion also
requires the claimed leaf count and zero omitted or open leaves.

Every outer numerical row checks its nonnegative rational multipliers
and recomputes a strictly negative residual upper bound. The E wrapper
additionally enforces `207/16<=k<=20` and the explicitly unboxed endpoint
constant required by the hand comparison. The R wrapper keeps the
original endpoint frame interval and the shoulder frame fixed by its
owned normal. Producer-recorded residual bounds are not trusted.

The compact central wrapper treats the full negative and mixed-sign
roots with the independently proved hand inequalities. Its remaining
analytic leaves must satisfy the signed-sum strip condition at both
extreme endpoints. Every numerical central row is explicitly required
to lie in the positive quadrant. It reconstructs only the simplified
positive-quadrant expression, avoiding a signed-sum formula switch, and
requires a strictly positive recomputed lower bound.

The completed finite components have 1,700 and 490 R-owned leaves,
25 and 28 E-owned leaves, and 1,684 numerical plus 34 analytic central
leaves. Separate exact replay reports identify their source hashes,
coverage counts and strongest shared margin. Both E-owned tables also
passed full independent Fraction replays.

The hand proofs remain necessary for the complementary sharp intervals,
the endpoint-owned slope comparison, the negative and mixed central
quadrants, and the signed-sum strip. The finite method proves all
remaining rows and their complete coverage; it makes no numerical
assumption about omitted physical centers or orientations.
