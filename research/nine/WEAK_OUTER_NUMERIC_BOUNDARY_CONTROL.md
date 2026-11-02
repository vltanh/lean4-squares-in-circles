# A rational nine-square control on the actual-link boundary

November 2, 2026. This control records an obstruction to strengthening the
weak-outer proof by an unconditional small-transverse-gap bound at equality.
It closes no mask. No Lean, Lake, or CI is used.

Let all nine unit squares be aligned with the coordinate axes and let their
centers be as follows.

| Original | x | y |
|---|---:|---:|
| A | -3/2 | -1/16 |
| B | -1/2 | -1/16 |
| C | 1/2 | -7/15 |
| D | 3/2 | -1/16 |
| E | -1 | 15/16 |
| F | 0 | 15/16 |
| G | 1 | 15/16 |
| H | 2/15 | -22/15 |
| I | -13/15 | -17/16 |

For an aligned square at `(x,y)`, the largest squared corner norm is
`(|x|+1/2)^2+(|y|+1/2)^2`. Each is at most `Q=1105/256`.
The respective exact reserves are printed by the companion rational
checker. In particular A,D,E,G attain Q.

Every physical pair is disjoint in open interiors. For the designated
chains `A,B,C,D` and `E,F,G`, consecutive horizontal gaps equal one.
Among the two remaining squares, `x_H-x_I=1`. Square I is vertically
separated by at least one from A,B and every upper-row square, and
horizontally separated by at least one from C,D. Square H is vertically
separated by at least one from B,C and every upper-row square, and
horizontally separated by at least one from A,D. This covers all 36 pairs.

The C,D transverse gap is

\[
 y_D-y_C=-\frac1{16}+\frac7{15}=\frac{97}{240}>\frac25.
\]

It therefore exceeds `7/30`, `9/32`, and `1/3`. The five designated cone
comparisons hold, but all five actual projection comparisons also hold.
Consequently this is a `000/00` configuration on the closure of the
`001/00` horizontal weak-link inequality, not a weak-link counterexample.

Any proof of `001/00` which closes a neighborhood of this boundary must
use strict weak-link information and orientation or positional penalties.
It cannot discard the whole boundary by claiming that all nine-square
configurations there satisfy one of the smaller transverse-gap bounds.

The exact checker `computer_assisted/weak_outer_numeric_boundary_control.py`
uses only rational arithmetic and checks every original corner, every
physical pair, and all five cone/actual comparisons. The floating-point
optimizer that suggested this control is not a premise of its hand proof.
