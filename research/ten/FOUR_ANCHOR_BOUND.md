# A sharp four-anchor lower bound

This conditional lemma applies regardless of how the other six squares are
placed or rotated. It does require four squares with a common orientation
and the coordinate gaps stated below; extracting such anchors from an
unrestricted packing remains open.

Translate the disk centre to zero and rotate these four squares' shared frame
to the coordinate axes. Label their centres `A,B,C,D` and assume

`x_A−x_B ≥ 2`, `x_D−x_C ≥ 2`,

`y_A−y_D ≥ 2`, `y_B−y_C ≥ 2`.

**Claim.** If these squares lie in the disk of radius `R`, then `R² ≥ 9/2`.
At equality, their centres are respectively `(1,1),(-1,1),(-1,-1),(1,-1)`.

**Proof.** Choose the vertices

`a=(x_A+1/2,y_A+1/2)`, `b=(x_B−1/2,y_B+1/2)`,

`c=(x_C−1/2,y_C−1/2)`, `d=(x_D+1/2,y_D−1/2)`.

The horizontal gaps `a_x−b_x` and `d_x−c_x` are at least three. For real
`r,s`, the identity

`r²+s² = ((r−s)²+(r+s)²)/2`

shows that each pair contributes at least `9/2` to the sum of squared
x-coordinates. Thus `a_x²+b_x²+c_x²+d_x² ≥ 9`. The vertical gaps `a_y−d_y`
and `b_y−c_y` are also at least three, giving a sum of squared y-coordinates
at least nine. All four vertices lie in the disk, so

`4R² ≥ ‖a‖₂²+‖b‖₂²+‖c‖₂²+‖d‖₂² ≥ 18`.

If `R²=9/2`, all inequalities are equalities. Each paired difference is three
and each paired sum is zero. Therefore the four vertices are respectively
`(3/2,3/2),(-3/2,3/2),(-3/2,-3/2),(3/2,-3/2)`, which fixes the four centres
as claimed.

This bound needs no hypotheses on the other six squares and covers the
entire six-parameter construction family. It gives a possible terminal step
for a future structural reduction, rather than that reduction itself.
