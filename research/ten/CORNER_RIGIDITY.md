# A unit square in an outward quadrant

**Status:** complete elementary hand proof. The square may have any
orientation. This is a local obstruction, not a proof that arbitrary
ten-square packings have the required corner structure.

## The corner theorem

Let alpha,beta>=0. If a closed unit square S lies in

    {x>=alpha, y>=beta}

and in the disk x^2+y^2<=q, then

    q >= (alpha+1)^2+(beta+1)^2.

At equality S is exactly the axis-parallel unit square
[alpha,alpha+1] x [beta,beta+1]. In particular, at q=9/2 a square
wholly in x>=1/2,y>=1/2 must be the square centered at (1,1).
No square fits in this quadrant if q<9/2. Reflections give the other
three outward quadrants; rotating the entire frame preserves the statement.

## Proof by an outward edge

Let alpha',beta' be the square's actual leftmost and bottommost coordinates.
Then alpha'>=alpha and beta'>=beta. Quarter turns and reversal of its frame
allow its side directions to be written in one of the two forms

    (a,b),(-b,a), or (a,-b),(b,a),
    a>=b>=0, a^2+b^2=1.

Put w=a+b. Thus a<=1, b<=1, w>=1. The square's center is
(alpha'+w/2,beta'+w/2).

If b=0, the square is axis-parallel and its upper right vertex is
(alpha'+1,beta'+1). This proves the inequality, and equality forces
alpha'=alpha,beta'=beta because all these coordinates are nonnegative.

Suppose b>0. Then a<1, b<1 and w>1.

For the positive-tilt frame, the outward edge joins

    (alpha'+a, beta'+w) and (alpha'+w, beta'+b).

Because a<=1<=w, this edge meets x=alpha'+1. The ordinate there is

    beta' + a + (1-a)/b
      = beta' + 1 + (1-a)*(1-b)/b
      > beta'+1.

For the negative-tilt frame, the outward edge joins

    (alpha'+b, beta'+w) and (alpha'+w, beta'+a).

Because b<=1<=w, its intersection with x=alpha'+1 has ordinate

    beta' + a + b*(w-1)/a
      = beta' + 1 + (1-a)*(1-b)/a
      > beta'+1.

The two identities use only a^2+b^2=1. In either orientation S therefore
contains a point p with p_x=alpha'+1>=alpha+1 and p_y>beta'+1>=beta+1.
Since alpha,beta>=0, its squared distance from the origin is strictly
greater than (alpha+1)^2+(beta+1)^2. This proves the inequality and
excludes every non-axis-parallel square from equality. QED.

## A consequence for subcritical ten-square research

For any orthonormal coordinate frame about the disk center, every unit
square in a disk of squared radius q<9/2 meets the open cross

    {|x|<1/2} union {|y|<1/2}.

Otherwise the connected square lies in the complement, whose four
connected components are the closed outward quadrants with coordinate
magnitudes at least 1/2; each is forbidden by the theorem. The result
does not assume that different squares share separating axes.

This cross-intersection statement alone is not a packing contradiction:
intersections may be arbitrarily small, and cannot be counted as disjoint
unit-width intervals. Combining it with the separate three-square cap
theorem gives unrestricted necessary conditions for a hypothetical
subcritical packing, but a global extraction argument remains necessary.

## Validation

The proof consists of the two explicitly displayed edge interpolations
and coordinate monotonicity. No numerical search, generated case table,
Lean elaboration, or kernel check is used or claimed.
