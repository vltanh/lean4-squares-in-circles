# An elementary lower bound sufficient to exclude three-square stresses

Every packing of eleven interior-disjoint unit squares in a disk of squared
radius q satisfies

    q > 1469/400 = 3.6725.

This is an elementary auxiliary bound, not the sharp eleven-square value.
It is independent of the existing n=8 theorem. The strict bound is just strong
enough for the three-square path exclusion in `SPARSE_MINIMIZER_STRESS.md`.

## 1. Unit-separated centers

The open disk of radius 1/2 around a square's center lies in its interior.
Consequently any two square centers have distance at least one: otherwise
the two open radius-1/2 disks, and hence the square interiors, intersect.

Let a square have center p, r=||p|| and orthonormal frame u,v. The largest
squared norm among its four corners is

    r^2 + 1/2 + |p dot u| + |p dot v| >= r^2 + r + 1/2.

Thus containment in the disk centered at zero gives

    r <= C(q) = sqrt(q-1/4)-1/2.

The remainder is a bound for mutually unit-separated points, independent
of square orientations.

## 2. A rational cosine bound

Put theta=2*pi/9 and c=cos(theta). Since 0<theta<pi/3, c>1/2.
The triple-angle identity gives

    8c^3-6c+1=0.

The polynomial f(t)=8t^3-6t+1 is strictly increasing for t>1/2, and

    f(25/33) = -2413/35937 < 0.

Therefore

    cos(2*pi/9) > 25/33.

## 3. At most ten centers in a disk of radius 27/20

Suppose mutually unit-separated points lie in the closed disk of radius
R=27/20. Split them into the inner disk of radius rho=11/20 and its outer
annulus.

The inner disk contains at most two points. For three points a,b,c there,

    ||a-b||^2 + ||b-c||^2 + ||c-a||^2
      = 3(||a||^2+||b||^2+||c||^2)-||a+b+c||^2
      <= 9rho^2 = 1089/400 < 3,

contradicting the three pairwise lower bounds of one.

The outer annulus contains at most eight points. To see this, take two radii
r,s in [rho,R] with angular distance delta<=theta. Their squared distance is

    r^2+s^2-2rs cos(delta) <= r^2+s^2-2rs c.

The expression on the right is convex in either radius separately. Its
maximum on the radial rectangle occurs at a corner. At the mixed corner,

    R^2+rho^2-2R rho c
      = (850-594c)/400
      < (850-594*(25/33))/400 = 1.

At the outer-outer corner,

    2R^2(1-c) < (1458/400)*(8/33) = 486/550 < 1.

The inner-inner value is smaller than the outer-outer value. Therefore
angular distance at most theta forces point distance strictly less than one.
If there were at least nine outer points, two consecutive angular directions
would have a cyclic gap at most 2*pi/9, a contradiction. Thus there are at
most eight outer points and at most ten points in total.

## 4. Consequence for eleven squares

Eleven square centers cannot all satisfy ||p_i||<=27/20. Since every center
satisfies ||p_i||<=C(q), we have C(q)>27/20. Hence

    sqrt(q-1/4) > 37/20,
    q > (37/20)^2+1/4 = 1469/400.

For the intended core exclusion, observe also that

    9/4+sqrt(2) < 1469/400,

because sqrt(2)<569/400 follows from
`2*400^2=320000 < 569^2=323761`.
