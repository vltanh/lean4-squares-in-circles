# An exact sixty-degree angular shadow bound for boundary unit squares

## Theorem

Let a unit square S be contained in a disk D_R
centered at zero and **touch** the containing
circle, with

    R^2 >= 39/10.

Then its complete set of radial directions
from zero has angular length strictly less
than pi/3. There is no orientation assumption,
and the circle contact may be anywhere on
the square boundary.

In particular, for any k<=6 such boundary
squares, their combined angular shadows have
total length strictly less than 2*pi.
Therefore **six or fewer circle-contact
squares cannot contain a closed curve
with nonzero winding around the disk center**.
Any winding contact cycle of at most six
exterior squares in this squared-radius
range must contain a unit square strictly
inside the circle.

This theorem is conditional on R^2>=39/10:
the existing purely analytic n=8 lower
bound R8>sqrt(2)+1/2 does not reach that
threshold. It also does **not** force
two circle-free units on a seven-square
contact ring. One circle-free unit may
fill the angular directions left uncovered
by six boundary squares.

## 1. Circle-contact centers and four exact vertices

A square touching the disk boundary
has its largest vertex norm equal to R,
since the square is compact and the
squared norm is convex along its edges.

Rotate coordinates so its center is
`p=(r,0)`, r>=0, and reflect the
square frame to take its angle
`theta in [0,pi/4]`. Set

    C=cos(theta),    S=sin(theta),
    L=C+S,          D=C-S.

Thus `1<=L<=sqrt(2)<10/7`,
`0<=D<=1`, and

    L^2+D^2=2,       L+D=2*C.

The farthest squared vertex formula is

    r^2+L*r+1/2=R^2>=39/10.                         (1)

It follows that `r>5/4`.
Indeed if r<=5/4, the left side of
(1) would be at most

    25/16+(5/4)*(10/7)+1/2
       =431/112 <39/10,

a contradiction. In particular `r>L/2`,
and every vertex has positive x coordinate.
Thus its angular shadow is the interval
between its smallest and largest
ordinary polar arguments, with no
winding or branch ambiguity.

The four vertices, relative to p, are

    top:    ( D/2,  L/2),
    left:   (-L/2,  D/2),
    bottom: (-D/2, -L/2),
    right:  ( L/2, -D/2).                           (2)

The bottom vertex has the least polar
argument: its downward ordinate is at
least as large in magnitude as the
right vertex's, while its horizontal
coordinate is smaller. The upper
extreme is either the top vertex or
the left vertex, since the other
two vertices have nonpositive
vertical coordinate.

Consequently the full angular width
is the maximum of

    w1=atan[D/(2*r-L)]+atan[L/(2*r-D)],              (3)
    w2=atan[L/(2*r+D)]+atan[L/(2*r-D)].              (4)

Each arctangent is nonnegative and
less than pi/2. We prove both sums
strictly less than pi/3.

## 2. The top-bottom angle is less than sixty degrees

The tangent addition formula and
`D^2+L^2=2` give

    tan(w2)=4*r*L/(4*r^2-2).                         (5)

The denominator is positive for r>5/4,
so the sum w2 lies in (0,pi/2),
including the limiting D=0 case.

For r>5/4 the function
`r -> 4*r*L/(4*r^2-2)` strictly
decreases. Using L<10/7 and r>5/4,

    tan(w2)
      < [4*(5/4)*(10/7)]/[4*(25/16)-2]
      =200/119<17/10<sqrt(3).                      (6)

The two rational comparisons are
`2000<2023` and `289<300`.
Since tangent is strictly increasing
on (0,pi/2) and tan(pi/3)=sqrt(3),
we have w2<pi/3.

## 3. The left-bottom angle is less than sixty degrees

The tangent addition formula now gives

    tan(w1)= (2*r*C-1)/[2*r*(r-C)].                (7)

The pre-addition denominator is
`4r(r-C)>0`, so w1<pi/2.
Also its numerator is positive,
because r>5/4 and C>=1/sqrt(2)>7/10.

We prove the **stronger** rational
inequality `tan(w1)<17/10`.
By (7), it is equivalent to

    G(r,C)=17*r^2-27*r*C+5 >0.                    (8)

Let r0 be the positive solution
of `r0^2+r0*(C+S)=17/5`, corresponding
to the lower ceiling `R^2=39/10`.
Equation (1) and monotonicity of
r^2+rL for r>=0 imply r>=r0>5/4.
Moreover

    partial_r G=34*r-27*C
                 >34*(5/4)-27>0.

Thus it suffices to prove G(r0,C)>0.

Substitute `r0^2=17/5-r0*(C+S)`
into (8). With

    K=314/5,       A=44*C+17*S>0,

the expression simplifies exactly to

    G(r0,C)=K-r0*A.                                  (9)

We now show `r0<K/A`.
Since `r^2+r*(C+S)` increases
strictly in positive r, it suffices
to check

    (K/A)^2+(K/A)*(C+S)>17/5.

After multiplication by A^2>0,
and substitution `C^2+S^2=1`,
this becomes exactly

    [3116*C^2-31390*C*S+100721*S^2]/25>0.       (10)

The last quadratic is **strictly
positive for every C,S>=0 not both zero**.
If CS=0 it is obvious. Otherwise
AM-GM gives

    3116*C^2+100721*S^2
      >=2*sqrt(3116*100721)*C*S
      >31390*C*S,

since the single integer comparison is

    4*3116*100721=1255386544
       >985332100=31390^2.                       (11)

Therefore (10) holds, r0<K/A
and G(r0,C)>0. Monotonicity of G
in r gives (8) for the actual
boundary square. Consequently

    tan(w1)<17/10<sqrt(3),

so w1<pi/3. Combining the two
angle cases proves the theorem.

## 4. The precise cycle consequence

The angular shadow of a convex square
omitting the origin is a connected
arc. If a closed curve contained in
the union of k exterior squares
has nonzero winding about the origin,
it must meet **every** radial
direction. Otherwise a missing
ray supplies a continuous argument
branch for the curve and forces
winding zero.

If k<=6 and every square touches
the containing circle, the first
three sections bound the angular
measure of their union by the sum
of k individual shadows:

    length(union shadows)< k*pi/3<=2*pi.

It cannot cover every direction,
a contradiction. Hence a winding
exterior contact cycle with k<=6
must have at least one strictly
circle-free member, under the
stated R^2 threshold.

The theorem makes no claim that
the angular shadows of circle-free
squares have the same width.
In particular six boundary squares
plus a seventh circle-free square
may still cover the full circle;
nothing here excludes a seven-square
cycle with just one circle-free
square. The global eight-square
optimality problem remains open.
