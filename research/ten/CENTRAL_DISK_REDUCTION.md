# An unrestricted exterior-arc bound for the ten-square disk

This is a complete hand derivation of a necessary condition. It does not
prove optimality for ten squares.

## Statement

Put Q=9/2, rho=sqrt(2), and

    alpha = 2*arcsin(1/(2*sqrt(2))).

If a unit square S lies in the disk of squared radius Q and avoids the
open disk of radius 1/2 about the same center, then its intersection
with the circle of radius rho has angular measure at least alpha.
The orientation of S is arbitrary.

Consequently at most eight pairwise interior-disjoint such squares
can avoid that open disk. In particular every ten-square packing in
the disk of squared radius at most Q has at least two squares meeting
the open disk of radius 1/2.

## Local coordinates

Rotate and reflect coordinates with the square. We may write its center
as (u,v), where u>=v>=0, and its point set as
[u-1/2,u+1/2] x [v-1/2,v+1/2]. Circle radii and angular measure are
unchanged by this operation. The hypotheses are exactly

    (u+1/2)^2+(v+1/2)^2 <= 9/2,                    (F)
    max(u-1/2,0)^2+max(v-1/2,0)^2 >= 1/4.        (N)

We use arcsin on [-1,1], taking values in [-pi/2,pi/2].

## Case 1: v<1/2

Condition (N) implies u>=1. Thus u+1/2>=3/2>rho, so the right
edge cannot cut the circle arc between heights v-1/2 and v+1/2.
The left edge cannot cut it either, because

    (u-1/2)^2+(v+1/2)^2 <= 2.

To verify this last inequality, if u>=5/4 subtract 2u from (F) to
get a bound at most 9/2-2u<=2. If u<=5/4, its left side is at
most (3/4)^2+1=25/16<2.

Therefore the arc has exactly the angular length

    arcsin((v+1/2)/rho)-arcsin((v-1/2)/rho).

This expression is minimized at v=0. Its derivative is nonnegative
for v>=0 because the derivative of arcsin is even and increases with
the absolute value of its argument, and |v+1/2|>=|v-1/2|. The
minimum is alpha, as claimed.

## Case 2: v>=1/2

Put A=u-1/2, B=v-1/2, U=A+1 and V=B+1. Then A>=B>=0,

    A^2+B^2 >= 1/4,
    U^2+V^2 <= 9/2,
    A+B <= 1.                                             (3)

For the last bound, (A+1)^2+(B+1)^2 is at least
(A+B)^2/2+2(A+B)+2, which exceeds 9/2 if A+B>1.

The square intersects the circle in a single nonempty interval of
first-quadrant angles. Nonemptiness follows because its nearest corner
has squared norm A^2+B^2<=1<2, whereas its farthest corner has squared
norm U^2+V^2>=1/4+2*(1/2)+2=13/4>2. In the last inequality use
A+B>=sqrt(A^2+B^2)>=1/2.

The lower endpoint comes from either y=B or x=U; the upper endpoint
comes from either y=V or x=A. Upper-bound sides outside the circle
cannot be active. There are four possibilities.

### 2a. Both active sides are horizontal

The width is arcsin(V/rho)-arcsin(B/rho). Since B>=0 and V-B=1,
monotonicity of the derivative of arcsin shows this is at least
arcsin(1/rho)=pi/4.

### 2b. Both active sides are vertical

The width is arccos(A/rho)-arccos(U/rho), equivalently
arcsin(U/rho)-arcsin(A/rho). The same argument gives at least pi/4.

### 2c. The two inward sides are active

The width is

    pi/2-arcsin(A/rho)-arcsin(B/rho).

For nonnegative x,y with x+y<=1, increasing derivative gives
arcsin(x)+arcsin(y)<=arcsin(x+y). Applying this with (3) gives

    arcsin(A/rho)+arcsin(B/rho)
       <= arcsin((A+B)/rho) <= pi/4.

Thus this width is at least pi/4.

### 2d. The two outward sides are active

Here U,V<=rho. Hence A,B<=k:=rho-1, and

    1/4 <= A^2+B^2 <= k*(A+B).

Since 1/k=rho+1, we obtain

    U^2+V^2 = A^2+B^2+2*(A+B)+2
       >= 11/4+rho/2 > 2+rho.                              (4)

The strict inequality is equivalent to rho<3/2.
Write p=arcsin(U/rho), r=arcsin(V/rho). The arc width is
phi=p+r-pi/2, and 0<=phi<=pi/2. The identity

    (U^2+V^2)/2 = sin(p)^2+sin(r)^2
      = 1+sin(phi)*cos(p-r) <= 1+sin(phi)

together with (4) implies sin(phi)>rho/2=sin(pi/4), and thus
phi>pi/4.

All four possibilities give angular width at least pi/4. Finally
pi/4>alpha: the equivalent comparison
1/(2*sqrt(2))<sin(pi/8) follows after squaring from sqrt(2)<3/2.
This finishes the one-square theorem.

## At most eight exterior squares

For pairwise interior-disjoint squares, their occupied open arcs on
the test circle are disjoint. Passing from square interiors to closed
squares changes only finitely many circle points, which does not change
angular measure. Thus the total occupied angle is at most 2*pi.

There cannot be nine exterior squares because alpha>2*pi/9. Here is
an exact trigonometric proof. Put beta=arcsin(sqrt(2)/4), so alpha=2*beta
and 0<beta<pi/6. The triple-angle identity gives

    sin(3*beta) = 3*(sqrt(2)/4)-4*(sqrt(2)/4)^3
                = 5*sqrt(2)/8 > sqrt(3)/2 = sin(pi/3).

The strict comparison follows by squaring: 25/32>24/32. Since
0<3*beta<pi/2, strict monotonicity of sine on that interval yields
3*beta>pi/3, hence alpha>2*pi/9. Nine exterior squares would therefore
occupy more than 2*pi. QED.

## Scope and validation

The derivation uses one-square geometry and angular measure only. It
does not assume pairwise separating axes, common orientations, or a
square containing the disk center. A floating-point search over a square
disjoint from a centered axis-parallel unit square suggested the bound;
the proof above uses the weaker and orientation-free condition of
avoiding the radius-1/2 disk, and does not depend on that search.

The result provides a necessary two-core-square condition. It does not
bound the total number of squares meeting the small disk, classify their
positions, or rule out a hypothetical ten-packing below 9/2.
