# An analytic central-square theorem from two auxiliary circles

Status: a complete pen-and-paper proof of the **central-square reduction**
at squared radius at most `98/25`. This replaces the computational
central-existence step in `EXTERIOR_MARKER_CERTIFICATE.md`. It does not
replace that note's marker-separation theorem, the central-core certificate,
or the still-missing sharp eight-square inequality.

The proof counts total angular measure on two concentric circles. Using
total measure is essential: a square can meet the larger circle in two
disconnected arcs. No numerical continuum verification or assumed contact
graph is used.

## 1. The weighted angular inequality

For a closed square S and `r>0`, let `L_r(S)` be the total angular length
of the set

    {theta modulo 2pi : r(cos(theta),sin(theta)) belongs to S}.

It is the sum of the lengths of finitely many closed arcs; isolated points
contribute zero. Define

    Q = 98/25,
    W(S) = 3 L_1(S) + L_(5/4)(S).

**One-square theorem.** Let S be a unit square contained in the disk
`|x|^2<=Q`, and suppose its open interior does not contain zero. Then

    W(S) >= pi.                                         (1.1)

Equality holds precisely, up to a rotation or reflection about zero, for

    S = [x,x+1] times [-1/2,1/2],
    0 <= x <= (sqrt(21)-4)/4.                            (1.2)

Every equality square satisfies

    L_1(S)=pi/3,       L_(5/4)(S)=0.                     (1.3)

Sections 2--6 prove the theorem. Section 7 applies it to eight squares.

## 2. Canonical coordinates and a monotonicity identity

Choose signed square axes so that its center has coordinates `(a,u)`
with `a>=u>=0`. Since zero is not in its open interior, `a>=1/2`.
Put

    x=a-1/2,       y=u-1/2.

The square becomes

    [x,x+1] times [y,y+1],
    x>=0,    -1/2<=y<=x,
    (x+1)^2+(y+1)^2 <= Q.                              (2.1)

The last inequality is exact farthest-vertex containment. Reflections do
not change any `L_r`, so using these canonical coordinates is harmless.

We will use

    x_0 = sqrt(Q-1)-1 = sqrt(73)/5-1 < 5/7,
    b   = sqrt(Q-1/4)-1 = sqrt(367)/10-1 < 11/12.        (2.2)

The first strict comparison follows from `49*73=3577<3600`; the second
from `367*144=52848<52900`. In particular every canonical x is below one.

### The derivative factorization

Let `X>=Y>0`, `X^2+Y^2=Q`, and `r>=1`. Define

    P_r(z) = z^2(r^2-(z-1)^2).

Writing `s=X+Y`, direct subtraction gives

    P_r(X)-P_r(Y)
      = (X-Y)[(r^2-1)s+s^2-Qs+Q].                      (2.3)

The bracket is strictly positive, because

    s^2-Qs+Q = (s-Q/2)^2 + Q(1-Q/4) > 0               (2.4)

and `0<Q<4`. Thus `P_r(X)>P_r(Y)` whenever `X>Y`.

This identity gives two elementary monotonicity facts.

**Straddling-axis fact.** For `0<=t<=1/2`, put

    X(t)=sqrt(Q-(1-t)^2),
    f_r(t)=acos((X(t)-1)/r)+asin(t/r).

Then `f_r` is strictly increasing. Indeed, with `Y=1-t`,

    f_r'(t)
      = 1/sqrt(r^2-t^2)
        -Y/[X sqrt(r^2-(X-1)^2)].                     (2.5)

All denominators are positive: `X-1<=b<1<=r` and `t<=1/2`.
Also `X>Y`, since `Y<=1` and `X^2>=Q-1>1`. After multiplying positive
denominators and squaring positive quantities, positivity of (2.5) is
exactly `P_r(X)>P_r(Y)`. Consequently, whenever

    0<=x<=sqrt(Q-(1-t)^2)-1,

we have

    acos(x/r)+asin(t/r) >= acos(x_0/r).                (2.6)

**Corner fact.** For `0<=y<=2/5`, put

    X(y)=sqrt(Q-(1+y)^2),
    g_r(y)=asin((X(y)-1)/r)+asin(y/r).

Then `g_r` is increasing, strictly before `y=2/5`. The derivative has
the same expression as (2.5), now with `Y=1+y`; again (2.3) applies.
Here `X>=Y`, with equality exactly at `X=Y=7/5`. Thus for every
canonical state with `y>=0`,

    asin(x/r)+asin(y/r) <= 2 asin(2/(5r)).             (2.7)

To justify the whole domain in this last statement, (2.1) and `x>=y`
give `y<=2/5`. For fixed y, increasing x increases the left side, so
one first places x at its farthest-vertex upper bound and then applies
the monotonicity of `g_r`.

## 3. Squares with x<1/4

For radius one the far vertical side `x+1>=1` does not cut an arc.

First suppose `y=-t`, with `0<=t<=1/2`. Put

    A=acos(x),   B=asin(1-t),   C=asin(t).

The intersection with the unit circle is the interval of angles from
`-min(A,C)` to `min(A,B)`. Hence

    L_1 = min(A,B)+min(A,C).                            (3.1)

Since `x<1/4`, we have `A>pi/3>C`. Thus

    L_1 = min(A+C,B+C) >= pi/3.                        (3.2)

Here `A+C>pi/3`, while convexity of asin gives
`B+C>=2asin(1/2)=pi/3`. Equality in (3.2) holds exactly when
`t=1/2`.

If instead `y>=0`, both far sides are outside the open unit disk, and

    L_1 = pi/2-asin(x)-asin(y)
        > pi/2-2asin(1/4) > pi/3.                     (3.3)

For the final strict inequality, `2asin(1/4)<pi/6`: its sine is
`sqrt(15)/8<1/2`, and both compared angles lie in `[0,pi/2]`.

Since `L_(5/4)>=0`, equations (3.2)--(3.3) prove `W>=pi` in this
region, and equality is possible only when `y=-1/2` and `L_(5/4)=0`.

For that centered strip, its farthest squared norm is `(x+1)^2+1/4`.
It has zero angular measure on the circle of radius `5/4` precisely when

    (x+1)^2+1/4 <= 25/16,
    x <= (sqrt(21)-4)/4.                              (3.4)

For completeness, if the farthest norm is larger than `5/4`, the open
square has points on both sides of that circle, and continuity along an
interior segment gives a circle point in the open square. An open arc
then lies inside, so its angular measure is positive. If the farthest
norm is at most `5/4`, there are at most isolated corner intersections.
Also `(sqrt(21)-4)/4<1/4`, so every equality state lies in this region.

## 4. Squares with x>=1/4 and y<0: the unit-circle bound

Write `y=-t`, `0<t<=1/2`, and retain `A,B,C` from section 3. We show

    L_1 > alpha,       alpha=acos(5/7).                (4.1)

Because `B>=C`, the three possibilities in (3.1) are as follows.

* If `A>=B`, then `L_1=B+C>=pi/3>alpha`.
* If `C<=A<=B`, then `L_1=A+C>=acos(x_0)>alpha`, by (2.6) and (2.2).
* If `A<=C`, then `L_1=2A`. By (2.2),

      cos(2A)=2x^2-1 < 49/72 < 5/7=cos(alpha).

  Since `2A,alpha` lie in `[0,pi]`, this gives `L_1>alpha`.

These possibilities cover the branch boundaries as well.

## 5. The larger-circle bound for the same straddling states

Put `r=5/4` and

    A_r=acos(x/r),
    B_r=asin((1-t)/r),
    C_r=asin(t/r).

The far vertical side does not cut the larger circle, because
`x+1>=5/4`. Also `A_r>C_r`: by (2.2),

    x^2+t^2 < (11/12)^2+(1/2)^2 = 157/144 < 25/16.

Consequently its total angular length is

    L_r = C_r+min(A_r,B_r)
        = min(A_r+C_r,B_r+C_r).                       (5.1)

Convexity of asin gives

    B_r+C_r >= 2asin(1/(2r)) = 2asin(2/5).

For the other branch, (2.6) and (2.2) give

    A_r+C_r >= acos(x_0/r) > acos(4/7)
              > 2asin(2/5).                          (5.2)

The last comparison follows from
`cos(2asin(2/5))=17/25>4/7`. Therefore

    L_(5/4) >= 2 beta,        beta=asin(2/5).           (5.3)

Combining (4.1) and (5.3),

    W > 3alpha+2beta > pi.                            (5.4)

The final inequality is exact: `alpha<pi/3`, so `3alpha` lies in
`[0,pi]`, and

    cos(3alpha) = -235/343 < -17/25 = cos(pi-2beta).

The strict rational comparison is `5875>5831`. Monotonicity of cosine
on `[0,pi]` proves `3alpha>pi-2beta`.

## 6. Squares with x>=1/4 and y>=0

The unit-circle arc has length

    L_1=pi/2-asin(x)-asin(y)
        >= pi/2-2beta,      beta=asin(2/5),            (6.1)

by the corner fact (2.7).

Set `r=5/4` and `gamma=asin(8/25)`. Since `x+1>=r`, the far
vertical side does not cut the larger circle. If `y>=1/4`, neither
far side cuts it, and (2.7) gives

    L_r=pi/2-asin(x/r)-asin(y/r)
        >= pi/2-2gamma.                               (6.2)

If `0<=y<1/4`, its length is the smaller of this same expression and

    H_r(y)=asin((y+1)/r)-asin(y/r).                    (6.3)

The latter function is increasing for `0<=y<1/4`, directly from its
derivative. Therefore

    H_r(y) >= asin(4/5) > pi/2-2gamma.                (6.4)

To check the strict comparison without decimals, both compared angles
lie in `[0,pi/2]`, and

    cos(asin(4/5))=3/5
      < 16sqrt(561)/625 = sin(2gamma).

After squaring positive quantities this is
`140625<143616`. Equations (6.2)--(6.4) prove uniformly that

    L_(5/4) >= pi/2-2gamma.                           (6.5)

Consequently

    W >= 2pi-6beta-2gamma > pi.                       (6.6)

For the last strict inequality, `beta<pi/6`, so `3beta<pi/2`, and

    sin(3beta)=118/125 < sqrt(561)/25=cos(gamma).

The squared comparison is `13924<14025`. Thus
`3beta<pi/2-gamma`, which is exactly the strict inequality in (6.6).

Sections 3--6 cover every canonical state. Only section 3 permits
equality, with exactly the family (1.2), completing the one-square
theorem.

## 7. Eight squares force a unique open central square

**Central-square theorem.** If eight unit squares with pairwise disjoint
open interiors fit a disk of squared radius at most `98/25`, exactly
one of them contains the disk center in its open interior.

Translate the disk center to zero. For each fixed radius r, pairwise
interior-disjoint squares have

    sum_i L_r(S_i) <= 2pi.                             (7.1)

Their intersections with that circle can overlap only on their square
boundaries. A circle meets the finite collection of straight boundary
segments in finitely many points, and these have angular measure zero.
This proves (7.1) for total angular measure, including disconnected arcs.

Suppose no square contained zero in its open interior. The one-square
theorem and (7.1) would give

    8pi <= sum_i W(S_i)
         = 3 sum_i L_1(S_i) + sum_i L_(5/4)(S_i)
         <= 8pi.                                     (7.2)

Equality throughout forces `W(S_i)=pi` for every square. By (1.3),
each then has `L_1(S_i)=pi/3`, giving

    sum_i L_1(S_i)=8pi/3>2pi,

contrary to (7.1). This proves existence of an open central square.
Uniqueness follows immediately from pairwise disjoint open interiors.

The theorem includes squares having zero on their boundary in its
contradiction hypothesis. Thus it proves open containment, not merely
closed containment. Once one square contains zero in its open interior,
no other closed square can contain zero: interior points of that other
square arbitrarily close to zero would enter the first square's open
interior.

## 8. What has and has not been closed

The central-square existence theorem at `q<=98/25` is now analytic.
In particular the central square may be normalized to have fixed axes
and center coordinates of absolute value below `1/2`, without invoking
the marker certificate. The argument applies throughout a disk-radius
range containing the proposed eight-square optimum.

The weighted inequality does not by itself produce marker separation,
marker-quadrant counts `(2,2,2,1)`, or a fixed positive central core.
Those stronger assertions are distinct. Nor does central existence
force the twin interior degree-two squares or the five-corner scaffold.
The next global step is to combine this central square with the proved
corner capacities, outward cap capacities, and contact-cycle restrictions
to obtain that scaffold or an equally strong packing obstruction.
