# A sharp three-square cap theorem with arbitrary orientations

## Theorem

For 0 <= h <= 1/3, three unit squares with pairwise disjoint open
interiors contained in D_R intersect {x >= h} satisfy

    R^2 >= (h+1)^2+9/4.                                      (1)

At equality the two extreme squares are

    [h,h+1] times [1/2,3/2],
    [h,h+1] times [-3/2,-1/2],                               (2)

and the middle square is

    [a-1/2,a+1/2] times [-1/2,1/2],
    h+1/2 <= a <= sqrt((h+1)^2+2)-1/2.                       (3)

Thus all frames are parallel at equality, but the middle square has
horizontal freedom. Parallelism is not a lower-bound hypothesis.

This is the saved continuation's three-square cap argument, reconciled
against remote head 6aa2ff6. The proof and its rational identities were
checked before integration. Symbolic calculation was used to check the
identity (18), not as a premise for an unproved continuous inequality.

Put

    q0=(h+1)^2+9/4,       R0=sqrt(q0),
    ell=9/10,            X=h+ell,       P_+=(X,1/2), P_-=(X,-1/2).

It suffices to classify three-square packings in the critical cap with
R <= R0. The two marked points will meet every square in that cap.

## 1. A long vertical slice through every nonparallel square

Let S be one unit square in the critical cap. Write its unsigned frame
angle modulo right angles as 0 <= theta <= pi/4, and put

    c=cos(theta), s=sin(theta), L=c+s, D=c-s.

Its horizontal width is L, so its center p satisfies

    h+L/2 <= p_x <= R0-L/2.

The function R0-h decreases for h >= 0, and R0-h <= sqrt(13)/2 < 181/100.
The distances from X to the two ends of the containing strip [h,R0] are
both less than 91/100. Consequently

    |p_x-X| < 91/100-L/2 < L/2.                             (4)

The line x=X crosses the square away from its extreme horizontal points.
For s>0 its vertical chord length at horizontal center offset delta is

    1/c                                  if |delta| <= D/2,
    (L/2-|delta|)/(c*s)                   if D/2 <= |delta| < L/2.
                                                                    (5)

Intersecting the line with the four square sides gives these formulas;
reflection of the frame leaves them unchanged. The first length exceeds
one. The second also exceeds one, by (4) and

    L-c*s = L-(L^2-1)/2 >= sqrt(2)-1/2 > 91/100.

The quadratic decreases for 1 <= L <= sqrt(2), and the last comparison
uses sqrt(2)>141/100.

Hence every nonparallel S has a chord of length greater than one at X.
If neither P_+ nor P_- is in its open interior, that chord's lower end
is at least 1/2 or its upper end is at most -1/2. Reflection reduces to
the former. One of the two upward-pointing normals to a lower face,
n=(a,b) with b>0, then gives

    n dot p >= n dot P_+ + 1/2.                             (6)

The normal is not horizontal, by (4). For a nonparallel square its four
possible forms are (c,s), (s,c), (-s,c), (-c,s), where c>=s>0.
We exclude each form below. This is a reduction for one square, not a
simultaneous motion of the packing.

## 2. Normal (c,s)

Containment bounds either coordinate xi of p in a square side frame by

    |xi| <= rho0-1/2,       rho0=sqrt((h+1)^2+2).

This follows from the exact farthest-vertex norm. Moreover
rho0 <= h+sqrt(3) < h+7/4, so |xi| < h+5/4. But (6) gives

    xi >= Z=c(h+ell)+s/2+1/2,
    Z-h-5/4 >= (37/30)c+s/2-13/12 > 0.                    (7)

The first inequality uses h<=1/3 and c<=1. The final positive sinusoid
is concave on [0,pi/4], so its minimum is at an endpoint. The endpoint
differences are 3/20 and 26/(15 sqrt(2))-13/12>13/180, using
1/sqrt(2)>2/3. This contradicts the containment bound.

## 3. Normal (s,c)

Use the orthonormal frame n=(s,c), m=(c,-s), with local center
coordinates xi=n dot p and eta=m dot p. Set

    a0=h+L/2,       Z=s(h+ell)+c/2+1/2.

Then xi>=Z>0 and s*xi+c*eta>=a0. For a fixed xi, the smallest possible
squared farthest-vertex norm is

    f(xi)=(xi+1/2)^2+
          (max((a0-s*xi)/c,0)+1/2)^2.                    (8)

This function increases strictly for xi>=Z. On the branch a0-s*xi>0,
half its derivative has numerator

    xi-s*a0+c(c-s)/2

and positive denominator c^2. At xi=Z the numerator is
c^2+c/2+s(ell-c)>0: use c^2>=1/2, c>7/10 and ell-c>=-1/10.
It increases with xi. On the other branch half the derivative is
xi+1/2>0; continuity handles the transition. It remains to show f(Z)>q0.

### 3.1 Active cap constraint

If a0-s*Z>=0, the minimizing center in (8) has

    p_x=h+L/2,
    p_y=1/2+1/(2c)+(s/c)(ell-L/2).

Its rightmost vertex is (h+L,Y), where

    Y=1/2+c-s+ell*s/c > 3/2-(13/50)s.                    (9)

Indeed

    (3/2-Y)/s=1+s/(1+c)-ell/c,
    (37/50)c+c*s/(1+c)
       <= (37/50)c+s/2 <= sqrt((37/50)^2+1/4) < 9/10,

which is exactly (9). The compared heights are positive. Thus

    |(h+L,Y)|^2-q0
       > 2h(L-1)+s(2c-39/50)+(169/2500)s^2 > 0,          (10)

using h>=0 and c>=1/sqrt(2). This proves f(Z)>q0 on this branch.

### 3.2 Center on the normal ray

If a0-s*Z<0, then s>2/5. In fact

    a0-s*Z=c^2*h+c(1-s)/2-ell*s^2

is positive when s<=2/5, using c>9/10 there. The required difference is

    f(Z)-q0 = [s(h+ell)+c/2+1]^2-(h+1)^2-2.              (11)

It is concave in h, with quadratic coefficient -c^2. At h=0 and h=1/3,
respectively, the positive quantities inside its square exceed

    ell*s+c/2+1 > 181/100 > sqrt(3),
    (37/30)s+c/2+1 > 1169/600 > sqrt(34/9).

Here s ranges from 2/5 to 1/sqrt(2). Both sinusoids are concave in theta,
so their minimum is at an endpoint. At s=2/5 use c>9/10 for the first
and c>91/100 for the second. At the other endpoint use 1/sqrt(2)>2/3;
the second value exceeds 97/45>1169/600. The final square check is
(1169/600)^2-34/9=729/40000>0. Hence (11) is positive throughout
0<=h<=1/3, completing this normal case.

## 4. Normal (-s,c)

The cap and (6) imply

    p_x>=h+L/2,
    p_y>=1/2+1/(2c)+(s/c)(L/2-ell).

Increasing p_x increases the required lower bound on p_y. The top vertex
therefore has positive coordinatewise lower bounds

    V_T=(h+c,Y),       Y=1/2+s+(1-ell*s)/c.

Writing delta=Y-3/2, one has

    delta > s/10+(3/10)s^2.                               (12)

The difference between the two sides is

    s^2[(1-(9/10)s)/(c(1+c))-3/10].

The bracket is positive: its numerator
Q(s)=1-(9/10)s-(3/10)c-(3/10)c^2 strictly decreases on
[0,1/sqrt(2)], since Q'=-9/10+(3/10)s/c+(3/5)s<0.
Its last value is 17/20-3sqrt(2)/5>0, by 289/400>288/400.

Using h<=1/3, c>7/10, and (12),

    |V_T|^2-q0
      =-2h(1-c)-s^2+3delta+delta^2
      >s[3/10-(483/1000)s+(3/50)s^2+(9/100)s^3]>0.       (13)

For the first comparison use
9/100+(2/3)/(1+c)<9/100+20/51<483/1000.
The cubic bracket decreases on [0,71/100], because its derivative
-483/1000+(3/25)s+(27/100)s^2 is negative there. Its final value is
1952799/100000000>0. Since s<=1/sqrt(2)<71/100, (13) follows.

## 5. Normal (-c,s)

The center lower bounds become

    p_x>=h+L/2,
    p_y>=Y0:=1/2+[1/2+c(L/2-ell)]/s.

Here Y0>1/2, since cL>=1 makes the numerator at least
1-ell*c>=1/10. The top and right vertices have positive coordinatewise
lower bounds

    V_T=(h+s,Y0+L/2),
    V_R=(h+L,Y0+(c-s)/2).                                (14)

Subtract q0(h) from their squared norms. The results are affine functions
of h with slopes 2(s-1)<0 and 2(L-1)>0. The maximum of these two affine
functions, over the whole real line, is minimized at their intersection.
That intersection is

    h_*=(1+s)/(2c)-ell.

At h_* the lower-bound center (h_*+L/2,Y0) has zero coordinate in direction
(-c,s) and positive coordinate A in direction (s,c). Positivity follows
from h_*>=-2/5 and L/2>=1/2. Put

    k=(1+s)/c,       1<k<=1+sqrt(2)<5/2.

Then

    s=(k^2-1)/(k^2+1),       c=2k/(k^2+1),
    A+1/2=1+[(k/2)(k^2+3)-(9/10)(k^2+1)]/(k^2-1).

Substitution and clearing denominators give the exact identity

    (A+1/2)^2+1/4-q0(h_*)
       =[-35k^3+141k^2-145k+40]/[25(k^2-1)^2] > 0.       (15)

To prove its sign on the whole interval: when 1<=k<=9/5, write u=k-1
and the numerator becomes 1+32u+u^2(36-35u)>0, since 0<=u<=4/5.
On [9/5,5/2], its second derivative 282-210k is negative. Concavity
reduces the minimum to its endpoint values 793/25 and 95/8, both positive.
Thus at least one vertex in (14) lies outside the critical disk. This
excludes the fourth and final nonparallel normal case.

## 6. Two-point incidence and equality

We have proved that every nonparallel unit square in the critical cap
contains at least one of P_+,P_- in its open interior.

For an axis-parallel square, X is strictly inside its horizontal interval
by (4). Its center satisfies p_x>=h+1/2 and

    (p_x+1/2)^2+(|p_y|+1/2)^2<=q0,

so |p_y|<=1. If 0<p_y<1 it contains P_+ openly; if -1<p_y<0 it
contains P_- openly. At p_y=+1 or -1, containment forces p_x=h+1/2,
giving (2). At p_y=0 it is exactly one of (3), containing both marked
points on its boundary.

Every square therefore contains at least one marked point as a closed-set
point. The only ones containing neither openly are (2)-(3).
An open marked point in one square excludes even closed containment in
another: every neighborhood of a closed square point meets its interior.

If three packed squares are present and no middle square (3) is among
them, at most one square can contain each marked point. The only boundary
exceptions are the unique upper and lower squares (2), so there would be
at most two squares, a contradiction. If a middle square (3) is present,
it contains both marked points. Neither other square can contain one
openly. Both must therefore be among (2)-(3). Two different middle squares
overlap at (X,0), so the other two are exactly (2). They have vertices of
squared norm q0. This proves (1), its equality description, and sharpness.

## 7. Scope of application

This theorem counts three entire squares beyond one straight line. Three
centers on one side are not sufficient. In particular a square separated
from a central square only on its own rotated axis need not lie in any
central-side cap. The opposite-cap consequence retains this distinction.
