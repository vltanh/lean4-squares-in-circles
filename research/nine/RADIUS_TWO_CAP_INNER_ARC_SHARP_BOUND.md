# The sharp inner-arc bound for every unit in a radius-two cap above one quarter

Date: October 26, 2026.

**Status: complete hand strengthening, accepted after independent full-source
and equality-scope review in REVIEW_RADIUS_TWO_CAP_ARC_SHARP_BOUND_C6_2026_10_26.md.**
This source strengthens the accepted
RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md. It uses the same full
orientation domain and proves the equality case needed for a weak
available-interval endpoint. No parameter grid or coefficient packet
is used.

Let S be an actual unit square contained in a disk of radius R<=2
about the origin and wholly in an actual half-plane n dot p>=H,
where n is a unit vector and H>1/4. Put

\[
 r=5/4,\qquad \beta_0=\arcsin(2/5),\qquad \Lambda=2\beta_0.
\tag{1}
\]

**Sharp arc theorem.** The whole open-interior intersection of S with
the circle of radius r is one connected open arc containing its
radial-center point, of angular length at least Lambda. Equality
holds exactly when the actual center lies on an actual own side axis.

**Pair capacity theorem.** Two interior-disjoint such squares cannot
both have their full open arcs in one common circle interval of length
at most 2Lambda=4arcsin(2/5). The interval premise requires actual
routing; no geometric region is assigned to that interval here.

The constant is sharp for a single unit. For example
[1/2,3/2] times [-1/2,1/2] is contained in the radius-two disk,
has cap height1/2, and has exactly the arc (-beta_0,beta_0).

## 1. The accepted complete own-frame geometry

Use the actual ordered signed own axes of the quarter-turn source:

\[
 S=[A,a]\times[B,b],\quad A=a-1,\quad B=b-1,
 \quad a\ge b\ge1/2,\quad a^2+b^2\le4.
\tag{2}
\]

The center is (a-1/2,b-1/2). The accepted source already proves
the exact connected intersection interval in each of the exhaustive
cases a>r and a<=r, including their face endpoints. It also proves
that the radial-center point belongs to the open unit, from the
actual center norm lying strictly between3/4 and3/2. We retain those
statements and strengthen the length comparison below.

In the inner-face case a>r, its whole-domain convex estimate is

\[
 1/4<A<1,\qquad -1/2\le B<1/2,\qquad
 E:=A^2+B^2+\sqrt2 AB<3/5.
\tag{3}
\]

The exact closed interval, in the open right half-plane, is

\[
 [\beta,\min(\alpha,\gamma)],\qquad
 \alpha=\arccos(A/r),\quad\beta=\arcsin(B/r),\quad
 \gamma=\arcsin(\min(b/r,1)).
\tag{4}
\]

In the outer-face case a<=r, the original cap premise gives

\[
 0<B\le A\le1/4,\qquad k^2=A^2+B^2>1/16,
\tag{5}
\]

and the exact interval is

\[
 [\max\{\arccos(a/r),\arcsin(B/r)\},
   \min\{\arccos(A/r),\arcsin(b/r)\}].
\tag{6}
\]

The accepted fixed-k derivative shows that its outer-outer length is
minimized on the diagonal A=B=k/sqrt(2). These are full-interval
geometric results of the cited source, not sampled orientations.

## 2. The inner-face length is at least Lambda, with an exact equality case

The exact double-angle values are

\[
 \cos\Lambda=17/25,\qquad \sin\Lambda=4\sqrt{21}/25.
\tag{7}
\]

The coefficient difference satisfies

\[
 0<8\sqrt{21}/25-\sqrt2<3/50.
\tag{8}
\]

Its positive sign follows from 1344/625>2. For the upper bound,
sqrt(21)<23/5 and sqrt(2)>353/250 give
8sqrt(21)/25-sqrt(2)<184/125-353/250=3/50;
both radical comparisons follow by positive squaring.
Since |AB|<1/2, (3) therefore gives

\[
 E_\Lambda:=A^2+B^2+\frac{8\sqrt{21}}{25}AB
       <\frac{63}{100}<\frac{289}{400}
       =r^2\cos^2\Lambda.
\tag{9}
\]

The last fixed reserve is37/400. Equation (9) is exactly

\[
 (A+B\sin\Lambda)^2
             <\cos^2\Lambda\,(r^2-B^2).
\tag{10}
\]

The right side is positive. Irrespective of the sign of the expression
on the left before squaring, its positive square-root upper bound gives

\[
 A<\cos\Lambda\sqrt{r^2-B^2}-B\sin\Lambda
                         =r\cos(\beta+\Lambda).
\tag{11}
\]

Here -beta_0<=beta<beta_0, and beta_0<pi/6 because 2/5<1/2.
Consequently 0<beta+Lambda<pi/2, so the decreasing principal cosine
comparison in (11) proves

\[
                              \alpha-\beta>\Lambda.
\tag{12}
\]

For b<=r, the other possible length in (4) is the whole strip function

\[
 D(b)=\arcsin(b/r)-\arcsin((b-1)/r).
\tag{13}
\]

It is nondecreasing for b>=1/2, and strictly increasing for b>1/2:
on the open interval its derivative has that sign because
b>|b-1| for b>1/2. Continuity includes b=r. Therefore

\[
 D(b)\ge D(1/2)=2\arcsin(2/5)=\Lambda,
\tag{14}
\]

with equality precisely at b=1/2. For b>r, gamma=pi/2 and
beta<beta_0<pi/6 give gamma-beta>Lambda directly.
Equations (12)--(14) prove the desired arc lower bound in this entire
case. Equality holds precisely at b=1/2, and then its exact open arc
is (-beta_0,beta_0) about the center's actual radial own axis.

## 3. Every outer-face length is strictly greater than Lambda

As in the quarter-turn source, the length in (6) is the minimum of
four upper-minus-lower differences. The two opposite-face differences
are D(a),D(b), strictly greater than Lambda since a,b>1>1/2.

The inner-inner difference is at least

\[
 \pi/2-2\arcsin(1/5)>\pi/3>\Lambda.
\tag{15}
\]

For the first strict comparison, sin(pi/12)=(sqrt(6)-sqrt(2))/4>1/5,
using sqrt(6)>12/5 and sqrt(2)<8/5. For the second, beta_0<pi/6.

For the outer-outer difference, the accepted whole fixed-k derivative
and k>1/4 give the strict lower bound

\[
 2\arcsin\left(\frac{4+1/\sqrt2}{5}\right)-\pi/2.
\tag{16}
\]

It exceeds Lambda because

\[
 \frac{4+1/\sqrt2}{5}
      >\sin(\pi/4+\beta_0)
      =\frac{\sqrt{21}+2}{5\sqrt2}.
\tag{17}
\]

After multiplying by the positive denominator, (17) is
4sqrt(2)-1>sqrt(21). Both sides are positive, and the squared
reserve is12-8sqrt(2)>0, using sqrt(2)<3/2. Both angles are on
the increasing principal sine branch. Thus all four complete
differences in (6) exceed Lambda, including a=r. There is no equality
case in this part of the domain.

Together Sections2--3 show that equality is exactly b=1/2 in (2),
which says precisely that one actual center own-coordinate vanishes.
The cap premise keeps the other coordinate positive and a>r.

## 4. The weak common-interval endpoint still excludes two squares

Suppose two actual units have disjoint open interiors and both full
open arcs lie in one circle interval of length at most2Lambda.
Their arcs are disjoint, each of length at least Lambda. Hence all
these length inequalities would have to be equalities. Both units
therefore have radial own axes, each arc has half-width beta_0 about
its radial-center direction, and the two arcs fill the interval up
to endpoints. Their center directions differ by exactly2beta_0 and
the adjacent arc endpoints coincide at one point p on the radius-r
circle.

In the ordered actual radial axes of either unit, p has coordinates

\[
             (r\cos\beta_0,\ \pm r\sin\beta_0)
                       =(\sqrt{21}/4,\ \pm1/2).
\tag{18}
\]

Both radial coordinates are strictly between the corresponding unit's
inner and outer faces: by (3), the inner coordinate A<1, while
sqrt(21)/4>1 and the outer coordinate a>r>sqrt(21)/4. Move p a
sufficiently small positive distance toward the origin, replacing it
by (1-epsilon)p. Its radial coordinates stay strictly between both
units' radial faces, while both absolute transverse coordinates become
(1-epsilon)/2<1/2. The new point lies in both open unit interiors,
a contradiction.

This proves the pair capacity theorem even when the available interval
length is only weakly bounded by2Lambda. It does not assume positive
circle weights on either extra or a preferred orientation; the radial
orientation arises only from its fully proved equality case.

For later exact gap comparisons,

\[
 \cos(2\Lambda)=-47/625,\qquad
 \sin(2\Lambda)=136\sqrt{21}/625.
\tag{19}
\]

An application still has to establish the actual common available
interval and its routing. This theorem supplies neither a C6 force
equation nor an unproved endpoint gap. Every original square, mean,
mask, individual weight and slider is retained. No original parent
gate, global nine-square theorem, Lean compilation or CI is asserted.
