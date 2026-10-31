# Every unit with center norm at least23/25 occupies an inner arc longer than43.5 degrees

**Status: complete whole-domain hand geometric theorem; root and separate
independent full hand and exact rational audits passed.**

Put
\[
           Q=1105/256,\qquad r=5/4,\qquad \rho_0=23/25.
\tag{1}
\]
Let S be any closed unit square contained in the disk of radius sqrt(Q),
with center c satisfying |c|>=rho_0. It need not physically touch the
containing circle and has no stress or degree premise.

**Theorem.** The entire intersection of S's open interior with the
circle |p|=r is one connected open arc. It contains the point
\(r\,c/|c|\), and its angular length is strictly greater than
\[
                              29\pi/120=43.5^\circ.
\tag{2}
\]
All orientations and every containing-disk radius at most sqrt(Q)
are covered. In particular two such disjoint open units cannot
occupy a common free inner-circle interval of angular length at most
29pi/60=87 degrees.

The proof extends the complete inner-face argument of
ANNULAR_CENTER_ARC_BUDGET.md and supplies the full additional
outer-face domain needed below center norm one.

## 1. Exact own-frame and center ranges

Choose signs and order of S's own orthonormal axes so its center is
(x,y), with x>=y>=0. Write
\[
 \begin{gathered}
 k=\sqrt{x^2+y^2}\ge23/25,\qquad
 a=x+1/2,\quad b=y+1/2,\quad A=a-1,\quad B=b-1,\\
 S=[A,a]\times[B,b],\qquad a\ge b\ge1/2.
 \end{gathered}
\tag{3}
\]
The farthest actual corner has squared norm
\[
 q=a^2+b^2=k^2+x+y+1/2.
\]
Containment and x+y>=k give
\[
          q\le Q,\qquad
 q\ge(23/25)^2+23/25+1/2=2833/1250>9/4,
\tag{4}
\]
with exact last margin41/2500. The outer bound gives
\[
             a<81/40,\quad b<3/2,\quad
                 A<41/40,\quad -1/2\le B<1/2.
\tag{5}
\]
It also yields
\[
 k^2+k+1/2\le Q,\qquad
 k\le\sqrt{Q-1/4}-1/2<91/60.
\tag{6}
\]
Consequently |r-k|<1/2: its lower-center side is at most33/100,
and its upper-center side is less than4/15. Thus the point
\(r\,c/|c|\) lies in the open radius-1/2 disk about c, and hence
in the open interior of S. This will identify the radial direction
inside the single arc, without assuming a centered arc width.

## 2. Complete outer-face domain: a<=r

Here x<=3/4 and y<=x<=3/4. The center bound gives
\[
 y^2\ge(23/25)^2-9/16
              =1/4+339/10000>1/4.
\]
Thus
\[
                         0<A,B\le1/4,\qquad1<b\le a\le r.
\tag{7}
\]
S lies in the open first quadrant. Its exact closed inner-circle
intersection has angular interval
\[
 \left[
  \max\{\arccos(a/r),\arcsin(B/r)\},
  \min\{\arccos(A/r),\arcsin(b/r)\}
 \right].
\tag{8}
\]
We prove that each of the four possible upper-minus-lower differences
is greater than29pi/120. This proves existence and the strict length
bound for (8), and its open interval satisfies all four square
inequalities strictly.

Three differences are uniformly greater than pi/4. For any1/2<=z<=r,
the function
\[
                 \arcsin(z/r)-\arcsin((z-1)/r)
\]
is nondecreasing, because z>=|z-1| and the derivative of arcsin
increases with the absolute value of its argument. Its minimum is
\(2\arcsin(2/5)>\pi/4\). The strict comparison is
\(\sin(\pi/8)<2/5\), from
\(2-\sqrt2<16/25\). This treats both opposite-face strip differences,
using z=a or z=b.

For the inner-inner difference, (7) gives
\[
       \arccos(A/r)-\arcsin(B/r)
                 \ge\pi/2-2\arcsin(1/5)>\pi/4.
\tag{9}
\]
Here \(\sin(\pi/8)>1/4>1/5\), verified by \(\sqrt2<7/4\).

It remains to bound the entire outer-outer difference
\[
       L=\arcsin((x+1/2)/r)+\arcsin((y+1/2)/r)-\pi/2.
\tag{10}
\]
Fix k^2=x^2+y^2 and vary x>=y, with x,y<=3/4. On the open
range where both arcsin derivatives are finite, set
\(y=\sqrt{k^2-x^2}\). The sign of L'(x) is the sign of
\[
 \begin{split}
 &y^2\big(r^2-(y+1/2)^2\big)
                  -x^2\big(r^2-(x+1/2)^2\big)\\
 &\quad=(x-y)\left[(x+y)(k^2-21/16)+k^2+xy\right].
 \end{split}
\tag{11}
\]
All factors used to square the two derivative terms are nonnegative.
Throughout this full domain,
\[
                  4/5<k^2\le9/8<21/16,\qquad x+y\le3/2.
\]
The bracket in (11) therefore has the strict lower bound
\[
        \frac32\left(\frac45-\frac{21}{16}\right)
                       +\frac45=\frac1{32}>0.
\tag{12}
\]
So L is nondecreasing away from x=y on each complete fixed-k arc.
Continuity includes a=r or b=r, where an individual derivative may
be unbounded. The diagonal value is increasing in k. Hence
\[
 L\ge2\arcsin\left(\frac{1/2+(23/25)/\sqrt2}{5/4}\right)-\pi/2
       =2\arcsin\left(\frac{50+46\sqrt2}{125}\right)-\pi/2.
\tag{13}
\]

The argument in (13) is strictly larger than23/25, because
\(\sqrt2>65/46\), whose squared margin is7/2116.
The exact elementary comparison proved in Section5 is
\[
                        \cos(31\pi/240)<23/25.
\tag{14}
\]
Since
\[
             \sin(89\pi/240)=\cos(31\pi/240),
\]
monotonicity of arcsin on its actual principal range gives
\[
             L>2(89\pi/240)-\pi/2=29\pi/120.
\tag{15}
\]
This closes the full outer-outer case and therefore all of (8).
There is no subdivision of square orientations or sampled sign.

## 3. Complete inner-face domain: a>r

Now A>1/4. We reproduce the uniform comparison that permits the
earlier inner-arc proof at the lower center threshold. Define
\[
                  E=A^2+B^2+\sqrt2\,AB.
\]
We claim
\[
                           E<25/32=r^2/2.
\tag{16}
\]
For fixed q=a^2+b^2, put t=a+b. Exact expansion gives
\[
 E=(1-1/\sqrt2)q+t^2/\sqrt2-(2+\sqrt2)t+2+\sqrt2.
\tag{17}
\]
This is convex in t. For a>=b>=1/2, its full possible t interval
has endpoints b=1/2 and a=b. Enlarging to that full interval,
even when an endpoint fails the center constraint, preserves the
upper bound.

At b=1/2, A=sqrt(q-1/4)-1. Equations(4)--(5) give
\[
                       \sqrt2-1<A<41/40.
\]
In particular A>2/5. Using sqrt(2)>7/5, the increasing polynomial
A^2+1/4-(7/10)A gives
\[
 E=A^2+1/4-(\sqrt2/2)A
         <A^2+1/4-(7/10)A
         <933/1600<25/32.
\tag{18}
\]
At a=b=sqrt(q/2)>1, the value
\((2+\sqrt2)(\sqrt{q/2}-1)^2\) increases with q.
The exact outer-radius bound sqrt(Q)<25/12 gives
\[
           E<\frac{626-287\sqrt2}{288}<25/32.
\tag{19}
\]
The last comparison follows by squaring401<287sqrt(2):
\(401^2<2\cdot287^2\). Thus convexity proves(16) on the whole domain.

The other required sign is also retained at the smaller center norm.
Since x>=y>=0,
\[
 (\sqrt2 x+y)^2-2(x^2+y^2)=y(2\sqrt2 x-y)\ge0.
\]
Consequently
\[
 \sqrt2 A+B
 \ge\frac{21}{50}\sqrt2-\frac12
 >\frac{21}{50}\frac75-\frac12
 =\frac{11}{125}>0.
\tag{20}
\]
No boundary-square or positive-load premise enters(16)--(20).

## 4. Exact connected arc in the inner-face domain

Use
\[
 \alpha=\arccos(A/r),\quad
 \beta=\arcsin(B/r),\quad
 \gamma=\arcsin(\min(b/r,1)).
\tag{21}
\]
The bounds(5) imply
\[
                  A^2+B^2<2081/1600<r^2.
\]
Thus beta>-alpha. Every S point has positive first coordinate,
the outer first face lies beyond the inner circle, and the exact
closed inner-circle intersection is the single interval
\[
                            [\beta,\min(\alpha,\gamma)].
\tag{22}
\]
Equations(16),(20) give
\[
      0<\sqrt2 A+B<\sqrt{r^2-B^2},
      \qquad A<r\cos(\beta+\pi/4).
\]
Here |B|<=1/2 gives |beta|<pi/4, so beta+pi/4 lies in(0,pi/2).
Cosine comparison is therefore on its strictly decreasing interval,
and
\[
                               \alpha-\beta>\pi/4.
\tag{23}
\]
If b<=r, the same full strip comparison used in Section2 gives
\(\gamma-\beta\ge2\arcsin(2/5)>\pi/4\).
If b>r, gamma=pi/2 and beta<pi/4 give that conclusion directly.
The endpoint b=r is covered by continuity or either formula.

Thus(22) has length strictly greater than pi/4, stronger than(2).
Its open interval satisfies every square inequality strictly.
Together with Section2, this proves that the entire open intersection
is one connected arc in every orientation. Equation(6) places the
actual radial-center point inside that arc.

## 5. Exact trigonometric comparison without a numerical angle premise

We give all rational constants used in(14). First,
\[
                                 \pi>25/8.
\tag{24}
\]
Indeed sin(t)<t for0<t<pi/2 and the exact half-angle formula give
\[
 \pi>24\sin(\pi/24)
          =12\sqrt{\,2-\sqrt{2+\sqrt3}\,}.
\]
We have \(\sqrt3<97/56\), since \(97^2-3\cdot56^2=1\).
For W=17807/9216,
\[
             W^2-\frac{209}{56}
                      =\frac{706855}{594542592}>0.
\]
As \(2+\sqrt3<209/56<W^2\), it follows that
\[
 2-\sqrt{2+\sqrt3}>2-W=625/9216.
\]
Taking positive square roots yields(24).

Now set z=155/384. Equation(24) gives
\[
                         31\pi/240>z.
\]
Both angles lie in(0,pi/2), where cosine is strictly decreasing.
Taylor's theorem for cosine, with its signed sixth-order remainder
on(0,pi/2), gives
\[
 \cos(31\pi/240)<\cos z
          <1-z^2/2+z^4/24<23/25.
\tag{25}
\]
The exact final rational reserve is
\[
 \frac{23}{25}-(1-z^2/2+z^4/24)
            =\frac{4682051447}{13045963161600}>0.
\tag{26}
\]
This proves(14). Every comparison is exact on its full stated interval.

## 6. Disjoint-arc consequence and precise application scope

Different interior-disjoint units have disjoint open arcs on the
same circle. If two units satisfying the center bound were both
routed into one free inner-circle interval of length at most87degrees,
their open arcs would have combined length strictly greater than
\(2\cdot43.5^\circ=87^\circ\), impossible.

Routing is a separate geometric obligation: the center-norm bound
alone does not identify a particular complementary pocket or free
circle interval. The unique-arc and radial-center conclusions in
Sections1--4 may be used in a complete such routing proof. No unit
is moved or rotated, and no physical obstacle is discarded.

This theorem has no force, physical circle-touching, generic selection
or canonical-minimizer premise. The seven exact rational margins
recorded above were reconstructed independently by the root in
integer arithmetic. No angle sampling, polynomial box subdivision,
Lean compilation or CI is used.
