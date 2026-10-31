# Both lower regions of the entire exact S/S wall family are empty

**Status: complete hand exclusion; root and independent full hand audits passed.**

Use the entire exact family in DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md:
\[
 \begin{gathered}
 x=(\sqrt{70}-8)/4,\quad \delta=x^2,\quad
 d=1+\delta,\quad u=1-\delta,\quad m=d+\tfrac12,\\
 f=1-2x,\quad v=f+1=2-2x,\qquad R^2=u^2+v^2,\\
 A=[\delta,d]\times[t-1,t],\\
 B=[-u,\delta]\times[-f,2x],\qquad
 C=[-u,\delta]\times[-v,-f],\\
 x(1-2x)/(1-x)\le t<2x.
 \end{gathered}
\tag{1}
\]
The two S leaves are
\[
 L_A=[d,d+1]\times[-1/2,1/2],\qquad
 L_B=S_d(e_B),\quad e_B=(-u,2x)/d.
\tag{2}
\]
The exact elementary bounds needed below are
\[
 \frac1{11}<x<\frac1{10},\quad 0<\delta<\frac1{100},\quad
 d<\frac{101}{100},\quad m<\frac{151}{100},\quad
 \frac45<f<\frac56,\quad \frac95<v<2,\quad v>d.
\tag{3}
\]
In particular \(R^2=u^2+v^2\) and
\[
                        d^2+v^2=R^2+4\delta>R^2.
\tag{4}
\]

The actual two-ray screening proved in
DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md puts each additional unit
square entirely in the upper wedge between \(e_A=(1,0)\) and
\(e_B\), or in its complementary lower sector. The upper wedge
has already been bounded by three squares.

**Theorem.** No additional unit square can belong to the complementary
lower sector, uniformly for every t in (1). Whole-square routing,
including possible turns around the bottom of C or the right end of
A, is proved below rather than assumed.

## 1. Every lower-sector center is to the right of the column

The full column and a fixed central rectangle are actual obstacles:
\[
 K=B\cup C=[-u,\delta]\times[-v,2x],\qquad
 H=[-u,d]\times[-f,0]\subseteq A\cup B.
\tag{5}
\]
The second inclusion follows from \(0<t<2x\). Let \((X,Y)\)
be the center of a proposed lower-sector square T.
Every unit-square center in this disk has norm at most m, by the
farthest-corner bound in the upper-capacity source. Its open inscribed
half-radius disk is disjoint from every core interior, so
\[
                 \operatorname{dist}((X,Y),K)\ge1/2.
\tag{6}
\]

Suppose X<=delta. We show that its center would be less than one
from the center
\[
                          \ell=m e_B=(-mu/d,2xm/d)
\tag{7}
\]
of the B leaf, contradicting the disjoint inscribed disks.

First let \(Y\le2x\). Since \(Y\ge-m>-v\), the center height
is within K's vertical interval. Equation (6) forces
\(X\le-u-1/2\), and hence
\[
                         |Y|\le\sqrt6\,x.
\tag{8}
\]
Indeed \(m^2-(u+1/2)^2=6\delta=6x^2\).
Both X and \(\ell_x\) belong to \([-m,-u]\), of width
\(m-u=1/2+2\delta<3/5\). Also
\[
          \ell_y<3x,\qquad \ell_y>2x\ge Y,
          \qquad \ell_y-Y<(3+\sqrt6)x<11/20<3/5.
\]
Thus \(|(X,Y)-\ell|^2<18/25<1\), impossible.

Now let \(Y>2x\). A lower-sector center with positive y-coordinate
must have X<0 and angle between the B-leaf ray and the negative
horizontal axis. Therefore
\[
                   2x<Y\le-\frac{2x}{u}X\le\frac{2xm}{u}.
\tag{9}
\]
The excess over the top of K is less than
\[
                  2x\frac{m-u}{u}<2x<1/5<1/2,
\]
because \(m-u<u\). Equation (6) therefore forces X<-u.
Both \((X,Y)\) and \(\ell\) lie in the rectangle
\[
                      [-m,-u]\times[2x,2xm/u].
\]
Its width is less than 3/5 and its height less than 1/5, so its
squared diameter is less than \(2/5<1\). This is the second
contradiction.

Consequently
\[
                              X>\delta.
\tag{10}
\]
A lower-sector center with positive X must have Y<0. Since
\(-m\le Y<0\) lies strictly inside K's vertical interval, (6)
sharpens (10) to
\[
                              X\ge\delta+1/2.
\tag{11}
\]

## 2. Actual half-plane routing and complete center bounds

Every point of T has x-coordinate at least
\(X-1/\sqrt2>\delta-1=-u\). If T had a point of positive
height, the segment from its negative-height center to that point
would cross \(y=0\) in its open interior at x>-u. That whole
horizontal ray is blocked: B covers \([-u,\delta]\), A covers
\([\delta,d]\), \(L_A\) covers \([d,d+1]\), and the radial
outer-face screen excludes x>=d+1. Thus
\[
                               T\subseteq\{y\le0\}.
\tag{12}
\]
This is whole-square containment, not an inference from the sign
of the center alone.

The center must have \(Y<-f\). Otherwise its height belongs
to H's interval; avoiding H would require \(X\ge d+1/2=m\),
contradicting the center-radius bound and Y<0.

Next suppose \(X\ge d\). Since \(X\le m<d+1\), avoiding
\(L_A\) with the open half-radius center disk gives \(Y\le-1\).
Write \(W=-Y>0\). The radius bound then gives
\[
 X<8/7,\qquad X-d<1/7,\qquad
 W^2\le m^2-d^2=d+1/4<63/50<81/64.
\]
Thus \(W<9/8\), while \(f>4/5\). The squared distance to
the corner \((d,-f)\) of H is
\[
 (X-d)^2+(W-f)^2
       <\frac1{49}+\left(\frac{13}{40}\right)^2<\frac14,
\tag{13}
\]
contradicting center-disk clearance from H. We have proved
\[
 \delta+\tfrac12\le X<d,\qquad
 W:=-Y\ge f+\tfrac12,\qquad
 W\le m<151/100<v.
\tag{14}
\]
The vertical inequality uses clearance from H once X is inside
its horizontal interval. Equations (12), (14), and the already
proved bound that every point of T has x>-u retain all orientations.

## 3. Exact orientation coordinates

If T is axis-aligned, (14) already puts it wholly in
\(x\ge\delta,\ y\le-f\). Otherwise represent its frame, after a
quarter-turn if needed, with
\[
 a\ge b>0,\quad a^2+b^2=1,\qquad
 h=(a+b)/2,\quad k=(a-b)/2,\quad
 j=\tfrac12-k=\frac{1-a+b}{2}\le b.
\tag{15}
\]
There are two signs of tilt.

For positive tilt the extreme vertices relative to the center
\((X,-W)\) are
\[
       \text{left }(-h,k),\quad
       \text{top }(k,h),\quad
       \text{right }(h,-k),\quad
       \text{bottom }(-k,-h).
\tag{16}
\]
The left vertex's height is strictly between -v and -f:
\[
                       -v<-W+k<-f.
\]
If that vertex had x<delta it would be inside C, since every
point of T has x>-u. Therefore positive tilt always gives
\[
                              \min_T x\ge\delta.
\tag{17}
\]

For negative tilt the corresponding relative extreme vertices are
\[
       \text{left }(-h,-k),\quad
       \text{top }(-k,h),\quad
       \text{right }(h,k),\quad
       \text{bottom }(k,-h).
\tag{18}
\]
Its top vertex has x-coordinate strictly between delta and d:
\(X-k>\delta\) and \(X-k<d\), by (14), b>0.
If its height exceeded -f, (12) and the strict slider bounds
would put it in the open interior of A. Hence negative tilt
always gives
\[
                              \max_T y\le-f.
\tag{19}
\]

It remains to handle possible wrapping in the other coordinate
and the case where neither coordinate wraps. All three cases give
an actual corner beyond the containing circle.

## 4. Wrapping around the right end of the central rectangle is impossible

Take positive tilt and suppose \(\max_Ty>-f\).
Its top vertex, by (12), is at height between -f and 0. Its
x-coordinate must be at least d, or it would lie in H. Thus
\[
                              X\ge d-k.
\]
Its rightmost vertex consequently has
\[
                  x\ge d+b,\qquad -y\ge v-j.
\]
The squared radius of that actual corner is at least
\[
                          (d+b)^2+(v-j)^2.
\tag{20}
\]
Using \(j=b(1+b/(1+a))/2\), its excess over \(R^2=u^2+v^2\)
is exactly
\[
 \begin{split}
 4\delta
 &+b(2d-v)\\
 &+b^2\left[1-\frac{v}{1+a}
                  +\frac14\left(1+\frac{b}{1+a}\right)^2\right].
 \end{split}
\tag{21}
\]
Every displayed contribution is positive or nonnegative, and the
first is strictly positive. Indeed \(2d>2>v\), while
\(a\ge1/\sqrt2>2/3\), \(v<2\), and therefore the bracket is
greater than \(5/4-6/5=1/20\).
Thus (20) exceeds \(R^2\), a contradiction.

## 5. Wrapping below the bottom of C is impossible

Take negative tilt and suppose \(\min_Tx<\delta\).
Its leftmost vertex has x>-u and height less than -f. By (19)
and nonoverlap with C it must lie at or below -v. Consequently
\[
                              W\ge v-k.
\]
The bottommost vertex then has
\[
                 x\ge d-j>0,\qquad -y\ge v+b.
\]
Its squared norm is at least
\[
                             (d-j)^2+(v+b)^2.
\tag{22}
\]
The excess over \(R^2\) is
\[
 4\delta-2dj+j^2+2vb+b^2
      \ge4\delta+2(v-d)b+j^2+b^2>0,
\tag{23}
\]
using j<=b and v>d from (3). This is another contradiction.

## 6. The remaining quadrant cannot contain a unit square

After Sections4--5, T lies wholly in
\[
                         x\ge\delta,\qquad y\le-f.
\tag{24}
\]
Its center therefore has \(X\ge\delta+h\), \(W\ge f+h\).

For positive tilt, the rightmost actual vertex has squared norm at
least
\[
                       (\delta+a+b)^2+(f+a)^2.
\]
Subtract \(d^2+v^2=(\delta+1)^2+(f+1)^2\). The difference is
\[
 2\delta(a+b-1)+2ab-b^2-\frac{2fb^2}{1+a}
 \ge2\delta(a+b-1)+b^2\left(1-\frac{2f}{1+a}\right)\ge0.
\tag{25}
\]
The last bracket is positive because \(2f<5/3<1+a\).

For negative tilt, the bottommost actual vertex has squared norm at
least
\[
                       (\delta+a)^2+(f+a+b)^2.
\]
Its difference from \(d^2+v^2\) is
\[
 2f(a+b-1)+2ab-b^2-\frac{2\delta b^2}{1+a}
 \ge2f(a+b-1)+b^2\left(1-\frac{2\delta}{1+a}\right)\ge0.
\tag{26}
\]
The axis-aligned case is included by b=0. Thus every orientation
has an actual corner with squared norm at least
\(d^2+v^2=R^2+4\delta>R^2\), by (4). This excludes (24).

## 7. Full lower-region conclusion

A proposed lower-sector square first has its center forced to the
right of the whole B/C column by Section1. Section2 proves the
actual lower-half-plane containment and all center constraints.
Sections3--6 exclude both ways an oblique square might wrap an
obstacle endpoint and then exclude the remaining whole quadrant.
No lower-region square remains, for any t in the complete slider
interval.

Together with DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md, every exact
S/S wall core admits at most three further unit squares. This is a
capacity statement about all four proposed extras, with arbitrary
frames and contacts. The whole distinct-S/S family follows after
the audited parallel-articulation reduction and wall classification;
the parent-cell assembly may cite these complete implications.

No sampled pose, independent-per-pocket assumption, Lean compilation
or CI is used.
