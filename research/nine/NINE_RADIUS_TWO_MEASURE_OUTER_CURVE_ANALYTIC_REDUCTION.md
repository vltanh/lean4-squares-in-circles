# The whole outer measure curve reduces to three fixed charges

Date: October 26, 2026.

**Current dependency update, October 27:** all three fixed mass targets
and the derivative target below now have direct analytic proofs in
NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md, Sections 4--5.
The complete branch cover, monotonicity, convexity and tangent assembly
below are unchanged. The full acceptance is recorded in
ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md. The checker, rounded
common rectangles and stored margins remain historical alternatives;
explicit rational/Taylor arithmetic remains in the current proof.

**Status: accepted complete analytic monotonicity/convexity reduction and
exact fixed checks**, after full reviews in
REVIEW_NINE_MEASURE_OUTER_REDUCTION_ROOT_2026_10_26.md and
REVIEW_NINE_MEASURE_OUTER_THREE_POINT_C6_2026_10_26.md.
This replaces97 outer charges and three empty leaves by three fixed
mass checks and one fixed derivative enclosure. The original208-check
programs remain historical alternatives. The complete current global
join is NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.

Use exactly the measure of NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md.
Its accepted outward-comparison theorem reduces every normalized square
with a>=27/20 to
\[
 S_b=[a-1,a]\times[b-1,b],\qquad
 a=\sqrt{4-b^2},\qquad1/2\le b\le\sqrt2.
\tag{1}
\]
This is a measure comparison, not a displacement of any packing unit.
The origin and the circle of radius 1/10 contribute zero on (1), since
\(a-1\ge\sqrt2-1>1/10\). Put
\[
 r_1=1,\quad r_2=11/10,\quad r_3=27/20,
 \qquad(w_1,w_2,w_3)=(3858,2424,1709).
\]
If L_j(b) is the actual unnormalized angular length of the circle
intersection at radius r_j, its complete measure is
\[
                    M(b)=\frac{\sum_jw_jL_j(b)}{2000\pi}.
\tag{2}
\]
We prove the uniform bound
\[
                         \boxed{M(b)>3013/3000>1.}
\tag{3}
\]
The independent fixed-check entry point is
NINE_RADIUS_TWO_MEASURE_OUTER_THREE_POINT_CHECK.py.

## 1. Exact branch cover of the three circle intersections

Write A=a-1 and w=b-1. Every measure circle has only its positive
x branch in the square: A>0. Its upper x bound is inactive because
\(a\ge\sqrt2>27/20\). Thus at any r>=1, with
\(t_r=\sqrt{r^2-A^2}>0\), the exact angular interval is
\[
 \left[\arcsin\frac{\max(w,-t_r)}r,
        \arcsin\frac{\min(b,t_r)}r\right].
\tag{4}
\]
The possible face coincidences have zero angular measure and remain
included by continuity.

Define the three exact transition values
\[
 b_0=\frac{5-\sqrt7}{4},\qquad
 b_1=\frac{\sqrt{16359}}{200},\qquad
 b_2=\frac{\sqrt{944559}}{800}.
\tag{5}
\]
They satisfy
\[
 1/2<b_0<3/5<b_1<13/20<1<13/12<6/5<b_2<5/4<\sqrt2.
\tag{6}
\]
Each comparison follows by positive squaring; in particular
\(b_1^2=16359/40000\) and \(b_2^2=944559/640000\).

The complete arc formulas are conveniently expressed using
\[
 h_r(b)=\arcsin(b/r)-\arcsin((b-1)/r),
\]
\[
 g_r(b)=\arccos((a-1)/r)-\arcsin((b-1)/r).
\tag{7}
\]
The resulting exhaustive cover is
\[
 L_1(b)=
 \begin{cases}
 2\arccos(a-1),&1/2\le b\le b_0,\\
 g_1(b),&b_0\le b\le\sqrt2,
 \end{cases}
\]
\[
 L_2(b)=
 \begin{cases}h_{11/10}(b),&1/2\le b\le b_1,\\
 g_{11/10}(b),&b_1\le b\le\sqrt2,
 \end{cases}
\qquad
 L_3(b)=
 \begin{cases}h_{27/20}(b),&1/2\le b\le b_2,\\
 g_{27/20}(b),&b_2\le b\le\sqrt2.
 \end{cases}
\tag{8}
\]

Here is a direct check of all transitions. The upper clipping changes
when \(t_r=b\), equivalently \(a=(5-r^2)/2\). At r=1 it
always clips, because a<2. The other two values are respectively
a=379/200 and a=1271/800, giving exactly b1 and b2 in (5).
For r=1, lower clipping changes when the opposite vertex has norm1:
\((a-1)^2+(b-1)^2=1\), equivalently a+b=5/2. The increasing
sum a+b gives the unique relevant root b0. For r>=11/10 there
is no lower clipping at all, since
\[
 (a-1)^2+(b-1)^2\le5-\sqrt{15}<6/5<(11/10)^2.
\tag{9}
\]
For (9), the sum a+b is minimized at b=1/2, and sqrt(15)>19/5.
These calculations establish the whole branch cover, not just its
values at three selected squares.

## 2. A whole-domain convexity lemma for every capped circle

For every r>=1, the function g_r in (7) is strictly decreasing on
\([1/2,\sqrt2)\) and strictly convex on \([1/2,\sqrt2]\).
All its radicals are positive on this interval. To prove this, put
\[
                 t=\sqrt{r^2-(a-1)^2},\qquad
                 v=\sqrt{r^2-(b-1)^2}.
\]
Direct differentiation gives
\[
 g_r'=\frac{b}{at}-\frac1v,\qquad
 g_r''=\frac{4t^2-ab^2(a-1)}{a^3t^3}-\frac{b-1}{v^3}.
\tag{10}
\]

For the first derivative put s=a+b. The exact difference of squares is
\[
 b^2v^2-a^2t^2
   =-(a-b)\bigl((s-2)^2+(r^2-1)s\bigr)<0
                          \quad(b<\sqrt2).
\tag{11}
\]
Here a>b, s>2 and r>=1. Both compared factors are positive, so
g_r'<0. At the diagonal a=b its derivative is zero.

For the second derivative the key exact identity is
\[
       4t^2-ab^2(a-1)=a(2-a)^2(a+3)+4(r^2-1)>0.
\tag{12}
\]
If b<=1, (10)--(12) immediately give g_r''>0.
If b>=1, then a-1>=b-1>=0 and hence t<=v. Thus
\[
 g_r''\ge
 \frac{a\{a^2(a-b)-8a+12\}+4(r^2-1)}{a^3t^3}.
\tag{13}
\]
The bracket in this expression is positive throughout the entire
domain. Indeed a+b<=2sqrt(2) and sqrt(2)<99/70 give
\[
 a^2(a-b)-8a+12
 \ge2a^3-2\sqrt2a^2-8a+12
 >p(a):=2a^3-\frac{99}{35}a^2-8a+12.
\tag{14}
\]
Set y=a-7/4. Since a>=sqrt(2)>7/5, y>-7/20, and
\[
 p(a)=\frac9{160}+\frac{19}{40}y
                  +y^2\left(\frac{537}{70}+2y\right)
       \ge\frac9{160}+\frac{19}{40}y+6y^2>0.
\tag{15}
\]
The final quadratic has negative discriminant, with exact reserve
\(4\cdot6\cdot(9/160)-(19/40)^2=1799/1600>0\).
This proves g_r''>0 without any subdivision of b or r.

The strip function h_r is increasing for b>=1/2 and b<r, and
strictly convex there:
\[
 h_r'=\frac1{\sqrt{r^2-b^2}}-\frac1{\sqrt{r^2-(b-1)^2}}\ge0,
\]
\[
 h_r''=\frac{b}{(r^2-b^2)^{3/2}}
          -\frac{b-1}{(r^2-(b-1)^2)^{3/2}}>0.
\tag{16}
\]
For b<=1 the second sign is immediate. For b>=1, the function
\(x/(r^2-x^2)^{3/2}\) is strictly increasing for 0<=x<r,
which proves it. The zero derivative h_r'(1/2) is retained.

## 3. The initial and final ranges reduce to the two endpoints

For 1/2<=b<=b1, both L2 and L3 are increasing strip functions.
The first term increases up to b0 and then decreases to b1, so its
minimum on this entire range is one of L1(1/2),L1(b1). In fact
\[
                            L_1(b_1)>3/4>L_1(1/2).
\tag{17}
\]
For the first comparison, a(b1)-1=179/200 and b1<13/20, so
\[
 g_1(b_1)=\arccos(179/200)+\arcsin(1-b_1)
                         >2/5+7/20=3/4.
\]
Here \(\cos(2/5)\ge1-(2/5)^2/2=23/25>179/200\),
and asin(x)>=x for x>=0. For the other comparison,
\(\sqrt{15}/2-1>187/200\), with squared reserve
\(15-(387/100)^2=231/10000\). The signed cosine bound gives
\[
 \cos(3/8)\le1-(3/8)^2/2+(3/8)^4/24
                 <187/200,
\]
where the last reserve is 3677/819200. Thus
\(2\arccos(\sqrt{15}/2-1)<3/4\), as needed.

Every summand in (2) is therefore at least its b=1/2 value on
the entire initial range. Consequently
\[
                         M(b)\ge M(1/2)
                              \quad(1/2\le b\le b_1).
\tag{18}
\]

For b2<=b<=sqrt(2), all three terms are capped functions g_r.
By (11) they decrease to the common diagonal endpoint. Hence
\[
                         M(b)\ge M(\sqrt2)
                              \quad(b_2\le b\le\sqrt2).
\tag{19}
\]
Both endpoint charges are included among the three fixed checks below.

## 4. One fixed tangent controls the entire intervening range

On b1<=b<=b2, the exact formula is
\[
 M(b)=\frac{3858g_1(b)+2424g_{11/10}(b)
                         +1709h_{27/20}(b)}{2000\pi}.
\tag{20}
\]
The first two second derivatives are strictly positive by Section 2.
For the third use b>3/5, b<5/4 and r=27/20. Its second derivative
has the uniform lower bound
\[
 h_{27/20}''>
      \frac{3/5}{(27/20)^3}
       -\frac{1/4}{(13/10)^3}
       =\frac{4800}{19683}-\frac{250}{2197}>\frac18.
\tag{21}
\]
For b-1<=0 the subtracted term in (16) is nonpositive. Otherwise
0<b-1<1/4 and
\(r^2-(b-1)^2>44/25>(13/10)^2\), proving the same
upper bound for that subtracted term. The final exact reserve in
(21) is 585083/115316136.
It follows that
\[
 M''>\frac{1709}{16000\pi}>\frac1{30}.
\tag{22}
\]
The last comparison uses pi<22/7, with rational reserve
\(1709\cdot7/(16000\cdot22)-1/30=689/1056000\).

Take the single fixed point
\[
                             b_*=13/12,
                      \qquad a_*=\sqrt{407}/12.
\tag{23}
\]
It lies strictly between b1 and b2. The exact checker proves
\[
                         M(b_*)>201/200,
                         \qquad |M'(b_*)|<1/150.
\tag{24}
\]
The first is one common-rectangle measure bound. The derivative is
bounded by ordinary fixed radical intervals, as detailed in Section 5.

Let y=b-b_*. Integrating (22) along the entire intervening interval,
including its endpoints by continuity, gives
\[
 \begin{split}
 M(b)&>\frac{201}{200}-\frac{|y|}{150}+\frac{y^2}{60}\\
 &=\frac{3013}{3000}
             +\frac1{60}\left(|y|-\frac15\right)^2
 \ge\frac{3013}{3000}>1.
 \end{split}
\tag{25}
\]
This is one whole-domain strong-convexity proof. No root of M' is
numerically isolated or used as an exact parameter.

## 5. Explicit fixed derivative and mass checks

At (23), write w=1/12 and let
\[
 t_j=\sqrt{r_j^2-(a_*-1)^2},\quad
 v_j=\sqrt{r_j^2-w^2},\quad
 u_3=\sqrt{r_3^2-b_*^2}.
\]
The following coarse rational intervals suffice; each integer entry
is a numerator over 1000:

| Quantity | Lower numerator | Upper numerator |
| --- | ---: | ---: |
| a_* |1681|1682|
| t1 |731|733|
| t2 |863|864|
| v1 |996|997|
| v2 |1096|1097|
| u3 |805|806|
| v3 |1347|1348|

All are strict positive-square comparisons. For a*,v1,v2,u3,v3
the exact radicands are respectively
\[
                407/144,\quad143/144,\quad
                 121/100-1/144,\quad146/225,\quad817/450.
\]
For t1,t2 substitute the upper a bound for their lower radicands
and the lower a bound for their upper radicands. The lower/upper
squared reserves are respectively
\[
             (103/200000,21/20000),\qquad
             (107/1000000,257/1000000).
\tag{26}
\]
Thus no unknown radical is treated as an independently rounded value.

The exact derivative numerator at the tangent is
\[
 T=3858\left(\frac{b_*}{a_*t_1}-\frac1{v_1}\right)
   +2424\left(\frac{b_*}{a_*t_2}-\frac1{v_2}\right)
   +1709\left(\frac1{u_3}-\frac1{v_3}\right),
 \qquad M'(b_*)=T/(2000\pi).
\tag{27}
\]
Substituting lower denominators for upper positive terms and upper
denominators for lower positive terms, with signs reversed for the
negative terms, gives the strict rational bounds
\[
 -40<-\frac{1254291053647768750}{34246309814693847}
              <T<
       -\frac{798076820624315593050}{62929379411568326209}<0.
\tag{28}
\]
Since pi>3, (28) proves the derivative part of (24). The standalone
checker verifies every squared comparison and both enclosure endpoints
using exact rational arithmetic. This is one fixed derivative
enclosure, not a sign assertion at unproved parameter samples.

For the three mass checks use the same scales
\(B=83886080\), \(Q=2^{56}\) and outward pi bounds as the
accepted original measure checker. Every coordinate entry below is
an integer numerator over B:

| Fixed parameter | a_l | a_h | b_l | b_h |
| --- | ---: | ---: | ---: | ---: |
| b=1/2 |162444695|162444696|41943040|41943040|
| b=13/12 |141028166|141028167|90876586|90876587|
| a=b=sqrt(2) |118632832|118632833|118632832|118632833|

Integer square roots round each a interval outward. At the tangent,
the rational b enclosure is also outward, and the a bounds use its
opposite b endpoints. At the diagonal both identical intervals enclose
the same exact sqrt(2). The common open rectangle in each parameter
box is contained in the exact square at that fixed parameter.

The three large-circle contributions alone are charged. There is no
origin atom. At the higher target 201/200=1005/1000, their exact
integer margins
\[
              \sum_{j=1}^3w_jL_j-1005\cdot2P_+
\]
are respectively
\[
 2486115696770948576,\qquad
 1716983502928824028,\qquad
 336341375099883104,
\tag{29}
\]
where P_+ is the reviewed upper pi numerator over Q. All three
are positive. The checker uses the already independently reviewed
outward atan/asin/acos primitives and four-quadrant common-rectangle
formula, reproduced within the standalone file. No float is used.

Equations (18)--(19),(25),(29) prove (3) on the complete closed
outer curve. Every branch transition, b=1/2 and b=sqrt(2) is included.

## 6. Exact certificate reduction and integration boundary

This proof replaces the 97 current outer-curve charge leaves by three
fixed mass checks and one fixed rational derivative enclosure. It
also removes the three outer empty leaves: the continuous domain is
now directly the closed interval [1/2,sqrt(2)], so no superfluous
portion beyond sqrt(2) is subdivided and discarded.

Together with NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md,
the complete measure theorem would require 21 charge checks after
review and integration: 14 corner-box charges, 2 middle-box charges,
2 fixed line charges and 3 fixed outer charges. Three exact empty
tests remain in the corner rectangle. The one additional fixed
outer derivative enclosure is explicitly retained. This is 187 fewer
charge obligations than the accepted 208-check version, with no
loss of physical or orientation scope.

The currently accepted source and full checkers have not been altered
by this new manuscript. These reduced scalar sources and their fixed
checkers require independent review before becoming the current
global-measure dependencies. The measure theorem remains a finite
certificate, rather than a table-free result. The same nine original
units, all orientations and all physical contact or circle-weight
patterns remain. No Lean compilation or CI was run.
