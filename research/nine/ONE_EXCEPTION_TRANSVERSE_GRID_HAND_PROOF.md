# One exceptional pair: transverse rank-grid closure by a common point

Hand continuation after ec0d76e. All arguments below are hand derivations.
No numerical search or mathematical script is a proof input.

This note proves a new weak-four-chain endpoint obstruction, two universal
quadrant bounds, and the harder transverse ordering of an exceptional pair
in the full original three-by-three rank grid. It does not claim closure
of every one-exception configuration or of the unrestricted problem.

## 1. Notation and elementary bounds

Put
\[
 Q=\frac{1105}{256},\qquad
 r_0=\frac{91}{60},\qquad b_0=\frac1{60},\qquad c_0=\frac{59}{60}.
\]
All physical unit squares have disjoint open interiors and lie in a disk
centered at the origin with squared radius at most \(Q\).

For a square \(S\), write its center as \((x_S,y_S)\), its coordinate
projection halfwidth as \(h_S\), and put
\[
 \frac12\le h_S\le\frac1{\sqrt2},\qquad
 g_S=\frac1{4h_S},\qquad k_S=\sqrt{\frac12-h_S^2}.
\]
The absolute side-axis components are \(h_S+k_S,h_S-k_S\). In each
coordinate quadrant a vertex has offsets \(h_S,k_S\), in one order.
The square contains the aligned square of halfwidth \(g_S\).

The maximum squared corner norm is
\[
 |c_S|^2+\frac12+|c_S\cdot u_S|+|c_S\cdot v_S|
 \ge |c_S|^2+|c_S|+\frac12.
\]
Since
\[
 r_0^2+r_0+\frac12-Q=\frac{31}{57600}>0,
\]
every center satisfies \(|c_S|<r_0\).

An actual comparison \(S<_xT\) means
\(x_T-x_S\ge h_S+h_T\), including contact. Define \(<_y\) similarly.
The pair-span theorem already proved gives
\[
 \max(|\Delta x|,|\Delta y|)\ge g_S+g_T,\qquad h_S+g_S\ge1.
\]

## 2. A nonexceptional far endpoint of a weak four-chain cannot end a perpendicular three-chain

Suppose four distinct physical squares satisfy
\[
 x_B-x_A\ge g_A+g_B,\qquad B<_xC<_xD.
 \tag{1}
\]
No actual x-comparison is assumed for \(A,B\). Then \(D\) cannot be
the upper or lower endpoint of any actual y-three-chain.

Indeed,
\[
 x_D-x_A
 \ge g_A+g_B+h_B+2h_C+h_D
 \ge g_A+2+h_D.
\]
Thus, setting
\[
 a_0=2-r_0+\frac1{2\sqrt2}
     =\frac{29}{60}+\frac1{2\sqrt2}>0,
\]
we have \(x_D>a_0+h_D\). If an actual y-three-chain ends above at \(D\),
then \(y_D>h_D-b_0\). Reflection handles the lower-end case.

Put \(h=h_D,\ k=\sqrt{1/2-h^2}\). The lower coordinate bounds
\(X=a_0+h,\ Y=h-b_0\) are positive, with \(X>Y\).
The outward vertex has offsets \(h,k\) in one order. Therefore
\[
 q>(a_0+h+k)^2+(2h-b_0)^2=:F(h).
 \tag{2}
\]
If the outward offsets are \(h,k\), the corresponding lower bound is
larger than the displayed one because \(X>Y\).

The function \(F\) is strictly concave on \(1/2<h<1/\sqrt2\):
\[
 k^3 F''(h)=4k^2(2k-h)-a_0-h<0.
\]
For \(2k-h\ge0\), the first term is at most \(1/2\), while
\(h\ge1/2\); for \(2k-h<0\) the conclusion is immediate.
Continuity extends the endpoint-minimum conclusion to the closed interval.

The two endpoint values are
\[
 F(1/2)=\frac{5701}{1800}+\frac18+\frac{89\sqrt2}{120},
\]
\[
 F(1/\sqrt2)=\frac{25}{8}+\frac{421}{1800}
                  +\frac{83\sqrt2}{120}.
\]
Using \(\sqrt2>7/5\), both exceed \(7789/1800\), and
\[
 \frac{7789}{1800}-Q=\frac{623}{57600}>0.
\]
This contradicts containment. The three-chain may share other squares
with (1); its being an actual three-chain ending at \(D\) is sufficient.

## 3. Universal quadrant bounds

If a square of halfwidth \(h\) has center coordinates satisfying
\[
 x\ge h+s,\qquad y\ge h+t,\qquad s,t>0,
\]
then
\[
 q\ge
 \min\left\{
 (1+s)^2+(1+t)^2,\
 (\sqrt2+s)^2+(1/\sqrt2+t)^2,\
 (\sqrt2+t)^2+(1/\sqrt2+s)^2
 \right\}. \tag{3}
\]
The same assertion holds after independently reflecting either coordinate.

To prove it, put \(k=\sqrt{1/2-h^2}\). An outward vertex gives either
\[
 F_{s,t}(h)=(2h+s)^2+(h+k+t)^2
\]
or \(F_{t,s}(h)\). Both are concave: direct differentiation gives
\[
 k^3F_{s,t}''(h)=4k^2(2k-h)-h-t<0.
\]
Their minima occur at \(h=1/2\) or \(h=1/\sqrt2\), giving (3).

Two rational consequences will be used:

| Whole-square location | Lower bound for \(q\) |
|---|---:|
| \(x-h\ge2/3,\quad y+h\le-3/10\) | \(4021/900>Q\) |
| \(x+h\le-1/3,\quad y+h\le-2/3\) | \(41/9>Q\) |

For the first row, the aligned endpoint is
\[
 (5/3)^2+(13/10)^2=4021/900.
\]
The smaller of the two other endpoints is
\[
 2731/900+(19/15)\sqrt2>4327/900>4021/900.
\]
For the second row the aligned endpoint is \(41/9\); the smaller other
endpoint is
\[
 55/18+(4/3)\sqrt2>443/90>41/9.
\]
These comparisons use only \(\sqrt2>7/5\).

## 4. A fixed point inside the outer exceptional square

Suppose
\[
 x_E-x_P\ge g_P+g_E,\qquad E<_xC<_xD,
 \tag{4}
\]
and \(P\) is the upper endpoint of an actual y-three-chain.
Then the following conclusions hold:
\[
 \frac{13}{20}<h_P<\frac{17}{25},\qquad
 Z:=\left(-\frac{59}{60},\frac13\right)\in\operatorname{int}(P),
 \tag{5}
\]
\[
 x_D>h_D+\frac{251}{255}>h_D+\frac{59}{60},
 \qquad |y_D|<\frac15. \tag{6}
\]

### 4.1. Coordinate bounds and the forced orientation

Write the center of \(P\) as \((-X,Y)\), and put
\(h=h_P,\ g=1/(4h),\ k=\sqrt{1/2-h^2}\).
The weak chain (4) and the actual y-three-chain give
\[
 X>c_0+g,\qquad Y>h-b_0. \tag{7}
\]
In particular \(X>4/3\) and \(Y>0\).

If the upper-left vertex of \(P\) had offset \((-h,k)\), containment
would give
\[
 q\ge(X+h)^2+(Y+k)^2
 >\left(\frac{119}{60}\right)^2+
       \left(\frac1{\sqrt2}-\frac1{60}\right)^2
 >\frac{7921}{1800}>Q.
\]
Here \(h+g\ge1,\ h+k\ge1/\sqrt2\), and \(1/\sqrt2>7/10\).

Thus its upper-left vertex has offset \((-k,h)\), and its left-lower
vertex has offset \((-h,-k)\). We may use the actual frame
\[
 u=(a,-b),\quad v=(b,a),\qquad a=h+k,\quad b=h-k.
\]
Both corner inequalities
\[
 q\ge(X+k)^2+(Y+h)^2,\qquad
 q\ge(X+h)^2+(Y-k)^2 \tag{8}
\]
are retained.

### 4.2. The exact halfwidth interval

First suppose \(1/2\le h\le13/20\). Put
\[
 S(h)=c_0+\frac1{4h}+k,\qquad
 G(h)=S(h)^2+(2h-b_0)^2.
\]
The first inequality in (8) and (7) give \(q>G(h)\).
On this interval,
\[
 S(h)>\frac{49}{30},\qquad
 \frac1{4h^2}+\frac hk\ge\frac{269}{169},\qquad
 2(2h-b_0)\le\frac{77}{30}.
\]
For the first bound use
\(k\ge\sqrt{31}/20>11/40\) and
\(S\ge59/60+5/13+11/40=2563/1560>49/30\).
Therefore
\[
 \frac12G'(h)
 =-S(h)\left(\frac1{4h^2}+\frac hk\right)+2(2h-b_0)
 <-\frac{168}{5070}<0.
\]
At \(h=13/20\), the same rational lower bound for \(S\) exceeds \(131/80\).
Hence
\[
 G(h)\ge G(13/20)>
 (131/80)^2+(77/60)^2
 =Q+\frac{43}{3600}.
\]
This is impossible, so \(h>13/20\).

Next suppose \(h\ge17/25\). Both \(h+1/(4h)\) and \(h-k\) increase.
Since \(k(17/25)=\sqrt{94}/50<1/5\), (7) gives
\[
 X+h>\frac{59}{60}+\frac{25}{68}+\frac{17}{25}>\frac{203}{100},
\]
\[
 Y-k>\frac{17}{25}-\frac15-\frac1{60}>\frac{23}{50}.
\]
The second corner inequality in (8) therefore gives
\[
 q>(203/100)^2+(23/50)^2
   =\frac{1733}{400}=Q+\frac{103}{6400}.
\]
Thus \(h<17/25\), completing the first assertion of (5).

### 4.3. The center is nearly on its physical side axis

Let
\[
 p=aX+bY=-c_P\cdot u,\qquad \tau=-bX+aY=c_P\cdot v.
\]
Containment in the actual frame is
\[
 (p+1/2)^2+(|\tau|+1/2)^2\le Q. \tag{9}
\]
We prove \(p>3/2\), whence (9) gives \(|\tau|<1/16\).

By (7),
\[
 p>P(h):=\frac{29h}{30}+h^2+\frac14+
 k\left(1+\frac1{4h}-h\right).
\]
This function is strictly concave on \(13/20\le h\le17/25\).
For completeness put \(f=1+1/(4h)-h\). Direct differentiation gives
\[
 P''(h)=2-\frac{f}{2k^3}
       +\frac{2h+1/(2h)}{k}+\frac{k}{2h^3}.
\]
Throughout this interval
\[
 \frac{19}{100}<k<\frac7{25},\quad f>\frac23,\quad
 2h+\frac1{2h}<\frac{11}{5},\quad
 \frac{k}{2h^3}<\frac35.
\]
The negative term has magnitude greater than
\(15625/1029>15\), whereas the sum of the positive terms is less than
\[
 2+\frac{220}{19}+\frac35<15.
\]
Thus \(P''<0\).

The endpoint lower bounds are explicit:
\[
 P(13/20)>\frac{1561}{1200}+\frac{2101}{10400}
 =\frac{46889}{31200}>\frac32,
\]
\[
 P(17/25)>\frac{10273}{7500}+\frac{33901}{255000}
 =\frac{383183}{255000}>\frac32.
\]
They use respectively \(k>11/40\) and \(k>29/150\).
Concavity proves \(p>3/2\) everywhere. Since \(Q-4=81/256\),
(9) now gives
\[
 |\tau|<1/16. \tag{10}
\]

### 4.4. Verifying the common point

For \(Z=(-c_0,1/3)\), write
\[
 u\cdot Z=-w,\qquad
 w=\frac{79h}{60}+\frac{13k}{20}.
\]
The function \(w\) is concave. At the two interval endpoints the same
lower bounds on \(k\) give
\[
 w(13/20)>\frac{2483}{2400}>\frac{61}{60},\qquad
 w(17/25)>\frac{1021}{1000}>\frac{61}{60}.
\]
Consequently \(w>61/60\).
Also \(w\le|Z|<21/20\), while \(3/2<p<r_0\). Hence
\[
 0<p-w<\frac12.
\]

The other coordinate is
\[
 v\cdot Z=-\frac{13h}{20}+\frac{79k}{60}.
\]
Using \(13/20<h<17/25\) and \(19/100<k<7/25\) bounds it strictly
between \(-1151/6000\) and \(-323/6000\), hence between \(-1/5\) and zero.
Together with (10),
\[
 |v\cdot Z-\tau|<\frac15+\frac1{16}<\frac12.
\]
Both physical frame coordinates of \(Z-c_P\) have absolute value below
\(1/2\). Thus \(Z\) is strictly inside \(P\).

### 4.5. Localization of the opposite endpoint

The y bound in (7) and \(h>13/20\) give \(Y>19/30\).
The center-radius bound implies
\[
 X^2<r_0^2-(19/30)^2=\frac{6837}{3600}<(83/60)^2.
\]
Also \(g>25/68\). The weak-chain span gives
\[
 x_D>x_P+g+2+h_D
 >h_D+2+\frac{25}{68}-\frac{83}{60}
 =h_D+\frac{251}{255}
 >h_D+\frac{59}{60}.
\]
This implies \(h_D<8/15\).
The endpoint localization argument already supplied in
[ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md](ONE_EXCEPTION_HEIGHT_FOUR_CONTINUATION.md)
now applies directly to this coordinate inequality: with
\(k_D=\sqrt{1/2-h_D^2}\), one has \(k_D>23/50\) and
\(h_D+k_D>99/100\). An outward-quadrant vertex would give, if
\(|y_D|\ge1/5\),
\[
 q>(148/75)^2+(33/50)^2=\frac{97417}{22500}>Q.
\]
Thus \(|y_D|<1/5\), proving (6).

## 5. Closing the harder transverse ordering in the original full rank grid

Assume the original actual x- and y-orders both have height at most three,
and their nine rank pairs are all distinct, hence fill the three-by-three
grid. All pairs except one are coordinate-separated.

Suppose the exceptional pair occupies the left-column middle and top cells.
Name the cells
\[
 \begin{array}{ccc}
 P=(1,3)&T=(2,3)&G=(3,3)\\
 A=(1,2)&C=(2,2)&D=(3,2)\\
 L=(1,1)&M=(2,1)&R=(3,1).
 \end{array}
\]
These are rank labels, not asserted center coordinates.
Consider the harder transverse ordering
\[
 x_A-x_P\ge g_P+g_A. \tag{11}
\]
The opposite ordering was closed by the four-span argument in
[ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md](ONE_EXCEPTION_RANK_BOUNDARY_CONTINUATION.md).

Equal actual y-ranks force actual x-comparisons within each row.
Equal actual x-ranks force actual y-comparisons within each column,
apart from \(A,P\). Therefore
\[
 P<_xT<_xG,\quad A<_xC<_xD,\quad L<_xM<_xR,
\]
\[
 M<_yC<_yT,\quad R<_yD<_yG,\quad L<_yA,\quad L<_yP.
 \tag{12}
\]
In addition, P has an actual y-three-chain ending at it because its
actual y-rank is three.

### 5.1. The inner exceptional square lies below the top-middle square

The comparison \(T<_xA\) would give the actual x-four-chain \(T,A,C,D\),
contrary to the original height bound.

If \(A<_xT\), then (11) and \(T<_xG\) give the weak four-chain
\(P,A,T,G\). But G is also the upper endpoint of the actual y-three-chain
\(R,D,G\). Section 2 excludes this configuration.

Thus A and T have overlapping x-projections. They are not the exceptional
pair, so they are actually y-separated. Their ranks determine the direction:
\[
 A<_yT. \tag{13}
\]

### 5.2. The common point forces the inner square's bottom edge down

Section 4 applies to the weak chain \(P,A,C,D\), so
\(Z=(-59/60,1/3)\) is strictly inside P.

The point's x-coordinate lies strictly inside A's inscribed aligned square.
Indeed \(A<_xC<_xD\) gives
\[
 x_A<-h_A+b_0,\qquad
 x_A-g_A<b_0-(h_A+g_A)\le-c_0.
\]
On the other side, (11) and the center bound give
\[
 x_A+g_A>-r_0+g_P+2g_A
 \ge-r_0+\frac3{2\sqrt2}>-\frac{31}{60}>-c_0.
\]
The inequality \(3/(2\sqrt2)>1\) suffices for the displayed strict bound.

Also (13) gives
\[
 y_A-g_A<r_0-\frac12-(h_A+g_A)
 \le\frac1{60}<\frac13.
\]
If \(y_A+g_A>1/3\), Z would lie in the open inscribed square of A
and in the interior of P, contradicting physical nonoverlap.
Consequently
\[
 y_A+g_A\le\frac13,\qquad
 y_A-h_A\le-\frac23. \tag{14}
\]
By \(L<_yA\),
\[
 y_L+h_L\le-\frac23. \tag{15}
\]

### 5.3. The bottom chain forces the same square too far left

Section 4 also gives \(|y_D|<1/5\).
Since \(R<_yD\),
\[
 y_R+h_R\le y_D-h_D<-\frac3{10}.
\]
The first quadrant bound in Section 3 implies
\[
 x_R-h_R<\frac23.
\]
The actual bottom x-three-chain then gives
\[
 x_L+h_L\le x_R-h_R-2h_M
 <\frac23-1=-\frac13. \tag{16}
\]
Equations (15)-(16) place the whole square L below \(-2/3\) and to
the left of \(-1/3\). The second quadrant bound forces \(q\ge41/9>Q\),
a contradiction.

This proves that the harder transverse ordering (11) is impossible
throughout the closed-Q domain. Reflections and coordinate interchange
give the corresponding statements at the other edges.

## 6. Scope of the closure

This is a whole geometric branch, with all nine rank-grid squares retained.
It does not assume that the centers themselves form a Cartesian grid.
Every comparison used in (12)-(13) is actual; only (11) is an inscribed-pair
comparison.

The new endpoint, quadrant, and common-point lemmas are reusable independently
of the full-grid application. In particular, the common-point lemma is stated
for a weak four-chain whose outer exceptional square ends an actual
perpendicular three-chain.

The remaining duplicated/missing rank cases and the other full-nine endpoint
capacity cases require their own proved implications. No canonical root
count, new mandatory gate ID, unrestricted coverage theorem, or unrestricted
equality classification is asserted here.

