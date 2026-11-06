# Central squares and the heights of the inner mains

This chapter proves a complete two-low-main exclusion by hand, retaining
one original central square and its same physical frame against both
inner mains. Its strengthened threshold and both displayed corollary
cases have received independent mathematical reading.

Put
\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q,\qquad
 \rho=\frac{91}{60},\qquad l=\frac{29}{60},\qquad
 \alpha=\frac1{60},\qquad g_*=\frac{15}{31}.
\]

## 1. The exact theorem and the correlated inset data

Let four original physical unit squares in the centered closed Q-disk
form an actual horizontal projection chain M0,M1,M2,M3. If
\[
 y_1\le-\frac35,\qquad y_2\le-\frac{23}{60},
 \tag{1}
\]
there is no distinct original square F, interior-disjoint from both inner
mains and contained in that disk, with
\[
 |x_F|\le l,\qquad y_F<\min(y_1,y_2).
 \tag{2}
\]
The main chain need not be a center-cone chain for this theorem.
Horizontal and vertical reflections give the corresponding variants.

The physical facts used here are proved in [FOUNDATION.md](FOUNDATION.md).
The actual-four localization and its correlated main bands are in
[ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md) and the retained
[outsider-strip proof](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md).

For the proof reflect vertically. Write (X,Y) for F, (x_i,Z_i) for the
two reflected mains, and h for F's coordinate halfwidth. Let g_i=1/(4h_i)
be the actual aligned inset halfwidth of main i. The actual-four
localization gives
\[
 \begin{gathered}
 x_1<-l\le X\le l<x_2,\qquad
 g_1,g_2>g_*,\\
 x_1+g_1>-\alpha,\qquad x_2-g_2<\alpha,\qquad
 x_2+g_2>\frac{59}{60}.
 \end{gathered}
 \tag{3}
\]
These are correlated inequalities about the same main squares.
For example x1>h1-61/60 and h1+g1>=1 give x1+g1>−1/60;
the reflected argument gives x2−g2<1/60. Also x2>h2−1/60
gives x2+g2>59/60.

Set
\[
 B=\frac35+g_*=\frac{168}{155},\qquad
 C=\frac{23}{60}+g_*=\frac{1613}{1860}.
 \tag{4}
\]
Thus
\[
 Z_1+g_1>B,\quad Z_2+g_2>C,\quad
 B>\frac{13}{12},\quad C>\frac{13}{15},\quad
 B\ge C,\quad B+C<2.
 \tag{5}
\]
The elementary radius estimates used below are
\[
 r<\frac{133}{64},\qquad
 r<B+1=\frac{323}{155},\qquad |(X,Y)|<\rho.
 \tag{6}
\]
The first is the positive squared comparison 17689>17680.
The second follows already from 133/64<323/155.
Containment also gives Y+h<=r.

## 2. The left main forces one upward-right side axis of the actual F

The gaps from the left main inset to F are D_L=X−x1>0 and
V_L=Y−Z1>0. Equations (3)--(6) give
\[
 D_L-g_1<X+\alpha\le\frac12,\qquad
 V_L-g_1<Y-B\le r-h-B<1-h\le\frac12.
 \tag{7}
\]
Since h>=1/2, neither coordinate axis separates F from that inset.

For any F-owned unit side normal, F's support is exactly one half.
A normal with nonpositive vertical component has adjusted projection
at most |n_x|(D_L−g1)<1/2. A normal with nonpositive horizontal
component and positive vertical component has adjusted projection
at most n_y(V_L−g1)<1/2. Thus neither can separate.

The physical separating-axis theorem consequently supplies an actual
F side axis
\[
 n=(p,q),\qquad p,q>0,\qquad p^2+q^2=1.
 \tag{8}
\]
Its other upward side direction is m=(−q,p). These two vectors are
the axes of the one unchanged physical F. Put
\[
 U=n\cdot(X,Y),\qquad V=m\cdot(X,Y).
\]
The left separating inequality and (3)--(5) give
\[
 U>\frac12-p\alpha+qB.
 \tag{9}
\]
In particular U>0. We will retain this same n in every right-main case.

A useful immediate consequence is
\[
 p>\frac14.
 \tag{10}
\]
Indeed, if p<=1/4 then q>=sqrt(15)/4>24/25, and (9) gives
\[
 U>\frac12-\frac1{240}+\frac{24}{25}\frac{13}{12}
   =\frac{1843}{1200}
   =\rho+\frac{23}{1200},
\]
contrary to U<=|(X,Y)|<rho.

## 3. The complete right-main separating-axis list

The positive gaps are D_R=x2−X and V_R=Y−Z2. The same correlated
bands give
\[
 D_R-g_2<\alpha-X\le\frac12.
 \tag{11}
\]
Thus the horizontal coordinate axis cannot separate, and a side
normal with nonpositive vertical component cannot separate either:
its adjusted projection is at most |n_x|(D_R−g2)<1/2.

The remaining possibilities are precisely:

1. the vertical coordinate axis;
2. the actual F axis n=(p,q);
3. the other actual F axis m=(−q,p).

These include all touching cases. We exclude them in turn below.

## 4. The same F side cannot separate it from the right main

If n=(p,q) also separates from the right inset, then
\[
 U>\frac12+\frac{59}{60}p+Cq.
 \tag{12}
\]

First suppose p>=q. The actual adjusted projection from the right inset
in this direction is
\[
 -p(D_R+g_2)+q(V_R-g_2)
 <q(\rho-C)<\frac34\frac23=\frac12.
\]
Here q<=1/sqrt(2)<3/4 and rho−C=302/465<2/3.
This contradicts the separating inequality.

Now suppose p<=q. By (10), p>1/4. On the quarter-circle part
1/4<=p<=q, the sum p+q is at least (1+sqrt(15))/4>6/5.
For example p sqrt(1−p²) increases on [1/4,1/sqrt(2)], so the
minimum of (p+q)²=1+2pq is at p=1/4.
Since 59/60>C, (12) yields
\[
 U>\frac12+C(p+q)>
       \frac12+\frac{13}{15}\frac65
       =\frac{77}{50}
       =\rho+\frac7{300},
\]
again contradicting U<rho. This excludes the same-axis case completely.

## 5. The two different F axes force an impossible original corner

If the right separator is m=(−q,p), its inequality gives
\[
 V>\frac12-q\alpha+pC.
 \tag{13}
\]
Both U,V are positive. The original F corner (X,Y)+(n+m)/2 has
squared norm
\[
 (U+1/2)^2+(V+1/2)^2.
\]
Using (9),(13), its squared norm is strictly greater than
\[
 \begin{aligned}
 &(1-p\alpha+qB)^2+(1-q\alpha+pC)^2\\
 &=2+\alpha^2+q^2B^2+p^2C^2
       -2\alpha pq(B+C)+2p(C-\alpha)+2q(B-\alpha)\\
 &\ge (1-\alpha)^2+(1+C)^2-\alpha(B+C).
 \end{aligned}
 \tag{14}
\]
The final step uses B>=C>alpha, p+q>=1, and pq<=1/2.
By (5), the last expression is greater than
\[
 \left(\frac{59}{60}\right)^2+
 \left(\frac{28}{15}\right)^2-\frac1{30}
 =\frac{3181}{720}
 =Q+\frac{1171}{11520}>Q.
 \tag{15}
\]
This is an actual original corner, so it contradicts containment.

## 6. Vertical separation also forces an impossible original corner

The remaining case is vertical separation from the right inset:
\[
 Y\ge Z_2+g_2+h>C+h.
 \tag{16}
\]
Since h=(p+q)/2, containment implies
\[
 p+q<r-C<\frac{73}{60}.
 \tag{17}
\]
For the last inequality, C+73/60=B+1>r.

If p,q were both at least 1/4, then
p+q>73/60. Indeed their smallest sum on this quarter-circle arc
is (1+sqrt(15))/4, which exceeds 73/60 because
sqrt(15)>58/15. Thus one component is smaller than 1/4.
Equation (10) shows it must be q:
\[
 0<q<\frac14,\qquad p>\frac{\sqrt{15}}4>\frac{24}{25}.
 \tag{18}
\]

Let
\[
 u=U+\frac12,\quad v=V+\frac12,\quad
 u_0=1-p\alpha+qB,\quad H=C+p+q.
\]
Equation (9) gives u>u0, while (16) gives
\[
 qu+pv>H.
 \tag{19}
\]
Here v>0: in fact V=−qX+pY>−l/4+(24/25)(C+1/2)>0.
The original corner as in Section 5 obeys u²+v²<=Q, so u<=r.

For completeness, minimizing this corner norm under (19) needs no
unprinted optimization. Since H>p>24/25 and qr<133/256, one has
H−qu>0. Therefore
\[
 u^2+v^2>f(u):=u^2+\frac{(H-qu)^2}{p^2}.
\]
Also H<C+sqrt(2)<5/2, so qH<5/8, whereas
u0>=1−alpha=59/60. Hence
\[
 f'(u)=\frac{2(u-qH)}{p^2}>0\qquad(u\ge u_0).
\]
Consequently
\[
 u^2+v^2>f(u_0)
 =u_0^2+\left(1+\frac Cp+q\alpha-\frac{Bq^2}{p}\right)^2.
 \tag{20}
\]
Both lower quantities in the following comparison are positive:
\[
 u_0\ge1-\alpha+Bq,\qquad
 1+\frac Cp+q\alpha-\frac{Bq^2}{p}
 \ge1+C-\frac{25B}{24}q^2>0.
\]
For positivity, use B<2, q<1/4 and C>0.
Expanding the two squares and discarding their nonnegative square terms
now gives
\[
 \begin{aligned}
 f(u_0)
 &\ge(1-\alpha)^2+(1+C)^2\\
 &\quad+2Bq\left[(1-\alpha)-\frac{25}{24}(1+C)q\right].
 \end{aligned}
 \tag{21}
\]
The bracket is positive: C<1 and q<1/4 give
\[
 (1-\alpha)-\frac{25}{24}(1+C)q
 >\frac{59}{60}-\frac{25}{48}
 =\frac{37}{80}>0.
\]
Thus (20)--(21) imply
\[
 u^2+v^2>
 \left(\frac{59}{60}\right)^2+\left(\frac{28}{15}\right)^2
 =\frac{641}{144}
 =Q+\frac{311}{2304}>Q.
 \tag{22}
\]
This contradicts containment and excludes the final right separator.

## 7. Conclusion and exact scope

Sections 3--6 exhaust the physical separating-axis alternatives between
the same F and the right original main's actual inset, after the left
pair forced F's actual n axis. No frame was chosen independently for
the two pairs. Hence the reflected predicates are impossible, proving
(1)--(2), including equality in both main-height thresholds.

The proof uses only the actual-four localization, physical support and
inset facts, the original center-radius bound, and the displayed rational
comparisons. It replaces the formerly computational strengthened two-low-main
input. No interval certificate, mathematical program, numerical search,
Lean build or CI is a premise.

## 8. A useful consequence with a retained lower central original

Suppose additionally that the actual main chain is also a center-cone
chain, and an original central G lies below both mains. There is at most
one original upper central square whose center height is at most 3/5.

Indeed, if two such upper centrals A,B have opposite horizontal signs,
the [own-half central clearance](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md)
greater than 59/60 gives y1,y2<−23/60. The theorem
and its horizontal reflection, applied to the same lower G, force both
mains above −3/5. Hence
\[
 23/60<y_A,y_B\le3/5.
\]
Their horizontal center gap is at most 29/30 and their vertical gap
less than 13/60, giving squared distance less than 3533/3600<1.
This contradicts their disjoint half-unit disks.

If instead A,B lie in the same closed horizontal half-plane, the main
cone bound y_i>−139/120 and own-half central clearance give
−7/40<y_A,y_B<=3/5. Their horizontal gap is at most l, so their
squared center distance is less than
\[
 (29/60)^2+(31/40)^2
 =12013/14400<1.
\]
This covers all horizontal signs, including a center at zero.

## 9. One low main: the stronger one-sided height bound

The following independent hand argument strengthens the one-main input
without a finite interval table. Its axis exclusions, constrained corner
minimum, and rational margins have also received independent reading.

Let original unit squares in the closed Q-disk, Q=1105/256, contain an
actual horizontal projection four-chain. If a central original F, with
|x_F|<=29/60, lies below an inner main M_i and is physically
interior-disjoint from it, then y_i>−9/10. No main cone comparison and
no assumption on the other main's height is needed.

Reflect horizontally to use the left main, and vertically to suppose
its center is (x_1,Z), with Z>=9/10, while F has center (X,Y), Y>Z.
Put
\[
 l=\frac{29}{60},\quad \alpha=\frac1{60},\quad
 \rho=\frac{91}{60},\quad g_*=\frac{15}{31},\quad
 B=\frac9{10}+g_*=\frac{429}{310},\quad
 d=\rho-B=\frac{247}{1860}.
\]
The same original main's aligned inset has halfwidth g>g_* and satisfies
x_1+g>−alpha, with x_1<−l<=X<=l. Consequently, for the positive
center gaps D=X−x_1 and W=Y−Z,
\[
 D-g<X+\alpha\le\frac12,\qquad
 W-g<Y-B<d<\frac12.
 \tag{9.1}
\]
The center bound |(X,Y)|<rho is used here.

Neither coordinate axis separates F from the inset. A side normal
owned by F has support one half. A normal with nonpositive vertical
component has adjusted projection at most |n_x|(D−g)<1/2, and an
upward normal with nonpositive horizontal component has adjusted
projection at most n_y(W−g)<1/2. Thus an actual F side axis must be
\[
 n=(p,q),\qquad p,q>0,\qquad p^2+q^2=1.
\]
Its other upward side axis is m=(−q,p). The original separator gives
\[
 U:=pX+qY>\frac12-p\alpha+qB.
 \tag{9.2}
\]
In particular
\[
 \frac12<p(X+\alpha)+q(Y-B)<\frac p2+qd.
\]
Since p=sqrt(1−q²)<=1−q²/2, this forces
\[
 0<q<4d=\frac{247}{465}<\frac35,\qquad p>\frac45.
 \tag{9.3}
\]

Let V=−qX+pY. The original corner (X,Y)+(n+m)/2 has coordinates
U+1/2,V+1/2 in the frame n,m. Put
\[
 u=U+\frac12,\quad v=V+\frac12,\quad
 u_0=1-p\alpha+qB,\quad K=l+\frac{p-q}{2}.
\]
Containment gives u²+v²<=Q. Equations (9.2) and X<=l give
\[
 u>u_0,\qquad pu-qv\le K,\qquad
 v\ge\frac{pu-K}{q}.
 \tag{9.4}
\]
At u=u0 the last expression is
\[
 v_0=\frac{pu_0-K}{q}
     =\frac12+pB+q\left(\alpha-\frac1{2(1+p)}\right).
 \tag{9.5}
\]
This quantity is positive. In fact
\[
 v_0\ge\frac12+pB-\frac q2
   >\frac12+\frac45\frac{11}{8}-\frac3{10}
   =\frac{13}{10}>0,
\]
using B>11/8. It follows that the lower bound in (9.4) is positive
for every u>=u0, so it may be squared.

The function
\[
 f(u)=u^2+\frac{(pu-K)^2}{q^2}
\]
is increasing for u>=u0: its derivative is 2(u−pK)/q², whereas
K<l+1/2=1−alpha, pK<=max(K,0)<1−alpha and u0>1−alpha.
Thus the actual corner norm is greater than f(u0)=u0²+v0².

Use
\[
 u_0\ge1-\alpha+Bq,\qquad
 v_0\ge\frac12+Bp-\frac q2>0.
\]
Expanding these two lower squares, and writing
F0=(1−alpha)²+(B+1/2)², gives
\[
 \begin{aligned}
 f(u_0)
 &\ge F_0-B(1-p)
       +q\left[2(1-\alpha)B-\frac12-Bp\right]+\frac{q^2}{4}\\
 &\ge F_0-Bq^2+q\left[(1-2\alpha)B-\frac12\right]\\
 &>F_0+q\left[\left(1-2\alpha-\frac35\right)B-\frac12\right]\\
 &=F_0+\frac{23}{3100}q>F_0.
 \end{aligned}
 \tag{9.6}
\]
Here 1−p=q²/(1+p)<=q², p<=1, and q<3/5. The displayed
coefficient is exact:
(11/30)(429/310)−1/2=23/3100.

Finally
\[
 F_0>
 \left(\frac{59}{60}\right)^2+\left(\frac{15}{8}\right)^2
 =Q+\frac{9571}{57600}>Q.
 \tag{9.7}
\]
This contradicts containment of that original corner.

All original side owners and both chiralities were included before the
physical n axis was forced. The same original frame is used in (9.2),
(9.4), and the final corner. Equality at the main height −9/10 is included.
The proof uses only the correlated actual-four inset edge and center
bounds, and the displayed hand inequalities. No interval table or
mathematical computation is an input.
