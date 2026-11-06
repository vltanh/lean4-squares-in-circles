# Complete (1,3,1) occupancy and the actual-cone four-plus-three theorem

**Status: CLOSED at the manuscript level.** This is the next fixed domain
after the complete (2,2,1) proof at commit
`7a0e4a8f5e666560dde802dab3bc3fd2a155375b`. It proves every (1,3,1)
central-height and side-order alternative in one manuscript. Section 9
then assembles the complete actual-and-cone four-chain / outsider-cone
three-chain theorem. The unrestricted nine-square theorem remains open:
the unrestricted extraction supplies cone links, not actual links.

The new arguments below are author-checked hand derivations. No independent
review or kernel verification of this continuation is claimed. No Lean
compilation, CI, numerical search, mathematical program, or archived
certificate replay was used. Existing cited hand theorems retain their
own validation boundaries.

Put
\[
 Q=1105/256,\quad r=\sqrt Q,\quad \rho=91/60,\quad
 l=29/60,\quad u=13/12,\quad G=15/31,\quad \alpha=1/60.
\]
For an original unit square V, write h_V for its horizontal and vertical
projection halfwidth and g_V=1/(4h_V) for the halfwidth of its actual
concentric aligned inset. Thus h_V>=1/2 and
 g_V>=1/(2sqrt(2)). All physical frames remain independent.

## 1. One fixed original-nine domain and its normalization

There are nine original unit squares with disjoint open interiors in a
centered disk of radius strictly less than r. Four specified originals
M0,M1,M2,M3 form an actual horizontal projection chain and their three
consecutive center differences are also in the positive horizontal cone.
The other five originals have count (left,central,right)=(1,3,1), using
x<=-l, -l<x<l, x>=l. Name the side originals S and T respectively.
There is a designated outsider horizontal cone three-chain L<P<R.
No actual projection separation is assumed on either selected outsider link.

Expand every center by one common factor greater than one and sufficiently
close to one, retaining every physical frame. The finitely many strict
corner margins and central-column margins permit an expansion that keeps
all corners inside Q and preserves this occupancy. Side-column membership
persists even at x=+/-l. Every physical separator becomes strict, and all
actual and homogeneous cone comparisons persist. The inward endpoint span
then satisfies
\[
 D=x_3-x_0-h_0-h_3>2.                                  \tag{1}
\]
We work in this closed-Q, closed-disjoint normalized domain. No expansion
to the Q-circle or invariance under a large expansion is assumed.

The actual-four localization gives
\[
\begin{gathered}
 |c_V|<\rho,\quad |x_V|<u\text{ for every outsider},\quad
 -31/60<x_1<-l,\quad l<x_2<31/60,\quad g_1,g_2>G,\\
 x_1+g_1>-\alpha,\quad x_2-g_2<\alpha,\quad
 x_2+g_2>59/60,\quad -x_1+g_1>59/60,\\
 |y_1|,|y_2|<139/120,\quad |y_2-y_1|<31/30.
\end{gathered}                                           \tag{2}
\]
The original outer endpoints satisfy every center and tilt guard of the
[five-square cap](FIVE_SQUARE_CAP.md). Thus it suffices to find three
distinct originals A,U,B, different from M0,M3, with
\[
 -u\le x_A\le0\le x_B\le u,\quad |x_U|\le l,\quad
 y_A,y_B\ge3/5,\quad y_U-h_U\ge1/10.                   \tag{3}
\]
That cap gives D<=2, contradicting (1). Its vertical reflection is also
available. An inner main is allowed as a shoulder if its actual guards hold.

### 1.1. The exact earlier hand inputs

The physical model, incircles, insets, supports, and separating axes are in
[FOUNDATION.md](FOUNDATION.md). The localization (2) and the following
center clearances are in the actual-four chapter and its retained sources:

* A central original in x<=0 has vertical center gap >59/60 from M1;
  in x>=0 it has gap >59/60 from M2. A side original has the corresponding
  own-half gap >97/100. See the
  [inner-clearance proof](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md).
* Any central original has vertical gap >23/50 from either inner main.
  The proof in [ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md),
  Section 2, uses only that original and the main's actual frame and
  localization; it has no two-upper-central or side-occupancy premise.
* Every central original is above both mains or below both. Indeed its
  horizontal residual from either inset is <1/2, so its incircle gives
  vertical gap >g_i. A between placement would have total gap
  >G+59/60>31/30, contrary to (2). Equality with a main height is excluded.
* The [adjacent-inset barrier](sources/ADJACENT_PROXY_BARRIER_HAND_PROOF.md)
  gives, for an upper central V,
  y_V-h_V>min(y1,y2)+869/1860; for a lower central it gives
  y_V+h_V<max(y1,y2)-869/1860.
* The [central-strip pair cap](sources/TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md)
  excludes two central originals both wholly below -9/20, or both
  wholly above 9/20. No original projection separation is required.
* [ACTUAL_FOUR_CENTRAL_BOUNDS.md](ACTUAL_FOUR_CENTRAL_BOUNDS.md) proves:
  y1<=-3/5 and y2<=-23/60 exclude a central below both, with horizontal
  reflection; a central below one inner main forces that main above -9/10;
  and, when a lower central is retained, at most one upper central has
  center height at most 3/5.
* The [nearby upper-central pair theorem](sources/UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md)
  gives the higher original whole floor >2807/24000>1/10 when their
  horizontal gap is at most 1/2.
* The column lemma in [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md), Section 2.1,
  gives horizontal gap >l for two originals whose centers are at least 3/5 high.
* The low-side extraction in [ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md),
  Appendix B, makes every upper central in the same closed horizontal half
  as a side original above its own main and below height 3/5 have whole
  floor >1/10. It includes both coordinate reflections.

Three further local theorems are used from the completed
[ACTUAL_FOUR_221.md](ACTUAL_FOUR_221.md), with all their guards checked below:
Appendix B's four-original low-right theorem, Appendix C's one-sided
main-height bound 17/50, Appendix D's low central cone-endpoint exclusion,
and Appendix E's low-floor/right-high exclusion. None assumes the present
(1,3,1) conclusion. Only the stated local theorem, not its (2,2,1) caller,
is imported in each use.

## 2. Common routing and elementary finite alternatives

Each original cone edge has horizontal gap at least the sum of its two
actual inset halfwidths, hence at least 1/sqrt(2). Therefore
\[
 |x_P|<u-1/\sqrt2<23/60,\qquad
 x_R-x_L\ge\sqrt2>2l.                                \tag{4}
\]
Thus P is central, and at least one selected endpoint is a side original.
Its horizontal gap from either main is <9/10. Using g_i>12/25, its
incircle gives vertical gap >(12+sqrt(46))/25>3/4 from either main.
Choose a common vertical reflection putting P above both mains.

Every selected side endpoint is above its own main. Otherwise its vertical
gap from P would exceed 3/4+97/100>22/15, whereas its cone horizontal
gap is <u+23/60=22/15. A selected central endpoint cannot be below
both mains either: its vertical gap from P would exceed 3/4+59/60,
whereas its horizontal gap is <2l. Thus all selected central endpoints
are upper. At least one of S,T is above its own main.

There are now precisely three possible upper-central counts: one, two,
or three. Sections 4, 6--7, and 5 respectively cover these whole counts.
No weak/actual bits of selected edges are fixed.

### 2.1. Low side centers, and at most one low upper side

For a side original above its own main, (2) and own-half clearance give
y>-113/600. If also y<3/5, then |y|<3/5. The corresponding endpoint
contains the fixed rectangle
\[
 [A,B]\times[-c,c],\qquad
 A=503/480,\quad B=937/480,\quad c=221/600,              \tag{5}
\]
or its reflection. Its disjoint incircle forces
\[
 |x|<A-\sqrt{1/4-(3/5-c)^2}<49/80.                    \tag{6}
\]
Indeed |x|<u<B. A center at or beyond A would have horizontal residual
zero and vertical residual <1/2, which is impossible. The final positive
root comparison has squared reserve 38839/5760000.

If both S,T were above their own mains and below 3/5, all five outsider
x-coordinates would lie in (-49/80,49/80). Their total span would be
<49/40<sqrt(2), contradicting (4). Thus, whenever both side originals
are upper relative to their own mains, at least one has height >=3/5.

### 2.2. Three upper centrals meet both horizontal halves

Every upper central has -7/40<y<rho. Three upper centrals cannot belong
to one closed horizontal half of the central strip: in height order their
two adjacent vertical gaps would each be at least sqrt(1-l^2), whereas
the total available height span is <203/120. The exact comparison is
\[
 1-l^2-(203/240)^2=587/11520>0.                         \tag{7}
\]
Thus three upper centrals include a strictly negative and a strictly
positive x-coordinate, and at most two belong to either closed half.
Three upper centrals also supply a good-floor original: after sorting
by x, one adjacent horizontal gap is at most l<1/2, so the nearby-pair
theorem applies. Here and below good means whole floor >1/10.

### 2.3. A selected central endpoint and opposite side orders

Suppose S is above M1 and T below M2. Then T cannot be selected. The
selected triple must have L=S and a central R. Its two inset gaps give
\[
 -23/60<x_P<-13/60,\quad 19/60<x_R<l,\quad
 -u<x_L<-11/12.                                      \tag{8}
\]
The lower T gives y2>-17/50 by ACTUAL_FOUR_221, Appendix C.
The selected L is above M1, so yL>-113/600. Its horizontal gap from
M0 is <3/5; their incircles force |yL-y0|>4/5. The lower alternative
would give yL<-27/40, a contradiction. Thus yL>27/40.

Put Z=-xL. Its incircle avoids the left version of (5), with horizontal
residual <A-11/12=21/160, so
\[
 y_L>c+\sqrt{1/4-(21/160)^2}>17/20.                    \tag{9}
\]
The last squared reserve is 4439/5760000.

If yP<=3/5, the unchanged originals M2,P,L meet every guard of
ACTUAL_FOUR_221, Appendix D: p=-xP is in (13/60,23/60), P is above
M2, y2>-17/50, Z is in (11/12,u), yL>17/20, and the genuine cone
edge gives yL-yP<=Z-p. That local theorem is a contradiction.
Hence yP>3/5. The high-central-endpoint theorem in
[ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md), Sections 1--4, now proves
\[
 y_R>3/5,\qquad y_P>y_L>17/20,\qquad y_P-h_P>1/10.
\]
The three originals L,P,R supply (3). This excludes the entire
opposite-side-order domain, regardless of the unselected central's
height. Horizontal reflection covers T above and S below.

## 3. A sharper selected-middle bound with two lower central originals

This section is used only in Section 4's one-upper/two-lower case.
It replaces the archived singleton-floor table in that exact caller.

### 3.1. The selected upper middle has a good whole floor

Suppose two distinct central originals V,W are below both mains.
The middle P obeys the sharper bound (4). Since
1/sqrt(2)>707/1000, its horizontal residual from either main inset is
\[
 d_i-g_i<\alpha+|x_P|<11/10-707/1000=393/1000.
\]
Its original incircle therefore gives
\[
 y_P-y_i>G+309/1000\quad(i=1,2),                      \tag{10}
\]
because 1/4-(393/1000)^2-(309/1000)^2=7/100000>0.
If a residual is negative, the bound only improves; the vertical gap
is positive by the chosen routing.

Suppose yP-hP<=1/10. Then yP<97/120, using hP<17/24. Consequently
\[
 \max(y1,y2)<97/120-G-309/1000.
\]
Apply the reflected adjacent-inset barrier to each of the same V,W:
\[
 y_V+h_V,\ y_W+h_W
 <97/120-G-309/1000-869/1860
 =-9/20-27/15500.                                    \tag{11}
\]
Both unchanged originals are central and wholly below -9/20. This
contradicts the central-strip pair cap. Hence P is good.

### 3.2. Two lower centrals force both main heights above -1/2

Suppose y1<=-1/2. The generic central/main clearance >23/50 puts
both lower centers below -24/25. Any such center with x<=0 also has
own-half clearance >59/60 and therefore y<-89/60. The center-radius
bound then gives |x|<sqrt(1/10)<1/3. A lower center with positive x
already has x<l. Thus both lower originals lie in the rectangle
\[
 -1/3<x<l,\qquad -\rho<y<-24/25.
\]
Its squared diameter is
\[
 (49/60)^2+(167/300)^2=43957/45000<1,                  \tag{12}
\]
contradicting their original incircles. Reflection proves
\[
                         y1,y2>-1/2.                 \tag{13}
\]

## 4. Exactly one upper central: complete closure

The sole upper central is P. Both selected endpoints must be the two
side originals S,T, and both are above their own mains by Section 2.
Section 3.1 makes P good. If both side heights are at least 3/5,
S,P,T supply (3).

Otherwise reflect horizontally so T has yT<3/5. Section 2.1 makes
S high and gives xT<49/80. The horizontal gap of T from M2 is
<31/240<g2. Its incircle then gives
\[
 y_T-y2\ge g2+1/2>61/62.
\]
Together with (13), this yields yT>15/31>119/310.
The originals M0,S,P,T now satisfy ACTUAL_FOUR_221, Appendix B's
four-original theorem: M0 has the stated left endpoint bounds and
inward distance >59/60; S is high, negative, and left of P; P has
whole floor >1/10; T has xT<49/80 and 119/310<yT<3/5; and the
actual cone edge P<T gives its cone and inset gap >=1/sqrt(2).
That local theorem is a contradiction. This closes every one-upper case.

## 5. Exactly three upper centrals: complete closure

Opposite side orders are already excluded by Section 2.3. Both sides
cannot be below their mains, since at least one selected endpoint is a
side original above its own main. Thus both S,T are above their mains.

If both are high, Section 2.2 supplies a good central U, and S,U,T
satisfy (3). Otherwise reflect horizontally so S is low. Then T is
high by Section 2.1. Every nonpositive upper central is good by low-side
extraction with S, so the column lemma allows at most one such original.
Section 2.2 ensures at least one strictly negative original. There are
therefore one negative good original A and two positive upper centrals.
The higher of the positive pair is good by the nearby-pair theorem.
Call it U. The distinct originals A,U,T satisfy (3). Every three-upper
configuration is excluded.

## 6. Exactly two upper centrals, both side originals high

Let V be the retained lower central. Opposite side orders are excluded
by Section 2.3, and both sides below are impossible by Section 2.
Thus both sides are above their mains. First assume yS,yT>=3/5.
The two-low-main consequence supplies at least one upper central F
with yF>3/5. The one-main theorem, applied to V below each main,
gives y1,y2>-9/10. Both upper central heights are therefore >1/12.

We recall the complete high-side bad-floor cut. A central original with
x>=1/5, center height >=3/5, and whole floor <=1/10 cannot coexist
with a high right-side original. For a direct check, its center height
is <97/120. If the side original is below it, their center gaps are
bounded by 53/60 and 5/24, with squared sum <1. If it is above it,
their squared distance is bounded by
\[
 (s-1/5)^2+(\sqrt{\rho^2-s^2}-3/5)^2,
 \qquad l\le s\le u.
\]
This is convex in s. Its endpoint bounds, using the positive comparisons
sqrt(rho^2-l^2)<36/25 and sqrt(rho^2-u^2)<17/16, are
\[
 (17/60)^2+(21/25)^2<1,\qquad
 (53/60)^2+(37/80)^2=57265/57600<1.
\]
All orders contradict the incircles. Reflection gives the left cut.

If both upper centrals were bad, the high one F would consequently have
|xF|<1/5. The other has |x|<l, and both heights belong to
(1/12,97/120). Their squared center distance would be less than
\[
 (41/60)^2+(29/40)^2=1-107/14400<1.
\]
Hence one upper central U is good. The originals S,U,T supply (3).
This closes the complete both-high alternative, including height 3/5.

## 7. Exactly two upper centrals, one low side

Reflect horizontally so S is above M1 with yS<3/5, while T is above
M2 with yT>=3/5. A lower central V is retained throughout.
Low-side extraction already makes every nonpositive upper central good.
Consider a positive upper central F=(X,Y), 0<X<l, and suppose
\[
                         Y-h_F\le1/10.                \tag{14}
\]
We will exclude this whole predicate.

### 7.1. Main-height consequences and the very-low helper

Write cS=(-s,z). From (6), s<49/80 and its horizontal gap from M1
is <31/240<g1. Thus
\[
 y1<z-61/62< -f_*,\qquad f_*:=119/310>23/60.
\]
The two-low-main theorem with the original V forces y2>-3/5.
Own-half clearance and (14) give
\[
                  23/60<Y<97/120.                    \tag{15}
\]

If z<f_*, then y1<-3/5, so the same two-low-main theorem now forces
y2>-23/60. Hence Y>3/5>223/372 and y2+g2>1/10.
Also -113/600<z<f_*<7/16. The local zero-side geometry in
ACTUAL_FOUR_FULL_SIDES, Section 3.1, gives
\[
 s<\zeta=2211/4000,\qquad s-g_S<J=23/150.
\]
It also gives the required helper top
\[
                         z+g_S>A_0=18911/59520.        \tag{16}
\]
Here is the local premise check, without a full-side assumption.
The gap from S to M1 is <5/48 because s<zeta<47/80. Its inset
margin is >15/31-5/48>3/8. The physical side-axis clearance consequently
is at least g1+hS-1/128: for t=bS/aS, the possible loss is bounded by
[t((1-t)/2-3/8)]_+<=1/128. The vertical order is S above M1;
the two upward component orders give this bound, and horizontal or
non-upward axes cannot separate. Adding gS and using hS+gS>=1,
y1>-139/120 and g1>15/31 proves (16).

All four guards of ACTUAL_FOUR_221, Appendix E, now hold with the
unchanged S,F,M2,T: the helper inner-edge and top bounds, F positive
central above M2 with Y>223/372 and bad floor, the M2 inset top >1/10,
and the high right-side original T. That hand theorem excludes (14).
This closes the entire z<f_* range.

### 7.2. The moderate helper forces X>7/20

Retain f_*<=z<3/5. The endpoint rectangle and S's incircle give
\[
 s\le K(z):=A-\sqrt{1/4-(z-c)^2},\qquad
 A=503/480,\quad c=221/600.                            \tag{17}
\]
Both z>c and s<A hold; (6) ensures the latter.
The positive-root comparisons give
\[
 K(f_*)<11/20,\qquad K(3/5)<243/400.                   \tag{18}
\]
For the first, f_*-c=289/18600<1/60 and
1/4-(239/480)^2-1/3600=415/230400>0.
For the second the exact squared reserve is 13615/5760000.

Suppose X<=7/20. For a fixed z, the upper squared center-distance bound
(K(z)+7/20)^2+(z-Y)^2 is maximized over the height range (15) at one
of its endpoints. For each fixed endpoint Y, expansion makes this a
convex function of z: its only nonlinear term is
-2(A+7/20)sqrt(1/4-(z-c)^2). Hence only z=f_* and z=3/5 need checking.
At the first, its value is less than
\[
 (9/10)^2+(17/40)^2=317/320<1,
\]
since 97/120-f_*<17/40. At the second it is less than
\[
 (383/400)^2+(13/60)^2
 <(24/25)^2+(11/50)^2=97/100<1.
\]
All possible vertical orders are included in these endpoint maxima.
The original incircles would overlap. Therefore
\[
                              X>7/20.                 \tag{19}
\]

### 7.3. A raised inset inside the same F

Keep F's one folded frame a>=b>=0, t=b/a, h=(a+b)/2, k=(a-b)/2.
Its own-half main clearance gives
\[
 Y-h>y2+G-r_F,\qquad
 r_F=\max\{0,t(k+\alpha-X)\}.                          \tag{20}
\]
To check physical coverage, F is left of M2 and above it. Its horizontal
residual from M2's inset is <alpha-X<1/2, excluding horizontal and
non-upward separators. For an upward F-owned separator, taking the
favorable horizontal sign weakens the inequality. The near-vertical
threshold is no larger than the other component order, because
(a-b)[1/2-(alpha-X)(a+b)]>=0. Thus the minimum of the vertical
threshold and this one side threshold gives exactly (20). The aligned
case has r_F=0. No physical vertical projection edge is assumed.

By (19), alpha-X<-1/3 and k<=(1-t)/2, so
\[
 r_F\le[t(1/6-t/2)]_+\le1/72.
\]
The actual inset of F therefore has right edge and top satisfying
\[
 X+g_F>7/10,\qquad
 Y+g_F>2/5+15/31-1/72=9709/11160>13/15.                \tag{21}
\]
We used y2>-3/5 and h_F+g_F>=1; the final reserve is 37/11160.

The original T is right of F because xT>=l>X. It is also above F.
Otherwise their center gaps would be <11/15 horizontally, by (19),
and <5/24 vertically, by (15) and yT>=3/5. Their squared sum is <1.
Thus T and the actual F inset satisfy every hypothesis of the raised-inset
lemma in Section 8. That lemma is a contradiction.

The entire moderate-helper complement of (14) is excluded. Every upper
central is consequently good, on both horizontal sides including zero.
Their heights exceed 3/5, so the column lemma places the two originals
on opposite strict horizontal sides. Take the negative one as A, the
positive one as U, and the original T as B. They satisfy (3).
This closes the complete one-low-side alternative.

## 8. The exact raised-inset obstruction, with no interval table

This lemma is used only at (21). It replaces the former raised-proxy
interval-certificate input with a complete physical argument.

Let C be an aligned square of positive halfwidth g, centered at (X0,Y0),
with
\[
 X0+g\ge a_0:=7/10,\qquad Y0+g\ge b_0:=13/15.
\]
Let F be any physical unit square in the closed Q-disk, with center (s,z)
satisfying l<=s<=u, s>=X0, and z>=Y0. Then C and F cannot have
disjoint open interiors. C need not itself be inside the disk.

### 8.1. Coordinate separators

A horizontal coordinate separator would require s>=a0+h>=6/5>u,
which is impossible. A vertical coordinate separator gives z>=b0+h.
Then z>s and top containment gives
\[
 h<(25/12-b0)/2=73/120.
\]
For k=sqrt(1/2-h^2), h+k is decreasing for h>=1/2 and
\[
 h+k>\frac{73+\sqrt{1871}}{120}>29/30.
\]
For either physical chirality, when z>=s>=0 an original outward corner
implies Q>=(s+h)^2+(z+k)^2. The corner offsets are (h,k) or (k,h),
and the latter has the larger norm in this quadrant. Hence
\[
 Q\ge(s+h)^2+(z+k)^2
 >(59/60)^2+(11/6)^2
 =Q+671/57600,
\]
a contradiction.

### 8.2. All possible unit-owned axes reduce to three closed ranges

Put D=s-X0>=0 and V=z-Y0>=0. For any actual F-owned separating
unit normal, replacing both components by their absolute values can only
increase its center projection. Let those absolute components be p,q,
with p,q>=0 and p^2+q^2=1. Its support on F is 1/2, so necessarily
\[
              p(s-a0)+q(z-b0)\ge1/2.                  \tag{22}
\]
The absolute-component replacement is used only as a necessary inequality.
We do not assert that (p,q) is a side axis of the original F.
Both physical chiralities are retained in the corner bound below.

For 4/15<=p<=3/4, the concave function a0 p+b0 sqrt(1-p^2)
has its minimum at an endpoint. At p=4/15 use q>24/25, giving
\[
 a0p+b0q>14/75+104/125=61/60+1/500.
\]
At p=3/4 use q>13/20, giving a still larger value than 61/60.
Equation (22) would imply p s+q z>rho, contrary to the center bound.
This excludes the whole middle range.

For p>=3/4, the unconstrained maximizer of p s+q z in the center
disk has horizontal coordinate p rho>=91/80>u. Its maximum with
s<=u is therefore at s=u. Consequently
\[
 p s+q z<p u+(17/16)q,
\]
using sqrt(rho^2-u^2)<17/16. Equation (22) would then require
\[
 1/2<p(23/60)+q(47/240)
 <\sqrt{(23/60)^2+(1/5)^2}<1/2,
\]
a contradiction. The final squared numerator comparison is 673<900.
This includes q=0 through the direct horizontal bound.

### 8.3. The complete near-vertical range 0<=p<=4/15

Here q>24/25 and q>=p. Equation (22) implies
\[
 z\ge z_0(s):=b0+\frac{1/2+p(a0-s)}q
 \ge13/15+179/450=569/450>u\ge s.
\]
Let h=(p+q)/2 and k=(q-p)/2. Regardless of the original signs of
its side axes, the same quadrant-corner comparison from Section 8.1 gives
\[
 Q\ge(s+h)^2+(z+k)^2\ge f(s):=(s+h)^2+(z_0(s)+k)^2.
\]
This lower bound therefore covers both original chiralities, not only a
fictitious axis with components (p,q).

For every s in [l,u],
\[
 0<z_0(s)+k\le13/15+(251/450)(25/24)+1/2<2,
 \qquad p/q\le5/18.
\]
Thus
\[
 f'(s)/2=s+h-(p/q)(z_0(s)+k)
 >59/60-5/9=77/180>0,
\]
and f(s)>=f(l). Since q>1/2 and 1-q=p^2/(1+q),
\[
 l+h\ge59/60+p/2-p^2/3.
\]
Also
\[
 z_0(l)+k=b0+\frac1{2q}+\frac q2
                    +p\left(\frac{13}{60q}-\frac12\right)
 \ge28/15-p/3.
\]
Both lower quantities are positive. Expanding their squares and dropping
nonnegative square terms gives
\[
 f(l)\ge641/144-(47/180)p-(59/90)p^2
 \ge641/144-16/135
 =9359/2160=Q+569/34560>Q.
\]
For the penultimate estimate use p<=4/15, 47/180<4/15, and
59/90<2/3. This excludes the entire near-vertical range, including p=0.

Every coordinate axis and every original unit-owned signed axis has been
covered. The separating-axis theorem now proves the raised-inset lemma.

## 9. Complete fixed coverage and the actual-cone four-plus-three corollary

The chosen selected middle is upper, so its central count is 1, 2, or 3.
At least one side original is above its own main. Opposite side orders
are completely excluded in Section 2.3. When both sides are above, at most
one is low, by Section 2.1. The resulting fixed cover is:

| Upper-central count | Remaining side orders/heights | Complete proof |
|---:|---|---|
| 1 | Both sides above; both high or exactly one low | Sections 3--4 |
| 2 | Opposite side orders | Section 2.3 |
| 2 | Both sides above and high | Section 6 |
| 2 | Both sides above, exactly one low | Sections 7--8 |
| 3 | Opposite side orders | Section 2.3 |
| 3 | Both sides above; both high or exactly one low | Section 5 |

Both sides below are impossible before this table. The boundary y=3/5
belongs to the high alternative, the boundary whole floor=1/10 is included
in every bad-floor contradiction or the cap, x=0 is included in closed
half-plane clearances, and the helper height f_* belongs to the moderate
range. The raised-inset proof covers every signed physical normal and all
three shared range endpoints. Horizontal and vertical reflections act on
all nine originals and their physical frames together.

Every row supplies a contradiction with the same original predicates.
Therefore the entire normalized (1,3,1) domain is empty. Section 1's small
expansion proves the stated strict-radius theorem without occupancy migration.

**Actual-cone four-plus-three corollary.** No nine-square packing below r
can have an actual-and-center-cone horizontal main four-chain together with
a disjoint outsider horizontal center-cone three-chain.

Indeed the strict-radius side-capacity theorem gives at most two outsiders
in each side. The five outsiders consequently have, up to horizontal
reflection, exactly the following six counts. A small common expansion can
preserve all strict central margins and make D>2, as above. Their complete
closures are:

| Count | Complete contradiction |
|---|---|
| (2,1,2) | [ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md) |
| (2,2,1) | [ACTUAL_FOUR_221.md](ACTUAL_FOUR_221.md) |
| (2,3,0) | [ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md) |
| (1,3,1) | The present manuscript |
| (1,4,0) | [ACTUAL_FOUR_140.md](ACTUAL_FOUR_140.md) |
| (0,5,0) | The selected cone triple has span >=sqrt(2), but all three centers would lie in a strip of width 2l<sqrt(2) |

These are six exhaustive counts, not infinitely many local cases and not a
percentage of the unrestricted proof. This corollary closes every selected
five-bit cone witness with all three main links actual, including every
possible status of the two short links. It does not close a cone four-chain
with a weak main link, nor prove that an unrestricted packing supplies an
actual four-chain. That remaining global implication is not assumed here.
