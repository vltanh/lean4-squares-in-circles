# The fixed (2,2,1) domain: assembly and the exact remaining predicate

**Target status: OPEN.** This chapter implements
[the active directive](ACTIVE_221_DIRECTIVE.md). It does not introduce a
new target or declare the (2,2,1) theorem complete. Sections 2–5 exclude
the full-side bottom and top patterns. The existing theorem excludes the
middle pattern when both central originals are on the same vertical side.
Section 7 states the remaining one-upper/one-lower predicate and proves
additional necessary conditions on that same predicate.

The new derivations below have been checked by their author, not by an
independent reviewer or a proof kernel. No Lean, CI, numerical search,
mathematical program, or archived certificate replay was used. The
unrestricted nine-square theorem is not a conclusion of this chapter.

Put
\[
 Q=1105/256,\quad r=\sqrt Q,\quad \rho=91/60,\quad
 l=29/60,\quad u=13/12,\quad g_*=15/31.
\]
For an original square write h for its coordinate halfwidth, g=1/(4h)
for the halfwidth of its actual contained aligned inset, and a>=b>=0
for its folded side components. Thus a²+b²=1, h=(a+b)/2, k=(a−b)/2.

## 1. Fixed domain, normalization, and the complete finite cover

Retain nine independently oriented original unit squares with pairwise
disjoint open interiors in a centered disk of radius R<r. Four specified
originals M0,M1,M2,M3 form an actual horizontal projection chain, and
all three consecutive center differences are in the positive horizontal
cone. Three distinct outsiders form a horizontal center-cone chain.
There are exactly two left outsiders, two central outsiders, and one
right outsider, in the columns x<=−l, −l<x<l, and x>=l.

A sufficiently small common expansion of all centers, keeping every
frame fixed, preserves this occupancy and keeps every corner strictly
inside the Q-disk. Indeed the two central centers have a positive
margin from the side boundaries, while expansion preserves membership
of each side column. Choose the expansion smaller than these finitely
many margins and the finitely many corner-containment margins permit.
Every original physical separator becomes strict, so all closed squares
become pairwise disjoint. Actual and cone comparisons persist. Their
inward endpoint span then satisfies
\[
 D=x_3-x_0-h_0-h_3>2.                                      \tag{1}
\]
This normalization does not expand to the Q-circle or assume that an
occupancy survives an arbitrarily large expansion. No outsider weak-edge
bit is fixed or needed in this chapter.

The following established hand inputs are used with their original frames:

* [Actual-four localization](ACTUAL_FOUR_CHAIN.md) and the retained
  [outsider-strip proof](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md):
  every outsider has |x|<u, every center has norm <rho,
  x1 in (−31/60,−l), x2 in (l,31/60), g1,g2>g_*,
  x1+g1>−1/60, x2−g2<1/60, x2+g2>59/60, and the endpoints
  satisfy the bands and tilt bounds of the five-square cap.
* The main cone comparisons give |y1|,|y2|<139/120 and
  |y2−y1|<31/30. The
  [physical inner clearances](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md)
  exceed 97/100 in the corresponding closed horizontal half-plane,
  and 59/60 for a central original in that half-plane.
* The [side markers](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_SIDE_CAPACITY_HAND_PROOF.md),
  the [middle-main height bound](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md),
  and the [extreme-main bound](sources/FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md),
  with its side-pair input supplied by [ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md),
  give the full left main's three possibilities:
  bottom y1<−3/5; middle |y1|<7/20; top y1>3/5.
* Every central original is above both inner mains or below both.
  Its horizontal residual from either main inset is <1/2, so its
  incircle gives a vertical gap >g_i; its own-half gap is >59/60.
  A between placement would require
  |y2−y1|>g_*+59/60>31/30. This proves the asserted routing,
  including exclusion of equality with either main height.
* The [two-low-main theorem](ACTUAL_FOUR_CENTRAL_BOUNDS.md) excludes a
  lower central original when y1<=−3/5 and y2<=−23/60.
* The [low-side extraction](ACTUAL_FOUR_CONE_TRIPLES.md), Appendix B,
  gives an upper central's whole floor >1/10 when it is in the same
  closed horizontal half-plane as a side outsider above its own main
  and of height <3/5. It includes either reflection.
* The [nearby upper-central pair theorem](sources/UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md)
  gives the higher original whole floor >2807/24000>1/10 when their
  horizontal gap is at most 1/2.
* The [five-square cap](FIVE_SQUARE_CAP.md) contradicts (1) whenever
  three distinct originals A,U,B, different from the outer endpoints,
  satisfy
  \[
    -u\le x_A\le0\le x_B\le u,\quad |x_U|\le l,\quad
    y_A,y_B\ge3/5,\quad y_U-h_U\ge1/10.                \tag{2}
  \]
  Original inner mains are permitted as shoulders if they meet these
  conditions. Its column lemma says that two centers of height >=3/5
  have horizontal gap >l.

The complete cover is the full-side main's three positions and the
number of upper central originals, 0, 1, or 2. This is a fixed nine-cell
cover, not a workload estimate. Vertical reflection exchanges bottom
and top and exchanges central counts 0 and 2. Sections 2–5 close all
bottom cells and therefore all top cells. Section 6 closes the two
same-side middle cells. The middle/one-upper/one-lower cell remains open.

## 2. Bottom full side: setup and the impossibility of two lower centrals

Suppose the left main is at the bottom. Write S,H for its lower and
higher left outsiders. The low-side geometry in
[ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md), Section 3, gives
\[
\begin{gathered}
 y_1<-3/5,\quad c_S=(-Z,y_S),\quad l\le Z<\zeta:=2211/4000,\\
 -113/600<y_S<7/16,\quad Z-g_S<J:=23/150,\\
 y_S+g_S>A_0:=18911/59520,\qquad y_H>367/600>3/5.
\end{gathered}                                               \tag{3}
\]
These facts concern the same original S and its actual inset.
Let T be the sole right-side outsider and let F,G be the central ones.

If a central original is below both mains, Section 4.1 of the same
full-sides chapter, applied only to M1 and that original, gives after
vertical reflection
\[
 1/3<X\le l,\qquad 3/5+g_*<Y<\rho.                     \tag{4}
\]
Its proof needs only y1<−3/5, not a second full side. Two lower central
originals would both belong to this rectangle. Its width is 3/20 and
its height is rho−3/5−g_*=161/372<1/2. Their center distance squared
would be less than (3/20)²+(1/2)²<1, contradicting their incircles.
Thus there is at least one upper central original.

## 3. Bottom full side with a right outsider below its main

Suppose y_T<y2. The one-sided main-height theorem gives y2>−7/20.
We first exclude any lower central original without assuming y2<7/20.
The main cone and y1<−3/5 give y2<13/30, hence
\[
 y_T<13/30-97/100=-161/300.
\]
Reflect vertically and write (X,Y) for a hypothetical lower central
and (s,z) for T. Equation (4) holds. Also l<=s<u and
z>f0:=161/300. The right endpoint contains
\[
 [A,B]\times[-c,c],\qquad
 A=503/480,\quad B=937/480,\quad c=221/600.
\]
The incircle of T therefore gives
\[
 z\ge L(s):=\begin{cases}
 f0,&l\le s\le s_0,\\
 c+\sqrt{1/4-(A-s)^2},&s_0\le s\le A,\\
 c+1/2,&A\le s\le u,
 \end{cases}\qquad
 s_0=A-\sqrt{1/4-(f0-c)^2}<7/12.                       \tag{5}
\]
The last positive-root comparison has squared reserve 33559/5760000.
Here z>f0>c and s<B, so the distance coordinates used in (5) are valid.

If z>=Y, their horizontal gap is <3/4 and their vertical gap is
<rho−3/5−g_*<1/2; their squared distance is <13/16<1.
If z<=Y, bound it by (s−X)²+(Y−L(s))². This function increases
on the two constant parts of L. On its curved part, expansion leaves
an affine function of s minus
2(Y−c)sqrt(1/4−(A−s)²), which is convex. Thus its maximum is at
s0 or u. At u its value is less than
\[
 (3/4)^2+(389/600)^2<(3/4)^2+(13/20)^2=197/200<1.
\]
At s0, if Y<=3/2, its value is less than
\[
 (1/4)^2+(289/300)^2=1-427/45000<1.                    \tag{6}
\]

For Y>=3/2 we need the correlated improvement X>2/5. Suppose X<=2/5.
Set C=3/5+g_*=168/155, d=161/372, v=Y−C. Against the actual
left-main inset, the adjusted positive horizontal and vertical gaps
are respectively <d and <v, where 0<v<=d and d−v=rho−Y.
Coordinate separation is impossible since both are <1/2. With the
original central frame a>=b, a²+b²=1, its largest possible adjusted
side-axis projection is less than
\[
 ad+bv\le2hv+d-v
 <2(133/64-Y)(Y-C)+\rho-Y=:W(Y),
\]
using top containment h+Y<=r<133/64. The quadratic W decreases on
[3/2,rho]: its derivative at 3/2 is −3353/4960 and decreases thereafter.
Its value there is 2963/5952=1/2−13/5952. Thus neither physical
side axis can separate, a contradiction. This proves X>2/5.
With this improvement, the value at s0 for Y>3/2 is less than
\[
 (11/60)^2+(49/50)^2=1-539/90000<1.                    \tag{7}
\]
All vertical orders give center distance <1. Therefore no lower central
exists in the present right-below case.

Both F,G are consequently upper. Section 8 of the full-sides chapter
now gives each whole floor >1/10: its two-proxy proof uses only the
same original S from (3), the correlated M2 inset bands, y2>−7/20,
and the tested central above M2. It uses no upper bound on y2 and no
second right outsider. The column lemma forces F,G to opposite strict
horizontal signs. The originals H,F_negative,F_positive satisfy (2).
This closes the entire right-below alternative.

## 4. Bottom full side with a low right outsider above its main

Suppose y2<y_T<3/5. Own-half clearance and the main cone bound give
y_T>−113/600, hence |y_T|<3/5. The endpoint rectangle and T's
incircle give
\[
 x_T<A-\sqrt{1/4-(3/5-c)^2}<49/80.                    \tag{8}
\]
To justify the horizontal order, x_T<u<B; if x_T>=A, its horizontal
residual would be zero and its vertical residual at most 3/5−c<1/2,
which is impossible. The squared reserve for the last bound in (8)
is 38839/5760000.

Since l<=x_T<49/80 and l<x2<31/60, their horizontal center gap is
<31/240<g2. T's incircle then gives y_T−y2>=g2+1/2>61/62. Thus
\[
 y2<3/5-61/62=-119/310<-23/60.
\]
Together with y1<−3/5, the two-low-main theorem excludes every lower
central. Hence F,G are both upper. Apply low-side extraction with S
to every nonpositive central, and with T to every nonnegative central.
Both have whole floors >1/10. The column lemma puts them on opposite
strict sides, and H,F_negative,F_positive supply (2). This closes
all of the right-above/low alternative, including zero central x-coordinates.

## 5. Bottom full side with a high right outsider above its main

Assume y_T>y2 and y_T>=3/5. H,T are already opposite high shoulders.
If both centrals are upper and one is nonpositive, low-side extraction
with S makes that one good. If both are positive, their horizontal gap
is <l<1/2 and the nearby-pair theorem makes the higher one good.
Either choice supplies the central U in (2).

The only remaining bottom pattern has one upper central F and one lower
central G. If x_F<=0, low-side extraction again closes it. Suppose x_F>0.
The two-low-main theorem, applied to the retained G, forces y2>−23/60.
Consequently
\[
 y_F>y2+59/60>3/5,\qquad y2+g2>1/10.                  \tag{9}
\]
We prove directly that y_F−h_F>1/10, using S,M2,T and this one F.
This is the only additional geometric assertion needed by the bottom
assembly; its complete separator argument follows.

### 5.1. Two helper separators retain one actual F frame

Suppose Y−h<=1/10, where c_F=(X,Y), 0<X<l, Y>3/5. Write its
one frame as a>=b>=0, h=(a+b)/2, k=(a−b)/2. Against M2's inset,
put D_R=x2−X>0, V_R=Y−y2>0, c_R=y2+g2−(Y−h)>0. Then
\[
 D_R-g2<1/60-X<1/2,\quad V_R-g2=h-c_R<h,\quad
 D_R+g2>1/2.
\]
Both coordinate separators fail. A side normal with nonpositive vertical
component has adjusted projection <1/2. An upward-right side normal
has adjusted projection at most bh<=1/2 or
ah−b(D_R+g2)<1/2, using ah=1/2+bk. Therefore the actual F-owned
separator is upward-left. An aligned F is already impossible; otherwise
t=b/a lies in (0,1] and the two possibilities give
\[
 X<1/60-k-tc_R\quad\hbox{or}\quad X<1/60+k-c_R/t.      \tag{10}
\]

For the left helper S, Y>3/5>7/16>y_S. Set
D_L=X+Z>0, V_L=Y−y_S>0 and c_L=A_0−(Y−h)>=c_0:=A_0−1/10.
The helper inequalities are
\[
 D_L-g_S<X+J,\qquad V_L-g_S<h-c_L.                    \tag{11}
\]
Vertical separation fails. Horizontal separation, if possible, implies
\[
 \mathcal H:\quad X>h-J.                              \tag{12}
\]
If it is impossible, any F-owned separator points upward-right. Here is
the full sign check. We have V_L+g_S>3/5−7/16+7/20=41/80>1/2.
A downward axis has adjusted projection at most ah−b/2<=1/2 or
bh−a/2<1/2. An upward-left axis has projection below bh<=1/2 or
1/2+b(k−D_L−g_S)−ac_L<1/2, since g_S>1/3 and c_L>1/6.
These exclude every other sign.

The two original F separators are now orthogonal. If the left axis
were (b,a) and the right (−a,b), summing their necessary inequalities
would give
\[
 Z-g_S+x2-g2>c_L/t+tc_R>=c_0>J+1/60=17/100,
\]
contrary to (3) and the correlated main band. Thus the oblique alternative
uses the actual axes (a,b),(−b,a) and gives
\[
 \mathcal O:\quad X>k+t(A_0-(Y-h))-J,\qquad
 aX+bY>1/2+bA_0-aJ.                                  \tag{13}
\]
In alternative H, the first right-axis choice in (10) would imply
h+k=a<J+1/60=17/100, also impossible. Hence H has these same axes.
Every helper/main separator has been included; no chirality is assumed.

### 5.2. The remaining right shoulder cannot avoid that same F

In O the summed proxy inequalities give tc_L+c_R/t<17/100, hence
t<(17/100)/c_0<4/5, since c_0>17/80. In H, X<l and (12) imply
h<l+J=191/300<h(4/5)=9/(2sqrt(41)), so again t<4/5.

Let g=7/20; the aligned square of halfwidth g centered at T is contained
in T. Write c_T=(s,z), D_T=s−X>=0 and delta=z−Y. We have
\[
 D_T<h+g.                                             \tag{14}
\]
For H, use D_T<u+J−h and 2h>=1>u+J−g=133/150.
For O, use D_T<u+J−k−tc_0 and
\[
 a\ge1-t/3,\quad c_0>3/14,\quad
 a+tc_0>1-5t/42>=19/21>133/150.
\]
The first inequality follows by positive squaring from
1−(1−t/3)²(1+t²)=t(6−10t+6t²−t³)/9>=0 on [0,4/5];
the cubic decreases there and ends at 166/125>0.

The center circle and s>=l give z<36/25, while Y>3/5. In the other
vertical order, the assumed bad floor and z>=3/5 give Y−z<=h−1/2.
Consequently
\[
 \delta<17/20,\qquad -\delta<5/24<g.                  \tag{15}
\]
Equations (14)–(15) exclude both coordinate separators of F and T's inset.

Because t<4/5, a>5/7 and a rho>u. Maximizing as+bz over the center
disk with s<=u therefore gives
\[
 as+bz<au+(17/16)b,
\]
using sqrt(rho²−u²)<17/16 (squared reserve 43/19200).
In O, a positive (a,b) separator from F to T's inset would require
\[
 a(133/150)+b(17/16-A_0-g)>1.
\]
This is impossible by Cauchy–Schwarz: the second coefficient is positive
and <2/5, and (133/150)²+(2/5)²=21289/22500<1.
In H, use aX+bY>a(1/2−J)+(3/5)b. The same separator would require
\[
 a(29/75)+b(9/80)>1/2,
\]
whereas (29/75)²+(9/80)²<(2/5)²+(1/8)²=281/1600<1/4.
The opposite sign of this axis has projection at most
b max(−delta,0)<5b/24, smaller than its required support.

For the other actual F axis (−b,a), if delta>=0 its positive projection
is at most delta<17/20<=1/2+g(a+b). Its negative projection is at
most bD_T<b(h+g)<=1/2+bg<1/2+g(a+b).
If delta<0, its positive projection is nonpositive and its negative
projection is less than b(h+g)+5a/24<1/2+g(a+b).
Thus both signs of both original F axes also fail. This contradicts
physical separation from the actual inset in T.

The assumed bad floor is impossible. Equation (9) and the unchanged
originals H,F,T therefore supply (2). This completes the high-right
case, and with Sections 2–4 proves every bottom pattern. Vertical
reflection proves every top pattern. No selected outsider cone edge
was needed inside this bottom/top assembly.

## 6. Middle full side with both centrals on one side

For a middle full side name its lower outsider S and upper outsider H.
Then y_S<y1<y_H and |y1|<7/20. When both central originals are above
both inner mains, the complete original-square theorem in
[ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md), Sections 1–8,
supplies (2), with every selected-triple position and every right-side
height alternative included. It contradicts (1).

When both central originals are below both mains, apply a common vertical
reflection and use exactly that theorem. The main and outsider cone
comparisons are preserved because they use absolute vertical differences;
the left main remains in the middle position. This closes that cell too.

## 7. The remaining middle/one-upper/one-lower predicate

Choose the common vertical reflection that puts the selected cone middle
above both inner mains. Call it P, and call the other central G. The
remaining original nine squares are exactly
\[
 M0,M1,M2,M3;\ S,H;\ P,G;\ T,
\]
with
\[
\begin{gathered}
 -u<x_S,x_H\le-l,\quad y_S<y1<y_H,\quad |y1|<7/20,\\
 |x_P|,|x_G|<l,\quad y_P>\max(y1,y2),\quad
 y_G<\min(y1,y2),\\
 l\le x_T<u,\quad y_T>y2,\qquad H<_cP<_cT.             \tag{16}
\end{gathered}
\]
Here all original corner and pair conditions, actual main links, main
cone comparisons and D>2 remain conjuncts.

For completeness the selected endpoints in (16) really are H,T. Every
selected cone edge has horizontal gap at least 1/sqrt(2)>7/10, so
|x_P|<23/60 and its vertical gap from either inner main exceeds 3/4.
A selected endpoint below its own main would have vertical gap from P
>3/4+97/100>22/15, while its cone horizontal gap is <u+23/60=22/15.
Hence selected endpoints are above their own mains. A central selected
endpoint would be above both mains by central routing, but G is below.
Thus both endpoints are side originals; the left one is H and the right
one is T. This proves the reduction without a weak-edge assumption.

### 7.1. A lower terminal forces y2>−3/5

The generic central clearance from either inner main exceeds 23/50;
its complete proof is in ACTUAL_FOUR_CONE_TRIPLES, Section 2, and uses
only the actual-four bands and that central's incircle. It applies to G.
If y2<=−3/5 then
\[
 y_G<y2-23/50<=-53/50,
 \qquad y_G+h_G<-53/50+3/4=-31/100<-1/10.
\]
Also y_S<y1−97/100<−31/50. After vertical reflection the originals
S,G,M2 satisfy every condition (2), with M2 as the right shoulder.
They are distinct and different from the outer endpoints. This is a
contradiction. Therefore
\[
 y2>-3/5,\qquad y_T>37/100.                            \tag{17}
\]

### 7.2. A low right shoulder cannot coexist with a bad P floor

Suppose y_T<=3/5. Equation (17), the endpoint rectangle, and the
incircle argument of (8) give x_T<49/80. The selected cone edge then
gives x_P<49/80−7/10=−7/80<0. Own-half clearance gives
\[
 y_P>y1+59/60>19/30>y_T.
\]
Suppose also y_P−h_P<=1/10. The high left original H has y_H>31/50.
The two-disk bad-floor cut proved in ACTUAL_FOUR_CONE_TRIPLES,
Section 3, applies to this one P and H: it uses no second upper
central and yields x_P>−1/5. Also y_P<97/120. Consequently
\[
 0<x_T-x_P<13/16,\qquad
 0<y_P-y_T<263/600.
\]
Their squared center distance is less than
\[
 (5/6)^2+(9/20)^2=3229/3600<1,
\]
contradicting their original incircles. Thus
\[
 y_T<=3/5\quad\Longrightarrow\quad y_P-h_P>1/10.       \tag{18}
\]
This does not by itself produce a high right shoulder.

### 7.3. Two explicit alternatives remain, not a closure claim

The upper five-square cap excludes y_T>=3/5 together with
 y_P−h_P>=1/10. Combining this with (18), every survivor has exactly
one of the following alternatives:
\[
\begin{array}{ll}
 \mathrm{I}:&y_T>3/5,\qquad y_P-h_P<1/10,\\
 \mathrm{II}:&37/100<y_T<3/5,\qquad y_P-h_P>1/10.
\end{array}                                                   \tag{19}
\]
In particular neither equality boundary in (19) is missing.

In I the adjacent-proxy barrier gives
 y_P−h_P>min(y1,y2)+869/1860. Since y1>−7/20, the bad floor
forces y2<−683/1860. In II, x_T<49/80 puts its horizontal center
inside M2's inset, so y_T−y2>61/62 and y2<−119/310.
Both alternatives therefore satisfy
\[
 -3/5<y2<-683/1860.                                  \tag{20}
\]
The reflected adjacent-proxy barrier, applied to the same G below both
mains, then gives
\[
 y_G+h_G<\max(y1,y2)-869/1860
          =y1-869/1860<-109/930<-1/10.                \tag{21}
\]
The equality in the maximum follows from y1>−7/20 and (20).

The currently missing implication is exclusion of the full original
predicate (16), together with all physical and main-chain conjuncts,
under alternatives I and II of (19). Equations (17), (20), and (21)
are necessary consequences available inside that same predicate; they
are not substitutes for excluding it. In I the right shoulder is high
but the central floor is insufficient for the upper cap. In II the
central floor is sufficient but the right shoulder is not high enough.
There is no established argument here that repairs either missing
hypothesis by changing original labels or direction.

## 8. Fixed coverage ledger

| Full left main position | Central count above both mains | Status and proof |
|---|---:|---|
| Bottom | 0 | Excluded by Section 2 |
| Bottom | 1 | Excluded by Sections 3–5 |
| Bottom | 2 | Excluded by Sections 3–5 |
| Middle | 0 | Excluded by reflected Section 6 |
| Middle | 1 | OPEN: the complete predicate is Section 7 |
| Middle | 2 | Excluded by Section 6 |
| Top | 0 | Excluded by reflection of the bottom/count-2 proof |
| Top | 1 | Excluded by reflection of the bottom/count-1 proof |
| Top | 2 | Excluded by reflection of the bottom/count-0 proof |

This ledger is exhaustive because central routing and the three full-side
main positions were proved before the split. It is not a percentage of
work completed. No remaining cell is represented by a claim about an
archived checker, an unprinted scalar table, or a changed domain.
The sole active target remains the complete (2,2,1) theorem, and it stays
OPEN until the middle/count-1 predicate is excluded.
