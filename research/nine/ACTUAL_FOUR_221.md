# Complete (2,2,1) occupancy: one integrated hand manuscript

**Status: CLOSED.** This single manuscript proves the entire fixed domain
specified by [ACTIVE_221_DIRECTIVE.md](ACTIVE_221_DIRECTIVE.md), including
all full-side main positions, every central vertical count, and the
horizontal reflection (1,2,2). It completes the assembly introduced in
commit d9bd61a01acf5d7465dc3ea0de7c91a4b0c79849.
The appendices print every new supporting proof and its exact use.
The unrestricted nine-square theorem remains open.

The independent reviews recorded here concern the printed local proofs and
their stated callers. No Lean compilation, CI, numerical search, or archived
certificate replay was used.

## 1. Fixed original-nine theorem

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 l=\frac{29}{60},\quad u=\frac{13}{12},\quad
 \rho=\frac{91}{60},\quad \alpha=\frac1{60},\quad G=\frac{15}{31}.
\]
Retain nine original independently oriented physical unit squares with
pairwise disjoint open interiors in a centered disk of radius strictly below r.
Four specified originals M0,M1,M2,M3 form an actual horizontal projection
chain, and their consecutive center differences satisfy the positive
horizontal cone comparisons. Three distinct outsiders form a designated
horizontal center-cone three-chain. Neither selected outsider edge is
assumed projection-separated.

The five outsiders have count (L,C,R)=(2,2,1), with columns
\[
 x\le-l,\qquad -l<x<l,\qquad x\ge l .
\]
We prove that this entire domain is empty. Horizontal
reflection includes (1,2,2). Every original pair condition, corner bound,
frame, and touching alternative remains in force.

### 1.1. A small normalization preserves the stated occupancy

Choose one common factor s>1 sufficiently close to one, and replace every
center c by sc while keeping every physical frame unchanged. Because the
original corner bounds are strict and there are finitely many corners,
all new corners still lie strictly inside the Q-circle for s close enough
to one. Each existing original separating inequality becomes strict,
since its positive center projection is multiplied by s while its two
supports stay fixed.

All actual-chain and center-cone comparisons persist. Each central outsider
has |x|<l, so s can also be chosen close enough to keep both central
originals in that open strip. Each side original stays in its side column
under positive expansion, including one originally on x=±l. Thus the
original occupancy is preserved; expansion all the way to the Q-circle
is unnecessary.

The inward endpoint span becomes
\[
 D=x_3-x_0-h_0-h_3>2,
 \tag{1}
\]
because the unexpanded actual four-chain already had inward span at least
two. It is therefore enough to exclude the same nine-original domain in
the closed Q-disk with (1). We use that normalized domain from now on.

### 1.2. Existing physical inputs and the common terminal

The actual-four localization, correlated insets, outsider strip, main
height and cone bounds, and own-half center clearances are stated in
[ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md) and its retained hand sources.
The local side-pair, low-side, and central routing proofs are in
[ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md).
The one-main and two-low-main exclusions are in
[ACTUAL_FOUR_CENTRAL_BOUNDS.md](ACTUAL_FOUR_CENTRAL_BOUNDS.md).
Their independent physical and support facts are in
[FOUNDATION.md](FOUNDATION.md).

The completed [five-square cap](FIVE_SQUARE_CAP.md) contradicts (1)
whenever three distinct originals L,U,R, different from M0,M3, satisfy
\[
 -u\le x_L\le0\le x_R\le u,\qquad |x_U|\le l,\qquad
 y_L,y_R\ge\frac35,\qquad y_U-h_U\ge\frac1{10}.
 \tag{2}
\]
Every remaining endpoint hypothesis follows from the same actual main
four-chain. Its vertical reflection is the corresponding lower terminal.
No central or shoulder projection separation is required.

## 2. The full-side main is extreme

The two left outsiders have horizontal center gap less than u−l=3/5.
Their disjoint incircles therefore force an absolute vertical gap
greater than 4/5. Name them S,H in strictly increasing center-height
order. Their own-half clearances exclude equality with y1, so M1
is below both, between them, or above both.

If M1 is below both, Appendix A proves the complete domain impossible.
It covers all right-side vertical orders and every central
upper/lower count, retaining the original lower central when needed.
Its stronger mixed-lower argument and every local floor input are printed.
It does not require the selected outsider cone three-chain.

Vertical reflection gives the case where M1 is above both. Hence only
\[
                         y_S<y_1<y_H                    \tag{3}
\]
remains. The entire orientation cover for this reduction is unchanged.

## 3. The middle-main routing and the already complete upper case

Appendix C proves the strengthened one-sided height theorem and gives,
under (3),
\[
 |y_1|<\frac{17}{50},\qquad
 y_H>\frac{63}{100},\qquad y_S<-\frac{63}{100}.
 \tag{4}
\]

Every central original is above both inner mains or below both; the
actual-and-cone central-routing proof includes all weak faces.
For the designated outsider cone triple L<P<R, the two original inset
gaps imply
\[
 |x_P|<\frac{23}{60}<l.
\]
The incircle/main-inset estimate then gives
|yP−yi|>3/4 for both inner mains. Since their vertical difference is less
than 31/30, P is above both or below both. Reflect vertically, if needed,
so P is above both; the middle position (3) persists.

If both central outsiders are now upper, the complete theorem in
[ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md) applies,
using the weaker consequence |y1|<7/20 of (4). It extracts (2) with
every selected-endpoint alternative retained. That proof uses both
unchanged upper central originals and includes the complete low-side
and coupled-cone floor lemmas. This closes the entire same-side central
count, including its reflected form.

Thus retain P upper and the other central original V below both mains.
A selected side endpoint cannot be below its own main: its vertical gap
from P would exceed 3/4+97/100=43/25, while its cone horizontal gap is
less than 22/15. The lower central V cannot be a selected endpoint:
its vertical gap from P exceeds 3/4+59/60=26/15, while their horizontal
gap is less than 2l=29/30. Consequently the designated original triple
is exactly
\[
                           H<P<R,\qquad y_R>y_2.        \tag{5}
\]
This is a direct routing argument for the upper/lower central variant;
it does not assume the two-upper hypothesis of the previous caller.

## 4. The remaining right-side height alternatives

If yR<3/5, Appendix B, Section 6, closes the complete branch.
It retains V to obtain either the reflected cap S,V,M2, or the positive
right height needed by its all-real-slope local theorem.

Hence retain
\[
                              y_R\ge\frac35 .           \tag{6}
\]
If P has whole floor f=yP−hP at least 1/10, (4)--(6) supply (2).
The remaining complete high-right predicate therefore has
\[
                              f<\frac1{10}.             \tag{7}
\]
The local bad-floor proofs may use the weaker f<=1/10, including its
equality boundary.

The adjacent-inset whole-square barrier and (4), applied to the same P,
force
\[
 y_2<-\frac{683}{1860}<y_1.
 \tag{8}
\]
Applied after vertical reflection to the same V, it also gives
\[
 y_V+h_V<y_1-\frac{869}{1860}
          <-\frac{1183}{9300}<-\frac1{10}.
 \tag{9}
\]
If y2<=−3/5, the three originals S,V,M2 supply the reflected cap,
using (4), (9), and M2 as the positive lower shoulder. Thus the
remaining main-height range is
\[
                    -\frac35<y_2<-\frac{683}{1860}<y_1.
 \tag{10}
\]

## 5. The negative or zero selected central: exact final scalar reduction

Suppose xP=−p<=0. Appendix F, Section 6.1, retains all the original
constraints and proves
\[
 0\le p<\frac15,\qquad
 \frac{193}{300}<Y:=y_P<\frac{97}{120}.
\]
Its complete separating-axis argument forces the actual P-owned
upward-right normal n=(b,a) against M1, with a>=b>0, a²+b²=1,
t=b/a, h=(a+b)/2, and k=(a−b)/2. The same physical P frame is retained
throughout. Its separating inequality gives
\[
                  y_1<f-G+t(k-p+\alpha).                \tag{11}
\]

Appendix F, Section 6.2, proves y1<−1/4, yS<−61/50, and xV>0.
Against M2's actual aligned inset, all horizontal and non-upward
separators fail. The exhaustive remaining possibilities are its vertical
coordinate axis or one of the two upward P-owned axes n=(b,a) and
m=(−a,b). Appendix F, Section 5, excludes both P-owned choices,
using the same S,V and the complete unary main-height theorem.
Thus the only remaining right-inset separator is vertical, giving
\[
                            y_2<f-G.                    \tag{12}
\]

Set d=sqrt(1+t²), a=1/d, lambda=29/27, d0=61/60, and
\[
                         \delta=2f+t(k-p+\alpha).
\]
The sharpened unary theorem in Appendix F, Sections 1--4, is
X+2Z<239/200. Its two applications to the retained lower originals,
together with their original disjoint incircles, prove in Section 6.3 that
\[
                 \delta>\frac{10907}{43400}>\frac14.    \tag{13}
\]

Appendix F, Sections 6.4--6.5, then uses both actual upper separators,
their complete real slope ranges, the unchanged P support, and the
original right-center radius bound. Exact elimination produces a
scalar 0<=z<1/t with
\[
 \delta<F(t,z)
 =2\lambda-a-d+\alpha t+t d_0\sqrt{1+z^2}
       -t\lambda z-\frac{(d-1)(2-tz)}{t+z}.              \tag{14}
\]
A nonpositive actual right slope is handled by a justified scalar z=0,
without asserting a replacement geometric separator. Positive slopes
at or beyond 1/t are excluded directly by the physical support bound.

Appendix I proves F(t,z)<1/4 on both complete compact rectangles
0<t<=3/4 and 3/4<=t<=1, with 0<=z<=3/4. Appendix F,
Section 7, proves F_z<0 for z>=3/4, so every remaining scalar
slope is covered. Equations (13)--(14) are now contradictory.
This closes the negative-or-zero-central alternative with every
original geometric constraint retained.

## 6. The positive selected central is completely excluded

Suppose xP>0 in the remaining high-right, bad-floor branch. Appendix G,
Sections 1--3, proves
\[
                    0<x_P<\frac15,\qquad y_P>\frac35 .
\]
Its small-positive-center argument keeps the correlated position and
physical support of the same actual M1; its larger-center argument applies
the reflected local theorem of Appendix D to the unchanged right shoulder.
Every endpoint of the position and height split is included.

Appendix G, Section 4, then forces one of the two actual upward-right
P-owned normals (a,b) or (b,a) against the M1 inset. All coordinate,
non-upward, opposite-horizontal, and aligned alternatives have already
been excluded. No owner for the separate P/R pair is imposed.

For the normal (a,b), Appendix G, Sections 5--10, proves that the
original right shoulder's center is less than one half from the same
physical P. Its complete profile and rounded-corner argument includes
the enlarged region's wedge faces, both vertical edges, and every
curved-boundary endpoint.

For the normal (b,a), Appendix H retains the genuine P/R separator in
every possible direction. The same-frame support breaks, two outer
envelopes, and the original right-center bound contradict every real
slope. Its two tilt ranges and both corner-height alternatives exhaust
the physical domain, including the a=b endpoint.

Thus every positive-P configuration in this fixed target is impossible.
Both appendices received independent complete mathematical review.

## 7. Exhaustive coverage and the complete theorem

The following finite cover concerns only the fixed target of Section 1.
An entry is closed only where a complete printed proof or an already
complete hand input supplies all hypotheses of a contradiction.

| Full-side main | Central/routing alternative | Status and proof |
| --- | --- | --- |
| Bottom or top | Every central count and right-side order | Closed, Appendix A and reflection |
| Middle | Both centrals on the same vertical side | Closed, Section 3 and the existing two-upper chapter |
| Middle, one central on each side | Selected upper triple, right height below 3/5 | Closed, Appendix B |
| Middle, one central on each side | Right height at least 3/5, central whole floor at least 1/10 | Closed by the five-square cap |
| Same high-right branch, bad floor | Right main at or below −3/5 | Closed by the reflected cap S,V,M2 |
| Same high-right branch, bad floor, xP<=0 | Either P-owned right-main separator | Closed, Section 5 and Appendix F |
| Same high-right branch, bad floor, xP<=0 | Vertical right-main inset separator | Closed, Appendices F and I |
| Same high-right branch, bad floor, xP>0 | Both possible original left-main separator directions | Closed, Appendices G and H |

Every row is closed. The three full-side main positions are exhaustive,
central routing includes every upper/lower count, and common reflections
account for the opposite vertical placement and the (1,2,2) count.
The low/high right-height split includes yR=3/5; the good/bad whole-floor
split includes f=1/10; xP=0 belongs to the nonpositive branch; and the
actual-frame analysis includes aligned squares and a=b. The final scalar
proof covers t=3/4, t=1, z=0, z=3/4, all larger admissible slopes,
and arbitrarily small positive t. An aligned P was excluded before
division by t.

All nine originals, all 36 pair conditions, every corner bound, the
actual and cone main comparisons, and the designated outsider cone triple
remain conjuncts throughout. Every local reduction uses the unchanged
original frames or actual contained insets. A local contradiction may
use fewer of the retained constraints, but no relaxed configuration is
used to infer a new property of an original square.

The normalized domain with D>2 is therefore empty. The small expansion
of Section 1.1 proves that the original strict-radius domain is empty
as well, without occupancy migration. This proves the entire fixed
(2,2,1) theorem and its horizontal reflection (1,2,2).

The complete hand lemmas below are parts of this manuscript. Their
section numbers, equation labels, and local variables are internal to
each appendix or expressly marked part unless another chapter is named.
The statement proved here has the explicit main-cone and outsider-cone
hypotheses of Section 1. No unrestricted nine-square lower bound or
global equality classification follows from this conditional closure.


<a id="appendix-a"></a>

## Appendix A. Extreme full-side main: every original alternative

5 November 2026. Complete hand proof, independently reviewed.
No mathematical program, interval table, certificate replay, Lean build,
or CI is used. All nine original physical squares and their independent
frames remain in the domain.

Put

\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad l=\frac{29}{60},\quad
 u=\frac{13}{12},\quad g_*=\frac{15}{31},\quad
 \zeta=\frac{2211}{4000},\quad J=\frac{23}{150},\quad
 A_0=\frac{18911}{59520}.
\]

For each physical unit V let h_V be its common coordinate support
halfwidth, and let g_V=1/(4h_V) be the halfwidth of its actual contained
aligned square. The physical support, inset, and center-radius facts are
proved in [FOUNDATION.md](FOUNDATION.md); the actual-four localization is
in [ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md).

### 1. Exact whole-domain theorem and active hand inputs

Retain nine original unit squares with pairwise disjoint open interiors
in the centered closed Q-disk. Four originals M_0,M_1,M_2,M_3 form
an actual horizontal projection chain, and their consecutive centers
also satisfy the positive-horizontal cone comparisons. Suppose

\[
             D=x_3-x_0-h_0-h_3>2.
\tag{1}
\]

The other five originals have normalized column counts (L,C,R)=(2,2,1),
using x<=-l, |x|<l, x>=l. Name the left outsiders S,H in increasing
center-height order, the central outsiders F,G, and the sole right
outsider R. Suppose the left inner main is below both left outsiders:

\[
                         y_1<y_S<y_H.
\tag{2}
\]

These complete hypotheses are impossible. No selected outsider cone
triple, actual outsider projection edge, or separator owner is assumed.
Vertical reflection covers a left main above both left outsiders.
Horizontal reflection covers the corresponding full-right count (1,2,2).

The active hand inputs, in their exact local domains, are:

* Actual-four localization, correlated main insets, center norm below
  rho, outsider strip |x|<u, and own-half center clearances greater
  than 97/100 (or 59/60 for a central outsider).
* The full-side extreme-main bound and zero-side geometry in
  [ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md), Sections 1--3.
  These give
  \[
  \begin{gathered}
  y_1<-\frac35,\qquad
  l\le -x_S<\zeta,\qquad -\frac{113}{600}<y_S<\frac7{16},\\
  -x_S-g_S<J,\qquad y_S+g_S>A_0,\qquad
  y_H>\frac{367}{600}>\frac35.
  \end{gathered}
  \tag{3}
  \]
* The [one-sided side/main-height theorem](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md):
  a right outsider below M_2
  implies y_2>-7/20. The stronger -17/50 version is available but
  is not needed here.
* The original lower-central localization in ACTUAL_FOUR_FULL_SIDES,
  Section 4.1, and the original central upper/lower routing in its
  Section 5. Section 2 below prints the stronger mixed-lower caller
  needed here; no archived extension is an unprinted dependency.
* The low-side same-half whole-floor theorem in
  [ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md), Appendix B.
* The two-inset, same-original-frame floor argument in
  ACTUAL_FOUR_FULL_SIDES, Sections 8.1--8.4. Its local use is
  verified explicitly in Section 4 below.
* The two-low-main theorem in
  [ACTUAL_FOUR_CENTRAL_BOUNDS.md](ACTUAL_FOUR_CENTRAL_BOUNDS.md), Section 1:
  y_1<=-3/5 and y_2<=-23/60 exclude an original central below both.
* The nearby upper-central pair theorem in
  [UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md](sources/UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md):
  an upper pair with horizontal gap at most 1/2 has a higher member
  whose whole floor exceeds 2807/24000.
* The original low-floor/right-high exclusion in
  [LOW_FLOOR_RIGHT_CENTRAL_AND_HIGH_RIGHT_SHOULDER_EXCLUSION.md](#appendix-e).
  Its exact four predicates are checked in Section 6.2.
* The upper-column separation and completed five-square terminal in
  [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md). In this chapter a cap triple
  means three distinct
  originals L,U,V, different from M_0,M_3, satisfying
  \[
  -u\le x_L\le0\le x_V\le u,\qquad |x_U|\le l,\qquad
  y_L,y_V\ge\frac35,\qquad y_U-h_U\ge\frac1{10}.
  \tag{4}
  \]
  The main endpoints supply every remaining terminal hypothesis;
  its conclusion D<=2 contradicts (1).

Every listed input already has a complete hand proof. No table from the
archived bottom-main assembly is invoked.

### 2. A lower central is impossible when the sole right outsider is lower

We first prove the following local strengthening of the mixed-lower
theorem, under the same actual-and-cone main chain:

\[
 y_1<-\frac35,\qquad l\le x_R<u,\qquad y_R<y_2
 \quad\Longrightarrow\quad
 \text{no central original V has }y_V<y_1.
\tag{5}
\]

There is no additional upper or lower bound assumed on y_2.

Suppose such V exists and reflect vertically. Write (X,Y) for its
center, (x_1,Z) for M_1, and (s,t) for R. The local proof in
ACTUAL_FOUR_FULL_SIDES, Section 4.1, uses only y_1<-3/5 and
this V's original disjointness from M_1. It gives

\[
 \frac13<X\le l,\qquad
 C:=\frac35+g_*=\frac{168}{155}<Y<\rho.
\tag{6}
\]

The full original center-radius constraint improves its height bound:

\[
 Y^2<\rho^2-X^2
       <\rho^2-\frac19=\frac{2627}{1200}
       =\frac94-\frac{73}{1200},
 \qquad Y<\frac32.
\tag{7}
\]

This simple coupled estimate removes the extra high-Y subcase present
in the old archived extension.

The main cone comparison gives y_2<y_1+31/30<13/30. The original
right outsider's own-half clearance then gives, in the reflected frame,

\[
 l\le s<u,\qquad t>\frac{97}{100}-\frac{13}{30}
                       =\frac{161}{300}=:f_0.
\tag{8}
\]

The original right endpoint contains the fixed aligned rectangle

\[
 [A,B]\times[-c,c],\qquad
 A=\frac{503}{480},\quad B=\frac{937}{480},\quad
 c=\frac{221}{600}.
\tag{9}
\]

Since s<u<B and t>f_0>c, R's original radius-half disk and this
rectangle imply

\[
 \max(A-s,0)^2+(t-c)^2\ge\frac14.
\tag{10}
\]

Set

\[
 s_0=A-\sqrt{\frac14-(f_0-c)^2}.
\]

Then l<s_0<A<u, and

\[
 s_0<\frac7{12},\qquad
 \frac14-(f_0-c)^2-(A-7/12)^2
          =\frac{33559}{5760000}>0.
\tag{11}
\]

For the first comparison l<s_0, note A-l=271/480>1/2 while
the displayed square root is at most 1/2. Thus every endpoint
of the following profile is in the stated interval. Equations
(8)--(10) give t>=L(s), where

\[
 L(s)=
 \begin{cases}
 f_0,&l\le s\le s_0,\\
 c+\sqrt{1/4-(A-s)^2},&s_0\le s\le A,\\
 c+1/2,&A\le s\le u.
 \end{cases}
\tag{12}
\]

If t>=Y, the original centers' horizontal gap is below 3/4 and
their vertical gap is below rho-C=161/372<1/2. Their squared
distance is therefore below 13/16<1, contradicting their two
original radius-half disks.

If t<=Y, their squared distance is at most

\[
 f(s)=(s-X)^2+(Y-L(s))^2.
\]

Here X<=l<=s. On the first and last profile intervals f increases
with s. On the middle interval its exact expansion is

\[
 \begin{aligned}
 f(s)={}&2(A-X)s+X^2-A^2+(Y-c)^2+\frac14\\
       &-2(Y-c)\sqrt{\frac14-(A-s)^2}.
 \end{aligned}
\]

It is convex, since Y>c and the radical is concave. Its maximum
over the full strip is consequently attained at s_0 or u. At s_0,
use (6)--(7), (11), and Y<3/2:

\[
 f(s_0)<
 \left(\frac14\right)^2+\left(\frac{289}{300}\right)^2
   =1-\frac{427}{45000}<1.
\tag{13}
\]

At u, the weaker height Y<rho already suffices:

\[
 f(u)<
 \left(\frac34\right)^2+\left(\frac{389}{600}\right)^2
   =1-\frac{6179}{360000}<1.
\tag{14}
\]

Every original vertical order contradicts the disjoint half-unit disks.
This proves (5), including all original frames and all boundary contacts.

### 3. There is at most one lower central outsider

Every central outsider is above both inner mains or below both, by
the actual-and-cone central routing. If both F,G were below both,
apply the local bounds (6) to each after vertical reflection. Their
horizontal gap would be less than l-1/3=3/20 and their vertical
gap less than rho-C=161/372<1/2. Their squared center distance would
therefore be less than

\[
                 \left(\frac3{20}\right)^2+
                 \left(\frac12\right)^2=\frac{109}{400}<1.
\tag{15}
\]

Their original incircles would overlap. Thus the two central outsiders
are either both upper or exactly one upper and one lower. Both unchanged
originals are used in this exclusion.

### 4. The sole right outsider is below M_2

Suppose y_R<y_2. The one-sided main-height theorem gives

\[
                         y_2>-\frac7{20}.
\tag{16}
\]

Section 2 excludes every central below y_1. Central routing therefore
places both F,G above both mains.

For each upper central V separately, apply the same-frame floor
argument in ACTUAL_FOUR_FULL_SIDES, Sections 8.1--8.4, to the
unchanged original left helper S and the unchanged inset of M_2.
Its complete local predicates are supplied as follows:

\[
 \begin{gathered}
 l\le Z=-x_S<\zeta,\quad |y_S|<7/16,\quad
 Z-g_S<J,\quad y_S+g_S>A_0,\\
 x_2-g_2<1/60,\quad x_2+g_2>59/60,\quad
 y_2+g_2>-\frac7{20}+\frac{15}{31}=\frac{83}{620},\\
 |x_V|<l,\qquad y_V>y_2.
 \end{gathered}
\tag{17}
\]

There is no upper-bound use of y_2 and no use of a second right
outsider in that local proof. Specifically, assuming y_V-h_V<=1/10,
its two positive top margins are

\[
 c_L=A_0-\frac1{10}=\frac{12959}{59520},\qquad
 c_R=\frac{83}{620}-\frac1{10}=\frac{21}{620}.
\]

The proof first forces the upward-left V side from M_2, deduces
V above S, and forces the other upward-right V side from S. Both
orders of its same original orthogonal frame would require an inset
gap greater than 2 sqrt(c_L c_R), whereas the actual correlated
gap is below J+1/60=17/100. The exact strict comparison is

\[
                4c_Lc_R-(17/100)^2
                    =\frac{45993}{76880000}>0.
\tag{18}
\]

All original separating-axis exclusions are printed in the cited
Sections 8.2--8.3 and need precisely (17). Thus both F and G have
whole floors greater than 1/10.

Their centers are consequently above 3/5. Upper-column separation
gives horizontal center gap greater than l, so two centers within
(-l,l) must have opposite strict signs. Call them C_- and C_+.
The three distinct originals H,C_-,C_+ satisfy the cap (4), contradicting
(1). This closes the complete right-below branch.

### 5. The right outsider is above M_2 but has height below three fifths

Suppose y_R>y_2 and y_R<3/5. The low-side endpoint estimates give

\[
                              x_R<\frac{49}{80}.
\tag{19}
\]

For completeness, if y_R<7/16, the local zero-side theorem in
ACTUAL_FOUR_FULL_SIDES Section 3.2 gives x_R<zeta<49/80; it
applies because R is above its own main, and the main cone lower
bound gives y_R>-113/600. If 7/16<=y_R<3/5, the endpoint
rectangle/incircle argument in ACTUAL_FOUR_CONE_TRIPLES Appendix B.2
gives (19) directly, without using any central square.

Now l<=x_R and l<x_2<31/60 give
|x_R-x_2|<31/240<g_2. The original incircle of R and actual
inset of M_2 imply

\[
 y_R-y_2\ge g_2+\frac12>\frac{61}{62},\qquad
 y_2<-\frac{119}{310}<-\frac{23}{60}.
\tag{20}
\]

Together with y_1<-3/5, the hand two-low-main theorem excludes a
central below both. Thus both F,G are upper.

For either one with x<=0, apply the reflected low-side floor theorem
to the original S, whose height is below 7/16<3/5. For either
one with x>=0, apply that theorem directly to the original R.
The zero/sign boundary is included in both local contracts. Hence
both originals have whole floors greater than 1/10.

As in Section 4, upper-column separation puts them on opposite
strict horizontal sides. The original triple H,C_-,C_+ gives
(4) and contradicts (1). This closes the complete low-right branch.

### 6. The right outsider is above M_2 and at least three fifths high

The remaining case has y_R>y_2 and y_R>=3/5. Equations (3)
already supply the high negative shoulder H, while R is the
high positive shoulder. It suffices to supply one upper central
original whose whole floor exceeds 1/10.

#### 6.1. Both central outsiders are upper

If either has nonpositive x-coordinate, the reflected low-side
floor theorem applied to S gives the required whole floor.
Otherwise both F,G are strictly positive and central, so their
horizontal gap is less than l<1/2. The complete upper-central
pair theorem gives the higher unchanged original a whole floor
greater than

\[
                         \frac{2807}{24000}>\frac1{10}.
\]

Use it as U in the original triple H,U,R. Equal center heights
were already impossible for the two original radius-half disks
within a horizontal gap below one. This closes every vertical
order and horizontal-sign choice in the two-upper branch.

#### 6.2. Exactly one central outsider is upper

Write F for the upper original and G for the lower one. If x_F<=0,
the low-side floor theorem with S again supplies the cap H,F,R.
Suppose x_F>0.

The retained lower original G and y_1<-3/5 make the two-low-main
theorem force

\[
                    y_2>-\frac{23}{60}.
\tag{21}
\]

The upper original F is on M_2's horizontal half, so its physical
own-half clearance gives

\[
 y_F>y_2+\frac{59}{60}>\frac35>\frac{223}{372},\qquad
 y_2+g_2>-\frac{23}{60}+\frac{15}{31}
        =\frac{187}{1860}
        =\frac1{10}+\frac1{1860}.
\tag{22}
\]

If the whole floor of F were at most 1/10, all four original
predicates of the active low-floor/right-high exclusion would hold:

1. The unchanged S supplies Z-g_S<J, y_S<7/16 and
   y_S+g_S>A_0 by (3).
2. The unchanged F has 0<x_F<l, lies above M_2, has
   y_F>223/372 by (22), and has the contrary whole-floor bound.
3. The unchanged M_2 inset has top y_2+g_2>1/10 by (22).
4. The unchanged R has l<=x_R<u and y_R>=3/5.

That complete physical separating-axis theorem excludes these
predicates. Therefore y_F-h_F>1/10, and H,F,R satisfy (4).
The cap contradicts (1).

Section 3 excluded the only other central vertical count. The entire
high-right alternative is therefore closed.

### 7. Complete coverage, normalization, and reflected cases

The right original has either y_R<y_2 or y_R>y_2; equality is
excluded by its physical own-half center clearance. Its upper
alternative splits at y_R=3/5, with that equality assigned to
Section 6. Sections 4--6 cover these complete alternatives. Section 3
leaves exactly the two central vertical counts used in Section 6.
Every horizontal sign-zero face, all original frames, separator owners,
physical touching conditions, and shared thresholds are retained.

Thus no normalized original-nine configuration satisfying (1)--(2)
exists. The strict-radius application uses the common small center
expansion proved in the main manuscript, Section 1.1. It preserves the
original (2,2,1) count and the center-height order (2), retains every
physical frame, keeps all corners strictly inside the Q-circle, and
gives D>2. The normalized theorem just proved therefore applies.
No expansion to the circle or occupancy migration is needed.

Vertical reflection treats a full-side main above both outsiders.
Horizontal reflection exchanges the left and right columns and reverses
the original main list, treating (1,2,2). These are common isometries
of all nine originals and their frames. The proof does not assume or
use a selected outsider short chain.

This is a whole-domain extreme-main occupancy theorem. It does not
assert closure of the full-side-middle case or the unrestricted
nine-square theorem.

<a id="appendix-b"></a>

## Appendix B. Low selected side and the lower-extra low-right caller

5 November 2026. Complete hand proof, independently reviewed.
The argument below uses no mathematical program, numerical search,
interval certificate, Lean build, or CI. Every support, corner, inset,
and separating inequality belongs to the original physical square named
in it.

Put

\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad u=\frac{13}{12},\quad
 A=46,\quad B=\frac{27}{2},\quad T=\frac{211}{4},
 \quad \lambda=\frac{29}{27},\quad
 \beta=\frac{451}{810}.
\]

The physical support of a unit square V in vector w is denoted by
H_V(w). Its common horizontal and vertical projection halfwidth is
h_V. Thus H_V(w)>=|w|/2 and 1/2<=h_V<=1/sqrt(2). Every original
center in the Q-disk has norm strictly less than rho, and r<133/64.
These physical facts are proved in [FOUNDATION.md](FOUNDATION.md).

### 1. A four-original local theorem, including its closed guards

Retain four distinct original unit squares E,H,P,R with pairwise
disjoint open interiors in the centered closed Q-disk. Suppose E has
the standard left endpoint bounds

\[
 -\frac{91}{60}\le x_E\le-\frac{89}{60},\qquad
 |y_E|\le\frac18,\qquad h_E\le\frac8{15},\qquad
 a:=-x_E-h_E>\frac{59}{60}.
 \tag{1}
\]

The other three originals satisfy

\[
 \begin{gathered}
 -u\le x_H\le0,\qquad y_H\ge\frac35,\qquad x_H<x_P,\\
 y_P-h_P\ge\frac1{10},\\
 x_R\le\frac{49}{80},\qquad
 \frac{119}{310}\le y_R<\frac35,\qquad
 x_R-x_P\ge |y_R-y_P|,\\
 x_R-x_P\ge\frac1{\sqrt2}.
 \end{gathered}
 \tag{2}
\]

These hypotheses are impossible. In particular the last two conditions
hold when P<R is an original positive-horizontal cone comparison: the
two actual aligned insets force its horizontal gap to be at least
g_P+g_R>=1/sqrt(2).

The theorem keeps the closed boundaries y_R=119/310,
x_R=49/80, and y_P-h_P=1/10. No main square or unlisted physical
contact is assumed in this local statement. A main four-chain can supply
(1), and a selected cone triple H<P<R supplies the required order.

### 2. The original H/P separator and the exact outer consequence

Set

\[
 p=-x_P,\qquad Y=y_P.
\]

The last two horizontal bounds in (2) give

\[
 p\ge\frac1{\sqrt2}-\frac{49}{80}
   >\frac7{10}-\frac{49}{80}=\frac7{80}>0.
 \tag{3}
\]

Since Y>=h_P+1/10>=3/5, both H and P have center heights at
least 3/5 and below rho. Their vertical center gap has magnitude less
than rho-3/5=11/12<1. Every directed physical unit separator from
P to H therefore has strictly negative horizontal component: a
nonnegative component, together with x_H<x_P, would give directed
center projection less than one, whereas the two original support
halfwidths sum to at least one.

Choose such a genuine separator and divide by the absolute value of
its horizontal component. It has the form

\[
 m=(-1,z),\qquad z\in\mathbb R.
 \tag{4}
\]

Write

\[
 \ell(z)=\frac{29}{2}z+
       \frac32\min(0,\max(-1,z)),\qquad
 J(z)=H_P((-1,z))+zY-\frac{\ell(z)}B.
 \tag{5}
\]

The reflected outer-envelope theorem from
[FIVE_SQUARE_CAP_OUTER.md](FIVE_SQUARE_CAP_OUTER.md),
applied to the unchanged originals E,H, gives

\[
 A a+B[-x_H+z y_H-H_H((-1,z))]\le T+\ell(z).
\]

The same original H/P separator gives

\[
 -x_H+z y_H-H_H((-1,z))
 \ge -x_P+zY+H_P((-1,z)).
\]

Combining these with a>59/60 proves the strict necessary inequality

\[
 \boxed{\quad p+J(z)<\frac TB-\frac AB\frac{59}{60}
                  =\frac{451}{810}=\beta.\quad}
 \tag{6}
\]

Every owner of the H/P separator is included. We will show that (6)
fails for every real slope z.

### 3. A two-vector support minimum for every original frame

For t>=0 define

\[
 M(t)=\sqrt{1+t^2},\qquad
 K(t)=\frac{1+t+2t^2}{2\sqrt{1+t^2}}.
 \tag{7}
\]

For every physical unit square V and either horizontal sign,

\[
 H_V((\pm1,t))+t h_V\ge K(t).
 \tag{8}
\]

The same statement holds with the sign of t reflected. To prove it,
let v=(1,t) and w=(0,t). Twice the left side is the sum of the
absolute projections of these two vectors onto the two original side
axes of V. Between successive zeros of those projections, the sum is
a positive function c cos(theta)+d sin(theta). Its second derivative
is its negative, so its minimum on that angular interval is at an
endpoint. The complete minimum over frames is consequently attained
when a side axis is parallel to v or w; this also includes the
degenerate case t=0 by continuity.

Alignment with w gives 1/2+t. Alignment with v gives K(t).
The latter is no larger, since both sides in the comparison are
positive and

\[
 (1+2t)^2(1+t^2)-(1+t+2t^2)^2=2t\ge0.
\]

This proves (8). All orientation choices have been minimized together;
no frame of V has been replaced independently in another constraint.

We need two elementary scalar consequences, both proved here.

#### 3.1. A uniform positive-slope lower bound

For every t>=0,

\[
 K(t)>\frac25+\frac{49}{50}t.
 \tag{9}
\]

Both sides are positive. After clearing the positive denominator and
squaring, (9) is equivalent to positivity of

\[
 F(t)=99t^4+540t^3+324t^2-710t+225.
\]

On t>=0,

\[
 F''(t)=1188t^2+3240t+648\ge648,
 \quad F(1/2)=\frac{395}{16},
 \quad F'(1/2)=\frac{137}{2}.
\]

Taylor's quadratic lower bound, followed by completing the square,
therefore gives

\[
 F(t)\ge\frac{395}{16}+\frac{137}{2}(t-1/2)
                   +324(t-1/2)^2
 \ge\frac{109211}{5184}>0.
 \tag{10}
\]

This proves (9) on the entire nonnegative half-line.

#### 3.2. The negative-slope range beyond one

For every t>=1,

\[
 K(t)>t+\frac25.
 \tag{11}
\]

Again both sides are positive. Twenty-five times their squared
numerator difference is

\[
 \begin{aligned}
 20t^3+9t^2-30t+9
 &=8+48(t-1)+69(t-1)^2+20(t-1)^3\\
 &>0.
 \end{aligned}
\]

More explicitly the difference being multiplied by 25 is
(1+t+2t^2)^2-4(1+t^2)(t+2/5)^2. This proves (11).

### 4. Every nonpositive slope contradicts the outer consequence

First let z=-t with 0<=t<=1. The cone condition and y_R<3/5
give the strict upper height bound

\[
 Y\le y_R+x_R-x_P<\frac{97}{80}+p.
 \tag{12}
\]

Here ell(-t)/B=-(32/27)t. Using the incircle support bound,
(3), and 1-t>=0, we obtain

\[
 \begin{aligned}
 p+J(-t)
 &\ge(1-t)p+\frac12\sqrt{1+t^2}-\frac{59}{2160}t\\
 &\ge\frac7{80}+\frac12\sqrt{1+t^2}-\frac{31}{270}t\\
 &\ge\frac7{80}+\sqrt{\frac14-\left(\frac3{25}\right)^2}
  >\frac7{80}+\frac{12}{25}=\frac{227}{400}>\beta.
 \end{aligned}
 \tag{13}
\]

The elementary inequality used in the third line is
a sqrt(1+t^2)-b t>=sqrt(a^2-b^2) for a>=b>=0; it follows either
by Cauchy--Schwarz in its hyperbolic form or by squaring after moving
b t to the other side. The numerical comparisons are
31/270<3/25 and sqrt(589)/50>12/25.

Next suppose 1<=t<=7. The uppermost support of P obeys Y+h_P<=r,
and ell(-t)/B=-(29/27)t-1/9. Hence (8) and (11) give

\[
 \begin{aligned}
 J(-t)
 &\ge H_P((-1,-t))+t h_P-(r-\lambda)t+\frac19\\
 &\ge K(t)-(r-\lambda)t+\frac19\\
 &>\frac25+\frac19-\frac7{1728}t\\
 &\ge\frac25+\frac19-\frac{49}{1728}
   =\frac{12}{25}+\frac{119}{43200}.
 \end{aligned}
 \tag{14}
\]

We used r<133/64 and
133/64-29/27=1+7/1728. Thus p+J(-t)>227/400>beta
throughout this closed interval.

Finally, for t>=7 the original center and incircle support bounds give

\[
 J(-t)>\frac t2-t(\rho-\lambda)+\frac19
       =\frac{31}{540}t+\frac19
       \ge\frac{277}{540}>\frac{12}{25}.
 \tag{15}
\]

Together with (3), this gives the same contradiction to (6). The
overlapping closed ranges include both breakpoints t=1 and t=7.

### 5. Positive slopes: a horizontal bound forces a higher original P

Let z>=0. Since ell(z)/B=lambda z and P has whole floor at
least one tenth, (8)--(9) give

\[
 \begin{aligned}
 J(z)
 &\ge H_P((-1,z))+z h_P-\frac{263}{270}z\\
 &\ge K(z)-\frac{263}{270}z>\frac25,
 \end{aligned}
 \tag{16}
\]

because 49/50>263/270. If (6) held, it would force

\[
 p<\beta-\frac25=\frac{127}{810}.
 \tag{17}
\]

Return now to the same original R. Its center lies to the right of P,
and (17) gives

\[
 0<x_R-x_P=x_R+p
     <\frac{49}{80}+\frac{127}{810}<\frac45.
 \tag{18}
\]

Their original radius-half disks are interior-disjoint, so their
center distance is at least one. Moreover P is above R, since
Y>=3/5>y_R. It follows that

\[
 Y-y_R>\frac35,\qquad
 Y>\frac{119}{310}+\frac35=\frac{61}{62}.
 \tag{19}
\]

The incircle support bound now improves (16), for the same slope z,
to

\[
 \begin{aligned}
 J(z)&\ge\frac12\sqrt{1+z^2}-\frac{151}{1674}z\\
 &\ge\sqrt{\frac14-\left(\frac1{10}\right)^2}
   >\frac{12}{25}.
 \end{aligned}
 \tag{20}
\]

The strict final comparison also covers z=0. We used
29/27-61/62=151/1674<1/10 and
1/4-1/100=6/25>144/625. Combining (3) and (20) gives

\[
 p+J(z)>\frac7{80}+\frac{12}{25}
         =\frac{227}{400}
         =\beta+\frac{347}{32400}>\beta,
 \tag{21}
\]

contrary to (6). Every real slope has now been excluded, proving
the local theorem of Section 1.

### 6. Complete lower-extra, low-right (2,2,1) caller

Retain all nine originals of an actual-and-cone main four-chain in the
closed Q-disk. Use the full-left-middle (2,2,1) geometry: S,H are
the two left-side outsiders, with y_S<y_1<y_H; P is one central
outsider above both inner mains; V is the other central outsider below
both; R is the sole right-side outsider. Let P be the middle of the
designated outsider cone triple, and suppose y_R<3/5. As usual D>=2
denotes the inward span of the two original outer mains.

The selected triple is necessarily H<P<R. Here is the full routing
check for this upper/lower central variant. The two cone gaps and
|x|<u put |x_P|<23/60 and each endpoint beyond its corresponding
coordinate +/-19/60. The main-inset incircle calculation in
[ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md), Appendix A,
gives y_P-y_i>3/4 for each
inner main. A selected side endpoint below its main would then differ
vertically from P by more than 3/4+97/100=43/25, whereas its
cone horizontal gap is below 22/15. A selected central endpoint V
below both mains would differ vertically from P by more than
3/4+59/60=26/15, whereas its horizontal gap is below 2l=29/30.
Thus every selected endpoint is above its own main and V cannot be
one of them. The selected left endpoint is H and the selected right
endpoint is R. This proof uses the same original V and does not
import the two-upper assumption of the earlier caller.

The conclusion is a complete five-square-cap alternative: the original
lower triple S,V,M_2 satisfies the vertically reflected cap. Every
configuration in this domain not supplying that triple is contradictory.
It follows that D<=2, strictly at a strict subcritical radius. Thus
this complete branch is impossible when D>2, or when the radius is
strictly below r and D>=2.

Only already hand-proved inputs from
[ACTUAL_FOUR_CONE_TRIPLES.md](ACTUAL_FOUR_CONE_TRIPLES.md),
[ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md), the
[adjacent-proxy barrier](sources/ADJACENT_PROXY_BARRIER_HAND_PROOF.md),
and the [five-square cap](FIVE_SQUARE_CAP.md) are used in the following
verification.

#### 6.1. A low right original localizes the right main

The full-side middle-height theorem gives |y_1|<7/20. Own-half
side clearances consequently give

\[
 y_H>\frac{31}{50},\qquad y_S<-\frac{31}{50}.
 \tag{22}
\]

The common cone routing places R above M_2. The complete low-side
bounds in ACTUAL_FOUR_CONE_TRIPLES, Appendix B, give

\[
 x_R<\frac{49}{80}.
 \tag{23}
\]

For clarity this covers its whole height range. If y_R<7/16,
the zero-side primitive gives x_R<2211/4000<49/80; its required
lower height bound follows from y_R>-139/120+97/100=-113/600.
If 7/16<=y_R<3/5, the endpoint inset argument gives (23)
directly.

Since l<=x_R and l<x_2<31/60, (23) gives
|x_R-x_2|<31/240<g_2. Thus the original center of R projects
inside the horizontal span of M_2's actual aligned inset. R's
incircle and that inset force

\[
 y_R-y_2\ge g_2+\frac12>\frac{61}{62},\qquad
 y_2<\frac35-\frac{61}{62}=-\frac{119}{310}<y_1.
 \tag{24}
\]

#### 6.2. The lower original gives a terminal or a positive right height

The reflected adjacent-proxy whole-square barrier, applied to the
same lower central V and the same actual inner insets, gives

\[
 y_V+h_V<\max(y_1,y_2)-\frac{869}{1860}
          =y_1-\frac{869}{1860}
          <-\frac{109}{930}<-\frac1{10}.
 \tag{25}
\]

If y_2<=-3/5, the three distinct originals S,V,M_2 supply
the reflected five-square cap: S has negative x and center below
-3/5 by (22), M_2 has positive x and center at most -3/5,
and V is central with whole top below -1/10 by (25). All three
are different from the outer endpoints M_0,M_3. This is the stated
terminal alternative.

In its complement y_2>-3/5, (24) implies

\[
 \frac{119}{310}<y_R<\frac35.
 \tag{26}
\]

We henceforth keep this complement and prove it impossible.

#### 6.3. The upper P has a good whole floor

The cone edge P<R and (23) give x_P<-7/80<0. Its own-half
central clearance and y_1>-7/20 give y_P>19/30. Suppose its
whole floor were at most 1/10. The high-left bad-floor cut in
ACTUAL_FOUR_CONE_TRIPLES, Section 3, using the unchanged H, gives

\[
 -\frac15<x_P<0,\qquad
 \frac{19}{30}<y_P<\frac{97}{120}.
 \tag{27}
\]

By (26), P is above R and y_R>37/100. Therefore their positive
center gaps are bounded by

\[
 x_R-x_P<\frac{13}{16},\qquad
 y_P-y_R<\frac{97}{120}-\frac{37}{100}
          =\frac{263}{600}.
\]

The sum of the squares of these bounds is strictly less than one:

\[
 \left(\frac{13}{16}\right)^2+
 \left(\frac{263}{600}\right)^2
 =\frac{1227301}{1440000}<1.
 \tag{28}
\]

This contradicts their original disjoint radius-half disks. Hence

\[
                         y_P-h_P>\frac1{10}.
 \tag{29}
\]

#### 6.4. The complete local theorem now applies

Take E=M_0 and the originals H,P,R already retained. Actual-four
localization gives every endpoint hypothesis (1). Equation (22) gives
the high H, the original cone triple gives x_H<x_P and the last
two gap conditions of (2), (23) and (26) give the closed low-right
bounds, and (29) gives the whole-floor condition. The local theorem
contradicts this complement. Consequently Section 6.2's reflected
five-square terminal is forced throughout the full stated lower-extra,
low-right branch.

The only additional original V is retained precisely where it is
needed: its whole top supplies the cap when y_2<=-3/5, thereby
forcing (26) on the complement. No seven-original exclusion is asserted
without that step. Horizontal and vertical reflection preserve the
same all-nine argument and every closed boundary.

The local theorem is independent of the all-nine caller in Section 6.
It may therefore be used in other occupancies after every guard in
(1)--(2) is supplied by their actual originals. This chapter does not
close the high-right complement of the lower-extra middle-main (2,2,1)
case or assert an unrestricted nine-square theorem.

<a id="appendix-c"></a>

## Appendix C. The strengthened side/main height bound

Complete hand proof, independently reviewed, 5 November 2026.
This strengthens the retained full-side height bound from 7/20 to 17/50.
The proof uses no mathematical program, interval certificate, Lean build,
or CI. Its physical support and corner facts are proved in
[FOUNDATION.md](FOUNDATION.md), and its main localization is in
[ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md). Every rational comparison
needed for the stronger constant is printed below.

Put
\[
 Q=\frac{1105}{256},\qquad l=\frac{29}{60},\qquad
 u=\frac{13}{12},\qquad c=\frac{17}{50}.
\]

### 1. Exact statement and physical center clearance

Let four original unit squares in the centered closed Q-disk form an
actual horizontal projection chain M0,M1,M2,M3. Let S be another
original unit square, interior-disjoint from M2, whose center (X,yS)
satisfies l<=X<=u and yS<y2. Then
\[
                         y_2>-\frac{17}{50}.             \tag{1}
\]
Horizontal and vertical reflection give the other three one-sided forms.
In particular, a side column with one original above and one below its
inner main has |yM|<17/50. No center-cone condition is required.

The actual-four localization gives l<x2<31/60 and
1/2<=hM<31/60. Fold each original frame so that its unsigned side
components satisfy a>=b>=0. Put
\[
 h=\frac{a+b}{2},\quad k=\frac{a-b}{2},\quad
 h^2+k^2=\frac12,\quad \frac12\le h\le\frac1{\sqrt2}.
\]
For the main square the same localization gives
\[
 b_M<\frac7{200},\qquad a_M>\frac{999}{1000}.
\]
These follow, for example, from
kM>193/400, bM=hM-kM<41/1200<7/200, and positive squaring.

For two physical unit squares with reduced relative angle Delta, every
side-owned separating axis has support sum
(1+cos Delta+sin Delta)/2. Their center distance is therefore at least
that number. For either pair of original chiralities,
\[
 \cos\Delta+\sin\Delta\ge2h a_M-2k b_M.
\]
For equal chiralities this follows by replacing the absolute sine of
the difference of frame angles by its signed sine; for opposite
chiralities the right side has instead the larger term +2k bM.
Consequently
\[
 |c_S-c_M|>
 \frac12+\frac{999}{1000}h-\frac7{200}k
 \ge h+\frac{241}{500}.                                  \tag{2}
\]
The improvement in the final constant is exact: h+k=a<=1 and k<=1/2
give h+35k=(h+k)+34k<=18, so
1/2-(h+35k)/1000>=241/500. The two inscribed radius-one-half disks
also give |cS-cM|>=1.

Suppose contrary to (1) that y2<=-c and reflect vertically, writing
Y=-yS. Define
\[
 D=X-\frac9{20},\qquad
 m=\max\left\{1,h+\frac{241}{500}\right\},\qquad
 s=\sqrt{m^2-D^2}.
\]
The main x-band gives |X-x2|<D: for X>=x2 use x2>l>9/20;
for X<x2 use 31/60-X<=X-9/20, valid for X>=l.
Thus
\[
 \frac1{30}\le D\le\frac{19}{30},\qquad
 Y>c+s,\qquad
 s\ge\frac{\sqrt{539}}{30}>\frac34.
                                                               \tag{3}
\]
The strict height inequality also holds when the disk clearance one is
active, because the horizontal-gap bound is strict. In particular
Y>109/100>u>=X.

### 2. Two retained original corners

For a square centered at (X,Y) with Y>=X>=0, either chirality gives
\[
 Q\ge\max\{(X+h)^2+(Y+k)^2,
                (X-k)^2+(Y+h)^2\}.                       \tag{4}
\]
For one chirality the two displayed terms are original corner norms.
For the other, the actual corner (X+k,Y+h) dominates them, with
respective squared-norm differences 2(h-k)(Y-X) and 4Xk.

Set
\[
 A(X,h)=(X+h)^2+(c+k+s)^2,\qquad
 B(X,h)=(X-k)^2+(c+h+s)^2.
\]
Equations (3)--(4) imply Q>max{A(X,h),B(X,h)}. For fixed h,
\[
 \frac12 A_X=\frac9{20}+h-\frac{D(c+k)}s
 >\frac{19}{20}-\frac{19}{30}\frac{21}{25}\frac43
 =\frac{361}{1500}>0.                                   \tag{5}
\]
Thus the first corner bound is minimized at X=l.

### 3. Small tilts: one half through 259/500

Put h0=259/500. For 1/2<=h<=h0, m=1 and at X=l one has
s0=sqrt(899)/30. The function
\[
 F_0(h)=(l+h)^2+(c+k+s_0)^2
\]
decreases with h. Indeed its derivative is negative precisely when
lk<h(c+s0), whose left side is at most 29/120 while its right side
is greater than one half.

At h=h0,
\[
 k^2=\frac{57919}{250000},\qquad
 k>\frac{4813}{10000},\qquad s_0>\frac{9994}{10000}.
\]
The positive squared reserves for the last two comparisons are
2631/100000000 and 19919/225000000. Therefore
\[
 \begin{aligned}
 A(X,h)&\ge F_0(h_0)\\
 &>\left(\frac{751}{750}\right)^2+
       \left(\frac{18207}{10000}\right)^2
 =Q+\frac{68101}{56250000}>Q.                            \tag{6}
 \end{aligned}
\]
This excludes the complete small-tilt interval, including its endpoints.

### 4. Intermediate tilts: 259/500 through 13/20

Here m=h+241/500>=1. At X=l,
\[
 m-s=\frac1{900(m+s)}<\frac1{1750}.
\]
For the last inequality m>=1 and s>=sqrt(899)/30>17/18 give
m+s>35/18. Hence
\[
 A(X,h)>
 F_1(h):=(l+h)^2+\left(h+k+\frac{23}{28}\right)^2,        \tag{7}
\]
where c+241/500-1/1750=23/28.

The function F1 is strictly concave throughout this interval. Indeed
\[
 F_1''=2+2(1-h/k)^2-
               \frac{h+k+23/28}{k^3}<0.
\]
Here 1<=h/k<5/2 and k<=1/2, so the positive terms are below 13/2.
Meanwhile h+k>7/10 and 23/28>4/5, so the subtracted term exceeds 12.
It therefore suffices to check the two endpoints.

At h=h0, the same comparison k>4813/10000 gives
\[
 h_0+k+\frac{23}{28}>
 \frac{18207}{10000},
\]
because h0+4813/10000+23/28-18207/10000=1/35000.
Thus (6) also bounds F1(h0) from below.

At h=13/20, use k=sqrt(31)/20>11/40. Then
\[
 h+k+\frac{23}{28}>\frac{489}{280}>\frac{349}{200},
\]
and consequently
\[
 F_1(13/20)>
 \left(\frac{17}{15}\right)^2+
 \left(\frac{349}{200}\right)^2
 =Q+\frac{18811}{1440000}>Q.                             \tag{8}
\]
Concavity excludes the whole intermediate interval.

### 5. Larger tilts: 13/20 through one over the square root of two

Use the other original corner B. For fixed h,
\[
 B_{XX}=-\frac{2(c+h)m^2}{s^3}<0,
\]
so its minimum on [l,u] occurs at an endpoint.

At X=l, the estimate of Section 4 gives
s>h+241/500-1/1750>9/8. Hence
\[
 B(l,h)>(c+h+s)^2>
 \left(\frac{21}{10}\right)^2
 =Q+\frac{599}{6400}>Q.                                 \tag{9}
\]

At X=u, the expression B(u,h) increases with h: k decreases,
s increases, and u-k is positive. At h=13/20 one has k<7/25
and s>93/100. For the latter, it suffices to replace m=283/250
by the smaller 113/100; the squared reserve is 49/4500.
Therefore
\[
 B(u,h)>
 \left(\frac{241}{300}\right)^2+
 \left(\frac{48}{25}\right)^2
 =Q+\frac{22087}{1440000}>Q.                             \tag{10}
\]
The endpoint h=1/sqrt(2) follows by continuity, or directly from the
same increasing quantities; no derivative of k at that endpoint is used.

All physical orientations and both chiralities have now been excluded
under y2<=-17/50. This proves (1), all reflected forms, and the stated
full-side middle-main bound. Every computation above is an exact
rational comparison or positive squaring, rather than an external table.

<a id="appendix-d"></a>

## Appendix D. The low central cone-endpoint exclusion

Complete hand proof, independently reviewed, 5 November 2026.
All separating directions and both original chiralities are retained.
The argument uses no mathematical program, numerical search, interval
certificate, Lean build, or CI.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad l=\frac{29}{60},\quad u=\frac{13}{12},
 \quad \alpha=\frac1{60},\quad G=\frac{15}{31},
 \quad C=G-\frac{17}{50}=\frac{223}{1550}>\frac7{50}.
\]

### 1. The exact local theorem

Retain an actual horizontal main four-chain in the centered closed Q-disk.
Let P and L be distinct original unit-square outsiders, disjoint in
interior from the mains and from one another. Suppose
\[
 \begin{gathered}
 c_P=(-p,Y),\qquad \frac{13}{60}<p<\frac{23}{60},
 \qquad y_2<Y\le\frac35,\qquad y_2>-\frac{17}{50},\\
 c_L=(-Z,H),\qquad \frac{11}{12}<Z<u,\qquad H>\frac{17}{20},
 \qquad H-Y\le Z-p .
 \end{gathered}
 \tag{1}
\]
These predicates are incompatible.

Here the last condition is the actual horizontal cone comparison L<P,
since H>Y. No projection separation between L and P is assumed.
No condition on the height of M1 or on another central outsider is needed.

The actual-four localization supplies, for the aligned inset of the
unchanged original M2,
\[
 x_2-g_2<\alpha,\qquad g_2>G,\qquad l<x_2<31/60.
 \tag{2}
\]
The physical support, inset, center-radius and separating-axis facts are
proved in [FOUNDATION.md](FOUNDATION.md); (2) is the correlated main
localization from [ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md).
In particular every original center has norm strictly below rho.

Write
\[
 d=Z-p,\qquad w=H-Y.
\]
The complete guards in (1) give
\[
 0<d<\frac{13}{15},\qquad \frac14<w\le d.
 \tag{3}
\]

### 2. The original M2/P separator has one of two upward-left forms

Let D=x2+p>0 and V=Y−y2>0. The aligned M2 inset satisfies
\[
 D-g_2<p+\alpha<\frac25,\qquad
 V-g_2<\frac{47}{50}-G<\frac12.
 \tag{4}
\]
Both coordinate axes therefore fail to separate this inset from P,
whose coordinate halfwidth h is at least one half.

By the physical separating-axis theorem, a separating normal must be
owned by the original P frame. Its vertical component must be positive:
a nonpositive vertical component has adjusted projection at most
\[
 |n_x|(D-g_2)-|n_y|(V+g_2)<\frac12.
\]
Its horizontal component must be negative: for an upward normal with
nonnegative horizontal component, the adjusted projection is
\[
 -n_x(D+g_2)+n_y(V-g_2)<\frac12.
\]
Both estimates contradict P's support one half on a unit side normal.

Fold the components of the same physical P frame as
\[
 a\ge b>0,\qquad a^2+b^2=1,\qquad
 h=\frac{a+b}{2},\qquad k=\frac{a-b}{2}.
\]
An aligned frame has only the excluded coordinate axes. The remaining
complete alternatives are
\[
 \begin{array}{c|c|c}
 \text{case}&n&\text{necessary original projection}\\ \hline
 \mathrm I&(-a,b)&n\cdot c_P>\frac12-a\alpha+bC\\
 \mathrm {II}&(-b,a)&n\cdot c_P>\frac12-b\alpha+aC .
 \end{array}
 \tag{5}
\]
Indeed the M2 inset separation requires
\[
 n\cdot c_P\ge\frac12+n\cdot c_{M2}
                         +g_2(|n_x|+|n_y|),
\]
and (2), y2>−17/50 give (5). The actual P frame that owns this
normal will be kept against L.

### 3. A point-to-square contradiction

Let q be an original unit side direction orthogonal to n, and put
\[
 v=n\cdot(c_L-c_P),\qquad z=q\cdot(c_L-c_P).
\]
In both cases v>0 by (3). The exact squared distance from cL to the
physical P is
\[
 \operatorname{dist}(c_L,P)^2
   =\left(v-\frac12\right)_+^2+
     \left(|z|-\frac12\right)_+^2.
 \tag{6}
\]
The original L contains the closed disk of radius one half about cL.
Thus distance less than one half contradicts the original disjoint
open interiors. We establish that strict bound for every possible frame.

We use two elementary circle consequences:
\[
 \sqrt{\rho^2-u^2}<\frac{17}{16},\qquad
 \sqrt{\rho^2-(11/12)^2}<\frac{121}{100}.
 \tag{7}
\]
Their positive squared reserves are 43/19200 and 41/10000.
For nonnegative coefficients s,t with s²+t²=1, the maximum of
sZ+t sqrt(rho²−Z²) on [11/12,u] occurs at u if s rho>u,
and at 11/12 if s rho<11/12. This follows directly by differentiation;
the unconstrained maximum is at Z=s rho.

#### 3.1. Case I with b at most nine twentieths

Take n=(−a,b), q=(b,a), and suppose b<=9/20.
Then a>4/5, hence a rho>u. Equations (5)--(7) imply
\[
 \begin{aligned}
 v&<a(u+\alpha)+b(17/16-C)-\frac12\\
  &<\frac{11}{10}a+\frac{93}{100}b-\frac12
   <\frac{19}{20}.
 \end{aligned}
 \tag{8}
\]
The last inequality is Cauchy--Schwarz, with exact squared reserve
\[
 (29/20)^2-(11/10)^2-(93/100)^2=\frac{69}{2500}>0.
\]

The same original main separator also restricts k. Since Y<=3/5,
\[
 T:=Y-h\le\frac1{10},\qquad
 c_R:=y_2+g_2-T>C-\frac1{10}>0.
\]
The separating inequality in this case gives
\[
 \frac12<a(p+\alpha)+b(h-c_R)<a(p+\alpha)+bh .
\]
Since 1/2−bh=ak, it follows that
\[
                              k<p+\alpha.                 \tag{9}
\]
The other original coordinate is z=−bd+aw. By (3),
\[
 -bd\le z\le(a-b)d,\qquad bd<\frac{39}{100},
\]
and (9) gives
\[
 (a-b)d<2(p+\alpha)(u-p)\le\frac{14}{25}.
\]
The quadratic in p is increasing through p=23/60, where its value
is 14/25. Consequently |z|<14/25. Substitution in (6) yields
\[
 \operatorname{dist}(c_L,P)^2
 <\left(\frac9{20}\right)^2+\left(\frac3{50}\right)^2
 =\frac{2061}{10000}<\frac14.
 \tag{10}
\]

#### 3.2. Case I with b at least nine twentieths

Now b>=9/20 and a<9/10. Use n·cL<rho directly in (5):
\[
 \begin{aligned}
 v&<\frac{61}{60}+\frac a{60}-bC\\
  &<\frac{61}{60}+\frac3{200}-\frac{63}{1000}
   =\frac{1453}{1500}<\frac{97}{100}.
 \end{aligned}
 \tag{11}
\]
Again z=−bd+aw is between −bd and (a−b)d. Here
\[
 (a-b)d<\left(\frac9{10}-\frac9{20}\right)\frac{13}{15}
          =\frac{39}{100},\qquad
 bd<\frac34\frac{13}{15}=\frac{13}{20}.
\]
Thus |z|<13/20. Formula (6) gives
\[
 \operatorname{dist}(c_L,P)^2
 <\left(\frac{47}{100}\right)^2+\left(\frac3{20}\right)^2
 =\frac{1217}{5000}<\frac14.
 \tag{12}
\]

#### 3.3. Case II with b at most one third

Take n=(−b,a), q=(a,b), and b<=1/3. Since b rho<11/12,
the second circle maximum in (7) and (5) give
\[
 \begin{aligned}
 v&<\frac{14}{15}b+(121/100-C)a-\frac12\\
  &<\frac{14b+16a}{15}-\frac12 .
 \end{aligned}
 \tag{13}
\]
The coefficient improvement is exact:
\[
 \frac{16}{15}-(121/100-C)=\frac1{1860}>0.
\]
The function 14b+16 sqrt(1−b²) increases on [0,1/3], as is seen
from its derivative 14−16b/sqrt(1−b²)>0. At the right endpoint
a=sqrt(8)/3<19/20. Therefore
\[
 \frac{14b+16a}{15}<\frac{14}{45}+\frac{76}{75}
       =\frac{298}{225}<\frac43,
 \qquad v<\frac56.                                  \tag{14}
\]
This frame has z=−ad+bw<=0 by (3), and
|z|=ad−bw<13/15. Hence
\[
 \operatorname{dist}(c_L,P)^2
 <\left(\frac13\right)^2+\left(\frac{11}{30}\right)^2
 =\frac{221}{900}<\frac14.
 \tag{15}
\]

#### 3.4. Case II with b at least one third

Here a<19/20, a>7/10, and b<3/4. The universal center bound
and (5) yield
\[
 \begin{aligned}
 v&<\frac{61}{60}+\frac b{60}-aC\\
  &<\frac{61}{60}+\frac1{80}-\frac{49}{500}
   =\frac{5587}{6000}<\frac{15}{16}.
 \end{aligned}
 \tag{16}
\]
Using the positive lower bound w>1/4 in (3) now gives
\[
 |z|=ad-bw<
 \frac{19}{20}\frac{13}{15}-\frac13\frac14
       =\frac{37}{50}.
\]
Thus the same physical P satisfies
\[
 \operatorname{dist}(c_L,P)^2
 <\left(\frac7{16}\right)^2+\left(\frac6{25}\right)^2
 =\frac{39841}{160000}
 =\frac14-\frac{159}{160000}<\frac14.
 \tag{17}
\]
This includes the boundary b=1/3; the earlier range includes it as well.

All original normal owners were exhausted before the frame was forced,
and both possible forced chiralities have now been excluded. The same
radius-half disk inside L meets the same original P in every case.
This proves the theorem in Section 1.

<a id="appendix-e"></a>

## Appendix E. A low-floor right central and a high right shoulder

Complete hand proof, independently reviewed, 5 November 2026. Every
physical separating axis is included. The scalar reserves needed below
are printed in the proof; no interval table, arithmetic program, Lean
build, or CI is an input.

Set

\[
 l=29/60,\quad u=13/12,\quad \rho=91/60,
 \quad J=23/150,\quad A_0=18911/59520,
\]

\[
 c=A_0-1/10=12959/59520,\quad v_0=223/372,
 \quad g=7/20,\quad G=J+1/60=17/100.
\]

### 1. The complete original-square predicate

Retain an actual horizontal main four-chain in the closed disk of squared
radius \(Q=1105/256\). Retain distinct original outsiders S,F,R, each
physically interior-disjoint from the main squares and from the other
outsiders. Suppose the left helper S has aligned inset halfwidth gS and
center \((-Z,y_S)\), with

\[
 Z>0,\qquad Z-g_S<J,\qquad y_S<7/16,
 \qquad y_S+g_S>A_0.
 \tag{1}
\]

Suppose F is a right central outsider above the right inner main M2,
whose center and whole floor satisfy

\[
 0<X=x_F\le l,\qquad Y=y_F>v_0,
 \qquad T=Y-h_F\le1/10.
 \tag{2}
\]

Suppose the original right inner main's proxy top is above one tenth:

\[
                            y_2+g_2>1/10.
 \tag{3}
\]

Finally suppose the original right outsider R satisfies

\[
                         l\le x_R<u,\qquad y_R\ge3/5.
 \tag{4}
\]

These complete predicates are incompatible. No short-chain comparison,
frame assumption, or separator owner is imposed on any square. The result
also holds after either coordinate reflection with the corresponding
reflected predicates.

The actual-four bounds supply

\[
 l<x_2<31/60,\qquad x_2-g_2<1/60,
 \qquad x_2+g_2>59/60,\qquad |c_R|<\rho.
 \tag{5}
\]

These correlated bounds belong to the same original main squares;
see [ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md) and the retained
[outsider-strip proof](sources/UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md).
The physical inset, support, and separating-axis facts are in
[FOUNDATION.md](FOUNDATION.md).

Every unit square contains an aligned square of halfwidth
\(1/(4h)\ge1/(2\sqrt2)>g=7/20\). Thus in particular \(g_S>g\),
and we may use the fixed aligned inset of halfwidth g inside R.

### 2. The right main forces an upward left F-owned separator

Write

\[
 a\ge b\ge0,\quad a^2+b^2=1,\quad h=(a+b)/2,
 \quad k=(a-b)/2
\]

for the unsigned components of the one original F frame. Define
\(c_R=y_2+g_2-T>0\). For F and the right main inset, the center gaps
are \(D_R=x_2-X>0\), \(V_R=Y-y_2>0\). Then

\[
 D_R-g_2<1/60-X<1/2,\qquad V_R-g_2=h-c_R<h.
 \tag{6}
\]

Both coordinate axes fail. Every physical separator must be an F side
axis and have positive vertical component: a nonpositive vertical component
would require \(|n_x|(D_R-g_2)\ge1/2+g_2|n_y|\), contrary to (6).

Its horizontal component must point left. An upward right F axis with
vertical component b has adjusted projection below \(bh\le1/2\).
For vertical component a the adjusted projection is below

\[
 ah-b(D_R+g_2)=1/2+b\{k-(D_R+g_2)\}\le1/2,
\]

since \(D_R+g_2>59/60-l=1/2\ge k\). Thus these alternatives also fail.
An aligned F has no remaining side axis; hence \(b>0\). Put
\(t=b/a\in(0,1]\). The two remaining original F side normals are

\[
 (-a,b)\quad\hbox{or}\quad(-b,a).
\]

Their respective necessary inequalities are

\[
 X<1/60-k-tc_R,
 \qquad X<1/60+k-c_R/t.
 \tag{7}
\]

### 3. The left helper leaves two complete alternatives

F is above S because \(Y>v_0>7/16>y_S\). Set
\(D_L=X+Z>0\), \(V_L=Y-y_S>0\), and \(c_L=A_0-T\ge c\).
The original S inset obeys

\[
 D_L-g_S<X+J,\qquad V_L-g_S<h-c_L.
 \tag{8}
\]

Vertical coordinate separation is impossible. If horizontal separation is
possible, (8) gives the first alternative

\[
                         \mathcal H:\quad X>h-J.
 \tag{9}
\]

Suppose it is impossible, so \(D_L-g_S<h\). Every remaining separator
is F-owned. Its vertical component must be positive. Indeed

\[
 V_L+g_S>v_0-7/16+7/20>1/2,
 \qquad v_0-47/80=89/7440>0.
\tag{10}
\]

A downward F axis with horizontal component a has adjusted projection less
than \(ah-b/2=1/2+b(k-1/2)\le1/2\). One with horizontal component b
has projection below \(bh-a/2<1/2\). Both fail.

An upward axis pointing left also fails. With vertical component b its
projection is below \(bh\le1/2\); with vertical component a it is below

\[
 1/2+b(k-D_L-g_S)-ac_L<1/2,
\]

because \(g_S>1/3\), \(k\le1/2\), and \(c_L\ge c>1/6\).
The left separator therefore points up and right.

It is the other orthogonal F axis from the upward left separator in
Section 2. If its components were \((b,a)\), the right components would
be \((-a,b)\), and summing their two necessary inequalities would give

\[
 Z-g_S+x_2-g_2>c_L/t+tc_R\ge c>G.
\]

This contradicts (1) and (5), which give the same sum less than G.
Thus in this oblique alternative the actual left and right F normals are
\((a,b)\), \((-b,a)\), and the left inequality gives

\[
 \mathcal O:\quad X>k+t(A_0-T)-J,
 \qquad aX+bY>1/2+bA_0-aJ.
 \tag{11}
\]

In alternative \(\mathcal H\), the first right-axis choice in (7)
is equally impossible: together with (9) it would imply
\(a=h+k<J+1/60=G\), whereas \(a\ge1/\sqrt2\). Therefore the
actual F axes in \(\mathcal H\) are also \((a,b)\), \((-b,a)\).

We have exhausted every original helper/main separator. Both alternatives
have the same original frame chirality; it has been deduced, not imposed.

### 4. Both alternatives give a small tangent and a horizontal overlap

In alternative \(\mathcal O\), add the left and right oblique
inequalities to obtain

\[
                    tc_L+c_R/t<G,
 \qquad t<G/c<4/5.
 \tag{12}
\]

In alternative \(\mathcal H\), (9) and \(X\le l\) give
\(h<l+J=191/300\). The function
\(h(t)=(1+t)/(2\sqrt{1+t^2})\) increases on \([0,1]\), and
\(h(4/5)^2=81/164>(191/300)^2\). Hence again \(t<4/5\).

We claim that the horizontal center gap from F to R obeys

\[
                         0\le D=x_R-X<h+g.
 \tag{13}
\]

In \(\mathcal H\), it is below \(u+J-h\), which is below \(h+g\)
because \(2h\ge1>u+J-g=133/150\).

In \(\mathcal O\), it is below \(u+J-k-tc\). For \(0\le t\le4/5\),

\[
 a\ge1-t/3,\qquad c>3/14,
 \qquad a+tc>1-(5/42)t\ge19/21>133/150.
 \tag{14}
\]

The first inequality follows by positive squaring:

\[
 1-(1-t/3)^2(1+t^2)=
 \frac{t}{9}(6-10t+6t^2-t^3)\ge0.
\]

The cubic decreases on \([0,4/5]\) and its right-endpoint value is
\(166/125>0\). Equation (14) proves (13), since \(h+k=a\).
The final strict margin in (14) is \(19/1050\).

### 5. All four axes fail against the original right shoulder's inset

Let \((s,z)\) be R's center, and put \(\delta=z-Y\). Its universal
center bound and \(s\ge l\) imply

\[
 z<\sqrt{\rho^2-l^2}<36/25,
 \qquad \delta<36/25-v_0<17/20.
 \tag{15}
\]

In the opposite vertical order, the assumed central floor and (4) give

\[
                 -\delta=Y-z\le h-1/2<5/24<g.
 \tag{16}
\]

Thus \(|\delta|<17/20\le h+g\). Together (13), (15)--(16) exclude
both coordinate-axis separators between F and R's fixed aligned inset.

#### 5.1. The F axis with components (a,b)

Because \(t<4/5\), the maximum of \(as+bz\) on
\(s^2+z^2\le\rho^2\), \(s\le u\), \(s,z\ge0\) occurs at s=u.
Indeed the unconstrained maximizing coordinate is \(a\rho>u\);
the exact squared reserve is
\[
 \frac{\rho^2}{1+(4/5)^2}-u^2=\frac{169}{738}>0.
\]
Also

\[
 \sqrt{\rho^2-u^2}<17/16,
 \quad (17/16)^2-(\rho^2-u^2)=43/19200>0.
\]

Consequently

\[
                         as+bz<au+(17/16)b.
 \tag{17}
\]

In alternative \(\mathcal O\), the positive (a,b) separator from F
to R would require, by (11) and (17),

\[
 a\underbrace{(u+J-g)}_{A}
 +b\underbrace{(17/16-A_0-g)}_{B}>1.
 \tag{18}
\]

Here \(A=133/150<9/10\), and
\[
 0<B=57/80-A_0<2/5,
 \qquad A_0-5/16=311/59520>0.
\]
Consequently \(A^2+B^2<97/100<1\). Since \(a^2+b^2=1\),
Cauchy--Schwarz makes (18) impossible.

In alternative \(\mathcal H\), (9), \(Y>v_0\), and \(h\ge1/2\)
give \(aX+bY>a(1/2-J)+bv_0\). The same necessary separator
would therefore require

\[
 a\underbrace{(u+J-g-1/2)}_{A_H}
 +b\underbrace{(17/16-v_0-g)}_{B_H}>1/2.
 \tag{19}
\]

Here
\[
 A_H=29/75<2/5,\qquad 0<B_H=57/80-v_0<1/8,
 \qquad v_0-47/80=89/7440>0.
\]
Thus
\[
 A_H^2+B_H^2<4/25+1/64=281/1600<1/4,
\]
so Cauchy--Schwarz again excludes it.

For the opposite sign of this same F axis, its center projection is
\(-aD-b\delta\le b\max(-\delta,0)<5b/24\), which is less than
its required support \(1/2+g(a+b)\). Thus neither sign separates.

#### 5.2. The other original F axis

The other side normal is \((-b,a)\). If \(\delta\ge0\), its
positive projection is \(-bD+a\delta\le\delta<17/20\), below
\(1/2+g(a+b)\). Its negative projection is at most
\(bD<b(h+g)\le1/2+bg<1/2+g(a+b)\), using \(bh\le1/2\).

If \(\delta<0\), the positive projection is negative. The negative
projection is, by (13) and (16),

\[
 bD+a(-\delta)<b(h+g)+5a/24
             \le1/2+bg+5a/24<1/2+g(a+b).
\]

Both signs fail again. Every coordinate and original F side axis has now
failed, contradicting the physical disjointness of F and the inset inside
R. This proves the complete statement in Section 1.

### 6. Exact scope

The conclusion is precisely the incompatibility of the original-square
predicates (1)--(4). It needs an actual main four-chain, but no main cone
comparison, side count, or selected outsider short chain. In applications,
the low-left-helper contract (1) can come from
[ACTUAL_FOUR_FULL_SIDES.md](ACTUAL_FOUR_FULL_SIDES.md), Section 3.2;
that section is a local theorem and does not require both sides to be full.

No original pair or frame has been replaced by an independently selectable
configuration. The one unchanged F frame was forced by the S/M2 pairs
and then used against the original R's contained inset. Both original
chiralities and every touching alternative were included before the frame
was forced. The inequalities retained in (1)--(4) give the strict reserves
displayed above.

<a id="appendix-f"></a>

## Appendix F. Sharpened main-height bound and complete negative-case reduction

Complete hand arguments, independently reviewed, 6 November 2026.
Appendix I supplies the final compact scalar inequality used by this reduction.

The physical support, incircle, inset, and separating-axis facts are in
[FOUNDATION.md](FOUNDATION.md); the correlated inner-main inset bounds
come from [ACTUAL_FOUR_CHAIN.md](ACTUAL_FOUR_CHAIN.md). The local theorem
in Sections 1–4 uses only its displayed proxy hypotheses. Section 5 is
a conditional application retaining its displayed original-square guards.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad u=\frac{13}{12},\quad
 \alpha=\frac1{60},\quad A=\frac{59}{60},\quad
 G=\frac{15}{31},\quad c=\frac{239}{400},\quad
 C=c+G=\frac{13409}{12400}.
\]

### 1. Exact local theorem

Let I be an aligned square of halfwidth g, centered at (x0,Z), with
\[
 g>G,\qquad x_0-g<\alpha,\qquad x_0+g>A.                 \tag{1}
\]
Let F be a physical unit square in the centered Q-disk, whose open
interior is disjoint from I. Write (X,Y) for its center and h for its
coordinate halfwidth. Suppose
\[
                    0\le X\le u,\qquad Y>Z.            \tag{2}
\]
Then
\[
                         X+2Z<\frac{239}{200}.                 \tag{3}
\]

The proxy I need not itself be contained in the Q-disk. In applications
it is the actual aligned inset of the right inner main of an actual
horizontal four-chain. Horizontal reflection gives the left-main
version, and vertical reflection gives the lower-original versions.
Every bound concerns the same original F.

Suppose contrary to (3) that
\[
                         Z\ge c-\frac X2.          \tag{4}
\]
The physical facts used below are
\[
 |(X,Y)|<\rho,\quad Y+h\le r,\quad r<\frac{25}{12},
 \quad C>\frac{27}{25},\quad r<C+1.                      \tag{5}
\]
The last inequality follows, for example, from
r<133/64<52/25<C+1.

Both horizontal coordinate directions fail to separate F from I:
\[
 X-x_0-g<X-A\le u-A=\frac1{10}<\frac12,
 \quad x_0-X-g<\alpha-X\le\alpha<\frac12.
\]
Every downward or horizontal F-owned normal fails for the same reason:
its adjusted horizontal contribution is below one half, and its
nonpositive vertical contribution cannot help because Y>Z. Thus the
complete remaining list consists of the vertical coordinate axis and
F-owned upward normals.

### 2. The vertical coordinate axis

A vertical separator gives Y>=Z+g+h. With v=(1/2,1), (4) yields
\[
                         v\cdot(X,Y)>C+h.               \tag{6}
\]
If h>=13/20, the center-radius bound gives a contradiction directly:
\[
 C+h>\frac{173}{100}>
 \frac{273}{160}=\frac98\rho>
 \frac{\sqrt5}{2}\rho>v\cdot(X,Y).
\]
Here sqrt(5)/2<9/8 by positive squaring.

It remains that h<13/20. Fold F's actual frame to a>=b>=0, with
a^2+b^2=1 and h=(a+b)/2, and put t=b/a. The increasing halfwidth
function h(t)=(1+t)/(2sqrt(1+t^2)) has
h(5/12)=17/26>13/20. Hence 0<=t<5/12<1/2.
For either original chirality,
\[
 H_F(v)\ge\frac{3a-b}{4},\qquad
 h+H_F(v)\ge\frac{5a+b}{4}\ge\frac54.
\]
The last inequality follows by squaring
(5+t)/sqrt(1+t^2)>=5: its numerator reserve is
10t-24t^2>=0. Containment and (6) now give
\[
 r|v|\ge v\cdot(X,Y)+H_F(v)>C+\frac54>
 \frac{233}{100}>r\frac{\sqrt5}{2}=r|v|,
\]
a contradiction. The final positive squared reserve is
\[
 \left(\frac{233}{100}\right)^2-\frac54 Q
       =\frac{21371}{640000}.
\]
Thus the vertical coordinate case is completely excluded.

### 3. Upward-left F-owned normals

Write such a unit normal as n=(-p,q), with p>=0,q>0 and
p^2+q^2=1. Its support on F is one half. Its separating inequality
and (1) give
\[
 -pX+qY>\frac12-\alpha p+q(Z+G).                         \tag{7}
\]
Here h=(p+q)/2.

First suppose p>=q/2. Use Y+h<=r and (4) in the adjusted separating
projection. It is strictly below
\[
 \alpha p+q(r-C-h)+(q/2-p)X
 \le\alpha p+q(r-C-h)
 <\alpha+\frac q2.
\]
The inequality p>=q/2 gives q<=2/sqrt(5)<9/10, so this is below
1/60+9/20=7/15<1/2. It cannot be a separator.

Now let 0<=p<=q/2 and t=p/q in [0,1/2]. Put d=sqrt(1+t^2).
Combining (7) with (4) gives, in direction v=(-p+q/2,q),
\[
 v\cdot(X,Y)>\frac12-\alpha p+Cq.
\]
The other physical F axis is (q,p), so
\[
 H_F(v)=\frac12-\frac{pq}{4}+\frac{q^2}{4}.
\]
Containment would consequently require
\[
 d+C-\alpha t+\frac{1-t}{4d}
       <r\sqrt{t^2-t+5/4}.                              \tag{8}
\]
But d+(1-t)/(4d)>=1+(1-t)/4, since d>=1 and the left
expression increases with d. Thus the left side minus the right side
of (8) is at least
\[
 W(t)=C+\frac54-\frac4{15}t-r\sqrt{t^2-t+5/4}.
\]
This is concave on [0,1/2], because the square root has strictly
positive second derivative. At t=0, W(t)>0 by the squared comparison
in Section 2. At t=1/2,
\[
 W(1/2)> \frac{233}{100}-\frac2{15}-r
           =\frac{659}{300}-r>0.
\]
A concave function is bounded below by the smaller of its endpoint
values. Hence (8) is impossible throughout its complete interval.

### 4. Upward-right F-owned normals

Write n=(p,q), p>=0,q>0,p^2+q^2=1. Its separation gives
\[
 pX+qY>\frac12+Ap+q(Z+G).                               \tag{9}
\]
Again h=(p+q)/2.

#### 4.1. A small vertical component is impossible

Suppose q<=2/5. Then p>9/10 and h>9/20+q/2.
From (4), Y+h<=r, and X<=u, the adjusted separating projection
in (9) is strictly below
\[
 \frac p{10}+q\left(r-G-\frac{67}{1200}-h\right)
 <\frac1{10}+\frac{11}{10}q-\frac{q^2}{2}
 \le\frac{23}{50}<\frac12.
\]
For the middle inequality use
r-G-67/1200<31/20: here c-u/2=67/1200 and
25/12-12/25-67/1200=619/400<31/20.
The quadratic increases on [0,2/5]. Thus
\[
 q>\frac25,\qquad 0\le t:=p/q<\frac{\sqrt{21}}2.         \tag{10}
\]

#### 4.2. The exact scalar consequence in the retained frame

Put v=(p+q/2,q). From (4) and (9),
\[
 v\cdot(X,Y)>\frac12+Ap+Cq.
\]
Its projections on the same physical axes n=(p,q), m=(-q,p) are
1+pq/2 and -q^2/2. Hence
\[
 H_F(v)=\frac12+\frac{pq}{4}+\frac{q^2}{4}.
\]
Writing d=sqrt(1+t^2), containment would require J(t)<0, where
\[
 J(t)=d+C+\frac{59}{60}t+\frac{1+t}{4d}
                    -r\sqrt{t^2+t+5/4}.                \tag{11}
\]
We prove J>0 on the closed interval [0,sqrt(21)/2].

#### 4.3. Direct concavity bounds

For f(t)=sqrt(1+t^2)+(1+t)/(4sqrt(1+t^2)),
\[
 f''(t)=\frac{3(1-t+2t^2)}{4(1+t^2)^{5/2}}.
\]
The second derivative of sqrt(t^2+t+5/4) is
1/(t^2+t+5/4)^{3/2}. Define
\[
 E(t)=\frac{1-t+2t^2}{1+t^2}
      =2-\frac{1+t}{1+t^2},\qquad
 F(t)=\frac{t^2+t+5/4}{1+t^2}.
\]
Thus J''<0 follows from
\[
                  \frac9{16}E(t)^2F(t)^3<Q.             \tag{12}
\]
On [0,1], E<=1 and F<5/3; the latter is the positive quadratic
8t^2-12t+5>0. On [1,infinity), E increases and F decreases.
The following four direct rational bounds exhaust (10).

| Interval for t | Bound for E | Bound for F | Bound for (9/16)E^2F^3 |
| --- | --- | --- | --- |
| [0,1] | 1 | 5/3 | 125/48<Q |
| [1,3/2] | 16/13 | 13/8 | 117/32<Q |
| [3/2,2] | 7/5 | 20/13 | 8820/2197<17/4<Q |
| [2,sqrt(21)/2] | 3/2 | 3/2 | 2187/512=Q-23/512 |

In the last row sqrt(21)/2<7/3, and
E(7/3)=43/29<3/2, while F(2)=29/20<3/2.
Every number in the table is obtained by the displayed monotonicity
or one positive rational comparison; the table is not an external
interval certificate. This proves strict concavity.

#### 4.4. The two endpoints

At t=0,
\[
 J(0)> \frac{233}{100}-r\frac{\sqrt5}{2}>0
\]
by Section 2.

At t=sqrt(21)/2, return to p=sqrt(21)/5, q=2/5.
Using C>27/25, the left side of the original supported inequality
is greater than L-1/750, where
\[
 L=\frac{442+65\sqrt{21}}{300}.
\]
The right side is (r/5)sqrt(26+2sqrt(21)). The auxiliary squared
difference is
\[
 L^2-\frac Q{25}(26+2\sqrt{21})
 =\frac{422110\sqrt{21}-1918826}{1440000}
 >\frac{75738}{10080000}.
\]
Here sqrt(21)>32/7 and
422110*32-1918826*7=75738>0. Also sqrt(21)<14/3 gives
L<559/225<5/2. Therefore the needed squared difference is
\[
 \left(L-\frac1{750}\right)^2
       -\frac Q{25}(26+2\sqrt{21})
 >\frac{75738}{10080000}-\frac1{150}
 =\frac{1423}{1680000}>0.
\]
Both quantities are positive, so J(sqrt(21)/2)>0.
Concavity and the two endpoint values prove J>0 everywhere in (10),
contradicting (11).

All coordinate and original side-owned separators have been excluded.
This proves the local theorem (3).

### 5. Application to the two P-owned right separators in middle (2,2,1)

This application retains the complete actual-and-cone main four-chain
and all nine physical originals. The full left side has S below M1
and H above it, P is the selected upper central original, V is the
other central original below both mains, and R is the selected high
right original. Suppose P is negative and has bad floor:
\[
 x_P=-p,\quad 0\le p<1/5,\quad f=y_P-h_P\le1/10.
\]
The physical reduction used in this application retains the guards
\[
 -\frac7{20}<y_1<-\frac14,\quad y_2<y_1,\quad y_S<-\frac{61}{50},\quad x_V>0,
 \quad y_V<y_2-\frac{59}{60}.
\]
The unchanged P frame has axes n=(b,a), m=(-a,b), with a>=b>0,
t=b/a<=1 and k=(a-b)/2. The left-main inset is separated on n, giving
\[
 y_1<f-G+t(k-p+\alpha).                                 \tag{13}
\]
The right-main inset has only a vertical coordinate separator or one
of the two upward P axes. We exclude both P-owned choices here.

If its separator is n=(b,a), then
\[
 y_2<f-G-t(59/60+p-k).
\]
Together with (13), 2k<=1, p>=0, t<=1 and f<=1/10 give
\[
 y_1+y_2<\frac15-2G+\frac1{30}
                 =-\frac{683}{930}.                    \tag{14}
\]

If instead its separator is m=(-a,b), then
\[
 y_2<f-G-\frac{k-p-\alpha}{t}.
\]
Use the retained y1>-7/20 guard in (13). In a full-left-middle caller,
it follows from the stronger reviewed
[17/50 main-height bound](#appendix-c). It gives t(k-p+alpha)>G-9/20=:c0=21/620.
Since t-1/t<=0, summing the two main inequalities yields
\[
 \begin{aligned}
 y_1+y_2
 &<\frac15-2G+c_0(1-t^{-2})+\frac{2\alpha}{t}\\
 &\le\frac15-2G+2\alpha=-\frac{683}{930}.
 \end{aligned}
\]
The last scalar function decreases as 1/t increases on [1,infinity),
because c0>alpha. Thus (14) holds for this owner as well.

Reflect vertically and apply the weaker 6/5 corollary of the local
theorem to original S at the left main and original V at the right main. Their horizontal center
gap is
\[
 x_V-x_S<\frac{12}{5}+2(y_1+y_2)
          <\frac{433}{465}<\frac{14}{15}.
\]
Both lower center heights are below -61/50: this is already known for
S, and follows for V from y2<y1<-1/4 and its 59/60 own-half gap.
Their absolute vertical center gap is therefore less than
rho-61/50=89/300<3/10. Consequently their center distance squared is
less than
\[
 \left(\frac{14}{15}\right)^2+\left(\frac3{10}\right)^2
       =\frac{173}{180}<1,
\]
contrary to their original disjoint incircles.

Only the right-main vertical-coordinate separator remains in this
negative bad-P branch. Sections 6--7 and Appendix I exclude that
last separator with the same original squares.


### 6. Negative bad P: the complete vertical-right reduction

This section retains the complete full-left-middle (2,2,1) caller.
The four mains are an actual horizontal projection chain and a
center-cone chain, with inward endpoint span D>=2. The five distinct
original outsiders are S,H in the left strip, P,V in the central
strip, and R in the right strip. They satisfy
\[
 y_S<y_1<y_H,\quad
 y_P>\max(y_1,y_2),\quad y_V<\min(y_1,y_2),\quad
 H<P<R
\]
for the selected original cone triple. In the branch treated here
\[
 y_R\ge3/5,\quad x_P=-p\le0,\quad f=y_P-h_P\le1/10.
\]
All nine original squares retain their original frames and corner
constraints. The usual reflected five-square cap has already removed
y2<=-3/5. Its adjacent-proxy barrier gives y2<y1.
The reviewed side-height theorem gives |y1|<17/50, and hence
yH>63/100 and yS<-63/100. The actual-four localization, center
clearances, cone routing, and five-square-cap inputs are unchanged.

For clarity, the guard proofs needed for the later scalar reduction
are included here.

#### 6.1. The high left original bounds p, and the left main fixes P's frame

The central strip and cone routing give 0<=p<23/60. Own-half central
clearance and the bad floor give
\[
                 \frac{193}{300}<Y:=y_P<\frac{97}{120}.
\]
In fact p<1/5. Suppose p>=1/5, and write cH=(-Z,H), with
l<=Z<=u, H>=3/5, and Z^2+H^2<rho^2.
If H<=Y, their center distance squared is less than
\[
 (53/60)^2+(5/24)^2=11861/14400<1.
\]
If H>=Y, that squared distance is at most
\[
 (Z-1/5)^2+\left(\sqrt{\rho^2-Z^2}-3/5\right)^2.
\]
This is a convex function of Z, so its maximum is at l or u.
At l use sqrt(rho^2-l^2)<36/25; the resulting bound is
(17/60)^2+(21/25)^2<1. At u use
sqrt(rho^2-u^2)<17/16; the bound is
\[
              (53/60)^2+(37/80)^2=57265/57600<1.
\]
All alternatives contradict the original disjoint incircles.

Let g1 be M1's actual aligned inset halfwidth. Its correlated bands give
x1+g1>-alpha and x1-g1<-59/60. Put
\[
 d_L=-p-x_1>0,\quad V_L=Y-y_1>0,\quad
 c_L=y_1+g_1-f>G-\frac{11}{25}=\frac{34}{775}.
\]
Then
\[
 d_L-g_1<\alpha-p\le\alpha,\quad
 d_L+g_1>59/60-p>1/2,\quad V_L-g_1=h_P-c_L.
\]
Both coordinate axes fail to separate P from that inset. Every
non-upward P-owned axis fails by its adjusted horizontal bound.
Every upward-left axis fails as well: if its vertical component is b
the adjusted projection is below bh<=1/2; if its vertical component
is a, the projection is below
ah-b(dL+g1)=1/2+b(k-dL-g1)<1/2.

Fold P's unsigned components to a>=b>=0, and put k=(a-b)/2.
If its upward-right axis were (a,b), its adjusted projection would
be less than
\[
 a\alpha+b(h_P-c_L)=\frac12-a(k-\alpha)-bc_L<\frac12.
\]
Indeed, with t=b/a, one has
k+(34/775)t>alpha: k=(a/2)(1-t), a/2>34/775, and
34/775>alpha. The aligned endpoint b=0 is included in the failure
of the coordinate axes. Thus b>0 and the actual surviving separator
is
\[
                 n=(b,a),\qquad m=(-a,b),\qquad
                 t=b/a\in(0,1],\quad h=(a+b)/2.
\]
These are the same P axes in every subsequent pair. Its separating
inequality gives
\[
 n\cdot c_P>\frac12-\alpha b+a(y_1+G),\qquad
 y_1<f-G+t(k-p+\alpha).                                 \tag{26}
\]

#### 6.2. The lower central is positive and the right-owned cases are exhausted

The elementary bound k<=(1-t)/2 yields
\[
 t(k-p+\alpha)\le\frac{31}{60}t-\frac{t^2}{2}
                    \le\frac{961}{7200}.
\]
Consequently (26) gives
\[
 y_1<-\frac14-\frac{89}{223200},\qquad y_S<-\frac{61}{50}.
\]
If xV<=0, its own-half central clearance would give yV<-37/30.
The centers of S and V would then lie in the rectangle
\[
 [-\sqrt{\rho^2-(61/50)^2},0]\times[-\rho,-61/50],
\]
whose squared diameter is 2rho(rho-61/50)=8099/9000<1.
This contradicts their disjoint incircles. Therefore xV>0, and
\[
                         y_V<y_2-\frac{59}{60}.          \tag{27}
\]

The right main inset has horizontal adjusted gap below p+alpha<1/2,
so its horizontal coordinate axis and every non-upward P axis fail.
Its only remaining separators are the vertical coordinate axis,
n=(b,a), and m=(-a,b). Section 5 excludes both P-owned choices,
using the same S,V and the same main squares. We retain the vertical
case. It gives
\[
                            y_2<f-G.                    \tag{28}
\]

#### 6.3. The sharpened unary theorem forces a strict lower scalar bound

Put
\[
                   L=t(k-p+\alpha),\qquad \delta=2f+L.
\]
We first record the useful uniform estimate
\[
                              L<\frac{121}{1000}.        \tag{29}
\]
Since p>=0, it suffices to bound tk+t/60. With
d=sqrt(1+t^2), the positive squared comparison
5d^2-(2+t)^2=(2t-1)^2 gives sqrt(5)d>=2+t, while
sqrt(5)<161/72 has squared reserve 1/5184. It follows that
\[
 tk+\frac t{60}
 \le\frac{829t-793t^2}{720(2+t)}<\frac{121}{1000}.
\]
The last comparison is exactly
\[
 19825t^2-18547t+4356>0,
\]
whose discriminant is -1439591. Thus (29) covers the whole actual
orientation interval without subdividing it.

Equations (26),(29),f<=1/10 give
\[
 y_1<\frac{221}{1000}-G=-\frac{8149}{31000}.
\]
Since y2<y1, (27) and the own-side clearance for S put both lower
centers below -97/100-8149/31000. Their absolute vertical center gap
is less than
\[
 \rho-\frac{97}{100}-\frac{8149}{31000}
       =\frac{26393}{93000}<\frac27.
\]
The disjoint incircles therefore force their horizontal gap to exceed
67/70, because
\[
                   (67/70)^2+(2/7)^2=4889/4900<1.
\]
Apply the sharpened unary theorem to S and V after reflection:
\[
 -x_S-2y_1<239/200,\qquad x_V-2y_2<239/200.
\]
Thus
\[
 \frac{67}{70}<x_V-x_S<
       \frac{239}{100}+2(y_1+y_2),
 \qquad y_1+y_2>-\frac{1003}{1400}.
\]
Combining this with (26),(28) proves the strict lower bound
\[
 \boxed{\quad
 \delta>\frac{30}{31}-\frac{1003}{1400}
       =\frac{10907}{43400}
       =\frac14+\frac{57}{43400}.\quad}                  \tag{30}
\]
This step uses both lower original squares. They have not been dropped
when the upper support inequalities are introduced.

#### 6.4. All actual upper separators reduce to one nonnegative scalar slope

Put
\[
 \lambda=\frac{29}{27},\quad \mu=\frac{32}{27},\quad
 d_0=\frac{61}{60},\quad
 \ell(z)=\frac{29}{2}z+\frac32\min(0,\max(-1,z)).
\]
For the one retained P define
\[
 J_L(s)=H_P((-1,s))+sY-\frac{\ell(s)}{27/2},\qquad
 J_R(z)=H_P((1,z))+zY-\frac{\ell(z)}{27/2}.
\]
The actual H/P and P/R separating normals have respectively negative
and positive horizontal components: both pairs have vertical center
gap less than rho-3/5<1, while their original support sums in a unit
direction are at least one. Dividing by the nonzero horizontal
component gives genuine finite slopes s,z in the indicated directions.

Apply the two reviewed outer envelopes to E_left,H and E_right,R,
and use these same original H/P and P/R separators. Their xP terms
cancel, giving
\[
 46D+\frac{27}{2}\{J_L(s)+J_R(z)\}\le\frac{211}{2}.
\]
Since D>=2,
\[
                          J_L(s)+J_R(z)\le1.             \tag{31}
\]
Every owner of both genuine separators is included.

The exact P support in its forced frame is
\[
 H_P((-1,s))=
 \begin{cases}
  -k-hs,&s\le-1/t,\\
  h-ks,&-1/t\le s\le t,\\
  k+hs,&s\ge t,
 \end{cases}
\]
and
\[
 H_P((1,z))=
 \begin{cases}
  k-hz,&z\le-t,\\
  h+kz,&-t\le z\le1/t,\\
  -k+hz,&z\ge1/t.
 \end{cases}
\]
Here b+f<lambda, a+f<mu, f<lambda, and
Y+h>193/300+1/2>lambda. Reading all intervals, including the
two breaks -1 and 0 of ell, proves
\[
 J_L(s)\ge h+t(b+f-\lambda)\quad(s\in\mathbb R),          \tag{32}
\]
\[
 J_R(z)\ge h\quad(z\le0),\qquad
 J_R(z)=h+z(a+f-\lambda)\quad(0\le z\le1/t).             \tag{33}
\]
For (32), the global minimum is at s=t. On each negative interval
the minimum is at an endpoint and is at least h; the interval from
0 to t decreases, and the interval beyond t increases.
For (33), the negative-interval slopes have the same asserted signs
because a+f<mu and f<lambda.

No genuine positive right separator can have z>=1/t. From (26) and
y1>-17/50,
\[
 n\cdot c_P>\frac12-\alpha b
             +a\left(G-\frac{17}{50}\right)>\frac7{12}.
\]
For the final comparison use a>7/10, b<3/4, and
G-17/50>7/50; the resulting lower bound 1171/2000 exceeds 7/12.
At z=1/t the normalized direction is n, so
\[
 \frac{(1,z)\cdot c_P+H_P((1,z))}{\sqrt{1+z^2}}
        =n\cdot c_P+\frac12>\frac{13}{12}>d_0.
\]
For z>=1/t, the left expression equals
\[
 \frac{-p-k+(Y+h)z}{\sqrt{1+z^2}},
\]
which increases, with derivative
[(Y+h)+(p+k)z]/(1+z^2)^(3/2)>0.
But any genuine right separator must satisfy the strict physical bound
\[
 (1,z)\cdot c_P+H_P((1,z))
                  <d_0\sqrt{1+z^2}:                    \tag{34}
\]
the original R center has norm<rho and its support is at least one
half times the direction length. This proves the exclusion.

If the genuine right slope is nonpositive, set a new scalar z=0
only in the following inequalities, using (33). No new geometric
separator is asserted. At this scalar value (34)'s weakened form
h-p<d0 holds directly, since h<=1/sqrt(2). Otherwise retain the
genuine positive slope, which lies in [0,1/t).
Equations (31)--(34) therefore imply that some scalar
0<=z<1/t satisfies
\[
 2h+t(b+f-\lambda)+z(a+f-\lambda)\le1,                  \tag{35}
\]
\[
                    h-p+(a+f)z<d_0\sqrt{1+z^2}.        \tag{36}
\]
The original P frame and all original pair constraints remain fixed.

#### 6.5. Exact elimination of p and f

Write
\[
 d=\sqrt{1+t^2}=\frac1a,\quad w=d-1,\quad
 \varepsilon=\lambda-a-f,\quad H_0=h-p.
\]
Since 2h=a+b and a+tb=d, (35) is exactly
\[
                w\le(t+z)\varepsilon.
\]
In particular epsilon>0, and epsilon>=w/(t+z).
Also (36) is
\[
                H_0+(\lambda-\varepsilon)z
                        <d_0\sqrt{1+z^2}.
\]
The scalar from (30) has the identity
\[
 \delta=2\lambda-a-d+\alpha t-2\varepsilon+tH_0.
\]
Consequently
\[
 \begin{aligned}
 \delta
 &<2\lambda-a-d+\alpha t+t d_0\sqrt{1+z^2}
                  -t\lambda z-(2-tz)\varepsilon\\
 &\le F(t,z),
 \end{aligned}
\]
where
\[
 \boxed{\quad
 F(t,z)=2\lambda-a-d+\alpha t+t d_0\sqrt{1+z^2}
       -t\lambda z-\frac{(d-1)(2-tz)}{t+z}.
 \quad}                                                \tag{37}
\]
The coefficient 2-tz is positive because z<1/t. Thus the exact
remaining scalar task is
\[
 F(t,z)\le\frac14
       \quad(0<t\le1,\ 0\le z<1/t).                    \tag{38}
\]
Appendix I proves (38) on its entire domain. Equations (30) and (37)
are therefore contradictory, closing the whole negative bad-P branch.

### 7. Analytic removal of the scalar tail z>=3/4

For completeness this section proves, by hand, that the remaining
scalar task (38) only needs 0<=z<=3/4. Continue to use (37).
Differentiation gives
\[
 \frac{F_z(t,z)}t
 =d_0\frac z{\sqrt{1+z^2}}-\lambda+
   g(t,z),\qquad
 g(t,z)=\frac{t(t^2+2)}{(d+1)(t+z)^2}.
\]
For fixed z>=1/2, the function g increases on 0<t<=1.
Indeed
\[
 \frac{g_t}g=
 \frac1{td}+\frac{2t}{t^2+2}-\frac2{t+z}.
\]
It suffices to check z=1/2. After positive multiplication its
numerator is
\[
 2t^3+t^2+4t+2+(2t^2-8t)d
 \ge(1-t)^2(t^2+2)\ge0,
\]
where d<=1+t^2/2 and 2t^2-8t<0 were used. Hence
\[
 g(t,z)\le\frac{3(\sqrt2-1)}{(1+z)^2}
             <\frac5{4(1+z)^2}.
\]
It remains to show
\[
 A(z):=d_0\frac z{\sqrt{1+z^2}}+
             \frac5{4(1+z)^2}<\lambda\quad(z\ge3/4).     \tag{39}
\]

On [3/4,1], (1+z)/sqrt(1+z^2)>=7/5, so A'(z)>0.
Thus
\[
 A(z)\le A(1)<\frac{61}{84}+\frac5{16}
          =\frac{349}{336}<\lambda.
\]

For z>=1, put
\[
 B(z)=d_0-\frac{d_0}{2(1+z^2)}+\frac5{4(1+z)^2}.
\]
The inequality sqrt(1-u)<=1-u/2 gives A<=B.
The function B decreases. Indeed
\[
 \frac{z(1+z)^3}{(1+z^2)^2}
 \le\frac{2z(1+z)}{1+z^2}<\frac{29}{12},
\]
using (1+z)^2<=2(1+z^2) and the positive quadratic
5z^2-24z+29>0. Therefore
\[
 2d_0\frac{z(1+z)^3}{(1+z^2)^2}
 <\frac{1769}{360}<5,
\]
which is precisely the sign B'(z)<0.

On [1,2], use the stronger positive-squaring inequality
sqrt(1-u)<=1-u/2-u^2/8, for 0<=u<=1.
The squared reserve is u^3/8+u^4/64 and the right side is positive.
It gives
\[
 A(z)\le B(z)-\frac{d_0}{8(1+z^2)^2}
       <B(1)-\frac1{200}
       =\frac{107}{100}<\lambda.
\]
For z>=2,
\[
 A(z)\le B(z)\le B(2)=\frac{1897}{1800}<\lambda.
\]
These three intervals prove (39), and hence F_z<0 for z>=3/4.
The tail is bounded by its endpoint at z=3/4, without any additional
orientation or parameter restriction.

Appendix I proves (38) on the compact rectangle 0<t<=1,
0<=z<=3/4 by two overlapping t ranges. Together with this decreasing
tail, it supplies the complete scalar upper bound used in Section 6.


<a id="appendix-g"></a>

## Appendix G. The positive-central reduction and first forced direction

Complete hand argument, independently reviewed, 6 November 2026. This text proves the common
positive-P reduction and the complete physical Case A. Case B remains
with its unchanged original predicate for Appendix H; this
appendix joins Appendix H to close both positive-P physical directions.

No mathematical script, numerical search, interval certificate, Lean
build, or CI is used. Every square frame and pair in the fixed nine-square
domain remains the original physical one.

Put
\[
 Q=\frac{1105}{256},\quad \rho=\frac{91}{60},\quad
 l=\frac{29}{60},\quad u=\frac{13}{12},\quad
 G=\frac{15}{31},\quad \alpha=\frac1{60},\quad
 C=G-\frac{17}{50}=\frac{223}{1550}>\frac7{50}.
 \tag{0}
\]

### 1. Exact use in the fixed (2,2,1) domain

The full-side inner main M1 is in its middle position. The proved
one-sided physical main-height theorem gives y1>-17/50. The present
branch has the selected central P=(p,Y) above both inner mains, with
p>0 and bad whole floor Y-h<=1/10. The original selected right endpoint
R=(s,z) is the unique right-side outsider and is high, z>=3/5.

The designated cone edge P<R gives
\[
 s-p\ge |z-Y|,\qquad s-p\ge g_P+g_R\ge\frac1{\sqrt2}.
 \tag{1}
\]
The second inequality follows from the physical disjointness of their
contained aligned insets. The outsider strip gives s<u and |p|<23/60.
All remaining originals, including the other central square, remain in
the domain. No premise is added concerning their frames or contacts.

The boundary p=0 belongs to the nonpositive-P branch of the integrated
manuscript. The local small-center theorem below also includes that
boundary, so its center-height reduction loses no endpoint.

The actual-four main localization provides
\[
 \begin{gathered}
 -\frac{31}{60}<x_1<-l,\quad
 \frac12\le h_1<\frac{31}{60},\quad
 x_1-h_1>-\frac{61}{60},\\
 g_1=\frac1{4h_1}>G,\quad x_1+g_1>-\alpha,\\
 a_1>\frac{999}{1000},\quad
 0\le b_1<\frac7{200},\quad
 h_1=\frac{a_1+b_1}{2},\quad
 k_1=\frac{a_1-b_1}{2}=\sqrt{\frac12-h_1^2}.
 \end{gathered}
 \tag{2}
\]
Here a1,b1 are the absolute components of the actual M1 frame. These
are correlated bounds about that same original main.

### 2. Physical clearance for the small positive center range

**Local theorem.** Under (2) and y1>-17/50, no original physical unit
P disjoint from M1 can satisfy
\[
 0\le X\le\frac{13}{60},\qquad y_1<Y\le\frac35.
 \tag{3}
\]
No P floor condition or cone edge is needed for this local statement.

Put d=X-x1 and v=Y-y1. Then
\[
 0<d<\frac{11}{15},\qquad 0<v<\frac{47}{50}.
 \tag{4}
\]
Every M1-owned unit side normal has center projection at most one of
d+b1 v and v+b1 d. Both are less than one:
\[
 \frac{11}{15}+\frac7{200}\frac{47}{50}<1,\qquad
 \frac{47}{50}+\frac7{200}\frac{11}{15}<1.
\]
The two original support halfwidths sum to at least one, so all
M1-owned axes fail, including both signs and both original chiralities.

A P-owned directed unit normal with a nonpositive coordinate also has
center projection less than one by (4). Thus any remaining physical
separator must be a P-owned unit normal n=(s,t) with s,t>0 and
s²+t²=1.

For every such direction the same original main has the support bound
\[
 H_{M_1}(s,t)\ge h_1\min(s,t)+k_1\max(s,t).
 \tag{5}
\]
This includes all absolute-projection regimes. For example, when t>=s,
one original chirality has support at least k1 s+h1 t, which is at
least h1 s+k1 t. For the other chirality the support is either exactly
h1 s+k1 t or exceeds it by b1 t-a1 s>=0. Interchanging s,t proves
the other half. This verifies (5) directly for both physical frames.

#### 2.1. The range t>=s

The P-owned separator would require
\[
 s(d-h_1)+t(v-k_1)\ge\frac12.
 \tag{6}
\]
The correlated x1/h1 bound in (2) and (3) give
\[
 d-h_1<X+\frac{61}{60}-2h_1
       \le A(h_1):=\frac{37}{30}-2h_1,\qquad
 v-k_1<B(h_1):=\frac{47}{50}-\sqrt{\frac12-h_1^2}.
 \tag{7}
\]
Both A and B are positive on [1/2,31/60]. A is affine and B is
positive and convex, so A²+B² is convex and its maximum is at an
endpoint of this closed interval.

At h1=1/2,
\[
 A^2+B^2=\left(\frac7{30}\right)^2+
          \left(\frac{11}{25}\right)^2
       =\frac14-\frac{11}{5625}.
 \tag{8}
\]
At h1=31/60, the exact comparison
\[
 k_1^2-\left(\frac{193}{400}\right)^2
   =\frac{359}{1440000}>0
\]
gives
\[
 A^2+B^2<
 \left(\frac15\right)^2+\left(\frac{183}{400}\right)^2
 =\frac14-\frac{111}{160000}.
 \tag{9}
\]
Consequently Cauchy--Schwarz makes the left side of (6) strictly
less than one half. This case is impossible.

#### 2.2. The range s>=t

Now the necessary P-owned inequality is
\[
 s(d-k_1)+t(v-h_1)\ge\frac12.
\]
The same main obeys
\[
 \begin{aligned}
 d-k_1
 &<X+\frac{61}{60}-(h_1+k_1)
 \le\frac{37}{30}-a_1
 <\frac{703}{3000}<\frac{47}{200},\\
 v-h_1&<\frac{11}{25}.
 \end{aligned}
 \tag{10}
\]
The last comparison in the first line has margin 1/1500. Therefore
\[
 \left(\frac{47}{200}\right)^2+
 \left(\frac{11}{25}\right)^2
 =\frac14-\frac{47}{40000}<\frac14.
\]
Cauchy--Schwarz excludes this case as well. All original separating
axes have failed, proving the complete local theorem (3).

### 3. The shared reduction Y>3/5 and 0<p<1/5

Suppose first Y<=3/5 in the positive branch of Section 1.

If p<=13/60, Section 2 applies directly to the unchanged M1 and P.
If p>13/60, (1) gives s>11/12. The standard right endpoint contains
the fixed aligned rectangle
\[
 [A,B]\times[-c,c],\qquad
 A=\frac{503}{480},\quad B=\frac{937}{480},\quad
 c=\frac{221}{600}.
 \tag{11}
\]
Because z>=3/5>c and 11/12<s<u<B, the disk of radius one half
inside R gives
\[
 z>c+\sqrt{\frac14-(21/160)^2}>\frac{17}{20}.
 \tag{12}
\]
The final squared reserve is 4439/5760000. Reflect horizontally.
The unchanged original M1 becomes the right main in the proved
low-central-cone-endpoint lemma in Appendix D, P has center (-p,Y) with
13/60<p<23/60, and the unchanged original R is the far-left
selected endpoint. Its height satisfies (12), its center lies in
11/12<-x_R'<u, and the original cone edge gives the required order.
The main has height greater than -17/50. Every local hypothesis
is therefore satisfied, and that hand lemma is a contradiction.

This proves Y>3/5, including the p=13/60 boundary through Section 2.

Next, a high central original of bad floor in the presence of a high
right-side original has p<1/5. Here is the complete disk argument.
If p>=1/5, then 3/5<Y<97/120. If R is below P, their squared
center distance is below (53/60)²+(5/24)²<1. If R is above P,
that distance is at most
\[
 (s-1/5)^2+
 \left(\sqrt{\rho^2-s^2}-3/5\right)^2,\qquad l\le s\le u.
\]
This is convex in s after expansion. Its endpoint bounds are
\[
 (17/60)^2+(21/25)^2<1,\qquad
 (53/60)^2+(37/80)^2=1-\frac{67}{11520}<1,
\]
using sqrt(rho²-l²)<36/25 and sqrt(rho²-u²)<17/16.
All center orders contradict the two original half-unit disks.

The full surviving positive-P predicate consequently has
\[
 \boxed{\quad 0<p<\frac15,\qquad
           \frac35<Y\le h+\frac1{10}<\frac{97}{120}.\quad}
 \tag{13}
\]

### 4. The actual M1 inset forces one of two P frames

Fold the unchanged P frame to a>=b>=0, a²+b²=1,
h=(a+b)/2 and k=(a-b)/2. Put
\[
 d_0=p-x_1>0,\quad v_0=Y-y_1>0,\quad
 c_0=y_1+g_1-(Y-h)>C-\frac1{10}>0.
\]
The correlated residuals satisfy
\[
 d_0-g_1<p+\alpha<\frac{13}{60}<h,\qquad
 v_0-g_1=h-c_0<h.
 \tag{14}
\]
Both coordinate axes fail. A P side normal with nonpositive vertical
component has adjusted projection less than one half and fails.

Both upward-left P side forms fail as well. For (-a,b), the adjusted
projection is less than bh<=1/2. For (-b,a), it is less than
\[
 ah-b(d_0+g_1)-ac_0
 =\frac12+b(k-d_0-g_1)-ac_0<\frac12,
\]
since d0+g1>l+G>1/2>=k. Thus an aligned P is impossible, b>0,
and an actual P side normal directed from M1 to P is one of

\[
 \begin{array}{c|c|c}
 &\text{normal }n&\text{other original side direction }q\\ \hline
 {\rm A}&(a,b)&(-b,a)\\
 {\rm B}&(b,a)&(-a,b).
 \end{array}
 \tag{15}
\]

Their necessary original center inequalities are, respectively,
\[
 n\cdot c_P>\frac12-a\alpha+bC\quad({\rm A}),\qquad
 n\cdot c_P>\frac12-b\alpha+aC\quad({\rm B}).
 \tag{16}
\]
No physical frame has been chosen independently for a later pair.
The rest of this appendix closes Case A completely. Case B retains
all of Sections 1--4 for the separate argument.

### 5. Case A: exact projection and profile bounds

Assume n=(a,b), q=(-b,a). Its separator in (14) implies
\[
 a(p+\alpha-k)>bc_0>0,\qquad
 k<p+\alpha<\frac{13}{60}.
 \tag{17}
\]
In particular
\[
 b>\frac9{20},\qquad a<\frac9{10}.
 \tag{18}
\]
Indeed k decreases with b on [0,1/sqrt(2)]; at b=9/20 the
comparison a>53/60 follows from the squared reserve 31/1800,
and gives k>13/60, contrary to (17).

Let the original R center be (s,z), and define
\[
 d=s-p,\quad w=z-Y,\quad
 N=a d+b w,\quad J=-b d+a w.
 \tag{19}
\]
The original cone edge gives |w|<=d and d>=1/sqrt(2).

Write s0=p+1/sqrt(2). The R center lies in the following larger
closed profile region:
\[
 s_0\le s\le u,\qquad L(s)\le z\le U(s),
 \tag{20}
\]
where
\[
 L(s)=c+\sqrt{\frac14-(A-s)_+^2},\qquad
 U(s)=\sqrt{\rho^2-s^2},
 \tag{21}
\]
and A,c are those in (11). Equation (21)'s lower bound is exactly
the distance condition from R's half-unit disk to the fixed original
endpoint rectangle. The upper bound is the universal center bound,
weakened to its closed rho-disk.

Every point in the entire enlarged profile region (20), not only the
original R, satisfies
\[
 z>\frac{11}{15},\qquad w>-\frac3{40}.
 \tag{22}
\]
For a printed radical check, 1/sqrt(2)>707/1000, so
(A-s)_+<4091/12000, and
\[
 \frac14-\left(\frac{4091}{12000}\right)^2
          -\left(\frac{73}{200}\right)^2
 =\frac{79319}{144000000}>0.
\]
Thus L(s)>c+73/200=11/15. Combine this with Y<97/120
to obtain the second inequality.

The following bounds also hold throughout (20):
\[
 0<N<\frac{97}{100},\qquad -J<\frac{22}{25}.
 \tag{23}
\]
For the lower bound, a>=1/sqrt(2), d>=1/sqrt(2), b<3/4
and (22) give N>1/2-9/160=71/160>0. For the upper bound,
use the same original P inequality (16) and |(s,z)|<=rho:
\[
 N<\frac{61}{60}+\frac a{60}-bC
  <\frac{61}{60}+\frac3{200}-\frac{63}{1000}
  =\frac{1453}{1500}<\frac{97}{100}.
\]
Finally
\[
 -J=b(s-p)-a(z-Y)
 <bu+\frac{3a}{40}
 <\frac{13}{16}+\frac{27}{400}=\frac{22}{25}.
\]

For the actual original R, the cone comparison additionally gives
\[
 J\le(a-b)d<2(p+\alpha)(u-p)
 \le\frac{689}{1800}<\frac12.
 \tag{24}
\]
The last quadratic increases for 0<=p<=1/5, so its displayed
maximum is at p=1/5. Only (24), not the bounds in (23), uses
the cone after (20) has been formed.

### 6. The only possible rounded-corner region

In P's one actual orthonormal frame, the exact squared distance is
\[
 \operatorname{dist}((s,z),P)^2
 =(|N|-1/2)_+^2+(|J|-1/2)_+^2.
 \tag{25}
\]
For the original R, equations (23)--(24) show that this squared distance
is less than 1/4 unless
\[
 N>\frac12,\qquad J<-\frac12.
 \tag{26}
\]
Indeed N<=1/2 leaves only (-J-1/2)_+<19/50, while
J>=-1/2 leaves only (N-1/2)_+<47/100.

In (26) the closest point of P is its unchanged physical corner
\[
 K=c_P+\frac{n-q}{2}=(p+h,Y-k).
 \tag{27}
\]
Its vertical coordinate satisfies
\[
 K_y=Y-k>\frac35-\frac{13}{60}
       =\frac{23}{60}>c.
 \tag{28}
\]
The distance squared is therefore exactly F(s,z)=|(s,z)-K|².

We may now drop the cone inequalities and use the compact relaxation
\[
 \mathcal D=\{(s,z):s_0\le s\le u,\ L(s)\le z\le U(s),
                         \ N\ge1/2,\ J\le-1/2\}.
 \tag{29}
\]
This is a genuine enlargement of the surviving original region.
Equations (23) continue to hold throughout it: their proof used only
(20) and the fixed physical P frame. The extra bound J<1/2 is
automatic from the explicit guard J<=-1/2 in (29), so it does not
silently retain a dropped cone assumption.

On the two closed wedge faces of (29) we immediately have
\[
 \begin{array}{c|c}
 N=1/2&F=(J+1/2)^2<(19/50)^2<1/4\\
 J=-1/2&F=(N-1/2)^2<(47/100)^2<1/4.
 \end{array}
 \tag{30}
\]

### 7. A rigorous reduction to the two vertical edges

If D is empty there is nothing left to prove. Otherwise F attains
a maximum on this compact set. It cannot have a maximum in its
interior, since F is a strictly convex quadratic.

The two horizontal-profile boundaries cannot contain a maximum away
from a vertical edge or a wedge face. To verify this without assuming
that D itself is convex, restrict F to each boundary curve.

On the upper circle,
\[
 F(s,U(s))=\rho^2+|K|^2-2K_xs-2K_y\sqrt{\rho^2-s^2},
\]
which is strictly convex in s because K_y>0.

For s<=A the lower boundary expansion is
\[
 \begin{aligned}
 F(s,L(s))={}&
 2(A-K_x)s+K_x^2-A^2+(c-K_y)^2+\frac14\\
 &-2(K_y-c)\sqrt{\frac14-(A-s)^2}.
 \end{aligned}
 \tag{31}
\]
It is strictly convex by (28). For s>=A, L(s)=c+1/2 and
F(s,L(s)) is a strictly convex quadratic in s. Their first derivatives
agree at A, both being 2(A-K_x), so the joined lower-boundary
function is strictly convex across the breakpoint as well.

There is no upper/lower boundary intersection: throughout [s0,u],
\[
 L(s)\le\frac{521}{600}<\frac{53}{50}<U(u)\le U(s),
\]
where U(u)²-(53/50)²=23/7500>0.

Consequently, if a maximizing point on a profile curve is on neither
a wedge face nor a vertical edge, all remaining guards are strict in
a neighborhood along that curve. A small two-sided parameter interval
therefore belongs to D. Strict convexity on that interval supplies a
point with larger F, a contradiction. This also treats s=A because
of the matching-derivative argument above.

Every maximum thus occurs on a closed wedge face or one of the two
vertical edges s=s0,u. The wedge faces were handled in (30).
No separate lower-profile breakpoint estimate is required.

### 8. The left vertical edge

At s=s0, d=1/sqrt(2). Equations (18),(22) give
\[
 -J<\frac b{\sqrt2}+\frac{3a}{40}
    <\frac12+\frac{27}{400}=\frac{227}{400}.
\]
Together with N<97/100, every point of this edge in D has
\[
 F=(N-1/2)^2+(J+1/2)^2
 <\left(\frac{47}{100}\right)^2+
  \left(\frac{27}{400}\right)^2
 =\frac{36073}{160000}
 =\frac14-\frac{3927}{160000}.
 \tag{32}
\]
This includes the closed left-edge endpoints and any wedge intersections.

### 9. The right vertical edge

At s=u, the allowed z values in D form a closed interval, or the
empty set, because the two wedge guards are linear in z. F(u,z) is
convex in z, so it is enough to check the endpoints of this interval.
An endpoint on a wedge face is already covered by (30). The only
other possibilities are the two original profile endpoints
\[
 z_-=\frac{521}{600},\qquad z_+=\sqrt{\frac{169}{150}}.
\]
The estimates below are needed only when the endpoint belongs to D;
thus N>=1/2 and J<=-1/2 are retained when squaring the gaps.

#### 9.1. The lower profile endpoint

Using (16),
\[
 N<\frac{11}{10}a+(z_--C)b-\frac12
  <\frac{11}{10}a+\frac{29}{40}b-\frac12
  <\frac{33}{40}.
 \tag{33}
\]
The coefficient difference is exactly C-43/300=1/1860>0.
For the final Cauchy comparison the squared reserve is
\[
 (53/40)^2-(11/10)^2-(29/40)^2=\frac1{50}>0.
\]
Also z_--Y>3/50, so
\[
 -J<bu-\frac{3a}{50}
 \le b(u-3/50)
 \le\frac{u-3/50}{\sqrt2}<\frac34.
 \tag{34}
\]
For example sqrt(2)>7/5 makes the last expression less than
307/420<3/4. Thus this endpoint, when it belongs to D, satisfies
\[
 F<\left(\frac{13}{40}\right)^2+\left(\frac14\right)^2
   =\frac{269}{1600}<\frac14.
 \tag{35}
\]

#### 9.2. The upper circle endpoint

Here 53/50<z_+<17/16, with squared reserves 23/7500 and
43/19200 respectively. Hence
\[
 N<\frac{11}{10}a+(17/16-C)b-\frac12
  <\frac{11}{10}a+\frac{93}{100}b-\frac12
  <\frac{19}{20},
 \tag{36}
\]
because
\[
 (29/20)^2-(11/10)^2-(93/100)^2=\frac{69}{2500}>0.
\]
The height bounds give z_+-Y>53/50-97/120>1/4. Consequently
\[
 -J<bu-\frac a4
 \le b(u-1/4)\le\frac5{6\sqrt2}<\frac35.
 \tag{37}
\]
The final squared comparison is 625<648. Therefore this endpoint,
when it belongs to D, has
\[
 F<\left(\frac9{20}\right)^2+\left(\frac1{10}\right)^2
   =\frac{17}{80}<\frac14.
 \tag{38}
\]

This completes the right-edge interval, including every closed profile
and wedge boundary.

### 10. Case A contradiction and retained complement

Sections 7--9 and (30) show F<1/4 throughout the compact relaxation D.
Equation (25) and the preliminary alternatives then give
\[
 \operatorname{dist}(c_R,P)<\frac12
\]
for the actual original R in every Case A configuration.

The open disk of radius one half centered at R belongs to the interior
of that original square. Its distance less than one half to the closed
square P implies an interior intersection with P as well: a nearby
interior point of P still has distance less than one half. This contradicts
the original pairwise interior nonoverlap.

Thus Case A is completely excluded. The unchanged Case B predicate
of (15)--(16), together with all common positive-P reductions and every
original constraint in the fixed nine-square domain, remains for the
separate argument. No conclusion about that complement is asserted here.

<a id="appendix-h"></a>

## Appendix H. The positive central's second forced direction

6 November 2026. Complete hand argument, independently reviewed and
integrated into the fixed target manuscript. This is one exhaustive remaining
physical alternative in that fixed all-nine proof, not a new research
domain or a claim of unrestricted closure. No mathematical program,
numerical search, certificate replay, Lean build, or CI is a premise.

### 1. Exact case supplied by the common positive-P reduction

Retain all nine originals and every corner and pair condition of the
fixed (2,2,1) target. Work after a sufficiently small common center
expansion that preserves the original occupancy, stays below the target
radius, and makes the actual main endpoint span D>2.

The full-left main is in its middle position. The selected outsider
triple is H<P<R, with the central P above both inner mains and the
other central original below both. The high-right branch has y_R>=3/5.
The common positive-P reduction has already proved

\[
 0<p:=x_P<\frac15,\qquad Y:=y_P>\frac35,\qquad
 f:=Y-h\le\frac1{10},\qquad y_1>-\frac{17}{50}.
\tag{B1}
\]

The original high left shoulder satisfies y_H>63/100. Both shoulders
are in their usual side columns. The consecutive selected comparisons
are center-cone comparisons, and in particular x_H<p<x_R. No selected
edge is assumed to be an actual projection separation.

Write the absolute components of P's one actual frame as a>=b>0,
a²+b²=1. Its coordinate halfwidth and complementary corner offset are

\[
 h=\frac{a+b}{2},\qquad k=\frac{a-b}{2},\qquad
 t=\frac ba\in(0,1],\qquad d=\sqrt{1+t^2}=\frac1a.
\tag{B2}
\]

In the present case B, P's actual upward-right side direction separating
it from the left main's actual inset is

\[
                       n=(b,a),
\]

and its other actual direction is m=(a,-b). This is the only additional
case hypothesis. The common proof covers the other direction separately.

Put

\[
 \alpha=\frac1{60},\qquad
 C=\frac{15}{31}-\frac{17}{50}=\frac{223}{1550},\qquad
 \lambda=\frac{29}{27},\qquad
 \beta=\frac{451}{810},\qquad d_0=\frac{61}{60}.
\tag{B3}
\]

The two coordinates of P's actual upper-right corner will be useful:

\[
                         u=p+h,\qquad v=Y+k=a+f.
\tag{B4}
\]

The proof below excludes all of case B. It does not require a further
placement or separator restriction on the lower side original or the
lower central original, which remain among the retained nine squares.

### 2. The forced left direction gives one exact linear inequality

Let g_1 be the halfwidth of the aligned inset inside the original M_1.
The actual-four localization and (B1) give

\[
 x_1+g_1>-\alpha,\qquad y_1+g_1>C.
\]

The original n separator therefore implies

\[
 b p+aY>\frac12-b\alpha+aC.
\tag{B5}
\]

Dividing by a gives Y+t p>d/2+C-alpha t. The exact identity

\[
                         k+t h=\frac d2
\]

then proves

\[
 \boxed{\qquad v+t u>d+C-\alpha t.\qquad}
\tag{B6}
\]

The same P frame is used in (B5), (B6), and every support calculation
below. In particular its chirality has not been optimized independently
for different pairs.

### 3. Original outer inequalities and physical right-side inequalities

Use the already proved [outer envelopes](FIVE_SQUARE_CAP_OUTER.md) with

\[
 A_{\rm cap}=46,\qquad B_{\rm cap}=\frac{27}{2},\qquad
 T_{\rm cap}=\frac{211}{4},
\]
\[
 \ell(z)=\frac{29}{2}z+\frac32\min(0,\max(-1,z)).
\]

Let a_L=-x_0-h_0 and a_R=x_3-h_3 be the two actual main endpoint
inward edges. They satisfy

\[
 a_L+a_R=D>2,\qquad a_L,a_R>\frac{59}{60}.
\tag{B7}
\]

For the latter, each inward edge is less than rho-1/2=61/60
and their sum exceeds two.

All three centers H,P,R have height at least 3/5 and below
rho=91/60. Each relevant vertical center difference consequently
has magnitude below 11/12<1. Because x_H<p<x_R, every genuine
directed separating normal from P to H has negative horizontal
component, and every such normal from P to R has positive horizontal
component. Otherwise its directed center projection would be less
than one, while the two original half-unit disks require support
sum at least one.

Normalize genuine separators to (-1,z_L) and (1,z_R), respectively.
Define the following functions of the unchanged original P:

\[
 \begin{aligned}
 J_L(z)&=H_P((-1,z))+zY-\ell(z)/B_{\rm cap},\\
 J_R(z)&=H_P((1,z))+zY-\ell(z)/B_{\rm cap}.
 \end{aligned}
\tag{B8}
\]

The two original shoulder separators and their outer envelopes give

\[
 A_{\rm cap}a_L+B_{\rm cap}[-p+J_L(z_L)]\le T_{\rm cap},
\]
\[
 A_{\rm cap}a_R+B_{\rm cap}[p+J_R(z_R)]\le T_{\rm cap}.
\tag{B9}
\]

Consequently

\[
 A_{\rm cap}D+B_{\rm cap}[J_L(z_L)+J_R(z_R)]\le2T_{\rm cap}.
\tag{B10}
\]

Since 2T_cap-B_cap=2A_cap, any lower bound J_L+J_R>=1
already contradicts D>2. Separately, the right inequality in (B9)
and a_R>59/60 give the strict necessary condition

\[
                         p+J_R(z_R)<\beta.
\tag{B11}
\]

There is also a physical upper bound retaining R itself. Its center
norm is below rho, and its support in any vector w is at least |w|/2.
The genuine P/R separator therefore implies

\[
 p+z_RY+H_P((1,z_R))<d_0\sqrt{1+z_R^2}.
\tag{B12}
\]

This follows from R's original corner containment and incircle; it is
not an independently selectable proxy configuration.

### 4. The exact all-real support breaks of this P

For z>=0, the actual frame m=(a,-b), n=(b,a) gives

\[
 H_P((1,z))=
 \begin{cases}
 h+kz,&0\le z\le1/t,\\
 -k+hz,&z\ge1/t,
 \end{cases}
\tag{B13}
\]

and

\[
 H_P((-1,z))=
 \begin{cases}
 h-kz,&0\le z\le t,\\
 k+hz,&z\ge t.
 \end{cases}
\tag{B14}
\]

These formulas agree at their shared endpoints and include t=1.

#### 4.1. Negative right slopes never improve the value h

Write z=-s, s>=0. Because
ell(-s)/B_cap=-(32/27)s for 0<=s<=1, and
ell(-s)/B_cap=-lambda s-1/9 for s>=1, (B13)--(B14) give

\[
 J_R(-s)=
 \begin{cases}
 h+s(32/27-v),&0\le s\le t,\\
 k+s(32/27-f),&t\le s\le1,\\
 k+1/9+s(\lambda-f),&s\ge1.
 \end{cases}
\tag{B15}
\]

Every slope here is positive. Indeed
v=a+f<=11/10<32/27, and f<=1/10. The function is continuous
at the breaks. Therefore

\[
                           J_R(z)\ge h\quad(z\le0).
\tag{B16}
\]

#### 4.2. The left minimum and the easy corner-height case

For z>=0, (B14) gives slopes Y-k-lambda on [0,t] and
Y+h-lambda on [t,infinity). The former is negative, since
Y-k=b+f<3/4+1/10=17/20<lambda. The latter is positive,
since Y+h>11/10>lambda. Thus the nonnegative minimum is at z=t:

\[
                      J_L(t)=\frac d2+t(Y-\lambda).
\tag{B17}
\]

For negative left slopes z=-s, the successive slopes as s increases
through [0,1], [1,1/t], and [1/t,infinity) are

\[
              32/27-b-f,\qquad \lambda-b-f,\qquad \lambda-f.
\]

They are positive, since b<3/4 and f<=1/10. The function is
continuous at the breaks and starts at h. Thus (B17) is the
global all-real minimum of J_L.

If v>=lambda, (B13) and the positivity of Y+h-lambda also
show that J_R(z)>=h for z>=0. Together with (B16),

\[
 \begin{aligned}
 J_L(z_L)+J_R(z_R)
 &\ge h+\frac d2+t(Y-\lambda)\\
 &=d+t(v-\lambda)>1.
 \end{aligned}
\tag{B18}
\]

The identity h-tk=d/2 was used. Equation (B10) contradicts
D>2. The entire v>=lambda alternative, including equality,
is therefore closed.

We henceforth retain

\[
                              v<\lambda.
\tag{B19}
\]

### 5. Two short scalar ranges force the right-corner constraints

We prove from (B6) and p>0 that

\[
 \boxed{\qquad u>\beta,\qquad
             u+\frac35v>\beta+\frac35\lambda=\frac{973}{810}.
       \qquad}
\tag{B20}
\]

No physical alternative is discarded during this scalar split.

#### 5.1. Small tilt: 0<t<=1/8

Set

\[
                         F(t)=d+C-t(\beta+\alpha).
\]

On [0,1/8] it is strictly decreasing, because
F'(t)=t/d-(beta+alpha)<1/8-(beta+alpha)<0. At the right endpoint,

\[
 F(1/8)=\frac{\sqrt{65}}8+C-\frac{\beta+\alpha}{8}
                  >\lambda+\frac9{8000}.
\tag{B21}
\]

Here is a complete rational verification of that strict reserve:

\[
 \frac{\sqrt{65}}8>\frac{201}{200},\qquad
 C>\frac{143}{1000},\qquad
 \beta+\alpha=\frac{929}{1620}<\frac{23}{40},\qquad
 \lambda<\frac{43}{40}.
\]

The positive squared difference for the first comparison is
65/64-(201/200)^2=7/1250. The other three comparisons follow
by positive cross multiplication. Their resulting reserve is exactly

\[
 \frac{201}{200}+\frac{143}{1000}
      -\frac{23}{320}-\frac{43}{40}=\frac9{8000}>0.
\]

Equations (B6), (B21) give

\[
                       v+t(u-\beta)>\lambda.
\tag{B22}
\]

Because v<lambda, this forces u>beta. Writing U=u-beta>0,
(B22) also gives

\[
 u+\frac35v>
 \beta+\frac35\lambda+\left(1-\frac35t\right)U
 >\beta+\frac35\lambda.
\]

Both assertions of (B20) follow throughout the closed small-tilt
range.

#### 5.2. Larger tilt: 1/8<=t<=1

The function h(t)=(1+t)/(2sqrt(1+t^2)) is nondecreasing on
[0,1]. Hence

\[
 u=p+h>h(1/8)=\frac9{2\sqrt{65}}
             >\frac{24}{43}>\beta.
\tag{B23}
\]

We used sqrt(65)<129/16, whose squared comparison has reserve
1/256. The final rational difference is

\[
                         \frac{24}{43}-\beta=\frac{47}{34830}>0.
\]

Use (B6) to bound the second expression in (B20). Direct collection
of the same-frame h,k terms gives

\[
 \begin{aligned}
 u+\frac35v
 &>p\left(1-\frac35t\right)
      +N(t)+\frac35C,\\
 N(t)&=\frac{11+2t+3t^2}{10\sqrt{1+t^2}}-\frac t{100}.
 \end{aligned}
\tag{B24}
\]

We prove N(t)>223/200 on this whole interval. Its derivatives are

\[
 N'(t)=\frac{3t^3-5t+2}{10(1+t^2)^{3/2}}-\frac1{100},
 \qquad
 N''(t)=\frac{19t^2-6t-5}{10(1+t^2)^{5/2}}.
\]

Thus N is concave on [1/8,1/2]. On [1/2,1],

\[
              3t^3-5t+2=(t-1)(3t^2+3t-2)\le0,
\]

so N is strictly decreasing. Its minimum over [1/8,1] is
therefore at 1/8 or 1. Both endpoints have explicit strict bounds:

\[
 \begin{aligned}
 N(1/8)&=\frac{723}{80\sqrt{65}}-\frac1{800}
       >\frac{241}{215}-\frac1{800}
        =\frac{223}{200}+\frac{161}{34400},\\
 N(1)&=\frac{4\sqrt2}{5}-\frac1{100}
       >\frac{559}{500}
        =\frac{223}{200}+\frac3{1000}.
 \end{aligned}
\tag{B25}
\]

The first uses sqrt(65)<129/16 as above. The second uses
sqrt(2)>141/100, whose squared reserve is 119/10000.
Since p>0 and 1-3t/5>0, (B24)--(B25) give

\[
 u+\frac35v>
 \frac{223}{200}+\frac{669}{7750}
 =\frac{973}{810}+\frac{221}{2511000}.
\tag{B26}
\]

This proves the second assertion of (B20) and completes the entire
small/large tilt split. The common boundary t=1/8 is covered by
both arguments.

### 6. Exclude nonpositive and steep right separators

If the genuine right slope z_R is nonpositive, (B16) and (B20)
give p+J_R(z_R)>=p+h=u>beta, contradicting (B11).

Now suppose z_R>=1/t. At z=1/t, the left side of (B12),
after division by sqrt(1+z^2), is exactly n dot c_P+1/2.
Equation (B5) gives

\[
 n\cdot c_P+\frac12>1+aC-b\alpha>d_0.
\tag{B27}
\]

For completeness the last comparison is strict because b<=a,
a>=1/sqrt(2)>7/10, and C>7/50, so

\[
 aC-b\alpha\ge a(C-\alpha)>
 \frac7{10}\left(\frac7{50}-\frac1{60}\right)
 =\frac{259}{3000}>\frac1{60}=d_0-1.
\]

The physical inequality (B12) already fails at z=1/t.
For z>=1/t, its left-minus-right function is

\[
             \Psi(z)=p-k+z(Y+h)-d_0\sqrt{1+z^2}.
\]

It is strictly increasing, since

\[
 \Psi'(z)=Y+h-d_0\frac z{\sqrt{1+z^2}}
                 >\frac{11}{10}-d_0=\frac1{12}>0.
\]

Thus (B12) fails throughout this closed steep range as well.

Every surviving genuine right separator would therefore satisfy

\[
                              0<z_R<1/t.
\tag{B28}
\]

### 7. The remaining right slopes violate physical separation

In the interval (B28), (B13) turns the outer and physical conditions
into the simultaneous inequalities

\[
 u+z_R(v-\lambda)<\beta,\qquad
 u+v z_R<d_0\sqrt{1+z_R^2}.
\tag{B29}
\]

Since v<lambda and u>beta, the first forces

\[
 z_R>z_0:=\frac{u-\beta}{\lambda-v}.
\]

The second assertion of (B20) gives z_0>3/5. If z_0>=1/t,
there is no surviving slope at all. Otherwise define on [z_0,1/t]

\[
                  \Phi(z)=u+vz-d_0\sqrt{1+z^2}.
\]

At z_0 the exact defining identity gives

\[
                 u+vz_0=\beta+\lambda z_0.
\]

For every z>=3/5,

\[
                         \beta+\lambda z>d_0\sqrt{1+z^2}.
\tag{B30}
\]

Indeed the difference of squares
(\beta+\lambda z)^2-d_0^2(1+z^2) is strictly increasing on
z>=0 because lambda>d_0 and beta>0. At z=3/5, use

\[
 \beta>\frac{11}{20},\qquad
 \lambda>\frac{16}{15},\qquad d_0<\frac{51}{50}.
\]

The positive squared reserve is at least

\[
 \left(\frac{119}{100}\right)^2
       -\left(\frac{51}{50}\right)^2\frac{34}{25}
       =\frac{289}{250000}>0.
\]

All sides being squared are positive. This proves (B30), so
Phi(z_0)>0. Equation (B27) gives Phi(1/t)>0 as well.

But

\[
                         \Phi''(z)=-\frac{d_0}{(1+z^2)^{3/2}}<0.
\]

By concavity, Phi is positive throughout the interval joining those
two endpoints. It cannot satisfy the second inequality in (B29)
at any z_R between them. This excludes the final possible right
separator and completes the contradiction.

### 8. Exhaustive coverage and exact use in the (2,2,1) manuscript

The common reduction supplies Y>3/5, 0<p<1/5, and one of the
two actual upward-right directions of P against M_1. This argument
covers the complete B direction n=(b,a), including a=b. The aligned
case b=0 cannot satisfy Y>3/5 together with Y-h<=1/10 and h=1/2.

Within B, the alternatives v>=lambda and v<lambda are exhaustive.
The latter's tilt intervals cover (0,1], and its right-separator
intervals z<=0, z>=1/t, and 0<z<1/t cover all real slopes with
every shared endpoint included. Every physical owner is retained:
the right separator is never assumed to be P-owned, and its support
inequalities use the original R itself.

The only external hand inputs are the standard actual-four endpoint
localization, the proved outer envelopes, and physical support,
incircle, and separating-axis facts. The forced-left inequality uses
the original M_1 inset and its established one-sided middle-height
bound. No new lower-original restriction, isolated proxy choice,
numerical exclusion, or omitted guard is introduced.

Thus the complete positive bad-P case B is impossible in the fixed
all-nine (2,2,1) target. Together with the common positive-P reduction and the other actual
direction in Appendix G, it closes the complete positive-P branch.
Appendices F and I close the separately covered nonpositive branch.

<a id="appendix-i"></a>

## Appendix I. The final scalar upper bound and negative-central contradiction

Complete hand proof, 6 November 2026. Independent readings checked the
scalar reductions, all polynomial identities and rational coefficient
bounds, the derivative arguments, and every endpoint. The derivation uses
no mathematical program or external certificate.

With the constants and function F of Appendix F, equation (37), we prove
\[
          F(t,z)<\frac14\qquad(0<t\le1,\ 0\le z<1/t).
\]
The two compact rectangles below cover 0<=z<=3/4. The decreasing
tail from Appendix F covers all remaining z. The polynomial named P
is local to each part: Part I.1 uses the sign F_q−1/4 and Part I.2
uses the sign 1/4−F_q, with both definitions printed explicitly.

### I.1. The smaller-tilt rectangle

Put
\[
 \lambda=\frac{29}{27},\quad d_0=\frac{61}{60},\quad
 \alpha=\frac1{60},\quad d=\sqrt{1+t^2},\quad a=\frac1d,\quad w=d-1.
\]
The scalar retained by the physical negative-vertical reduction is
\[
 F(t,z)=2\lambda-a-d+\alpha t
       +t d_0\sqrt{1+z^2}-t\lambda z
       -\frac{w(2-tz)}{t+z}.
 \tag{1}
\]
We prove the strict bound
\[
 \boxed{\quad F(t,z)<\frac14
       \quad\text{for }0<t\le\frac34,\quad0\le z\le\frac34.\quad}
 \tag{2}
\]
Part I.2 proves the larger-t rectangle; Appendix F, Section 7, proves the
decreasing z tail. The symbols P, r, and the numbered equations in this
part are local to this smaller-tilt argument.

#### 1. One cubic and its four Bernstein coefficients

Positive squaring gives sqrt(1+z²)<=1+z²/2. Let F_q replace that
radical in (1) by its upper bound, so F<=F_q. Define
\[
 \begin{aligned}
 K&=\frac{205}{108}-d-\frac1d+\frac{31}{30}t,\\
 P(t,z)&=(t+z)\left(F_q(t,z)-\frac14\right)
       =A_0+A_1z+A_2z^2+A_3z^3,\\
 A_0&=tK-2w,\\
 A_1&=K-\lambda t^2+tw,\\
 A_2&=\frac{d_0}{2}t^2-\lambda t,\qquad
 A_3=\frac{d_0}{2}t.
 \end{aligned}
 \tag{3}
\]
These are direct expansions of the original scalar, with no parameter
discarded.

Put r=4z/3 in [0,1]. The exact cubic identity is
\[
 P=b_0(1-r)^3+3b_1r(1-r)^2+3b_2r^2(1-r)+b_3r^3,
 \tag{4}
\]
where
\[
 \begin{aligned}
 b_0&=A_0,&
 b_1&=A_0+\frac14A_1,\\
 b_2&=A_0+\frac12A_1+\frac3{16}A_2,&
 b_3&=P(t,3/4).
 \end{aligned}
 \tag{5}
\]
We will prove
\[
 b_0<-\frac{t}{25},\qquad
 b_1<\frac{3t}{100},\qquad
 b_2<-\frac{t}{50},\qquad
 b_3\le-\frac{85}{9216}<0.
 \tag{6}
\]
A positive b1 is allowed; Section 6 proves the sign of the whole
quadratic group without falsely asserting that every coefficient is
negative.

#### 2. The first coefficient

The identities t²=2w+w² and d+1/d-2=w²/d give
\[
 \frac{b_0}{t}
 =-\frac{11}{108}+\frac{t}{30}
          +g(t),\qquad
 g(t)=w^2\left(\frac1t-\frac1d\right)>0.
 \tag{7}
\]
The function g increases on the full interval (0,3/4]. To see this,
put q=t/d, so 0<q<=3/5 and 1/d>=4/5. Logarithmic differentiation,
using d'=t/d and q'=1/d³, yields the exact formula
\[
 \frac{t g'(t)}{g(t)}
 =1+\frac2d-q-q^2
 \ge 1+\frac85-\frac35-\frac9{25}
 =\frac{41}{25}>0.
 \tag{8}
\]
At t=3/4, d=5/4 and w=1/4, so g(3/4)=1/30. Therefore
\[
 \frac{b_0}{t}
 \le-\frac{11}{108}+\frac1{40}+\frac1{30}
 =-\frac{47}{1080}<-\frac1{25}.
 \tag{9}
\]
The last strict margin is 19/5400. This proves the first bound in (6).

#### 3. The second coefficient

Collecting the original radical terms in b1 gives
\[
 b_1=\frac{413}{540}t^2+\frac{2059}{1080}t+\frac{1069}{432}
       -\frac{3t^3+9t^2+7t+10}{4d}.
 \tag{10}
\]
Equivalently,
\[
 b_1-\frac{3t}{100}
 =\frac{8260t^2+20266t+26725}{10800}
       -\frac{3t^3+9t^2+7t+10}{4d}.
 \tag{11}
\]
All displayed numerator polynomials are positive for t>=0. Thus
positive squaring reduces the desired strict inequality to R1>0,
where
\[
 R_1=
 \bigl(2700(3t^3+9t^2+7t+10)\bigr)^2
 -(1+t^2)(8260t^2+20266t+26725)^2.
 \tag{12}
\]

There is a short direct positive-bracket proof on the whole interval.
Put x=t-1/2, so -1/2<x<=1/4; allowing the closed endpoint -1/2
only enlarges the range. Direct polynomial expansion gives
\[
 \begin{aligned}
 R_1={}&1763995-173049x\\
 &+x^2(45348655+31017468x)\\
 &+x^4(113582844+51012880x-2617600x^2).
 \end{aligned}
 \tag{13}
\]
The three factors in this grouping have the explicit lower bounds
\[
 \begin{aligned}
 1763995-173049x&\ge\frac{6882931}{4}>0,\\
 45348655+31017468x&\ge29839921>0,\\
 113582844+51012880x-2617600x^2
   &\ge87422004>0.
 \end{aligned}
 \tag{14}
\]
Here x>=-1/2, x<=1/4, and x²<=1/4 suffice. Thus R1>0, so
(11) is negative and b1<3t/100 throughout its complete t interval.

#### 4. The third coefficient

Similarly the exact expression for b2 is
\[
 b_2=\frac{10223}{17280}t^2+\frac{3701}{2160}t+\frac{637}{216}
       -\frac{t^3+5t^2+3t+6}{2d}.
 \tag{15}
\]
Consequently
\[
 b_2+\frac{t}{50}
 =\frac{51115t^2+149768t+254800}{86400}
       -\frac{t^3+5t^2+3t+6}{2d}.
 \tag{16}
\]
Again both numerator polynomials are positive. It suffices to prove
\[
 R_2=
 \bigl(43200(t^3+5t^2+3t+6)\bigr)^2
 -(1+t^2)(51115t^2+149768t+254800)^2>0.
 \tag{17}
\]
Use the same x=t-1/2 in [-1/2,1/4]. For a direct check of the
translated arithmetic, (17) becomes exactly
\[
 \begin{aligned}
 64R_2={}&1866240000(8x^3+52x^2+70x+71)^2\\
 &-(4x^2+4x+5)(204460x^2+803532x+1369851)^2.
 \end{aligned}
\]
Expanding and grouping gives
\[
 \begin{aligned}
 64R_2={}&25257028995+37267413876x\\
 &+x^2(584056471620+434328819168x)\\
 &+x^4(789868496464+71174891840x-47776206400x^2).
 \end{aligned}
 \tag{18}
\]
Every group is nonnegative and the first is strictly positive:
\[
 \begin{aligned}
 25257028995+37267413876x&\ge6623322057>0,\\
 584056471620+434328819168x&\ge366892062036>0,\\
 789868496464+71174891840x-47776206400x^2
   &\ge742336998944>0.
 \end{aligned}
 \tag{19}
\]
As before, these bounds use only x>=-1/2 and x²<=1/4.
Equations (17)--(19), followed by positive squaring in (16), prove
b2<-t/50 on the entire interval.

#### 5. The last coefficient: the complete z=3/4 endpoint

This is the complete hand endpoint argument supplied for this same cubic.
Set
\[
 P_*(t)=-b_3=\left(t+\frac34\right)
                   \left(\frac14-F_q(t,3/4)\right).
\]
It extends continuously to t=0. Direct collection gives
\[
 \begin{aligned}
 P_*(t)&=H(t)-2-\frac{205}{108}\left(t+\frac34\right)
              +\frac34t-q_0t\left(t+\frac34\right),\\
 H(t)&=\frac{11+t}{4}d+\frac{t+3/4}{d},\qquad
 q_0=\frac{2959}{5760}.
 \end{aligned}
 \tag{20}
\]
Differentiation yields
\[
 H''(t)=
 \frac{2-\frac94t+\frac{17}{4}t^2+\frac54t^3+\frac12t^5}
      {(1+t^2)^{5/2}},\qquad
 H'''(t)=\frac{51t^2(1-t)-6t-9}{4(1+t^2)^{7/2}}.
 \tag{21}
\]
The latter numerator is strictly negative. Indeed
\[
 \frac4{27}-t^2(1-t)
  =\left(t-\frac23\right)^2\left(t+\frac13\right)\ge0,
\]
so 51t²(1-t)-6t-9<=-13/9-6t<0. Therefore H'' decreases,
and throughout [0,3/4],
\[
 P_*''(t)\ge H''(3/4)-2q_0
   =\frac{6859}{6250}-\frac{2959}{2880}
   =\frac{126017}{1800000}>0.
 \tag{22}
\]
The right-endpoint derivative is nevertheless negative:
\[
 \begin{aligned}
 P_*'(3/4)
 &=\frac{2299}{1000}-\frac{31}{27}-\frac{2959}{2560}\\
 &=-\frac{8653}{1728000}<0.
 \end{aligned}
 \tag{23}
\]
Since the derivative is increasing by (22), it is negative throughout
the interval. Thus P_* decreases, and direct endpoint substitution gives
\[
 P_*(t)\ge P_*(3/4)
    =\frac{2925}{1024}-\frac{205}{72}
    =\frac{85}{9216}>0.
 \tag{24}
\]
This proves the last inequality of (6), including t=3/4.

#### 6. The entire cubic is strictly negative

For fixed t>0, group (4) as
\[
 P=(1-r)\left[b_0(1-r)^2+3b_1r(1-r)+3b_2r^2\right]+b_3r^3.
 \tag{25}
\]
If b1<=0, the bracket is strictly negative for every r in [0,1],
because b0,b2<0 and r,1-r cannot both vanish.

If b1>0, the bounds already proved give
\[
 b_1^2<\frac{9t^2}{10000}
 <\frac{4t^2}{3750}
 <\frac43 b_0b_2.
 \tag{26}
\]
The middle coefficient margin is
4/3750-9/10000=1/6000>0. Thus the discriminant of the bracket
viewed as the homogeneous quadratic
b0 u²+3b1 uv+3b2 v² is strictly negative:
\[
 (3b_1)^2-4b_0(3b_2)<0.
\]
Since b0<0, that quadratic is negative for every nonzero (u,v),
in particular u=1-r, v=r. This establishes the same strict sign
for the bracket in the remaining b1 case.

For r<1, equation (25) is now strictly negative. At r=1 it equals
b3<0 by (24). Therefore P(t,z)<0 for every point in the closed
z interval, including both endpoints. Since t+z>0 and F<=F_q,
equation (3) proves the strict scalar bound (2).

This completes the entire small-t rectangle. Combined with the proved
large-t rectangle and the decreasing z tail, it supplies the scalar
upper bound required by the unchanged negative-vertical physical
predicate; the physical lower bound in that caller is strictly greater
than one quarter.


### I.2. The larger-tilt rectangle

#### 1. Exact inequality and the quadratic radical bound

Put

\[
 \lambda=\frac{29}{27},\qquad d_0=\frac{61}{60},\qquad
 \alpha=\frac1{60},\qquad
 d=\sqrt{1+t^2},\qquad a=\frac1d,\qquad w=d-1.
\]

For

\[
                    \frac34\le t\le1,\qquad 0\le z\le\frac34,
\tag{L1}
\]

define the scalar from the retained negative-P geometric reduction:

\[
 F(t,z)=2\lambda-a-d+\alpha t
        +t d_0\sqrt{1+z^2}-t\lambda z
        -\frac{w(2-tz)}{t+z}.
\tag{L2}
\]

We prove the strict bound

\[
                              F(t,z)<\frac14
\tag{L3}
\]

throughout the entire rectangle (L1), including all four sides.

The positive-squared comparison

\[
             (1+z^2/2)^2-(1+z^2)=z^4/4\ge0
\]

gives sqrt(1+z²)<=1+z²/2. Let F_q be (L2) with that single
radical replaced by 1+z²/2. Its coefficient t d_0 is positive, so

\[
                              F\le F_q.
\]

Set

\[
 P(t,z)=(t+z)\left(\frac14-F_q(t,z)\right),\qquad
 q(z)=\frac{31}{30}-\lambda z+\frac{d_0}{2}z^2.
\tag{L4}
\]

The denominator t+z is positive on (L1). Thus it suffices to prove
P(t,z)>0.

#### 2. A uniform second-derivative bound in t

For fixed z, direct collection of the exact terms in (L4) gives

\[
 \begin{aligned}
 P(t,z)
 &=H_0(t)+zH_1(t)-2-\frac{205}{108}(t+z)
       +tz-q(z)t(t+z),\\
 H_0(t)&=d(2+t)+\frac td,\\
 H_1(t)&=d(1-t)+\frac1d.
 \end{aligned}
\tag{L5}
\]

Here 205/108=2lambda-1/4 and 31/30=alpha+d_0. In particular,

\[
                        P_{tt}=H_0''+zH_1''-2q(z).
\tag{L6}
\]

The exact derivatives needed for the uniform bound are

\[
 \begin{aligned}
 H_0''(t)&=\frac{2+2t^2+5t^3+2t^5}{d^5},\\
 H_0'''(t)&=\frac{3t(2t-1)(2-t)}{d^7},\\
 H_1''(t)&=\frac{-3t+3t^2-5t^3-2t^5}{d^5},\\
 H_1'''(t)&=-\frac{3[(1-t)^2+3t^3]}{d^7}.
 \end{aligned}
\tag{L7}
\]

On 3/4<=t<=1, H_0''' is positive and H_1''' is negative.
Consequently

\[
 H_0''(t)\le H_0''(1)=\frac{11}{4\sqrt2}<2,\qquad
 H_1''(t)\le H_1''(3/4)=-\frac{3222}{3125}<-1.
\tag{L8}
\]

The first strict comparison is the positive square comparison
121<128. The second is immediate from 3222>3125.

Using z>=0 in (L6), we obtain

\[
 \begin{aligned}
 P_{tt}
 &<-\frac1{15}+\frac{31}{27}z-\frac{61}{60}z^2\\
 &\le-\frac1{15}+\frac{14415}{44469}\\
 &=\frac4{15}-\frac{136}{14823}<\frac4{15}.
 \end{aligned}
\tag{L9}
\]

The middle step is the maximum of the displayed concave quadratic,
obtained by completing its square. No t or z sample is used.

#### 3. Interpolation reduces the full t interval to two endpoint cubics

Let theta=4t-3, so 0<=theta<=1. From P_tt<4/15, the function

\[
          P(t,z)-\frac2{15}(t-3/4)(t-1)
\]

is concave in t. Its endpoint values agree with those of P.
Therefore

\[
 \begin{aligned}
 P(t,z)\ \ge\ &(1-\theta)P(3/4,z)+\theta P(1,z)\\
              &-\frac2{15}(t-3/4)(1-t).
 \end{aligned}
\tag{L10}
\]

The product in the last line is at most 1/64, because the interval
has length 1/4. Thus the possible loss is at most

\[
                            \frac2{15}\frac1{64}=\frac1{480}.
\tag{L11}
\]

It remains to prove the two complete endpoint statements

\[
 P(3/4,z)>\frac1{480},\qquad
 P(1,z)>\frac1{480}
 \qquad(0\le z\le3/4).
\tag{L12}
\]

The next two sections do so with exact quadratic and cubic arithmetic.

We will use one elementary observation. A cubic with negative leading
coefficient has a downward-opening quadratic derivative. If that
derivative is positive at z=1/3, the cubic on [1/3,3/4] first
increases and can then only decrease: its derivative has at most one
zero to the right of a point where it is positive. Its minimum on
that interval is consequently at 1/3 or 3/4.

#### 4. The t=3/4 endpoint, including every z

Substitution of d=5/4 gives the exact cubic

\[
 Q_0(z):=P(3/4,z)
 =\frac{47}{1440}-\frac{223}{1080}z
      +\frac{2993}{5760}z^2-\frac{61}{160}z^3.
\tag{L13}
\]

For 0<=z<=1/3, use z³<=z²/3. After subtracting 1/480,

\[
 Q_0(z)-\frac1{480}
 \ge \frac{11}{360}-\frac{223}{1080}z
                    +\frac{2261}{5760}z^2>0.
\tag{L14}
\]

The leading coefficient is positive, and its complete-square
positivity is certified by the exact strict reserve

\[
 4\frac{11}{360}\frac{2261}{5760}
                 -\left(\frac{223}{1080}\right)^2
                 =\frac{24923}{4665600}>0.
\tag{L15}
\]

For the remaining interval, direct differentiation gives

\[
                      Q_0'(1/3)=\frac{37}{2880}>0.
\tag{L16}
\]

The cubic observation from Section 3 reduces its minimum on
[1/3,3/4] to its two endpoints. At 1/3 the strict inequality
was already proved in (L14). At 3/4 its exact value is

\[
 Q_0(3/4)=\frac{85}{9216}
        =\frac1{480}+\frac{329}{46080}>\frac1{480}.
\tag{L17}
\]

This proves the first endpoint statement of (L12) over the whole
closed z interval.

#### 5. The t=1 endpoint, including every z

With d=sqrt(2), exact collection gives

\[
 \begin{aligned}
 P(1,z)
 &=\left(\frac72+\frac z2\right)\sqrt2
       -\frac{2663}{540}-\frac{463}{540}z
       +\frac{611}{1080}z^2-\frac{61}{120}z^3.
 \end{aligned}
\tag{L18}
\]

For z>=0 the coefficient of sqrt(2) is positive. The exact
lower bound sqrt(2)>140/99 has positive squared reserve

\[
                          2-\left(\frac{140}{99}\right)^2
                            =\frac2{9801}>0.
\]

Consequently

\[
 P(1,z)>Q_1(z):=
 \frac{107}{5940}-\frac{893}{5940}z
       +\frac{611}{1080}z^2-\frac{61}{120}z^3.
\tag{L19}
\]

For 0<=z<=1/3, again use z³<=z²/3:

\[
 Q_1(z)-\frac1{480}
 \ge\frac{757}{47520}-\frac{893}{5940}z
                       +\frac{107}{270}z^2>0.
\tag{L20}
\]

The exact complete-square reserve is

\[
 4\frac{757}{47520}\frac{107}{270}
             -\left(\frac{893}{5940}\right)^2
             =\frac{93540}{35283600}>0.
\tag{L21}
\]

For z>=1/3, the lower cubic's derivative is downward-opening and

\[
                         Q_1'(1/3)=\frac{409}{7128}>0.
\tag{L22}
\]

Its minimum on [1/3,3/4] is therefore at an endpoint. The first
was already covered by (L20), and the second has exact value

\[
 Q_1(3/4)=\frac{6871}{760320}
        =\frac1{480}+\frac{5287}{760320}>\frac1{480}.
\tag{L23}
\]

Thus Q_1>1/480 throughout the closed interval. Equation (L19)
proves the second endpoint statement in (L12).

#### 6. Complete large-t conclusion and integration contract

For each fixed z in [0,3/4], both endpoint values in (L10)
are strictly greater than 1/480, while its interpolation loss
is at most 1/480. Therefore P(t,z)>0 on the entire closed
rectangle (L1). Since t+z>0, the definition (L4) gives

\[
                         F(t,z)\le F_q(t,z)<\frac14.
\]

This completes the assigned large-t scalar inequality. Every derivative,
endpoint polynomial, and rational positivity comparison used above is
printed explicitly. The two z intervals overlap at 1/3, and the
t boundaries 3/4 and 1 are included; no unexamined interior range
remains in this rectangle.

This rectangle joins the smaller-tilt proof in Part I.1 and the
monotone tail in Appendix F, Section 7. Part I.3 records their complete
scalar and geometric conclusion.


### I.3. Every slope is covered and the last physical predicate is impossible

Parts I.1 and I.2 give F(t,z)<1/4 on the complete rectangle
0<t<=1, 0<=z<=3/4. Their t ranges overlap at 3/4, and both
include all z boundaries. Appendix F, Section 7, proves F_z<0 for
z>=3/4, with no extra t restriction. Thus
\[
 F(t,z)<\frac14\quad(0<t\le1,\ z\ge0),
\]
in particular for the complete physical scalar domain 0<=z<1/t.

Appendix F, Section 6.3, gives the strict lower bound from the two
retained original lower squares:
\[
 \delta>\frac{10907}{43400}
        =\frac14+\frac{57}{43400}.
\]
Sections 6.4--6.5 of that same appendix, using both genuine upper
separators and the unchanged physical P frame, give delta<F(t,z)
at some scalar point in the covered domain. The two inequalities
are contradictory.

This excludes the complete negative-or-zero-P, vertical-right-inset
alternative. Appendix F, Section 5, already excludes both P-owned
right-inset alternatives, and Sections 6.1--6.2 establish that these
exhaust every possible actual separator. The negative-central part
of the fixed all-nine (2,2,1) theorem is therefore closed.

