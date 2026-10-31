# The radius-two measure theorem without the fixed angle-checker dependencies

Date: October 27, 2026.

**Status: complete analytic replacement, pending independent acceptance.**
The reference sources were retrieved at exact PR11 head
`50c0cd616eb494ade100f055ad518cdbd33c7275`.
This manuscript supplies direct analytic proofs of all five fixed mass
targets and the one derivative target retained by
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`.
Its complete geometric reductions and open-interior conventions are
unchanged. The high-precision inverse-angle checkers and their stored
common-rectangle margins are no longer needed after acceptance of this
replacement.

The proof still uses explicit finite arithmetic: one common Taylor
lemma, thirteen displayed rational angle comparisons, positive-square
radical bounds and short rational sums. The claim is removal of the
five fixed mass-checker dependencies and the derivative-checker
dependency, not absence of arithmetic. All historical sources, data,
checkers and reviews remain intact.

## 1. The exact current targets

Keep the original radial measure

\[
\mu=\frac1{1000}\left(
292\delta_0+714\lambda_{1/10}+3858\lambda_1
+2424\lambda_{11/10}+1709\lambda_{27/20}\right),
\qquad \mu(\mathbb R^2)=8997/1000<9.
\tag{1}
\]

Here \(\lambda_r\) is normalized angular measure on the circle of
radius r about the containing-disk center. The unchanged own-frame
normalization is

\[
S(a,b)=[a-1,a]\times[b-1,b],\qquad
1/2\le b\le a,\qquad a^2+b^2\le4.
\tag{2}
\]

The current line analytic source locates one minimum on each side of
a=1. Its left submeasure is

\[
L(a)=\frac{292}{1000}
+\frac{714}{1000\pi}\arccos(10(a-1))
+\frac{3858}{1000\pi}(\pi/6-\arccos a),
\tag{3}
\]

and its unique minimum occurs at
\(927/1000<a_0<928/1000\). The actual origin atom is present on
this whole critical interval. Its right, atom-free measure is

\[
U(a)=\frac{643}{1000}
+\frac{714\arccos(10(a-1))
+2424[\arcsin(5/11)-\arccos(10a/11)]}{1000\pi},
\tag{4}
\]

with exact unique minimum at \(a_*=324943/298110\).
The accepted derivative arguments establish these minima on their
entire intervals, including the actual atom-free a=1 endpoint.
We prove directly that \(L(a_0)>1\) and \(U(a_*)>1\).

For the accepted outer reduction put

\[
a=\sqrt{4-b^2},\quad
S_b=[a-1,a]\times[b-1,b],\quad 1/2\le b\le\sqrt2,
\quad M(b)=\mu(\operatorname{int}S_b).
\tag{5}
\]

Its complete circle-face cover and convexity argument require

\[
M(1/2)>201/200,\qquad M(13/12)>201/200,
\qquad M(\sqrt2)>201/200,
\quad |M'(13/12)|<1/150.
\tag{6}
\]

These are precisely the remaining current fixed targets. No new
parameter enclosure, branch assumption, origin atom or sampled minimum
is introduced below.

## 2. One exact Taylor lemma for all the required angles

For \(0\le x\le13/10\), define

\[
\begin{aligned}
C_8(x)&=1-x^2/2!+x^4/4!-x^6/6!+x^8/8!,\\
C_{10}(x)&=C_8(x)-x^{10}/10!,\\
S_9(x)&=x-x^3/3!+x^5/5!-x^7/7!+x^9/9!,\\
S_{11}(x)&=S_9(x)-x^{11}/11!.
\end{aligned}
\]

The alternating Taylor remainder gives

\[
C_{10}(x)\le\cos x\le C_8(x),\qquad
S_{11}(x)\le\sin x\le S_9(x).
\tag{7}
\]

The term magnitudes decrease throughout this whole interval; for the
cosine series already the first ratio is at most
\((13/10)^2/2<1\), and every subsequent ratio is smaller.
The sine ratios are smaller still. Thus the stated remainder signs
apply to every row below, rather than to individually sampled angles.

We also use the explicit pi bounds

\[
\frac{314159}{100000}<\pi<\frac{22}{7}.
\tag{8}
\]

For the lower bound, the exact Machin identity already proved in the
original measure source and the signed atan remainder give

\[
\begin{aligned}
\pi
&=16\arctan(1/5)-4\arctan(1/239)\\
&>16\left(\frac15-\frac{1}{3\cdot5^3}
+\frac{1}{5\cdot5^5}-\frac{1}{7\cdot5^7}\right)
-\frac4{239}\\
&=\frac{314159}{100000}+\frac{21011}{12547500000}.
\end{aligned}
\]

For the upper bound, direct polynomial division and integration give

\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=22/7-\pi.
\]

In particular \(13/10<\pi/2\), so every inverse-angle comparison
uses the usual strictly monotone branch on \([0,\pi/2]\).

The following table states every required fixed Taylor comparison.
In its last column, R denotes exactly the rational polynomial
difference written in the preceding column. The displayed positive
lower bound is obtained by direct substitution in (7), with rational
arithmetic only. No inverse-trigonometric evaluator occurs in any row.

**Table (9). Exact Taylor comparisons.**

| x | y | Positive rational difference R | Bound for \(10^9R\) |
| --- | --- | --- | ---: |
| 767/1000 | 18/25 | \(y-C_8(x)\) | >4139 |
| 769/2000 | 927/1000 | \(y-C_8(x)\) | >13903 |
| 4507/10000 | 26833/29811 | \(C_{10}(x)-y\) | >38417 |
| 2359/5000 | 5/11 | \(y-S_9(x)\) | >55080 |
| 1349/10000 | 324943/327921 | \(y-C_8(x)\) | >3759 |
| 1791/5000 | 1873/2000 | \(C_{10}(x)-y\) | >29400 |
| 1897/5000 | 10/27 | \(y-S_9(x)\) | >7166 |
| 8213/10000 | 1703/2500 | \(C_{10}(x)-y\) | >70141 |
| 9029/10000 | 1703/2750 | \(C_{10}(x)-y\) | >62981 |
| 4657/5000 | 65/81 | \(y-S_9(x)\) | >13001 |
| 4271/10000 | 20711/50000 | \(S_{11}(x)-y\) | >13052 |
| 3861/10000 | 20711/55000 | \(S_{11}(x)-y\) | >14751 |
| 3119/10000 | 20711/67500 | \(S_{11}(x)-y\) | >37888 |

For example, a row of the form \(y-C_8(x)>0\) proves
\(\cos x<y\), hence \(\arccos y<x\). A row of the form
\(y-S_9(x)>0\) proves \(\sin x<y\), hence
\(\arcsin y>x\). The other two row types give the reverse
inverse-angle inequalities. All signs and branches are explicit.

One further whole-interval inequality handles all three small
subtracted angles at the outer tangent:

\[
\arcsin x\le x+x^3/5<\frac{501}{500}x
\qquad(0<x\le1/12).
\tag{10}
\]

To prove the first inequality, put t=x^2. The comparison of positive
quantities in the derivative is justified by

\[
(1+3t/5)^2(1-t)-1
=\frac{t}{25}(5-21t-9t^2)>0
\qquad(0<t\le1/144).
\]

Integrating from zero gives the claim. The second inequality follows
from \(x^2/5\le1/720<1/500\). At zero the weak inequality is exact.

## 3. Both entire line minima have direct positive reserves

### 3.1. The left minimum and its actual origin atom

The unchanged analytic location of \(a_0\) implies

\[
\arccos(10(a_0-1))>\pi-\arccos(18/25),\qquad
\arccos a_0<\arccos(927/1000).
\]

The first two rows of (9) therefore give

\[
L(a_0)>
\frac{1649}{1000}
-\frac{714(767/1000)+3858(769/2000)}{1000\pi}.
\]

The numerator being subtracted is positive. The lower pi bound in
(8), with the correct direction for this negative term, yields

\[
L(a_0)>
\frac{314944291}{314159000}
=1+\frac{785291}{314159000}>1.
\tag{11}
\]

This directly proves the exact critical value. No smaller common
rectangle and no rounding of \(a_0\) beyond its already proved
rational enclosure is needed. The origin atom is used only where
\(a_0<1\); the actual square at a=1 remains in the next case.

### 3.2. The right minimum, including the atom-free endpoint domain

At \(a_*=324943/298110\),

\[
10(a_*-1)=26833/29811,\qquad 10a_*/11=324943/327921.
\]

Rows 3--5 of (9) imply

\[
\arccos(10(a_*-1))>4507/10000,
\quad \arcsin(5/11)>2359/5000,
\quad \arccos(10a_*/11)<1349/10000.
\]

Their resulting weighted numerator is positive. Using the upper pi
bound in (8) gives

\[
\begin{aligned}
U(a_*)&>\frac{643}{1000}
+\frac{714(4507/10000)+2424(2359/5000-1349/10000)}
{1000(22/7)}\\
&=\frac{110575589}{110000000}
=1+\frac{575589}{110000000}>1.
\end{aligned}
\tag{12}
\]

The unchanged derivative signs prove that (11)--(12) bound the full
two line intervals. The a=1 square has no atom in (4), and continuity
on that atom-free right interval includes it. The original even-density
translation therefore extends these two bounds to the complete
two-dimensional inner region exactly as before.

## 4. Three outer values without an inverse-angle enclosure

The following three strict radical upper bounds are useful:

\[
\sqrt{15}/2<3873/2000,\qquad
\sqrt{407}/12<4203/2500,\qquad
\sqrt2<70711/50000.
\tag{13}
\]

Their positive-square reserves, in the same order, are

\[
129/4000000,\qquad1253/28125000,
\qquad45521/2500000000.
\]

### 4.1. The initial endpoint b=1/2

The exact original circle branches at this endpoint give

\[
M(1/2)=\frac{
3858\arccos(\sqrt{15}/2-1)
+2424\arcsin(5/11)+1709\arcsin(10/27)}{1000\pi}.
\tag{14}
\]

The first bound in (13) and rows 4, 6, 7 of (9) give respective
angle lower bounds \(1791/5000\), \(2359/5000\),
\(1897/5000\). Hence

\[
M(1/2)>
\frac{111089069}{110000000}
=\frac{201}{200}+\frac{539069}{110000000}
>\frac{201}{200}.
\tag{15}
\]

Here and in the next subsection the positive angle numerator is
divided by the conservative upper pi bound \(22/7\).

### 4.2. The one interior tangent b=13/12

Put \(a=\sqrt{407}/12\), \(A=a-1\), and w=1/12.
The exact accepted branches at this point are

\[
\begin{aligned}
L_1&=\arccos A-\arcsin(1/12),\\
L_2&=\arccos(10A/11)-\arcsin(5/66),\\
L_3&=\arcsin(65/81)-\arcsin(5/81),\\
M(13/12)&=(3858L_1+2424L_2+1709L_3)/(2000\pi).
\end{aligned}
\tag{16}
\]

The second radical bound in (13) gives \(A<1703/2500\).
Rows 8--10 of (9) supply the three positive angle lower bounds in
(16). The one uniform small-angle bound (10) supplies all three
subtracted-angle upper bounds. Consequently

\[
L_1>8213/10000-167/2000,
\]
\[
L_2>9029/10000-167/2200,
\qquad L_3>4657/5000-167/2700.
\]

All three displayed differences are positive. Exact rational
addition and the upper pi bound give

\[
M(13/12)>
\frac{65874322367}{65340000000}
=\frac{201}{200}+\frac{207622367}{65340000000}
>\frac{201}{200}.
\tag{17}
\]

### 4.3. The complete diagonal endpoint a=b=sqrt(2)

Write \(d=\sqrt2-1\). For each of the three large circles, the
exact interval length is
\(\pi/2-2\arcsin(d/r_j)\). Thus

\[
M(\sqrt2)=\frac{7991}{4000}
-\frac{3858\arcsin d+2424\arcsin(10d/11)
+1709\arcsin(20d/27)}{1000\pi}.
\tag{18}
\]

The last bound in (13) gives \(d<20711/50000\). Rows 11--13 of
(9), and monotonicity of asin, give upper bounds
\(4271/10000\), \(3861/10000\), \(3119/10000\) for the three
subtracted angles. Their weighted numerator is positive. The lower
pi bound in (8) is therefore the correct conservative substitution
in (18), giving

\[
M(\sqrt2)>
\frac{1263766449}{1256636000}
=\frac{201}{200}+\frac{847269}{1256636000}
>\frac{201}{200}.
\tag{19}
\]

This argument uses the actual diagonal square and its actual open
circle intervals. It does not replace the two equal radical
coordinates by independent rounded parameters.

## 5. The derivative target from three simple rational intervals

At the same exact tangent b=13/12, a=\(\sqrt{407}/12\), put

\[
t_j=\sqrt{r_j^2-(a-1)^2},\qquad
v_j=\sqrt{r_j^2-1/144},\qquad
u_3=\sqrt{r_3^2-(13/12)^2},
\]

where \((r_1,r_2,r_3)=(1,11/10,27/20)\). These positive radicals
satisfy the following strict bounds. Entries in the middle two
columns are numerators over 1000. The final columns are the exact
positive-square reserves proving those bounds.

**Table (20). Positive radical intervals.**

| Quantity | Lower | Upper | Lower squared reserve | Upper squared reserve |
| --- | ---: | ---: | --- | --- |
| a | 1681 | 1682 | 5651/9000000 | 3077/1125000 |
| t1 | 731 | 733 | 103/200000 | 21/20000 |
| t2 | 863 | 864 | 107/1000000 | 257/1000000 |
| v1 | 996 | 997 | 2339/2250000 | 8581/9000000 |
| v2 | 1096 | 1097 | 4139/2250000 | 3181/9000000 |
| u3 | 805 | 806 | 311/360000 | 1681/2250000 |
| v3 | 1347 | 1348 | 10319/9000000 | 871/562500 |

For a, v1, v2, u3, v3 the exact radicands are
\(407/144,143/144,121/100-1/144,146/225,817/450\).
For t1,t2 the lower squared reserve uses a<1682/1000 and the upper
one uses a>1681/1000. This correctly retains the dependence of t1,t2
on the same a; no independent rounding of an unknown radical is
assumed.

Let

\[
G_1=\frac{13/12}{at_1}-\frac1{v_1},\qquad
G_2=\frac{13/12}{at_2}-\frac1{v_2},\qquad
H=\frac1{u_3}-\frac1{v_3}.
\]

All denominators in (20) are positive. Substituting their endpoints
in the correct directions yields the short bounds

\[
-126/1000<G_1<-121/1000,
\quad -167/1000<G_2<-164/1000,
\quad 498/1000<H<501/1000.
\tag{21}
\]

For complete rational evidence, the exact lower and upper endpoint
expressions and their reserves from the corresponding bound in (21)
are:

**Table (22). Exact derivative-term intervals.**

| Term | Endpoint lower bound | Lower reserve | Endpoint upper bound | Upper reserve |
| --- | --- | --- | --- | --- |
| G1 | -6412750/51165599 | 17057737/25582799500 | -446183000/3675373701 | 1462782179/3675373701000 |
| G2 | -6232375/37330308 | 446609/9332577000 | -786859000/4774263573 | 969943507/1193565893250 |
| H | 270500/542841 | 82591/271420500 | 27150/54257 | 32757/54257000 |

Each reserve is positive. For an upper bound its reserve is the
desired upper endpoint in (21) minus the rational endpoint expression
in (22). Thus (21) is an explicit rational consequence of (20).

The exact original differentiated circle formula is

\[
M'(13/12)=\frac{T}{2000\pi},\qquad
T=3858G_1+2424G_2+1709H.
\]

The weights are positive. Equation (21) gives directly

\[
-40<-\frac{19917}{500}<T<-\frac{1629}{200}<0.
\tag{23}
\]

For the leftmost comparison, \(40-19917/500=83/500>0\).
Since \(\pi>3\), (23) proves
\( |M'(13/12)|<40/(2000\cdot3)=1/150\).
This replaces the former derivative-checker call by the displayed
positive-square and rational inequalities.

## 6. Full continuous-domain and same-nine-square assembly

The accepted outer source proves its full initial and final ranges
are bounded below by \(M(1/2)\) and \(M(\sqrt2)\), respectively.
On the whole intervening interval it proves \(M''>1/30\), with
the exact tangent \(b_*=13/12\) in that interval. No new
subdivision or location of a derivative root is used here.
Equations (17),(23) therefore give, for every point of that whole
middle interval,

\[
\begin{aligned}
M(b)&>201/200-|b-b_*|/150+(b-b_*)^2/60\\
&=3013/3000+(|b-b_*|-1/5)^2/60
\ge3013/3000>1.
\end{aligned}
\tag{24}
\]

Equations (15),(19) give the stronger endpoint bounds on the other
two ranges. Their closed branch transitions and the two geometric
outer endpoints remain included. Thus the entire original outer
curve has exactly the same uniform bound as before.

For clarity, the complete unchanged global cover is:

| Actual normalized region | Entire-domain proof after this replacement |
| --- | --- |
| a<=9/10 | The original atom plus small-circle bound is 1006/1000. |
| 9/10<=a<=11/10, b<=9/10 | The original even-density translation reduces to b=1/2; the complete line derivative arguments and (11)--(12) prove its full charge. |
| 9/10<=b<=a<=11/10 | The accepted rectangle analytic reduction covers all four corner cases, including every atom boundary. |
| 11/10<=a<=27/20, b<=1 | The original two-circle strip estimate exceeds one by 189/34375. |
| 11/10<=a<=27/20, 1<=b<=a | The accepted rectangle analytic reduction covers both middle cases. |
| a>=27/20 | The original outward comparison reduces to (5); its full branch and convexity proof, (15),(19),(24), give a mass greater than 3013/3000. |

This is the same exhaustive cover of (2) already proved by the
current five-point assembly. Every origin boundary is assigned to
an atom-free actual formula when required. All circle boundary points
excluded from an open square form a finite set and have zero angular
measure. No origin atom is supplied by continuity.

It follows that every actual unit square contained in D2 has
\(\mu(\operatorname{int}S)\ge1\). Nine pairwise disjoint open
square interiors would have total measure at least nine, contradicting
the same measure's total mass \(8997/1000\). The conclusion remains
the uniform geometric theorem \(R>2\) for the same nine actual
squares, with arbitrary orientations and every physical contact or
circle-mask pattern. Forces and means are irrelevant to this measure
theorem and are never modified.

## 7. Exact dependency replacement and retained scope

After independent acceptance, the changes to the current measure
assembly are precisely:

| Previous fixed obligation | Complete analytic replacement |
| --- | --- |
| Left critical common-rectangle charge | Section 3.1, directly at the uniquely located actual scalar minimum |
| Right critical common-rectangle charge | Section 3.2, directly at its exact rational minimum |
| Outer b=1/2 charge | Section 4.1 |
| Outer b=13/12 charge | Section 4.2 |
| Outer a=b=sqrt(2) charge | Section 4.3 |
| Fixed derivative enclosure checker | Section 5, all radical and rational bounds displayed |

The whole geometry, continuous line monotonicity, entire outer branch
cover, convexity estimates, corner/middle analytic reductions and
additive-measure contradiction are retained. The original 208-charge
forest and the later five-charge checkers remain historical
alternatives. They are not counted as additional required checks.

This removes the remaining high-precision integer inverse-angle and
fixed-enclosure checker dependencies from the current R>2 theorem.
There are still thirteen explicitly displayed Taylor comparisons,
the elementary radical and rational comparisons above, and the
already accepted analytic arithmetic in the other regions. No claim
that the proof contains no fixed comparisons is made.

The replacement reaches every current caller that already uses the
same-nine-square R>2 theorem, including
`GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md`, Section 4.
It does not assert R>2 for an isolated six-square core. It adds no new
graph closure by itself, and does not prove the unrestricted sharp
bound \(R^2\ge1105/256\), classify its equality cases, resolve the
remaining canonicalization audit or supply Lean integration.
No physical unit, original force, contact normal, individual circle
weight, graph degree or mean is changed. No numerical sampling,
optimization or adaptive subdivision is a proof premise. No Lean
compilation, CI, ledger edit or remote mutation was performed.
