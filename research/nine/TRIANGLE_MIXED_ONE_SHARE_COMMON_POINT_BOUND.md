# One common comparison point bounds every original mixed shared mean by radius two

Date: October 26, 2026.

**Status: complete analytic geometric theorem and original-physical join,
accepted after root and separate independent full-source reviews.** See
REVIEW_TRIANGLE_MIXED_COMMON_POINT_ROOT_2026_10_26.md and
REVIEW_C6_COMMON_POINT_FERMAT_BOUND_C6_2026_10_26.md.
The only fixed arithmetic witness is one
rational force point, with all radical comparisons displayed in Section 3.
There is no angular subdivision, parameter grid or coefficient packet.
The fixed witness does not replace a continuous-domain proof: global
convexity and explicit Hessian bounds establish the complete domain.

## 1. The geometric statement, including the entire mean interval

Let \(f_0,f_1,f_2\) be a counterclockwise nondegenerate triangle in an
oriented Euclidean plane, let \(J\) rotate counterclockwise through
\(\pi/2\), and put
\[
 F_i=f_{i-1}-f_i,\qquad P=\sum_i|F_i|,
\]
\[
 g_0=f_2+JF_0,\quad g_1=f_0+JF_1,\quad g_2=f_2+JF_2.
\tag{1}
\]
For \(0\le\delta\le1\), define the original-mean support functional
\[
 \Phi_\delta(x)=\sum_i|f_i-x|+|g_1-x|+|g_2-x|
                   +|g_0-\delta f_0-(1-\delta)x|.
\tag{2}
\]
Let
\[
 \Psi(x)=\sum_i|f_i-x|+|g_1-x|+|g_2-x|+\sqrt2|F_0|.
\tag{3}
\]
The theorem supplies a **single point** \(x\), depending on the
triangle but not on \(\delta\), such that
\[
                          \Phi_0(x)<2P,\qquad\Psi(x)<2P.
\tag{4}
\]
Norm convexity at this same point then gives
\[
 \Phi_\delta(x)\le(1-\delta)\Phi_0(x)+\delta\Psi(x)<2P,
                           \qquad0\le\delta\le1.
\tag{5}
\]
Indeed \(g_0-f_0=(I+J)F_0\), whose norm is \(\sqrt2|F_0|\).
Thus (5) preserves the full original shared-mean interval, including
both endpoints. Section 7 treats collinear and coincident limits as well.
Section 8 gives the exact physical consequence \(R<2\).

Choose an original-triangle Fermat point \(o\), minimizing
\(\sum_i|f_i-o|\). If it is an interior Fermat point, its three
unit radial vectors are 120 degrees apart. Rotate the coordinate
frame and use homogeneity to write
\[
 f_0-o=a e_0,\quad f_1-o=b e_1,\quad f_2-o=e_2,
 \qquad a,b>0,
\]
\[
 e_0=(1,0),\quad e_1=(-1/2,\sqrt3/2),\quad
 e_2=(-1/2,-\sqrt3/2).
\tag{6}
\]
This only divides the geometric inequality by the original positive
distance \(|f_2-o|\). It does not change a physical certificate or
redistribute its force magnitudes. The common point in these units
will be either \(o\) or \(o+(e_2-e_0)/55\). Before normalization,
the latter displacement is \(|f_2-o|(e_2-e_0)/55\).

Put
\[
 \sigma=\sqrt3,\quad h=(1+\sigma)/2,
\]
\[
 D(a,b)=\sqrt{a^2+ab+b^2},\qquad
 E(a,b)=\sqrt{2a^2+(1+\sigma)ab+b^2},
 \qquad G(a,b)=2D(a,b)-E(a,b).
\tag{7}
\]
At the Fermat point define
\[
 \begin{split}
 G_0(a,b)&=2P-\Phi_0(o)\\
 &=G(a,b)+G(1,b)+G(1,a)-(a+b+1),
 \end{split}
\tag{8}
\]
and \(G_1(a,b)=2P-\Psi(o)\). The complete endpoint theorem
`TRIANGLE_MIXED_COLLAPSED_SHARE_FERMAT_BOUND.md` proves \(G_1>0\)
for every \(a,b>0\), and supplies the stronger scalar reserve used
in Section 4 below.

## 2. Global convexity localizes every failure of the original Fermat point

The function \(G\) is jointly convex on the positive quadrant.
In detail,
\[
 \nabla^2G=\Lambda(a,b)
     \begin{pmatrix}b^2&-ab\\-ab&a^2\end{pmatrix},
\quad
 \Lambda(a,b)=\frac{3/2}{D^3}
                  -\frac{1-\sigma/2}{E^3}>0.
\tag{9}
\]
Here \(E>D\) and \(0<1-\sigma/2<3/2\). Therefore \(G_0\)
is globally convex as well.

Consider the single rectangle
\[
             Q=[2/5,7/10]\times[1/5,1/2].
\tag{10}
\]
It will be a sublevel-set enclosure proved by convexity, not a
subdivision of the physical force or angle domain. On all of Q,
\[
 \nabla^2G_0\succeq
 \begin{pmatrix}13/30&0\\0&3/5\end{pmatrix}
       +\frac{10}{9}
          \begin{pmatrix}b^2&-ab\\-ab&a^2\end{pmatrix}.
\tag{11}
\]
Here and below \(\succeq\) means that the difference is positive
semidefinite. We give the full coefficient proof.

For \(0\le t\le7/10\),
\[
 E(1,t)^2-\frac85D(1,t)^2
   =\frac25+(\sigma-3/5)t-\frac35t^2
   >\frac{53}{500}>0.
\]
Since \((8/5)^3>4\), we get \(E(1,t)^3>2D(1,t)^3\), and
\[
 \Lambda(1,t)>\frac{1+\sigma/4}{D(1,t)^3}
                         >\frac{10}{7D(1,t)^3}.
\tag{12}
\]
We used \(\sigma>12/7\). For \(t=a\le7/10\),
\(D^2\le219/100\) and \(D<3/2\), so
\[
 \Lambda(1,a)>\frac{2000}{4599}>\frac{13}{30},
                 \qquad\frac{2000}{4599}-\frac{13}{30}
                      =\frac{71}{45990}>0.
\]
For \(t=b\le1/2\), \(D^2\le7/4\) and \(D<4/3\), giving
\[
                      \Lambda(1,b)>\frac{30}{49}>\frac35.
\]
Finally, on Q,
\[
 \Lambda(a,b)>\frac{(1+\sigma)/2}{D(a,b)^3}
             >\frac{4}{3D(a,b)^3}.
\]
Since \(D^2\le109/100\) and \(D<11/10\),
\[
 \Lambda(a,b)>\frac{4000}{3597}>\frac{10}{9},
           \qquad\frac{4000}{3597}-\frac{10}{9}
                      =\frac{10}{10791}>0.
\]
These are exactly the three contributions in (11).

For any direction \((v,w)\), completing the square in the right
side of (11), first in w and then in v, gives the two simultaneous
lower bounds
\[
 (v,w)\nabla^2G_0(v,w)^T\ge\frac9{20}v^2,
 \qquad
 (v,w)\nabla^2G_0(v,w)^T\ge\frac7{10}w^2.
\tag{13}
\]
For clarity, the first Schur complement is at least
\[
 \frac{13}{30}+
 \frac{(3/5)(10/9)(1/5)^2}{3/5+(10/9)(7/10)^2}
    =\frac{13}{30}+\frac{12}{515}>\frac9{20},
\]
with reserve \(41/6180\). The second is at least
\[
 \frac35+
 \frac{(13/30)(10/9)(2/5)^2}{13/30+(10/9)(1/2)^2}
      =\frac35+\frac{13}{120}>\frac7{10},
\]
with reserve \(1/120\).

## 3. One fixed rational point, with all arithmetic explicit

Set
\[
                   a_*=\frac{5417}{10000},\qquad
                   b_*=\frac{3303}{10000}.
\tag{14}
\]
The only fixed numerical witness needed in this proof is
\[
 -\frac{447}{100000}<G_0(a_*,b_*)<0,
 \qquad
 |(G_0)_a(a_*,b_*)|, |(G_0)_b(a_*,b_*)|<\frac1{10000}.
\tag{15}
\]
The following table verifies it with positive-integer square
comparisons. Every radical is strictly between the two tabulated
integers divided by \(10^6\). The last two columns are the lower
and upper squared reserves multiplied by \(10^{14}\).
For a nested radical, substitute the tabulated lower or upper bound
for \(\sigma\) in its radicand before taking its squared reserve.

| Radical at (14) | Lower numerator | Upper numerator | Lower squared reserve ×10^14 | Upper squared reserve ×10^14 |
| --- | ---: | ---: | ---: | ---: |
| \(\sigma\) | 1732050 | 1732051 | 279750000 | 66660100 |
| \(D(a_*,b_*)\) | 762535 | 762536 | 86377500 | 66129600 |
| \(D(1,b_*)\) | 1199749 | 1199750 | 42699900 | 197250000 |
| \(D(1,a_*)\) | 1354672 | 1354673 | 266241600 | 4692900 |
| \(E(a_*,b_*)\) | 1088486 | 1088488 | 207329950 | 210172499 |
| \(E(1,b_*)\) | 1735365 | 1735366 | 252177500 | 61865600 |
| \(E(1,a_*)\) | 1942521 | 1942522 | 253955900 | 80378400 |

All reserve integers are positive. Thus the complete radical
comparisons are established by squaring positive rational numbers.
The formulas to which the table is applied are
\[
 G_0=2\{D(a,b)+D(1,b)+D(1,a)\}-a-b-1
                       -E(a,b)-E(1,b)-E(1,a),
\]
\[
 (G_0)_a=\frac{2a+b}{D(a,b)}+\frac{2a+1}{D(1,a)}-1
                   -\frac{2a+hb}{E(a,b)}-\frac{a+h}{E(1,a)},
\]
\[
 (G_0)_b=\frac{a+2b}{D(a,b)}+\frac{1+2b}{D(1,b)}-1
                   -\frac{b+ha}{E(a,b)}-\frac{b+h}{E(1,b)}.
\tag{16}
\]
For each lower bound use upper denominators in the positive terms,
lower denominators in the subtracted terms, and the upper value of
h in subtracted numerators. Reverse these directions for upper bounds.
Exact rational substitution gives
\[
 -\frac{279}{62500}<G_0(a_*,b_*)< -\frac{2227}{500000},
\]
\[
 -\frac{54}{10^6}<(G_0)_a(a_*,b_*)<-\frac{45}{10^6},
 \qquad
 \frac{60}{10^6}<(G_0)_b(a_*,b_*)<\frac{67}{10^6}.
\tag{17}
\]
These imply (15); its close lower-value reserve is
\(447/100000-279/62500=3/500000>0\).
This is one fixed point and its explicit gradient, not a table of
continuous parameter cells or an inferred sign between samples.

For every \((a,b)\in Q\),
\[
                    |a-a_*|+|b-b_*|\le\frac{41}{125}.
\]
Convexity and (15) already give
\[
 G_0(a,b)>-\frac{447}{100000}-\frac{41}{1250000}
                                      >-\frac1{200}.
\tag{18}
\]
On the boundary of Q, integrate one of the two Hessian bounds (13)
along the segment from \((a_*,b_*)\). The distance to a vertical
face is at least \(1417/10000\), and to a horizontal face at least
\(1303/10000\). The smaller quadratic contribution is
\(\frac9{40}(1417/10000)^2\); indeed
\[
                 14\cdot1303^2-9\cdot1417^2=5698325>0.
\]
Therefore the entire boundary has the strict lower bound
\[
 G_0>
 -\frac{447}{100000}-\frac{41}{1250000}
     +\frac9{40}\left(\frac{1417}{10000}\right)^2
       =\frac{59801}{4000000000}>0.
\tag{19}
\]
Because G_0 is globally convex and is negative at (14), a point
outside Q with \(G_0\le0\) would make the intervening boundary
point negative by the convex segment inequality. This contradicts
(19). We have proved the exact global implications
\[
 G_0(a,b)\le0\ \Longrightarrow\ (a,b)\in Q^\circ,
 \qquad G_0>-1/200\ \hbox{on Q}.
\tag{20}
\]
No unsampled region is omitted: global convexity handles the entire
positive quadrant outside the single enclosed sublevel region.

## 4. The collapsed endpoint has extra reserve on this whole sublevel enclosure

Write \(m=(a+1)/2\). The complete collapsed-endpoint proof gives
\[
 f(t)>\frac{19}{20000}\quad(t\ge0),
\]
\[
 f(t)=4\sqrt{1+t+t^2}-2\sqrt{2+(1+\sigma)t+t^2}-t
                       +(2-\sqrt2)\sigma-2.
\tag{21}
\]
Retaining, rather than dropping, the first symmetrization remainder
in that proof yields
\[
 G_1(a,b)\ge m f(b/m)
              +(2-\sqrt2)\{D(a,1)-\sigma m\}.
\tag{22}
\]
On Q, \(m\ge7/10\), \(m\le17/20\), and
\[
 D(a,1)-\sigma m
   =\frac{(1-a)^2}{4\{D(a,1)+\sigma m\}}
                    >\frac9{1195}.
\tag{23}
\]
Indeed \((1-a)^2\ge9/100\), \(D(a,1)<3/2\), and
\(\sigma m<(7/4)(17/20)=119/80\), so the denominator is
less than \(239/20\). Since \(2-\sqrt2>7/12\), equations
(21)--(23) give
\[
 G_1>\frac{133}{200000}+\frac{21}{4780}>\frac1{200}.
\tag{24}
\]
The final exact reserve is \(2787/47800000>0\). This lower bound
is uniform over the entire rectangle, with no restriction on the
ratio \(b/m\).

## 5. One common displacement improves the first endpoint and preserves the second

Put \(v=e_2-e_0\), so \(|v|=\sqrt3\), and vary only the
comparison point \(x=o+\tau v\), \(0\le\tau\le1/55\).
All quantities in this section are evaluated at (6), with c=1.
Set
\[
 \beta=(3-\sigma)/2,\qquad K=(3+\sigma)/2.
\]
The explicit derived vectors are
\[
 g_0=((\sigma-1)/2,-a-h),
\]
\[
 g_1=(a+\sigma b/2,a+b/2),\qquad
 g_2=(-h-\sigma b/2,-(\sigma-1)/2-b/2).
\tag{25}
\]
Define
\[
 Z(z)=\frac{Kz+\sigma b}{E(z,b)},\qquad
 V(a)=\frac{\sigma a/2+\beta}{E(1,a)}.
\tag{26}
\]
A direct dot-product calculation gives
\[
 v\cdot\left(\frac{g_0}{|g_0|}
      +\frac{g_1}{|g_1|}+\frac{g_2}{|g_2|}\right)
                      =V(a)+Z(1)-Z(a),
\]
\[
 v\cdot\left(\frac{g_1}{|g_1|}
                   +\frac{g_2}{|g_2|}\right)=Z(1)-Z(a).
\tag{27}
\]
The two required whole-interval direction bounds are elementary:
\[
 Z'(z)=\frac{(3/2-\sigma)zb}{E(z,b)^3}<0,
 \qquad
 \frac K{\sqrt2}<Z(z)<\sigma.
\tag{28}
\]
The range is uniformly smaller than \(3/50\), since
\[
 \sigma-\frac K{\sqrt2}
   <\frac{26}{15}-\frac{(3+26/15)35}{99}
   =\frac{89}{1485}<\frac3{50}.
\tag{29}
\]
Here \(\sigma<26/15\), \(\sqrt2<99/70\), and the expression
is increasing in both radicals. The last reserve is \(1/14850\).

Also V is increasing: its derivative numerator is
\[
        (\sigma h/2-\beta)a+\sigma-h\beta
            =\frac{3(\sigma-1)}4a+\frac\sigma2>0.
\]
At \(a=2/5\), the bound \(\sigma<26/15\) gives numerator
\(>49/50\) and squared denominator \(<244/75<(181/100)^2\).
Thus on Q,
\[
                  V(a)>\frac{98}{181}>\frac{27}{50}.
\tag{30}
\]
The last unsquared reserve is \(13/9050\); the squared-denominator
reserve is \(683/30000\).

The three original unit radial vectors in (6) sum to zero. Equations
(27)--(30) therefore give the exact initial derivative bounds
\[
 \left.\frac{d}{d\tau}\Phi_0(o+\tau v)\right|_{\tau=0}
                                      <-\frac{12}{25},
\]
\[
 \left.\frac{d}{d\tau}\Psi(o+\tau v)\right|_{\tau=0}
                                        <\frac3{50}.
\tag{31}
\]
No numerical angle estimate is involved.

### Uniform second derivative along the full actual comparison segment

For a nonzero vector w,
\[
 \frac{d^2}{d\tau^2}|w-\tau v|
                   =\frac{\det(w,v)^2}{|w-\tau v|^3}.
\tag{32}
\]
The following six elementary bounds hold on Q and even on the larger
segment \(0\le\tau\le1/50\). They also prove that none of the
vectors in (32) vanishes along the segment.

For \(f_0=a e_0\), its dot product with v is \(-3a/2\), so
\(|f_0-\tau v|\ge a\), giving a second derivative at most
\(3/(4a)\le15/8\). For \(f_1=b e_1\), its dot product with
v is zero, giving a bound \(3/b\le15\). For \(f_2=e_2\),
\[
 |f_2-\tau v|^2=1-3\tau+3\tau^2\ge47/50>(24/25)^2,
\]
so its second derivative is less than
\((3/4)(25/24)^3<7/8\).

For g_1, its dot product with v is negative and
\(\det(g_1,v)=\beta a\). Since \(E(a,b)\ge a+b\) and
\(\beta<2/3\), its second derivative is less than
\[
 \frac49\frac{a^2}{(a+b)^3}\le\frac{80}{243}<\frac13.
\]
To check the maximum here, first decrease b to 1/5; the function
\(a^2/(a+1/5)^3\) is nonincreasing for \(a\ge2/5\).
For g_2, \(|\det(g_2,v)|=\beta\), and
\(E(1,b)>8/5\) because \(b\ge1/5\) and \(\sigma>5/3\).
Thus
\[
 |g_2-\tau v|>\frac85-\frac7{200}>\frac32,
\]
and its second derivative is less than \(32/243<2/15\).

Finally \(|g_0|=E(1,a)>7/4\). The displacement has norm at
most \(7/200\), so
\(|g_0-\tau v|>(49/50)|g_0|\). Using
\(\det(g_0,v)^2\le3|g_0|^2\), its second derivative is less than
\[
                  \frac{12}{7}(50/49)^3<2.
\]
All radical estimates used in this paragraph follow from
\(5/3<\sigma<7/4\). The bound \(E(1,a)>7/4\) follows, for
example, from \(a\ge2/5\) in its squared formula.

Adding the six bounds gives
\[
 \frac{d^2}{d\tau^2}\Phi_0(o+\tau v)
        <\frac{15}{8}+15+\frac78+\frac13+\frac2{15}+2
        =\frac{1213}{60}<21.
\tag{33}
\]
The functional \(\Psi\) omits only the varying g_0 norm and
adds a constant, so its second derivative has the same upper bound.

Integrating (31)--(33) to \(\tau=1/55\), we obtain
\[
 \Phi_0(o+v/55)<\Phi_0(o)-\frac{12}{1375}
                                  +\frac{21}{6050}
                    <\Phi_0(o)-\frac1{200},
\tag{34}
\]
\[
 \Psi(o+v/55)<\Psi(o)+\frac3{2750}+\frac{21}{6050}
                    <\Psi(o)+\frac1{200}.
\tag{35}
\]
The exact final reserves are respectively
\[
 \frac{12}{1375}-\frac{21}{6050}-\frac1{200}
                      =\frac{31}{121000}>0,
\]
\[
 \frac1{200}-\frac3{2750}-\frac{21}{6050}
                      =\frac{53}{121000}>0.
\tag{36}
\]

## 6. The two endpoints have the same valid comparison point

If \(G_0(a,b)>0\), use the original Fermat point o. Equation (8)
and the complete collapsed-endpoint theorem give both inequalities
in (4) there.

If \(G_0(a,b)\le0\), the global implication (20) puts the
point in Q, with \(G_0>-1/200\). Use the single displacement
\(x=o+v/55\). Equations (18),(34) give \(\Phi_0(x)<2P\).
Equations (24),(35) give \(\Psi(x)<2P\). Therefore (4) holds
at this one common point for every positive Fermat triple.

Applying norm convexity at this same x proves (5) simultaneously for
all \(\delta\in[0,1]\). No separate endpoint minimizers were
combined, and no original shared mean was selected or moved.

## 7. Every vertex, collinear and coincident alternative

If a Fermat point is a triangle vertex, the angle between its two
nonzero rays is at least 120 degrees. This is the original sum-of-three-
distances subgradient condition; it includes an angle of 120 degrees
and a collinear angle of 180 degrees. The point itself is common to
both endpoint comparisons below.

If \(o=f_0\), write \(b=|f_1-o|>0\), \(c=|f_2-o|>0\),
and \(d=|f_1-f_2|\). Here
\(\Phi_0(o)=\Psi(o)\), and the complete calculation is
\[
 d^2\ge b^2+bc+c^2\ge(b/2+c)^2,
\]
\[
 \Phi_0(o)=\Psi(o)\le3b+(1+2\sqrt2)c,
\quad
 2P-\Psi(o)\ge(3-2\sqrt2)c>0.
\tag{37}
\]
The norm estimate uses \(|g_1-o|=b\) and
\(|g_2-o|\le b+\sqrt2c\).

If \(o=f_2\), its collapsed endpoint has the reflected bound
\(2P-\Psi(o)\ge(3-2\sqrt2)|f_0-o|>0\), while
\(\Phi_0(o)<\Psi(o)\), because its variable g_0 norm is
\(|f_0-o|\) instead of \(\sqrt2|f_0-o|\).

If \(o=f_1\), put \(a=|f_0-o|>0\), \(c=|f_2-o|>0\),
and \(d=|f_0-f_2|\). For the collapsed endpoint,
\[
 \Psi(o)=(1+\sqrt2)(a+c)+\sqrt2d,
 \quad d\ge\frac{\sqrt3}{2}(a+c)>rac{a+c}{\sqrt2},
\]
so \(\Psi(o)<2P\). For the other endpoint, the triangle
inequality gives
\[
 \Phi_0(o)\le(2+\sqrt2)a+(1+2\sqrt2)c.
\]
Both quantities in the following comparison are positive, and
\[
\begin{split}
 4d^2-\{\sqrt2a+(2\sqrt2-1)c\}^2
 &\ge2\{a-(1-1/\sqrt2)c\}^2+(6\sqrt2-8)c^2>0.
\end{split}
\tag{38}
\]
Thus \(\Phi_0(o)<2(a+c+d)=2P\) as well.

Every collinear triple of distinct points has a middle vertex which
is a Fermat point, so (37)--(38) include all such degenerate limits.
If two points coincide, take that common point as x. For the three
possible coincident pairs the larger of the two endpoint values is
respectively
\[
\begin{array}{c|c|c}
\text{Coincident pair}&\max\{\Phi_0(x),\Psi(x)\}&P\\ \hline
 f_0=f_1&(1+2\sqrt2)|f_2-x|&2|f_2-x|\\
 f_0=f_2&3|f_1-x|&2|f_1-x|\\
 f_1=f_2&(1+2\sqrt2)|f_0-x|&2|f_0-x|
\end{array}
\]
Each is strictly below \(2P\) when the triple is not constant.
If all three points coincide, \(P=0\) and both endpoint minima
are zero; only the non-strict zero statement holds. This is the only
constant exception, and it is absent from the physical force triangle.
Consequently the common-point theorem covers every nonconstant
counterclockwise or collinear triple, with all limits stated explicitly.

## 8. Exact physical join for the remaining mixed outgoing-share C6

Retain the original full physical domain of
`SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md`: all nine units,
physical unique-circle-corner masks at the three loaded units, all
positive original forces, the genuine outgoing share at unit 0, every
original shared-mean endpoint and all three side-transmitter sliders.
The canonical corner word is \(\chi=(1,1,0)\).

Use its unchanged vectors \(f_i=\mu_i n_i\), \(\mu_i>0\),
\(F_i=f_{i-1}-f_i\), and its original chord length
\(0<\ell_0\le1\). Set only
\[
                             \delta=1-\ell_0\in[0,1).
\]
The exact actual norm model is
\[
 g_0^\delta=f_2+JF_0-\delta f_0,\quad
 g_1=f_0+JF_1,\quad g_2=f_2+JF_2,
\]
\[
 u_0=g_0^\delta/|g_0^\delta|,\quad u_i=g_i/|g_i|\ (i=1,2).
\tag{39}
\]
All denominators are positive in the actual physical chart. Its
complete original contact equations imply the actual closure
\[
                   \sum_i n_i+\ell_0u_0+u_1+u_2=0
\tag{40}
\]
and the unchanged virial identity
\[
 R\sum_i|F_i|=\sum_i\mu_i+|g_0^\delta|+|g_1|+|g_2|
                                                   =\Phi_\delta(0).
\tag{41}
\]
These are precisely the norm, closure and virial identities in
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md` and the accepted five-scalar
compatibility source. Their use does not assert that closure and virial
alone reconstruct all individual channels; every actual channel remains
part of the original physical hypotheses.

For this fixed actual \(\delta\), the function \(\Phi_\delta\)
is convex in x. Equation (40) says exactly
\(\nabla\Phi_\delta(0)=0\), so the original force-plane origin
is a global minimizer. The actual force triangle is nondegenerate and
counterclockwise. For example its canonical normals put the three
forces at \((\mu_0,0)\), \((-\mu_1c_1,\mu_1s_1)\), and
\((-\mu_2c_0,-\mu_2s_0)\), with every displayed coefficient
positive, making the signed triangle determinant strictly positive.
In particular \(P=\sum_i|F_i|>0\).

The complete common-point theorem therefore supplies an x with
\(\Phi_\delta(x)<2P\). Combining it with the exact minimum and
virial gives
\[
                      RP=\Phi_\delta(0)
                          \le\Phi_\delta(x)<2P,
 \qquad\boxed{R<2.}
\tag{42}
\]
This is a whole original-orbit bound, with no force-ratio or angular
box premise. The comparison point x is a point in an auxiliary convex
force functional; it is not a motion of a physical unit or a change of
any actual application mean.

The original radius window for every remaining core is now reduced to
\(79/40\le R<2\). This supplies the radius hypothesis of the
conditional pocket-0 capacity theorem, but does not by itself prove
that theorem's remaining coordinate hypotheses. The three-extra-square
completion and every still-open allocation remain explicit. No broader
geometric gate, inherited matrix certificate, Lean theorem or CI result
is claimed closed by this radius bound alone.
