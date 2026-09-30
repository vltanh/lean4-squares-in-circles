# Analytic diagonal remainder and cardinal-frame refinement

This note records the mathematical arguments used by the new analytic Lean
modules. It does not use any numerical certificate or subdivision table.
It proves two components, not the whole six-square theorem: the diagonal
remainder on its stated angle domain, and the cardinal facing-angle refinement
once the broad chart bounds are available. Obtaining those hypotheses from an
arbitrary packing without the remaining computational arguments is still work
for the full human-analytic proof. Lean compilation remains deferred.

## 1. Constants and exact bounds

Write

\[
h=\sqrt2/2,\quad A=(1466+1940h)/267,\quad B=(327+432h)/712,
\]
\[
s_*={2B\over A+\sqrt{A^2-4B}},\qquad
 t_*=(-20+30h)s_*+{7\over2}-{9h\over2},
\]
\[
q_*=2s_*^2+4s_*+{5\over2},\quad R=\sqrt{q_*},\quad
\rho=\sqrt{q_*-1/4}-1/2,
\]
\[
r={s_*+1/2\over s_*+3/2},\quad k={t_*+1/2\over3/2-s_*},\quad
m=(1+r)k,\quad K=2hm.
\]

The following deliberately coarse bounds suffice:

\[
{251\over200}<K<{253\over200},\qquad
{8\over5}<R<{1689\over1000},\qquad
{111\over100}<\rho<{1113\over1000},\qquad
{139\over100}<K\rho<{141\over100}.
\tag{1}
\]

These are algebraic estimates, not interval certificates. Here is the route
used in `Analytic/CandidateBounds.lean`. The defining quadratic
\(p(s)=s^2-As+B\) vanishes at \(s_*\), and \(0<s_*<1/5\), \(A>10\).
Its value at \(421/5000\) is positive, as direct substitution and rational
bounds for \(h\) show. If \(s_*\le421/5000\), then

\[
p(421/5000)-p(s_*)=(421/5000-s_*)(421/5000+s_*-A)\le0,
\]

a contradiction. Thus \(421/5000<s_*<17/200\). Substitution in the affine
formula for \(t_*\) gives \(21/50<t_*<211/500\). In particular,

\[
{73\over198}<r<{117\over317},\qquad
{115\over177}<k<{922\over1415},
\]
\[
{31165\over35046}<m<{400148\over448555}.
\]

Multiplying by rational bounds for \(2h\) proves the bounds for \(K\).
The identity \(\rho^2+\rho+1/2=q_*\), or directly the positive square root,
gives the bounds for \(\rho\). Finally \(q_*<142559/50000\) gives the upper
bound for \(R\); the lower bound follows from \(\rho>111/100\). Multiplying
the positive bounds gives the last pair of inequalities in (1).

Put \(d_*=1/2+h-t_*\). The candidate radius identities give
\(\rho=2hd_*\). Hence the pair-base constant satisfies the exact identity

\[
2\,\mathrm{pairBase}=2m(1/2-t_*)=K(\rho-1).
\tag{2}
\]

## 2. Exact diagonal geometry and the support switch

Assume

\[
-11/25\le w\le2/5,\qquad -2/5\le s\le11/25,\qquad
1/2\le d\le\pi/4.
\tag{3}
\]

Set

\[
\beta=(w-s)/2,\qquad \delta=d-\pi/4-(w+s)/2,\qquad Z=|w|+|s|.
\]

Then \(-11/25\le\beta\le2/5\), \(|\delta|\le71/100\), and
\(d-w,d-s\in[0,\pi/2]\). The elementary estimates
\(\cos x\ge1-x^2/2\) and \(|\sin x|\le|x|\) imply

\[
\cos\beta-\sin\beta>0,\qquad
\cos\delta>0,\qquad |\sin\delta|\le\cos\delta.
\]

The actual diagonal force is

\[
g=K(\cos\beta-\sin\beta)(\cos\delta,-\sin\delta).
\]

Its norm is \(L=K(\cos\beta-\sin\beta)>0\). The exact constrained-disk
support condition \(2R\min(|g_x|,|g_y|)\le|g|\) is therefore

\[
2R|\sin\delta|\le1.
\tag{4}
\]

The fact that the first force coordinate is larger does NOT select the cap
branch; (4) does. The scalar diagonal contribution is

\[
D_{\rm cap}=K((1-\rho)\cos\beta+\rho\sin\beta)\cos\delta
\]

on (4), and

\[
D_{\rm vertex}=K\left(
{3\cos\beta-\sin\beta\over2}\cos\delta+
{\cos\beta-\sin\beta\over2}|\sin\delta|
-R(\cos\beta-\sin\beta)\right)
\]

on the vertex branch. These identities are proved by angle addition and the
exact support formula in `Stress/DiagonalFormula.lean`.

The remainder to prove nonnegative is

\[
\mathcal D=\mathrm{pairLine}(w)+\mathrm{pairLine}(-s)+D+2\,\mathrm{pairBase},
\]

where

\[
\mathrm{pairLine}(x)={73\over100}\max(-x,0)-{13\over50}\max(x,0),
\]
\[
\mathrm{pairLine}(w)+\mathrm{pairLine}(-s)
={47\over200}Z-{99\over100}\beta.
\tag{5}
\]

## 3. Cap branch

Let \(T=K\rho\) and

\[
P=K(\rho-1)(1-\cos\beta\cos\delta)\ge0.
\]

By (2) and (5), the cap remainder is

\[
\mathcal D_{\rm cap}={47\over200}Z-{99\over100}\beta
+T\sin\beta\cos\delta+P.
\tag{6}
\]

If \(\beta\le0\), then \(\sin\beta\cos\delta\ge\beta\).
Since \(T<141/100\), and \(2|\beta|\le Z\), (6) gives

\[
\mathcal D_{\rm cap}\ge {47\over200}Z+{42\over100}\beta\ge Z/40.
\]

If \(\beta\ge0\), put \(q=\beta^2/6+\delta^2/2\). The domain gives
\(0\le q\le16723/60000\). The sine and cosine Taylor inequalities give

\[
\sin\beta\cos\delta\ge\beta(1-q).
\]

One way to obtain this product inequality without multiplying inequalities
of uncertain sign is to add the nonnegative products
\((\beta-\sin\beta)(1-\cos\delta)\) and
\(\beta(\cos\delta-1+\delta^2/2)\) to
\(\sin\beta\ge\beta-\beta^3/6\).

By (1), \(T-99/100-Tq>0\). Thus (6) again gives
\(\mathcal D_{\rm cap}\ge Z/40\).

Equality therefore forces \(w=s=0\). Equation (6) then reduces to
\(K(\rho-1)(1-\cos(d-\pi/4))=0\). Its coefficient is positive, and
\(1-\cos z\ge z^2/5\) for \(|z|\le\pi\); hence \(d=\pi/4\).
This is `Stress/DiagonalCapBound.lean`.

## 4. Vertex branch: the diamond, not a box partition

Write

\[
X=|(w+s)/2|,\qquad Y=|\beta|,\qquad t=|\delta|.
\]

The change of coordinates gives

\[
X+Y=\max(|w|,|s|)\le11/25,\qquad
2\max(X,Y)\le Z.
\tag{7}
\]

The vertex premise \(1\le2R|\sin\delta|\), the radius bound (1), and
\(|\sin\delta|\le t\) imply \(t\ge29/100\). The upper bound on \(d\)
and \(\pi<22/7\) give

\[
29/100\le t\le2/7+X<3/4.
\tag{8}
\]

Let

\[
A(t)={3\over2}\cos t+{1\over2}\sin t-R,\qquad
B(t)=R-(\cos t+\sin t)/2.
\]

The unit-circle identity proves
\(3\cos t/2+\sin t/2\le8/5\) and \(\cos t+\sin t\le3/2\).
Consequently \(A(t)\le0\), \(B(t)\ge17/20\), and \(KB(t)\ge17/16\).
Since \(A\cos\beta\ge A\), it remains to control the signed sine term.
For \(\beta\le0\), use \(\sin\beta\ge\beta\). For \(\beta\ge0\),
use \(\sin\beta\ge(23/24)\beta\), valid for \(0\le\beta\le1/2\),
and
\((17/16)(47/24)>198/100\). Both signs yield

\[
-{99\over100}\beta+KB\sin\beta
\ge {99\over100}Y-KBY.
\]

Using (7), \(47/100\ge(37/100)K\), \(99/100\ge(39/50)K\), and (1),
we obtain \(\mathcal D_{\rm vertex}\ge K F(X,Y,t)\), where

\[
F={37\over100}\max(X,Y)+{39\over50}Y+
\left({3\over2}+{Y\over2}\right)\cos t+
\left({1\over2}+{Y\over2}\right)\sin t
-{1689\over1000}(1+Y)+{111\over100}-1.
\tag{9}
\]

Thus it suffices to prove \(F>0\) on the diamond (7) and interval (8).

## 5. Concavity reduces the angle to two endpoints

For fixed \(X,Y\), the second derivative of (9) with respect to \(t\) is

\[
-\left({3\over2}+{Y\over2}\right)\cos t
-\left({1\over2}+{Y\over2}\right)\sin t\le0.
\]

Therefore the minimum occurs at \(t=29/100\) or \(t=2/7+X\).
Define

\[
b(t)={3\over2}\cos t+{1\over2}\sin t-{1579\over1000},\qquad
p(t)={909\over1000}-{\cos t+\sin t\over2}.
\]

Then \(F=b(t)+(37/100)\max(X,Y)-p(t)Y\). On \([2/7,3/4]\),

\[
0\le p(t)\le37/100.
\tag{10}
\]

For the upper bound in (10), Taylor's inequalities give
\(\cos t+\sin t\ge1+t/2\): indeed
\(1/2-t/2-t^2/6\ge0\) for \(0\le t\le3/4\).
The lower bound follows from \(\cos t+\sin t\le3/2\).

At \(t=29/100\), the max/penalty terms are nonnegative, and the same Taylor
bounds give

\[
b(29/100)\ge {10711\over12000000}>0.
\]

At \(t=2/7+X\), (10) shows that the least possible value of the max/penalty
term occurs at

\[
Y=\min(X,11/25-X).
\]

This creates exactly two cases, with the geometrically forced boundary
\(X=11/50\). It is not a numerical partition chosen by a search.

## 6. Two quartic chord inequalities

Put \(T=2/7+X\). Replacing cosine by \(1-T^2/2\) and sine by \(T-T^3/6\)
is valid because their coefficients are nonnegative. The two lower polynomials
are

\[
f_1(T)=-{19\over280}+{2227\over7000}T-{5\over28}T^2
-{13\over42}T^3-{1\over12}T^4,
\quad {2\over7}\le T\le{177\over350},
\]
\[
f_2(T)=-{21067\over43750}+{11493\over7000}T-{501\over350}T^2
+{223\over2100}T^3+{1\over12}T^4,
\quad {177\over350}\le T\le{127\over175}.
\]

For a quartic \(f(x)=a_0+a_1x+a_2x^2+a_3x^3+a_4x^4\), direct expansion gives

\[
(u-l)f(x)=(u-x)f(l)+(x-l)f(u)-(u-l)(x-l)(u-x)Q(x),
\]
\[
Q(x)=a_2+a_3(x+l+u)+a_4(x^2+(l+u)x+l^2+lu+u^2).
\tag{11}
\]

For \(f_1\), all the displayed higher coefficients are negative and all
arguments are nonnegative, so \(Q\le0\). For \(f_2\), all three arguments
are at most \(3/4\), hence

\[
Q\le-{501\over350}+{223\over2100}{9\over4}+{1\over12}{27\over8}
=-{5103\over5600}<0.
\]

The endpoint arithmetic is explicit:

\[
f_1(2/7)={709\over1029000}>0,
\]
\[
f_1(177/350)=f_2(177/350)={16124279\over8575000000}>0,
\]
\[
f_2(127/175)={2548159\over128625000}>0.
\]

Equation (11) now proves positivity throughout both intervals. Consequently
\(F>0\) and \(\mathcal D_{\rm vertex}>0\), including the cap/vertex wall.
Combining with the cap result proves

\[
\mathcal D\ge0,\qquad
\mathcal D=0\Longrightarrow w=s=0,\ d=\pi/4.
\]

The Lean chain is `Analytic/EndpointReduction.lean`, `VertexMinorant.lean`,
`DiagonalVertex.lean`, then `Stress/DiagonalVertexBound.lean` and
`DiagonalRemainder.lean`. The old diagonal check is only a compatibility import.

## 7. A separate analytic replacement for six cardinal-angle checks

Let a contained square have local center \((a,b)\), with
\(|a|\le\rho_0\), \(|b|<1/2\), and lie in a cap of depth
\(h\ge c_{\rm core}=3/2-\rho_0\). Suppose its primary phase relative to the
cap normal belongs to \([-3\pi/4,3\pi/4]\), as the broad labelled windows ensure.

Inside \([-\pi/4,\pi/4]\), the existing analytic cap support gives
\(|t|<2/5\). Outside this interval, a quarter-turn of the SIDE FRAME puts the
cap angle in that interval but makes the short coordinate \(\pm b\) primary.
Denote the resulting coordinates by \((a',b')\). Then \(|a'|<1/2\),
\(|b'|\le\rho_0\), and the cap bound again gives \(|\sin t'|<2/5\).
The exact cap half-plane inequality implies

\[
h\le(|a'|-1/2)\cos t'+(|b'|-1/2)|\sin t'|
\le(\rho_0-1/2){2\over5}<{77\over200}<c_{\rm core},
\]

a contradiction. Thus the cap necessarily faces the primary frame and its
angle is below \(2/5\). This is `Analytic/CardinalFrame.lean`; its four cardinal
coordinate instances replace the six checks in `Normalization/CardinalWindows`.
No global reflection is spent. The prior broad-window and strong-core
construction remains a separate analytic obligation.
