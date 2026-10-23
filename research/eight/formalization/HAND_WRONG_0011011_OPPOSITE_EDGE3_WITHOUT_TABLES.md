# The whole opposite outer edge-3 family without derivative tables

This note replaces all continuous derivative tables in
`../WRONG_0011011_EDGE3_OPPOSITE_AXES12_HAND_PROOF.md` and
`../WRONG_0011011_EDGE3_OPPOSITE_AXES34_HAND_PROOF.md`.
Together with their analytic contact reductions, it proves the entire
outer/outer edge-3 \((-,+)\) family, and its reflected edge-5 family:

\[
 C=\phi-T(b)-L(B)>.89777>.89765,
 \qquad0\le b,B\le d,\quad |\phi-\pi/2|\le .7.                \tag{1}
\]

All four original signed separating axes, both angle halves, and all
closed boundary ties are included. The result uses no coordinate
mesh, interval cover, or verifier output.

Every terminating decimal denotes an exact rational. The common data are

\[
 Q=9789/2500,\quad a(y)=\sqrt{Q-(y+.5)^2}-.5,
 \quad d=\sqrt{Q/2}-.5,\quad b_1=\sqrt{Q-2.25}-.5,
\]
\[
\begin{aligned}
 T(y)&=.01670+2.42322y-.91744y^2-.95769a(y)y,\\
 L(y)&=.03965+3.85510y-1.49748y^2-1.89442a(y)y.
\end{aligned}
\]

The elementary derivative identities in the two parent notes give
\(T''',L'''>0\), with both third derivatives increasing. In particular
\(T'''>1.6\), \(L'''>3.17\), \(T'<1.069\), and
\(.624<L'<1.176\). Those facts are consequences of their printed
radical formulas, not of the tables being replaced.

## 1. Both aligned contacts have whole-domain positive curvature

### 1.1. The first aligned contact

Write \(u=a(B)+.5\), \(v=B+.5\), \(r=v/u\), and
\(j=a(B)-1=u-1.5\). The first aligned cost is

\[
 H_{12}(B)=\pi/2-T(j)-L(B),\qquad0\le B\le b_1.
\]

Its third derivative is

\[
 H_{12}'''=T'''(j)r^3-3T''(j)rr'+T'(j)r''-L'''(B),
 \quad r'=Q/u^3,\quad r''=3Qv/u^5.
\]

Here \(0\le j<.415\), so \(T'''(j)<2.34\),
\(-T''(j)<1.335\), and \(T'(j)<1.069\).
Multiplication by \(u^5/(3Q)>0\) gives the uniform estimate

\[
 \frac{u^5H_{12}'''}{3Q}
 <\frac{2.34(2.25)(1.291)^3}{3Q}
   +1.335\frac Q2+1.069(1.291)
   -1.89442(Q-.6455)<-1.23.                                  \tag{2}
\]

Indeed \(uv\le Q/2\), \(v<1.291\), and
\(u^2v^3=(Q-v^2)v^3\) increases up to the endpoint of this arc,
since \(v^2\le Q-2.25<3Q/5\). Its endpoint is at \(u=1.5\).
These observations justify every bound in (2) over the full arc.

Thus \(H_{12}''\) decreases. Its single endpoint comparison is
\(H_{12}''(b_1)>.22\). At the rational point
\(B=.685356885\),

\[
 H_{12}>.8980812,\qquad |H_{12}'|<10^{-6}.
\]

Completing a square gives \(H_{12}>.89808\) everywhere.

### 1.2. The other aligned contact

For \(j=a(b)-1\), define

\[
 A(b)=L'(j)-.95769b.
\]

Since \(j<a(0)-1<.4146\), \(L''(j)<-.45\).
Consequently

\[
 A''=L'''(j)r^2-L''(j)r'>.45(.557)>.25.
\]

At \(b=.5781\), direct substitution gives
\(A>.343739\), \(|A'|<.0001\). A square completion proves
\(A>.34\) on the entire \([0,b_1]\).

The second aligned contact therefore satisfies

\[
\begin{aligned}
 H_{34}''
 &=-T''(b)-L''(j)r^2+L'(j)r'\\
 &=1.83488-1.91538r-L''(j)r^2+A(b)r'\\
 &>2.00488-1.91538r+.705r^2>.87.                              \tag{3}
\end{aligned}
\]

For the last line, \(r<.861\) and
\(r'=(1+r^2)^{3/2}/\sqrt Q>\tfrac12(1+\tfrac32r^2)\).
The displayed quadratic decreases on \([0,.861]\) and has value
greater than \(.878\) at its right endpoint.

At \(b=.59709465\),
\(H_{34}>.8977817\), \(|H_{34}'|<10^{-6}\).
Equation (3) proves \(H_{34}>.89778\) everywhere.
This replaces both aligned derivative tables.

## 2. Inverse-contact curvature on the whole first lower half

The lower secondary contact has the form

\[
 (a(y)-.5)\cos x-(y+.5)\sin x=z,
 \qquad z\ge .5.
\]

Write

\[
 u=a(y)+.5,\quad r=(y+.5)/u,\quad q=Q+1-2u,
 \quad w=\sqrt{q-z^2},\quad t=z/w,\quad f=-x.
\]

Let \(f_1=(Q-u)/(uq)\), and let its primes mean derivatives in
\(u\). Set

\[
 X=-r'f_1'+r^2f_1'',\quad
 A_1=\frac{9rr'}{q^2}-\frac{15r^3}{q^3}-\frac{r''}{q},
 \quad A_3=\frac{3rr'}{q^2}-\frac{10r^3}{q^3}.
\]

Straight differentiation gives the convenient identities

\[
 f_{yy}=-rf_1'+\frac{r^2}{q^2}t^3
                   +\left(\frac{3r^2}{q^2}-\frac{r'}q\right)t,
                                                               \tag{4}
\]
\[
 f_{yyy}=X+A_1t+A_3t^3-\frac{3r^3}{q^3}t^5.                 \tag{5}
\]

Also \(f_z=1/w\), \(f_{zz}=z/w^3\), and \(f_{zy}=-r/w^3\).
The partial fractions

\[
 f_1=\frac{Q}{(Q+1)u}+\frac{Q-1}{(Q+1)q}
\]

give \(f_1''=2Q/[(Q+1)u^3]+8(Q-1)/[(Q+1)q^3]\).
These formulas make it possible to prove derivative shape on each
entire minimum regime without subdividing either state coordinate.

### 2.1. A uniformly convex rectangle

For lower axis 1, take \(y=B\), \(z=b+.5\).
The original monotone reduction leaves the rectangle
\(0\le b\le .1\), \(0\le B\le .4\).
Throughout it,

\[
\begin{gathered}
 1.762<u<1.915,\quad .261<r<.511,\quad r'<.716,
 \quad r''>.228,\\
 1.0856<q<1.3916,\qquad0<t<.705.
\end{gathered}
\]

Here \(f_1'>0\). The preceding formulas give directly

\[
 X<1.045,\qquad A_1<2.532,\qquad A_3<.866.
\]

For example, an upper bound for \(A_1\) is

\[
 \frac{9(.511)(.716)}{1.0856^2}
 -\frac{15(.261)^3}{1.3916^3}-\frac{.228}{1.3916}<2.532;
\]

the other two bounds follow by the same single substitution into
their displayed formulas. Thus (5) gives

\[
 f_{BBB}<1.045+.705(2.532)+(.705)^3(.866)<3.14<L'''(B).
                                                               \tag{6}
\]

It follows that \(C_{BB}\) decreases with \(B\) at every fixed
\(b\) in the rectangle. At \(B=.4\), (4) gives

\[
 C_{BB}>.33574+.13478t^3-.10997t,
 \qquad .468<t<.591.
\]

Hence, uniformly in \(b\),

\[
 C_{BB}>.33574+.13478(.468)^3-.10997(.591)>.28.               \tag{7}
\]

The mixed derivative has the stronger global bound
\(|C_{bB}|<.5\). To prove it, use \(w^2\ge q-.36\) and consider

\[
 p(u)=\tfrac14u^2(q-.36)^3-(Q-u^2).
\]

With \(s=u-1.8\), its exact expansion is

\[
 p=
 \frac{48792979389}{1562500000000}
 -\frac{8226392679}{156250000000}s
 +\frac{348466455869}{62500000000}s^2
 +\frac{30884037}{12500000}s^3
 -\frac{10833}{2500}s^4-2s^5.
\]

Since \(|s|<.115\),

\[
 p>.0312-.0527|s|+5.22s^2>.031>0.                           \tag{8}
\]

Squaring the positive quantities in the mixed derivative reduces
\(|C_{bB}|<.5\) exactly to (8).
The original uniform bound \(C_{bb}>1.5\) also follows immediately
from \(C_{bb}=z/w^3-T''(b)\).
Since

\[
 (1.5-.01)(.28-.01)-.5^2>0,
\]

the Hessian is greater than \(.01I\) throughout this rectangle.
At its single reference \((b,B)=(.05878084,.33400286)\),
\(C>.8977764\) and both first derivatives have magnitude below
\(10^{-6}\). The resulting square completion proves
\(C>.89777\) on the whole rectangle.

### 2.2. The remaining stationary points are absent

For \(.4\le B\le .5\), the original check
\(C_b(.105,.5)>.0014\), together with \(C_{bb}>0\) and
\(C_{bB}<0\), forces \(b<.105\) at any stationary minimum.
It therefore suffices to prove

\[
 D(B)=f_B(.105,B)-L'(B)>0.
\]

Use (5) at the fixed free coordinate \(z=.605\).
On this entire range,

\[
\begin{gathered}
 1.707<u<1.763,\quad .510<r<.586,\quad
 1.3896<q<1.5016,\quad t<.599,\\
 X<.718,\qquad A_1<1.150,\qquad A_3<.325.
\end{gathered}
\]

Equation (5) gives \(f_{BBB}<1.477\), whereas
\(L'''(B)\ge L'''(.4)>4.5\). Thus \(D''<0\).
Its two endpoint values satisfy
\(D(.4)>.0061\) and \(D(.5)>.0152\), so concavity proves \(D>0\)
throughout. This replaces the three interior endpoint comparisons.

For \(B\ge .5\), use the full physical contact condition
\(z\le u-1\), which implies \(w\ge B+.5\ge1\).
Consequently

\[
 1.5\le u<1.708,\quad .585<r<.861,\quad
 1.4996<q\le1.9156,\quad t<.709.
\]

Now \(-r'f_1'<.036\), \(r^2f_1''<1.394\),
\(A_1<3.150\), and \(A_3<1.049\).
For the first bound, use \(f_1''>0\), the endpoint \(u=1.5\),
and \(r'<1.161\). For the \(A_1\) substitution retain the sharper
\(r'\le Q/(1.5)^3\); the resulting upper bound is below
3.148705. The other bounds are single substitutions into the same
formulas. Therefore

\[
 f_{BBB}<.036+1.394+.709(3.150)+(.709)^3(1.049)<4.04
                 <L'''(.5).                                \tag{9}
\]

At \(B=.5\), the cubic expression (4), after subtraction of
\(L''(.5)\), is convex in \(t>0\). Its two physical endpoints
\(z=.5\) and \(z=u-1\) give values below \(-.1339\) and
\(-.1110\), respectively. Thus \(C_{BB}<-.11\) there, for every
physical free coordinate. At fixed \(z\), the path back from any
larger physical \(B\) to \(.5\) remains physical. Equation (9)
therefore gives \(C_{BB}<0\) on the full remaining contact surface.
No interior minimum can occur there.

These arguments replace all of the first lower half's curvature
tables. The parent's boundary motions lead only to the convex
rectangle or the aligned contacts already proved in Section 1.

## 3. The other primary upper half is concave in its target

For upper axis 2, the original contact reductions first reduce to
alignment, the target diagonal, or \(b\le .1\), \(B>.664\).
We supply whole-domain bounds for both remaining curvature statements.

On the target diagonal, the inverse-contact expression in the parent is

\[
 J''=-rf_1'(u)+\frac{z_0}{q\sqrt{q-z_0^2}}
 \left(r'-\frac{2r^2}{q}-\frac{r^2}{q-z_0^2}\right)-T''(b),
 \qquad z_0=d-.5.
\]

For \(b\le .1\), \(r<.319\), \(r'>.557\), and

\[
 r'-\frac{2r^2}{q}-\frac{r^2}{q-z_0^2}
 >.557-\frac{2(.319)^2}{1.0856}-\frac{(.319)^2}{.9256}>0.
\]

The uniform bound \(rf_1'<1/4\) is proved in Section 1 of
`HAND_WRONG_0011011_OPPOSITE_EDGE2_WITHOUT_TABLES.md` by one circle
support inequality and an explicit quintic. Also
\(T''(b)\le T''(.1)<-1.169\). Hence \(J''>.9\) on this whole
initial domain. The parent's single reference
\(b=.00542853\), with \(J>.8977735\), \(|J'|<10^{-6}\), still
gives \(J>.89777\). Its subsequent monotonicity proof for \(b\ge.1\)
is already analytic.

For the remaining target curvature, set

\[
 U=a(B)+.5,\quad z=U-1,\quad \rho=(B+.5)/U,
 \quad w^2=Q+1-2(a(b)+.5)-z^2.
\]

On the entire enlarged rectangle
\(0\le b\le.1\), \(.664\le B\le d\),

\[
 1.399<U<1.601,\quad .399<z<.601,\quad \rho\le1,
 \qquad w>.85.
\]

The exact derivatives are

\[
 C_{BB}=\frac Q{U^3w}-\frac{z\rho^2}{w^3}-L'',
\]
\[
 C_{BBB}=
 \frac{3Q\rho}{U^4w}
 +\frac{\rho(\rho^2-3Qz/U^3)}{w^3}
 +\frac{3z^2\rho^3}{w^5}-L'''.                               \tag{10}
\]

The middle numerator is negative, since
\(3Q(.399)/(1.601)^3>1.14>\rho^2\). Thus

\[
 C_{BBB}<\frac{3Q}{1.399^4(.85)}
                 +\frac{3(.601)^2}{(.85)^5}-7.06<0,
\]

using \(L'''(.664)>7.06\).
At \(B=.664\), the coordinate formulas give
\(Q/U^3<.956\), \(z\rho^2>.3175\), \(L''>.963\),
and \(w<.886\). Consequently

\[
 C_{BB}<.956/.85-.3175/(.886)^3-.963<-.29.                    \tag{11}
\]

By (10), (11) extends to every larger target coordinate in the
rectangle. This proves the required fixed-source concavity throughout,
replacing all three target-curvature rows. Its endpoints are the
aligned contact and target diagonal, both already covered.

## 4. The interior critical curve on the other lower secondary axis

For lower axis 3, the free coordinate is \(z=B+.5\), while the
underlying outer coordinate in (4) is \(b\).
The parent's strictly convex minimization in \(B\) produces a unique
critical curve characterized by

\[
 q(b)=S(B):=(B+.5)^2+\frac1{L'(B)^2}.                         \tag{12}
\]

The physical curve exits at the unique \(b_*\in(.5,.6)\)
where it meets alignment. For \(b\ge b_*\), the aligned minimum
applies. These reductions use only the signs \(L'>0,L''<0\) on
the relevant target range and the two exit derivative signs.

There is no need to enclose (12) on six source intervals. The two
endpoint comparisons
\(S(.03)<q(0)\), \(S(.15)>q(.6)\), and strict monotonicity of
\(S\) show that its smooth continuation on all of \([0,.6]\)
satisfies

\[
                         .03<B(b)<.15.                       \tag{13}
\]

### 4.1. A one-variable envelope removes the critical-curve mesh

Write \(p=L'(B)\), \(l=L''(B)\), \(z=B+.5\), and

\[
 h=zp,\quad D=z-l/p^3,\quad q=z^2+p^{-2}.
\]

Define the target envelope locally along (12) by

\[
 g(q)=-\arccos(z/\sqrt q)-L(B).
\]

The stationarity equation eliminates derivatives of \(B\) from its
first derivative. Derivatives of \(h,D\) in the next display are
with respect to \(B\), while the derivatives of \(g\) are in \(q\):

\[
\begin{aligned}
 g'&=-h/(2q),\\
 g''&=h/(2q^2)-h'/(4qD),\\
 g'''&=-h''/(8qD^2)+h'/(2q^2D)
                      +h'D'/(8qD^3)-h/q^3,\\
 h'&=p+zl,\qquad h''=2l+zL''',\qquad
 D'=1-L'''/p^3+3l^2/p^4.
\end{aligned}                                                \tag{14}
\]

On the whole interval in (13), the radical derivative formulas give

\[
 .911<p<1.117,\quad -1.910<l<-1.506,
 \quad3.225<L'''<3.504,\quad .53<z<.65.
\]

Thus \(-2.112<h''<-.734\), so \(h'\) decreases. Its endpoint
values give \(-.069<h'<.105\). Concavity of \(h\) gives
\(h>.591\) from its two endpoints. Integrating \(h'<.105\)
from \(.03\), where \(h<.592\), also gives \(h<.605\).

Moreover \(-l-1.5p\) decreases, because its derivative is
\(-L'''-1.5l<0\), and it is still positive at \(B=.15\).
It follows that

\[
 D-1.5q=z(1-1.5z)+\frac{-l-1.5p}{p^3}>0.                   \tag{15}
\]

We also have \(0<D'<8.6\). Positivity follows from
\(3l^2>pL'''\). For the upper bound, \(-l/p^2\) increases,
since \(2l^2>pL'''\); its right endpoint is less than \(1.816\).
Hence

\[
 D'<1+3(1.816)^2-3.225/(1.117)^3<8.6.
\]

Using (15) in (14) proves the useful uniform bounds

\[
 g'<0,\qquad q^2g''<.605/2+.069/6<.315,\qquad g'''<0.       \tag{16}
\]

For the last sign, \(D>1.5q>1.59\), so

\[
 q^3g'''<
 \frac{2.112}{18}+.105/3
             +\frac{.105(8.6)}{18(1.59)}-.591<0.
\]

### 4.2. A single derivative sign controls the full reduced minimum

Let \(\alpha(b)=\arctan((b+.5)/(a(b)-.5))\). Its derivative is
\(\alpha'=f_1\). The reduced cost along (12) is

\[
 R(b)=\pi/2+\alpha(b)+g(q(b))-T(b).
\]

Since \(q'=2r\), \(q''=2r'\), \(q'''=2r''\),

\[
 R'''=X-T'''+8r^3g'''+12rr'g''+2r''g'.                     \tag{17}
\]

Here \(X=\alpha'''\) is the rational function

\[
 X=\frac Q{Q+1}\left(\frac{r'}{u^2}+\frac{2r^2}{u^3}\right)
 -\frac{2(Q-1)}{Q+1}
                    \left(\frac{r'}{q^2}-\frac{4r^2}{q^3}\right).
\]

On \(0\le b\le.6\), \(1.644<u<1.915\), and \(X<.55\).
Here is one polynomial proof of that entire-domain bound. Substitute
\(r^2=(Q-u^2)/u^2\), \(r'=Q/u^3\), and set
\(P(u)=(.55-X)u^5q^3\). With \(s=u-1.644\in(0,.271)\),
ordinary expansion gives

\[
 P(1.644+s)>
 1.56+s\{106.91-163.75s-39.362s^5-25.426s^6-4.4s^7\}>0.    \tag{18}
\]

The discarded coefficients of degrees three, four, and five are
positive. The other exact coefficients are bounded in the indicated
directions; the eighth is exactly \(-4.4\). The last parenthesis
exceeds \(62\) even after replacing every occurrence of \(s\)
by \(.271\). This proves (18) by one polynomial identity, with no
source subdivision.

Also \(u^2q>3.98\): its derivative is
\(2u(Q+1-3u)<0\) on this interval, and its value at \(1.915\)
exceeds \(3.98\). Thus

\[
 \frac{rr'}{q^2}=\frac{Q(b+.5)}{u^4q^2}
                  <\frac{1.1Q}{3.98^2}<.273.
\]

Equations (16)--(18) now give on the full continued critical curve

\[
 R'''<.55-1.6+12(.273)(.315)<0.                             \tag{19}
\]

This replaces both six-row source/target brackets and all six
third-derivative rows. The remainder of the minimum argument uses
only two individual source points, not intervals of a covering.
At \(b=.5\), (12) gives
\(.12539102082<B<.12539102083\), and exact substitution gives
\(R''>.06\), \(R'>.00025\). By (19), \(R''>.06\) throughout
\([0,.5]\). At \(b=.495\), the corresponding root satisfies
\(.12421535815<B<.12421535816\), with
\(R>.89779\), \(|R'|<.0001\). A square completion gives

\[
 R>.89779-.0001^2/.12>.89777\qquad(0\le b\le.5).
\]

On \([.5,b_*]\), \(R'\) is concave and starts positive.
It cannot cross from a negative value back to a positive one.
Hence the minimum of \(R\) is at \(.5\) or \(b_*\); the latter
is the aligned contact in Section 1. This completes the full lower
axis-3 contact, including its curved exit.

## 5. The last upper-primary target ratio is globally concave

For upper axis 4 the last target-ratio function in the parent is

\[
 F(B)=c+r s-L'(B)V,
 \quad V=(u-1)c+(B+.5)s,\quad
 c=\cos(.7),\ s=\sin(.7),\quad .2\le B\le d.
\]

Write \(m=s-rc\). Its exact second derivative is

\[
 F''=r''s-L'''V-2L''m+L'r'c.
\]

On this whole outer arc,
\(u<1.851\), \(u^2<3.426\), \(B+.5<1.4\),
\(|L''|<3.3\), and \(|m|<.36\). The last two facts follow
from monotonicity and their two endpoints. The function
\(V=c\sqrt{Q-v^2}+sv-c\) is concave in \(v=B+.5\), and both
endpoints exceed \(1.10\). Hence \(V>1.10\) throughout.

Multiplication by \(u^5/Q>0\) now gives the single bound

\[
\begin{aligned}
 \frac{u^5F''}{Q}
 &<3(1.4)(.645)+1.176(3.426)(.765)
       +\frac{2(3.3)(.36)(1.851)^5}{Q}\\
 &\hspace{12mm}-3(1.89442)(Q-.7)(1.10)<-1.12<0.              \tag{20}
\end{aligned}
\]

Thus \(F\) is concave on the entire target range.
The endpoint comparisons \(F(.2)>.082\), \(F(d)>.0068\)
prove \(F>0\), which is the required positive derivative along
the retained active contact. This replaces its three derivative
intervals. The parent's remaining primary-height bounds and the
two contact motions for \(B\le.2\) already follow from whole-domain
convexity; no table is used in them.

## 6. Exhaustion and arithmetic

The two parent manuscripts explicitly retain the four signed axes.
Section 1 above supplies both aligned endpoints. Section 2 completes
all minimum and boundary alternatives for lower axis 1. Section 3
completes upper axis 2. Section 4 completes lower axis 3, and Section 5
completes upper axis 4. Upper axes 1 and 3 reduce monotonically to
alignment or their analytic zero-coordinate exit; lower axes 2 and 4
have uniformly positive angle derivatives. Those four unchanged
arguments use no derivative-range table. Together these statements
prove (1) on all eight original axis/angle halves.

Every point bound above is a substitution into a displayed radical
formula or one of the two exact aligned costs. Square-root bounds are
checked by squaring positive rational endpoints. Trigonometric point
values on \([0,.7]\) use adjacent alternating sine/cosine sums through
degrees 11/13 and 12/14. The two inverse-contact reference angles are
positive arctangents with argument below \(.31\), for which adjacent
alternating sums through 24 and 25 terms suffice. The two scalar roots
in Section 4 are bounded by evaluating the strictly increasing
function \(S\) at their stated rational endpoints. Thus no table of
continuous states, certificate generator, or numerical optimizer is
an input to this hand theorem.

The complete wrong-word contradiction still requires the other
radial/sign components and their cyclic label cancellation; this
pair theorem asserts exactly the family in (1).
