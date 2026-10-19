# Analytic replacements for the four-type scalar certificates

**Status.** This note removes every Bernstein-coefficient premise from
the L/L, L/M, and M/M whole-pair arguments, and both the Bernstein premise
and the nine-interval curvature mesh in the C/M argument. It does not
yet close G1: the other whole-pair
manuscripts have further scalar obligations. The geometric reductions,
labels, and original separating-axis cases in the cited manuscripts
are unchanged. No Lean code or recursive certificate is an input here.

All terminating decimals below denote exact rational numbers.

## 1. Two scalar lemmas

### 1.1 Loss of a trigonometric support function

Let

\[
 F(x)=C+x+A\cos x-B\sin x,\qquad A,B\ge0,
 \quad 0\le x\le\pi/2.
\]

Put \(r=\sqrt{A^2+B^2}\). If \(r\le1\), then \(F'\ge0\).
If \(r>1\), put \(y=\sqrt{r^2-1}\). Then

\[
 F(x)\ge F(0)-2(y-\arctan y)
          \ge F(0)-\frac{2y^3}{3}.                    \tag{1}
\]

Indeed, choose \(\delta\in[0,\pi/2]\) with
\(B=r\cos\delta\), \(A=r\sin\delta\). Then
\(F'=1-r\cos(x-\delta)\). Its negative part on the stated
interval is contained in the single interval
\(|x-\delta|<\eta\), where
\(\eta=\arccos(1/r)=\arctan y\). The integral of the negative
part over this entire interval is

\[
 \int_{-\eta}^{\eta}(r\cos t-1)\,dt
 =2(r\sin\eta-\eta)=2(y-\arctan y).
\]

Finally \(y-\arctan y=\int_0^y t^2/(1+t^2)\,dt\le y^3/3\).
This proves (1), including the zero-amplitude boundary cases.

### 1.2 Curvature of a circle support norm

Suppose

\[
 N(x)^2=a+b\sin x+c\cos x>0,
 \qquad a^2\ge b^2+c^2.
\]

Two differentiations give the exact identity

\[
 N''+\frac N4=\frac{a^2-b^2-c^2}{4N^3}.                \tag{2}
\]

In particular, for the norm of the difference between a fixed vector
of length \(\sqrt{p^2+q^2}\) and a rotating vector of length
\(\lambda\), the numerator in (2) is
\((p^2+q^2-\lambda^2)^2\). The identity applies on the entire
angle interval, without a subdivision or a sampled curvature bound.

We also use the elementary strong-convexity consequence

\[
 F''\ge m>0\Longrightarrow
 F(x)\ge F(z)+F'(z)(x-z)+\frac m2(x-z)^2
 \ge F(z)-\frac{F'(z)^2}{2m}.                           \tag{3}
\]

## 2. The complete L/L replacement

Use the constants and geometric support reductions of
`../LOW_LOW_WHOLE_PAIR_HAND_PROOF.md`:

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 u=.403875,\quad v=1.089065,\quad \beta=.18.
\]

The outer arc endpoints satisfy

\[
 1.41457<a_0<1.41458,\quad
 1.29874<a_1<1.29875,\quad b_1=a_1/4,
 \quad .30681<L_1<.30683.                              \tag{4}
\]

These are direct substitutions in
\((a+1/2)^2+(b+1/2)^2=Q\), with positive square roots.
The primary-axis regimes in Sections 3.1--3.2 of that manuscript
already use endpoint concavity only. The following arguments replace
all five polynomial rows in its Section 4.

### 2.1 Both full-circle support bounds

The two cases are

\[
 (\lambda,\varepsilon,z)=(.945,.00002,.96),\qquad
 (\lambda,\varepsilon,z)=(1,0,1.1).
\]

The actual scalar support is

\[
 G=x+.09+ua_0+(u+v+\lambda)/2-\varepsilon
     +(\lambda-.09)\sin x-.09\cos x-RN,
\]

where

\[
 N^2=u^2+v^2+\lambda^2+2\lambda(u\sin x-v\cos x).
\]

Set \(S_3=x-x^3/6\), \(S_5=S_3+x^5/120\),
\(C_4=1-x^2/2+x^4/24\), and
\(C_6=C_4-x^6/720\). Put

\[
\begin{split}
 T&=x+ua_0^-+(u+v+\lambda)/2-.91-\varepsilon
                 +(\lambda-.09)S_3+.09(1-C_4),\\
 V&=u^2+v^2+\lambda^2+2\lambda(uS_5-vC_6),
 \qquad P=T^2-QV,\qquad a_0^-=1.41457.
\end{split}                                               \tag{5}
\]

Then \(G-.91\ge T-R\sqrt V\). Throughout \([0,1.1]\),
\(T>0\): its constant term exceeds .88 and
\(S_3\ge0\), \(1-C_4\ge0\). It therefore suffices to prove
\(P>0\).

Here there is a uniform concavity argument, valid for every
\(.945\le\lambda\le1\) and \(0\le\varepsilon\le.00002\).
Write

\[
 T=t_0+t_1x+t_2x^2+t_3x^3+t_4x^4,
\]

where

\[
 t_0=\frac{326223567}{800000000}+\frac\lambda2-\varepsilon,
 \quad t_1=\lambda+.91,\quad t_2=.045,
 \quad t_3=-(\lambda-.09)/6,\quad t_4=-3/800.
\]

Expansion of (5) gives

\[
\begin{split}
 P''={}&2(t_1^2+2t_0t_2-Q\lambda v)\\
 &+6(2t_0t_3+2t_1t_2+Q\lambda u/3)x\\
 &+12(2t_0t_4+2t_1t_3+t_2^2+Q\lambda v/12)x^2\\
 &+20(2t_1t_4+2t_2t_3-Q\lambda u/60)x^3\\
 &+30(2t_2t_4+t_3^2-Q\lambda v/360)x^4
       +84t_3t_4x^5+56t_4^2x^6.
\end{split}                                               \tag{6}
\]

On the parameter rectangle just stated, the coefficients in (6)
give the single upper bound

\[
 P''<-1+\frac{51}{20}x-\frac{23}{10}x^2
  +x^3\left(-1+\frac{13}{40}x+
                  \frac6{125}x^2+\frac1{1250}x^3\right). \tag{7}
\]

For completeness, these coefficient bounds require no interval
checker: the constant and quadratic coefficients decrease with
\(\lambda\), the linear, quartic, and quintic coefficients increase,
and the cubic coefficient is a negative affine function of
\(\lambda\). Substitution at \(\lambda=.945,1\), using
\(.4077<t_0-\lambda/2<.4078\), gives respectively the seven
bounds displayed in (7). For the linear coefficient one may simplify
it first to
\(-\lambda^2+(.63-2C+2Qu)\lambda+.18C+.4914\),
where \(C=t_0-\lambda/2\); its derivative is positive on the
whole parameter interval. The other assertions follow immediately
from (6).

The quadratic on the right of (7) is strictly negative, because
\((51/20)^2<4(23/10)\). The expression in parentheses is negative
for \(0\le x\le11/10\), by substituting \(11/10\) in its three
positive terms. Hence \(P''<0\) on the complete interval.

It remains to check only its endpoints. At zero the two values are
greater than \(1/20\) and \(3/20\), respectively. The other
endpoint substitutions are, exactly,

\[
 P_{.945,.00002}(24/25)
 =\frac{3866007991357988342593}{250000000000000000000000}
 >\frac3{200},
\]

\[
 P_{1,0}(11/10)
 =\frac{33137867620677937}{5760000000000000000}
 >\frac1{200}.
\]

Concavity now gives \(P>0\) between the endpoints. This proves
both full-circle support bounds \(G>.91\).

### 2.2 Both endpoint-continuation bounds

For the same two triples \((\lambda,\varepsilon,z)\), the endpoint
support is

\[
 E(x)=x-\varepsilon-L_1+(\lambda+.18)/2
          +A\cos x-B\sin x,
\]

where
\(A=(\lambda-.18)/2+\lambda b_1\) and
\(B=\lambda a_1-(\lambda-.18)/2\).
On \([z,\pi/2]\), (4) gives

\[
 A<.735,\qquad B>.84,
 \quad E''=B\sin x-A\cos x
 >(.84)(.819)-(.735)(.574)>\frac14.                     \tag{8}
\]

At both permitted starting points,

\[
 E(z)>.918,\qquad E'(z)>-.06.                           \tag{9}
\]

These two inequalities follow directly from (4) and
\( .81919<\sin(.96)<.81920\),
\( .57351<\cos(.96)<.57352\),
\( .89120<\sin(1.1)<.89121\),
\( .45359<\cos(1.1)<.45360\).
The alternating Taylor polynomials through sine degrees 11/13 and
cosine degrees 10/12 prove all four brackets. For example the lower
values of \(E(z)\) obtained this way are
\(3675642376643/4000000000000\) and
\(18487057633/20000000000\); the lower derivative values are
\(-98438659/2000000000\) and \(-18527311/320000000\).

For \(x\ge z\), integration of (8)--(9) gives
\(E(x)>.918-.06(x-z)+(x-z)^2/8\). Completing the square gives

\[
 E(x)>.918-\frac{.06^2}{2(1/4)}=.9108>.91.              \tag{10}
\]

This replaces both endpoint-continuation Bernstein rows.

### 2.3 The remaining negative-target axial bound

The fifth support is

\[
 A_\lambda(x)=.557+x+.39\cos x-B\sin x,
 \quad B=.96a_0-.39<.969.
\]

Thus \(.39^2+B^2<1.1\). In (1), \(y<1/3\), and therefore

\[
 A_\lambda(x)>.947-\frac2{81}>.91
       \qquad(0\le x\le\pi/2).                         \tag{11}
\]

The other negative-target endpoint function was already strictly
increasing in the whole-pair manuscript. Equations (5)--(11)
therefore remove all five Bernstein rows from the complete L/L entry,
including all source signs, both original source axes, and their
reflected target-axis images. All intervals are closed.

## 3. The complete C/M scalar replacement

### 3.1 The full-circle bound is decreasing on a whole quadrant

Use

\[
 p=1.489593,\quad q=1.580219,\quad g=1.077372,
 \quad K_F=4.306667.
\]

The sole Bernstein row in
`../CORE_MID_WHOLE_PAIR_HAND_PROOF.md`, Section 7, bounds

\[
 F(x)=x+K_F+(g-.09)\sin x-.09\cos x-RN(x),
 \quad N^2=p^2+q^2+g^2+2g(p\sin x-q\cos x).             \tag{12}
\]

In fact \(F'<0\) throughout \([0,\pi/2]\).
Put \(z=\tan(x/2)\), \(D=1+z^2\), \(s_0=2z\),
\(c_0=1-z^2\), and

\[
 \mathcal N=(p^2+q^2+g^2)D+2g(ps_0-qc_0),
 \qquad J=D+(g-.09)c_0+.09s_0.
\]

The two quantities compared in the derivative have positive signs.
After multiplying their squared difference by \(D^3\), the
assertion \(F'<0\) is equivalent to positivity of

\[
 P(z)=Qg^2(pc_0+qs_0)^2D-J^2\mathcal N.                 \tag{13}
\]

This is a degree-six polynomial, and its exact rational expansion
has the coefficientwise lower bound

\[
 P(z)>.32+15z-\frac{25}{4}z^2-\frac{29}{4}z^3
                         +34z^4-43z^5+10z^6.
\]

This inequality follows by direct expansion of (13); it is a single
low-degree polynomial comparison, with the coefficients defined by
(13), rather than a positivity lookup. Its right side is at least

\[
 .32+\frac32z+z^4(34-43z+10z^2)>.32,
       \qquad 0\le z\le1.                              \tag{14}
\]

Indeed \(34-43z+10z^2\) decreases to 1 on \([0,1]\).
This proves the derivative assertion.

Consequently the desired minimum on \([.7,1.53]\) occurs at 1.53.
The elementary brackets

\[
 .99916<\sin(1.53)<.99917,\qquad
 .04078<\cos(1.53)<.04079
\]

follow from alternating sine degrees 11/13 and cosine degrees 10/12.
They give

\[
 x+K_F+(g-.09)\sin x-.09\cos x>6.8195,
 \qquad QN^2<(5.9182)^2\quad(x=1.53).
\]

Thus

\[
 F(x)\ge F(1.53)>.9013>.9005.                           \tag{15}
\]

This replaces the complete degree-16 Bernstein row and its separate
positive-nonradical row. The other scalar obligation is treated next.

### 3.2 One touching support replaces all nine curvature intervals

The core-side scalar in Sections 5.1 and 6 of the C/M manuscript is

\[
\begin{split}
 F(x)={}&x-.09(\sin x+\cos x-1)-c_M+(p+q+g)/2\\
       &+g\csc x+(13g/12)\cot x
              -R\sqrt{(p+g\csc x)^2+q^2},
 \qquad .6\le x\le1.2,\quad c_M=-2.143075.              \tag{16}
\end{split}
\]

Put \(t=\cot x\), \(w=\sqrt{1+t^2}\), and
\(N(w)=\sqrt{(p+gw)^2+q^2}\). Then \(x=\operatorname{arccot}t\)
and \(F(x)=H(t)\), where

\[
 H(t)=\operatorname{arccot}t-.09(1+t)/w+C+gw+(13g/12)t-RN(w),
 \quad C=.09-c_M+(p+q+g)/2.
\]

Elementary Taylor bounds at .6 and 1.2 give

\[
 3/8<t<147/100,
 \qquad \sqrt{73}/8<w<9/5.                              \tag{17}
\]

On this entire enlarged interval,

\[
 N>123/40,\qquad
 N''(w)=\frac{g^2q^2}{N(w)^3}<\frac1{10}.                \tag{18}
\]

To check the first inequality it suffices to use
\(w>267/250\), whose square is below \(73/64\), and square
\((p+g(267/250))^2+q^2>(123/40)^2\).
For the second, \(g^2q^2<(123/40)^3/10\) is a direct rational
comparison. Thus (18) uses neither trigonometric subintervals nor
pointwise curvature samples.

Choose the single contact point \(x_0=27/25=1.08\), and write
\(t_0=\cot x_0\), \(w_0=\csc x_0\), \(N_0=N(w_0)\).
Integrating (18) yields the global upper tangent quadratic

\[
 N(w)\le N_0+N'_0(w-w_0)+(w-w_0)^2/20.                  \tag{19}
\]

Let \(H_0(t)\) be the lower bound for \(H(t)\) obtained by
substituting the right side of (19) for \(N(w)\).
It has the form

\[
 H_0(t)=\operatorname{arccot}t-.09(1+t)/w+C_0+aw
                          +(13g/12)t-(R/20)t^2,
\]

where
\(a=g-Rg(p+gw_0)/N_0+(R/10)w_0\).
It touches both the value and derivative of \(H\) at \(t_0\).
The single-point brackets in the original manuscript, established
there by alternating Taylor bounds and squaring, give

\[
\begin{gathered}
 .881957806<\sin x_0<.881957807,\quad
 .471328364<\cos x_0<.471328365,\\
 1.978787507<R<1.978787508,\quad
 3.138070988<N_0<3.138070991.
\end{gathered}
\]

They imply the coarse bound \(a>-.541\). Explicitly, a lower
bound is

\[
 g-\frac{1.978787508\,g(p+g/.881957806)}{3.138070988}
          +\frac{1.978787507}{10(.881957807)}>-.541.       \tag{20}
\]

We now prove the uniform estimate \(H_0''>1/200\). Differentiation
uses only \(w'=t/w\), \(w''=1/w^3\), and gives

\[
 H_0''=\frac{2t}{w^4}
     +\frac{.09(1+3t-2t^2)}{w^5}+\frac a{w^3}-\frac R{10}.
\]

By (20) and \(R<1.98\),

\[
 w^5(H_0''-.005)
 >w\{2t-.203(1+t^2)^2\}+.27t-.451-.721t^2.              \tag{21}
\]

The coefficient \(B(t)=2t-.203(1+t^2)^2\) is positive on
\([3/8,147/100]\). Indeed \(B''<0\), and direct substitution
at both endpoints gives \(B>2/5\).
Since \(w<9/5\), the identity \(w-1=t^2/(w+1)\) gives
\(w>1+(5/14)t^2\). Substitute this lower bound into (21),
whose coefficient of \(w\) is positive. The result is

\[
\begin{split}
 w^5(H_0''-.005)&>P(t),\\
 P(t)&=-\frac{327}{500}+\frac{227}{100}t
       -\frac{2399}{2000}t^2+\frac57t^3
       -\frac{87}{250}t^4-\frac{29}{400}t^6.             \tag{22}
\end{split}
\]

This low-degree polynomial is strictly concave on the whole real
line, because

\[
 P''=-\frac{2399}{1000}+\frac{30}{7}t
          -\frac{522}{125}t^2-\frac{87}{40}t^4<0.
\]

The quadratic part has negative discriminant and negative leading
coefficient. Its two required endpoint values are positive:

\[
 P(3/8)=\frac{217097121}{3670016000}>0,\qquad
 P(147/100)=\frac{1326684931659}{400000000000000}>0.
\]

Thus (22) proves \(H_0''>1/200\) over the entire interval (17).

The same single-point brackets used in (20), substituted in (16)
and its derivative, give

\[
 H_0(t_0)=F(x_0)>.9006,\qquad
 |H_0'(t_0)|=\sin^2(x_0)|F'(x_0)|<.0003.
\]

For clarity, the lower value substitution is

\[
 1.08-.09(.881957807+.471328365-1)-c_M+(p+q+g)/2
 +\frac g{.881957807}
 +\frac{13g(.471328364)}{12(.881957807)}
 -(1.978787508)(3.138070991)>.9006.
\]

The derivative comparison uses the exact formula

\[
 F'=1+.09(s-c)+\frac g{s^2}
       \left[c\left(\frac{R(p+g/s)}{N}-1\right)-\frac{13}{12}\right],
\]

with the same brackets. The last square bracket is negative,
so its denominator bounds retain that sign.

Finally (3) gives, throughout the entire domain,

\[
 F(x)=H(t)\ge H_0(t)
 >.9006-\frac{.0003^2}{2(1/200)}
 =.900591>.9005.                                       \tag{23}
\]

This replaces the ten-row endpoint mesh and all nine interval
curvature estimates in the old Section 6. Together with Section 3.1,
it removes the scalar lookup premises from the complete C/M entry.

## 4. Both M/M scalar bounds

The labels and constants \(p,q,Q\) are as above, while
\(\gamma=.8912\).

### 4.1 The transverse support is increasing

The support in Section 4.2 of
`../MID_MID_WHOLE_PAIR_HAND_PROOF.md` is

\[
 F(x)=x+K+(\lambda-.09)\sin x-.09\cos x-RN,
\]

where

\[
 \lambda=.87,\quad K=4.21132981092,
 \quad N^2=p^2+q^2+\lambda^2+
                    2\lambda(p\sin x-q\cos x).
\]

To prove \(F'>0\), define \(D,s_0,c_0\) as in Section 3 and

\[
 \mathcal N=(p^2+q^2+\lambda^2)D+2\lambda(ps_0-qc_0),
 \quad J=D+(\lambda-.09)c_0+.09s_0,
\]

\[
 P(z)=J^2\mathcal N-Q\lambda^2(pc_0+qs_0)^2D.            \tag{24}
\]

All factors being compared are positive in the first quadrant.
Write \(y=z-3/8\). Direct expansion of the one degree-six
polynomial (24) gives the following whole-interval bound for
\(|y|\le1/4\):

\[
\begin{split}
 P(3/8+y)
 &>\frac3{1000}-\frac{17}{500}|y|\\
 &\quad+y^2\left(\frac{39}{2}
          -\frac{201}{10}|y|-15|y|^3-\frac{31}{5}|y|^4\right)\\
 &>\frac3{1000}-\frac{17}{500}|y|+14y^2>0.              \tag{25}
\end{split}
\]

To make the algebra behind (25) explicit, if
\(P(3/8+y)=\sum_{j=0}^6 c_jy^j\), the exact expression (24)
gives \(c_0>.003\), \(|c_1|<.034\), \(c_2>19.5\),
\(|c_3|<20.1\), \(c_4>0\), \(|c_5|<15\), and
\(|c_6|<6.2\). Dropping the positive quartic term and bounding
the other remainder terms proves the first line of (25).
The second line follows by \(|y|\le1/4\). Its minimum is
at least \(3/1000-(17/500)^2/56>0\), by completing the square.

For \(.6\le x\le1.09\), one has
\(1/8<\tan(x/2)<5/8\): the lower bound follows from
\(\tan(.3)>.3\), and the upper follows from
\(8S_5(.55)<5C_6(.55)\). Thus (25) applies throughout the
required interval and proves \(F'>0\).

At \(x=.6\), the elementary brackets
\(.5646<\sin x<.5647\), \(.8253<\cos x<.8254\) give

\[
 x+K+.78\sin x-.09\cos x>5.1774,
 \qquad QN^2<(4.276)^2.
\]

Consequently

\[
 F(x)\ge F(.6)>.9014>.8912.                             \tag{26}
\]

### 4.2 The primary support is concave

The other support, used only on the physical second quadrant, is

\[
 F(x)=x+K_P-.09\sin x-.91\cos x-RN(x),
 \quad K_P=2.613213938,
\]

\[
 N^2=p^2+q^2+1-2(p\cos x+q\sin x),
 \qquad \pi/2\le x\le37/20.                            \tag{27}
\]

The norm increases on this interval. At its right endpoint,
\(\sin(37/20)>.96\) and \(-.276<\cos(37/20)<-.275\)
by the alternating Taylor inequalities. Squaring now gives

\[
 N<15/8,\quad (p^2+q^2-1)^2>69/5,
 \quad 197/100<R<99/50.
\]

Using (2), together with \(\cos x\le0\), yields the uniform bound

\[
\begin{split}
 F''
 &<\frac9{100}+\frac{99}{50}\frac{15/8}{4}
       -\frac{197}{100}\frac{69/5}{4(15/8)^3}\\
 &=-\frac{116363}{9000000}<0.                           \tag{28}
\end{split}
\]

Thus only the two physical endpoints need consideration. At
\(\pi/2\), use \(N<1.6\) and \(\pi/2>1.57\) to get
\(F>.9252\). At \(37/20\), the bounds just proved give

\[
 F>1.85+2.613213938-.09+.91(.275)-(1.98)(1.875)
   =.910963938>.8912.                                   \tag{29}
\]

Concavity proves the bound everywhere between them. The artificial
extension to \([1.57,1.85]\) used by the old polynomial is unnecessary:
the physical support formula is only used for \(x\ge\pi/2\).

Equations (24)--(29) remove both Bernstein rows from the entire M/M
pair theorem. The previously proved true-contact deformation and
primary/secondary case coverage remain applicable to all original
axes and all closed state boundaries.

## 5. The complete L/M replacement

The eight scalar rows in the L/M whole-pair proof have three distinct
geometric forms: a transverse separator with middle target, a
transverse separator with low target, and a primary separator.
We handle each form on its entire physical interval. Constants and
state endpoints are those of the original L/M proof; in particular,
the required pair bound is \(\gamma=.9005\).

Write \(s=\sin x\), \(c=\cos x\), and, for a target label
\(c_T+pa+qb\), put

\[
 m=p^2+q^2,\qquad
 K=.09+f-c_T+(p+q+\lambda)/2.                           \tag{30}
\]

Here \(f\) is the already proved source minimum, including its
multiplier term. A transverse separator has

\[
 N^2=m+\lambda^2+2\lambda(ps-qc).
\]

Its lower support is
\(x+K+(\lambda-.09)s-.09c-RN\) in the first quadrant
and \(x+K+(\lambda-.09)(s-c)-RN\) in the second.
A primary separator has

\[
 N^2=m+\lambda^2-2\lambda(pc+qs),
\]

with supports \(x+K-.09(s+c)-RN\) and
\(x+K-.09s-(\lambda-.09)c-RN\), respectively.
These are precisely the unsquared, physical support functions
underlying the old rows.

### 5.1 First middle-target transverse support

For \(p=1.489593\), \(q=1.580219\),
\(c_T=-2.143075\), \(\lambda=.945\), and \(f=-.00001\),
consider the entire interval \([.76,1.4]\).
Put \(n_0=13/5\), \(U=N^2\), \(e=m+\lambda^2-n_0^2\),
and \(k=R/216\). We have \(0<U<9\): the norm increases
on this interval, and substitution of
\(.9854<\sin(1.4)<.9855\),
\(.1699<\cos(1.4)<.17\) at its endpoint gives \(U<9\).
Since the second derivative of \(\sqrt U\) is at most
\(-1/108\) for \(0<U\le9\), Taylor's integral formula gives

\[
 N\le\frac{n_0}2+\frac{U}{2n_0}
          -\frac{(U-n_0^2)^2}{216}.                    \tag{31}
\]

Substitute (31) into the support. The resulting lower function is

\[
 E(x)=x+C_0+A\sin x+B\cos x+C\sin 2x+D\cos 2x,          \tag{32}
\]

where

\[
\begin{split}
 C_0&=K-R\{n_0/2+(m+\lambda^2)/(2n_0)\}
             +k\{e^2+2\lambda^2m\},\\
 A&=\lambda-.09-R\lambda p/n_0+4ke\lambda p,\\
 B&=-.09+R\lambda q/n_0-4ke\lambda q,\\
 C&=-4k\lambda^2pq,\qquad
 D=2k\lambda^2(q^2-p^2).
\end{split}
\]

Direct rational comparison, using
\(1.978787507<R<1.978787508\), gives
\(A<0\), \(B>1.10\), \(-.078<C<0\), and \(D>0\).
On this entire interval \(s>.68\), \(c>0\), and
\(\sin2x>0\). Consequently

\[
 E'''=-Ac+Bs-8C\cos2x+8D\sin2x
       >1.10(.68)-8(.078)>0.
\]

Thus \(E''\) is increasing. At the single endpoint \(1.4\),
Taylor bounds give \(E''(1.4)<.21\). The same elementary
evaluation gives

\[
 E(.76)>.9204,\qquad E(1.4)>.9096.                     \tag{33}
\]

These evaluations require only the alternating sine and cosine
bounds through degree 13 and 14, respectively. For example,
the exact lower and upper functions are obtained by replacing each
sine or cosine term in (32), or its second derivative, by the
appropriate one of its two consecutive Taylor sums. Their argument
is at most \(2.8\), so the omitted terms decrease in magnitude.

For completeness, the elementary upper-curvature chord inequality
is

\[
 E''\le M\ \Longrightarrow\
 E(a+t)\ge (1-t/\ell)E(a)+(t/\ell)E(a+\ell)
                 -\frac M2t(\ell-t),
 \quad 0\le t\le\ell.                                 \tag{34}
\]

It follows by applying concavity to
\(E(x)-Mx^2/2\). With \(a=.76\), \(\ell=.64\),
and \(M=.21\), (33)--(34) give

\[
 E(x)>.9204-.084075t+.105t^2
 \ge\frac{202399677}{224000000}>.9035>.9005.
\]

This disposes of the first old L/M row on its whole domain.

### 5.2 The remaining middle-target transverse support

For the same target, use \(\lambda=.98\), \(f=-.00004\),
and \(n_0=14/5\). The upper tangent inequality
\(N\le n_0/2+N^2/(2n_0)\) gives the lower support

\[
 E(x)=x+C+B\cos x-A\sin x,\quad 1\le x\le\pi/2,        \tag{35}
\]

where

\[
 A=R\lambda p/n_0-(\lambda-.09)>0,\quad
 B=-.09+R\lambda q/n_0>1,
\]

\[
 C=K-R\{n_0/2+(m+\lambda^2)/(2n_0)\}.
\]

Since \(E''=A\sin x-B\cos x\) changes sign at most once,
from negative to positive, \(E'\) first decreases and then
increases. Its right endpoint is \(E'(\pi/2)=1-B<0\).
Thus \(E\) has no interior minimum. Direct endpoint substitution
gives \(E(1)>.9053\) and \(E(\pi/2)>.9109\).
For the first, sine and cosine Taylor sums through degrees 11
and 12 suffice; for the latter use
\(1.5707963267<\pi/2<1.5707963268\).
This proves the entire first-quadrant portion of the second row.

On the second-quadrant portion \([\pi/2,1.71]\), the actual
norm increases, \(N>2.9\), and

\[
 N'=\frac{\lambda(pc+qs)}N
       \le\frac{.98q}{2.9}<.54,\qquad s+c>.84.
\]

Hence the physical support satisfies
\(F'>1+.89(.84)-1.98(.54)>0\).
Its value at \(\pi/2\) is at least the lower value proved using (35).
This handles the complete third row as well.

### 5.3 Low target: choose the contact multiplier exactly

The fourth old row used a fitted linear multiplier on
\([.4,.79]\). Here choose the minimizing target contact
directly. Put

\[
 p=.403875,\quad q=1.089065,\quad
 \delta=.013966884,\quad
 \bar c=-\frac{457049398977}{800000000000},
\]

\[
 a=s-\delta,\quad \rho=\sqrt{Q-a^2},\quad
 h=ps-qc,\quad j=pc+qs.
\]

On this interval \(a,j>0\), \(h<0\). Choose

\[
 \lambda_*=\frac{aj}{\rho}-h.                         \tag{36}
\]

This is a valid multiplier for the source minimum. Indeed
\(\rho<R<1.979\), so
\(\lambda_*>f_0=-h+(s-\delta)j/1.979\), and

\[
 f_0''=h(1-2c/1.979)+(\delta-2s)j/1.979<0.
\]

Here \(c<.93\) and \(s>.38\) throughout. Endpoint substitution
gives \(f_0(.4)>.99\) and \(f_0(.79)>.85\). Concavity
therefore gives \(\lambda_*>.85\) on the whole interval.
The chord slope between the middle-chart endpoints is less
than \(.8\). Since the middle marker is concave in its arc
parameter, the source expression \(M(b)-\lambda_*b\)
has its minimum at the high endpoint. The original exact
endpoint brackets now yield the uniform lower bound

\[
 f>.4555-\lambda_*(.513966884).                        \tag{37}
\]

This verifies the source support independently of a fitted
multiplier formula.

Substituting (37) into the target full-circle support leaves

\[
 x+C_1-.09(s+c)+a\lambda_*
             -R\sqrt{(\lambda_*+h)^2+j^2},
 \quad C_1=.09+.4555-\bar c+(p+q)/2
          =1.86328174872125.
\]

Because \(a^2+\rho^2=R^2\), (36) reduces this exactly to

\[
 E(x)=x+C_1-.09(s+c)-ah-j\rho.                        \tag{38}
\]

Geometrically, the minimizing far corner \((Y,Z)\) is the
intersection of \(Ys-Zc=a\) with \(Y^2+Z^2=Q\):
\((Y,Z)=(as+\rho c,-ac+\rho s)\).
Thus (38) is the supporting-contact expression itself.

We next prove that (38) decreases on the whole interval. Define

\[
 \mathcal A=1+.09(s-c)-ch-aj,\qquad
 \mathcal B=(Q-a^2)h+acj.
\]

Differentiation gives
\(\rho E'=\rho\mathcal A+\mathcal B\).
The coarser bounds

\[
 .38<s<.72,\quad .69<c<.93,\quad
 0<a<.71,\quad h<-.46,\quad 0<j<1.2
\]

hold even on \([.4,.8]\). They imply
\(\mathcal A>1-.09-.71(1.2)>0\) and
\(\mathcal B<3.4(-.46)+.71(.93)(1.2)<0\),
using \(Q-a^2>3.4\).

To compare their magnitudes without squaring a function whose
sign is unknown, put \(z=\tan(x/2)\), \(d=1+z^2\), and
substitute \(s=2z/d\), \(c=(1-z^2)/d\) in

\[
 P(z)=d^5\{\mathcal B^2-(Q-a^2)\mathcal A^2\}.          \tag{39}
\]

Cancellation makes (39) a polynomial of degree ten. The physical
interval has \(.2<z<.42\), so let \(y=.42-z\in[0,.22]\).
Expanding the factored expression (39), and collecting the
positive even powers, gives the simple exact lower bound

\[
 P(.42-y)>
 .05+3.5y-23y^3-225y^5-135y^7-2y^9-y^{10}.             \tag{40}
\]

Here is enough algebra to check that comparison directly.
The constant coefficient exceeds \(.05\), the linear coefficient
exceeds \(3.5\), and the coefficients of \(y^2,y^4,y^6,y^8\)
are positive. The absolute values of the negative coefficients
of \(y^3,y^5,y^7,y^9,y^{10}\) are less than
\(23,225,135,2,1\), respectively; each comparison follows
by substituting the four rational constants \(Q,p,q,\delta\)
in (39). This is a single polynomial domination on the entire
physical interval, not an interval partition or a Bernstein
coefficient test.

For \(0\le y\le11/50\),

\[
 23y^2+225y^4+135y^6+2y^8+y^9
 \le\frac{3233582948210791}{1953125000000000}
 <\frac53.
\]

Thus (40) is at least
\(.05+(11/6)y>0\). Since \(\mathcal A>0\) and
\(\mathcal B<0\), (39) implies
\(-\mathcal B>\rho\mathcal A\), hence \(E'<0\).

At the sole remaining endpoint \(x=.79\), the elementary
Taylor and square comparisons give

\[
\begin{split}
 .7103532724&<s<.7103532725,\\
 .7038453156&<c<.7038453157,\qquad
 \rho<1.852200313.
\end{split}
\]

Writing \(s^-,s^+,c^-,c^+,\rho^+\) for these rational
endpoints, a direct lower bound for (38) is

\[
\begin{split}
 E(.79)&>.79+C_1-.09(s^++c^+)
       +(s^--\delta)(qc^--ps^+)\\
       &\hspace{20mm}-(pc^++qs^+)\rho^+\\
 &=\frac{4503003292525619045919613}
          {5000000000000000000000000}
 >.90059>.9005.                                       \tag{41}
\end{split}
\]

This proves the complete low-target transverse support.

### 5.4 All four primary rows are concave

The norm identity (2) yields, in either physical quadrant,

\[
 F''\le .18+\frac{RN}{4}
               -\frac{R(m-\lambda^2)^2}{4N^3}.         \tag{42}
\]

In the second quadrant the cosine contribution is nonpositive;
in the first quadrant \(.09(s+c)\le.18\).

For the middle target, the old fifth and sixth rows use
\(\lambda=.9\), \(f=-1.4757025241\), hence
\(K=2.7422784759\), on the physical interval
\([1.5,1.71]\). The norm increases there.
At \(1.71\), squaring with the sine and cosine Taylor bounds
gives \(N<9/5\); directly
\((m-\lambda^2)^2>15\). Therefore

\[
 F''<.18+\frac{1.98(9/5)}4
       -\frac{1.97(15)}{4(9/5)^3}
       =-\frac{95119}{486000}<0.                       \tag{43}
\]

For the low target, the old seventh and eighth rows use
\(\lambda=.94\),
\(f=-.455511-.94(1.199256062)\), hence
\(K=.29497005044125\), on \([1.3,1.71]\).
Again the norm increases. Endpoint squaring gives
\(N<14/25\), while directly
\((m-\lambda^2)^2>.21\). Hence

\[
 F''<.18+\frac{1.98(14/25)}4
       -\frac{1.97(.21)}{4(14/25)^3}
       =-\frac{2065479}{15680000}<0.                   \tag{44}
\]

Both physical quadrant pieces are therefore concave. It remains
to check their actual endpoints, including the shared point
\(\pi/2\). The middle-target norm is less than \(1.6,5/3,1.8\)
at \(1.5,\pi/2,1.71\), respectively. Use \(R<1.98\),
\(s+c<1.42\), \(\pi/2>1.57\), and \(-\cos1.71>.138\).
The corresponding support values exceed, respectively,

\[
\begin{split}
 1.5+2.7422784759-.1278-3.168&=.9464784759,\\
 1.57+2.7422784759-.09-3.3&=.9222784759,\\
 1.71+2.7422784759-.09+.81(.138)-3.564
      &=.9100584759.
\end{split}
\]

For the low target, the endpoint norms at
\(1.3,\pi/2,1.71\) are less than \(.24,.431,.558\).
The same substitutions give the respective lower bounds
\(.99197005044125\), \(.92159005044125\), and
\(.92743005044125\). Every displayed bound is greater
than \(.9005\). Each norm bound is a direct squared comparison
at one fixed angle, using the alternating Taylor sums; no
intermediate angle checks enter (43)--(44).

This proves all four primary rows and completes all eight L/M
scalar obligations. The original proof's quarter-contact lower
bounds, endpoint deformations, and reflection/reversal reduction
then supply all original signed axes, as before.

## 6. Coverage boundary

The new arguments above remove five L/L rows, one C/M polynomial row,
the entire nine-interval C/M curvature mesh, two M/M rows,
and all eight L/M rows.
They cover each complete continuous interval formerly
certified by those rows. They do not replace a row by tests on a finer
partition, and their mathematical premises contain no generated
coefficient arrays or numerical PASS status.

The separate note `HAND_CORE_HIGH_AND_HIGH_HIGH_CURVATURE.md`
removes the C/H and H/H scalar gates, and `HAND_MID_HIGH_CURVATURE.md`
removes the M/H gates. `HAND_CORE_LOW_SCALAR_WITHOUT_TABLES.md` and
`HAND_LOW_HIGH_SCALAR_REPLACEMENTS.md` discharge the C/L and L/H
obligations. The complete frame-concentration proof, with its exact
geometric and scalar dependency list, is assembled in
`../HAND_EXTERIOR_FRAME_CONCENTRATION.md`. G2's two residual whole-word
inequalities remain separate obligations.
