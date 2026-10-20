# A polynomial EH multiplier with a retained quadratic gain

## 1. The scalar statement and its contact scope

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 K=\frac{13}{12},\qquad T=\frac{61}{250}.
\tag{1}
\]
For
\[
 \frac{647}{1000}\le k\le\frac45,\qquad 0\le t\le T,
\]
define
\[
 p(t)=1+\frac12t^2+50t^4
\tag{2}
\]
and the exact EH baseline correction
\[
 H_k(t)=p(t)\left(1+\frac12\cos t+K\sin t\right)-\frac32
       -R\left\{\sqrt{p(t)^2+k^2}-\sqrt{1+k^2}\right\}.
\tag{3}
\]

Use the parameter and two explicit polynomials
\[
 r=\frac{R}{\sqrt{1+k^2}},\qquad y=r-\frac85,
\tag{4}
\]
\[
 \begin{split}
 \tau(r)&=.13953+.5431y+1.839y^2+7.852y^3,\\
 \Lambda(r)&=1.05278886-.20268828y-.89246999y^2\\
           &\hspace{19mm}-3.99914425y^3-17.76287293y^4.
 \end{split}
\tag{5}
\]
Then
\[
 \boxed{\displaystyle
 H_k(t)\ge
 t\left\{\Lambda(r)+\frac{2t}{\tau(r)}
                         (t-\tau(r))^2\right\}.}
\tag{6}
\]
Every decimal is an exact rational. Equality of both sides
at \(t=0\) is understood directly.

Here is the contact use of this scalar. Suppose E is a nonpositive
flat-core state with \(a_E=7/12\), \(b_E\ge0\), the EH1 error is
\(-t\), and the preceding DE force has E-tangent coefficient \(+1\).
This includes a secant-weighted negative DE3. Give EH1 multiplier
\(p(t)\). The elementary bound
\[
 p(t)\cos t-1
 \ge t^4\left(\frac{199}{4}-25t^2\right)\ge0
\tag{7}
\]
follows from \(\cos t\ge1-t^2/2\).
The remaining E-tangent force is therefore
\[
                       \{1-p(t)\cos t\}b_E\le0.
\]
Discarding it in an upper force bound, and using
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2},
\]
gives exactly (3) as a lower baseline correction:
\[
 p(t)W(t)-1+p(t)\frac7{12}\sin t
    -\{\overline S(p(t),k)-\overline S(1,k)\}=H_k(t).
\tag{8}
\]
The accompanying ordinary H pair is \((k,p(t))\). Its remaining
angular support must be retained or compared explicitly in a
subsequent angle concentration. The present lemma proves (6)
for the baseline correction.

## 2. One polynomial lower bound

The range of (4) is contained in the rational interval
\[
                  r_-=1.545\le r\le1.662=r_+.
\tag{9}
\]
Positive squaring proves this from
\[
 r_-^2(1+.8^2)<Q,\qquad r_+^2(1+.647^2)>Q.
\]
The derivative of \(\tau\), as a polynomial in y, is positive:
\[
 \tau'=.5431+3.678y+23.556y^2
 \ge .5431-\frac{3.678^2}{4(23.556)}>0.
\tag{10}
\]
Its rational endpoint values consequently give
\[
                           .113<\tau(r)<.183<T.
\tag{11}
\]

Let \(S_{11}\) and \(C_{10}\) be the alternating sine and cosine
Taylor polynomials ending at their indicated degrees. Define
\[
 \begin{split}
 v(t)&=1+\frac{401}{4}t^2+50t^4+2500t^6,\\
 E(t)&=\frac{p(t)\{1+\tfrac12C_{10}(t)+KS_{11}(t)\}-3/2}{t}.
 \end{split}
\tag{12}
\]
The numerator defining E has zero constant term, so E is a
polynomial. The identity \(p(t)^2-1=t^2v(t)\) gives the polynomial
\[
 P(r,t)=E(t)-
 \sum_{j=1}^{9}
   {1/2\choose j}\,Q^{1-j}r^{2j-1}t^{2j-1}v(t)^j.
\tag{13}
\]
Its degrees are at most 17 in r and 71 in t.

For \(0<t\le T\),
\[
                           \frac{H_k(t)}t\ge P(r,t).
\tag{14}
\]
To verify this directly, put
\[
 z=\frac{r^2}{Q}\{p(t)^2-1\}.
\]
It is nonnegative and is less than \(1/3\), as follows by
substituting \(r_+\) and T. The alternating binomial expansion
has decreasing term magnitudes on this interval. Its odd
partial sum therefore bounds the square root above:
\[
 \sqrt{1+z}-1\le\sum_{j=1}^{9}{1/2\choose j}z^j.
\tag{15}
\]
Also
\[
 R\{\sqrt{p(t)^2+k^2}-\sqrt{1+k^2}\}
      =\frac Qr\{\sqrt{1+z}-1\}.
\]
Together with \(S_{11}\le\sin\), \(C_{10}\le\cos\), these identities
give (14). At zero the removable values are
\(H_k(t)/t\to K=P(r,0)\).

## 3. A derivative bound makes a divided remainder monotone

All derivatives in this section are in t, with r fixed.
The following exact whole-interval bound will be certified in
Section 5:
\[
                         P_{ttt}(r,t)<\frac{12}{\tau(r)}
                    \qquad(0\le t\le T).
\tag{16}
\]
Write \(\tau=\tau(r)\) and define the continuous divided remainder
\[
 A_r(t)=
 \frac{P(r,t)-P(r,\tau)-P_t(r,\tau)(t-\tau)}
      {(t-\tau)^2},\qquad
 A_r(\tau)=\frac12P_{tt}(r,\tau).
\tag{17}
\]
Taylor's integral identity gives
\[
 A_r(t)=\int_0^1(1-v)P_{tt}(r,\tau+v(t-\tau))\,dv.
\]
Consequently
\[
 \frac{d}{dt}\left\{A_r(t)-\frac{2t}{\tau}\right\}
 =\int_0^1v(1-v)P_{ttt}(r,\tau+v(t-\tau))\,dv-\frac2\tau<0,
\tag{18}
\]
because \(\int_0^1v(1-v)\,dv=1/6\).

Put \(d=1/40\). Section 5 also proves the intrinsic endpoint
comparison
\[
                        A_r(T)-\frac{2T}{\tau}>d.
\tag{19}
\]
Equations (18)--(19) imply, on the entire interval,
\[
 P(r,t)\ge P(r,\tau)+P_t(r,\tau)(t-\tau)
                +\left(d+\frac{2t}{\tau}\right)(t-\tau)^2.
\tag{20}
\]
The remaining exact point bounds are
\[
 |P_t(r,\tau)|<.0007,\qquad
 P(r,\tau)-\Lambda(r)>.00001513>
                   \frac{(.0007)^2}{4d}=.0000049.
\tag{21}
\]
Completing the square in the linear term and \(d(t-\tau)^2\)
in (20) gives
\[
                P(r,t)\ge\Lambda(r)+\frac{2t}{\tau}(t-\tau)^2.
\tag{22}
\]
Combining (14) and (22) proves (6).

## 4. Explicit coefficient bounds on the whole parameter interval

This section specifies the exact finite sums used in the
certificates. There is no subdivision of the r or t interval.

Normalize r by
\[
                  r=\frac{3207+117x}{2000},\qquad -1\le x\le1.
\tag{23}
\]
For a polynomial \(f(x)=\sum_{j=0}^m a_jx^j\), convert its first
29 monomials to Chebyshev polynomials:
\[
 \sum_{j=0}^{\min(m,28)}a_jx^j=\sum_{n=0}^{28}b_nT_n(x).
\]
The coefficients are explicitly
\[
 b_n=\sum_{\substack{n\le j\le\min(m,28)\\j\equiv n\pmod2}}
       a_j\,2^{-j}{j\choose(j-n)/2}
                \begin{cases}1,&n=0,\\2,&n>0.\end{cases}
\tag{24}
\]
Set
\[
 \begin{split}
 {\cal L}(f)&=b_0-\sum_{n=1}^{28}|b_n|-\sum_{j=29}^{m}|a_j|,\\
 {\cal U}(f)&=b_0+\sum_{n=1}^{28}|b_n|+\sum_{j=29}^{m}|a_j|.
 \end{split}
\tag{25}
\]
Then \({\cal L}(f)\le f(x)\le{\cal U}(f)\) on the whole normalized
interval, since \(|T_n(x)|\le1\), \(|x|\le1\). For degrees below
29 the final sum is empty.

For the t variable write exactly
\[
 P_{ttt}(r,t)=\sum_{j=0}^{68}B_j(r)\,
                              T_j\left(\frac{2t}{T}-1\right).
\tag{26}
\]
Each \(B_j\) has degree at most 17. Its coefficients are determined
by differentiating (13) and using the elementary multiplication
identities
\[
 \begin{split}
 tT_0(2t/T-1)&=\frac T2(T_0+T_1)(2t/T-1),\\
 tT_j(2t/T-1)&=\left\{\frac T2T_j+\frac T4(T_{j-1}+T_{j+1})\right\}
                         (2t/T-1),\qquad j\ge1.
 \end{split}
\tag{27}
\]
Thus all following sums are exact rational expressions in the
displayed coefficients (1), (2), (5), and (12)--(13).

## 5. The four rational certificates

Every application of \({\cal L},{\cal U}\) below includes the
substitution (23). The third-derivative coefficients satisfy
\[
 \begin{gathered}
 {\cal U}(B_2)<0,\qquad {\cal U}(B_3)<0,\qquad
 {\cal L}(B_4)>0,\qquad {\cal L}(B_5)>0,\\
 \sum_{j=6}^{68}\max\{|{\cal L}(B_j)|,|{\cal U}(B_j)|\}
                         <.83.
 \end{gathered}
\tag{28}
\]
Define
\[
 A=B_0-B_2-B_3+B_4+B_5+.83.
\]
Completing the square in the first three t-Chebyshev terms,
using \(B_2<0\), yields
\[
 P_{ttt}\le A+\frac{B_1^2}{8(-B_2)}.
\]
The exact polynomial comparison
\[
 {\cal L}\left(8(-B_2)(12-\tau A)-\tau B_1^2\right)>343
\tag{29}
\]
proves (16). The cleared numerator in (29) has no denominator
of variable sign.

For the divided remainder at T, define
\[
 D(r)=
 \tau\{P(r,T)-P(r,\tau)-P_t(r,\tau)(T-\tau)\}
            -(2T+d\tau)(T-\tau)^2.
\tag{30}
\]
Its complete coefficient bound is
\[
                              {\cal L}(D)>.0000867>0.
\tag{31}
\]
Since \(\tau>0\) and \(T-\tau>0\), this is precisely (19).

Finally the two point polynomials satisfy
\[
 \begin{split}
 {\cal L}\{P_t(r,\tau)\}&>-.00056073>-.0007,\\
 {\cal U}\{P_t(r,\tau)\}&< .00052866< .0007,\\
 {\cal L}\{P(r,\tau)-\Lambda(r)\}&>.00001513.
 \end{split}
\tag{32}
\]
These prove (21). The degrees of \(P(r,\tau)\) and
\(P_t(r,\tau)\) are respectively 230 and 227. Formula (25)
bounds their complete higher-degree tails; none is discarded
as a numerical approximation.

For scale, the exact coefficient sums in (28), (29), and (31)
are bounded respectively by
\[
 .829170,\qquad
 8(-B_2)(12-\tau A)-\tau B_1^2>343.69,\qquad
 D>.000086705.
\]
Only the weaker rational comparisons explicitly used above
are needed. They follow by substitution in the fixed coefficient
formulas (13), (23)--(27). No sampled angles, fitted numerical
values, or geometric state inventory enter the proof.

This proves the adaptive EH gain (6), with the H angular pair
\((k,p(t))\) retained for its subsequent use.
