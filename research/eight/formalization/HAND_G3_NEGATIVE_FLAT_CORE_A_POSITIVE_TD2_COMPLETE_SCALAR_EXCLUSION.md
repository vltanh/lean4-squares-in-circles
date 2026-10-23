# A negative flat-core A primary and positive TD2: endpoint certificates

## 1. Scope and the scalar endpoints

Work on the fixed-original-witness G0--G2 boundary at

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]

H, G, B and D are original sorted outer states with signed tangents
respectively positive, negative, negative and negative. A is positive
flat core, so \(a_A=7/12\). T and E may have either sign and either
radial kind. The original owners are

\[
 BT=2,\quad TD=2,\quad DE=2,\quad EH=0,\qquad HG\in\{0,2\},
\tag{2}
\]

and one of the following two alternatives holds:

* GA3 has error \(-s\), \(0\le s\le1/4\), and AB0 has arbitrary error;
* AB2 has error \(-s\), \(0\le s\le19/50\), and GA2 has arbitrary error.

Put \(z=d_{TD}\ge0\). There is no such original cycle. No frame order
is assumed.

The local reductions proving the flat-core description and the strict
angle cuts for a genuinely primary negative witness are in
[the negative-A entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md).
The present scalar proof includes the endpoints of those cuts.

Use the notation

\[
 \begin{gathered}
 \eta=\frac{293}{1000},\qquad
 m=c(\cos z+\eta\sin z),\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\\
 c_0=\sqrt{Q/2}-\frac12,\qquad
 W(t)=\frac{1+\cos t+\sin t}{2}\quad(0\le t\le h),\\
 S(f,g)=
 \max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},
 \qquad
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
 \end{gathered}
\tag{3}
\]

For the GA alternative set
\((\lambda_G,\lambda_B)=(l\sec s,l)\); for the AB alternative set
\((\lambda_G,\lambda_B)=(l,l\sec s)\). Define the exact baseline

\[
\begin{split}
 B_O(s,z)={}&k+\lambda_G+\lambda_B+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(\lambda_G,k)
       -\overline S(m,\lambda_B)-S(1,c)\\
 &+l\sec s\{W(s)-1\}+\frac7{12}l\tan s,
 \qquad O\in\{\mathrm{GA},\mathrm{AB}\}.
\end{split}
\tag{4}
\]

The two baselines agree at \(s=0\); write their common value as \(B_0(z)\).
For each ordered pair \(0<p\le q\), put

\[
\begin{split}
 N_{p,q}(t)&=\sqrt{p^2+q^2+2pq\sin t},\\
 V_{p,q}(t)&=q(\cos t-1)
                    -R\{N_{p,q}(-t)-N_{p,q}(0)\}.
\end{split}
\tag{5}
\]

At \(s=0\), the three pairs are

\[
 (p_H,q_H)=(k,1),\qquad (p_G,q_G)=(k,l),\qquad
 (p_B,q_B)=(\min(l,m),\max(l,m)).
\tag{6}
\]

Write their functions as \(V_H,V_G,V_B\), and set

\[
 M_G(z)=k\{\cos(h-z)+\sin(h-z)-1\}
       +l(\cos h-1)-R\{N_{k,l}(-z)-N_{k,l}(0)\}.
\tag{7}
\]

The companion
[angle-concentration theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
reduces the original necessary inequalities to the following endpoint
obligations for the families below. On \(I_0=[0,1/5]\) they are

\[
\begin{gathered}
 B_0+V_H(z)>0,\qquad B_0+M_G(z)>0,\\
 B_0-\frac{109}{200}(m+.4z)(h-z)+V_H(h)>0,\\
 B_0-\frac{109}{200}(m+.4z)(h-z)+V_G(h)>0,\\
 B_{\mathrm{GA}}(z,z)>0.
\end{gathered}
\tag{8}
\]

On \(I_1=[1/5,h]\) they are

\[
 B_0+V_H(z)>0,\quad B_0+V_G(z)>0,\quad B_0+V_B(z)>0,\quad
 B_{\mathrm{GA}}(z,z)>0,\quad B_{\mathrm{AB}}(z,z)>0.
\tag{9}
\]

There are also four endpoints at the original angle cuts:

\[
\begin{array}{ll}
 B_{\mathrm{GA}}(1/4,z)+V_H(z-1/4)>0,\quad
 B_{\mathrm{GA}}(1/4,z)+V_B(z-1/4)>0,
       &1/4\le z\le h,\\
 B_{\mathrm{AB}}(19/50,z)+V_G(z-19/50)>0,\quad
 B_{\mathrm{AB}}(19/50,z)+V_H(z-19/50)>0,
       &19/50\le z\le h.
\end{array}
\tag{9a}
\]

The pairs in these four \(V\)-functions are unchanged by the secant:
H is always unaffected; B is unaffected in the GA alternative and
G is unaffected in the AB alternative.

The equal-angle expressions in (8)--(9) are scalar endpoints. They
remain defined when \(z\) exceeds an original negative-angle cut;
they do not assert an original witness at that artificial endpoint.
The affected norm's exact concavity permits those artificial endpoints.
For the unaffected norms, (9a) instead supplies the endpoint of their
proved concavity interval. No extension of that interval is assumed.

On the low interval, \(m\ge l\ge k\). Since
\(\sqrt{p^2+x^2}-\sqrt{l^2+x^2}\) decreases with \(x>0\) when \(p\ge l\),
the GA assignment has the larger sum of the two affected norm supports.
Its baseline is therefore no larger than the AB baseline at \(s=z\).
This proves that only the GA endpoint is needed in (8).
On the high interval both assignments are certified directly.

All decimals in this note are exact rationals.

## 2. Two continuous families

For \(0\le z\le1/5\), put \(t=1/5-z\) and choose

\[
\begin{split}
 k&=.676-.2t+3.8t^2-5t^3,\\
 l&=1.025-.25t+14.5t^2+13.75t^3-200t^4,\\
 c&=1+1.1t+17t^2.
\end{split}
\tag{10}
\]

For \(1/5\le z\le h\), put \(t=z-1/5\) and choose

\[
\begin{split}
 k&=.676+.2t+.9t^2-1.3t^3,\\
 l&=1.025+.22t-.3t^2,\\
 c&=1-.7t+.88t^2.
\end{split}
\tag{11}
\]

The two families agree at \(z=1/5\). Their useful whole-interval ranges
are as follows:

\[
\begin{array}{ll}
 I_0:\;&
 \displaystyle \frac23<k\le.748,\quad 1.023<l\le1.345,\quad
 1\le c\le1.9,\quad
 .55<\frac{k}{l}<.66,\quad 1<\frac ml<1.42,\\[3pt]
 &\displaystyle l\sec(.38)<m+.4z;\\[5pt]
 I_1:\;&
 \displaystyle .676\le k\le.8385,\quad
 1.025\le l\le\frac{799}{750},\quad .86<c\le1,\quad k<c,\\[3pt]
 &\displaystyle .659<\frac{k}{l}<.82,\qquad
 .77<\frac ml<1.032.
\end{array}
\tag{12}
\]

There are also the useful restricted high-interval inequalities

\[
 \begin{split}
 m&<l &&(z\ge1/4),\\
 m&<.94l &&(z\ge.3),\\
 m&<.92l &&(z\ge1/3),\\
 m&>.8l &&(z\le.38),\\
 \max(l,m)&<l+.03(h-z) &&(z<h).
 \end{split}
\tag{13}
\]

The last inequality is non-strict at \(z=h\) if its left side is \(l\).
In every case \(k<l\), \(k<c\), and the coefficient-pair conditions of
the companion concentration theorem hold for the full original
\(s\)-intervals. In particular, with \(p=l\sec s\), each ordered
pair has ratio of its smaller to larger coefficient at least \(1/2\).
On the high interval the stronger ratios and largest coefficients are

\[
\begin{array}{lll}
 \mathrm{GA}:&
 p_i/q_i>.6375,&q_{\max}<1.1,\\
 \mathrm{AB}:&
 p_i/q_i>.65,&q_{\max}<1.15,
\end{array}
\qquad q_{\min}=1.
\tag{14}
\]

We give exact range proofs in Section 4 after fixing a convenient
notation for whole-interval polynomial bounds.

## 3. Exact polynomial conventions

Let \(S_j,C_j\) be the alternating sine and cosine polynomials ending
in degree \(j\). Throughout \(0\le z\le h\), write

\[
 S_-=S_{11}(z),\quad S_+=S_9(z),\qquad
 C_-=C_{10}(z),\quad C_+=C_{12}(z).
\tag{15}
\]

They bound sine and cosine in the indicated directions. Use

\[
 \bar R=1.978787508,\qquad
 \bar c=.899214066,\qquad
 \bar\sigma=1.415477291.
\tag{16}
\]

Their required strict upper bounds follow by positive squaring:

\[
 \bar R^2>Q,\qquad
 (\bar c+\tfrac12)^2>Q/2,\qquad
 \left(\bar\sigma+\frac{1+\eta}{2}\right)^2>Q(1+\eta^2).
\tag{17}
\]

For polynomial upper bounds \(P_i\) of squared norms and positive
polynomials \(r_i\), define

\[
\begin{split}
 {\cal D}(\mathbf r)&=2\prod_i r_i,\\
 {\cal N}(A;\mathbf P,\mathbf r)
   &=2A\prod_i r_i
       -\bar R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.
\end{split}
\tag{18}
\]

The inequality \(\sqrt{P_i}\le(P_i+r_i^2)/(2r_i)\) proves that
\({\cal N}>0\) is sufficient for the corresponding scalar lower bound.

For an interval \(I=[v,w]\), put \(M=(v+w)/2\), \(r=(w-v)/2\).
If \(P(z)=\sum_i p_i z^i\), its centered coefficients are

\[
 a_n=r^n\sum_{i\ge n}\binom in p_i M^{i-n},
 \qquad
 P(M+rx)=\sum_n a_nx^n=\sum_j b_jT_j(x).
\tag{19}
\]

Here \(T_0=1,T_1=x,T_{j+1}=2xT_j-T_{j-1}\), and the exact
coefficient conversion is

\[
\begin{split}
 b_0&=\sum_{n\equiv0\pmod2}2^{-n}\binom n{n/2}a_n,\\
 b_j&=\sum_{\substack{n\ge j\\n\equiv j\pmod2}}
           2^{1-n}\binom n{(n-j)/2}a_n\qquad(j\ge1).
\end{split}
\tag{20}
\]

Since \(|T_j(x)|\le1\) on \([-1,1]\), the following are lower
bounds for \(P\) on the entire interval:

\[
\begin{split}
 {\mathfrak L}_I(P)&=b_0-\sum_{j\ge1}|b_j|,\\
 {\mathfrak Q}_I(P)&=b_0-b_2-\frac{b_1^2}{8b_2}
                            -\sum_{j\ge3}|b_j|\quad(b_2>0),\\
 {\mathfrak m}_I(P)&=a_0-\sum_{j\ge1}|a_j|.
\end{split}
\tag{21}
\]

The middle bound completes the square in
\((b_0-b_2)+b_1x+2b_2x^2\). Every aggregate below is a finite rational
sum specified by (19)--(21) and the displayed polynomials; there is no
angular subdivision or sampling premise.

## 4. Whole-interval verification of the weights

First consider the low family. Its \(k\) is convex in \(t\), and

\[
 k\ge.676-.2t+2.8t^2>\frac23.
\tag{22}
\]

Its maximum is the larger endpoint value, .748. Also

\[
 l\ge1.025-.25t+9.25t^2>1.023.
\tag{23}
\]

To bound \(l\) above, its derivative has the exact form

\[
 l'=-.25+5.25t+t(.2-t)(800t+118.75).
\tag{24}
\]

It is nonnegative for \(t\ge1/21\). Before \(1/21\),
\(l''\ge29-2400/441>23\), so \(l'\) increases and \(l\) has
at most one minimum. The largest endpoint value is \(l(.2)=1.345\).
The bounds for \(c\) are immediate.

The upper ratio follows from

\[
 .66l-k=.0005+.035t+t^2(5.77+14.075t-132t^2)>0;
\tag{25}
\]

the concave bracket is at least 3.305 on \([0,.2]\). For the lower
ratio it is convenient to use \(z=.2-t\):

\[
\begin{split}
 k-.55l&=.00825-.28z+z^2(14.6875-75.4375z+110z^2)\\
 &\ge .00825-.28z+4z^2>.0033.
\end{split}
\tag{26}
\]

The bracket in the first line decreases to 4 on the low interval.

For the remaining trigonometric comparisons define

\[
 m_-=c(C_-+\eta S_-),\quad
 m_+=c(C_++\eta S_+),\quad
 m_c=c(C_2+\eta S_3).
\tag{27}
\]

Then \(m_c\le m\), \(m_-\le m\le m_+\), and direct substitution
into (20)--(21) gives

\[
 {\mathfrak L}_{I_0}(1.42l-m_+)>.00989.
\tag{28}
\]

The polynomial \(m_c-l\), expanded in \(t=.2-z\), has the lower bound

\[
 m_c-l>
 .0132+1.304t+t^2(2.524-15.765t+191.055t^2)+.830t^5>0.
\tag{29}
\]

The middle quadratic is greater than 2.19 by completing its square.
Similarly

\[
\begin{split}
 .9286(m_c+.4z)-l
 &>.01336+.858t+
       t^2(1.308-15.621t+191.69t^2)+.770t^5>0.
\end{split}
\tag{30}
\]

Here the quadratic is greater than .989. Since
\(C_6(.38)>.9286\), (30) proves the low secant comparison in (12).

For the high family, \(k'\) is a concave quadratic positive at both
endpoints. Thus \(.676\le k\le.8385\). Completing squares in \(l\)
and \(c\) gives

\[
 1.025\le l\le1.025+\frac{.22^2}{1.2}
       =\frac{799}{750},\qquad
 c\ge1-\frac{.7^2}{4(.88)}>.86,\quad c\le1.
\tag{31}
\]

The inequality \(t(t-.5)^2\ge0\) gives

\[
 c-k=.324-.9t-.02t^2+1.3t^3
       \ge.324-1.225t+1.28t^2>.0309.
\tag{32}
\]

Also \(l-k\ge.349-1.2(.5)^2=.049>0\), and

\[
 k-.659l=.000525+.05502t+t^2(1.0977-1.3t)>0.
\tag{33}
\]

The other high comparisons are the following whole-interval rational
aggregates:

\[
\begin{gathered}
 {\mathfrak L}_{I_1}(.82l-k)>.02054,\qquad
 {\mathfrak L}_{I_1}(1.032l-m_+)>.01904,\\
 {\mathfrak L}_{[1/4,h]}(l-m_+)>.02773,\qquad
 {\mathfrak L}_{[.3,h]}(.94l-m_+)>.00303,\\
 {\mathfrak L}_{[1/3,h]}(.92l-m_+)>.00499,\\
 {\mathfrak L}_{[1/5,.38]}(m_--.8l)>.0868,\\
 {\mathfrak L}_{I_1}\bigl(l+.03(h-z)-m_+\bigr)>.00124.
\end{gathered}
\tag{34}
\]

Finally \(P=m_c-.77l\) satisfies

\[
 {\mathfrak L}_{I_1}(-P')>.1576,\qquad P(h)>.0045.
\tag{35}
\]

Thus \(P\) decreases and stays positive, proving \(m>.77l\).
This completes (12)--(13).

The pair conditions and (14) now follow directly. In the low GA
case \(2(.55)C_6(.25)>1\), so \(l\sec s<2k\). The remaining
low pair ratios use \(1<m/l<1.42\) and \(C_6(.38)>.9286\).
In the high GA case
\(.659(.9689)>.6375\); in the high AB case
\(.77(.9286)>.65\). The largest coefficients obey

\[
 \frac{799}{750}<1.1(.9689),\qquad
 \frac{799}{750}<1.15(.9286),\qquad
 1.032\,\frac{799}{750}<1.1,
\tag{36}
\]

while \(C_6(.25)>.9689\). The H pair has larger coefficient 1,
and all other larger coefficients exceed 1, so \(q_{\min}=1\).

## 5. Common endpoint polynomials

Use (27), and also put

\[
 \mu=c(C_4+\eta S_5),\qquad
 W_-=\frac{1+C_-+S_-}{2}.
\tag{37}
\]

Define \(I(z)\) separately for the two families:

\[
\begin{split}
 I_{\rm low}
 &=2k+3l+\tfrac32m_-+cW_-+\tfrac52
       -c\bar\sigma S_+-(1+c)\bar c,\\
 I_{\rm high}
 &=2k+3l+\tfrac32m_-+cW_-+\tfrac52
       -c\bar\sigma S_++\tfrac{1+c}{2}.
\end{split}
\tag{38}
\]

For \(c\ge1\), the exact sorted D support is
\(S(1,c)=(1+c)c_0\). For \(c\le1\), its full-circle upper
bound is \(\overline S(1,c)\). These facts give (38).
The ranges above also imply \(I-l>5>0\).

The unrotated and rotated squared-norm upper bounds are

\[
\begin{gathered}
 P_H=1+k^2,\quad P_G=k^2+l^2,\quad P_B=m_+^2+l^2,\quad
 P_D=1+c^2,\\
 P_{H,-}=P_H-2kS_-,\qquad
 P_{G,-}=P_G-2klS_-,\qquad
 P_{B,-}=P_B-2lm_-S_-.
\end{gathered}
\tag{39}
\]

Choose the auxiliary polynomials

\[
\begin{gathered}
 r_H=.83+.558k,\quad r_G=.55k+.835l,\quad
 r_B=.725\mu+.689l,\quad r_D=.7071(1+c),\\
 r_{H,-}=.895C_4+.446(k-S_5),\\
 r_{G,-}=.9lC_4+.436(k-lS_5),\\
 r_{B,-}=.752lC_4+.66(\mu-lS_5).
\end{gathered}
\tag{40}
\]

For the H endpoint on either interval, use

\[
 N_H={\cal N}(I+C_--1;\
                   (P_G,P_B,P_{H,-}),\ (r_G,r_B,r_{H,-})).
\tag{41}
\]

On the high interval append \((P_D,r_D)\) to this and every
three-norm construction in this section. The high G and B endpoints
are

\[
\begin{split}
 N_G&={\cal N}(I+l(C_--1);\
                (P_H,P_B,P_{G,-}),\ (r_H,r_B,r_{G,-})),\\
 N_B&={\cal N}(I+q_*(C_--1);\
                (P_H,P_G,P_{B,-}),\ (r_H,r_G,r_{B,-})),\\
 q_*&=l+.03(h-z).
\end{split}
\tag{42}
\]

Equation (34) gives \(q_*\ge\max(l,m)\); since \(C_--1\le0\),
it has the required direction in the B lower bound.

## 6. The two equal-angle assignments

Multiplying \(B_O(z,z)\) by the positive factor \(\cos z\) removes
the secant. Its elementary part has the common lower bound

\[
 A_Z=C_-(I-l)+l+\frac{13}{12}lS_-.
\tag{43}
\]

The use of \(C_-\) in the first term is valid because \(I-l>0\).
For the GA assignment use

\[
\begin{split}
 \mathbf P_Z&=
  (C_+^2P_H,\ l^2+k^2C_+^2,\ C_+^2P_B),\\
 \mathbf r_Z&=
  (C_4r_H,\ .84l+.543kC_4,\ C_4r_B),\\
 N_Z&={\cal N}(A_Z;\mathbf P_Z,\mathbf r_Z).
\end{split}
\tag{44}
\]

On the high interval append \((C_+^2P_D,C_4r_D)\).
For the high AB assignment use instead

\[
\begin{split}
 \mathbf P_{ZA}&=
 (C_+^2P_H,\ C_+^2P_G,\ l^2+m_+^2C_+^2,\ C_+^2P_D),\\
 \mathbf r_{ZA}&=
 (C_4r_H,\ C_4r_G,\ .8l+.6\mu C_4,\ C_4r_D),\\
 N_{ZA}&={\cal N}(A_Z;\mathbf P_{ZA},\mathbf r_{ZA}).
\end{split}
\tag{45}
\]

These are separate certificates. In particular the proof does not
assume that the same assignment is worse on the whole high interval.

## 7. The three additional low endpoints

Put

\[
 C_h^-=C_{10}(h),\quad C_h^+=C_{12}(h),\quad S_h^-=S_{11}(h),
\qquad
 \Phi_-=(C_h^-+S_h^-)C_--(C_h^+-S_h^-)S_+.
\tag{46}
\]

The formula for \(\cos(h-z)+\sin(h-z)\) proves that \(\Phi_-\)
is a lower bound. The same-block G numerator is

\[
 N_M={\cal N}\bigl(I+k(\Phi_--1)+l(C_h^--1);\
              (P_H,P_B,P_{G,-}),\ (r_H,r_B,r_{G,-})\bigr).
\tag{47}
\]

For the two separated endpoints put

\[
\begin{gathered}
 I_*=I-\frac{109}{200}(m_++ .4z)(h-z),\\
 P_{H,h}=P_H-2kS_h^-,\qquad
 P_{G,h}=P_G-2klS_h^-.
\end{gathered}
\tag{48}
\]

Then define

\[
\begin{split}
 N_{SH}&={\cal N}(I_*+C_h^--1;\
                  (P_G,P_B,P_{H,h}),\ (r_G,r_B,.77)),\\
 N_{SG}&={\cal N}(I_*+l(C_h^--1);\
                  (P_H,P_B,P_{G,h}),\ (r_H,r_B,.77l)).
\end{split}
\tag{49}
\]

The larger coefficient \(m+.4z\) in (8) is essential here: by
(30) it controls the secant weight throughout the whole original
negative-angle range.

## 8. Positive whole-interval certificates

Every auxiliary \(r\) used in (41)--(49) is positive. More precisely,
substitution into (19),(21) gives \(\mathfrak m_{I_0}(r)>.58\)
for every low auxiliary and \(\mathfrak m_{I_1}(r)>.58\)
for every high auxiliary.

For the low H numerator, write

\[
 N_H(.2-t)=\sum_{j=0}^{37} a_jt^j.
\]

Its exact coefficient bounds are

\[
 a_0>.00161,\quad a_1>-.0346,\quad a_2>-.382,\qquad
 {\mathfrak L}_{[0,.2]}
       \left(\sum_{j=3}^{37}a_jt^{j-3}\right)>31.6.
\tag{50}
\]

Therefore

\[
\begin{split}
 N_H&>.00161-.0346t-.382t^2+31.6t^3\\
 &\ge .00161-.04724t+.882t^2>.00097.
\end{split}
\tag{51}
\]

The second line uses \(t(t-.02)^2\ge0\), and the last step completes
a square.

For the low equal-angle numerator, write
\(N_Z(.2-t)=\sum_{j=0}^{66}a_jt^j\), now with its own coefficients.
The corresponding bounds are

\[
 a_0>.001506,\quad a_1>-.0987,\qquad
 {\mathfrak L}_{[0,.2]}
       \left(\sum_{j=2}^{66}a_jt^{j-2}\right)>7.70.
\tag{52}
\]

Consequently

\[
 N_Z>.001506-.0987t+7.70t^2>.00118.
\tag{53}
\]

The other three low numerators have the direct certificates

\[
 {\mathfrak Q}_{I_0}(N_M)>.0306,\qquad
 {\mathfrak L}_{I_0}(N_{SH})>.1848,\qquad
 {\mathfrak L}_{I_0}(N_{SG})>.0314.
\tag{54}
\]

Their degrees are respectively 40, 32 and 35; the coefficient \(b_2\)
required in the first bound is positive.

For the high H and G numerators,

\[
\begin{gathered}
 N_H(.2)>.00228,\qquad
 {\mathfrak L}_{I_1}
       \left(\frac{N_H(z)-N_H(.2)}{z-.2}\right)>.0212,\\
 N_G(.2)>.00865,\qquad
 {\mathfrak L}_{I_1}
       \left(\frac{N_G(z)-N_G(.2)}{z-.2}\right)>.0914.
\end{gathered}
\tag{55}
\]

These quotients are polynomials, including at the left endpoint.
The remaining high bounds are

\[
 {\mathfrak L}_{I_1}(N_B)>.005,\qquad
 {\mathfrak L}_{I_1}(N_Z)>.00182,\qquad
 {\mathfrak L}_{I_1}(N_{ZA})>.00408.
\tag{56}
\]

The high H, G, B, GA-equal and AB-equal numerator degrees are
respectively 38, 40, 36, 72 and 72. All comparisons (50)--(56)
follow by rational substitution in the explicit coefficient sums
(19)--(21); no choice of test angles occurs.

Since every denominator in (18) is positive, (50)--(56) prove the
ten scalar obligations (8)--(9).

## 9. Four endpoints at the original negative-angle cuts

It remains to prove (9a). Fix \(s_*=1/4\) for the GA alternative,
or \(s_*=19/50\) for the AB alternative, and restrict \(z\) to
\([s_*,h]\). Put

\[
\begin{gathered}
 \gamma_-=C_{10}(s_*),\quad \gamma_+=C_{12}(s_*),\qquad
 \tau_-=S_{11}(s_*),\quad \tau_+=S_9(s_*),\\
 \gamma_a=C_4(s_*),\qquad \tau_a=S_5(s_*),\qquad
 \theta=z-s_*,\\
 C_\theta^-=\gamma_-C_-+\tau_-S_-,\qquad
 S_\theta^-=\gamma_-S_- -\tau_+C_+,\\
 C_\theta^a=\gamma_aC_4+\tau_aS_5,\qquad
 S_\theta^a=\gamma_aS_5-\tau_aC_4.
\end{gathered}
\tag{57}
\]

The first two angle polynomials are lower bounds for
\(\cos\theta,\sin\theta\); the superscript \(a\) expressions are
used only to choose positive auxiliary polynomials. As in (43),
the elementary part after multiplication by \(\cos s_*\) has
the common lower bound

\[
 A_*=\gamma_-(I-l)+l+\frac{13}{12}l\tau_-.
\tag{58}
\]

For the GA case start with the four squared-norm bounds and auxiliaries

\[
\begin{split}
 \mathbf P^{\mathrm{GA}}
  &=(\gamma_+^2P_H,\ l^2+\gamma_+^2k^2,\
                         \gamma_+^2P_B,\ \gamma_+^2P_D),\\
 \mathbf r^{\mathrm{GA}}
  &=(\gamma_a r_H,\ .84l+.543\gamma_a k,\
                         \gamma_a r_B,\ \gamma_a r_D).
\end{split}
\tag{59}
\]

For the AB case use

\[
\begin{split}
 \mathbf P^{\mathrm{AB}}
  &=(\gamma_+^2P_H,\ \gamma_+^2P_G,\
                         l^2+\gamma_+^2m_+^2,\ \gamma_+^2P_D),\\
 \mathbf r^{\mathrm{AB}}
  &=(\gamma_a r_H,\ \gamma_a r_G,\
                         .8l+.6\gamma_a\mu,\ \gamma_a r_D).
\end{split}
\tag{60}
\]

The order in both lists is H, G, B, D. For a rotated H component,
replace its entry by

\[
 \begin{split}
 P_H^*&=\gamma_+^2P_H-2\gamma_-^2kS_\theta^-,\\
 r_H^*&=\gamma_a\{.87C_\theta^a+.493(k-S_\theta^a)\},
 \end{split}
\tag{61}
\]

and replace the elementary term \(A_*\) by
\(A_*+\gamma_+(C_\theta^--1)\).
For the rotated G component in the AB case, use

\[
 \begin{split}
 P_G^*&=\gamma_+^2P_G-2\gamma_-^2klS_\theta^-,\\
 r_G^*&=\gamma_a\{.9lC_\theta^a+.436(k-lS_\theta^a)\},
 \end{split}
\tag{62}
\]

and the elementary term \(A_*+\gamma_+l(C_\theta^--1)\).
For the rotated B component in the GA case, use

\[
 \begin{split}
 P_B^*&=\gamma_+^2P_B-2\gamma_-^2lm_-S_\theta^-,\\
 r_B^*&=\gamma_a\bigl\{(.714+.55\theta)lC_\theta^a
              +(.7-.82\theta)(\mu-lS_\theta^a)\bigr\},
 \end{split}
\tag{63}
\]

again with elementary term \(A_*+\gamma_+l(C_\theta^--1)\).
Here \(m<l\), because \(z\ge1/4\); this justifies the coefficient
\(l\) in the B angular cost. In (61)--(63) the squared-norm bounds
have the correct direction even if the lower sine polynomial is
slightly negative at \(\theta=0\), since the actual sine is nonnegative.

Let \(N_{\mathrm{GA},H},N_{\mathrm{GA},B},
N_{\mathrm{AB},G},N_{\mathrm{AB},H}\) be the four instances of
\({\cal N}\) obtained by these replacements in (59)--(60).
Every auxiliary in these four instances has
\(\mathfrak m_{[s_*,h]}(r)>.93\). The numerator degrees are
respectively 38, 36, 40 and 38, and their exact certificates are

\[
\begin{gathered}
 N_{\mathrm{GA},H}(1/4)>.0066,\qquad
 {\mathfrak L}_{[1/4,h]}
 \left(\frac{N_{\mathrm{GA},H}(z)-N_{\mathrm{GA},H}(1/4)}
                  {z-1/4}\right)>.453,\\
 {\mathfrak L}_{[1/4,h]}(N_{\mathrm{GA},B})>.00672,\\
 {\mathfrak L}_{[19/50,h]}(N_{\mathrm{AB},G})>.0535,\qquad
 {\mathfrak L}_{[19/50,h]}(N_{\mathrm{AB},H})>.0555.
\end{gathered}
\tag{64}
\]

These are direct substitutions into the same finite rational sums
(19)--(21). They prove the four inequalities (9a).

All the scalar endpoints required by the companion angle-concentration
theorem are now strictly positive. That theorem contradicts the
necessary stress inequality for every original cycle in Section 1,
completing the negative flat-core A primary / nonnegative TD2 exclusion.
