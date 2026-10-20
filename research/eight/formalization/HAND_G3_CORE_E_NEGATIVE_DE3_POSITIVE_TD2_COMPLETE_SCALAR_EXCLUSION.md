# A negative core DE3 and positive TD2: continuous endpoint certificates

## 1. Scope and the necessary scalar

Work on the fixed-original-witness G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]
The sorted outer states H, G, B and D have signed tangents,
respectively, positive, negative, negative and negative. E is
nonpositive and is a true core state. Retain the original owners
\[
 HG\in\{0,2\},\qquad BT=2,\qquad TD=2,\qquad DE=3,\qquad EH=0,
\tag{2}
\]
where \(d_{TD}=z\ge0\) and \(d_{DE}=-s\le0\).
The EH0 error has either sign. At A allow no primary, a single
nonnegative GA3 or AB2, or both GA3 and AB2 with nonnegative
signed total \(a\). An A edge that retains its secondary owner
GA2 or AB0 has arbitrary error. Put \(a=0\) when neither primary
is present. A and T may have either sign and either radial kind.

There is no such cycle. This statement has no frame-order
hypothesis. The proof uses only the stated circle constraints,
the actual neighboring inequalities, and the original variation
bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{3}
\]
It therefore also applies to a transported necessary system
preserving these inputs. Virtual angles below are scalar
arguments; they assert no new original owner.

Use
\[
\begin{gathered}
 \eta=\frac{293}{1000},\qquad K=\frac{13}{12},\qquad
 W(t)=\frac{1+\cos t+\sin t}{2}\quad(0\le t\le h),\\
 c_0=\sqrt{Q/2}-\frac12,\qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\\
 S(f,g)=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},\\
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2},\\
 \sigma=S(1,\eta)
       =R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 j(a)=W(a)-1-S(\sin a,1-\cos a).
\end{gathered}
\tag{4}
\]

The actual EH0 inequality forces \(b_E\le a_0-1<.415\).
Consequently the actual true-core E has \(a_E=7/12\), by
[the secant D-support note, Section 2](HAND_G3_CORE_E_NEGATIVE_DE3_SECANT_D_SUPPORT.md).
With multiplier \(q=\sec s\) on DE3, its tangent cancels EH0:
\[
 qP_{DE3}(-s)=q a_D-\frac7{12}\tan s+b_E.
\tag{5}
\]
The remaining demand correction is
\[
 q\{W(s)-1\}+\frac7{12}\tan s
                =K\tan s-\frac12(q-1).
\tag{6}
\]

Put \(\theta=a+z\), so \(0\le\theta\le h\). Choose positive
weights \(k,l,c\) depending only on \(\theta\), and put
\[
                    m=c(\cos z+\eta\sin z).
\tag{7}
\]
The three full-circle blocks use the ordered coefficient pairs
\[
 (p_H,q_H)=(k,1),\quad (p_G,q_G)=(k,l),\quad
 (p_B,q_B)=(\min(l,m),\max(l,m)).
\tag{8}
\]
The D force is the unrotated pair \((q,c)\). The exact baseline,
before the remaining angle increments, is
\[
\begin{split}
 B_s(a,z)={}&k+2l+m+cW(z)+q+1-c\sigma\sin z+l j(a)\\
 &-\overline S(1,k)-\overline S(l,k)-\overline S(m,l)-S(q,c)\\
 &+K\tan s-\frac12(q-1).
\end{split}
\tag{9}
\]
The positive-A comparison is the single-primary comparison or
[the signed two-primary combination](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
Both use the same multiplier \(l\), and both preserve the
necessary variation enlargement. After deleting the A-primary
arguments, TD and DE, the remaining positive and negative masses
satisfy
\[
 P\le h-\theta,\qquad N\le h-s,\qquad P-N=s-\theta.
\tag{10}
\]
If no A argument is deleted, the extra zero arguments are simply
the permitted virtual arguments in the full-circle blocks.

For \(0<p\le q\), set
\[
\begin{split}
 N_{p,q}(t)&=\sqrt{p^2+q^2+2pq\sin t},\\
 U_{p,q}(t)&=p(\cos t+\sin t-1)
                  -R\{N_{p,q}(t)-N_{p,q}(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)
                  -R\{N_{p,q}(-t)-N_{p,q}(0)\}.
\end{split}
\tag{11}
\]
Write \(U_i,V_i\) for the three pairs in (8).
The companion
[E-angle concentration theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
reduces (9)--(10) to intrinsic \(s\)-endpoints, followed by
the split endpoints \((a,z)=(0,\theta)\) and
\((\theta,0)\). The scalar endpoint conditions are stated below
and proved explicitly. All decimals in this note are exact
rationals.

## 2. Endpoint obligations

Write \(L=1/6\) and \(I_0=[0,L]\), \(I_1=[L,h]\).
At \(s=0\), let \(B_0=B_0(a,z)\). On \(I_0\), D is diagonal,
and the four sufficient endpoint functions are
\[
\begin{split}
 B_0+V_H(\theta),\qquad&
 B_0+V_H(\theta)
       +k\{\cos(h-\theta)+\sin(h-\theta)-1\}
       +l(\cos h-\cos\theta),\\
 B_0-\frac{109}{200}m(h-\theta)+V_H(h),\qquad&
 B_0-\frac{109}{200}m(h-\theta)+V_G(h).
\end{split}
\tag{12}
\]
For the second function, \(V_G(\theta)\ge V_H(\theta)\)
was used to lower the G same-block function. The other same-block
functions dominate their pure-negative functions. The two
separated bounds use \(U_i(t)\ge-(109/200)q_i t\) and
\(q_{\max}=m\). These are whole-interval scalar bounds from
[the scalar-envelope theorem](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).

Also require, on \(I_0\),
\[
              B_\theta(a,z)>0,
\tag{13}
\]
whereas on the high interval use the full-D lower baseline
\[
             \overline B_s(a,z)\le B_s(a,z).
\tag{14}
\]
Here \(\overline B_s\) denotes (9) with \(S(\sec s,c)\)
replaced by its full-circle upper bound
\(\overline S(\sec s,c)\).

On \(I_1\), use the full D-circle throughout. The four sufficient
functions are
\[
 \overline B_0+V_H(\theta),\quad
 \overline B_0+V_G(\theta),\quad
 \overline B_0+V_B(\theta),\quad
 \overline B_\theta.
\tag{15}
\]
Each positive expression in (12), (13), and (15) is certified at both split
endpoints. Section 10 also supplies the two endpoint derivative
inequalities used in the high-angle concentration proof.

## 3. The two continuous weight families

For \(0\le\theta\le L\), put \(u=\theta-L\) and choose
\[
\begin{split}
 k&=.6708+.15u+4u^2,\\
 l&=1.0073-1.7u+2.2u^2,\\
 c&=1.0389-3.45u+9u^2.
\end{split}
\tag{16}
\]
For \(L\le\theta\le h\), put
\[
                     t=\frac{\theta-L}{h-L}
                       =\frac{15}{8}(\theta-L)
\]
and choose
\[
\begin{split}
 k&=.670158+.113718t+.006506t^2+.009026t^3+.001t^4,\\
 l&=1.005069-.146411t-.157739t^2+.162815t^3,\\
 c&=1.021248-.168873t-.165381t^2+.175944t^3.
\end{split}
\tag{17}
\]
The two stresses need not agree at \(L\). Either valid stress
may be used at that one value of the total angle.

The useful low ranges, valid for every \(0\le z\le\theta\le L\),
are
\[
 \frac23<k<.757,\qquad 1<l\le c<1.864,\qquad
 l<1.352,\qquad l<2k,\qquad
             c\le m<1.38l<\frac32l.
\tag{18}
\]
In particular \(c\ge1.0389>\sec L\), so D is diagonal
when \(s\le\theta\le L\).

The useful high ranges, valid throughout \(L\le\theta\le h\)
and \(0\le z\le\theta\), are
\[
\begin{gathered}
 .670158\le k\le.800408,\qquad
 .863<l\le1.005069,\qquad
 .862<c\le1.021248,\\
 k<\min(l,c,m),\qquad l<\frac32k,\qquad
 .9<\frac cl<1.017,\qquad \frac ml<1.061,\\
 \frac{p_i}{q_i}>\frac23,\qquad
 q_{\max}<1.066,\qquad
             \frac{q_{\max}}{q_{\min}}<\frac{29}{25}.
\end{gathered}
\tag{19}
\]
The strict ratio \(p_i/q_i>2/3\) includes H, G and B.
There is also the correlated high bound
\[
                    c\le1.073-.3\theta.
\tag{20}
\]

These ranges give all coefficient assumptions in the companion
concentration theorem. They also give the low split bounds
\(c/l,m/l<3/2\), and the high split bounds
\(.9<c/l<1.1\), from
[the two-positive-error split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
The \(s\)-concentration is applied before those split comparisons;
no split-concavity assertion is made for an unreduced saturated
two-angle alternative.

## 4. Direct range certificates

For (16), put \(x=L-\theta\). Then
\[
 k=.6708-.15x+4x^2,\quad
 l=1.0073+1.7x+2.2x^2,\quad
 c=1.0389+3.45x+9x^2.
\tag{21}
\]
Completing the square gives
\(.6708-.15^2/16>2/3\). Convexity gives the upper k endpoint.
The l and c bounds, and \(c-l>0\), follow directly from the
positive coefficients in (21). In the original variable,
\[
             2k-l=\frac{72935}{450000}
                         +\frac{\theta}{15}+5.8\theta^2>0.
\tag{22}
\]
Since \(\cos z+\eta\sin z\) increases on \([0,L]\),
\[
 m\le c(1+\eta\theta).
\]
The exact polynomial is
\[
 1.38l-c(1+\eta\theta)
   =\frac{11305}{7500000}+2.5458773\theta
                       -4.07415\theta^2-2.637\theta^3.
\tag{23}
\]
Its whole-interval coefficient bound, defined in Section 6, is
\[
                 \mathcal C_{I_0}\{1.38l-c(1+\eta\theta)\}
                              =.0007443125>0.
\tag{24}
\]

The low E-angle proof also uses
\[
 C_0(k,l):=\frac{Rk^2l^2}{(k^2+l^2)^{3/2}}>\frac12.
\tag{25}
\]
Here is one polynomial certificate for it. Expand
\[
             P(x)=4Q k(x)^4l(x)^4-\{k(x)^2+l(x)^2\}^3
                    =\sum_{j=0}^{16}a_jx^j
\]
using (21). Its exact coefficients satisfy
\[
 a_0>.123,\quad -1.626<a_1<0,\quad a_2>15.99,\quad
                    \min_{3\le j\le16}a_j>177.
\tag{26}
\]
Therefore
\[
 P(x)>.123-1.626x+15.99x^2
       \ge .123-\frac{1.626^2}{4(15.99)}>.0816>0.
\tag{27}
\]
Positive squaring gives (25).

For (17), k has positive coefficients and its endpoint values
give the stated range. The quotients
\((l(t)-l(0))/t\) and \((c(t)-c(0))/t\) are convex quadratics
negative at both endpoints, proving the two upper bounds.
The lower bounds follow from one completed square. For either
polynomial p=l,c, write
\[
 p(1-v)=A_0+A_1v+A_2v^2+A_3v^3,\qquad A_3<0.
\]
Expand at \(v_0=1/25\), with \(w=v-v_0\):
\[
 p(1-v)=b_0+b_1w+b_2w^2+b_3w^3
 \ge b_0+b_1w+\{b_2+b_3(1-v_0)\}w^2.
\tag{28}
\]
The brace is positive. Completing the square in (28) gives,
respectively, bounds strictly larger than .863 and .862.

For the G-pair ratio,
\[
 \frac32k-l
 =.000168+.316988t+.167498t^2-.149276t^3+.0015t^4>0.
\tag{29}
\]
The other ratio comparisons have the exact aggregate bounds
\[
 \mathcal C_{[0,1]}(1.017l-c)>.0002596,\qquad
 \mathcal C_{[0,1]}(c-.9l)>0.
\tag{30}
\]
For \(0\le z\le h\), concavity and the endpoints give
\[
             .95<\cos z+\eta\sin z<1.043.
\tag{31}
\]
The upper bound also follows from
\(1+\eta^2<1.043^2\). Thus
\(m>.862(.95)>.800408\) and
\(m/l<1.017(1.043)<1.061\).
This proves all pair ratios. To check the final q-ratio in
(19), if \(l<1\) and \(m\le1\), use \(l>.863>25/29\);
if \(l<1<m\), use \(m/l<1.061\); and if \(l\ge1\),
use \(q_{\max}<1.066<29/25\).

Finally the exact difference in (20), in the variable t, is
\[
\begin{split}
 1.073-.3\theta-c
   ={}&.001752(1-t)+.000062t\\
      &+t(1-t)(.010563+.175944t)\ge.000062>0.
\end{split}
\tag{32}
\]

## 5. A polynomial envelope for the A support

The exact sorted support in (4) gives
\[
 j(a)=\frac{\cos a-1}{2}+\left(\frac12-a_0\right)\sin a
\]
up to its intrinsic axis transition \(a_{\rm ax}>1/2\).
Beyond it, the amount by which the right side exceeds j is
\[
 2R\sin(a/2)
             \left\{1-\cos\frac{a-a_{\rm ax}}2\right\}
       \le \frac{Ra(a-\tfrac12)^2}{8}.
\tag{33}
\]
This is the exact support comparison in Section 7 of
[the split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
For \(1/2\le a\le h\), the ratio
\[
                    \frac{a(a-\tfrac12)^2}{(a-L)^6}
\]
increases: its derivative has the sign of
\(-3a^2+2a+1/12\), which is positive on this interval and
equals \(1/75\) at h. Since \(R<1.978787508\),
\[
 \frac{1.978787508\,h(h-\tfrac12)^2}{8(h-L)^6}
             =\frac{2524438163331}{8388608000000}<.302.
\tag{34}
\]
Consequently the single whole-high-interval envelope
\[
 j(\theta)\ge
 \frac{\cos\theta-1}{2}
       +\left(\frac12-a_0\right)\sin\theta
                         -.302(\theta-L)^6
\tag{35}
\]
is valid on \(I_1\). On \(I_0\), the same expression without
the final term is exact. This sixth-power allowance avoids
any auxiliary angle subdivision.

## 6. Exact polynomial conventions

Let \(S_j,C_j\) be the alternating sine and cosine polynomials
ending in degree j. Throughout \(0\le\theta\le h\), put
\[
 S_-=S_{11}(\theta),\quad S_+=S_9(\theta),\qquad
 C_-=C_{10}(\theta),\quad C_+=C_{12}(\theta).
\tag{36}
\]
They bound sine and cosine in the indicated directions. Use
\[
\begin{gathered}
 R_-=1.978787507,\qquad \overline R=1.978787508,\\
 \overline c=.899214066,\qquad
 \overline a=1.414575672,\qquad
 \overline\sigma=1.415477291.
\end{gathered}
\tag{37}
\]
Their strict bounds follow by positive squaring:
\[
\begin{gathered}
 R_-^2<Q<\overline R^2,\quad
 (\overline c+\tfrac12)^2>Q/2,\quad
 (\overline a+\tfrac12)^2>Q-\tfrac14,\\
 \left(\overline\sigma+\frac{1+\eta}{2}\right)^2
                                      >Q(1+\eta^2).
\end{gathered}
\tag{38}
\]
Define
\[
 J_0=\frac{C_--1}{2}+\left(\frac12-\overline a\right)S_+,
 \qquad J_1=J_0-.302(\theta-L)^6.
\tag{39}
\]

For a polynomial B, positive auxiliary polynomials \(r_i\),
and polynomial upper bounds \(P_i\) of squared norms, define
\[
\begin{split}
 D&=2\prod_i r_i,\\
 \mathcal N(B;\mathbf r;\mathbf P)
  &=DB-\overline R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.
\end{split}
\tag{40}
\]
The elementary inequality
\(\sqrt{P_i}\le(P_i+r_i^2)/(2r_i)\) implies
\[
             B-\overline R\sum_i\sqrt{P_i}\ge
                    \frac{\mathcal N(B;\mathbf r;\mathbf P)}D.
\tag{41}
\]
It is enough to prove the numerator positive.

Here are the explicit aggregate conventions used to do so.
On \(I=[\alpha,\beta]\), let
\[
 p\left(\frac{\alpha+\beta}{2}
                +\frac{\beta-\alpha}{2}x\right)
                    =\sum_{j=0}^n b_jT_j(x),\qquad -1\le x\le1.
\tag{42}
\]
The \(T_j\) are the Chebyshev polynomials. No evaluation nodes
are used: if the centered power coefficients are \(a_j\) and
\(\rho=(\beta-\alpha)/2\), their coefficients are given by
\[
 x^n=
 \begin{cases}
 2^{1-n}\displaystyle\sum_{r=0}^{(n-1)/2}
                   \binom nr T_{n-2r}(x),& n\text{ odd},\\[4pt]
 2^{-n}\binom n{n/2}
 +2^{1-n}\displaystyle\sum_{r=0}^{n/2-1}
                   \binom nr T_{n-2r}(x),& n\text{ even}.
 \end{cases}
\tag{43}
\]
Apply (43) linearly to \(\sum a_j\rho^jx^j\).
Define
\[
\begin{split}
 \mathcal C_I(p)&=b_0-\sum_{j\ge1}|b_j|,\qquad
 \mathcal U_I(p)=b_0+\sum_{j\ge1}|b_j|,\\
 \mathcal Q_I(p)&=b_0-b_2-\frac{b_1^2}{8b_2}
                              -\sum_{j\ge3}|b_j|\quad(b_2>0),\\
 A_I(p)&=2b_2-4|b_3|,\\
 \mathcal K_I(p)&=b_0-b_2-\sum_{j\ge4}|b_j|
                -\frac{(b_1-3b_3)^2}{4A_I(p)}
                                      \quad(A_I(p)>0).
\end{split}
\tag{44}
\]
Each lower aggregate is a lower bound for p on I.
For the last one, use
\(4b_3x^3\ge-4|b_3|x^2\) and complete the square.
For the low interval, also expand
\[
             p(L-x)=\sum a_jx^j,\qquad 0\le x\le L,
\]
and use the endpoint aggregate
\[
             \mathcal R(p)
                =a_0-\sum_{\substack{j\ge1\\a_j<0}}|a_j|L^j.
\tag{45}
\]
All these are single whole-interval coefficient identities.

## 7. Low endpoint numerators

In this section use (16). Superscripts T and A denote the
split endpoints \((a,z)=(0,\theta)\) and \((\theta,0)\).
For T define
\[
\begin{gathered}
 m_-=c(C_-+\eta S_-),\qquad
 m_+=c(C_++\eta S_+),\qquad
 \mu=c(C_2+\eta\theta),\\
 E=2k+3l+\frac32m_-+\frac52
       +\frac c2(1+C_-+S_-)-c\overline\sigma S_+.
\end{gathered}
\tag{46}
\]
For A define
\[
 m_-=m_+=\mu=c,\qquad
             E=2k+3l+\frac52c+\frac52+lJ_0.
\tag{47}
\]
In either case put
\[
 B=E-\overline c(1+c),
\tag{48}
\]
and introduce the norm polynomials
\[
\begin{gathered}
 P_H=1+k^2,\qquad P_G=k^2+l^2,\qquad P_B=m_+^2+l^2,\\
 P_{H,-}=P_H-2kS_-,\\
 c_h=C_{10}(h),\quad C_h=C_{12}(h),\quad
 s_h=S_{11}(h),\\
 P_{H,h}=P_H-2ks_h,\qquad P_{G,h}=P_G-2kls_h.
\end{gathered}
\tag{49}
\]
The positive auxiliary polynomials are
\[
\begin{gathered}
 r_H=.82+.572k,\qquad r_G=.55k+.835l,\qquad
 r_B=.729\mu+.6845l,\\
 r_{H,-}=.89C_2+.456(k-S_3),\qquad
 r_{H,h}=.77,\qquad r_{G,h}=.765l.
\end{gathered}
\tag{50}
\]

The first numerator is
\[
 N_{0H}=\mathcal N\bigl(B+C_--1;\
          (r_{H,-},r_G,r_B);\
          (P_{H,-},P_G,P_B)\bigr).
\tag{51}
\]
Write its denominator (40) as \(D_{0H}\). For the G
same-block lower bound in (12), define
\[
\begin{split}
 Z_G={}&k\{(c_h+s_h)C_--(C_h-s_h)S_+-1\}
                                  +l(c_h-C_+),\\
                     N_{0M}&=N_{0H}+D_{0H}Z_G.
\end{split}
\tag{52}
\]
The two separated numerators are
\[
\begin{split}
 N_{0SH}&=\mathcal N\bigl(
 B-\tfrac{109}{200}m_+(h-\theta)+c_h-1;\
 (r_{H,h},r_G,r_B);\
 (P_{H,h},P_G,P_B)\bigr),\\
 N_{0SG}&=\mathcal N\bigl(
 B-\tfrac{109}{200}m_+(h-\theta)+l(c_h-1);\
 (r_H,r_{G,h},r_B);\
 (P_H,P_{G,h},P_B)\bigr).
\end{split}
\tag{53}
\]

At \(s=\theta\), multiply the scalar by \(\cos\theta>0\).
D is diagonal. With \(\overline d=\overline c-1/2\), define
\[
\begin{split}
 N_Z=\mathcal N\bigl(&C_-(B+\overline d)+KS_--\overline d;\
 (C_4r_H,C_4r_G,C_4r_B);\
 (C_+^2P_H,C_+^2P_G,C_+^2P_B)\bigr).
\end{split}
\tag{54}
\]
The coefficient \(B+\overline d\) is positive throughout
the interval; in fact its aggregate \(\mathcal C_{I_0}\)
is larger than one. Thus the multiplication uses the lower
cosine in the correct direction.

The squared norms in (49) and (54) are upper bounds:
positive squared terms use upper trigonometric approximations,
and every subtracted positive product uses lower ones.
Every auxiliary in (50) and (54) satisfies the exact
whole-interval bounds
\[
          \min_i\mathcal C_{I_0}(r_i)>.74,\qquad
             \mathcal C_{I_0}(B+\overline d)>1.
\tag{55}
\]

Here are exact rational aggregate inequalities for these
explicit polynomials. For the T endpoint:
\[
\begin{gathered}
 \deg N_{0H}=33,\qquad \mathcal R(N_{0H})>.0018458,\\
 \deg N_{0M}=33,\qquad \mathcal Q_{I_0}(N_{0M})>.0304587,\\
 \deg N_{0SH}=30,\qquad \mathcal C_{I_0}(N_{0SH})>.3021758,\\
 \deg N_{0SG}=32,\qquad \mathcal C_{I_0}(N_{0SG})>.1617320,\\
 \deg N_Z=64,\qquad \mathcal R(N_Z)>.0018219.
\end{gathered}
\tag{56}
\]
For the A endpoint:
\[
\begin{gathered}
 \deg N_{0H}=19,\quad
 \mathcal U_{I_0}(N_{0H}')<-.9115,\quad
                         N_{0H}(L)>.0125371,\\
 \deg N_{0M}=21,\qquad \mathcal C_{I_0}(N_{0M})>.0475408,\\
 \deg N_{0SH}=16,\qquad \mathcal C_{I_0}(N_{0SH})>.3024216,\\
 \deg N_{0SG}=18,\qquad \mathcal C_{I_0}(N_{0SG})>.1682265,\\
 \deg N_Z=40,\quad
 \mathcal U_{I_0}(N_Z')<-.8814,\quad N_Z(L)>.0129080.
\end{gathered}
\tag{57}
\]
Every displayed lower bound is positive, with the two
derivative bounds placing the corresponding minima at L.
Equations (40)--(57) are exact definitions and finite rational
coefficient sums, not values sampled at angle points.
They prove (12)--(13) at both split endpoints.

## 8. High endpoint numerators

Now use (17). For the T endpoint, set
\[
\begin{gathered}
 m_-=c(C_-+\eta S_-),\quad
 m_+=c(C_++\eta S_+),\quad
 \mu=c(C_4+\eta S_5),\\
 B=2k+3l+\frac32m_-+\frac c2+3
       +\frac c2(1+C_-+S_-)-c\overline\sigma S_+.
\end{gathered}
\tag{58}
\]
For the A endpoint, set
\[
 m_-=m_+=\mu=c,\qquad B=2k+3l+3c+3+lJ_1.
\tag{59}
\]
Here B already includes all four shifted full-circle constants.
Use
\[
\begin{gathered}
 P_H=1+k^2,\quad P_G=k^2+l^2,\quad
 P_B=m_+^2+l^2,\quad P_D=1+c^2,\\
 P_{H,-}=P_H-2kS_-,\quad
 P_{G,-}=P_G-2klS_-,\quad
 P_{B,-}=P_B-2lm_-S_-,
\end{gathered}
\tag{60}
\]
and positive auxiliaries
\[
\begin{gathered}
 r_H=.8+.6k,\qquad r_G=.62k+.7846l,\qquad
 r_B=.7071(l+\mu),\qquad r_D=.72+.694c,\\
 r_{H,-}=.93C_4+.3676(k-S_5),\\
 r_{G,-}=.93lC_4+.3676(k-lS_5),\\
 r_{B,-}=.83lC_4+.56(\mu-lS_5).
\end{gathered}
\tag{61}
\]
For the B cosine coefficient use
\[
                   q_*:=l+.15(h-\theta)\ge\max(l,m).
\tag{62}
\]
For the A endpoint this follows from
\[
             \mathcal C_{I_1}(q_*-c)=.000796.
\]
For T, \(m\le c(C_4+\eta S_5)\), and
\[
 \mathcal Q_{I_1}\{q_*-c(C_4+\eta S_5)\}>.0051799.
\tag{63}
\]
Because \(\cos\theta-1\le0\), this is a lower-bound
replacement of the B coefficient, including the part of the
interval where \(m>l\).

The three \(s=0\) numerators are
\[
\begin{split}
 N_{0H}&=\mathcal N\bigl(B+C_--1;\
       (r_G,r_B,r_{H,-},r_D);\
       (P_G,P_B,P_{H,-},P_D)\bigr),\\
 N_{0G}&=\mathcal N\bigl(B+l(C_--1);\
       (r_H,r_B,r_{G,-},r_D);\
       (P_H,P_B,P_{G,-},P_D)\bigr),\\
 N_{0B}&=\mathcal N\bigl(B+q_*(C_--1);\
       (r_H,r_G,r_{B,-},r_D);\
       (P_H,P_G,P_{B,-},P_D)\bigr).
\end{split}
\tag{64}
\]
For \(s=\theta\), multiply by \(\cos\theta\) and define
\[
\begin{split}
 N_Z=\mathcal N\bigl(&C_-(B-1)+1+KS_-;\
 (C_4r_H,C_4r_G,C_4r_B,.758+.652cC_4);\
 (C_+^2P_H,C_+^2P_G,C_+^2P_B,1+c^2C_+^2)\bigr).
\end{split}
\tag{65}
\]
The aggregate of \(B-1\) is larger than one. All auxiliaries
in (61), (64), and (65) have whole-interval lower bounds
larger than .60.

## 9. High whole-interval positivity

The T-endpoint polynomials in (64)--(65) satisfy
\[
\begin{gathered}
 \deg N_{0H}=42,\quad
 \mathcal C_{I_1}(N_{0H}')>.0275690,\quad
                           N_{0H}(L)>.0012686,\\
 \deg N_{0G}=45,\quad A_{I_1}(N_{0G})>.0046795,\quad
                    \mathcal K_{I_1}(N_{0G})>.0006044,\\
 \deg N_{0B}=41,\qquad
                    \mathcal C_{I_1}(N_{0B})>.0016343,\\
 \deg N_Z=77,\qquad \mathcal Q_{I_1}(N_Z)>.0003948.
\end{gathered}
\tag{66}
\]
The A-endpoint polynomials satisfy
\[
\begin{gathered}
 \deg N_{0H}=28,\quad
 \mathcal C_{I_1}(N_{0H}')>.0077290,\quad
                           N_{0H}(L)>.0010199,\\
 \deg N_{0G}=31,\quad A_{I_1}(N_{0G})>.0035767,\quad
                    \mathcal K_{I_1}(N_{0G})>.0003537,\\
 \deg N_{0B}=32,\qquad
                    \mathcal C_{I_1}(N_{0B})>.0669354,\\
 \deg N_Z=54,\qquad \mathcal Q_{I_1}(N_Z)>.0001815.
\end{gathered}
\tag{67}
\]
The derivative conditions put the two H minima at L.
The G conditions use a completed square after retaining the
cubic Chebyshev term. The other conditions use the whole
interval aggregate or quadratic completion. This proves all
four functions in (15) at both split endpoints.

## 10. The high endpoint derivative inequalities

For high-angle E concentration, the s-dependent full-D part is
\[
 F_0(s)=\sec s+K\tan s-R\sqrt{\sec^2s+c^2},
\tag{68}
\]
up to an s-independent constant. Its derivative is
\[
 F_{0,s}(s)
  =\frac{K+\sin s-R\sin s/\sqrt{1+c^2\cos^2s}}{\cos^2s}.
\tag{69}
\]
The two required endpoint inequalities are
\[
 F_{0,s}(\theta)<
      \frac{Rk}{\sqrt{1+k^2}},\qquad
 F_{0,s}(\theta)<
      \frac{Rkl}{\sqrt{k^2+l^2}}
                       \qquad(\theta\in I_1).
\tag{70}
\]
Since \(m\ge k\), the corresponding B comparison follows
from the monotonicity of \(xy/\sqrt{x^2+y^2}\) in each
positive coordinate.

For completeness, here are exact polynomial certificates of
(70), using only one reciprocal-norm bound:
\[
                 \frac1{\sqrt P}\ge\frac{2r}{P+r^2}
                              \qquad(P,r>0).
\tag{71}
\]
Use \((P,r,f)=(P_H,r_H,k)\) and \((P_G,r_G,kl)\) from
(60)--(61), and put
\[
 P_d=1+c^2C_+^2,\quad r_d=.758+.652cC_4,\quad
 A=P+r^2,\quad D=P_d+r_d^2.
\]
Define
\[
 \mathcal D(P,r,f)
   =2R_-\,r f C_-^2D+2R_-\,r_d S_-A-(K+S_+)AD.
\tag{72}
\]
Both A and D are positive, and every auxiliary is larger
than .9. The exact aggregate bounds are
\[
\begin{split}
 \deg\mathcal D(P_H,r_H,k)&=58,&
 \mathcal C_{I_1}\{\mathcal D(P_H,r_H,k)\}&>.5310,\\
 \deg\mathcal D(P_G,r_G,kl)&=61,&
 \mathcal C_{I_1}\{\mathcal D(P_G,r_G,kl)\}&>.04744.
\end{split}
\tag{73}
\]
After division by AD, (71) shows that these are lower
bounds for
\[
 \frac{Rf\cos^2\theta}{\sqrt P}
 +\frac{R\sin\theta}{\sqrt{1+c^2\cos^2\theta}}
                                      -(K+\sin\theta).
\]
Thus (73) proves (70).

## 11. Completion and exact-arithmetic scope

All defining coefficients in (16)--(17), (36)--(40),
(46)--(55), (58)--(65), and (72) are explicit rationals.
The coefficient formula (43) determines every aggregate
in (24), (30), (56)--(57), (63), (66)--(67), and (73)
without any numerical evaluation of an angle. The elementary
range identities and completed squares establish all
coefficient hypotheses on each full interval.

The E-angle concentration theorem reduces a feasible necessary
system to (12), (13), and (15). At its intrinsic s-endpoints, split
concavity reduces to the A and T endpoints certified here.
Every resulting function is strictly positive, whereas a
positive weighted sum of the actual separating inequalities
requires the corresponding stress to be nonpositive.
This contradiction proves the claim in Section 1.

This theorem retains BT2 and EH0 and the stated nonnegative
A-primary total and positive-TD2 scope. It does not assert
an arbitrary-owner E transport or replace a remaining
primary witness by a secondary one.
