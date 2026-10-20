# Positive GA1 with three aligned zero edges and a nonpositive H/D span

## 1. Scope and conclusion

Put
\[
 Q=9789/2500,\qquad R=\sqrt Q,\qquad h=7/10,
 \qquad L=447/800,\quad \kappa_0=L+1/2=847/800.
\tag{1}
\]
All terminating decimals below are exact rational numbers.
Consider a necessary seven-cycle in roles H,G,A,B,T,D,E.
Each own-frame state is sorted, satisfies the true central
exclusion, and has shifted corner square at most Q. The signed
tangents are normal: H,A,T are nonnegative and G,B,D,E are
nonpositive. The frame spread is at most h. Retain actual weak
witnesses HG, AB and TD at zero error, GA1, BT2, DE3 and EH1.
Write the three common frames as
\[
 \theta_H=\theta_G=\alpha,\qquad
 \theta_A=\theta_B=u,\qquad
 \theta_T=\theta_D=0,
\]
and put
\[
                 x=u-\alpha\ge0,\qquad s=-\alpha=x-u\ge0.
\tag{2}
\]
No order condition is imposed on E's frame. In particular, the
two E-primary errors may have opposite signs. Their signed sum
is \(\alpha=-s\). A state need not lie on its shifted circle.

**Theorem.** No necessary cycle with these hypotheses exists.
This includes \(x=0\), \(s=0\), either sign of u, every E
radial kind, and all weak ties between the retained witnesses.
The final contradiction is strict at Q.

This is an entry-branch exclusion, not the unrestricted normal
primary-entry theorem. The three zero-edge alignments and the
two E-primary witnesses are hypotheses. In particular, the
argument does not replace an arbitrary AB or TD error by zero.

The proof uses four continuous scalar endpoint inequalities.
Their certificates are single rational polynomials on their
whole intervals; there is no angular sampling or subdivision.

## 2. A negative primary-pair charge on the entire frame interval

The following elementary estimate is useful independently of
the aligned-cycle hypotheses. Suppose
\[
 A\ge |Y|,\qquad A\ge L,\qquad p+q=-s,\qquad
 0\le s\le h,\quad |p|,|q|\le h,
\]
and define
\[
 \begin{split}
 \mathcal L={}&W(p)+W(q)-2-A(\sin p+\sin q)
                         -Y(\cos q-\cos p),\\
 W(z)&=(1+\cos z+|\sin z|)/2,\qquad
 \phi(z)=\sin z+\cos z.
 \end{split}
\]
Then
\[
                   \mathcal L\ge\kappa_0\{\phi(s)-1\}.
\tag{3}
\]

To prove this, put \(C=\cos(s/2)\), \(S=\sin(s/2)\) and
\(\Delta=|p-q|/2\). If both errors are nonpositive, then
\(0\le\Delta\le s/2\), and
\[
 \mathcal L\ge(C+2AS)\cos\Delta-2|Y|S\sin\Delta-1.
\]
The right side decreases in \(\Delta\). At its right endpoint
it equals
\[
 (A+1/2)\sin s-(1/2+|Y|)(1-\cos s)
 \ge(A+1/2)\{\phi(s)-1\},
\]
which implies (3).

If the errors have opposite signs, then
\(s/2\le\Delta\le h-s/2\). Using \(|Y|\le A\),
\(\Delta\le h<\pi/4\), and \(A\ge L\), gives
\[
 \mathcal L\ge f(\Delta)
  :=(C+2LS)\cos\Delta+(C-2LS)\sin\Delta-1.
\tag{4}
\]
Both coefficients are positive, so f is concave. Its near
endpoint is exactly \(\kappa_0(\phi(s)-1)\). Write
\(c_h=\cos(h/2)\), \(s_h=\sin(h/2)\). The far endpoint
minus the near one is
\[
 2\sin((h-s)/2)
       \{C(c_h-s_h)-2LS(c_h+s_h)\}.
\tag{5}
\]
The expression in braces is positive. Indeed
\(S/C\le s_h/c_h\), and multiplication by \(c_h\) reduces
the required sign to
\[
 c_h^2-(1+2L)c_hs_h-2Ls_h^2>0.
\]
Use \(c_h\ge751/800\), \(s_h\le7/20\), \(c_h\le1\):
\[
 (751/800)^2-(1+2L)(7/20)-2L(7/20)^2
                      =.0032328125>0.
\tag{6}
\]
Thus both intrinsic endpoints of (4) satisfy (3), proving
the estimate on the entire interval \(0\le s\le h\).

Apply (3) to the actual DE3/EH1 pair. Its projections are
\[
 a_D+a_E\sin d+b_E\cos d,\qquad
 a_H+a_E\sin e-b_E\cos e,
\quad d+e=-s.
\]
Use \(A=a_E\), \(Y=-b_E\) in (3). Sorting and the true-core
bound supply its hypotheses. Consequently
\[
                   a_H+a_D\ge2+\kappa_0\{\phi(s)-1\}.
\tag{7}
\]

## 3. The exact aligned-chain stress

The retained aligned inequalities and the two quarter
inequalities are
\[
 \begin{split}
 b_H+b_G&\ge1,\qquad b_A+b_B\ge1,\qquad b_T+b_D\ge1,\\
 a_A+a_G\sin x-b_G\cos x&\ge W(x),\\
 a_B\cos u-b_B\sin u-b_T&\ge W(u).
 \end{split}
\tag{8}
\]
For \(0\le x\le h\), choose
\[
 \begin{split}
 k&=.8626-.45x-.37x^2,\\
 l&=.5052+.57x-1.2x^2,\\
 m&=.8626+.63x-1.06x^2,\\
 \eta&=.383+.05x+.64x^2,\\
 n&=k(\cos x+\eta\sin x).
 \end{split}
\tag{9}
\]
These weights are positive. In particular
\(k\ge.3663\), \(l\ge.3162\), \(m\ge.7842\),
\(\eta\ge.383\), and
\[
                     m-l=.3574+.06x+.14x^2>0.
\tag{10}
\]

Multiply HG, GA1, AB, BT2 and TD in (8) by
\(n,k,l,m,m\), respectively, and add \(a_H+a_D\).
The resulting forces at H,G,A,B,D are
\[
 (1,n),\quad k\sin x(1,\eta),\quad(k,l),\quad
        (m\cos u,l-m\sin u),\quad(1,m).
\tag{11}
\]
The T tangent cancels exactly. For any shifted circle at most Q,
Cauchy's inequality gives the full-circle support bound
\[
             fa+gb\le\overline S(f,g)
                :=R\sqrt{f^2+g^2}-(f+g)/2.
\tag{12}
\]
It remains valid for a negative coefficient. Thus (8)--(12)
give
\[
                          a_H+a_D\le2-N(x,u),
\tag{13}
\]
where
\[
 \begin{split}
 N(x,u)={}&3+k+2l+2m+2k\cos x+k(1+2\eta)\sin x\\
 &+m\cos u+m(-\sin u)_+\\
 &-R\big\{\sqrt{1+n^2}+k\sin x\sqrt{1+\eta^2}
                 +\sqrt{k^2+l^2}\\
 &\hspace{35mm}+\sqrt{m^2+l^2-2ml\sin u}
                 +\sqrt{1+m^2}\big\}.
 \end{split}
\tag{14}
\]
No radial equality was used in this stress.

The frame interval and (2) imply
\[
                      0\le x\le h,\quad x-h\le u\le x.
\tag{15}
\]
There is a useful further bound when u is positive:
\[
                               u<2/5.
\tag{16}
\]
Indeed sorting gives every tangent less than .9. AB in (8)
therefore gives \(b_B>.1\), and B's actual circle gives
\(a_B<1.386\). Combining BT2 and TD yields
\[
 (a_B-1/2)\cos u-(b_B+1/2)\sin u
                            \ge3/2-b_D>.6.
\]
Its left side is less than \(.886\cos u-.6\sin u\), a
strictly decreasing function on \([0,h]\). At \(u=2/5\),
the upper cosine and lower sine Taylor bounds give
\[
 .886\{1-u^2/2+u^4/24\}-.6\{u-u^3/6\}<.583<.6.
\]
This proves (16).

To contradict (7) and (13), it is enough to prove
\[
 F(x,u):=N(x,u)+\kappa_0\{\phi(x-u)-1\}>0
\tag{17}
\]
on the closed enlargement of (15)--(16).

## 4. Concavity leaves four intrinsic endpoints

Fix x, hence all weights in (9), and put \(r=l/m\in(0,1)\).
The u-dependent part of N, normalized to zero at u=0, is
\[
 \begin{split}
 V(u)&=m(\cos u-1)
       -R\{\sqrt{m^2+l^2-2ml\sin u}-\sqrt{m^2+l^2}\},
                  &&u\ge0,\\
 U(z)&=m(\phi(z)-1)
       -R\{\sqrt{m^2+l^2+2ml\sin z}-\sqrt{m^2+l^2}\},
                  &&u=-z\le0.
 \end{split}
\tag{18}
\]
Both U and V are strictly concave on \([0,h]\), for every
\(0<r\le1\). Here is a verification that does not assume
the sometimes-used ratio restriction \(r\ge1/2\).

Write \(s_z=\sin z\), \(c_z=\cos z\) and
\(D_\pm=\sqrt{1+r^2\pm2rs_z}\). Then
\[
 \frac{U''}{m}=-(c_z+s_z)+R
          \left\{\frac{rs_z}{D_+}+\frac{r^2c_z^2}{D_+^3}\right\}.
\]
The expression in braces increases with r on \((0,1]\).
After multiplying its derivative by a positive denominator,
its numerator is
\[
 s_z(1+rs_z)(1+r^2+2rs_z)
                  +c_z^2r(2-r^2+rs_z)\ge0.
\]
At r=1 the braces equal \(\sqrt{1+s_z}/(2\sqrt2)\).
Since \(R<2\), \(\phi(z)\ge1\), and \(s_z<.65\),
this proves \(U''<0\).

Similarly
\[
 \frac{V''}{m}=-c_z+
       R\frac{r(r-s_z)(1-rs_z)}{D_-^3}.
\tag{19}
\]
If \(r\le s_z\), its sign is already negative. Otherwise
the positive fraction increases with r. The numerator of its
r derivative, after multiplication by a positive denominator,
is
\[
 r^3(2s_z^2-1)-s_zr^2(2+s_z^2)+r(2+s_z^2)-s_z.
\]
It is concave in r on \([s_z,1]\), since \(s_z<.65<1/\sqrt2\).
Its endpoint values are \(s_z(1-s_z^2)^2\) and
\((1-s_z)^3\), both nonnegative. At r=1 the fraction in
(19) equals \(\sqrt{1-s_z}/(2\sqrt2)\). This is less than
\(c_z/R\), proving \(V''<0\).

The last summand of F in (17) is also concave in u.
Consequently F is strictly concave on each of
\[
                 [x-h,0],\qquad [0,\min(x,2/5)].
\]
Its minimum is attained among precisely these endpoint
functions:
\[
\begin{array}{c|c|c|c}
\text{label}&u&s=x-u&\text{x interval}\\ \hline
X&x&0&[0,2/5]\\
O&0&x&[0,h]\\
F&x-h&h&[0,h]\\
C&2/5&x-2/5&[2/5,h].
\end{array}
\tag{20}
\]
These are endpoints of the actual analytic minimization,
including the necessary bound (16), not sampled cases.

## 5. Four exact whole-interval certificates

Use the alternating Taylor polynomials
\[
 S_j(z)=\sum_{i=0}^{(j-1)/2}\frac{(-1)^iz^{2i+1}}{(2i+1)!},
 \qquad
 C_j(z)=\sum_{i=0}^{j/2}\frac{(-1)^iz^{2i}}{(2i)!}.
\]
On \([0,h]\), set
\[
       S_-=S_{11}\le\sin\le S_9=S_+,
       \qquad C_-=C_{10}\le\cos\le C_{12}=C_+.
\tag{21}
\]
For the G radical, the elementary positive-mass inequality
\(R\sqrt Z\le Q\mu+Z/(4\mu)\), at \(\mu=7/25\), gives
\[
 G_*(x)=Q(7/25)+(1+\eta^2)/(28/25)
                        \ge R\sqrt{1+\eta^2}.
\tag{22}
\]
Define \(n_+=k(C_+(x)+\eta S_+(x))\), so \(n\le n_+\).

For each row of (20), the following are lower cosine and
sine data used in its B block. The last column is the lower
bound for \(m(-\sin u)_+\):
\[
\begin{array}{c|c|c|c}
&c_B&s_B&e_B\\ \hline
X&C_-(x)&S_-(x)&0\\
O&1&0&0\\
F&C_-(h-x)&-S_+(h-x)&mS_-(h-x)\\
C&C_-(2/5)&S_-(2/5)&0.
\end{array}
\tag{23}
\]
In particular \(s_B\le\sin u\) even in the negative row.
For the appropriate s from (20), put
\[
 \begin{split}
 B_*={}&3+k+2l+2m+2kC_-(x)+k(1+2\eta)S_-(x)
              +mc_B+e_B\\
       &-kS_+(x)G_*(x)
                    +\kappa_0\{S_-(s)+C_-(s)-1\},\\
 Z_H={}&1+n_+^2,\quad Z_A=k^2+l^2,\\
 Z_B={}&m^2+l^2-2mls_B,\quad Z_D=1+m^2.
 \end{split}
\tag{24}
\]
Each Z is an upper bound for the corresponding squared norm
in (14). All estimates in (21)--(24) have the required
direction, including the negative sign before the G support.

Use these fixed positive rational mass polynomials:
\[
 \begin{split}
 \mu_H={}&.3337034-.019974x-.1523945x^2+.1168558x^3-.0323545x^4,\\
 \mu_A={}&.2525877-.0249256x-.1743984x^2-.1162378x^3+.0518704x^4,\\
 \mu_D={}&.3336997+.1039263x-.1535742x^2-.0717423x^3+.0604541x^4.
 \end{split}
\tag{25}
\]
The B mass depends only on the intrinsic endpoint:
\[
 \begin{split}
 \mu_{B,X}={}&.2525929+.099921x-.5162674x^2+.1800659x^3+.107877x^4,\\
 \mu_{B,O}={}&.2526055+.2093237x-.3729143x^2-.0441765x^3+.0515538x^4,\\
 \mu_{B,F}={}&.3157017+.2046503x-.5971197x^2+.0428184x^3+.1356038x^4,\\
 \mu_{B,C}={}&.2123234+.1002024x-.0833135x^2-.3108043x^3+.1978061x^4.
 \end{split}
\tag{26}
\]
Simply dropping each positive nonconstant term and replacing
x by its right endpoint in each negative term gives
\[
 \mu_H>.23,\quad\mu_A>.10,\quad\mu_D>.23,
\]
\[
 \mu_{B,X}>.16,\quad\mu_{B,O}>.05,\quad
 \mu_{B,F}>.02,\quad\mu_{B,C}>.06.
\tag{27}
\]

For each row, let \(I=\{H,A,B,D\}\), with its B mass from
(26), and form the rational polynomial
\[
 P=4\prod_{i\in I}\mu_i
            \left(B_*-Q\sum_{i\in I}\mu_i\right)
             -\sum_{i\in I}Z_i\prod_{j\ne i}\mu_j.
\tag{28}
\]
Equations (12), (21)--(27) imply
\[
                  F(x,u)\ge\frac{P(x)}{4\prod_i\mu_i(x)}.
\tag{29}
\]
Each P has degree 40. We use compact Chebyshev norm
certificates, including one positive endpoint quotient and
one negative derivative. For a rational polynomial p and a
rational interval \([a,b]\), write
\[
 p\left(\frac{a+b}{2}+\frac{b-a}{2}t\right)
        =\sum_{j=0}^d v_jt^j=\sum_{j=0}^d c_jT_j(t),
 \qquad |t|\le1,
\tag{30}
\]
where \(T_j\) is the usual Chebyshev polynomial. No recurrence
or numerical conversion is needed: the exact coefficients are
\[
 c_0=\sum_{2i\le d}v_{2i}2^{-2i}\binom{2i}{i},
 \qquad
 c_j=\sum_{\substack{r\ge j\\r-j\text{ even}}}
           v_r2^{1-r}\binom r{(r-j)/2}\quad(j\ge1).
\tag{31}
\]
Define the two exact rational norms
\[
 \mathscr L_{[a,b]}p=c_0-\sum_{j\ge1}|c_j|,
 \qquad
 \mathscr U_{[a,b]}p=c_0+\sum_{j\ge1}|c_j|.
\tag{32}
\]
Since \(|T_j(t)|\le1\), these bound p below and above on its
entire interval. Substitution of (24)--(28) in the single
formula (31) gives these four certificates:

* For X, put \(q_X(x)=(P_X(x)-P_X(0))/x\), with its polynomial
  value at zero. Then
  \[
   P_X(0)>9/100000,
   \qquad\mathscr L_{[0,2/5]}q_X>174/100000.
  \tag{33}
  \]
  Hence \(P_X(x)>9/100000\) on its whole interval.
* Directly for O,
  \[
                   \mathscr L_{[0,7/10]}P_O>34/10^6.
  \tag{34}
  \]
* For F,
  \[
    \mathscr U_{[0,7/10]}P_F'<-274/100000,
    \qquad P_F(7/10)>24/100000.
  \tag{35}
  \]
  Thus \(P_F\) decreases and is positive throughout.
* Directly for C,
  \[
                  \mathscr L_{[2/5,7/10]}P_C>27/100000.
  \tag{36}
  \]

These are exact rational coefficient-norm inequalities,
not inventories of angular cases. Equations (24)--(28) and
(30)--(32) completely specify each side using only polynomial
arithmetic, binomial coefficients and absolute values of
rational numbers. In particular, no sine, cosine or square
root is evaluated in their verification. Together with (27)
and (29), they prove the four strict endpoint inequalities
in (20).

## 6. Contradiction and equality scope

Concavity in Section 4 now proves (17) on the entire domain
(15)--(16). But the actual E pair gives (7), while the actual
aligned chain gives (13). Together they would require
\[
       0\ge N(x,u)+\kappa_0\{\phi(x-u)-1\}=F(x,u)>0.
\]
This contradiction includes all original weak inequalities.
The branch is excluded at the ceiling Q itself, so there is
no equality case to pass to the sharp hard-owner theorem.
The proof does not require strict slack in an original
witness; strictness comes from the polynomial reserves.
