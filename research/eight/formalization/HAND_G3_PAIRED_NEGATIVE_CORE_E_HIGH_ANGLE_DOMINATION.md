# Modified H support in the paired negative-core-E stress

## 1. Two scalar conclusions

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad T=\frac{61}{250},\quad K=\frac{13}{12},
 \qquad p(t)=1+\frac12t^2+50t^4.
\tag{1}
\]
For \(0<p_0\le q_0\), use the ordinary increments
\[
\begin{split}
 N_{p_0,q_0}(v)&=\sqrt{p_0^2+q_0^2+2p_0q_0\sin v},\\
 U_{p_0,q_0}(v)&=p_0(\cos v+\sin v-1)
             -R\{N_{p_0,q_0}(v)-N_{p_0,q_0}(0)\},\\
 V_{p_0,q_0}(v)&=q_0(\cos v-1)
             -R\{N_{p_0,q_0}(-v)-N_{p_0,q_0}(0)\}.
\end{split}
\tag{2}
\]
All decimals below are exact rationals.

The first conclusion is the modified-H comparison
\[
 \boxed{\quad V_{k,p(t)}(d)\ge V_{k,1}(d)\quad}
\tag{3}
\]
whenever
\[
 0\le t\le T,\quad 0\le d,\quad d+t\le\theta\le h,
 \qquad .6+.27\theta\le k\le.8.
\tag{4}
\]
It retains the actual coefficient \(p(t)\) until the pointwise
comparison is proved.

The second conclusion concerns the high range
\[
 \frac15\le\theta\le h,\quad 0\le z\le\theta,\qquad
 .663<k<.8,\quad .847<l<1,\quad .847<c<1.013,
\tag{5}
\]
with
\[
 m=c(\cos z+.293\sin z).
\]
For fixed \(t\in[0,T]\), the three actual ordinary pairs are
\[
 (k,l),\qquad (k,p(t)),\qquad
 (\min(l,m),\max(l,m)).
\tag{6}
\]
Suppose their remaining variation domain is
\[
 P\le h-\theta,\qquad N\le h-s-t,\qquad
 N-P=\theta-s-t,\qquad s\ge0,\quad s+t\le h.
\tag{7}
\]
The usual two simplex concentrations leave pure, same-block and
separated terms. Every same-block or separated term is at least
its pure counterpart. Thus only
\[
 V_i(\theta-s-t)\quad(s+t\le\theta),\qquad
 U_i(s+t-\theta)\quad(s+t\ge\theta)
\tag{8}
\]
remain. If (4)'s coefficient condition also holds, the H term
in the first part of (8) may be replaced by \(V_{k,1}\).

These are algebraic support comparisons. They do not assert an
alignment or a new original owner. In the paired-E application
the E baseline correction from
[the adaptive EH gain lemma](HAND_G3_CORE_E_ADAPTIVE_EH_QUADRATIC_GAIN.md)
is unchanged.

## 2. A universal larger-coefficient comparison

For \(r=k/q\in[1/2,1]\), differentiation gives
\[
 \partial_qV_{k,q}(d)
 =\cos d-1-R\left\{
 \frac{1-r\sin d}{\sqrt{1+r^2-2r\sin d}}
                   -\frac1{\sqrt{1+r^2}}\right\}.
\tag{9}
\]
As a function of r, the right side is increasing. Its derivative is
\[
 Rr\left\{\frac{\cos^2d}{(1+r^2-2r\sin d)^{3/2}}
                     -\frac1{(1+r^2)^{3/2}}\right\}>0
 \qquad(d>0).
\tag{10}
\]
Indeed \(\sin d<.645<2r/(1+r^2)\), since the latter is at least
\(4/5\). This also proves the required positive comparison of
the two denominators in (10).

We will prove
\[
 \partial_qV_{k,q}(d)\ge0
       \quad\hbox{if}\quad \frac kq\ge\frac12+.33d,
       \qquad 0\le d\le h.
\tag{11}
\]
By (10), it suffices to put \(\rho=1/2+.33d\) in (9).
Here is one exact polynomial certificate, with its squaring
directions explicit.

Let \(S_j,C_j\) denote the alternating Taylor polynomials of
sine and cosine through the indicated degree, and set
\[
\begin{gathered}
 A=1+\rho^2,\quad
 B_-=A-2\rho S_5(d),\quad B_+=A-2\rho S_3(d),\\
 v_-=1-C_4(d),\qquad v_+=1-C_6(d),\\
 J=Q\rho^2S_3(d)\{2\rho-A S_5(d)\}+AB_-v_-^2,\\
 \Pi(d)=\frac{J^2-4QAB_+^2v_+^2}{d^2}.
\end{gathered}
\tag{12}
\]
The numerator of \(\Pi\) has a double zero at zero; \(\Pi\)
is a polynomial of degree 30.

All factors in J are nonnegative, and its first term is positive
for \(d>0\). For example
\[
 2\rho-A S_5(d)\ge 1-\frac54(.645)>0.
\]
Here \(2\rho-(1+\rho^2)S_5(d)\) increases with \(\rho\)
on the stated interval, so its lower endpoint is \(\rho=1/2\).
Write \(y=\sin d\), \(v=1-\cos d\), \(B=A-2\rho y\). The exact
quantity
\[
 L=Q\rho^2y(2\rho-Ay)+ABv^2
\]
is at least J. Also \(v\le v_+\) and \(B\le B_+\).
Consequently \(\Pi>0\) implies
\[
                         L>2RvB\sqrt A.
\tag{13}
\]
Expanding (13), and then reversing one positive square, gives
\[
 \left(\frac R{\sqrt A}-v\right)^2
        >\frac{Q(1-\rho y)^2}{B}.
\]
Both sides before squaring are nonnegative: in particular
\(R/\sqrt A-v>1\) on this interval. Reversing the square again
gives precisely (9) \(>0\).

For completeness, define the exact endpoint quotient
\[
             \Xi(d)=\frac{\Pi(d)-\Pi(h)}{d-h}.
\tag{14}
\]
Polynomial division makes it a degree-29 polynomial. The two
whole-interval rational comparisons are
\[
 \Pi(h)>.00477608,\qquad
                  \Xi(d)<-.91856\quad(0\le d\le h).
\tag{15}
\]
The second implies \(\Pi(d)\ge\Pi(h)>0\). Thus (11) holds,
strictly for \(d>0\); at zero both sides of (9) vanish.

Here and below the coefficient bounds have the following explicit
meaning. For any polynomial f on \([a,b]\), expand
\[
 f\left(\frac{a+b}2+\frac{b-a}2x\right)
      =\sum_j a_jx^j=\sum_n b_nT_n(x),\qquad |x|\le1,
\]
where
\[
 b_n=\sum_{\substack{j\ge n\\j\equiv n\pmod2}}
 a_j2^{-j}{j\choose(j-n)/2}
       \begin{cases}1,&n=0,\\2,&n>0.\end{cases}
\tag{16}
\]
Then use \(b_0-\sum_{n>0}|b_n|\) and
\(b_0+\sum_{n>0}|b_n|\) as the lower and upper bounds.
For \(\Xi\), the upper sum is below \(-.91856764\).
All coefficients come from (12)--(14); no interval partition
or sampled angle enters (15).

## 3. The paired-E coefficient relation

Under (4), for every \(1\le q\le p(t)\),
\[
 k-q(.5+.33d)
 \ge .6+.27(d+t)-p(t)(.5+.33d).
\]
The right side decreases with d, so use \(d\le h-t\).
Its resulting lower bound is
\[
 D(t)=.058+.33t-(.5t^2+50t^4)(.731-.33t).
\tag{17}
\]
It is concave on \([0,T]\). Indeed
\[
 D''(t)=-.731+.99t-438.6t^2+330t^3<0.
\]
The endpoint comparisons are
\[
 D(0)=.058,\qquad
 D(T)=.003874045392896>.003874.
\tag{18}
\]
Thus \(k/q>.5+.33d\) throughout the coefficient interval.
Integrating (11) from \(q=1\) to \(q=p(t)\) proves (3).

## 4. Derivative bounds for all three high pairs

The ranges (5) imply
\[
 .95<\cos z+.293\sin z<1.043,\qquad
 .8<m<1.057,\qquad p(t)<1.208.
\tag{19}
\]
The lower trigonometric bound follows by concavity and its two
endpoints; the upper follows by the Euclidean norm.
Every pair in (6) has ratio at least \(1/2\), so the previously
proved concavity of U and V applies.

We need the following two uniform bounds:
\[
 \begin{split}
 V_i'(v)&>.66 &&(0\le v\le h-t),\\
 U_i'(v)&>-.65 &&(0\le v\le1/2).
 \end{split}
\tag{20}
\]

For the actual modified H pair, \(V'\) increases with k and
decreases with v. Put \(\kappa=.663\), \(n=h-t\), and define
\[
\begin{split}
 Z(t)={}&Q\kappa^2p(t)^2 C_6(n)^2\\
 &-\{p(t)S_5(n)+.66\}^2
       \{\kappa^2+p(t)^2-2\kappa p(t)S_7(n)\}.
\end{split}
\tag{21}
\]
It has degree 29. Direct coefficient bounds (16) give
\[
 Z(0)>.01118,\qquad
 \frac{Z(t)-Z(0)}t>1.12384\quad(0\le t\le T).
\tag{22}
\]
The quotient has its continuous value at zero. Positive squaring
in (21) proves \(V'_{\kappa,p(t)}(h-t)>.66\), hence the first
part of (20) for H.

For G, decrease its smaller coefficient to .663. At \(v=h\),
\(V'_{.663,q}(h)\) is concave in \(q\in[.847,1]\), because its
second q derivative has the sign of
\[
             2(.663^2+q^2)\sin h-.663q(3+\sin^2h)<0.
\]
Its two endpoint values exceed .667. For B, decrease its smaller
coefficient to .8; the analogous q-concavity on \([.8,1.057]\)
and its two endpoint comparisons give \(V'_B(h)>.88\).
These inequalities prove the first part of (20) for G and B.

For the second part of (20), concavity reduces to \(v=1/2\).
At that point \(U'\) decreases in each coefficient for ordered
pairs with ratio at most one. The derivative in the smaller
coefficient is largest at ratio one and is already negative.
It suffices to use the two endpoint pairs
\[
             (.8,1.208),\qquad (1.057,1.057).
\]
Positive squaring with \(S_3,S_5,C_6,C_4\) gives, respectively,
\[
 U'_{.8,1.208}(1/2)>-.65,\qquad
 U'_{1.057,1.057}(1/2)>-.65.
\tag{23}
\]
The first also bounds G by increasing its larger coefficient.
This proves (20).

## 5. Same-block and separated concentration

Write
\[
\begin{split}
 \Psi_i(P,N)={}&p_i(\cos P+\sin P-1)+q_i(\cos N-1)\\
 &-R\{N_{p_i,q_i}(P-N)-N_{p_i,q_i}(0)\}.
\end{split}
\]
As established in the ordinary concentration theorem, these
functions are separately concave. Its algebraic concentration
argument applies to (7), including virtual zero arguments.

First let \(P\le N\). The exact same-block difference is
\[
 \frac{\Psi_i(P,N)-V_i(N-P)}{p_i}
 =(1-r_i\cos N)(\cos P-1)+(1-r_i\sin N)\sin P,
 \quad r_i=q_i/p_i.
\tag{24}
\]
It is nonnegative whenever \(r_i\sin N\le1\).
This condition holds for G and B by (5), (19), and \(\sin h<.645\).
For H, \(N\le h-t\), and
\[
 p(t)\sin(h-t)\le\sin h.
\tag{25}
\]
Indeed \(\sin(h-t)\le\sin h-t\cos h\),
\(p(t)-1<.849t\), and \(.849(.645)<.764<\cos h\).
Since \(k>.663>\sin h\), (25) proves the H condition.

If \(N\le P\), then \(P\le h-\theta\le1/2\). The exact difference
is
\[
 \frac{\Psi_i(P,N)-U_i(P-N)}{p_i}
 =(\cos P+\sin P-r_i)(1-\cos N)
                       +(\cos P-\sin P)\sin N.
\tag{26}
\]
All three ratios are below 1.83. Therefore (26) is at least
\[
 \sin N\{.398-.83\tan(N/2)\}
 \ge\sin N\{.398-.83(.256)\}>0
\]
when \(N>0\), and is zero when \(N=0\).

For a separated term with \(P\le N\), the universal ordinary
bound \(U_i(P)\ge-.545q_iP\), together with (20), gives
\[
 U_i(P)+V_j(N)
 \ge V_j(N-P)+\{.66-.545(1.208)\}P
 =V_j(N-P)+.00164P.
\tag{27}
\]
For \(N\le P\), the other part of (20) gives
\[
                  U_i(P)+V_j(N)\ge U_i(P-N)+.01N.
\tag{28}
\]
These scalar comparisons are valid also if the two indices
coincide. Thus replacing a negative block by a pointwise lower
comparison does not require an original duplicated block.

Equations (24)--(28) remove every saturated alternative and
prove (8). The H restoration (3) applies to the remaining
negative H argument \(d=\theta-s-t\), since \(d+t=\theta-s\le\theta\).

## 6. The positive-excess s endpoint

There is one useful direct continuation. Keep t and the A/TD
split fixed. The s-dependent full D baseline, in
\(x=\tan s\), is
\[
 F_c(x)=\sqrt{1+x^2}+Kx-R\sqrt{1+c^2+x^2}.
\]
For \(c>.847\) its derivative with respect to s satisfies
\[
                             F_{c,s}>.95.
\tag{29}
\]
Indeed
\[
 \frac R{\sqrt{1+c^2\cos^2s}}<1.67,
\]
and, putting \(y=\sin s\),
\[
 K-.95-.67y+.95y^2>0
\]
by completing the square. An actual diagonal D branch has the
stronger lower derivative \(>1.045\); its derivative matches at
the diagonal/full join.

Together with (20), every pure-U term in (8), added to either
D baseline, increases in s on \(s+t\ge\theta\). Its minimum
therefore occurs at
\[
                         s=\max(0,\theta-t).
\tag{30}
\]

## 7. A useful upper bound for the D derivative

For the full D support, write \(D(s)=F_{c,s}(s)\). Uniformly for
\(.847\le c\le1.013\),
\[
 D(s)\le K\quad(0\le s\le.4),\qquad
 D'(s)>0\quad(.4\le s\le h).
\tag{31}
\]
In particular, for every \(0\le w\le\theta\le h\),
\[
                    D(w)\le\max\{K,D(\theta)\}.
\tag{32}
\]

To prove the first part of (31), put \(y=\sin s\). Apart from
the equality at zero, it is equivalent to
\[
 Q\ge(1+Ky)^2(1+c^2-c^2y^2).
\]
The right side increases with c, and with y on \(0\le y\le.39\).
At \(c=1.013,y=.39\), the exact reserve is greater than .13146.
Since \(\sin(.4)<.39\), the assertion follows.

For the second part put \(A=1+c^2\). Direct differentiation gives
\[
 D_y=\frac1{(1-y^2)^2}
 \left\{1+y^2+2Ky-
 R\frac{A(1+y^2)-2c^2y^4}{(A-c^2y^2)^{3/2}}\right\}.
\tag{33}
\]
The radial fraction in braces decreases with A. Its derivative is
\[
 -\frac{(1-y^2)^2\{A(1+2y^2)-2y^2\}}
         {2\{A(1-y^2)+y^2\}^{5/2}}<0.
\]
Thus it suffices to use \(c=.847\). Positive squaring reduces
(33) to the degree-10 polynomial
\[
\begin{split}
 P(y)={}&(1+y^2+2Ky)^2(1+.847^2-.847^2y^2)^3\\
       &-Q\{(1+.847^2)(1+y^2)-2(.847^2)y^4\}^2.
\end{split}
\tag{34}
\]
Write \(P(.389+u)=\sum_{j=0}^{10}a_ju^j\). The exact coefficients
from (34) satisfy
\[
 a_0>1.75594,\qquad
 a_1-\sum_{\substack{j\ge2\\a_j<0}}|a_j|(.256)^{j-1}>8.02956.
\tag{35}
\]
Hence \(P>0\) on \(.389\le y\le.645\), which contains
\(\sin(.4)\le y\le\sin h\). This proves (31)--(32).

The same upper bound (32) also holds if the actual diagonal
D support is retained. Its derivative is
\[
                         \frac{K-d_0\sin s}{\cos^2s}.
\]
Such a branch has \(\sec s\le c\le1.013\), hence
\(\sin s<.161\). Since \(d_0>.39>K(.161)\), its derivative
is at most K. Above .4 the support is full, and at every
\(\theta\ge1/5\) its endpoint is also full. The derivatives
agree at their support transition.

The negative-excess interval still requires its separate
s-derivative or endpoint argument. The present note supplies
(32) for that argument but does not claim to complete the
remaining paired-E concentration.
