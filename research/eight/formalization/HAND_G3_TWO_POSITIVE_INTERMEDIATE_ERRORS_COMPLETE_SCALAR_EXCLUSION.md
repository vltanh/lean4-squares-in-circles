# Two positive intermediate errors: complete endpoint certificates

## 1. Original scope

Work on the fixed-original-witness G0--G2 boundary at

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]

The original sorted outer states H, G, B and D have signed
tangents respectively positive, negative, negative and negative.
A, T and E may have either sign and either radial kind. Consider
either of the following original-owner patterns:

* GA2, AB2, BT2, TD2, DE2, EH0, with \(a=d_{AB}\ge0\);
* GA3, AB0, BT2, TD2, DE2, EH0, with \(a=d_{GA}\ge0\).

In both patterns \(HG\in\{0,2\}\) and \(z=d_{TD}\ge0\).
There is no such cycle. This conclusion has no frame-order
hypothesis.

Put \(\theta=a+z\). Original total variation gives
\(0\le\theta<h\). Use
[the two-positive-error split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md),
including its notation

\[
 \begin{gathered}
 \eta=\frac{293}{1000},\qquad
 m(z)=c(\cos z+\eta\sin z),\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\\
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,
 \qquad c_0=\sqrt{Q/2}-\tfrac12,\\
 j(a)=\frac{\cos a+\sin a-1}{2}
                         -S(\sin a,1-\cos a).
 \end{gathered}
\tag{2}
\]

Here \(S\) is the support of the original sorted shifted
circle. For weights fixed at each \(\theta\), a feasible cycle
would satisfy

\[
                B(z)+l j(a)+\mathcal E_{m(z)}(\theta)\le0.
\tag{3}
\]

The cited theorem makes the relevant scalar alternatives
concave throughout the entire split \(a+z=\theta\). We give
admissible weights and positive endpoint certificates for
\((a,z)=(0,\theta)\) and \((\theta,0)\). All decimals below
are exact rationals.

## 2. One low family and one high family

Write \(L=1/6\). For \(0\le\theta\le L\), put
\(u=\theta-83/500\) and retain the previously audited family

\[
 \begin{split}
 k&=.672-.2u+2.5u^2,\\
 l&=1.01-2.5u+6u^2+48u^3,\\
 c&=1.043-4.2u+8u^2.
 \end{split}
\tag{4}
\]

Its whole-interval ranges are proved in Section 2 of
[the complete TD2 scalar theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_COMPLETE_SCALAR_EXCLUSION.md).
In particular

\[
 \frac23<k<.775,
 \qquad 1<l\le c<2,
 \qquad l<2k,
 \qquad c(\cos\theta+\eta\sin\theta)<\frac32l.
\tag{5}
\]

The function \(\cos z+\eta\sin z\) increases on \([0,L]\).
Consequently (5) gives every low-angle admissibility and
split-concavity hypothesis for all \(0\le z\le\theta\),
not just at the endpoints.

For \(L\le\theta\le h\), put \(t=\theta-L\) and choose

\[
 \begin{split}
 k&=.6692+.5218t-.5956t^2+.4216t^3,\\
 l&=1+.0175t-1.0932t^2+1.278t^3,\\
 c&=1.0163-.0209t-1.1486t^2+1.4069t^3.
 \end{split}
\tag{6}
\]

These satisfy on the entire high interval

\[
 \begin{gathered}
 .6692\le k<.843,
 \qquad .89<l<1.0002,
 \qquad .89<c\le1.0163,\\
 k<\min(l,c),\qquad l<\frac32k,
 \qquad .9l<c<1.1l.
 \end{gathered}
\tag{7}
\]

Here is a direct verification of these ranges. The quadratic
\(k'\) is positive by completing the square. The quadratic
\(c'\) is convex and negative at both endpoints, so c decreases.
The quotient \((l(\theta)-l(h))/(h-\theta)\) is a concave
quadratic positive at both endpoints. Thus \(l\ge l(h)>.89\).
For \(d=h-L=8/15\),

\[
 l\le1+.0175t-(1.0932-1.278d)t^2
 \le1+\frac{.0175^2}{4(1.0932-1.278d)}<1.0002.
\tag{8}
\]

The endpoint values of k and c give the remaining individual
bounds. In particular \(1.0002<1.5(.6692)\).
For the last two comparisons in (7), their expressions in t are

\[
 \begin{split}
 c-.9l&=.1163-.03665t-.16472t^2+.2567t^3,\\
 1.1l-c&=.0837+.04015t-.05392t^2-.0011t^3.
 \end{split}
\tag{9}
\]

Discard their positive nonconstant terms and use \(t\le d\);
both resulting rational lower bounds are positive.

Concavity and the endpoint values give, for every split,

\[
       .95<\cos z+\eta\sin z<1.043,
             \qquad 0\le z\le\theta\le h.
\tag{10}
\]

The upper bound also follows by squaring
\(\sqrt{1+\eta^2}<1.043\). Thus each of the G, H and B
coefficient pairs in the split theorem has \(p_i/q_i\ge2/3\).
Moreover

\[
 q_{\min}>.89,
 \qquad q_{\max}<1.061<\frac65(.89).
\tag{11}
\]

Indeed \(q_H=1\), \(q_G=l\), and
\(q_B=\max(l,m)\), while
\(m<1.0163(1.043)<1.061\). Equations (7)--(11) verify
all concentration conditions, all balanced-pair conditions,
and \(.9\le c/l\le1.1\) on the whole split interval.

At \(\theta=L\) either family may be chosen; a stress for
one fixed total angle need not agree with the stress chosen
for another.

## 3. Exact polynomial conventions

Let \(S_j\) and \(C_j\) be the alternating sine and cosine
polynomials ending in degree j. For \(0\le\theta\le h\), set

\[
 S_-=S_{11}(\theta),\quad S_+=S_9(\theta),\qquad
 C_-=C_{10}(\theta),\quad C_+=C_{12}(\theta).
\tag{12}
\]

They bound sine and cosine in the indicated directions.
Use the strict radical upper bounds

\[
 \bar R=1.978787508,
 \quad \bar a=1.414575672,
 \quad \bar c=.899214066,
 \quad \bar\sigma=1.415477291.
\tag{13}
\]

Positive squaring verifies respectively

\[
 \bar R^2>Q,\quad
 (\bar a+\tfrac12)^2>Q-\tfrac14,\quad
 (\bar c+\tfrac12)^2>Q/2,\quad
 \left(\bar\sigma+\frac{1+\eta}{2}\right)^2>Q(1+\eta^2).
\tag{14}
\]

For polynomial upper bounds \(P_i\) of squared norms and
positive polynomials \(r_i\), define

\[
 \begin{split}
 \mathcal D(\mathbf r)&=2\prod_i r_i,\\
 \mathcal N(A;\mathbf P,\mathbf r)
   &=2A\prod_i r_i
      -\bar R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.
 \end{split}
\tag{15}
\]

The inequality
\(\sqrt{P_i}\le(P_i+r_i^2)/(2r_i)\) shows that
\(\mathcal N>0\) certifies
\(A-\bar R\sum_i\sqrt{P_i}>0\).
No root isolation or numerical norm value is needed.

We use two elementary, whole-interval polynomial estimates.
For an interval \(I=[v,w]\), let \(M=(v+w)/2\),
\(r=(w-v)/2\), and write

\[
 P(M+rx)=\sum_n a_nx^n=\sum_j b_jT_j(x),\qquad -1\le x\le1.
\tag{16}
\]

The Chebyshev polynomials are defined by
\(T_0=1,T_1=x,T_{j+1}=2xT_j-T_{j-1}\); hence
\(|T_j(x)|\le1\). The coefficients in (16) are explicit
finite rational sums:

\[
 \begin{split}
 b_0&=\sum_{n\equiv0\pmod2}2^{-n}\binom n{n/2}a_n,\\
 b_j&=\sum_{\substack{n\ge j\\n\equiv j\pmod2}}
       2^{1-n}\binom n{(n-j)/2}a_n\quad(j\ge1).
 \end{split}
\tag{17}
\]

The monomial coefficients themselves are
\(a_n=r^n\sum_{i\ge n}\binom in p_iM^{i-n}\) when
\(P(\theta)=\sum p_i\theta^i\). Thus every aggregate below
is specified by finite sums of displayed rational polynomials.

The basic lower bounds we use are

\[
 \begin{split}
 \mathfrak L_I(P)&=b_0-\sum_{j\ge1}|b_j|,\\
 \mathfrak Q_I(P)&=b_0-b_2-\frac{b_1^2}{8b_2}
                         -\sum_{j\ge3}|b_j|\quad(b_2>0),\\
 \mathfrak C_I(P)&=b_0-b_2
       -\frac{(b_1-3b_3)^2}{4(2b_2-4|b_3|)}
       -\sum_{j\ge4}|b_j|\quad(2b_2>4|b_3|).
 \end{split}
\tag{18}
\]

Each is a lower bound for P on I. The second completes the
square in \((b_0-b_2)+b_1x+2b_2x^2\). For the third, use
\(T_3=4x^3-3x\) and \(|x^3|\le x^2\), then complete
the resulting quadratic square.

We also use the ordinary centered coefficient bounds

\[
 \mathfrak m_I(P)=a_0-\sum_{j\ge1}|a_j|,
 \qquad
 \mathfrak M_I(P)=a_0+\sum_{j\ge1}|a_j|.
\tag{19}
\]

These are respectively lower and upper bounds for P on I.
All bounds (18)--(19) concern an entire stated interval.

## 4. The low endpoint with all rotation at A

For the low family, the endpoint \((a,z)=(0,\theta)\)
is exactly the already proved low endpoint of
[the complete TD2 scalar theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_COMPLETE_SCALAR_EXCLUSION.md).
We need only \((a,z)=(\theta,0)\), where \(m=c\).

Since \(\theta\le L<\alpha_0\), the exact A support of the
split theorem is its tangent-zero branch. Define

\[
 \begin{split}
 j_-&=\tfrac12(C_--1)+(\tfrac12-\bar a)S_+,\\
 A_0&=2k+3l+\tfrac52c+\tfrac52-(1+c)\bar c+l j_-,\\
 P_H&=1+k^2,\qquad P_G=k^2+l^2,\qquad P_B=c^2+l^2,\\
 P_{H,-}&=P_H-2kS_-.
 \end{split}
\tag{20}
\]

The sorted D support is exactly \((1+c)c_0\), because
\(c\ge1\). The three remaining full-circle supports give
the constant terms in \(A_0\).

Choose the positive auxiliary polynomials

\[
 \begin{split}
 r_H&=.89(1-\theta^2/2)+.456(k-\theta+\theta^3/6),\\
 r_G&=.55k+.835l,\qquad r_B=.729c+.6845l.
 \end{split}
\tag{21}
\]

The single-negative H numerator and its denominator are

\[
 \begin{split}
 N_H&=\mathcal N(A_0+C_--1;
                  (P_{H,-},P_G,P_B),(r_H,r_G,r_B)),\\
 D_H&=\mathcal D(r_H,r_G,r_B).
 \end{split}
\tag{22}
\]

For the one additional same-block case, put

\[
 \begin{split}
 C_h^-&=C_{10}(h),\quad C_h^+=C_{12}(h),\quad S_h^-=S_{11}(h),\\
 J_-&=k\{(C_h^-+S_h^-)C_-
                   -(C_h^+-S_h^-)S_+-1\}+l(C_h^--C_+),\\
 N_M&=N_H+D_HJ_-.
 \end{split}
\tag{23}
\]

Finally let

\[
 \begin{gathered}
 A_* = A_0-\frac{109}{200}c(h-\theta),\\
 P_{H,h}=P_H-2kS_h^-,\qquad
 P_{G,h}=P_G-2klS_h^-,\\
 N_{SH}=\mathcal N(A_*+C_h^--1;
             (P_{H,h},P_G,P_B),(.77,r_G,r_B)),\\
 N_{SG}=\mathcal N(A_*+l(C_h^--1);
             (P_H,P_{G,h},P_B),(.82+.572k,.765l,r_B)).
 \end{gathered}
\tag{24}
\]

These are precisely the four sufficient scalar inequalities
of Section 6 of
[the concentration envelopes](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md),
now with \(m=c\) and the extra A charge. In particular the
coefficient c in \(A_*\) is the largest positive-block weight.

Here are whole-interval certificates, with \(I_0=[0,L]\):

\[
 \begin{gathered}
 N_H(L)>.0127,\qquad
 \mathfrak L_{I_0}\left(\frac{N_H(\theta)-N_H(L)}{L-\theta}\right)>.84,\\
 \mathfrak Q_{I_0}(N_M)>.093,\qquad
 \mathfrak m_{I_0}(N_{SH})>.18,
 \qquad \mathfrak m_{I_0}(N_{SG})>.043.
 \end{gathered}
\tag{25}
\]

The quotient is a polynomial, including at \(\theta=L\).
The four numerators in (22)--(24) have degrees 22, 24, 19
and 21. Substitution in the explicit coefficient sums
(16)--(19) proves every comparison in (25); the coefficient
\(b_2\) required for \(\mathfrak Q_{I_0}(N_M)\) is positive.
Thus all four scalar alternatives are strictly positive.

The low split-concavity theorem now proves positivity for
every \(0\le a\le\theta\le L\).

## 5. A single polynomial A envelope on the high interval

The split theorem proves the following lower bound on
\(I_1=[L,h]\):

\[
 j(\theta)\ge
 \frac{\cos\theta-1}{2}
       +(\tfrac12-a_0)\sin\theta-.086(\theta-L)^4.
\tag{26}
\]

For completeness, its only additional loss bounds the
transition from the tangent-zero support to the interior
circle support. The transition angle \(\alpha_0\) is greater
than \(1/2\). Beyond that transition the difference of the
two expressions is

\[
 2R\sin(\theta/2)
       \{1-\cos((\theta-\alpha_0)/2)\}
 \le\frac R8\theta(\theta-\tfrac12)^2.
\tag{27}
\]

On \([1/2,h]\), the ratio
\(\theta(\theta-1/2)^2/(\theta-L)^4\) increases, since its
derivative has the sign of \(-\theta^2+\theta+1/12>0\).
Its value at h, together with \(R<1.979\), makes the last
expression in (27) smaller than \(.086(\theta-L)^4\).
Before the transition the extra subtraction in (26) is
harmless. This is one lower envelope on the whole high interval.

In the polynomials below use

\[
 j_-=\tfrac12(C_--1)+(\tfrac12-\bar a)S_+-.086t^4.
\tag{28}
\]

## 6. Six high endpoint numerators

The balanced split reduction leaves just the G, H and B
single-negative alternatives. We certify them at both
endpoints, using the full D-circle support as a lower
relaxation of the baseline.

Index the endpoint with all rotation at T by X=T and the
endpoint with all rotation at A by X=A. Define

\[
 \begin{array}{lll}
 m_-^T=c(C_-+\eta S_-),&
 m_+^T=c(C_++\eta S_+),&
 \mu^T=c(C_4+\eta S_5),\\
 m_-^A=c,&m_+^A=c,&\mu^A=c.
 \end{array}
\tag{29}
\]

Every trigonometric polynomial without an explicit argument
in this section is evaluated at \(\theta\). Set

\[
 \begin{split}
 A_T={}&2k+3l+\tfrac32m_-^T+\tfrac12c+3
        +\tfrac12c(1+C_-+S_-)-c\bar\sigma S_+,\\
 A_A={}&2k+3l+3c+3+l j_-.
 \end{split}
\tag{30}
\]

For either X use the squared-norm bounds

\[
 \begin{gathered}
 P_H=1+k^2,\quad P_G=k^2+l^2,\quad P_D=1+c^2,\quad
 P_B^X=(m_+^X)^2+l^2,\\
 P_{H,-}=P_H-2kS_-,\qquad
 P_{G,-}=P_G-2klS_-,\qquad
 P_{B,-}^X=P_B^X-2l m_-^X S_-.
 \end{gathered}
\tag{31}
\]

Choose

\[
 \begin{gathered}
 r_H=.8+.6k,\quad r_G=.62k+.7846l,\quad r_D=.72+.694c,\\
 r_B^X=.7071(l+\mu^X),\\
 r_{H,-}=.89C_4+.456(k-S_5),\\
 r_{G,-}=.89lC_4+.456(k-lS_5),\\
 r_{B,-}^X=.83lC_4+.56(\mu^X-lS_5).
 \end{gathered}
\tag{32}
\]

They are all positive on \(I_1\). For example
\(C_4>.7648\), \(S_5<.645\),
\(\mu^X>.95(.89)\), and (7) give each negative-norm
auxiliary in (32) greater than \(.6\). The other auxiliaries
are manifestly positive.

To handle the B coefficient without splitting at \(m=l\),
put

\[
                    q_*=l+\frac3{20}(h-\theta).
\tag{33}
\]

Then

\[
        q_*\ge\max(l,m^T),\qquad q_*\ge\max(l,m^A).
\tag{34}
\]

One direct whole-interval check of the first assertion uses
the degree-eight polynomial \(P=q_*-c(C_4+\eta S_5)\).
If \(P(\theta)=\sum_j e_j(\theta-M)^j\), where
\(M=(L+h)/2\), \(r=(h-L)/2\), then

\[
 E_2:=e_2-\sum_{j\ge3}|e_j|r^{j-2}>.2675,
 \qquad e_0-\frac{e_1^2}{4E_2}>.004.
\tag{35}
\]

This completes the square and proves \(P>0\).
For the second assertion, the derivative of \(q_*-c\) is
at most
\(-.1116+.1108^2/(4(.3867))<-.1\), while its value at h
is greater than \(.00038\). Also \(q_*\ge l\) directly.

The six promised numerators are now specified completely:

\[
 \begin{split}
 N_{XH}&=\mathcal N(A_X+C_--1;
       (P_G,P_B^X,P_{H,-},P_D),(r_G,r_B^X,r_{H,-},r_D)),\\
 N_{XG}&=\mathcal N(A_X+l(C_--1);
       (P_H,P_B^X,P_{G,-},P_D),(r_H,r_B^X,r_{G,-},r_D)),\\
 N_{XB}&=\mathcal N(A_X+q_*(C_--1);
       (P_H,P_G,P_{B,-}^X,P_D),(r_H,r_G,r_{B,-}^X,r_D)).
 \end{split}
\tag{36}
\]

Because \(\cos\theta-1\le0\), (34) is exactly the needed
direction for the B charge. Every other substitution in
(29)--(36) follows directly from (12)--(15). Thus positivity
of these polynomials proves positivity of all six original
endpoint scalar alternatives.

## 7. Whole-interval positivity of the six numerators

First consider H. For X=T,A define the polynomial

\[
              Q_{XH}(\theta)=
                  \frac{N_{XH}(\theta)-N_{XH}(L)}{\theta-L}.
\tag{37}
\]

The explicit coefficient formula (17) gives

\[
 \begin{gathered}
 N_{TH}(L)>.0017,
 \qquad \mathfrak L_{I_1}(Q_{TH})>.058,\\
 N_{AH}(L)>.00165,
 \qquad \mathfrak L_{I_1}(Q_{AH})>.0575.
 \end{gathered}
\tag{38}
\]

Consequently both H numerators are positive everywhere.

Define \(Q_{TG}\) and \(Q_{AG}\) by the same endpoint
quotient. These have the exact completed-square bounds

\[
 \begin{gathered}
 N_{TG}(L)>.00176,
 \qquad \mathfrak Q_{I_1}(Q_{TG})>.0069,\\
 N_{AG}(L)>.0017,
 \qquad \mathfrak C_{I_1}(Q_{AG})>.0116.
 \end{gathered}
\tag{39}
\]

For orientation, the three coefficients governing the last
completion satisfy

\[
 b_0-b_2>.01525,\qquad
 |b_1-3b_3|<.01183,\qquad
 2b_2-4|b_3|>.02114,
 \qquad \sum_{j\ge4}|b_j|<.00191.
\tag{40}
\]

These bounds alone already make the last expression in (39)
positive. The exact sum in (18) gives the stated stronger
reserve. The coefficient \(b_2\) in the first completion
and \(2b_2-4|b_3|\) in the second are positive, so both
applications of (18) are valid.

For B, let \(\ell_{XB}(\theta)\) be the affine interpolation
of \(N_{XB}(L)\) and \(N_{XB}(h)\), and define

\[
 Q_{XB}(\theta)=
  \frac{N_{XB}(\theta)-\ell_{XB}(\theta)}
                   {(\theta-L)(h-\theta)}.
\tag{41}
\]

Again this is a polynomial, including at both endpoints.
Both endpoint values of each \(N_{XB}\) exceed \(.03\).
For their chord quotients the centered coefficient bounds are

\[
 \begin{gathered}
 Q_{TB}(h)>1.24,
 \qquad \mathfrak M_{I_1}(Q'_{TB})<-.4,\\
 Q_{AB}(h)>.075,
 \qquad \mathfrak M_{I_1}(Q'_{AB})<-1.4.
 \end{gathered}
\tag{42}
\]

Hence both quotients decrease to a positive endpoint value.
Equation (41) proves positivity of both B numerators.

For clarity, the numerator degrees in the order
TH, TG, TB, AH, AG, AB are 41, 44, 39, 27, 30 and 30.
Every strict comparison (35), (38)--(42) is an exact rational
comparison obtained from the displayed polynomial formulas
and finite coefficient sums. These formulas supply the
complete certificate; there is no angular subdivision or
external list of interval values.

## 8. Closing the two owner patterns

For \(0\le\theta\le L\), the old TD endpoint and the four
new A endpoint bounds (25), together with low split concavity,
make the left side of (3) strictly positive.

For \(L\le\theta\le h\), (7)--(11) reduce the envelope to
the three single-negative curves. High split concavity and
the six strict endpoint bounds (38)--(42) again make the left
side of (3) positive throughout the entire split.

This contradicts the necessary inequality (3) and excludes
both original owner patterns in Section 1. The conclusion
does not require a sign assumption on A, T or E, a radial-kind
assumption on those states, or an ordering of their frames.

The theorem concerns nonnegative a and nonnegative original
TD2 error. Negative intermediate errors, arbitrary original
TD0 errors and the other primary-owner choices require their
own reductions; none is inferred here from an endpoint scalar.
