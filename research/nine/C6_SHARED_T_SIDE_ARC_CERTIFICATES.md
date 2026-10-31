# Exact full-domain height and center-angle certificates for the shared-T six-cycle

**Status: complete exact polynomial identities and coefficient-sign
certificate; root and separate independent full hand/algebra audits
passed.** This source proves four scalar implications
on one complete analytic rectangle. Their physical C6 application,
actual pocket routing and parent closure require the separate geometric
assembly. No sampled pose or angle subdivision is a premise.

## 1. The entire angle triangle is one rational rectangle

Put sigma=1/sqrt(2), k=sqrt(2)-1, and take
\[
       0\le x,y\le1,\qquad
       t=kx,\quad H=1+k^2x,\quad j=k(1-x)y,\quad w=j/H.
\tag{1}
\]
Set
\[
                 \alpha=\pi/4+2\arctan t,\qquad
                 \beta=\pi/4+2\arctan w.
\tag{2}
\]
This map covers the entire closed triangle
\[
          \alpha,\beta\ge\pi/4,\qquad\alpha+\beta\le3\pi/4.
\tag{3}
\]
Indeed 0<=t<=k and
\[
       0\le w\le\frac{k-t}{1+kt}
                   =\tan(\pi/8-\arctan t).
\]
Conversely, for any point of(3), use
\(t=\tan((\alpha-\pi/4)/2)\), x=t/k, and recover
\(y=wH/(k(1-x))\) when x<1. At x=1, (3) forces
alpha=pi/2,beta=pi/4,w=0; every y maps to that endpoint.
All denominator factors in(1) are positive. No open portion or
degenerate edge is omitted.

Write
\[
 \begin{gathered}
 a_0=\cos\alpha,\quad b_0=\sin\alpha,\quad
 u=\cos\beta,\quad v=\sin\beta,\\
 C=\cos(\alpha+\beta)=a_0u-b_0v,\qquad
 S=\sin(\alpha+\beta)=b_0u+a_0v.
 \end{gathered}
\tag{4}
\]
The exact rational formulas are
\[
 \cos\alpha=\sigma\frac{1-t^2-2t}{1+t^2},\quad
 \sin\alpha=\sigma\frac{1-t^2+2t}{1+t^2},
\tag{5}
\]
with the same formulas in w for beta. In particular
\[
 \begin{gathered}
 0\le u\le\sigma,\quad \sigma\le v\le1,\quad
 1\le u+v\le\sqrt2,\quad 0\le v-u\le1,\\
             -\sigma\le C\le0,\qquad S\ge\sigma>0.
 \end{gathered}
\tag{6}
\]

## 2. Circle equations and the exact torque normalization

Define the real scalar functions
\[
 \begin{gathered}
 \ell=(\sqrt2-a_0-u)/v,\\
 p=1+u+v+S,\qquad q=1+v-u-C,\\
 r_0=1+u-v-\ell,\qquad s_0=2+u+v,\\
 D=p s_0-q r_0.
 \end{gathered}
\tag{7}
\]
They are defined throughout the rectangle. We have ell>=0.
Also p>=2+sigma, s_0>=3, 1<=q<=2+sigma and r_0<=1.
Therefore
\[
                       D\ge3p-q\ge4+\sqrt2>0.
\tag{8}
\]
Define A,B by the exact two-circle equations
\[
 pA+qB=(p^2+q^2)/2,\qquad
 r_0 A+s_0 B=(r_0^2+s_0^2)/2,
\]
namely
\[
 \begin{split}
 A&=\frac{s_0(p^2+q^2)-q(r_0^2+s_0^2)}{2D},\\
 B&=\frac{p(r_0^2+s_0^2)-r_0(p^2+q^2)}{2D}.
 \end{split}
\tag{9}
\]
Use the following exact torque polynomial normalization:
\[
                  F=S[A-(1-\ell)B]+\ell C A.
\tag{10}
\]
The factor S is part of the definition. Do not replace(10) by F/S
when reusing the coefficient certificate.

For the actual shared-T star, its original applications in the T
frame are P=(A-1,B-1) and Q=(A-1+ell,B-1), and its two incoming
unit normals are(S,-C) and(0,1). Its true force equations give
mu=k_T A/S and nu=k_T(B+AC/S), with positive k_T.
Substituting into its unchanged origin torque gives
\[
             A-(1-\ell)B+\ell CA/S=0.
\]
Since S>0, this is exactly F=0. The circle equations and all
physical hypotheses of this star must be supplied by the geometric
assembly; no shared application is chosen anew in this scalar proof.

## 3. The four actual target functions

Set
\[
 \begin{gathered}
 h_B=C(A-1)+S(B-1),\qquad h_C=A-1+\ell,\\
 c_T=(A-1/2,B-1/2),\\
 c_B=(A-p+(u+v)/2,\ B-q+(v-u)/2),\\
 c_C=(A-r_0-(v-u)/2,\ B-s_0+(u+v)/2).
 \end{gathered}
\tag{11}
\]
In the displayed oriented T-coordinate plane, define
\[
 \begin{split}
 L_1&=h_B-21/50+F/4,\\
 L_2&=h_C-21/50,\\
 L_3&=4c_T\cdot c_B+3\det(c_T,c_B),\\
 L_4&=4c_C\cdot c_T+3\det(c_C,c_T).
 \end{split}
\tag{12}
\]
**Scalar theorem.** All four L_i are strictly positive throughout
the entire closed rectangle(1). Thus any actual star with F=0 has
both side heights>21/50. The two center-angle consequences require
the actual positive orientation and angular range established in
the geometric assembly, not an unproved branch of inverse tangent.

## 4. Positive clearing factors and full polynomial identities

Put
\[
 D_a=1+t^2,\quad D_w=H^2+j^2,\quad
 V=\sigma(H^2-j^2+2Hj)=vD_w.
\tag{13}
\]
All three are strictly positive on the complete rectangle.
Let
\[
                             K=2D\,D_a^2D_wV.
\tag{14}
\]
The checker/data label `2D` denotes this numerator K of the fully
canceled rational expression 2D; it does not denote the rational
function 2D itself.

This rationally defined expression is a polynomial in x,y over
Q(sqrt(2)). The identities below, or expansion of(4)--(9), verify
the exact cancellation. Its positivity follows from(8),(13).

For explicit verification of that cancellation, let
\[
 \begin{gathered}
 L=\sigma(1-t^2-2t),\quad M=\sigma(1-t^2+2t),\\
 U=\sigma(H^2-j^2-2Hj),\\
 C_n=LU-MV,\quad S_n=MU+LV,\\
 P_n=D_a(D_w+U+V)+S_n,\\
 Q_n=D_a(D_w+V-U)-C_n,\\
 J_n=\sqrt2 D_aD_w-LD_w-UD_a,\\
 R_n=D_aV(D_w+U-V)-J_nD_w,\qquad
 T_n=2D_w+U+V.
 \end{gathered}
\tag{15}
\]
Then the polynomial K in the attached complete coefficient data
satisfies the exact identity
\[
                  D_wK=2(D_aVP_nT_n-Q_nR_n).
\tag{16}
\]
The identity \(U^2+V^2=D_w^2\) explains the removable D_w factor;
all divisions in the checker are exact polynomial divisions.

Define four polynomial numerators by the following exact identities:
\[
 \begin{array}{c|c|c}
 i & P_i=L_i Z_i & Z_i\\ \hline
 1 & L_1 Z_1 & D_a^2V^2KD_w\\
 2 & L_2 Z_2 & D_aVK\\
 3 & L_3 Z_3 & D_aV^2K^2D_w\\
 4 & L_4 Z_4 & D_a^2V^2K^2D_w
 \end{array}
\tag{17}
\]
Every Z_i is strictly positive. Every full expanded power coefficient
of P_i and each clearing factor is supplied in
C6_SIDE_ARC_CERTIFICATES.json. The exact standalone derivation is
C6_SIDE_ARC_CERTIFICATES.js. Neither file relies on an external
algebra library, floating arithmetic, pose samples or a parameter cover.

The script constructs precisely(1),(4)--(17) with field elements
(a+b*sqrt(2))/d, using integer a,b,d and d>0. It performs polynomial
addition, multiplication and exact division over that field.
A failed exact division is never silently accepted. The resulting
actual bidegrees are those in the next section; they are the degrees
of these explicit clearing factors, not a claim about a minimal
rational normal form.

## 5. Every coefficient sign on the entire rectangle

For a polynomial
\(P(x,y)=\sum a_{ij}x^iy^j\) of bidegree(m,n), its exact Bernstein
coefficients on[0,1]^2 are
\[
 b_{kl}=\sum_{\substack{i\le k\\j\le l}}
 a_{ij}\frac{\binom{k}{i}\binom{l}{j}}
                 {\binom{m}{i}\binom{n}{j}}.
\tag{18}
\]
The identity
\[
 P(x,y)=\sum_{k=0}^m\sum_{l=0}^n
 b_{kl}\binom{m}{k}x^k(1-x)^{m-k}
          \binom{n}{l}y^l(1-y)^{n-l}
\tag{19}
\]
then holds exactly. The nonnegative basis weights sum to one throughout
the closed rectangle. A strict lower bound for every coefficient is
therefore a strict lower bound for the full polynomial.

All1,080 exact coefficients, with every index and field numerator,
are included in C6_SIDE_ARC_CERTIFICATES.json. Their exact minima and
strict rational floors are:

| Polynomial | Bidegree | Coefficients | Exact minimum | Strict rational floor |
| --- | --- | ---: | --- | --- |
| P1 | (18,10) | 209 | (10sqrt(2)-9)/50 | 1/10 |
| P2 | (12,6) | 91 | (20-9sqrt(2))/50 | 1/7 |
| P3 | (24,14) | 375 | (762852688-539178072sqrt(2))/6279 | 50 |
| P4 | (26,14) | 405 | (187+132sqrt(2))/2 | 186 |

The checker computes every coefficient by(18), compares each directly
to its stated rational floor, and also compares all coefficients
algebraically to compute the exact minimum. No decimal comparison is
used. The four minimum/floor comparisons reduce respectively to
\[
 \begin{gathered}
 200-196=4>0,\qquad8100-2\cdot3969=162>0,\\
 762538738^2-2\cdot539178072^2
                  =39340299358276>0,\\
 2\cdot132^2-185^2=623>0.
 \end{gathered}
\tag{20}
\]
All quantities squared have the indicated positive comparison signs.
Equations(18)--(20) and the complete coefficient lists prove P_i>0.
The positive factors(17) then prove all four L_i>0 as claimed.

## 6. Audit and application limits

The root independently reconstructed the rational map, the two
circle equations, the true T torque, all center/height formulas,
the four positive clearing factors and every Bernstein coefficient.
The exact standalone JavaScript was evaluated in memory with all
1,080 floor comparisons passing. Its complete output is preserved
alongside the source. No executor, Lean compilation or CI was used.

The separate independent audit used different BigInt field and
polynomial arithmetic. It reconstructed every rational function,
verified both unit-trigonometric identities, the positive K identity
and both circle equalities, and cross-multiplied all four target
identities. It reconstructed each power polynomial from the full
Bernstein basis expansion (the reverse conversion direction), checked
all1,080 strict coefficient floors and independently recovered every
minimum in the table. All exact checks passed.

SIX_CYCLE_ONE_DIAGONAL_SIDE_CAPACITIES.md supplies the complete
actual channel/center-angle identification and physical region routing.
Its separate root and independent full audits retain the original
shared-T mean, every core body, weak junction and all three extras.
Together with the connected annular-arc theorem, that complete
assembly closes the entire physical-unique one-diagonal family.
This scalar certificate alone makes no graph or coarse-cell claim.
