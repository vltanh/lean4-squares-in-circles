# Whole-rectangle rational certificates for the sole-E positive-T theorem

## 1. What is proved

This is the scalar and coefficient companion of
[the complete sole-E positive-T theorem](HAND_G5_POSITIVE_GA1_SOLE_E_PRIMARY_POSITIVE_T_EXCLUSION.md).
It uses exactly its five coefficient families, its two T owners,
its two primary faces, and its four actual negative indices.
All terminating decimals below are exact rational numbers.

The principal assertion is the single uniform inequality
\[
                 F_i(t,z)>1/10000,\qquad 0\le z\le t,
\tag{1}
\]
for each family interval and every indicated index. The proof
constructs a polynomial of total degree at most 14 on one whole
rectangle and bounds its analytic remainder. A tensor polynomial
identity proves positivity on that entire rectangle. Its
coefficient indices are algebraic indices, not sampled angles.
No coefficient-row inventory or angle subdivision is an input.

Put
\[
 Q_1=1957767069/500000000,\quad R_+=1.978770866,
 \quad A_+=1.914558470771,
 \quad h=.7.
\tag{2}
\]
Direct positive squaring gives
\[
 R_+^2>Q_1>(1.978770865)^2,
 \qquad A_+^2>Q_1-1/4.
\tag{3}
\]

## 2. Explicit rational enclosure arithmetic

Use variables X,Y in [−1,1]. For a polynomial
\(p=\sum p_{ij}X^iY^j\), write
\[
 \|p\|_1=\sum|p_{ij}|,\qquad
 \tau p=\sum_{i+j\le14}p_{ij}X^iY^j.
\tag{4}
\]
A pair \([p,e]\), with nonnegative rational e, represents a
function f satisfying \(|f-p|\le e\) on the full square.
Constants and X,Y start with zero error. Use these exact rules:
\[
\begin{split}
 [p,e]+[q,f]&=[p+q,e+f],\\
 -[p,e]&=[-p,e],\\
 [p,e][q,f]&=
 [\tau(pq),\;\|(1-\tau)(pq)\|_1+e\|q\|_1+f\|p\|_1+ef].
\end{split}
\tag{5}
\]
Multiplication by a rational constant uses the same rule.
These are immediate consequences of the triangle inequality;
they retain every discarded coefficient in a rigorous error.
Integer powers use binary exponentiation with (5). All displayed
products below are evaluated from left to right, with the stated
parentheses. Sums may be evaluated in any order.

For an argument u whose actual values lie in [0,h], define its
sine and cosine enclosures by evaluating
\[
 S(u)=\sum_{j=0}^{6}\frac{(-1)^ju^{2j+1}}{(2j+1)!},
 \qquad
 C(u)=\sum_{j=0}^{7}\frac{(-1)^ju^{2j}}{(2j)!}
\tag{6}
\]
with (5), then adding respectively
\[
                    h^{15}/15!,\qquad h^{16}/16!
\tag{7}
\]
to the error. For u=e/2 use h/2 in (7). Thus the notation S,C
in the construction below means a rational enclosure, not a
replacement of a trigonometric function without its remainder.

For a positive squared-norm enclosure v=[p,e], let
\[
 \rho=10^{-8}\left\lfloor10^8\sqrt{p_{00}}+\frac12\right\rfloor,
 \qquad
 H_7(w)=\sum_{j=0}^7\binom{1/2}{j}w^j.
\tag{8}
\]
Every p00 used here is positive and rho is nonzero. The integer
in (8) is defined by two positive rational squares; it involves
no approximate root premise. Evaluate
\[
                  \mathcal S(v)=\rho H_7((v-\rho^2)/\rho^2)
\tag{9}
\]
by Horner's rule and (5). For every real v≥0,
\[
                            \sqrt v\le\rho H_7((v-\rho^2)/\rho^2).
\tag{10}
\]
Indeed the eighth derivative of the square root is negative;
the degree-seven Taylor remainder is nonpositive on either
side of rho². Continuity includes v=0. This global upper bound
does not require a bound on \(|v/\rho^2-1|\).

## 3. One polynomial construction for all scalar indices

For the family interval [a,b] define
\[
 t=(a+b)/2+(b-a)X/2,\qquad z=t(1+Y)/2.
\tag{11}
\]
Choose either
\[
 (x,e)=(t-z,0)\quad\hbox{or}\quad(0,t-z).
\tag{12}
\]
Use the rational base families (6) of the main note, then
\[
 k=K+.06z,\quad l=L-.23z,\quad c=C-.53z,
 \quad \eta=.25+.33t,
\]
\[
 n=k(C(x)+gS(x)),\qquad m=c(C(z)+\eta S(z)).
\tag{13}
\]
For EH0 and EH1, set \(p=C(e)+\epsilon S(e)\) with their
specified epsilon; for EH2 set p=1. All expressions are
enclosures under (5)--(7).

For clarity, here are the four pairs used in the construction,
reproduced without any implicit sign or ordering convention:
\[
\begin{array}{c|cccc}
&H&A&B&D\\ \hline
\mathrm{EH,TD}&(1,n)&(k,l)&(l,m)&(p,c)\\
\mathrm{EH,BT}&(1,n)&(k,l)&(l,c)&(p,m)\\
\mathrm{DE,TD}&(1.25,n)&(k,l)&(l,m)&(1,c)\\
\mathrm{DE,BT}&(1.25,n)&(k,l)&(l,c)&(1,m).
\end{array}
\tag{14}
\]
Write these as \((a_j,b_j)\). The scalar negative coefficients
are
\[
\begin{array}{c|cccc}
&H&A&B&D\\ \hline
\mathrm{EH,TD}&n&l&m&1.131\\
\mathrm{EH,BT}&n&l&l&1.131\\
\mathrm{DE,TD}&1.25&l&m&1.131\\
\mathrm{DE,BT}&1.25&l&l&1.131.
\end{array}
\tag{15}
\]
The last column is a uniform enlargement of the actual negative
coefficient, justified in the main note.

The following short recipe specifies each final enclosure
\([P_i,E_i]\) completely. First form
\[
\begin{split}
 B_0={}&k\{1+2C(x)+(1+2g)S(x)\}
       +c\{1+2C(z)+(1+2\eta)S(z)\}+2l\\
 &-R_+\{kS(x)\mathcal S(1+g^2)
                       +cS(z)\mathcal S(1+\eta^2)\}.
\end{split}
\tag{16}
\]
Add the following E term:
\[
\begin{cases}
 1+2C(e)+(1+2\epsilon)S(e)-R_+S(e)\mathcal S(1+\epsilon^2),
                         &\mathrm{EH}_0,\mathrm{EH}_1,\\
 3+S(e)-2R_+S(e/2),&\mathrm{EH}_2,\\
 1+C(e)/2+(1-A_+)S(e)+3(1.25)/2,&\mathrm{DE}_0,\mathrm{DE}_1.
\end{cases}
\tag{17}
\]
For index i, add \(\widehat\nu_i(C(t)-1)\), and subtract
\[
 R_+\mathcal S(a_j^2+b_j^2)
       \quad(j\ne i),\qquad
 R_+\mathcal S(a_i^2+b_i^2-2a_ib_iS(t))
\tag{18}
\]
in the order H,A,B,D. This is the promised pair \([P_i,E_i]\).

The actual positive primary sine weights in (16)--(17) are
nonnegative. Equations (3), (10) and the enclosure rules imply
\[
                             F_i\ge P_i-E_i
\tag{19}
\]
on the entire square. The chosen negative-index norm is positive
because the pair coefficients are positive and \(\sin t<1\).
The construction never divides by a variable polynomial.

## 4. A compact tensor polynomial identity

For any polynomial \(P(X,Y)=\sum a_{ij}X^iY^j\) of total degree
at most 14, define
\[
 d_{kl}=2^{k+l}
 \sum_{i\ge k,\,j\ge l}
       (-1)^{i+j-k-l}\binom{i}{k}\binom{j}{l}a_{ij},
\]
\[
 \beta_{AB}(P)=
 \sum_{k=0}^{A}\sum_{l=0}^{B}
 d_{kl}\frac{\binom{A}{k}}{\binom{16}{k}}
        \frac{\binom{B}{l}}{\binom{16}{l}},
 \qquad 0\le A,B\le16.
\tag{20}
\]
Terms with a nonexistent coefficient are zero. Put
\(U=(X+1)/2,V=(Y+1)/2\). The exact identity is
\[
 P(X,Y)=\sum_{A,B=0}^{16}\beta_{AB}(P)
 \binom{16}{A}U^A(1-U)^{16-A}
 \binom{16}{B}V^B(1-V)^{16-B}.
\tag{21}
\]
Its basis functions are nonnegative and sum to one. Consequently
\(P\ge\min\beta_{AB}(P)\) on the complete square.

Substitution of the explicit rational recipes (4)--(18) into
(20) gives the following **uniform rational bounds**:
\[
                  0\le E_i<\frac7{500000},
 \qquad
                  \beta_{AB}(P_i)>\frac1{6250}
                  \quad(0\le A,B\le16).
\tag{22}
\]
The quantifiers in (22) range over all five families, both faces,
both T owners, and all four negative indices. There is no
additional family selected by an angle or by a coefficient.
Every operation in (22) is a rational addition, multiplication,
absolute value, binomial coefficient, or the uniquely specified
integer in (8). Thus (20), (22) constitute compact algebraic
certificates, with no external coefficient data.

For exact integer verification, take a common denominator D
of the dkl, and take
\(B_*=\mathop{\rm lcm}_{0\le j\le14}\binom{16}{j}\).
Multiplying (20) by \(DB_*^2\) makes every summand an integer:
\[
 Dd_{kl}
 \left(B_*\frac{\binom{A}{k}}{\binom{16}{k}}\right)
 \left(B_*\frac{\binom{B}{l}}{\binom{16}{l}}\right).
\tag{23}
\]
This verifies (22) by exact signed-integer comparisons, without
floating-point comparisons or an approximation of a polynomial
minimum. It is the arithmetic reproduction rule for the
uniform assertion, not an angle-grid evaluation.

Finally, (19)--(22) give
\[
 F_i>\frac1{6250}-\frac7{500000}
             =\frac{73}{500000}>\frac1{10000},
\tag{24}
\]
which proves (1).

## 5. Coefficient ranges used by the angular envelope

The same formulas also verify the ratio ranges in (22) of the
main note. Before applying a square-root enclosure, form each
actual pair \((a,b)\) from (13)--(14). Use
\[
 r(t)=
 \begin{cases}
 .585+.3t,&\mathrm{EH}_0,\\
 .65,&\mathrm{EH}_1,\\
 .72,&\mathrm{EH}_2,\mathrm{DE}_1,\\
 .72,&\mathrm{DE}_0\text{ at H or D},\\
 .533,&\mathrm{DE}_0\text{ at A},\\
 .625+.27t,&\mathrm{DE}_0\text{ at B}.
 \end{cases}
\tag{25}
\]
Evaluate both \(a-rb\) and \(b-ra\) by (5)--(7). For their
resulting polynomial/error pairs [p,e], direct substitution in
(20) gives the one uniform strict comparison
\[
                  \beta_{AB}(p)-e>1/100000
                  \quad(0\le A,B\le16).
\tag{26}
\]
This proves all ratio assertions, including the single-angle A
index that cannot be assigned the already fixed GA error.

The other ranges are elementary consequences of the coefficient
families. In the first two EH families, c is at least .86265
and .92325, respectively; m≥c, p≥1, k≥.86265 and .983,
and the H pair contains 1. Their largest coefficients are below
1.05 and 1.11. In the high EH family, l≥.7455, c≥.759,
k≥1.003, n>.95, p=1, and m≥c; all coefficients are below 1.131.
The bounds for n follow from
\(\cos h>.7648,\sin h>.6442\) and
\(n\le k\sqrt{1+g^2}\).

In DE0, l≥.565, k≥1.025, n≥k, c≥.903 and m≥c.
The ratio l/k is at most .81, since increasing z decreases it,
and its z=0 ratio is largest at t=.35. All coefficients are at
most 1.25. In DE1, l≥.749, c≥.759, k≥.986,
\(n>.95\), and m≥c; the same upper bound 1.25 applies.
For every family eta−tan(t/2)>0 by concavity and its two positive
endpoint values. Thus m≥c. The high-family upper bound m<1.131
is the completed square (24) in the main note; in the lower
families m decreases as z increases at fixed t, so m≤C.

For mixed B one also needs m≥l. In the low and middle families
c≥l. In DE1, c−l≥.01. In EH2,
\[
 \cos z+\eta\sin z\ge1+.091z,
\]
by \(\cos z\ge1-z^2/2\), \(\sin z\ge z-z^3/6\),
\(\eta=.25+.33t\) and z≤t≤.7. Therefore
\[
 m-l\ge.43-.36t-.30z+.091z(1.13-.53z)> .016.
\tag{27}
\]
The last expression decreases separately in t and z, so its
minimum is at t=z=.7. These observations justify all available
negative coefficients and mixed-block assignments in the main
note.

## 6. Fixed-angle and one-variable envelope checks

The fixed-angle bounds are obtained from
\[
 S_{15}(u)\le\sin u\le S_{13}(u),\qquad
 C_{14}(u)\le\cos u\le C_{16}(u),\qquad0\le u\le h.
\tag{28}
\]
For a positive rational v, bracket its square root between
\(10^{-12}\lfloor10^{12}\sqrt v\rfloor\) and that rational
plus \(10^{-12}\). The two square inequalities prove the
bracket. Applying (28) and these positive-square brackets proves
\[
 .862\frac{V_{.585}(h)-V_{.585}(.2)}{h-.2}>.605741768,
\]
\[
 .923\frac{V_{.65}(h)-V_{.65}(.35)}{h-.35}>.705683577.
\tag{29}
\]
This supplies both fixed secants used in the main note.

For a univariate rational polynomial p(s)=sum an s^n on [0,D],
define
\[
 b_0=\sum_na_n\frac{D^n}{4^n}\binom{2n}{n},\qquad
 b_j=2\sum_{n\ge j}a_n\frac{D^n}{4^n}\binom{2n}{n-j},
\]
\[
                           \mathcal L_D(p)=b_0-\sum_{j\ge1}|b_j|.
\tag{30}
\]
The exact Chebyshev identity gives p≥L_D(p). Applying it to
\[
 p(s)=Q_1(.72+s)^2(.7648)^2
  -(.72+s+.6443)^2\{1+(.72+s)^2-2(.72+s)(.6442)\}
\]
with D=.28 gives
\[
                              \mathcal L_{.28}(p)>.08298.
\tag{31}
\]
This proves the derivative comparison (28) of the main note.
The single-angle A bound there is the rational inequality
\[
 .565\{- .6443+1.978770865(.7648)/.785\}>.72.
\tag{32}
\]

It remains to prove the DE0 B chord (30) of the main note.
For t in [0,.35], set
\[
 a=.903(.625+.27t),\quad b=.903,\quad
 s_h=S_{15}(h),\quad c_h=C_{14}(h),
\]
\[
 v_h=a^2+b^2-2ab s_h,\quad
 v_\Delta=2ab\{s_h-S_{13}(t)\},
\]
\[
 A=.7(h-t)+b\{C_{16}(t)-c_h\},\qquad
 B=Q_1v_\Delta-A^2,\qquad
 P=B^2-4Q_1A^2v_h.
\tag{33}
\]
These are explicit rational polynomials. Formula (30) gives
\[
 \mathcal L_{.35}(A)>.4025,\quad
 \mathcal L_{.35}(B)>1.2221,\quad
 \mathcal L_{.35}(P)>.2638.
\tag{34}
\]
The degrees are 16,32,64. Since A,B are positive, two positive
squarings of P>0 yield
\[
 R\{\sqrt{v_h+v_\Delta}-\sqrt{v_h}\}>A.
\]
The Taylor inequalities (28) make this a lower bound for the
actual norm difference and an upper bound for the required
right side. This is exactly the desired strict chord.

Finally, the same-block endpoint and derivative comparisons in
Section 4.1 of the main note use only (28). For EH0 their three
positive checks are
\[
\begin{split}
 .585\{\phi(h)-1\}+\cos h-1&>0,\\
 .3\{\phi(h)-1\}-.585\phi'(h)&>0,\\
 .3\{\phi(.5)-1\}-.645\phi'(.5)+\sin(.2)&>0.
\end{split}
\tag{35}
\]
For EH1 the convexity, final derivative and final value follow
from
\[
 \cos(.35)-.65\phi(.5)>0,\quad
 -.65\phi'(.35)+\sin(.35)<0,\quad
 .65\{\phi(.35)-1\}+\cos h-\cos(.35)>0.
\tag{36}
\]
All quantities in (35)--(36) have strict rational signs after
(28). Together, (26)--(36) verify the full signed angular
envelope needed before the polynomial scalar proof. No Lean
compilation, CI result, numerical optimizer, or sampled minimum
is used in any of these inequalities.
