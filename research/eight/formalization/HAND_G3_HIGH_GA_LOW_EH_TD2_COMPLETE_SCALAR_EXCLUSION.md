# The complete TD2 extension of the secondary-owner four-circle exclusion

## 1. Original scope and conclusion

Retain the fixed-witness G0--G2 boundary cycle at

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]

The four original sorted outer states H, G, B and D have signed
tangents respectively positive, negative, negative and negative.
A, T and E may have either sign and either radial kind. The
original owner choices in this note are

\[
 GA=2,\quad AB=0,\quad BT=2,\quad TD=2,\quad
 DE=2,\quad EH=0,\qquad HG\in\{0,2\}.
\tag{2}
\]

**There is no such boundary cycle.** No frame-order hypothesis
is imposed, and none of the original inequalities is replaced by
an assumed aligned witness.

Use the exact whole-angle reduction in
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).
It already excludes nonpositive TD error. For a positive TD
error \(z\in(0,h)\), use its notation

\[
 \begin{gathered}
 \eta=\frac{293}{1000},\qquad
 m=c(\cos z+\eta\sin z),\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\\
 W(z)=\frac{1+\cos z+\sin z}{2},\qquad
 c_0=\sqrt{Q/2}-\frac12.
 \end{gathered}
\tag{3}
\]

Thus its necessary inequality is

\[
                         B(z)+\mathcal E(z)\le0.
\tag{4}
\]

This note gives positive weights satisfying every hypothesis of
that reduction and proves the reverse strict inequality on the
entire interval. The scalar simplifications used below are proved
in
[the concentration scalar envelopes](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).

## 2. Two explicit weight formulas

Put

\[
                 L=\frac16,\qquad b=\frac{37}{80},
                 \qquad K=\frac{653}{800}.
\tag{5}
\]

For \(0\le z\le L\), let \(t=z-83/500\), and choose

\[
 \begin{split}
 k&=.672-.2t+2.5t^2,\\
 l&=1.01-2.5t+6t^2+48t^3,\\
 c&=1.043-4.2t+8t^2.
 \end{split}
\tag{6}
\]

For \(L\le z\le h\), choose

\[
 l=1,\qquad k=\min\{K,.585+.5z\},\qquad
 c=\max\{k,1.14-.7z\}.
\tag{7}
\]

The last formula has just one intrinsic coefficient change:
on \([L,b]\) it is
\[
                    k=.585+.5z,\qquad c=1.14-.7z;
\tag{8}
\]
on \([b,h]\) it is \(k=c=K\). Both expressions in (8)
equal K at b. At \(z=L\), either (6) or (7) may be used.
A stress may be chosen separately for each fixed z; agreement
of these two choices at L is unnecessary.

All displayed decimals in this note are exact rationals.
The first family satisfies

\[
 \frac23<k<.775,\qquad
 1<l\le c<2,\qquad l<2k,\qquad
 l\le m<\frac32l.
\tag{9}
\]

Here k, l and c decrease on \([0,L]\). For l, its derivative
is a convex quadratic negative at both endpoints. For the
difference, \((c-l)''=51.808-288z\ge3.808>0\), while
\((c-l)'(L)<0\); thus \(c-l\) decreases and its right
endpoint is still positive. One particularly short check of
\(2k-l>0\) is

\[
 2k-l=.177410208-1.536064z+22.904z^2-48z^3
 \ge .177410208-1.536064z+14.904z^2>0.
\tag{10}
\]

The last quadratic is positive by completing the square.
Moreover \(\cos z+\eta\sin z\ge1\) here, since its derivative
is at least
\(\eta(1-L^2/2)-L>0\). For the upper bound on m it suffices
to use \(\cos z+\eta\sin z\le1+\eta z\). Direct expansion
then gives

\[
 \begin{split}
 \frac32l-c(1+\eta z)
  & =.095506688+5.495626136z-32.847192z^2+69.656z^3\\
  &\ge .095506688+
          \left(5.495626136-\frac{32.847192}{6}\right)z
   >.0955.
 \end{split}
\tag{11}
\]

This verifies (9) on one whole interval.

For the second family,

\[
 \frac23<k\le K<.817,\qquad
 k\le c<1.024,\qquad
 \frac23<m<\frac65,\qquad km<1.
\tag{12}
\]

For example, concavity and the two endpoint values give
\(\cos z+\eta\sin z>.95\) on \([L,h]\), while
\(\cos z+\eta\sin z<1.043\). Thus
\[
 m>.95K>\frac23,\qquad
 m<1.024(1.043)<\frac65,\qquad
 km<.817(1.024)(1.043)<1.
\]

Consequently both families satisfy precisely the concentration
requirements
\[
 \frac12\le k\le\frac{17}{20},\quad
 k\le c\le2,\quad k\le l\le2k,\quad
 \frac12\le l/m\le2.
\tag{13}
\]

## 3. A common exact polynomial certificate

Let \(S_j\) and \(C_j\) be the ordinary alternating sine and
cosine polynomials ending in degree j. Throughout \([0,h]\),
use

\[
 S_-=S_{11}\le\sin z\le S_9=S_+,\qquad
 C_-=C_{10}\le\cos z\le C_{12}=C_+.
\tag{14}
\]

Set

\[
 \bar R=1.978787508,\qquad
 \bar c=.899214066,\qquad
 \bar\sigma=1.415477291.
\tag{15}
\]

These are strict upper bounds for R, \(c_0\), and \(\sigma\):
positive squaring gives
\[
 \bar R^2>Q,\qquad
 (\bar c+1/2)^2>Q/2,\qquad
 \left(\bar\sigma+\frac{1+\eta}{2}\right)^2>Q(1+\eta^2).
\tag{16}
\]

For any weight polynomials k, l and c used on one of the stated
intervals, define

\[
                  m_-=c(C_-+\eta S_-),\qquad
                  m_+=c(C_++\eta S_+).
\tag{17}
\]

Then \(0<m_-\le m\le m_+\).

Here is the only radical-to-polynomial device needed. For
positive polynomials \(r_1,\ldots,r_n\), and polynomial upper
bounds \(P_i\) for the squared norms in a scalar, put

\[
 \begin{split}
 \mathcal D(\mathbf r)&=2\prod_i r_i,\\
 \mathcal N(A;\mathbf P,\mathbf r)
 &=2A\prod_i r_i
       -\bar R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.
 \end{split}
\tag{18}
\]

The elementary inequality
\[
                         \sqrt P\le\frac{P+r^2}{2r}
\tag{19}
\]
shows that a scalar at least \(A-R\sum_i\sqrt{P_i}\) is at
least \(\mathcal N/\mathcal D\).
The auxiliary \(r_i\) need only be positive. No assertion that
they approximate the roots is a premise.

For clarity, all coefficient comparisons below specify their
polynomials through (14)--(18), rather than giving a coefficient
inventory. If \(P(z)=\sum_i p_i z^i\), its coefficients about
a rational point x are exactly
\[
                   [P]_{x,j}=\sum_{i\ge j}
                          \binom ij p_i x^{i-j}.
\tag{20}
\]
Every aggregate below is therefore an explicit finite rational
expression. The inequalities establish positivity on complete
intervals.

## 4. The lower interval reduces to four scalars

Use (6) on \([0,L]\). In the notation of the concentration
theorem, its pairs are
\[
                 G=(k,l),\qquad H=(k,1),\qquad B=(l,m).
\tag{21}
\]

The scalar-envelope note proves the following facts.
The pure negative minimum is \(V_H(z)\), because \(V\) is
coordinatewise increasing for \(z\le1/6\) and the relevant
ratios lie in \([1/2,2]\). The H and B same-block alternatives
satisfy \(M_i(z)\ge V_i(z)\), by (9). The remaining same-block
alternative obeys
\[
 M_G(z)\ge V_H(z)
        +k\{\phi(h-z)-1\}+l(\cos h-\cos z),
 \qquad \phi(s)=\cos s+\sin s.
\tag{22}
\]

For the separated alternative, its uniform estimate
\[
                         U_{p,q}(s)\ge-.545qs
\tag{23}
\]
and \(q\le m\) give a positive-part lower bound
\(-.545m(h-z)\). This also covers the D alternative, since
\(c_0-1/2<.4<.545m\).
Its B negative part cannot be the minimum:
\[
                    V_B(h)>.87l>.87>V_H(h).
\tag{24}
\]
For the last comparison one may use \(k<.775\),
\(\sqrt{1+.775^2}<1.266\), \(.7648<\cos h<.765\),
and \(R<1.979\), obtaining
\[
 V_H(h)<-.235+1.979(1.266-.7648)<.8.
\]

It is therefore enough to prove positivity of four scalars:

\[
 \begin{split}
 B+V_H(z),\qquad&
 B+V_H(z)+k\{\phi(h-z)-1\}+l(\cos h-\cos z),\\
 B-.545m(h-z)+V_H(h),\qquad&
 B-.545m(h-z)+V_G(h).
 \end{split}
\tag{25}
\]

### 4.1. The only tight lower-interval scalar

Because \(c>1\), the original sorted D support is exactly
\(S(1,c)=(1+c)c_0\). After cancellation of the H norm at zero,
a polynomial lower bound for the nonradical part of \(B+V_H(z)\) is

\[
 \begin{split}
 A={}&2k+3l+\frac32m_-+\frac32+C_-
       +\frac c2(1+C_-+S_-)\\
    &-(1+c)\bar c-c\bar\sigma S_+.
 \end{split}
\tag{26}
\]

Use the three squared-norm upper bounds

\[
 P_H=1+k^2-2kS_-,\qquad
 P_G=k^2+l^2,\qquad
 P_B=m_+^2+l^2,
\tag{27}
\]

and the positive auxiliary polynomials

\[
 \begin{split}
 r_H&=.89(1-z^2/2)+.456(k-z+z^3/6),\\
 r_G&=.55k+.835l,\\
 r_B&=.729c(1+\eta z-z^2/2)+.6845l.
 \end{split}
\tag{28}
\]

On this entire interval, a centered coefficient sum gives
\[
                         r_H>1.09,\quad r_G>1.16,\quad r_B>1.42.
\tag{29}
\]

Let
\[
 \mathcal D=2r_Hr_Gr_B,\qquad
 P=\mathcal N(A;(P_H,P_G,P_B),(r_H,r_G,r_B)).
\tag{30}
\]

This explicitly defined polynomial has degree 34.
Expand \(P(L-x)=\sum_j a_jx^j\). Direct rational expansion gives

\[
 \begin{gathered}
 a_0>.00199,\qquad a_1>.0172,\qquad a_2>5.54,\\
 a_3-\sum_{\substack{j\ge4\\a_j<0}}|a_j|L^{j-3}>2.97.
 \end{gathered}
\tag{31}
\]

For example, the first coefficient is exactly
\[
 a_0=
 \frac{323394430823162533113808416734176389126673268916861323711041837256472632221}
 {161966341129312173206226862080000000000000000000000000000000000000000000000000}.
\]
For \(0\le x\le L\), the negative higher coefficients in (31)
are absorbed by the cubic term. All positive higher coefficients
may be discarded. Hence
\[
                  P(L-x)>.00199+.0172x+5.54x^2+2.97x^3>0.
\tag{32}
\]

Equations (18)--(19) prove \(B+V_H(z)>0\) on the whole
lower interval, including both endpoints.

### 4.2. The remaining same-block scalar

Put
\[
 c_h=C_{10}(h),\quad C_h=C_{12}(h),\quad s_h=S_{11}(h).
\tag{33}
\]

The exact identity
\(\phi(h-z)=\phi(h)\cos z-(\cos h-\sin h)\sin z\)
and (14) give the polynomial lower bound

\[
 J=k\{(c_h+s_h)C_--(C_h-s_h)S_+-1\}
                       +l(c_h-C_+)
\tag{34}
\]
for the extra term in (22). Thus the second scalar in (25)
is at least
\[
                         P_M/\mathcal D,\qquad P_M=P+\mathcal D J.
\tag{35}
\]

Write \(P_M(L/2+x)=\sum_j b_jx^j\). The whole-interval
quadratic certificate is

\[
 b_0>.0368,\qquad |b_1|<.475,\qquad
 b_2-\sum_{j\ge3}|b_j|(L/2)^{j-2}>7.48.
\tag{36}
\]

Consequently
\[
             P_M>.0368-.475|x|+7.48x^2
                 \ge .0368-\frac{.475^2}{4(7.48)}>.029>0.
\tag{37}
\]

### 4.3. The separated H and G scalars

Define the common nonradical lower bound

\[
 \begin{split}
 A_*={}&2k+3l+\frac32m_-+\frac52
        +\frac c2(1+C_-+S_-)\\
       &-(1+c)\bar c-c\bar\sigma S_+
                           -.545m_+(h-z).
 \end{split}
\tag{38}
\]

For the separated H scalar use

\[
 \begin{split}
 P_{Hh}&=1+k^2-2ks_h,\\
 P_{SH}&=\mathcal N
   (A_*+c_h-1;\ (P_{Hh},P_G,P_B);\ (.77,r_G,r_B)).
 \end{split}
\tag{39}
\]

For the separated G scalar use

\[
 \begin{split}
 P_{H0}&=1+k^2,\qquad P_{Gh}=k^2+l^2-2kls_h,\\
 P_{SG}&=\mathcal N
   (A_*+l(c_h-1);\ (P_{H0},P_{Gh},P_B);\
                    (.82+.572k,\ .765l,\ r_B)).
 \end{split}
\tag{40}
\]

All auxiliary polynomials here are positive. Both formulas
come from cancelling exactly the norm at zero belonging to
the added V term. In particular they retain the same original
baseline B.

If \(u_j=[P_{SH}]_{L/2,j}\), direct expansion gives
\[
                       u_0-\sum_{j\ge1}|u_j|(L/2)^j>.18.
\tag{41}
\]
Thus the separated H scalar is strictly positive.

For the other one, let
\[
 T(z)=\left(1-\frac zL\right)P_{SG}(0)
                              +\frac zL P_{SG}(L).
\]
The quotient
\[
                       Q_G(z)=\frac{P_{SG}(z)-T(z)}{z(L-z)}
\tag{42}
\]
is a polynomial, since the numerator vanishes at both endpoints.
The exact comparisons are
\[
 P_{SG}(0)>.0451,\qquad P_{SG}(L)>.3963,
\tag{43}
\]
and, with \(v_j=[Q_G]_{L/2,j}\),
\[
                         v_0-\sum_{j\ge1}|v_j|(L/2)^j>8.8.
\tag{44}
\]

Hence \(P_{SG}(z)\ge T(z)>0\). This proves positivity of
the fourth scalar in (25), and completes the entire lower
interval.

## 5. The upper interval has only two scalar obligations

For the weights (7), all three coefficient ratios \(p_i/q_i\)
are at least \(2/3\); moreover \(q_{\min}=1\) and
\(q_{\max}<6/5\). Section 4 of the scalar-envelope note
therefore removes every saturated alternative. It suffices to
show

\[
                          B+V_H(z)>0,\qquad B+V_B(z)>0.
\tag{45}
\]

There is a useful exact convention for the B comparison.
When \(m\le1\), its pair is \((m,1)\), and the formulas below
are precisely \(B+V_{m,1}(z)\). When \(m\ge1\), its actual
pair is \((1,m)\). In that case

\[
                 V_{1,m}(z)=mV_{1/m,1}(z)\ge V_{k,1}(z)=V_H(z).
\tag{46}
\]

Indeed \(km<1\), the function \(V_{r,1}(z)\) is increasing
in r on the relevant ratio interval, and it is positive for
\(z>0\). Positivity follows by concavity from its positive
value at h and its zero value at zero. For monotonicity,
the squared derivative comparison is
\[
 \sin z\{2r-(1+r^2)\sin z\}>0,
\]
using \(r\ge2/3\) and \(\sin h<.645\).
It is thus enough to certify \(B+V_{m,1}(z)>0\) where
\(m\le1\). We certify its algebraic expression on the
larger complete intervals for convenience.

In this section replace the sorted D support by its
complete-circle upper bound
\[
                        S(1,c)\le R\sqrt{1+c^2}-\frac{1+c}{2}.
\tag{47}
\]
This relaxation is valid also where \(c>1\).
After collecting the linear terms, both scalar expressions
have the common nonradical lower bound

\[
 A^+=2k+5+C_-+\frac32m_-+\frac c2
                 +\frac c2(1+C_-+S_-)-c\bar\sigma S_+.
\tag{48}
\]

Define
\[
 \begin{gathered}
 \widetilde m=c(C_4+\eta S_5),\\
 r_k=.81+.586k,\qquad
 r_m=.715+.699\widetilde m,\qquad
 r_c=.72+.694c,\\
 r_-^H=.9C_4+.435(k-S_5),\qquad
 r_-^B=.9C_4+.435(\widetilde m-S_5),\\
 P_k=1+k^2,\quad P_m=1+m_+^2,\quad P_c=1+c^2,\\
 P_-^H=1+k^2-2kS_-,\qquad
 P_-^B=1+m_+^2-2m_-S_-.
 \end{gathered}
\tag{49}
\]

All five auxiliary polynomials in (49) exceed .68 on
both intervals below. The two numerators are

\[
 \begin{split}
 P^H&=\mathcal N(A^+;\
             (P_k,P_m,P_-^H,P_c);\
             (r_k,r_m,r_-^H,r_c)),\\
 P^B&=\mathcal N(A^+;\
             (P_k,P_k,P_-^B,P_c);\
             (r_k,r_k,r_-^B,r_c)).
 \end{split}
\tag{50}
\]

The first bounds \(B+V_H\), while the second bounds
\(B+V_{m,1}\). In the latter expression, the coefficient of
\(\cos z-1\) is exactly one. Its use for the actual B pair
is restricted as explained in (46).

### 5.1. Before the coefficient clamp

Use (8) on \([L,b]\). The length is
\[
                              d=b-L=\frac{71}{240}.
\]
The polynomial \(P^H\) has degree 33. Expand
\(P^H(L+x)=\sum_j a_jx^j\). Exact expansion gives
\[
 a_0>.00154,\qquad a_1>.109,\qquad
 a_2-\sum_{\substack{j\ge3\\a_j<0}}|a_j|d^{j-2}>.77.
\tag{51}
\]

Thus \(P^H>.00154+.109x+.77x^2>0\) for all \(0\le x\le d\).
This is the tight upper-interval certificate; it already uses
the complete-circle D relaxation (47).

For \(P^B\), which has degree 29, use its coefficients
\(b_j\) about the midpoint \(151/480\). A single centered
sum gives
\[
                    b_0-\sum_{j\ge1}|b_j|(71/480)^j>.14.
\tag{52}
\]

Both obligations (45) follow throughout \([L,b]\).

### 5.2. After the coefficient clamp

Now \(k=c=K\), \(l=1\), on \([b,h]\). Use exactly the
same definitions (48)--(50); no new norm estimate is needed.
The midpoint and radius are \(93/160\) and \(19/160\).
For the coefficients \(a_j\) and \(b_j\) of \(P^H\) and
\(P^B\) about that midpoint, respectively, the whole-interval
comparisons are

\[
 \begin{split}
 a_0-\sum_{j\ge1}|a_j|(19/160)^j&>.10,\\
 b_0-\sum_{j\ge1}|b_j|(19/160)^j&>.03.
 \end{split}
\tag{53}
\]

The polynomial degrees are 29 and 24. This proves both
remaining scalar inequalities on \([b,h]\).

## 6. Completion

Sections 4 and 5 prove \(B(z)+\mathcal E(z)>0\) for every
\(0<z<h\), with weights satisfying (13). This contradicts
the necessary original-cycle inequality (4). The concentration
theorem already excluded \(z\le0\), so every TD2 error is
covered.

Together with the
[secondary-owner TD0 exclusion](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md),
the result covers both original TD owners, both HG owners,
and every sign and radial kind of A, T and E, under the other
five fixed original owners in (2).

The auxiliary intervals above come from the two explicit weight
formulas and the single coefficient clamp \(c=k\). Every bound
is a whole-interval analytic inequality or an exact rational
coefficient aggregate. No angular mesh, optimizer output,
generated case inventory, Lean build, or CI run is a premise.
