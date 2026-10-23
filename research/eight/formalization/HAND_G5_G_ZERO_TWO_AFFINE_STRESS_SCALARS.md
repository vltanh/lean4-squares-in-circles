# Two continuous stresses exclude the zero-transverse outer endpoint

## 1. The scalar domain and theorem

Put

\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,
 \qquad k_0=\sqrt{Q-1/4}-1,
 \qquad L=\frac{311}{1000},\quad h_0=\frac{107}{1000}.
\tag{1}
\]

The scalar domain in this note is

\[
 0\le x\le\frac{51}{250},\qquad
 h_0\le h\le L-x,\qquad
 0\le t,d\le x,
 \qquad u=x-t,\quad v=x-d.
\tag{2}
\]

In geometric use, x is the H/D span, t and u split that span at
the common A/B frame, d and v split it at E, and h is the remaining
positive HG error. Establishing (2) from an original candidate is
a separate entry step. The proof below is on all of (2), not on
sampled angles or on an assumed stationary neighborhood.

Define five positive weights \(a,b,e,k,\lambda\) by affine
interpolation. For \(0\le x\le17/100\), interpolate between

\[
\begin{aligned}
 (a,b,e,k,\lambda)(0)&=(.780,1.240,1.376,.382,1.128),\\
 (a,b,e,k,\lambda)(.17)&=(.755,1.100,1.090,.431,1.090).
\end{aligned}
\tag{3}
\]

For \(17/100\le x\le51/250\), interpolate between the second
line of (3) and

\[
 (a,b,e,k,\lambda)(.204)=(.7495,1.030,.964,.416,1.080).
\tag{4}
\]

Every decimal in (3)--(4) is an exact rational number. These are
two formulas for continuous weights; they agree at their one join.
Put

\[
 c=\cos x,\quad s=\sin x,\qquad f=e c+k s,
 \qquad g(h)=\tfrac12+\tfrac12\cos h-k_0\sin h.
\tag{5}
\]

Use the original corner support for the five forces

\[
\begin{aligned}
 F_A&=(\cos(t+h),\ a-\sin(t+h)),\\
 F_B&=(b\cos u,\ a-b\sin u),\\
 F_D&=(f,b),\\
 F_E&=(f\sin d+e\sin v,\ f\cos d-e\cos v),\\
 F_H&=(e,\lambda).
\end{aligned}
\tag{6}
\]

Write \(W(z)=(1+\cos z+\sin z)/2\). Define N to be

\[
\begin{split}
N={}&\lambda g(h)+W(t+h)+a+b(1+W(u))
                         +fW(d)+eW(v)\\
 &-\sum_{i=A,B,D,E}\{R|F_i|-(F_{i,1}+F_{i,2})/2\}
                         -H(e,\lambda),
\end{split}
\tag{7}
\]

where the exact sorted-H support is

\[
 H(e,\lambda)=
 \begin{cases}
 R\sqrt{e^2+\lambda^2}-(e+\lambda)/2,&x\le.17,\\
 (R/\sqrt2-1/2)(e+\lambda),&x\ge.17.
 \end{cases}
\tag{8}
\]

Indeed \(e\ge\lambda\) on the first interval and
\(e\le\lambda\) on the second. The second support follows from
the actual sorted H condition \(a_H\ge b_H\), whose boundary
has equal corner coordinates. At the join the two supports agree.

**Scalar theorem.** On the entire domain (2),

\[
                              N>\frac{13}{50000}.
\tag{9}
\]

Consequently no five-anchor/G-zero endpoint with squared corner
ceiling at most Q can satisfy (2) and the six inequalities

\[
\begin{gathered}
 b_H\ge g(h),\qquad
 a_A\cos(t+h)-b_A\sin(t+h)\ge W(t+h),\\
 b_A+b_B\ge1,\qquad
 a_B\cos u-b_B\sin u+b_D\ge1+W(u),\\
 a_D+a_E\sin d+b_E\cos d\ge W(d),\\
 a_H+a_E\sin v-b_E\cos v\ge W(v).
\end{gathered}
\tag{10}
\]

H, A, B and D have nonnegative own-frame coordinates as displayed.
E may have either signed transverse coordinate `b_E`: its actual
corner condition is `(a_E+1/2)^2+(|b_E|+1/2)^2<=Q`. Thus the
statement also covers the reflected outer endpoint without imposing
a new E sign after reflection.

To see the implication, give (10) respective weights
\(\lambda,1,a,b,f,e\), collect (6), and apply the five actual
corner disks and the sorted H support. Feasibility would give
\(N\le0\), contrary to (9). If the original containing ceiling
is q<Q, its G-zero primary is at most
\(\sqrt{Q-1/4}-1/2\), so the first inequality of (10) remains
necessary. No replacement circle of radius Q is asserted to be
an original contact.

For signed E, its contribution has the same upper bound used in
(7), because

\[
 F_{E,1}a_E+F_{E,2}b_E
 \le F_{E,1}a_E+|F_{E,2}|\,|b_E|
 \le R|F_E|-(F_{E,1}+|F_{E,2}|)/2
 \le R|F_E|-(F_{E,1}+F_{E,2})/2.
\]

No E sign is used by any scalar comparison below.

## 2. The two frame splits have one worst endpoint

The E force has the exact norm

\[
 |F_E|^2=f^2+e^2-2fe\cos x
                 =s^2(e^2+k^2).
\tag{11}
\]

Thus its norm is independent of d. Its entire d-dependent part
in (7) is

\[
                      f(\cos d+\sin d)+e\sin(x-d).
\]

This function is concave for \(0\le d\le x\), so its minimum
is at an endpoint. The difference between the values at d=0
and d=x is exactly

\[
 \frac{s^2}{1+c}\{e(c+s)-k(1+c-s)\}\ge0.
\tag{12}
\]

It is positive when x>0: on both intervals \(e\ge.964\),
\(2k\le.862\), \(c+s\ge1\), and \(1+c-s\le2\).
Consequently the worst E split has

\[
                              d=x,\qquad v=0.
\tag{13}
\]

For the A/B split, abbreviate

\[
 A(z)=\cos z-R\sqrt{1+a^2-2a\sin z},
\]
\[
 B(z)=b\cos z-R\sqrt{b^2+a^2-2ab\sin z}.
\tag{14}
\]

The only t-dependent part is \(A(t+h)+B(x-t)\).
Both functions are strictly concave on the interval needed here.
For completeness, for \(0<p\le4/5\) and \(0\le z\le L\),
the second derivative of
\(\cos z-R\sqrt{1+p^2-2p\sin z}\) is

\[
 -\cos z+R\frac{p(p-\sin z)(1-p\sin z)}
                         {(1+p^2-2p\sin z)^{3/2}}.
\tag{15}
\]

If the numerator is nonpositive, negativity is immediate.
Otherwise the positive fraction decreases as \(\sin z\)
increases. Its derivative has the opposite sign to

\[
 1-p^2+p^4-p(1+p^2)\sin z+p^2\sin^2z
 \ge\frac34-\frac45\frac{41}{25}\frac{311}{1000}>0.
\]

It is therefore at most \(p^2/(1+p^2)^{3/2}<25/82\).
Since \(R<2\) and \(\cos z>19/20\), (15) is less than
\(-279/820\). Apply this first with p=a and then with p=a/b,
including the positive factor b in the latter application.

The t minimum is therefore at 0 or x. In fact t=x is the worse
endpoint. To check this without comparing unrelated circle states,
put \(p=a/b\) and
\(n(q,z)=\sqrt{1+q^2-2q\sin z}\). Direct differentiation and
positive denominator comparison give

\[
\begin{split}
B'(z)-A'(z)
\ge(b-1)\left\{-\sin z+
\frac{Ra^2\cos z\,(p-\sin z)}{b\,n(a,z)^2n(p,z)}\right\}.
\end{split}
\tag{16}
\]

For the first weight interval, the positive term in braces is
greater than

\[
 \frac{(197/100)(9/16)(197/200)(43/100)}
      {(5/4)(13/8)(5/4)}
   =\frac{15019083}{81250000}>\frac9{50}>\sin z
\tag{17}
\]

when \(0\le z\le x\le.17\). Here \(a>.75\), \(p>.6\),
\(b<5/4\), \(n(a,z)^2<13/8\), and \(n(p,z)<5/4\).
For the second interval, use \(a>.74\), \(p>.68\),
\(b\le1.1\), \(n(a,z)^2<8/5\), and \(\cos z>.979\).
The positive term is then greater than

\[
 \frac{(197/100)(37/50)^2(979/1000)(119/250)}
      {(11/10)(8/5)(5/4)}
    =\frac{2856318563}{12500000000}>
                    \frac{11}{50}>\sin z.
\tag{18}
\]

Thus \(B'(z)>A'(z)\). Concavity of A also gives
\(A'(z+h)\le A'(z)\). Integrating from 0 to x proves

\[
 A(h)+B(x)\ge A(x+h)+B(0).
\tag{19}
\]

Together with t concavity, this proves the worst split is

\[
                              t=x,\qquad u=0.
\tag{20}
\]

## 3. Only the two outer-error endpoints remain

With the weights held fixed at x, h enters through
\(\lambda g(h)+A(t+h)\). On the whole domain,

\[
 g''(h)=-\tfrac12\cos h+k_0\sin h
       <-\frac{19}{40}+.915\frac{311}{1000}<0.
\tag{21}
\]

Together with (15), this proves strict h concavity. After
(13) and (20), it suffices to check

\[
 N_0(x):=N(x,0,x,0,h_0),\qquad
 N_1(x):=N(x,0,x,0,L-x),
\tag{22}
\]

where the entries in (22) name \((t,u,d,v,h)\).
The entire domain (2) has been reduced to these two functions by
continuous comparisons; no state enumeration is being used.

Here is a useful explicit formula for either function. Put
\(z=x+h\), let

\[
\begin{gathered}
 n_A=\sqrt{1+a^2-2a\sin z},\quad
 n_B=\sqrt{a^2+b^2},\quad n_D=\sqrt{f^2+b^2},\\
 n_K=\sqrt{e^2+k^2},\qquad
 n_H=\begin{cases}\sqrt{e^2+\lambda^2},&x\le.17,\\
                    (e+\lambda)/\sqrt2,&x\ge.17.
       \end{cases}
\end{gathered}
\tag{23}
\]

Then

\[
\begin{split}
N_j(x)={}&\tfrac12+2a+3b+e+\lambda
             +f(1+\cos x+\sin x)\\
 &+\lambda(\tfrac12\cos h-k_0\sin h)+\cos z\\
 &-R\{n_A+n_B+n_D+\sin x\,n_K+n_H\}.
\end{split}
\tag{24}
\]

## 4. One whole-interval Taylor estimate for each weight formula

Both functions in (22) are strictly decreasing on each of the two
weight intervals. The following short coefficient calculation gives
quantitative bounds and avoids assuming that the functions are
concave in x.

For a smooth function V write \([V]_r=V^{(r)}/r!\) at the point
under consideration. At the midpoint \(m=17/200\) of the first
interval, both functions have

\[
 [N_j]_1<-\frac{99}{1000},\qquad
 |[N_j]_2|<\frac{101}{1000},\qquad
 |[N_j]_3|<\frac{19}{125}.
\tag{25}
\]

Throughout that whole interval, \(|[N_j]_4|<14\).
At the midpoint \(m=187/1000\) of the second interval, both have

\[
 [N_j]_1<-\frac{19}{250},\qquad
 |[N_j]_2|<\frac{29}{20},\qquad
 |[N_j]_3|<\frac{91}{50},
\tag{26}
\]

and throughout that interval \(|[N_j]_4|<68\).
The exact algebra giving these coefficient bounds is recorded below.

Taylor's theorem applied to \(N_j'\), with \(|x-m|\le r\), gives

\[
 N_j'(x)\le [N_j]_1(m)+2|[N_j]_2(m)|r
             +3|[N_j]_3(m)|r^2
             +4\sup|[N_j]_4|r^3.
\tag{27}
\]

For \(r=17/200\), (25) and (27) give the exact upper bound

\[
 -\frac{99}{1000}
 +2\frac{101}{1000}\frac{17}{200}
 +3\frac{19}{125}\left(\frac{17}{200}\right)^2
 +56\left(\frac{17}{200}\right)^3
 =-\frac{110361}{2500000}<-\frac1{25}.
\tag{28}
\]

For \(r=17/1000\), (26) gives

\[
 -\frac{19}{250}
 +2\frac{29}{20}\frac{17}{1000}
 +3\frac{91}{50}\left(\frac{17}{1000}\right)^2
 +272\left(\frac{17}{1000}\right)^3
 =-\frac{5946431}{250000000}<-\frac1{50}.
\tag{29}
\]

Thus only the right endpoint of each complete weight interval needs
a value comparison.

### Exact coefficient arithmetic in (25)--(26)

All coefficient checks use only fourth-order differentiation of (24).
The following formulas specify the calculation completely. For
\(P(y)=\sum_{r=0}^4p_ry^r+O(y^5)\), \(p_0>0\), set
\(v_0=\sqrt{p_0}\). The first four coefficients of \(\sqrt P\) are

\[
\begin{aligned}
v_1={}&p_1/(2v_0),\\
v_2={}&p_2/(2v_0)-p_1^2/(8v_0^3),\\
v_3={}&p_3/(2v_0)-p_1p_2/(4v_0^3)+p_1^3/(16v_0^5),\\
v_4={}&p_4/(2v_0)-(2p_1p_3+p_2^2)/(8v_0^3)
       +3p_1^2p_2/(16v_0^5)-5p_1^4/(128v_0^7).
\end{aligned}
\tag{30}
\]

Equivalently one may use
\(2v_0v_r=p_r-\sum_{i=1}^{r-1}v_iv_{r-i}\).
For an affine weight its only nonzero coefficients are its stated
value and its exact slope from (3) or (4). The sine and cosine
coefficients are their cyclic derivatives divided by \(r!\).
For h=L-x each derivative has the additional factor \((-1)^r\);
for h=h0 its positive-order coefficients vanish. Products use the
ordinary finite convolution.

These formulas apply to the five radicands in (23). All their
denominators are positive; on the first interval the respective
lower norm bounds for A, B, D, K and H are

\[
                 1.052,\quad1.334,\quad1.537,\quad1.154,\quad1.541,
\tag{31}
\]

and on the second they are

\[
                 1.050,\quad1.273,\quad1.445,\quad1.049;
\tag{32}
\]

H is affine on the second interval. Lower bounds in (31)--(32)
are obtained by positive squaring after substitution in (23).

For every trigonometric value used in this calculation, the rational
enclosures are

\[
 S_7(y)\le\sin y\le S_7(y)+y^9/9!,\qquad
 C_8(y)-y^{10}/10!\le\cos y\le C_8(y),
\tag{33}
\]

where

\[
 S_7=y-y^3/6+y^5/120-y^7/5040,
 \quad C_8=1-y^2/2+y^4/24-y^6/720+y^8/40320.
\]

Only \(0\le y\le L\) occurs. For an interval of such y, sine
increases and cosine decreases, so their endpoint enclosures give
whole-interval enclosures. In particular (33) is not a collection
of pointwise assumptions.

The only algebraic constants in this calculation are enclosed by
the positive-square comparisons

\[
 1.978787<R<1.978788,\qquad .914575<k_0<.914576.
\]

Thus (30), the exact affine slopes, these two brackets, and (33)
are a fully rational way of checking every enclosure below.

At the two midpoints, substitution in (30), (33), and (24) gives
the following common coefficient enclosures, stated with outward
rational slack:

\[
\begin{array}{c|ccc}
 & [N_j]_1&[N_j]_2&[N_j]_3\\ \hline
 m=.085&(-.100,-.099)&(-.101,-.080)&(-.152,-.110)\\
 m=.187&(-.080,-.076)&(1.407,1.450)&(-1.820,-1.809).
\end{array}
\tag{34}
\]

Both values of j are enclosed in each row. The table records
coefficients at the two rational reference points, not a cover of
the angle domain. Equations (25)--(26) follow immediately.

For clarity, the whole-interval fourth-order remainder also has
small component bounds. Substituting the full intervals into the
same formulas gives

\[
\begin{split}
(&|[n_A]_4|,|[n_B]_4|,|[n_D]_4|,
                  |[\sin x\,n_K]_4|,|[n_H]_4|)\\
 &\le(1/2,1/25,3,2,3/5)\qquad (0\le x\le.17),\\
 &\le(1/10,5/4,18,13,0)\qquad (.17\le x\le.204),
\end{split}
\tag{35}
\]

For these enclosures use the displayed square-root recurrence,
forming each squared norm from its two force components before
applying the recurrence. This retains the common quantities in the
derivative formulas; all inputs are the rational bounds printed here.

where the zero in the last line means exact equality for that
affine component. For the three nonaffine terms preceding the
norms in (24), their fourth-order absolute bounds are

\[
 (3/2,1/16,1/24)\quad\hbox{and}\quad(5/2,1/10,1/24),
\tag{36}
\]

respectively, in the order \(f(1+\cos x+\sin x)\),
\(\lambda(\tfrac12\cos h-k_0\sin h)\), and \(\cos z\).
Affine terms have zero fourth coefficient. Since R<2, the sum
of (35)--(36) is less than 14 in the first case and 68 in the
second. For example the exact reserves in these two last
positive-rational comparisons are \(139/1200\) and \(79/120\).
This proves the full-interval remainder bounds used in (27).

## 5. The three rational endpoint value comparisons

Write (24) as \(N_j=U-RV\), where U denotes its first two lines
and V is the sum of its five nonnegative norm terms. The same
alternating bounds (33) and positive squaring give

\[
\begin{array}{c|cc}
 (x,h)&U\text{ lower bound}&V\text{ upper bound}\\ \hline
 (.17,.107)&11.359259&5.739013\\
 (.17,.141)&11.313483&5.715927\\
 (.204,.107)&10.760023&5.437549.
\end{array}
\tag{37}
\]

All inequalities in (37) are strict. These are the three endpoints
selected by the preceding analytic comparisons. At x=.204 the two
h endpoints coincide.

The rational upper bound \(R<1.978788\) has squared reserve
\(121809/62500000000\). Using it in (37), the first two N values
exceed \(14/5000\), with exact reserves

\[
 \frac{42235939}{250000000000},\qquad
 \frac{18810881}{250000000000},
\tag{38}
\]

and the last exceeds \(13/50000\), with reserve

\[
                         \frac{1572347}{250000000000}>0.
\tag{39}
\]

The monotonicity from (28)--(29) proves (9) for both h functions.
The continuous comparisons in Sections 2--3 then prove it on all
of (2), and the positive circle stress proves the exclusion of
(10).

The proof uses two explicit continuous affine weight formulas, one
Taylor estimate on each of their whole domains, and three rational
endpoint comparisons. It has no angle mesh, state cover, sampled
minimum, generated Bernstein row inventory, external acceptance
result, Lean compilation, or CI premise.
