# Six short-word opposite-sign secondary families, without tables

All terminating decimals in this note are exact rationals. This proves
the whole outer/outer quarter-one families
\[
 (i,\sigma,\tau,j)\in
 \{(2,-,+,1),(2,-,+,3),(4,-,+,1),(4,-,+,3),
                         (6,-,+,1),(6,-,+,3)\}
\tag{1}
\]
for the role labels of the short wrong word \(0010111\). The final
coordinate \(j\) is the original separating axis. For every original
weak separator and every \(|\phi-\pi/2|\le.7\), the corrected cost satisfies
\[
 C_2>.8975,\qquad C_4>.89765,\qquad C_6>.89765.
\tag{2}
\]
Both angle halves and all owner ties are included. There are twelve
original angle branches in (1).

The proof uses one fixed support multiplier per role/owner family.
A common concave quadratic proves monotonicity on the positive angle
half. An exact norm identity proves concavity on the negative half.
There is no subdivision of either the angle interval or the state arcs.

## 1. States, normalization, and the common scalar

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12.
\]
An outer state is
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\qquad 0\le b\le d,
\tag{3}
\]
and the target state \((A,B)\) satisfies the same relation. In particular,
\[
 a'(b)=-\frac{b+\tfrac12}{a+\tfrac12},\qquad
 a''(b)=-\frac{Q}{(a+\tfrac12)^3}<0.
\tag{4}
\]
We will use
\[
\begin{gathered}
 1.414575671<a_0<1.414575672,\qquad
 .899214065109<d<.899214065110,\\
 R< R_+=1.978788,\qquad
 .764<\cos u\le1,\quad 0\le\sin u<.645
                     \quad(0\le u\le.7).
\tag{5}
\end{gathered}
\]
The algebraic bounds follow by squaring; the trigonometric ones follow
from their alternating series.

An original axis 1 is already in the following normalization.
For an original axis 3, reflect and reverse the pair, replacing the
source and target coefficients by
\[
 (c,p,q,P,t)\longmapsto(c,-P,t,-p,q).
\tag{6}
\]
The angle and corrected cost are preserved. The normalized signs are
\((-,+)\) in every case, and the retained separator becomes
\[
 -b+Ak+rBs\ge W,\qquad
 \phi=\frac\pi2+ru,\quad r\in\{-1,1\},\quad
 s=\sin u,\quad k=\cos u,\quad W=\frac{1+k+s}{2}.
\tag{7}
\]
The corrected cost is
\[
 C=\phi+c+pa-qb-PA-tB.
\tag{8}
\]

Here are the six exact tuples \((c,p,q,P,t;\lambda)\), in the order (1):
\[
\begin{aligned}
 {\cal T}_{2,1}&=(.6618,.09133,.88074,.51554,1.19909;\ .93308),\\
 {\cal T}_{2,3}&=(.6618,-.51554,1.19909,-.09133,.88074;\ 1.11499),\\
 {\cal T}_{4,1}&=(-.25931,.19335,.76744,0,.86884;\ 1.00982),\\
 {\cal T}_{4,3}&=(-.25931,0,.86884,-.19335,.76744;\ 1.08532),\\
 {\cal T}_{6,1}&=(-.1866,.18602,.80996,0,.94766;\ 1.10143),\\
 {\cal T}_{6,3}&=(-.1866,0,.94766,-.18602,.80996;\ 1.12741).
\end{aligned}
\tag{9}
\]
The first five coordinates come directly from the adjacent exact role
labels in \( \mathtt{short\_hand\_labels.json}\). The positive sixth
coordinate is a fixed multiplier for the original weak separator (7).

The source expression after subtracting that multiplier times the
separator margin is
\[
 pa+(\lambda-q)b.
\]
For \(p\ge0\), this expression is concave in \(b\), so a valid source
lower support is
\[
 S=\min\{pa_0,(p+\lambda-q)d\}.
\tag{10}
\]
For the sole negative-\(p\) tuple, \({\cal T}_{2,3}\), it is increasing:
by (4),
\[
 \frac{d}{db}\{pa+(\lambda-q)b\}
 \ge .51554(.26115)-.0841>0.
\tag{11}
\]
Here \((b+\tfrac12)/(a+\tfrac12)\ge
1/[2(a_0+\tfrac12)]>.26115\). Thus \(S=pa_0\) for this tuple.

For every real \(X,Y\), the full circle gives the lower support
\[
 XA+YB\ge-\frac{X+Y}{2}-R\sqrt{X^2+Y^2}.
\tag{12}
\]
Applying (12) with \(X=-P-\lambda k\) and
\(Y=-t-r\lambda s\), and applying the source support above, gives
\[
\begin{split}
 C\ge F_r(u):={}&\frac\pi2+ru+c+S+
  \frac{\lambda+P+t}{2}+\lambda k+
                  \frac{1+r}{2}\lambda s-RN_r(u),\\
 N_r(u)^2={}&P^2+t^2+\lambda^2+2\lambda(Pk+rts).
\end{split}
\tag{13}
\]
This deduction used the original separator itself; it did not replace
a separating-axis union by one preferred owner.

## 2. The whole positive half is increasing

Fix any tuple in (9), and put
\[
 h=Pk+ts,\qquad g=tk-Ps,\qquad N=N_+.
\]
Throughout \(0\le u\le.7\), the exact coefficients and (5) give
\[
 g>0,\qquad \lambda+h>0,\qquad
 N^2=(\lambda+h)^2+g^2.
\tag{14}
\]
For the only positive \(P\), positivity of \(g\) follows already from
\(1.19909(.764)-.51554(.645)>0\). For \(P\le0\), it is immediate.
Also \(\lambda+h\ge\lambda+\min\{P,0\}>0\).

Differentiating (13) and using \(N\ge\lambda+h\), we obtain
\[
 F_+'(u)
 =1+\lambda(k-s)-R\lambda\frac{g}{N}
 \ge\frac{J(u)}{\lambda+h},
\tag{15}
\]
where
\[
 J(u)=\{1+\lambda(k-s)\}(\lambda+Pk+ts)-R_+\lambda(tk-Ps).
\tag{16}
\]
The replacement of \(R\) by \(R_+\) is justified by \(g>0\).

Define the exact rational constants
\[
 A=P+\lambda^2-R_+\lambda t,\qquad
 B=t-\lambda^2+R_+\lambda P.
\tag{17}
\]
Expansion of (16), using \(k^2=1-s^2\), gives
\[
 J=\lambda(1+P)+Ak+Bs-\lambda(P+t)s^2+
                                      \lambda(t-P)sk.
\tag{18}
\]
For every tuple in (9), \(A<-.66\) and \(t-P>0\).
The elementary inequalities
\[
 k=\sqrt{1-s^2}\le1-\frac{s^2}{2},\qquad k>.764
\]
therefore yield
\[
 J(u)\ge q_*(s):=
 \lambda(1+P)+A+
 [B+.764\lambda(t-P)]s+
 [-\lambda(P+t)-A/2]s^2.
\tag{19}
\]
Direct rational substitution from (9) and (17) gives, for all six tuples,
\[
 -\lambda(P+t)-A/2<-.29,\qquad
 q_*(0)>.195,\qquad q_*(.645)>.041.
\tag{20}
\]
These are six fixed rational comparisons, not sampled-angle assertions.
For example the smallest right-end value is the last tuple's exact
value
\[
 q_*(.645)=
 \frac{2077692808538408393}{50000000000000000000}>.041.
\tag{21}
\]
All constants in (20) are given explicitly by (9), (17), and (19), so
each comparison can also be checked by multiplying positive integer
denominators.

The quadratic \(q_*\) is concave. Hence (20) proves \(q_*(s)>.041\)
throughout \(0\le s\le.645\). Equations (15) and (19) prove
\[
 F_+'(u)>0\qquad(0\le u\le.7).
\tag{22}
\]
In particular, the positive half has its lower bound at \(u=0\).

## 3. The whole negative half is concave

Put \(N=N_-\) and
\[
 N_0=N_-(0)=\sqrt{(P+\lambda)^2+t^2}.
\]
All six negative-half norms are positive. Indeed
\(t-\lambda s\ge t-.645\lambda>.067\), and
\[
 N^2=(P+\lambda k)^2+(t-\lambda s)^2.
\]
The following identity retains the cosine factor that is needed for
the whole interval:
\[
 N(u)^2-N_0^2k^2
   =N_0^2s^2-2\lambda P(1-k)-2\lambda ts.
\tag{23}
\]
If \(P\ge0\), use \(1-k\ge s^2/2\). If \(P<0\), use
\(1-k=s^2/(1+k)<s^2/1.764\).
Consequently
\[
 N(u)^2-N_0^2k^2\le s(Ds-2\lambda t),
\tag{24}
\]
where the fixed rational coefficient is
\[
 D=
 \begin{cases}
 N_0^2-\lambda P,&P\ge0,\\
 N_0^2+2\lambda|P|/1.764,&P<0.
 \end{cases}
\]
For all six tuples, exact substitution gives
\[
 2\lambda t-.645D>.267,\qquad 4\lambda-R_+N_0>.011.
\tag{25}
\]
For the second comparison it suffices to use the explicit upper bounds
on \(N_0\) in Section 4. Thus (24) proves
\[
 N(u)\le N_0 k.
\tag{26}
\]

Differentiating the squared norm in (13) twice gives the exact
circle-norm identity
\[
 N''+\frac N4=
 \frac{(P^2+t^2-\lambda^2)^2}{4N^3}\ge0.
\tag{27}
\]
Therefore (13), (26), and (25) imply
\[
 F_-''=-\lambda k-RN''
 \le-\lambda k+\frac{RN}{4}
 \le k\left(-\lambda+\frac{RN_0}{4}\right)<0.
\tag{28}
\]
This proves concavity on the entire interval. Its minimum is therefore
at \(u=0\) or \(u=.7\).

## 4. The fixed endpoint arithmetic

For clarity, here are sufficient rational bounds for all endpoint
comparisons. They appear in the order of (9):
\[
\begin{aligned}
 S&\ge
 (.129190084,\ -.729270342,\ .273508205,\ 0,\ .263139366,\ 0),\\
 N_0&<
 (1.880509701,\ 1.350400957,\ 1.332148407,\
             1.176679496,\ 1.452999491,\ 1.241873719),\\
 N_-(.7)&<
 (1.366936046,\ .778595795,\ .802609647,\
                  .640396588,\ .875421590,\ .681426094).
\end{aligned}
\tag{29}
\]
The source bounds follow from (5), (10), and (11). The \(N_0\) bounds
follow by squaring. For \(N_-(.7)\), substitute in its displayed squared
norm the rational alternating-series bounds
\[
\begin{gathered}
 .64421768723<\sin(.7)<.64421768724,\\
 .76484218728<\cos(.7)<.76484218729,
\end{gathered}
\tag{30}
\]
and square the proposed upper bound. The sign of \(P\) determines which
cosine endpoint is used. These checks concern only the two endpoints
of a scalar already proved monotone or concave.

Substituting (29), (30), \(R<R_+\), and
\(\pi/2>1.570795\) in (13) gives
\[
\begin{aligned}
 F_\pm(0)&>
 (.89758,\ .89835,\ .89810,\ .89811,\ .89813,\ .92987),\\
 F_-(.7)&>.994\quad\hbox{for all six tuples}.
\end{aligned}
\tag{31}
\]
For example, the first and smallest initial rational lower bound is
\[
 1.570795+.6618+.129190084+
       \frac{.93308+.51554+1.19909}{2}+.93308
          -1.978788(1.880509701)
 =\frac{224397513444403}{250000000000000}>.89758.
\tag{32}
\]
The same literal substitution proves the other five comparisons in
(31).

The monotonicity (22), concavity (28), and endpoint bounds (31)
prove (2) over every original case in (1), including \(u=0\), \(u=.7\),
arc endpoints, and simultaneous separating owners. The edge-2 constant
is intentionally the assembly's \(.8975\); together with six other
edge bounds \(.89765\), it retains the strict cyclic reserve
\[
 .8975+6(.89765)=\frac{31417}{5000}>\frac{710}{113}>2\pi.
\]

