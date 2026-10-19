# Eight same-sign short-word owners by one unit support

This note removes all angle-table dependencies for the following
outer/outer quarter-one original owners of \(0010111\):
\[
\begin{gathered}
 (2,-,-,1),\ (4,-,-,1),\ (4,+,+,3),\ (6,+,+,3),\\
 (2,-,-,2),\ (4,-,-,2),\ (4,+,+,4),\ (6,+,+,4).
\end{gathered}
\tag{1}
\]
For each of these eight original owner families, and on both complete
angle halves \(|\phi-\pi/2|\le.7\), the corrected cost satisfies
\[
 C>.949>.89765.
\tag{2}
\]
Thus all sixteen angle branches, including separating-axis ties, satisfy
the short-word assembly's required bound. A single multiplier
\(\lambda=1\) suffices throughout.

Every terminating decimal below is an exact rational. No angle
subdivision, state subdivision, coefficient-status table, or numerical
minimum is a premise.

## 1. Geometry and exact label normalization

Use
\[
 Q=\frac{9789}{2500},\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12.
\]
Both outer states lie on
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad 0\le b\le d,
 \qquad
 A=\sqrt{Q-(B+\tfrac12)^2}-\tfrac12,\quad 0\le B\le d.
\tag{3}
\]
In particular,
\[
 d\le a,A\le a_0,\qquad
 a'(b)<0,\quad a''(b)<0.
\tag{4}
\]
The rational bounds used in this proof are
\[
\begin{gathered}
 1.414575671<a_0<1.414575672,\qquad
 .899214065109<d<.899214065110,\\
 \cos u>.764,\quad 0\le\sin u<.645
                     \qquad(0\le u\le.7),\\
 \cos(.7)<.765,\qquad \frac\pi2>1.570795.
\end{gathered}
\tag{5}
\]
They follow by squaring and the alternating series.

Write
\[
 \phi=\frac\pi2+ru,\quad r\in\{-1,1\},\quad
 0\le u\le.7,\quad k=\cos u,\quad s=\sin u,\quad
 W=\frac{1+k+s}{2}.
\tag{6}
\]
After the exact reflection and reversal for target-owned axes, the
first line of (1) has normalized signs \((-,-)\), source axis 1,
and tuples
\[
\begin{aligned}
 {\cal V}_2&=(c,p,q,P,t)=(-.53489,.09133,.88074,-.33147,1.1336),\\
 {\cal V}_{4,-}&=(-.53062,.19335,.76744,-.20967,.83048),\\
 {\cal V}_{4,+}&=(.03846,0,.86884,0,.71553),\\
 {\cal V}_6&=(-.20704,0,.94766,-.21826,.83472).
\end{aligned}
\tag{7}
\]
The second line of (1) has normalized signs \((+,+)\), source axis 4,
and tuples
\[
\begin{aligned}
 {\cal U}_2&=(-.53489,.33147,1.1336,-.09133,.88074),\\
 {\cal U}_{4,-}&=(-.53062,.20967,.83048,-.19335,.76744),\\
 {\cal U}_{4,+}&=(.03846,0,.71553,0,.86884),\\
 {\cal U}_6&=(-.20704,.21826,.83472,0,.94766).
\end{aligned}
\tag{8}
\]
Each tuple is the literal difference of the adjacent affine role
labels in \( \mathtt{short\_hand\_labels.json}\). For example,
reflection and reversal replaces
\((p,q,P,t,\sigma,\tau)\) by
\((-P,t,-p,q,-\tau,-\sigma)\); this explains the original
axis-3 and axis-2 entries in (1).

We work directly with the original weak separator after this
normalization, so no owner tie is omitted.

## 2. The V families: both secondary angle halves

For a tuple in (7), the cost and separator are
\[
 C=\phi+c+pa-qb-PA+tB,\qquad
 -b+Ak-rBs\ge W.
\tag{9}
\]
Subtract the separator margin, with multiplier one. The source and
target expressions are
\[
 pa+(1-q)b,\qquad (-P-k)A+(t+rs)B.
\tag{10}
\]
The source expression is concave in \(b\). Its axial endpoint is the
smaller endpoint because, for all four tuples,
\[
 (p+1-q)d-pa_0>.047.
\tag{11}
\]
For \(p=0\), this is immediate; the other two comparisons follow by
substitution from (5) and (7).

For the target expression,
\[
 -P-k<.33147-.764<0,\qquad
 t+rs>.71553-.645>0.
\]
Its derivative in \(B\) is positive, so its minimum is axial.
It follows that
\[
 C\ge G_r(u):=\frac\pi2+ru+c+(p-P)a_0+
               \frac12+\left(\frac12-a_0\right)k+\frac s2.
\tag{12}
\]

For \(r=1\),
\[
 G_+'=1+(a_0-\tfrac12)s+\tfrac12 k>0.
\tag{13}
\]
For \(r=-1\),
\[
 G_-''=(a_0-\tfrac12)k-\tfrac12s
  >.914575671(.764)-.645/2>.37.
\tag{14}
\]
Thus \(G_-'\) is increasing. At its right endpoint,
\[
 G_-'(.7)
 <-1+.914575672(.645)+.765/2<-.027.
\tag{15}
\]
Consequently \(G_-\) is decreasing on the entire interval.

The fixed endpoint substitutions give, for every tuple in (7),
\[
 G_+(0)>1.194,\qquad G_-(.7)>1.031.
\tag{16}
\]
For the latter comparison one may use
\[
 .64421768723<\sin(.7)<.64421768724,\qquad
 .76484218728<\cos(.7)<.76484218729.
\tag{17}
\]
The smallest right-end value is the tuple \({\cal V}_{4,+}\);
the literal formula (12) and (5), (17) give its lower bound
\(1.031857\). Thus all eight branches from the first line of (1)
satisfy (2).

## 3. The U families on the negative half

For a tuple in (8), the cost and separator are
\[
 C=\phi+c+pa+qb-PA-tB,\qquad
 a+rAs-Bk\ge W.
\tag{18}
\]
Again use multiplier one. The source expression is
\[
 (p-1)a+qb.
\]
It is increasing in \(b\), since \(p<1\) and \(q>0\), so its minimum is
\[
 (p-1)a_0.
\tag{19}
\]

When \(r=-1\), the target expression is
\[
 (-P+s)A+(k-t)B.
\tag{20}
\]
Here \(-P+s\ge0\). Therefore (20) is concave in \(B\), regardless of
the sign of \(k-t\). Its minimum lies at the axial or diagonal endpoint.

The corresponding two scalar lower bounds are
\[
\begin{aligned}
 A_-(u)&=\frac\pi2-u+c+(p-1-P)a_0+\frac12+
                       \frac k2+(\tfrac12+a_0)s,\\
 D_-(u)&=\frac\pi2-u+c+(p-1)a_0-(P+t)d+\frac12+
                                      (\tfrac12+d)(s+k).
\end{aligned}
\tag{21}
\]
Thus \(C\ge\min\{A_-(u),D_-(u)\}\).

The axial scalar is increasing throughout:
\[
 A_-'=-1-\frac s2+(\tfrac12+a_0)k
 >-1-.645/2+1.914575671(.764)>.14.
\tag{22}
\]
The diagonal scalar is concave throughout:
\[
 D_-''=-(\tfrac12+d)(s+k)<0.
\tag{23}
\]
It is therefore enough to check the three fixed endpoint values.
Substitution from (5), (8), and (17) gives, for all four tuples,
\[
 A_-(0)>1.194,\qquad
 D_-(0)>1.279,\qquad D_-(.7)>1.151.
\tag{24}
\]
This proves (2) for all four negative-half primary branches.

## 4. The U families on the positive half

For \(r=1\), the target expression after subtraction is
\[
 (-P-s)A+(k-t)B.
\tag{25}
\]
The four tuples have \(P\le0\) and \(t>.764\). Using only the full arc
bounds (4) and (5), we have
\[
 (-P-s)A+(k-t)B
 \ge -Pd-a_0s-(t-.764)d.
\tag{26}
\]
Indeed the term \(-PA\) is at least \(-Pd\), the term \(-sA\) is at
least \(-sa_0\), and \((k-t)B\ge-(t-.764)d\).

Combining (19), (26), and the multiplier-one inequality gives
\[
 C\ge\frac\pi2+u+c+(p-1)a_0+\frac12+\frac k2+
                   (\tfrac12-a_0)s-(P+t-.764)d.
\tag{27}
\]
On this whole angle interval, \(u\ge\sin u=s\). Also \(a_0<1.5\).
Consequently
\[
 u+(\tfrac12-a_0)s\ge(1.5-a_0)s\ge0,\qquad k/2>.382.
\]
Equation (27) therefore yields the angle-independent bound
\[
 C>\frac\pi2+c+(p-1)a_0+.882-(P+t-.764)d.
\tag{28}
\]
For the four exact tuples, these fixed expressions respectively exceed
\[
 .94936,\qquad .97496,\qquad .98240,\qquad .97477.
\tag{29}
\]
The weakest is the first; for it the comparison is already
\[
 1.570795-.53489-.66853(1.414575672)+.882
                    -.02541(.899214065110)>.94936.
\tag{30}
\]
For the other tuples, use the sign of \(P+t-.764\) when choosing
the corresponding endpoint from (5).

Thus all four positive-half primary branches also satisfy (2).
Together with Sections 2 and 3, this proves the entire sixteen-branch
theorem, including the common angle endpoint, both state-arc endpoints,
and every weak-separator tie.

