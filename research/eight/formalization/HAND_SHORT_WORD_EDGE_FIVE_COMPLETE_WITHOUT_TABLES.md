# The remaining outer role-5 contacts of 0010111, without tables

All terminating decimals are exact rationals. At
\(Q=9789/2500\), every outer/outer quarter-one pair on edge 5 of
the short wrong word satisfies its required corrected-cost inequality
\(C>.89765\), provided one of the four retained original axes separates
and \(|\phi-\pi/2|\le.7\).

The opposite-sign \((-,+)\) case, including all four original axes, was
proved in
[HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md](HAND_SHORT_WORD_OPPOSITE_EDGE_FIVE_WITHOUT_TABLES.md).
This note proves its entire 24-branch complement: the other three sign
pairs, all four axes, and both angle halves. Thus these two notes close
the full outer/outer quarter-one role-5 family.

The bounds come from fixed circle supports and whole-angle
monotonicity or concavity. No angle table, coefficient-status appendix,
or subdivision of a state domain is used.

## 1. Geometry and the four same-sign normalizations

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12.
\]
An outer state satisfies
\[
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\qquad
 0\le b\le d,\qquad
 -a'(b)=\frac{b+\tfrac12}{a+\tfrac12}\in(0,1].
\tag{1}
\]
We use the elementary bounds
\[
 1.414575671<a_0<1.414575672,\quad
 .899214065109<d<.899214065110,\quad
 R<1.978788,
\tag{2}
\]
as well as
\[
 .644<\sin(.7)<.645,\qquad
 .764<\cos(.7)<.765,\qquad
 \sqrt{\tfrac14+(a_0-\tfrac12)^2}<1.043.
\tag{3}
\]
They follow by squaring and the alternating trigonometric series.

The same-sign original branches reduce, by exact reflection and
reversal for target-owned axes, to four normalized coefficient tuples:
\[
\begin{aligned}
 {\cal A}_0&=(c,p,q,P,t)=(.23152,0,.86884,.21826,.83472),\\
 {\cal A}_1&=(.48239,-.18602,.80996,.20967,.83048),\\
 {\cal B}_0&=(.48239,-.20967,.83048,.18602,.80996),\\
 {\cal B}_1&=(.23152,-.21826,.83472,0,.86884).
\end{aligned}
\tag{4}
\]
An \({\cal A}\) tuple has normalized signs \((+,+)\); a
\({\cal B}\) tuple has signs \((-,-)\). Write that common sign as
\(\sigma\), so the cost is
\[
 C=\phi+c+pa+\sigma qb-PA-\sigma tB.
\tag{5}
\]
Each tuple is used with both source axis 1 and source axis 4:

* \({\cal A}_0\) is original \(++\), axes 1 and 4.
* \({\cal A}_1\) is original \(--\), axes 3 and 2.
* \({\cal B}_0\) is original \(--\), axes 1 and 4.
* \({\cal B}_1\) is original \(++\), axes 3 and 2.

This accounts for every same-sign original axis, including ties.

Set
\[
 \phi=\pi/2+r u,\quad r\in\{-1,1\},\quad
 0\le u\le.7,\quad s=\sin u,\quad k=\cos u,\quad
 W=\frac{1+k+s}{2}.
\]
The two normalized separating inequalities are
\[
 \sigma b+Ak+\sigma rBs\ge W
 \quad\text{and}\quad
 a+rAs-\sigma Bk\ge W.
\tag{6}
\]

### The support rules used below

For all real \(X,Y\), a whole-circle lower support is
\[
 Xa+Yb\ge-\frac{X+Y}{2}-R\sqrt{X^2+Y^2}.
\tag{7}
\]
If \(X\le0,\ Y\ge0\), the actual outer-arc minimum is \(Xa_0\):
its derivative in \(b\) is nonnegative. If \(Y\ge0\), for arbitrary
\(X\), the minimum is at the axial or diagonal endpoint. Indeed it
increases for \(X<0\), and is concave for \(X\ge0\). Thus the common
endpoint lower bound
\[
 \min\{Xa_0,(X+Y)d\}
\tag{8}
\]
is valid whenever \(Y\ge0\).

Subtracting a nonnegative multiplier \(\lambda\) times a separator
margin gives
\[
 C\ge\phi+c+\lambda W+m(X_s,Y_s)+m(X,Y),
\tag{9}
\]
where \(m\) may be any valid lower support, and
\[
\begin{array}{c|cc|cc}
 &X_s&Y_s&X&Y\\ \hline
 1&p&\sigma(q-\lambda)&-P-\lambda k&
                          \sigma(-r\lambda s-t)\\
 4&p-\lambda&\sigma q&-P-r\lambda s&
                          \sigma(\lambda k-t).
\end{array}
\tag{10}
\]
This is an exact consequence of the original weak separating
inequality.

## 2. The positive-to-negative sign pair

For original signs \((+,-)\), the corrected cost is
\[
 C=\phi+.21108+.86884b-.18602A+.80996B.
\tag{11}
\]
It is at least
\[
 \phi+.21108-.18602a_0+.80996(b+B).
\tag{12}
\]
If \(\phi\ge\pi/2\), this already exceeds \(1.518\).

Suppose \(\pi/2-.7\le\phi\le\pi/2\). Each of the four retained axis
projections is at most
\[
 a_0\sin\phi+b+B.
\tag{13}
\]
For the secondary projections this is immediate. A primary projection
is at most \(a_0-d\cos\phi+b+B\), which is no larger than (13), since
\[
 \frac{1-\sin\phi}{\cos\phi}
 =\tan\left(\frac{\pi/2-\phi}{2}\right)<\frac38<\frac d{a_0}
\]
away from the endpoint \(\phi=\pi/2\); at that endpoint the assertion
holds directly. Therefore separation on any retained axis implies
\[
 b+B\ge
 \frac{1+\sin\phi+\cos\phi}{2}-a_0\sin\phi.
\tag{14}
\]
Combining (12) and (14), define the lower scalar
\[
 F(\phi)=\phi+.21108-.18602a_0+
 .80996\left[\frac12+\frac12\cos\phi+
                        \left(\frac12-a_0\right)\sin\phi\right].
\]
Its derivative satisfies
\[
 F'(\phi)\ge
 1-.80996\sqrt{\tfrac14+(a_0-\tfrac12)^2}
 >1-.80996(1.043)>0.
\tag{15}
\]
At the left endpoint, (2), the alternating series at \(.7\), and
\(\pi/2>1.570795\) give \(F(\pi/2-.7)>.9180\).
This proves all eight branches of this sign pair.

## 3. The A tuples: source-secondary axes

Take axis 1 and a tuple \({\cal A}_i\). For any source lower support
\(S\), (7)--(10) give
\[
\begin{split}
 C\ge F_r(u):={}&\frac\pi2+r u+c+S+\frac{\lambda+P+t}{2}
       +\lambda k+\frac{1+r}{2}\lambda s-RN_r(u),\\
 N_r(u)^2={}&P^2+t^2+\lambda^2+2\lambda(Pk+rt s).
\end{split}
\tag{16}
\]

### 3.1 The upper half

Choose \(\lambda=.75\). Here \(p\le0\) and \(q-\lambda>0\), so
\(S=pa_0\) is the exact source minimum.

The numerator \(tk-Ps\) is positive and decreasing on \(0\le u\le.7\),
while \(N_+(u)\) increases. Hence
\[
 \frac{tk-Ps}{N_+(u)}
 \le\frac{t}{N_+(0)}<.663.
\]
For the last bound, \(t\le.83472\) and \(N_+(0)>1.26\).
Consequently
\[
 F_+'=1+\lambda(k-s)
           -R\lambda\frac{tk-Ps}{N_+(u)}
 >1+.75(.119)-1.978788(.75)(.663)>.10.
\tag{17}
\]
The two exact initial values from (16) exceed \(.9241\) and \(.9238\),
respectively. This proves both whole upper halves.

### 3.2 The lower half: a useful common concavity identity

For \({\cal A}_0\), choose \(\lambda=.86884=q\), so \(S=0\).
For \({\cal A}_1\), choose \(\lambda=.878\) and use
\[
 S=-\frac{p+q-\lambda}{2}
       -R\sqrt{p^2+(q-\lambda)^2}.
\tag{18}
\]
Let \(N=N_-\) and \(N_0=N(0)\). Both choices satisfy
\[
 N_0<1.372,\qquad .645N_0^2<2\lambda t,\qquad
 RN_0<4\lambda.
\tag{19}
\]
These comparisons follow already from
\(\lambda\ge.86884,\ t\ge.83048\), and the displayed bound on \(N_0\).

The exact identity
\[
 N(u)^2-N_0^2k^2
 =N_0^2s^2-2\lambda P(1-k)-2\lambda ts
\tag{20}
\]
therefore proves \(N(u)\le N_0k\) on the whole lower half.
Also, differentiating its squared norm gives
\[
 N''+\frac N4=
 \frac{(P^2+t^2-\lambda^2)^2}{4N^3}\ge0.
\tag{21}
\]
It follows from (16) that
\[
 F_-''=-\lambda k-RN''
 \le-\lambda k+\frac{RN}{4}
 \le k\left(-\lambda+\frac{RN_0}{4}\right)<0.
\tag{22}
\]
Thus each lower scalar is concave on its entire angle domain, and
only its two endpoints matter.

At zero, their respective values exceed \(.9199\) and \(.9174\).
At \(.7\), both exceed \(.8981\). These are four fixed comparisons
in the explicit radical expression (16); for the latter pair, outward
rational evaluation gives respectively
\[
 \frac{1122638465184619}{1250000000000000}<F_-(.7),\qquad
 \frac{28065845112673}{31250000000000}<F_-(.7).
\tag{23}
\]
For these exact fractions use \(\pi/2>1.570795,\ R<1.978788\),
\[
 .64421768723<\sin(.7)<.64421768724,\qquad
 .76484218728<\cos(.7)<.76484218729,
\]
and the norm upper bounds \(.924626445,\ .920144087\), respectively.
The source radical in (18) is less than \(.198072921\).
The trigonometric bounds follow by alternating series, and the three
radical bounds follow by squaring in the explicitly displayed formulas.
Equations (20)--(22),
rather than any coefficient or angle table, extend the endpoint bounds
over the whole intervals.

## 4. The B tuples: source-secondary axes

Take axis 1 and a tuple \({\cal B}_i\), so \(\sigma=-1\). Choose
\(\lambda=1\). The source coefficients are \(p<0,\ 1-q>0\).
The target coefficients satisfy
\[
 X=-P-k<0,\qquad Y=t+r s>0,
\]
including the lower half because \(t>.809\) and \(s<.645\).
Both supports are therefore axial. Formula (9) becomes
\[
 C\ge H_r(u):=\frac\pi2+r u+c+(p-P)a_0+\frac12
                      +(\tfrac12-a_0)k+\frac12s.
\tag{24}
\]
For \(r=1\), its derivative is positive.
For \(r=-1\),
\[
 H_-'=-1+(a_0-\tfrac12)s+\tfrac12k<0.
\tag{25}
\]
To prove the last inequality throughout the half, the positive expression
being subtracted from 1 increases on \([0,.7]\), since
\((a_0-\tfrac12)k-\tfrac12s>0\); its value at \(.7\) is less than
\(.914575672(.645)+.5(.765)<.973\).

The two initial values \(H_+(0)=H_-(0)\) exceed \(1.0788\).
The two terminal values \(H_-(.7)\) exceed \(.9160\).
These endpoint bounds and (25) prove all four corresponding branches.

## 5. The B tuples: source-primary axes

Take axis 4, again with a tuple \({\cal B}_i\), and choose
\(\lambda=.8\). The source circle support is the constant
\[
 S=\frac{\lambda-p+q}{2}
           -R\sqrt{(\lambda-p)^2+q^2}.
\tag{26}
\]
The target secondary coefficient is \(Y=t-\lambda k>0\).

For \(r=1\), also \(X=-P-\lambda s\le0\), so its support is axial:
\[
 C\ge H_A^+(u):=
 \frac\pi2+u+c+S-Pa_0+\frac\lambda2+
                 \frac\lambda2k+\lambda(\tfrac12-a_0)s.
\tag{27}
\]
Its derivative is greater than
\[
 1-\lambda\sqrt{\tfrac14+(a_0-\tfrac12)^2}
 >1-.8(1.043)>0.
\tag{28}
\]
The two initial values exceed \(.9231\) and \(.9234\).

For \(r=-1\), rule (8) gives the minimum of two endpoint scalars:
\[
\begin{aligned}
 H_A^-(u)&=\frac\pi2-u+c+S-Pa_0+\frac\lambda2+
                   \frac\lambda2k+\lambda(\tfrac12+a_0)s,\\
 H_D^-(u)&=\frac\pi2-u+c+S+(t-P)d+\frac\lambda2+
                   \lambda(\tfrac12-d)k+\lambda(\tfrac12+d)s.
\end{aligned}
\tag{29}
\]
The axial scalar is strictly concave, so its minimum is at 0 or
\(.7\). Its zero values are those just stated; its \(.7\) values
exceed \(1.1158\) and \(1.1160\).

The diagonal scalar is increasing:
\[
 (H_D^-)'=-1+\lambda\{(d-\tfrac12)s+(d+\tfrac12)k\}>0.
\tag{30}
\]
The expression in braces is positive and concave, and after multiplying
by \(\lambda\), its endpoint values both exceed \(1.06\).
At zero the diagonal support is no smaller than the axial support,
since \(X=-P\le0,\ Y=t-\lambda>0\). Thus (29) exceeds \(.9231\)
on both endpoint choices throughout the half.

## 6. The A tuples: source-primary axes

Take axis 4 and a tuple \({\cal A}_i\).

For \(r=1\), use \(\lambda=.8\). The source coefficients
\(p-\lambda<0,\ q>0\) have the exact axial minimum
\(S=(p-\lambda)a_0\). The target whole-circle support gives
\[
 C\ge G(u):=\frac\pi2+u+c+S+\frac{\lambda+P+t}{2}
                  +\lambda s-RN(u),
\]
\[
 N(u)^2=P^2+t^2+\lambda^2+
                    2\lambda(Ps-tk).
\tag{31}
\]
The Cauchy inequality
\[
 |Pk+ts|\le N(u)
\]
follows by taking the dot product of the unit vector \((k,s)\)
with \((P+\lambda s,t-\lambda k)\). Hence
\[
 G'\ge1+\lambda k-R\lambda
 >1-.8(1.978788-.764)>0.
\tag{32}
\]
The two initial values exceed \(1.1598\) and \(1.1592\).

For \(r=-1\), feasibility already forces \(u<.226\). Indeed
\(As+Bk\) increases with \(B\), so its minimum is \(a_0s\).
The separator would otherwise require
\[
 a_0(1-\sin u)\ge W.
\tag{33}
\]
The left side minus right side is strictly decreasing and is negative
at \(.226\), by (2) and the alternating trigonometric series.
Thus on every feasible angle \(k>.974,\ s<.225\).

Use \(\lambda=1\). The source minimum remains axial, now
\(S=(p-1)a_0\). The target has
\[
 X=-P+s,\qquad Y=k-t>0,
\]
so rule (8) gives two endpoint lower bounds:
\[
\begin{aligned}
 G_A(u)&=\frac\pi2-u+c+(p-1-P)a_0+\frac12+
                     \frac12k+(\tfrac12+a_0)s,\\
 G_D(u)&=\frac\pi2-u+c+(p-1)a_0-(P+t)d+\frac12+
                     (\tfrac12+d)(k+s).
\end{aligned}
\tag{34}
\]
Both increase on the entire feasible range:
\[
\begin{aligned}
 G_A'&=-1-\tfrac12s+(\tfrac12+a_0)k
       >-1-.5(.225)+1.914(.974)>0,\\
 G_D'&=-1+(\tfrac12+d)(k-s)
       >-1+1.399(.974-.225)>0.
\end{aligned}
\tag{35}
\]
At zero, the diagonal value is no smaller than the axial one because
\(X=-P<0,\ Y=1-t>0\). The two axial initial values exceed \(1.0788\).
This completes both remaining lower-half primary cases.

## 7. Completion and an immediate role-4 corollary

Sections 3--6 cover all sixteen same-sign role-5 branches, and Section 2
covers the eight \((+,-)\) branches. Together with the previously
proved eight \((-,+)\) branches, the full role-5 outer/outer
quarter-one family is proved, using the original role labels and every
retained owner axis.

The same elementary label argument also closes every role-4 outer
quarter-one branch with signs \((+,-)\). Its cost is
\[
 C_4=\phi-.23285+.71553b+.20967A+.83048B.
\]
The target expression \(.20967A+.83048B\) increases with \(B\), by
(1), so it is at least \(.20967a_0\). Therefore, throughout both halves,
\[
 C_4\ge\frac\pi2-.7-.23285+.20967a_0>.9345>.89765.
\tag{36}
\]
This corollary requires no separator beyond those already assumed in
the word's pair interface.

