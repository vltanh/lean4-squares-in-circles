# A reversed intermediate span cannot retain two nonnegative outer errors

## 1. Exact scope

Put
\[
 Q=\frac{9789}{2500},\qquad
 W(z)=\frac{1+\cos z+|\sin z|}{2}.
\]
Work with sorted own-frame coordinates \(a_i\ge b_i\ge0\) at
H, G, A, B, T, D, and a possibly signed E tangent
\(a_E\ge|b_E|\). Each actual shifted corner obeys
\[
 (a_i+\tfrac12)^2+(b_i+\tfrac12)^2\le Q,
 \qquad
 (a_E+\tfrac12)^2+(|b_E|+\tfrac12)^2\le Q.
\tag{1}
\]
Retain the true central exclusion and a common real frame interval
of length at most \(7/10\). In particular,
\[
 a_i>\frac{447}{800},\qquad a_i<\frac{283}{200},
 \qquad b_i<\frac9{10}.
\tag{2}
\]
The absolute E tangent obeys the same last bound. The first bound
follows from \(a_i\ge1/2+1/(12\sqrt2)\).

Assume the actual A and B frames agree and their transverse sum is
exact:
\[
 \theta_A=\theta_B=\rho,\qquad b_A+b_B=1.
\tag{3}
\]
Keep the hard GA0 and BT2 inequalities, either original transverse
owner on HG and TD, and the two displayed E inequalities:
\[
\begin{aligned}
 a_A\cos(\theta_G-\rho)-b_A\sin(\theta_G-\rho)-b_G
     &\ge W(\theta_G-\rho),\\
 a_B\cos(\rho-\theta_T)-b_B\sin(\rho-\theta_T)-b_T
     &\ge W(\rho-\theta_T),\\
 a_D+a_E\sin\delta+b_E\cos\delta&\ge W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon&\ge W(\epsilon),
\end{aligned}
\tag{4}
\]
where \(\delta=\theta_E-\theta_D\) and
\(\epsilon=\theta_H-\theta_E\).

**Theorem.** No such system can also satisfy
\[
             \theta_H\le\theta_G\le\theta_T\le\theta_D.
\tag{5}
\]

Thus, after the exact AB alignment (3), a reversed intermediate
order cannot have both remaining outer errors nonnegative. The
theorem makes no assumption on the location of the common AB frame
or the E frame. It also allows either sign of the E tangent.
It does not claim that arbitrary AB frames have already been aligned
when \(\theta_G<\theta_T\).

## 2. The middle pair costs at most one sine term

Write
\[
 r=\theta_T-\theta_G,\quad h=\theta_G-\theta_H,
 \quad k=\theta_D-\theta_T,\quad v=r+h+k=\theta_D-\theta_H.
\tag{6}
\]
Under (5), all four are nonnegative and \(v\le7/10\).
Set
\[
 R_1=\sqrt{Q-1},\quad S_0=2R_1-3,
 \quad k_0=\sqrt{Q-1/4}-1,
 \quad g(x)=k_0\sin x+\tfrac12(1-\cos x).
\tag{7}
\]
The elementary rational bounds used below are
\[
 \frac9{10}<k_0<\frac{183}{200},\qquad
 S_0<\frac{52}{125}.
\tag{8}
\]

Put \(z=\theta_G-\rho\), \(w=\rho-\theta_T\), so
\(z+w=-r\). Rearranging the first two inequalities in (4), and
discarding the nonpositive terms
\(-(a_A-1/2)(1-\cos z)\) and
\(-(a_B-1/2)(1-\cos w)\), gives
\[
 b_G+b_T\le a_A+a_B-2+\mathcal S,
\tag{9}
\]
where a nonnegative argument x contributes
\(-(b+1/2)\sin x\) to \(\mathcal S\), and a negative
argument \(-x\) contributes \((b-1/2)\sin x\).

Because (2)--(3) imply \(1/10<b_A,b_B<9/10\),
\[
                         \mathcal S\le\frac25\sin r.
\tag{10}
\]
Here is a direct proof covering every possible location of \(\rho\).
If \(z,w\le0\), their absolute values sum to r. At most one of
\(b_A-1/2,b_B-1/2\) is positive; its value is less than \(2/5\)
and its sine is at most \(\sin r\). If \(z\ge0\), then
\(w=-(r+z)\), and
\[
\begin{aligned}
 \mathcal S
 &= (\tfrac12-b_A)\sin(r+z)-(\tfrac12+b_A)\sin z. 
\end{aligned}
\]
For \(b_A\ge1/2\) this is nonpositive. Otherwise expanding
\(\sin(r+z)\) leaves a sine-z coefficient
\((1/2-b_A)\cos r-(1/2+b_A)<0\), so the expression is at
most \((1/2-b_A)\sin r\cos z\le(2/5)\sin r\).
The case \(w\ge0\) is the same calculation with A and B exchanged.

The concavity of \(b\mapsto\sqrt{Q-(b+1/2)^2}-1/2\),
together with (3), gives
\(a_A+a_B\le2\sqrt{Q-1}-1\). Consequently
\[
                 b_G+b_T\le S_0+\frac25\sin r.
\tag{11}
\]

## 3. Both outer owners give the same total cost

For HG0 the inequality is
\(b_H+a_G\sin h+b_G\cos h\ge W(h)\); for HG2 it is
\(b_G+a_H\sin h+b_H\cos h\ge W(h)\).
Either one, using the actual primary upper bound
\(a\le\sqrt{Q-1/4}-1/2\) and nonnegative tangents, implies
\[
                         b_H+b_G\ge1-g(h).
\tag{12}
\]
Both TD owners similarly give \(b_T+b_D\ge1-g(k)\).

For \(x,y\ge0\), \(x+y\le7/10\), the exact identity
\[
\begin{aligned}
 g(x+y)-g(x)-g(y)
 =4\sin(x/2)\sin(y/2)
 \left\{\tfrac12\cos((x+y)/2)-k_0\sin((x+y)/2)\right\}
\end{aligned}
\tag{13}
\]
is nonnegative. Indeed the braced expression exceeds
\[
 \frac12\frac{15}{16}-\frac{183}{200}\frac7{20}
                      =\frac{297}{2000}>0.
\]
Also \((2/5)\sin r\le g(r)\). Adding (11)--(12) and
applying (13) twice therefore gives the necessary inequality
\[
                      2\le b_H+b_D+S_0+g(v).
\tag{14}
\]

## 4. The E pair forces the opposite primary sum

This step uses only the last two inequalities of (4), their two
endpoint circles, and the actual E bounds. If \(b_E<0\), interchange
\(a_H,a_D\) and \(\epsilon,\delta\), and replace \(b_E\) by
\(-b_E\). This exchanges those two inequalities exactly. Their sum,
\(\delta+\epsilon=-v\), and the common frame-span restriction
are unchanged. Thus for this symmetric primary-sum estimate we may
write \(b_E\ge0\).

Put
\[
 \omega=v/2,\quad c=\cos\omega,\quad s=\sin\omega,
 \quad \zeta=(\delta-\epsilon)/2.
\]
Then
\(\delta=-\omega+\zeta\),
\(\epsilon=-\omega-\zeta\), and
\(|\zeta|\le7/10-\omega\). The sum of the E inequalities reads
\[
\begin{aligned}
 a_H+a_D\ge C(\zeta)
 :=W(\delta)+W(\epsilon)
       -a_E(\sin\delta+\sin\epsilon)
       -b_E(\cos\delta-\cos\epsilon).
\end{aligned}
\tag{15}
\]
In the central interval \(|\zeta|\le\omega\),
\[
 C(\zeta)=1+\{c+2s(a_E+\tfrac12)\}\cos\zeta
                                      -2sb_E\sin\zeta.
\tag{16}
\]
For \(\eta=|\zeta|\ge\omega\),
\[
 C(\zeta)=1+(c+2sa_E)\cos\eta
                 +(c-\operatorname{sgn}(\zeta)2sb_E)\sin\eta.
\tag{17}
\]

### 4.1 An E frame outside the endpoint interval cannot lower its sum

Let \(M=(\eta+\omega)/2\), so
\(\omega\le M\le7/20\). The difference between (17) and
its value at the corresponding endpoint \(\zeta=\pm\omega\)
is \(2\sin((\eta-\omega)/2)\) times
\[
\begin{aligned}
 D_-&=c(\cos M-\sin M)+2s(b_E\cos M-a_E\sin M)
                                      &&(\zeta<0),\\
 D_+&=c(\cos M-\sin M)-2s(b_E\cos M+a_E\sin M)
                                      &&(\zeta>0).
\end{aligned}
\tag{18}
\]
Use
\(\cos M>15/16\), \(\sin M\le7/20\),
\(\tan\omega<3/8\), and \(a_E<283/200\). Then
\[
 \frac{D_-}{c}
 >\frac{47}{80}-2\frac{283}{200}\frac38\frac7{20}
 =\frac{3457}{16000}>0.
\tag{19}
\]
For \(\zeta>0\), the actual EH inequality has
\(\epsilon=-2M\). It implies
\[
 a_E\sin(2M)+b_E\cos(2M)<\frac{83}{200},
\tag{20}
\]
because \(a_H<283/200\) and \(\sin(2M)+\cos(2M)\ge1\).
The function \(a_E\sin u+b_E\cos u\) is increasing on
\([M,2M]\): sorting gives
\(a_E\cos u-b_E\sin u\ge a_E(\cos u-\sin u)>0\).
Thus its value at M also satisfies (20), and
\[
 \frac{D_+}{c}
 >\frac{47}{80}-\frac{83}{100}\frac38
 =\frac{221}{800}>0.
\tag{21}
\]
The elementary bounds in (19)--(21) follow already from
\(\cos(7/20)\ge1-(7/20)^2/2>15/16\) and
\((3/8)(1-(7/20)^2/2)>7/20\).

### 4.2 The two central endpoints

For \(-\omega\le\zeta\le0\), (16) gives
\[
 C(\zeta)\ge2+(a_E+\tfrac12)\sin v
                                      -\tfrac12(1-\cos v).
\tag{22}
\]
For \(0\le\zeta\le\omega\), (16) is concave:
its nonconstant part is positive, since \(a_E\ge b_E\) and
\(\cos\zeta>\sin\zeta\). Its smaller endpoint is
\(\zeta=\omega\), because the difference between its value at
zero and at \(\omega\) is
\(\{c+2s(a_E+1/2)\}(1-c)+2s^2b_E\ge0\). Hence
\[
 C(\zeta)\ge2+(a_E+\tfrac12)\sin v
                                  -(\tfrac12+b_E)(1-\cos v).
\tag{23}
\]
Equations (19)--(21) extend these same bounds to the corresponding
outside intervals.

Whenever \(\zeta\ge0\), write
\(u=-\epsilon=\omega+\zeta\ge0\). Sorting and
\(\sin u\ge1-\cos u\) give, from EH,
\[
 a_H\ge\tfrac12+(a_E+\tfrac12)\sin u
                         +(b_E+\tfrac12)\cos u\ge1+b_E.
\tag{24}
\]
Consequently \(b_E<83/200\).

If moreover \(v\ge6/25\), then \(u\ge3/25\).
Suppose \(b_E\ge3/10\), and put \(K=847/800\).
The right side of (24) would exceed
\(1/2+K\sin u+(4/5)\cos u\). This function increases on
\([3/25,7/10]\), since its derivative exceeds
\[
 K\frac34-\frac45\frac{13}{20}=\frac{877}{3200}>0.
\]
At \(u=3/25\), its degree-three sine and degree-two cosine
lower bounds exceed \(283/200\) by exactly
\[
                         \frac{149627}{25000000}>0.
\tag{25}
\]
This contradicts (2), and proves \(b_E<3/10\) in this sector.

Combining (15), (22)--(25), and \(a_E+1/2>K\) proves
the following bound for every E frame and either E sign:
\[
 \boxed{
 a_H+a_D\ge2+K\sin v-d(1-\cos v),\quad
 d=\begin{cases}
  183/200,&0\le v\le6/25,\\
  4/5,&6/25\le v\le7/10.
 \end{cases}}
\tag{26}
\]
At the common endpoint either displayed bound may be used.

## 5. One scalar contradiction on each of two intrinsic ranges

By the two actual H and D circles and the concavity of
\(x\mapsto\sqrt{Q-x^2}\), (26) gives
\[
 b_H+b_D\le2\sqrt{Q-X_d(v)^2}-1,
 \qquad X_d(v)=\frac32+\frac K2\sin v-\frac d2(1-\cos v).
\tag{27}
\]
Thus (14) would require
\[
 F_d(v):=2\sqrt{Q-X_d(v)^2}-1+S_0+g(v)\ge2.
\tag{28}
\]
We prove a strict upper bound below 2 throughout each range.

### 5.1 The interval \(0\le v\le6/25\)

Put \(Y_0=\sqrt{Q-9/4}\), \(B_0=(3/2)/Y_0\).
Direct squaring gives
\[
 Y_0<\frac{1291}{1000},\qquad
 \frac{29}{25}<B_0<\frac76.
\tag{29}
\]
The tangent line to \(\sqrt{Q-X^2}\) at \(X=3/2\)
gives, for \(d=183/200\),
\[
 F_d(v)\le F_d(0)+(k_0-B_0K)\sin v
                           +(\tfrac12+B_0d)(1-\cos v).
\tag{30}
\]
The sine coefficient is less than \(-6263/20000\); the other
coefficient is less than \(627/400\). Also
\(\tan(v/2)<1/8\), since
\((1/8)(1-(3/25)^2/2)-3/25=41/10000>0\).
For \(v>0\), the increment in (30) is therefore less than
\[
 \left(-\frac{6263}{20000}+\frac{627}{400}\frac18\right)\sin v
                     =-\frac{9377}{80000}\sin v<0.
\]
Finally (8) and (29) give
\[
 F_d(0)=2Y_0-1+S_0<\frac{999}{500}<2.
\tag{31}
\]
This also covers \(v=0\).

### 5.2 The interval \(6/25\le v\le7/10\)

Here \(d=4/5\). Write
\[
 X=A+B\cos v+C\sin v,
 \quad A=\frac{11}{10},\quad B=\frac25,
 \quad C=\frac{847}{1600},\quad Y=\sqrt{Q-X^2}.
\tag{32}
\]
The derivative \(X'=C\cos v-B\sin v\) exceeds
\(877/6400>0\). The degree-three sine and degree-two cosine
lower bounds at \(6/25\) give
\[
 X>\frac{161}{100},\qquad
 X(6/25)-\frac{161}{100}>\frac{53879}{12500000}.
\tag{33}
\]
Also \(X\le A+\sqrt{B^2+C^2}<9/5<\sqrt Q\), so
all radicands are positive, and (33) gives \(Y<6/5\).

Define the single polynomial
\[
 N(X)=X(X-A)(Q-X^2)-Q\{B^2+C^2-(X-A)^2\}.
\tag{34}
\]
Direct differentiation gives the useful identity
\[
 N'(X)=(4X-3A)(Q-X^2)>0.
\tag{35}
\]
At the left comparison point,
\[
 N(161/100)=\frac{2440818723}{6400000000}
                  >\frac{19}{50}.
\tag{36}
\]
Differentiating (28) twice and using
\((X')^2=B^2+C^2-(X-A)^2\) gives
\[
\begin{aligned}
 F_d''(v)
 &=\frac{2N(X)}{Y^3}+\frac12\cos v-k_0\sin v\\
 &>\frac{2(19/50)}{(6/5)^3}+\frac38
                         -\frac{183}{200}\frac{13}{20}
   =\frac{23767}{108000}>0.
\end{aligned}
\tag{37}
\]
Thus the maximum of \(F_d\) on this entire interval is at an
endpoint. No subdivision of the interval is used.

At \(v=6/25\), (33) gives \(Y<1151/1000\), while
\(g(v)<117/500\). Consequently
\[
 F_d(6/25)
 <2\frac{1151}{1000}-1+\frac{52}{125}+\frac{117}{500}
 =\frac{244}{125}<2.
\tag{38}
\]
At \(v=7/10\), alternating Taylor bounds give
\[
 \frac{161}{250}<\sin v<\frac{129}{200},
 \qquad \cos v>\frac{191}{250}.
\tag{39}
\]
They imply \(X>873/500\), \(Y<233/250\), and
\(g(v)<28327/40000\). Thus
\[
 F_d(7/10)
 <2\frac{233}{250}-1+\frac{52}{125}+\frac{28327}{40000}
 =\frac{79527}{40000}
 =2-\frac{473}{40000}<2.
\tag{40}
\]
For explicit square checks in (38)--(40), the positive reserves are
\[
 (1151/1000)^2-(Q-(161/100)^2)=\frac{1301}{10^6},
 \qquad
 (233/250)^2-(Q-(873/500)^2)=\frac{77}{50000}.
\]
The lower cosine of degree six, lower sine of degree seven, and
upper sine of degree five prove (39) directly.

Equations (31), (37)--(40) contradict (28) in every case. This proves
the theorem, including all weak original contacts and endpoint
coincidences. The proof consists of exact supports, one symmetric
two-endpoint estimate for E, and two whole-interval scalar arguments.
No numerical acceptance premise, state or angle mesh, Lean
compilation, or CI is used.
