# Intermediate frame order with every low-EH and high-DE owner

## 1. The original mixed witnesses may be retained before alignment

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 p=\frac{50}{49},\quad S_0=2\sqrt{Q-1}-3,
 \quad K=\frac{847}{800}.
\tag{1}
\]
Retain the actual hard normal-sign necessary cycle at a common
circle ceiling \(q\le Q\), the true core, and a real frame interval
of length at most \(7/10\). The signed tangents are positive at
H,A,T and negative at G,B,D,E, with zero tangents allowed where
the original constraints allow them. All own-frame magnitudes
are nonnegative and sorted. Retain the original witnesses
\[
 HG,AB,TD\in\{0,2\},\qquad GA=0,\qquad BT=2,
 \qquad DE\in\{2,3\},\qquad EH\in\{0,1\}.
\tag{2}
\]
No outer error sign, A/B alignment, or frame order is assumed.
The E state need not be a radial boundary representative.

**Theorem.** Every such original system has
\[
                         \theta_G>\theta_T.
\tag{3}
\]
In particular, the original DE/EH owners need not first be
converted to DE3/EH1. This theorem precedes all non-E alignment
and does not invoke the later aligned mixed-owner reduction.
The hard GA0/BT2 owners and the normal G/T signs remain explicit
inputs; other quarter owners and intermediate signs are not
removed here.

The new ingredient is the following endpoint statement. For the
actual H,D,E coordinates, put
\[
 \delta=\theta_E-\theta_D,\quad
 \epsilon=\theta_H-\theta_E,\quad
 \alpha=\delta+\epsilon=\theta_H-\theta_D.
\]
Then every one of the four mixed-owner pairs in (2) satisfies
\[
                 b_H+b_D-p\alpha+S_0<2.
\tag{4}
\]
Sections 2--6 prove (4) using only H,D,E, their circles, their
normal signs, the true core, and their actual mixed inequalities.

## 2. One norm comparison for a rotated mixed error

For \(4/5\le\lambda\le2\), define
\[
 N_\lambda(d)=\sqrt{1+\lambda^2+2\lambda\sin d},\qquad
 \Psi_\lambda(d)=R N_\lambda(d)
       -\lambda\{\cos d+(\sin d)_+\}-p d.
\tag{5}
\]
We claim that, on the whole interval \(|d|\le7/10\),
\[
                  \Psi_\lambda(d)\le\Psi_\lambda(0),
\tag{6}
\]
strictly when \(d\ne0\).

For \(d=x>0\), the concave square-root tangent gives
\[
 R\{N_\lambda(x)-N_\lambda(0)\}
 \le c_\lambda\sin x,
 \qquad c_\lambda=\frac{R\lambda}{\sqrt{1+\lambda^2}}.
\]
The function \(c_\lambda\) is concave in positive \(\lambda\).
Its tangent at one, and \(Q<98/25\), give
\[
 c_\lambda\le\frac{R}{2\sqrt2}(1+\lambda)
                     <\frac7{10}(1+\lambda).
\]
Also \(\tan(x/2)<3/8\), from the degree-two lower cosine
at \(7/20\). Consequently
\[
\begin{aligned}
 \Psi_\lambda(x)-\Psi_\lambda(0)
 &\le\{c_\lambda-\lambda+\lambda\tan(x/2)\}\sin x-px\\
 &<\left(\frac7{10}+\frac3{40}\lambda\right)\sin x-px
 \le\left(\frac{17}{20}-p\right)x<0.
\end{aligned}
\tag{7}
\]

For \(d=-x<0\), it suffices to prove positivity of
\[
 G_\lambda(x)=R\left\{\sqrt{1+\lambda^2}
              -\sqrt{1+\lambda^2-2\lambda\sin x}\right\}
                   -\lambda(1-\cos x)-px.
\tag{8}
\]
For each fixed \(0<x\le7/10\), this is concave in
\(\lambda\in[4/5,2]\). Indeed, writing \(s=\sin x\),
\(c=\cos x\), \(n_0=\sqrt{1+\lambda^2}\), and
\(n_-=\sqrt{1+\lambda^2-2\lambda s}\),
\[
 \partial_\lambda^2G_\lambda
       =R\left(\frac1{n_0^3}-\frac{c^2}{n_-^3}\right)<0.
\tag{9}
\]
To check the sign, on this lambda interval
\(2\lambda/(1+\lambda^2)\ge4/5>s\), since
\(\sin(7/10)<13/20\). Thus \(n_-<c n_0\), which proves
(9). It is enough to prove (8) at the two lambda endpoints.

The Taylor inequality
\(1-\sqrt{1-z}\ge z/2+z^2/8\), for \(0\le z<1\), gives
\[
 R(n_0-n_-)\ge c_\lambda\sin x+d_\lambda\sin^2x,
 \qquad d_\lambda=\frac{R\lambda^2}{2(1+\lambda^2)^{3/2}}.
\tag{10}
\]
The following rational lower bounds follow by positive squaring:
\[
\begin{array}{c|cc}
 \lambda&c_\lambda&d_\lambda\\ \hline
 4/5&>123/100&>3/10\\
 2&>7/4&>7/20.
\end{array}
\tag{11}
\]
The two reserves for the squared c bounds are respectively
\(6207/410000\) and \(3499/50000\); the d bounds follow
from \(d_\lambda/c_\lambda=10/41\) and \(1/5\).

Use \(\sin x\ge x-x^3/6\), its positive square for
\(\sin^2x\), and
\(1-\cos x\le x^2/2-x^4/24+x^6/720\).
After dividing (8) by x, (10)--(11) give the two lower
polynomials
\[
\begin{aligned}
 P_{4/5}(x)
 &=\frac{1027}{4900}-\frac{x}{10}-\frac{41x^2}{200}
                         -\frac{x^3}{15}+\frac{13x^5}{1800},\\
 P_2(x)
 &=\frac{143}{196}-\frac{13x}{20}-\frac{7x^2}{24}
                         -\frac{x^3}{30}+\frac{x^5}{144}.
\end{aligned}
\tag{12}
\]
Drop the positive fifth-degree term and put \(x=7/10\)
in every negative term. On the entire interval,
\[
 P_{4/5}(x)\ge\frac{47849}{2940000}>0,
 \qquad P_2(x)\ge\frac{117837}{980000}>0.
\tag{13}
\]
Concavity in lambda proves (8) for every intermediate lambda,
and hence proves (6). This uses no subdivision of the angle
or lambda intervals.

## 3. Collect each actual endpoint circle once

Write shifted corners
\[
 X_i=a_i+1/2,\qquad Y_i=b_i+1/2,
 \qquad X_i^2+Y_i^2\le Q.
\]
The actual mixed inequalities are exactly
\[
\begin{array}{c|l}
 DE2&X_D\cos\delta+Y_D\sin\delta+Y_E
                   \ge1+\cos\delta+(\sin\delta)_+\\
 DE3&X_D+X_E\sin\delta+Y_E\cos\delta
                   \ge1+\cos\delta+(\sin\delta)_+\\
 EH0&X_H\cos\epsilon+Y_H\sin\epsilon-Y_E
                   \ge\cos\epsilon+(\sin\epsilon)_+\\
 EH1&X_H+X_E\sin\epsilon-Y_E\cos\epsilon
                   \ge1+(\sin\epsilon)_+.
\end{array}
\tag{14}
\]
For the endpoint objective
\[
                 \Phi=Y_H+Y_D-1-p(\delta+\epsilon),
\tag{15}
\]
add lambda times each nonnegative mixed-constraint margin.
At a primary endpoint, the collected corner force is
\((\lambda,1)\), of norm \(\sqrt{1+\lambda^2}\).
At a rotated endpoint with error d, it is
\((\lambda\cos d,1+\lambda\sin d)\), of norm
\(N_\lambda(d)\). Each support is at most R times that
norm, using that endpoint's actual circle once.

For DE2/EH0, the two E terms cancel exactly. Equations
(6), (14) give
\[
 \Phi\le\Psi_\lambda(\delta)+\Psi_\lambda(\epsilon)
                          -\lambda-1
       \le2R\sqrt{1+\lambda^2}-3\lambda-1.
\tag{16}
\]
Choose \(\lambda=7/6\). The square reserve
\[
 (6\cdot3041/1000)^2-85Q=\frac{22629}{250000}>0
\]
gives \(R\sqrt{1+\lambda^2}<3041/1000\). Since
\(S_0<52/125\),
\[
                 \Phi+S_0<\frac{999}{500}<2.
\tag{17}
\]
This proves (4) for the two rotated owners, without using
an E radial kind or coordinate bound beyond its displayed
normal sign.

For DE2/EH1, delete the rotated delta term with (6).
The exact remaining estimate is
\[
 \Phi\le2R\sqrt{1+\lambda^2}-3\lambda-1
                         +\lambda J_H(\epsilon)-p\epsilon,
\quad
 J_H(r)=X_E\sin r+Y_E(1-\cos r)-(\sin r)_+.
\tag{18}
\]
For DE3/EH0, delete the rotated epsilon term instead:
\[
 \Phi\le2R\sqrt{1+\lambda^2}-3\lambda-1
                         +\lambda J_D(\delta)-p\delta,
\quad
 J_D(r)=X_E\sin r+(1-Y_E)(1-\cos r)-(\sin r)_+.
\tag{19}
\]
These are algebraic comparisons of the original constraints.
They do not move an endpoint, preserve a hypothetical owner
at a new angle, or require a new E radial representative.

## 4. Bounds for the remaining primary error

We use the two already audited scalar families in Sections
3--6 of
[the primary-owner frame-order theorem](HAND_G5_GLOBAL_INTERMEDIATE_FRAME_ORDER.md).
Their estimates concern H,D,E alone; AB alignment and an
intermediate frame order are not inputs to those sections.
The bounds needed to apply them to (18)--(19) are recorded
explicitly here.

### 4.1 A nonnegative remaining error

For \(r=x\ge0\), since \(Y_E\ge1/2\), both remainders
in (18)--(19) are at most
\[
 J_E(x)=(X_E-1)\sin x+Y_E(1-\cos x).
\tag{20}
\]
Put \(k_0=\sqrt{Q-1/4}-1\). The restricted E-circle
support in Section 4.1 of the cited theorem gives
\[
 J_E(x)\le g(x):=k_0\sin x+\tfrac12(1-\cos x)
                                      \quad(0\le x\le1/2),
\tag{21}
\]
and
\[
 J_E(x)\le\frac{41}{40}x\quad(1/2\le x\le7/10).
\tag{22}
\]
For (21), the unrestricted support direction has transverse
corner \(R\sin(x/2)<1/2\), so the true lower transverse
floor \(Y_E=1/2\) is active. For (22), unrestricted circle
support gives \(2R\sin(x/2)-\sin x\), and the printed
Taylor comparison in that section gives the stated linear
upper bound. Both statements hold for every contained E
state, including a core state.

### 4.2 A negative remaining error

For \(r=-x<0\), true core avoidance gives \(X_E>K\).
The DE remainder immediately satisfies
\[
 J_D(-x)=-X_E\sin x+(1-Y_E)(1-\cos x)
               \le-K\sin x+\tfrac12(1-\cos x).
\tag{23}
\]
For the EH remainder, retain its actual EH1 witness at
\(\epsilon=-x\). It gives
\[
 a_H\ge\tfrac12+X_E\sin x+Y_E\cos x\ge1+b_E,
\]
where the last inequality follows from sorting and
\(\sin x\ge1-\cos x\). Hence \(b_E<83/200\).
For \(x\ge6/25\), in fact \(b_E<3/10\): if not,
\(a_H>1/2+K\sin x+(4/5)\cos x\). This last function
increases on \([3/25,7/10]\), and its degree-three sine
and degree-two cosine lower bounds at \(3/25\) exceed
\(283/200\) by \(149627/25000000>0\), a contradiction.
This is the same actual-EH estimate used in Section 3 of
the cited theorem.

Consequently both (18) and (19) obey
\[
 J_H(-x),J_D(-x)\le-K\sin x+d(1-\cos x),
\quad
 d=\begin{cases}
 183/200,&0\le x\le6/25,\\
 4/5,&6/25\le x\le7/10.
 \end{cases}
\tag{24}
\]
The bound for \(J_H\) is used only in its actual EH1 branch;
no EH1 witness is introduced in the DE3/EH0 branch.

## 5. The existing scalar certificates have admissible stress weights

If a remainder has upper bound j, put
\[
 X=\frac{3-j}{2},\qquad Y=\sqrt{Q-X^2}.
\]
Whenever \(\lambda=X/Y\in[4/5,2]\), the right sides of
(18)--(19) simplify to
\[
               2Y-1-pr,
\tag{25}
\]
because \(2R\sqrt{1+\lambda^2}-2\lambda X=2Y\).
The lambda range is essential: it is verified separately
for every use of (25).

For \(0\le r=x\le1/2\), take \(j=g(x)\). The bounds
proved in Section 5 of the cited theorem are
\[
 31/25\le X\le3/2,\qquad 0<Y<31/20.
\]
They give \(\lambda>4/5\); also \(Y>1\), so
\(\lambda<3/2<2\). Its whole-interval concavity certificate
proves precisely
\[
             2Y-1+S_0-px<2-\frac{27}{160000}<2.
\tag{26}
\]
Thus (4) follows on this entire range.

For \(1/2\le r=x\le7/10\), use (22) and the fixed
admissible weight \(\lambda=4/5\), without an optimizer.
The positive square reserve
\[
 (507/200)^2-Q(41/25)=\frac{4641}{10^6}>0
\]
gives \(R\sqrt{1+\lambda^2}<507/200\).
The bound for \(\Phi+S_0\) is decreasing in x, since
\(41/50-p<0\). At \(x=1/2\), it is less than
\[
 2\frac{507}{200}-\frac{17}{5}
       +\frac12\left(\frac{41}{50}-p\right)+\frac{52}{125}
                  =2-\frac{87}{6125}<2.
\tag{27}
\]

For \(r=-x\le0\), take the bound j in (24). Then
\[
 X=X_d(x)=\frac32+\frac K2\sin x-\frac d2(1-\cos x).
\tag{28}
\]
Here \(3/2\le X<7/4\). For the first d interval,
the upper bound follows already from
\(X\le3/2+(847/1600)(6/25)<7/4\); the lower bound
uses \(K>d\tan(x/2)\). For the second interval,
\[
 X=\frac{11}{10}+\frac25\cos x+\frac{847}{1600}\sin x
\]
is increasing, with derivative greater than \(877/6400\).
The degree-four upper cosine and degree-five upper sine at
\(7/10\) put it below \(7/4\) by the exact reserve
\(56774471/19200000000>0\).

In particular, \(\lambda=X/Y>4/5\), while
\[
                 4Q-5(7/4)^2=\frac{3499}{10000}>0
\]
gives \(\lambda<2\). Formula (25) is therefore valid.
Sections 3.1--3.2 of the cited theorem prove on both entire
d intervals that
\[
                 2Y-1+S_0+px<2.
\tag{29}
\]
Equations (26)--(29) prove (4) for each one-rotated pair.

For DE3/EH1, Sections 3--6 of that theorem already prove
(4) for every H,D,E frame position and either E tangent
sign. Their endpoint estimate is independent of the middle
path and can be used directly here. Together with (17),
this completes (4) for all four original mixed-owner pairs.

## 6. Join to the original middle path and zero charges

Suppose \(r=\theta_T-\theta_G\ge0\). The already proved
[arbitrary-frame middle bound](HAND_G5_REVERSED_INTERMEDIATE_MIDDLE_PATH_BOUND.md)
gives
\[
                         b_G+b_T\le S_0+\frac{149}{240}r.
\]
Set \(h=\theta_G-\theta_H\), \(k=\theta_D-\theta_T\),
so \(\theta_D-\theta_H=r+h+k=-\alpha\).
The actual all-sign zero charges on HG and TD, exactly as
collected in Section 2 of the primary-owner frame-order
theorem, imply
\[
                      2\le b_H+b_D+S_0-p\alpha.
\tag{30}
\]
This deduction uses neither DE nor EH, and uses no signs
of h or k. It retains the actual original b_G,b_T and
both original transverse witnesses. Equation (4) contradicts
(30), proving (3).

The result includes all weak original contacts and every
mixed-owner tie. No endpoint was moved in this proof, and
no radial-boundary assumption was added. The only new
comparison is the fixed family (6), certified on its full
lambda and angle intervals by concavity and the two printed
polynomials. No state or angle mesh, numerical acceptance
premise, Lean compilation, or CI result is used.
