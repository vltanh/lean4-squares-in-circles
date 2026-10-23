# The hard normal-sign class has strictly ordered intermediate frames

## 1. No frame-order hypothesis

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 R=\sqrt Q,\quad R_1=\sqrt{Q-1},\quad S_0=2R_1-3,
 \quad k_0=\sqrt{Q-1/4}-1.
\tag{1}
\]
Work with the actual hard normal-sign necessary cycle at
\(q\le Q\): nonnegative sorted H,G,A,B,T,D magnitudes, actual
corner circles, the true core, and real frames of total spread
at most \(7/10\). The E tangent may have either sign, with
its actual corner \((a_E+1/2,|b_E|+1/2)\).
Retain original owners
\[
       HG\in\{0,2\},\quad GA=0,\quad AB\in\{0,2\},
       \quad BT=2,\quad TD\in\{0,2\},\quad DE=3,\quad EH=1.
\tag{2}
\]
There is no assumption on the sign of any outer error, no AB
alignment, no frame ordering, and no mismatch or tangent cut.
The E inequalities are exactly
\[
 a_D+a_E\sin\delta+b_E\cos\delta\ge W(\delta),\qquad
 a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge W(\epsilon),
\tag{3}
\]
where \(\delta=\theta_E-\theta_D\),
\(\epsilon=\theta_H-\theta_E\), and
\(W(z)=(1+\cos z+|\sin z|)/2\).

**Theorem.** Every such system satisfies
\[
                              \boxed{\theta_G>\theta_T.}
\tag{4}
\]
This removes the intermediate-order hypothesis within precisely
the original hard normal-sign owner class (2). It does not assert
that other original quarter or mixed owners have already been
excluded.

## 2. The middle path and the two exact zero charges

Suppose otherwise that \(r=\theta_T-\theta_G\ge0\).
HAND_G5_REVERSED_INTERMEDIATE_MIDDLE_PATH_BOUND.md proves, with
the original arbitrary A/B frames and either AB witness,
\[
                  b_G+b_T\le S_0+\frac{149}{240}r.
\tag{5}
\]
Put
\[
 h=\theta_G-\theta_H,\qquad k=\theta_D-\theta_T,
 \qquad v=\theta_D-\theta_H=r+h+k.
\tag{6}
\]
The all-sign zero-edge theorem
HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md gives, for either
actual transverse owner on HG,
\[
 b_H+b_G\ge1-p h+\frac1{49}\,\frac{\sin|h|+\cos|h|-1}{2}.
\tag{7}
\]
The corresponding TD inequality has \(b_T+b_D\) and k.
These are the exact clipped labels for the normal signs here;
no new marker or radial representative is selected.
The last terms are nonnegative throughout the full frame span.
Add the two inequalities and use (5). Since
\(p-149/240=4699/11760>0\), every putative reversed system
must satisfy
\[
 \boxed{\quad 2\le b_H+b_D+S_0+p v.\quad}
\tag{8}
\]
This step allowed all signs of h and k. The rest of the proof
uses only H,D,E and the real number \(-7/10\le v\le7/10\).

## 3. Nonnegative endpoint span

Assume first \(0\le v\le7/10\), and put \(K=847/800\).
The local E-pair calculation in Section 4 of
HAND_G5_REVERSED_INTERMEDIATE_SPAN_WITH_NONNEGATIVE_OUTER_ERRORS.md
uses only (3), the two actual endpoint circles, the true E core,
and the original full frame interval. In particular it does not
use AB alignment or any outer-error sign. It gives, for either
E sign and every E frame,
\[
 a_H+a_D\ge2+K\sin v-d(1-\cos v),\qquad
 d=\begin{cases}
 183/200,&0\le v\le6/25,\\
 4/5,&6/25\le v\le7/10.
 \end{cases}
\tag{9}
\]
The two endpoint circles and concavity therefore bound the
right side of (8) by
\[
 F_d^+(v)=2\sqrt{Q-X_d(v)^2}-1+S_0+p v,
 \qquad X_d=\frac32+\frac K2\sin v-\frac d2(1-\cos v).
\tag{10}
\]
We show it is strictly below two.

### 3.1 The interval \([0,6/25]\)

Put \(Y_0=\sqrt{Q-9/4}\), \(B_0=(3/2)/Y_0\).
Direct squaring gives
\[
 Y_0<\frac{1291}{1000},\quad S_0<\frac{52}{125},
 \qquad \frac{29}{25}<B_0<\frac76.
\tag{11}
\]
The square-root tangent at \(X=3/2\) bounds the increment
in (10) by
\[
 p v-B_0K\sin v+B_0d(1-\cos v).
\]
Use \(\sin v\ge v-v^3/6\),
\(1-\cos v\le v^2/2\), and \(v\le6/25\).
The increment is at most v times
\[
 p-\frac{29}{25}K\left(1-\frac{(6/25)^2}{6}\right)
       +\frac76\frac{183}{200}\frac{6/25}{2}
                 =-\frac{41559103}{612500000}<0.
\tag{12}
\]
At zero, (11) gives \(F_d^+(0)<999/500<2\).
This proves the contradiction on the entire first interval.

### 3.2 The interval \([6/25,7/10]\)

Here
\[
 X=\frac{11}{10}+\frac25\cos v+\frac{847}{1600}\sin v.
\]
The exact polynomial calculation in Sections 5.2 of the same
local E note gives \(Y=\sqrt{Q-X^2}<6/5\) and
\[
 \frac{d^2}{dv^2}(2Y)=\frac{2N(X)}{Y^3}>0,
 \qquad N(X)>\frac{19}{50}.
\tag{13}
\]
For clarity, the identity is
\[
\begin{gathered}
 N(X)=X(X-A)(Q-X^2)-Q\{B^2+C^2-(X-A)^2\},\\
 N'(X)=(4X-3A)(Q-X^2),\qquad
 (A,B,C)=(11/10,2/5,847/1600).
\end{gathered}
\]
Thus (10), whose added term is linear, is convex. The same
endpoint square bounds give
\[
\begin{aligned}
 F_d^+(6/25)
 &<2\frac{1151}{1000}-1+\frac{52}{125}+p\frac6{25}
                         =2-\frac{909}{24500},\\
 F_d^+(7/10)
 &<2\frac{233}{250}-1+\frac{52}{125}+p\frac7{10}
                         =2-\frac1{175}.
\end{aligned}
\tag{14}
\]
Convexity excludes (8) on this whole interval as well.

## 4. Negative endpoint span: minimize the actual E pair

It remains to treat \(v=-\alpha\), \(0\le\alpha\le7/10\).
Then \(\delta+\epsilon=\alpha\).
For this symmetric endpoint-primary estimate, if \(b_E<0\),
exchange \(a_H,a_D\) and \(\delta,\epsilon\), and replace
\(b_E\) by \(-b_E\). This exchanges the two inequalities (3)
exactly and leaves their sum and all circle bounds unchanged.
Hence assume \(b_E\ge0\) in this subsection.

Put \(\omega=\alpha/2\), \(c=\cos\omega\),
\(s=\sin\omega\), \(\zeta=(\delta-\epsilon)/2\).
The summed primary demand is
\[
 C(\zeta)=W(\delta)+W(\epsilon)
       -a_E(\sin\delta+\sin\epsilon)
       -b_E(\cos\delta-\cos\epsilon),
 \qquad a_H+a_D\ge C(\zeta).
\tag{15}
\]
For \(|\zeta|\le\omega\),
\[
 C(\zeta)=1+\{c+s-2a_Es\}\cos\zeta+2b_Es\sin\zeta.
\tag{16}
\]
Its nonconstant part is positive throughout this interval.
Indeed \(a_E<283/200\), \(b_E<9/10\),
\(c,\cos\zeta>15/16\), and
\(s,|\sin\zeta|\le7/20\) give the lower bound
\[
 \left(\frac{15}{16}-\frac{183}{100}\frac7{20}\right)
                 \frac{15}{16}
                  -\frac95\left(\frac7{20}\right)^2
                       =\frac{927}{16000}>0.
\tag{17}
\]
Consequently (16) is concave, and its minimum is at an endpoint.
The smaller endpoint for \(b_E\ge0\) is \(\zeta=-\omega\).

The E frame cannot lower the demand by leaving that interval.
For \(\eta=|\zeta|\ge\omega\),
\[
 C(\zeta)=1+(c-2a_Es)\cos\eta
                    +(c+\operatorname{sgn}(\zeta)2b_Es)\sin\eta.
\tag{18}
\]
Put \(M=(\eta+\omega)/2\le7/20\), using the full frame span.
The difference from the corresponding endpoint is
\(2\sin((\eta-\omega)/2)\) times
\[
\begin{cases}
 c(\cos M-\sin M)+2s(b_E\cos M+a_E\sin M),&\zeta>0,\\
 c(\cos M-\sin M)+2s(a_E\sin M-b_E\cos M),&\zeta<0.
\end{cases}
\]
The first expression is positive. Sorting bounds the second
below by
\((c-2b_Es)(\cos M-\sin M)>0\), because
\[
 c-2b_Es>\frac{15}{16}-\frac95\frac7{20}
                                      =\frac{123}{400}>0.
\]
Thus the actual E pair has its smallest possible sum at one of
its two endpoint frames, for every fixed E coordinate pair.

At the worse endpoint, (15) becomes
\[
 a_H+a_D\ge2-J_E(\alpha),\qquad
 J_E(\alpha)=(a_E-\tfrac12)\sin\alpha
                         +(b_E+\tfrac12)(1-\cos\alpha).
\tag{19}
\]

### 4.1 The restricted E support

Let \(X_E=a_E+1/2\), \(Y_E=b_E+1/2\ge1/2\).
Then
\(J_E=(X_E-1)\sin\alpha+Y_E(1-\cos\alpha)\).
On the Q-circle the unconstrained maximizing corner has
\(Y_E=R\sin(\alpha/2)\). For \(\alpha\le1/2\),
\[
 R\sin(\alpha/2)<\frac{1979}{1000}\frac14
                         =\frac12-\frac{21}{4000}.
\]
Hence the transverse floor is active, and the restricted support
is attained at \(Y_E=1/2\). Equivalently, the objective decreases
along the circle for \(Y_E\ge1/2\). Therefore
\[
 J_E(\alpha)\le g(\alpha):=
                  k_0\sin\alpha+\frac12(1-\cos\alpha)
                         \qquad(0\le\alpha\le1/2).
\tag{20}
\]
For larger \(\alpha\), unrestricted circle support gives
\[
 J_E(\alpha)\le2R\sin(\alpha/2)-\sin\alpha
                                  \le\frac{41}{40}\alpha.
\tag{21}
\]
The last inequality is an explicit Taylor comparison on
\([0,7/10]\): with \(R_+=1979/1000\), its ratio to \(\alpha\)
is at most
\[
 R_+-1+\left(\frac16-\frac{R_+}{24}\right)\alpha^2
                                     +\frac{R_+}{1920}\alpha^4.
\]
The coefficients of \(\alpha^2,\alpha^4\) are positive.
At \(\alpha=7/10\), this expression is less than \(41/40\)
by \(28738807/6400000000>0\). The comparison uses only the
degree-five upper sine at \(\alpha/2\) and degree-three lower
sine at \(\alpha\).

## 5. The narrow scalar range is strictly concave

For \(0\le\alpha\le1/2\), the two endpoint circles,
(19)--(20), and (8) would require
\[
 F^-(\alpha):=2Y-1+S_0-p\alpha\ge2,
 \qquad X=\frac32-\frac12g(\alpha),\quad Y=\sqrt{Q-X^2}.
\tag{22}
\]
We give a whole-interval upper certificate with one fixed rational
comparison point.

Write
\[
 X=A+B\cos\alpha+C\sin\alpha,
 \qquad (A,B,C)=(5/4,1/4,-k_0/2).
\]
The same elementary differentiation as in (13) gives
\[
 (F^-)''=\frac{2N(X)}{Y^3},\qquad
 N(X)=X(X-A)(Q-X^2)-Q\{B^2+C^2-(X-A)^2\},
\tag{23}
\]
and \(N'(X)=(4X-3A)(Q-X^2)\).
The bounds
\(g(\alpha)\le(183/200)\alpha+\alpha^2/4\le13/25\)
give
\[
                    \frac{31}{25}\le X\le\frac32,
                    \qquad0<Y<\frac{31}{20}.
\]
Thus N increases over the relevant X range. Moreover
\[
 N(3/2)=\frac38(Q-9/4)-\frac Q4 k_0^2<-\frac{19}{100}.
\tag{24}
\]
For an exact check, use \(k_0>1829/2000\); substituting this
lower bound makes the right side of (24) smaller than
\(-19/100\) by \(162564149/40000000000\).
Consequently, throughout the entire interval,
\[
 (F^-)''<-\frac{2(19/100)}{(31/20)^3}< -\frac1{10}.
\tag{25}
\]

Use the one comparison point \(a=31/200\). The exact rational
root bounds
\[
 \frac{914575}{10^6}<k_0<\frac{914576}{10^6},\qquad
 R_1<\frac{1707513}{10^6}
\tag{26}
\]
follow by positive squaring. At a, alternating Taylor bounds give
\[
\begin{gathered}
 \frac{14264067}{10^7}<X(a)<\frac{14264068}{10^7},\qquad
 \frac{1371482}{10^6}<Y(a)<\frac{1371483}{10^6},\\
 \frac{980800}{10^6}<g'(a)<\frac{980803}{10^6}.
\end{gathered}
\tag{27}
\]
For reproducibility use
\[
 S_5(t)=t-t^3/6+t^5/120,\quad S_7(t)=S_5(t)-t^7/5040,
 \quad C_4(t)=1-t^2/2+t^4/24,\quad C_6(t)=C_4(t)-t^6/720.
\]
Substitute (26), \(S_7(a)\le\sin a\le S_5(a)\), and
\(C_6(a)\le\cos a\le C_4(a)\) into X and
\(g'=k_0\cos a+(1/2)\sin a\).
The two Y bounds in (27) then follow from the positive square
reserves
\[
 Q-(14264068/10^7)^2-(1371482/10^6)^2
                            =\frac{2389343}{3125000000000},
\]
\[
 (1371483/10^6)^2-Q+(14264067/10^7)^2
                            =\frac{169309389}{10^{14}}.
\]
Equations (26)--(27) give the two exact point bounds
\[
                       F^-(a)<\frac{199983}{100000},
                       \qquad |(F^-)'(a)|<\frac1{2000}.
\tag{28}
\]
Indeed the upper bound for F is
\(12248951/6125000\), less than the displayed bound by
\(31/24500000\). The derivative is
\(Xg'/Y-p\); the rational lower and upper substitutions from
(27) lie strictly between \(-1/2000\) and \(1/2000\).
Their respective positive reserves are
\(190270169/1120044450000\) and
\(19829265943/24000935000000\).

Integrate (25) in either direction from a and complete the square.
For every \(0\le\alpha\le1/2\),
\[
\begin{aligned}
 F^-(\alpha)
 &\le F^-(a)+(F^-)'(a)(\alpha-a)-\frac1{20}(\alpha-a)^2\\
 &\le F^-(a)+5\{(F^-)'(a)\}^2
 <\frac{199983}{100000}+5\left(\frac1{2000}\right)^2
                         =2-\frac{27}{160000}<2.
\end{aligned}
\tag{29}
\]
This contradicts (22) on the whole narrow range. The rational
comparison point is used with a global curvature bound, not as a
sampled acceptance test.

## 6. The remaining negative-span range decreases

For \(1/2\le\alpha\le7/10\), (19), (21), and the two endpoint
circles bound the right side of (8) by
\[
 F_{\mathrm{lin}}^-(\alpha)
 =2\sqrt{Q-Z(\alpha)^2}-1+S_0-p\alpha,
 \qquad Z(\alpha)=\frac32-\frac{41}{80}\alpha.
\tag{30}
\]
This function decreases. Its derivative is
\[
 \frac{41}{40}\frac{Z}{\sqrt{Q-Z^2}}-p.
\]
The ratio decreases as \(\alpha\) increases; at \(\alpha=1/2\),
\(Z=199/160\), \(\sqrt{Q-Z^2}>3/2\), and
\((41/40)(199/160)<p(3/2)\). At that same endpoint,
\(\sqrt{Q-Z^2}<77/50\), by positive squaring. Hence
\[
 F_{\mathrm{lin}}^-(\alpha)\le F_{\mathrm{lin}}^-(1/2)
 <2\frac{77}{50}-1+\frac{52}{125}-\frac{25}{49}
                            =2-\frac{87}{6125}<2.
\tag{31}
\]

Equations (12), (14), (29), and (31) contradict (8) for every
possible endpoint span v. Thus the original supposition
\(\theta_G\le\theta_T\) was impossible, proving (4).

The proof retained every original outer sign and both original
transverse owners, arbitrary A/B/E frames, either E tangent sign,
and all weak contacts. Its fixed middle stress, exact zero charges,
and whole-interval scalar bounds require no state or angle mesh,
numerical acceptance premise, Lean compilation, or CI.
