# The H/D span is positive in every aligned normal-sign hard chain

## 1. Statement without any frame-order hypothesis

Put \(Q=9789/2500\). Let H,A,B,D,E have nonnegative sorted
own-frame magnitudes and corner ceilings
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+\tfrac12)^2+(b_i+\tfrac12)^2\le q\le Q.
\tag{1}
\]
Assume the three zero edges are aligned. Write \(\rho\) for the
common A/B frame and put
\[
 t=\theta_H-\rho,\quad u=\rho-\theta_D,\quad
 \alpha=t+u=\theta_H-\theta_D,\quad
 \delta=\theta_E-\theta_D,\quad
 \epsilon=\theta_H-\theta_E.
\tag{2}
\]
All real frames lie in an interval of length at most \(7/10\).
There is no order assumption on these frames. The original
normal signs and hard owners give the necessary inequalities
\[
\begin{aligned}
 b_H+a_A\cos t-b_A\sin t&\ge1+\widehat W(t),\\
 b_A+b_B&\ge1,\\
 a_B\cos u-b_B\sin u+b_D&\ge1+\widehat W(u),\\
 a_D+a_E\sin\delta+b_E\cos\delta&\ge\widehat W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon&\ge\widehat W(\epsilon),
\end{aligned}
\qquad
\widehat W(z)=\frac{1+\cos z+|\sin z|}{2}.
\tag{3}
\]

**Positive-span conclusion.** Every system (1)--(3) satisfies
\[
                         a_H+a_D<2,\qquad \theta_H>\theta_D.
\tag{4}
\]
The first assertion uses only the first three inequalities of
(3), and holds for arbitrary signs of \(t,u\). Consequently the
common-frame clamp and E-order reduction apply to every
aligned-three-zero normal-sign hard-owner system, without any
frame-order hypothesis. Such a system has \(q\ge q_*\), with
the original-anchor equality statement of the aligned sharp
theorem.

This does not align arbitrary original zero edges. It removes
all remaining frame-order assumptions after those alignments
have already been made.

## 2. A decreasing quarter-cap bound independent of the angle's sign

For \(0\le b\le C_Q=\sqrt{Q/2}-1/2\), define
\[
 f(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12
\tag{5}
\]
and
\[
 R(b)=
 \begin{cases}
 f(b)-\tfrac12,&0\le b\le\tfrac12,\\[2mm]
 \sqrt{(f(b)-\tfrac12)^2+(b-\tfrac12)^2},
       &\tfrac12\le b\le C_Q.
 \end{cases}
\tag{6}
\]
Every sorted corner in (1) has \(b\le C_Q<9/10\), and its
primary satisfies \(a\le f(b)\).

Consider either hard-quarter inequality in (3), and denote its
outer transverse coordinate by \(b_{\mathrm{out}}\), its middle
coordinates by \(a,b\), and its signed quarter angle by \(v\).
Rearranging gives, for \(v\ge0\),
\[
 \frac32-b_{\mathrm{out}}
       \le(a-\tfrac12)\cos v-(b+\tfrac12)\sin v.
\tag{7}
\]
For \(v=-z\le0\), it gives
\[
 \frac32-b_{\mathrm{out}}
       \le(a-\tfrac12)\cos z+(b-\tfrac12)\sin z.
\tag{8}
\]
The left side exceeds \(3/5\). Feasibility forces \(a>1/2\):
otherwise sorting also gives \(b\le1/2\), making either right
side nonpositive. Since \(0\le z,v\le7/10<\pi/2\), (7) is
at most \(a-1/2\). The same is true of (8) if \(b\le1/2\).
If \(b\ge1/2\), Cauchy's inequality bounds (8) by
\(\sqrt{(a-1/2)^2+(b-1/2)^2}\).
Increasing \(a\) to \(f(b)\) in these bounds proves
\[
 (b_H+\tfrac12)+R(b_A)\ge2,\qquad
 (b_D+\tfrac12)+R(b_B)\ge2.
\tag{9}
\]

The function \(R\) is decreasing on its whole domain.
This is immediate below \(1/2\). Above \(1/2\), put
\[
 Y=b+\tfrac12,\qquad X=\sqrt{Q-Y^2},\qquad S=X+Y.
\tag{10}
\]
Sorting of the frontier means \(X\ge Y\), so
\[
 S'=1-\frac YX\ge0,\qquad
 R(b)^2=(X-1)^2+(Y-1)^2=Q+2-2S.
\tag{11}
\]
The two branches agree at \(b=1/2\), establishing the claimed
monotonicity.

At least one of \(b_A,b_B\) is at least \(1/2\). Call that
coordinate \(b\); the other is at least \(1-b\). By (9),
\(R(b)>3/5\). On the other hand,
\[
 \sqrt{Q-(61/50)^2}<\frac{779}{500}=1.558,
 \qquad
 R(18/25)^2<(.558)^2+(.22)^2=.359764<.36.
\tag{12}
\]
Monotonicity therefore forces
\[
                      \frac12\le b<\frac{18}{25}.
\tag{13}
\]
The other coordinate's lower bound \(1-b\) is in
\((.28,.5]\). Applying monotonicity once more,
\[
 R(b_A)+R(b_B)
 \le R(b)+R(1-b)
 =R(b)+f(1-b)-\tfrac12=:T(b).
\tag{14}
\]

## 3. The continuous scalar comparison has its maximum at an endpoint

Work on \(1/2\le b\le18/25\), and retain \(X,Y,S\) from
(10). Write \(r=R(b)\). The following bounds hold throughout:
\[
 \frac{31}{20}<X<\frac74,\qquad
 0<S'<\frac37,\qquad
 -S''=\frac Q{X^3}>\frac7{10},\qquad
 S'''=-\frac{3QY}{X^5}<0,\qquad
 r>\frac{11}{20}.
\tag{15}
\]
For the first bounds, use
\((31/20)^2+(61/50)^2<Q\) and \(Q-1<(7/4)^2\).
Next \(Y\ge1\) gives \(Y/X>4/7\), while \(X>Y\) on this
interval. The second-derivative bound follows from
\[
 \frac{39}{10}-\frac7{10}\left(\frac74\right)^3
                         =\frac{19}{128}>0.
\tag{16}
\]
Finally \(r\ge X-1>11/20\).

Differentiating \(r^2=Q+2-2S\) gives
\[
\begin{aligned}
 r'&=-\frac{S'}r,\\
 r''&=\frac{(-S'')r^2-(S')^2}{r^3},\\
 r'''&=-\frac{S'''}r+
       \frac{3S'}{r^5}\bigl((-S'')r^2-(S')^2\bigr).
\end{aligned}
\tag{17}
\]
The common numerator is strictly positive by (15), since
\[
 \frac7{10}\left(\frac{11}{20}\right)^2
                -\left(\frac37\right)^2
                    =\frac{5503}{196000}>0.
\tag{18}
\]
Thus \(r''>0\) and \(r'''>0\) on the whole interval.
Also
\[
 f'''(z)=-\frac{3Q(z+\tfrac12)}
                    {[Q-(z+\tfrac12)^2]^{5/2}}<0
       \quad(.28\le z\le.5).
\tag{19}
\]
Consequently
\[
              T'''(b)=r'''(b)-f'''(1-b)>0.
\tag{20}
\]
At \(b=1/2\), \(r=f(1/2)-1/2\) and \(r'=f'(1/2)\);
therefore
\[
                           T'(1/2)=0.
\tag{21}
\]

Equations (20)--(21) suffice to put the maximum of \(T\) at an
endpoint. Indeed \(g=T'\) is strictly convex with \(g(1/2)=0\).
For \(1/2<x<y\le18/25\), convexity gives
\[
           \frac{g(x)}{x-1/2}
                  \le \frac{g(y)}{y-1/2}.
\tag{22}
\]
Thus \(T'\) can change sign only from negative to positive.
The function \(T\) is monotone or first decreases and then
increases, so
\[
             T(b)\le\max\{T(1/2),T(18/25)\}.
\tag{23}
\]
This is a whole-interval derivative argument, with no angular
mesh or finite row selection.

The endpoint estimates are
\[
\begin{aligned}
 T(1/2)
   &=2\bigl(\sqrt{Q-1}-1\bigr)<1.416,\\
 T(18/25)
   &<.59981+1.81859-1=1.4184.
\end{aligned}
\tag{24}
\]
For the second line use the first root comparison in (12)
and the positive-square comparisons
\[
\begin{aligned}
 (.59981)^2-(.558)^2-(.22)^2
                   &=\frac{80361}{10^{10}}>0,\\
 (1.81859)^2-Q+(.78)^2
                   &=\frac{695881}{10^{10}}>0.
\end{aligned}
\tag{25}
\]
The first line follows from \((1.708)^2>Q-1\).
Combining (14), (23)--(25) yields
\[
                         R(b_A)+R(b_B)<1.4184.
\tag{26}
\]

## 4. The two outer primaries cannot sum to two

Suppose \(a_H+a_D\ge2\). The function
\(U\mapsto\sqrt{Q-U^2}\) is concave and decreasing for \(U>0\).
Applying its two-point concavity to the two outer corners gives
\[
\begin{aligned}
 (b_H+\tfrac12)+(b_D+\tfrac12)
 &\le2\sqrt{Q-\left(\frac{a_H+a_D}{2}+\tfrac12\right)^2}\\
 &\le2\sqrt{Q-\frac94}<2(1.29059).
\end{aligned}
\tag{27}
\]
The final root comparison is exact:
\[
                    (1.29059)^2-Q+\frac94
                          =\frac{225481}{10^{10}}>0.
\tag{28}
\]
But adding the two necessary inequalities (9), and then using
(26)--(27), gives the contradiction
\[
 4\le
 (b_H+\tfrac12)+(b_D+\tfrac12)+R(b_A)+R(b_B)
 <2(1.29059)+1.4184
 =4-\frac{21}{50000}.
\tag{29}
\]
This proves the first conclusion of (4), independently of
the signs of \(t,u\) and independently of E.

## 5. A nonpositive H/D span contradicts the mixed constraints

Suppose \(\alpha\le0\), and put
\[
             \omega=\frac{\alpha}{2},\qquad
             \zeta=\frac{\delta-\epsilon}{2}.
\tag{30}
\]
The full real-frame spread gives \(-.35\le\omega\le0\)
and \(|\zeta|\le.7<\pi/4\). The E contribution in the sum
of the last two inequalities of (3) is
\[
\begin{aligned}
 a_E(\sin\delta+\sin\epsilon)
          +b_E(\cos\delta-\cos\epsilon)
   &=2\sin\omega\,(a_E\cos\zeta-b_E\sin\zeta)\\
   &\le0.
\end{aligned}
\tag{31}
\]
Indeed \(\sin\omega\le0\), whereas sorting implies
\[
 a_E\cos\zeta-b_E\sin\zeta
       \ge a_E(\cos\zeta-|\sin\zeta|)\ge0.
\tag{32}
\]
Since \(\widehat W(z)\ge1\) for \(|z|\le.7\), the mixed
constraints now imply
\[
                a_H+a_D\ge
                     \widehat W(\delta)+\widehat W(\epsilon)\ge2,
\tag{33}
\]
contradicting Section 4. This includes \(\alpha=0\), and
proves \(\theta_H>\theta_D\).

## 6. Consequence for the complete aligned-three-zero class

Apply HAND_G5_COMMON_AB_FRAME_CLAMP.md using the now proved
positive H/D span. If the common A/B frame was outside D--H,
it moves to the nearer endpoint with strict decreases in both
actual middle circle values. H,D,E remain fixed. Then
HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md excludes E above
H and moves E below D to D with strict decrease in its actual
circle value. These constructions keep every frame in the
original span.

The resulting aligned and ordered system satisfies
HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md, which gives
\(q\ge q_*\). Its five positive circle masses retain any
strict middle or E loss. Hence equality rules out either
frame descent; the original common A/B and E frames were
already ordered. Applying that same sharp identity directly
to the original anchors gives their canonical stationary
values. No descendant is silently identified with an
original anchor.
