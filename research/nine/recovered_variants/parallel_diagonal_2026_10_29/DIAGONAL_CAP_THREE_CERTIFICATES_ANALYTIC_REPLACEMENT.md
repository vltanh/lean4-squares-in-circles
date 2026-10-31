# Three whole diagonal-cap inequalities without coefficient tables

Date: October 27, 2026.

**Status: complete analytic replacement, pending independent acceptance.**
The reference source is the exact PR11 head
`8680a4b9204c0d6fb82a8d052ece5bb52aa9b6c8`.
This note replaces Certificates I, II and III of
`SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md`, Section 7, on their
entire original closed parameter rectangles. Their geometric callers
and all their unchanged physical hypotheses are retained. Certificate
IV, and the vertical-row scalar inequality which uses it, remain active.

The replacement removes 20+20+36=76 Bernstein coefficient comparisons.
It does not retire the whole 202-entry packet: its remaining 126-entry
vertical-cap certificate is still required. Historical source formulas,
tables, scripts and reviews are preserved.

## 1. Common notation and exact targets

Write
\[
 r=\sqrt2,\quad Q=\frac{1105}{256},\quad A=2+r,\quad
 \lambda=r-1,\quad h_0=\frac25,\quad
 \kappa=h_0+\frac r2,\quad
 \alpha=\frac{Q+4-b^2}{4}.
\]
Throughout this note,
\[
 \frac12\le b\le\frac32,\qquad 0\le z\le\lambda.
 \tag{1}
\]
We use only the elementary radical bracket
\[
 \frac{140}{99}<r<\frac{99}{70}.
 \tag{2}
\]
Indeed \(2\cdot99^2-140^2=2>0\) and
\(99^2-2\cdot70^2=1>0\). In particular
\(7/5<r<3/2\), \(0<\lambda<1/2\), and
\(0<\kappa-1<1/4\).

For the first two targets, retain exactly the source polynomials
\[
 P_I=\sum_{j=0}^4p_jz^j,\qquad P_{II}=\sum_{j=0}^4q_jz^j,
\]
where
\[
\begin{aligned}
p_0&=(1+\kappa)^2-Q,\\
p_1&=4\alpha(1+\kappa-b)+8b-2A(1+\kappa),\\
p_2&=2b^2+4(1-A)\alpha+A^2+2-2\kappa^2,\\
p_3&=4\alpha b-4(A/2-\alpha)(1-\kappa),\\
p_4&=(1-\kappa)^2-b^2,
\end{aligned}
\qquad
\begin{aligned}
q_0&=1+2b,\\
q_1&=4(1+b)-4\alpha(1+b-2/5),\\
q_2&=6-4\alpha-4b^2+16/25,\\
q_3&=4(1-b)+16/5-4\alpha(7/5-b),\\
q_4&=5-4\alpha-2b.
\end{aligned}
\tag{3}
\]
The source identities identify these with \((1+z^2)^2F\), after
\(a=\alpha\), for its two E-owned separating axes and the two complete
angular sectors. The parameter is \(z=\tan(\theta/2)\),
\(0\le\theta\le\pi/4\). The two orders of the actual own directions are
\((u,v)=(\cos\theta,\sin\theta)\) and
\((u,v)=(\sin\theta,\cos\theta)\), respectively.

We shall prove
\[
 P_I>\frac3{25},\qquad P_{II}>\frac3{25}.
 \tag{4}
\]
Section 5 proves the source's third squared excess directly, without
introducing its cleared polynomial or a coefficient table.

## 2. The shared 45-degree endpoint

At \(z=\lambda\), the two expressions agree. Put \(x=b-1/2\in[0,1]\).
Direct expansion gives
\[
\begin{aligned}
P_I(b,\lambda)=P_{II}(b,\lambda)
={}&-\frac{365547}{6400}+\frac{129529}{3200}r\\
&+\left(-\frac{35711}{640}+\frac{12757}{320}r\right)x\\
&+\left(\frac{33}{5}-\frac{22}{5}r\right)x^2
 +(6-4r)x^3.
\end{aligned}
\tag{5}
\]
The constant exceeds \(3/25\), with rational lower gap
\(587/126720\) from (2). The linear coefficient is positive by the
same lower radical bound, and both remaining coefficients are positive
because \(r<3/2\). Thus (5) is greater than \(3/25\) throughout.

At the other endpoint of the first sector,
\[
 p_0=-\frac{11881}{6400}+\frac75r>\frac3{25};
 \tag{6}
\]
the rational lower gap from (2) is \(2149/633600\).

## 3. The entire first sector

First note
\[
 \frac32<\alpha<\frac{21}{10},\qquad
 A/2-\alpha>-\frac25,\qquad
 p_3>\frac{13}{5},\qquad -\frac94<p_4<0.
 \tag{7}
\]
For example \(p_3=4\alpha b+4(A/2-\alpha)(\kappa-1)\);
the first three bounds and \(0<\kappa-1<1/4\) give its stated bound.
Set
\[
 D=p_3+\lambda p_4>\frac{13}{5}-\frac98=\frac{59}{40}>0.
 \tag{8}
\]

### 3.1. The lower part of the b interval

Suppose \(1/2\le b\le2/3\). The functions \(p_2,p_3\) are increasing
in b, since
\[
 p_2'=2(A+1)b>0,\qquad
 p_3'=Q+4-3b^2+2b(\kappa-1)>0.
\]
Since \(p_4<0\), \(p_3>0\), and \(z\le\lambda\),
\[
\begin{aligned}
 \partial_z^2P_I
 &\le2p_2+6\lambda p_3\\
 &\le-\frac{2755147}{28800}+\frac{154135}{2304}r<-1.
\end{aligned}
\tag{9}
\]
The last value is the exact expression at \(b=2/3\); substitution of
\(r<99/70\) leaves a gap of \(40891/806400\) below \(-1\).
Thus \(P_I\) is concave in z. Its minimum on the interval occurs at
an endpoint, and (5)--(6) prove (4) on this whole subrectangle.

### 3.2. The upper part of the b interval

Suppose \(2/3\le b\le3/2\). From \(p_4<0\) and \(z\le\lambda\),
\[
 P_I-p_0
 =z(p_1+p_2z+p_3z^2+p_4z^3)
 \ge z(p_1+p_2z+Dz^2).
\]
Use \((z-\lambda/2)^2\ge0\) and (8) to obtain
\[
 p_1+p_2z+Dz^2
 \ge U+(p_2+D\lambda)z,
\]
where the two endpoint values of this last affine function are
\[
 U=p_1-\frac{D\lambda^2}{4},\qquad
 V=p_1+p_2\lambda+\frac{3D\lambda^2}{4}.
 \tag{10}
\]
We prove both positive on the whole b interval.

Put \(x=b-2/3\in[0,5/6]\). Expansion gives
\[
\begin{aligned}
U={}&-\frac{3166399}{691200}+\frac{1300589}{276480}r\\
&+\left(-\frac{36627}{5120}+\frac{27583}{7680}r\right)x
 +\left(\frac{13}{10}-\frac{37}{40}r\right)x^2
 +\left(\frac74-\frac r2\right)x^3\\
&>2-\frac{21}{10}x-\frac1{100}x^2
 \ge\frac{35}{144}>0.
\end{aligned}
\tag{11}
\]
Each strict coefficient bound follows directly from (2); for the
quadratic one, the rational gap is \(1/560\). The lower quadratic
is decreasing for \(x\ge0\), and takes \(35/144\) at \(x=5/6\).

Likewise,
\[
\begin{aligned}
V={}&\frac{12943841}{691200}-\frac{6082321}{460800}r\\
&+\left(\frac{51391}{3072}-\frac{27583}{2560}r\right)x
 +\left(-\frac52+\frac{111}{40}r\right)x^2
 +\left(-\frac54+\frac32r\right)x^3\\
&>\frac1{20}+x+x^2+\frac45x^3>0.
\end{aligned}
\tag{12}
\]
Again all four coefficient bounds follow from (2). In particular the
constant's lower gap above \(1/20\) is \(121429/13824000\).
An affine function with positive endpoint values is positive
throughout. Equations (10)--(12) therefore give
\(P_I\ge p_0>3/25\), including \(z=0\). Together with Section 3.1,
this proves the first inequality of (4) on all of (1).

## 4. The entire second sector

The coefficients in (3) satisfy
\[
 q_2=\frac{66}{25}-Q-3b^2<0,\qquad
 q_4=(b-1)^2-Q<0.
\]
Also
\[
 q_3'=Q+\frac{14}{5}b-3b^2>0\quad(1/2\le b\le3/2).
\]
This quadratic is concave in b and positive at both endpoints.
Consequently
\[
 q_3\le q_3(3/2)=\frac{925}{512}<2.
\]
It follows that
\[
 \partial_zP_{II}
 =q_1+2q_2z+3q_3z^2+4q_4z^3
 \le q_1+6\lambda^2.
\]
For \(x=b-1/2\in[0,1]\), the exact last expression is
\[
 \frac{7745}{512}-12r-\frac{3797}{1280}x
       +\frac{21}{10}x^2+x^3
 <-\frac95+\frac{171}{1280}x<0.
 \tag{13}
\]
Here the constant bound follows from (2), and the rest uses
\(x^2,x^3\le x\). Thus \(P_{II}\) is strictly decreasing in z.
Its minimum is the shared endpoint (5), proving its inequality in
(4) on the whole original rectangle.

## 5. The whole W-owned sector from one monotone comparison

This section retains the actual closest-point reduction in the source,
Section 4.2. Its geometric argument already proves that the squared
norm of the actual top vertex is no smaller than that of its
two-normal intersection, and that lowering h to \(h_0=2/5\) and then
raising a to \(\alpha\) can only lower the squared excess. The remaining
target is precisely
\[
\begin{gathered}
 0\le u\le v,\quad u^2+v^2=1,\quad w=u+v,\\
 z_x^*=1-\alpha+u-v+\frac{v(b-h_0)}w,\qquad
 z_y^*=w+\frac{h_0u+bv}w,\\
 F=(z_x^*)^2+(z_y^*)^2-\alpha^2-b^2.
\end{gathered}
\tag{14}
\]
We prove \(F>9/100\) for every such direction and every b in (1).

Put
\[
 t=v-u=\sqrt{2-w^2},\qquad 1\le w\le r,\qquad
 q=\frac{b-h_0}{2}\in[1/20,11/20],\qquad
 e=\frac{b+h_0}{2},\qquad d=1-\alpha+q.
\]
Then
\[
 z_x^*=d-t+\frac{qt}{w},\qquad
 z_y^*=w+e+\frac{qt}{w}.
\]
Define the 45-degree endpoint excess
\[
 F_*=d^2+(r+e)^2-\alpha^2-b^2.
\]
Using \(w^2+t^2=2\) and \(r-w=t^2/(r+w)\), direct subtraction yields
\[
 F-F_*=2tB,
\]
with
\[
 B=(\alpha-1)(1-q/w)+bq/w
       -\frac{qt}{w}(1-q/w)-\frac{et}{r+w}.
 \tag{15}
\]

For fixed q, the function
\[
 f(w)=\frac{\sqrt{2-w^2}(w-q)}{w^2}
\]
is strictly decreasing on \(1<w<r\). After multiplication of its
derivative by the positive factor
\(\sqrt{2-w^2}\,w^3\), its numerator is
\[
 q(4-w^2)-2w\le3\cdot\frac{11}{20}-2=-\frac7{20}<0.
\]
Continuity at the endpoints gives \(f(w)\le f(1)=1-q\).
The other terms in (15) use
\(1-q/w\ge1-q\), \(1/w\ge1/r\), and
\(t/(r+w)\le1/(r+1)=r-1\). All their multipliers have the displayed
positive signs. Therefore
\[
 B\ge L(b):=(\alpha-1-q)(1-q)+\frac{bq}{r}-e(r-1).
 \tag{16}
\]
For \(y=3/2-b\in[0,1]\), expansion is
\[
 L=\frac{95741}{102400}-\frac{43r}{80}
   +\left(\frac{469}{10240}-\frac{3r}{20}\right)y
   +\left(\frac{41}{80}+\frac r4\right)y^2-\frac18y^3.
\]
The first three coefficients are respectively greater than
\(17/100,-1/6,17/20\), by (2). Since \(y^3\le y^2\),
\[
\begin{aligned}
 L&>\frac{17}{100}-\frac y6+\frac{29}{40}y^2\\
  &=\frac{29}{40}\left(y-\frac{10}{87}\right)^2
       +\frac{17}{100}-\frac5{522}
   >\frac4{25}.
\end{aligned}
\tag{17}
\]
The last constant gap is \(11/26100>0\). Thus \(F\ge F_*\),
with strict inequality unless \(t=0\).

Finally, with \(x=b-1/2\in[0,1]\),
\[
 F_*=-\frac{60409}{51200}+\frac9{10}r
      +\left(-\frac{5077}{5120}+r\right)x
      +\frac{11}{40}x^2+\frac14x^3>\frac9{100}.
 \tag{18}
\]
The constant exceeds \(9/100\), with rational lower gap \(1613/563200\)
from (2); every other coefficient is positive. Equations (15)--(18)
prove the required whole-angle inequality.

The source's cleared expression is exactly
\[
 P_{III}=D_z^2W_z^2F,\qquad
 D_z=1+z^2,\quad W_z=1+2z-z^2>0.
\]
Hence this argument proves its strict positivity on its original
closed rectangle, including both angular endpoints and \(b=1/2\).
No expansion into Bernstein coefficients is needed.

## 6. Exact dependency replacement and retained scope

The substitution is local to the source's three stated inequalities:

| Original input in SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY | Exact replacement | Coefficient comparisons removed |
| --- | --- | ---: |
| Section 4.1, \(u\ge v\), Certificate I | Sections 2--3, \(P_I>3/25\) on all of (1) | 20 |
| Section 4.1, \(u\le v\), Certificate II | Sections 2 and 4, \(P_{II}>3/25\) on all of (1) | 20 |
| Section 4.2, \(u\le v\), Certificate III | Section 5, the original reduced squared excess \(F>9/100\) | 36 |
| Section 5, the complete vertical center cap, Certificate IV | Unchanged; 126 coefficients remain active | 0 |

The W-owned case \(u\ge v\) still uses the source's unchanged reduction
to its E-owned case. The horizontal-row argument remains unchanged.
The full separating-axis cover, the two-normal positive-combination
argument, every actual square, every physical endpoint mask, the
original transverse means and all monotonic reductions remain as in
the source. This note adds no condition \(R\ge2\) to the original
polynomial rectangles and does not omit weak endpoints.

In particular the accepted current all-mask local diagonal theorem
`FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md`, Section 2, uses precisely
this balanced diagonal-cap argument; its other endpoint sectors are
unchanged. That theorem in turn remains an explicit dependency of
`GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md`, Section 2.
Thus the replacement reaches the current whole-simple-C6 assembly
through its actual retained balanced diagonal-cap caller.

The precise inherited count is now 126 rather than 202 if this
replacement is independently accepted. This does not add 76 again to
the older separately retired packets of sizes 1559, 45, 209 and 288,
or to the 12 earlier matrix certificates. It also does not retire any
of the 1080 side-arc comparisons merely by replacing these three
different inequalities. The same-nine-square \(R>2\) proof still has
its separately counted five fixed mass charges and one derivative
enclosure. No new selected component, graph mask, force equation, gate
or equality conclusion is asserted here.

All source identities displayed above are exact polynomial or rational
identities. Only elementary differentiation, monotonicity, concavity,
the one rational bracket (2), and the displayed fixed rational
comparisons enter the proof. No numerical sampling, subdivision,
optimization or new computational certificate is a premise.
