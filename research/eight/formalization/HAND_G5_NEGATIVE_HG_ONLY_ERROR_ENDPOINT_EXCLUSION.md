# The negative HG0 endpoint with all other hard-path frames aligned is impossible

## 1. Exact scope

Put
\[
 Q=\frac{9789}{2500},\qquad K=\frac{13}{12}.
\]
Retain nonnegative sorted own-frame magnitudes for H, A, B and D,
with their actual circle inequalities
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{1}
\]
For E, allow a signed transverse coordinate: require
`a_E>=|b_E|` and `(a_E+1/2)^2+(|b_E|+1/2)^2<=q`.
Let
\[
 0\le\alpha\le\frac{27}{100},\qquad
 \delta,\epsilon\ge0,\qquad\delta+\epsilon=\alpha,
 \quad W(z)=\frac{1+\cos z+\sin z}{2}.
\tag{2}
\]
The following necessary five-anchor system is impossible:
\[
\begin{aligned}
 b_H+a_A\cos\alpha
       &\ge\frac12+\frac32\cos\alpha+K\sin\alpha,\\
 b_A+b_B&\ge1,\\
 a_B+b_D&\ge2,\\
 a_D+a_E\sin\delta+b_E\cos\delta&\ge W(\delta),\\
 a_H+a_E\sin\epsilon-b_E\cos\epsilon&\ge W(\epsilon).
\end{aligned}
\tag{3}
\]
Here the first inequality is accompanied by `a_A>=1`, as supplied
by its original GA0 contact. No sign or outer-boundary equality for
E is assumed.

This includes the original hard-owner endpoint in which
\[
 \theta_G=\theta_A=\theta_B=\theta_T=\theta_D=0,
 \qquad\theta_H=\alpha,
 \qquad0\le\theta_E\le\alpha,
\]
and the retained original axes are HG0, GA0, AB0/2, BT2, TD0/2,
DE3 and EH1, with the stated intended signs. The only nonzero
outer zero error is the negative HG error. Indeed, its true core
bound `a_G>=7/12`, established before eliminating G, and the same
GA0 inequality `a_A-b_G>=1` give the first line of (3).
The aligned opposite path gives the third line. Reflection gives
the corresponding endpoint on the D side.

The full shared negative-outer chain already supplies
`alpha<27/100` in
`HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md`. This note
does not assert that an arbitrary chain reaches the particular
endpoint (3).

## 2. Eliminate the same E circle in the sum of its two contacts

Define
\[
 f(b)=\sqrt{Q-(b+1/2)^2}-1/2,\qquad
 R=\sqrt{Q-1},\qquad R_0=\sqrt{Q-1/4},\qquad k=R_0-1.
\tag{4}
\]
The four nonnegative anchors have `a_i<=f(b_i)`, and E has
`a_E<=f(|b_E|)`. For positive alpha,
put `A=alpha/2` and `v=delta-alpha/2`. The force on E in the
sum of its two contacts is
\[
 (\sin\delta+\sin\epsilon,\ \cos\delta-\cos\epsilon)
       =2\sin A(\cos v,-\sin v).
\]
Its first component is positive, and the absolute ratio of its
second component to its first is at most
\[
 \tan(\alpha/2)<.137<\frac{1}{2R_0}.
\tag{5}
\]
For example, `sin(.135)<=.135` and
`cos(.135)>=1-.135^2/2` prove the first comparison, while
`R_0<383/200=1.915` proves the last one by positive squaring.

If the force components are X,Y, its value is at most
`X a_E+|Y| |b_E|`. Along E's containing-circle frontier,
the derivative of this upper bound with respect to `b=|b_E|`
is strictly negative:
\[
 X f'(b)+|Y|
 =-X\frac{b+1/2}{\sqrt{Q-(b+1/2)^2}}+|Y|
 \le X\left(-\frac1{2R_0}+.137\right)<0.
\]
Thus its maximum over the entire signed E domain is attained
at `b=0,a=R_0-1/2`. This is a support estimate for the same E
center; no E deformation is asserted.

Consequently the two original E contacts imply
\[
\begin{aligned}
 a_H+a_D
 &\ge W(\delta)+W(\epsilon)
            -(R_0-1/2)(\sin\delta+\sin\epsilon)\\
 &=1+[\cos A-(2R_0-2)\sin A]\cos v\\
 &\ge\frac32+\frac12\cos\alpha-k\sin\alpha.
\end{aligned}
\tag{6}
\]
The last comparison uses `|v|<=A`. Its bracket is positive,
since `cos A>.99`, `sin A<=.135`, and `2R_0-2<1.83`.
At alpha zero, the last line of (6) follows immediately by
adding the two contacts, so the same conclusion holds on the
closed interval (2).

## 3. Retain the A/B and H/D circle concavities together

The sorted circles give `b_H,b_D<9/10`. The first line of (3),
using `a_A>=1`, gives
\[
 b_H+a_A
 \ge2+K\sin\alpha-(3/2-a_A)(1-\cos\alpha)
 \ge2+K\sin\alpha-\frac12(1-\cos\alpha)\ge2.
\]
Here `K>tan(alpha/2)/2` proves the last inequality, including
alpha zero. Thus
\[
                         a_A>11/10.
\tag{7}
\]
The function f is decreasing and strictly concave. The actual AB
sum therefore gives
\[
 a_A+a_B\le f(b_A)+f(b_B)
 \le2f((b_A+b_B)/2)\le2f(1/2)=2R-1.
\tag{8}
\]
Add the first and third lines of (3), use (7)--(8), and put
`s=sin(alpha), c=cos(alpha)`. The result is
\[
\begin{aligned}
 b_H+b_D
 &\ge\frac52+\frac32c+Ks-(a_A+a_B)+(1-c)a_A\\
 &\ge5-2R+Ks-\frac25(1-c).
\end{aligned}
\tag{9}
\]
The weak final comparison is sufficient, including alpha zero.
Set
\[
 B=\frac52-R+\frac{13}{24}s-\frac15(1-c).
\tag{10}
\]
A second use of the same concavity, this time at the original
H and D centers, gives
\[
 a_H+a_D\le2f((b_H+b_D)/2)\le2f(B).
\tag{11}
\]
All square roots are defined at a feasible system: (9) places B
below its actual H/D average, and this average lies in the
nonnegative f domain.

Combining (6) and (11), and squaring positive quantities, yields
the necessary inequality
\[
 \left(\frac54+\frac14c-\frac{k}{2}s\right)^2
 +\left(\frac{14}{5}-R+\frac15c+\frac{13}{24}s\right)^2
 \le Q.
\tag{12}
\]
This comparison still concerns the five shared anchors in (3).
In particular A and B have not been replaced by independent
per-edge extrema.

## 4. One exact quartic contradicts (12) on the whole interval

Positive squaring gives
\[
 R<\frac{10672}{6250}=1.70752,
 \qquad k<\frac{183}{200}=.915,
\tag{13}
\]
with respective squared reserves
\[
 (10672/6250)^2-(Q-1)=\frac{959}{39062500},\qquad
 (383/200)^2-(Q-1/4)=\frac{13}{8000}.
\]
Both terms on the left side of (12) are positive. They are at
least the corresponding quantities obtained by replacing R and k
with the upper bounds in (13). Define the resulting exact excess
\[
 P(s,c)=
 \left(\frac54+\frac14c-\frac{183}{400}s\right)^2
 +\left(\frac{3414}{3125}+\frac15c+\frac{13}{24}s\right)^2-Q.
\tag{14}
\]
Reducing `c^2=1-s^2` gives
\[
 P=P_0+A(c-1)+B_1s+C_1sc+D_1s^2,
\tag{15}
\]
where
\[
\begin{gathered}
 P_0=\frac{47896}{9765625},\qquad
 A=\frac{132749}{125000}>0,\qquad
 B_1=\frac{3977}{100000},\\
 C_1=-\frac{29}{2400}<0,\qquad
 D_1=\frac{576301}{1440000}.
\end{gathered}
\]

For `0<=s<=27/100`, the positive square-root comparison
\[
             c\ge1-s^2/2-.13s^4
\tag{16}
\]
holds. On writing `v=s^2`, the square of the right side minus
`1-v` is `v^2(-.01+.13v+.0169v^2)`. The bracket is increasing
for nonnegative v and at `v=(27/100)^2` equals
`-433186471/10^12<0`.

Since `A>0`, `C_1<0`, and `c<=1`, substitution in (15) gives
\[
\begin{aligned}
 P(s,c)
 &\ge\frac{47896}{9765625}
   +\frac{4153}{150000}s
   -\frac{4708331}{36000000}s^2
   -\frac{1725737}{12500000}s^4\\
 &>p(s):=.0049+.027s-.131s^2-.139s^4.
\end{aligned}
\tag{17}
\]
Every terminating decimal in (17) is an exact rational; the
coefficient comparisons have been rounded in the displayed
lower-bound directions.

There is one whole-interval positivity argument. The quartic p
is strictly concave for nonnegative s, since
\[
                  p''(s)=-.262-1.668s^2<0.
\]
Its minimum on `[0,27/100]` is therefore at an endpoint. Both
endpoint values are positive:
\[
 p(0)=\frac{49}{10000},\qquad
 p(27/100)=\frac{190139701}{100000000000}>0.
\tag{18}
\]
Thus (14) is positive throughout the entire angular interval,
contradicting (12). This proves the endpoint theorem (1)--(3).

The proof uses two shared-circle concavity inequalities, one E
support, and one explicit quartic with two endpoint comparisons.
No state cover, angle mesh, sampled minimum, generated row
certificate, Lean compilation, or CI result is a premise.
