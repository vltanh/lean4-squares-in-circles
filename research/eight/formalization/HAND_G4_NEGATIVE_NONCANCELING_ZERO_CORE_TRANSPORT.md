# Negative noncanceling zero owners: core transport and an E boundary reduction

## 1. Scope and unchanged data

Put
\[
 Q=\frac{9789}{2500},\qquad U=\frac{283}{200},\qquad
 K=\frac{13}{12}.
\]
Consider the original signs H positive, G negative and A positive,
with unsigned own-frame coordinates \((a_i,b_i)\), sorting
\(a_i\ge b_i\ge0\), actual containing-circle bounds
\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q,
\]
and the actual core-avoidance condition. Normalize A's frame to zero.
Assume
\[
 \theta_H=\Theta\ge0,\qquad \theta_G=t<\Theta,\qquad
 e=\Theta-t>0,
\]
and that the three frames have spread at most \(7/10\).
Retain original HG axis 0 and original GA axis 0. Thus
\[
\begin{split}
 b_H-a_G\sin e+b_G\cos e&\ge W(e),\\
 a_A\cos t-b_A\sin t-b_G&\ge W(|t|),
 \qquad W(x)=\frac{1+\cos x+\sin x}{2}.
\end{split}                                                     \tag{1}
\]
The primary and tangent signs, hard owner and outer-frame order are
explicit hypotheses. There is no mismatch bound.

**Small-transverse transport.** If \(b_A\le1/2\), the same original
H and A coordinates satisfy
\[
 \boxed{\quad
 b_H+a_A\cos\Theta-b_A\sin\Theta
     >1+W(\Theta)+\frac e{150}.
 \quad}                                                        \tag{2}
\]
This is a necessary composite inequality with strict slack; it
does not move either retained anchor. Reflection gives the same
statement for original BT axis 2 followed by original TD axis 2
with negative reflected outer error and \(b_B\le1/2\).

Section 4 also restores the order \(0\le\theta_G\le\theta_H\)
when G initially lies below A, without assuming \(b_A\le1/2\).
Section 5 derives an E-interior boundary theorem for a full shared
chain whose remaining noncanceling outer errors are negative.
Neither result claims the as-yet-unproved global owner or order
capture.

## 2. The true core gives the needed primary, before any relaxation

The original GA witness, the actual center norm bound and \(W\ge1\)
give
\[
 0\le b_G
 \le a_A\cos t-b_A\sin t-W(|t|)
 \le |p_A|-1<U-1=\frac{83}{200}<\frac12.
\]
For this original G center, core avoidance therefore says
\[
 a_G\ge\frac7{12},\qquad a_G+\frac12\ge K.                       \tag{3}
\]
Indeed the distance from the origin to the sorted square is
\(\sqrt{(a_G-1/2)_+^2+(b_G-1/2)_+^2}\ge1/12\);
its second term vanishes. This uses the true core before
discarding any G coordinates.

Write \(P=a_A-1/2>0\) and define the continuous piecewise functions
\[
\begin{split}
 V(t)&=P\cos t-J(t)\sin t,\\
 U_A(t)&=P\sin t+J(t)\cos t,\\
 J(t)&=
 \begin{cases}
 b_A-1/2,&t<0,\\
 b_A+1/2,&t\ge0.
 \end{cases}
\end{split}                                                     \tag{4}
\]
Only V is asserted continuous at zero; its one-sided derivatives
are the stated \(-U_A\). The second inequality in (1) is
\(b_G+1/2\le V(t)\). The first one and (3) consequently imply
\[
 F(t):=b_H-\frac12+V(t)\cos(\Theta-t)
                   -K\sin(\Theta-t)-\cos(\Theta-t)\ge0.         \tag{5}
\]

For an auxiliary frame value \(z\) between the original t and
\(\Theta\), put \(r=\Theta-z\). Whenever \(F(z)\ge0\), the
sorted H circle, \(b_H<9/10\), gives
\[
 V(z)>D(r):=1-\frac25\sec r+K\tan r.                            \tag{6}
\]
Here \(0\le r\le7/10\), and
\[
 D(0)=\frac35,\qquad
 D'(r)=\frac{K-(2/5)\sin r}{\cos^2r}>0.                         \tag{7}
\]
The elementary bounds
\[
 \cos r\ge\frac34,\qquad \sin r\le\frac{13}{20},\qquad
 \cos r>\sin r
                                                                    \tag{8}
\]
will be used throughout.

## 3. A forward barrier proves the full negative transport

Suppose first \(z\ge0\) and \(b_A\le1/2\). In this case
\(B=b_A+1/2\le1\) and \(U_A(z)>0\). The original A circle gives
\[
 V(z)^2+U_A(z)^2=P^2+B^2
 \le Q+1-2\sqrt{Q-B^2}
 \le Q+1-2\sqrt{Q-1}<\frac{1501}{1000}.                         \tag{9}
\]
The first inequality follows by increasing the nonnegative P to
its circle frontier. The final strict bound follows by squaring
\(\sqrt{Q-1}>17073/10000\); its squared reserve is
\(72671/100000000\).

Ordinary differentiation of (5) gives
\[
 F'(z)=(K-U_A(z))\cos r+(V(z)-1)\sin r.                         \tag{10}
\]
At a point where \(F(z)\ge0\), (6), (9), and monotonicity in V
give
\[
 \frac{F'(z)}{\cos r}>
 K-\sqrt{\frac{1501}{1000}-D(r)^2}
                    +(D(r)-1)\tan r
 =D'(r)-\sqrt{\frac{1501}{1000}-D(r)^2}.                        \tag{11}
\]
The radicand is nonnegative whenever such a point exists, by
\(D<V\) and (9).

There is a single continuous squared reserve in (11). Directly,
\[
 \cos^3r\,[D(r)+D''(r)]
 =\cos^3r+K\sin r(3-\sin^2r)-\frac45.
\]
As a function of \(s=\sin r\), the first two terms have derivative
\[
 3\sqrt{1-s^2}\,[K\sqrt{1-s^2}-s]>0
\]
on the whole interval (8). Therefore \(D+D''>0\), and
\[
 D^2+(D')^2\ge D(0)^2+D'(0)^2
 =\frac9{25}+\frac{169}{144}.
\]
Consequently
\[
 D^2+(D')^2-\frac{1501}{1000}
 \ge\frac{587}{18000}.                                       \tag{12}
\]
Moreover \(D'<52/27<2\) and
\(\sqrt{1501/1000-D^2}<5/4\). Rationalizing (11) and then using
\(\cos r\ge3/4\) yields
\[
 F'(z)>\frac34\,\frac{587/18000}{13/4}
       =\frac{587}{78000}>\frac1{150}.                         \tag{13}
\]

If \(z<0\), the assumption \(b_A\le1/2\) gives
\(U_A(z)\le0\). Equations (6)--(8), (10) then give the stronger
bound
\[
 F'(z)>K\frac34-\frac25\frac{13}{20}>\frac1{150}.               \tag{14}
\]
The scalar F is continuous at zero. Thus it cannot first cross
from \(F\ge0\) to \(F<0\) as z increases: on either open sign
interval its derivative at every possible crossing is positive,
and both one-sided derivatives at zero have the same property.
Starting from (5), it follows that F stays nonnegative throughout
the whole interval from t to \(\Theta\). Integrating (13)--(14)
gives \(F(\Theta)>e/150\). Its exact endpoint value is
\[
 F(\Theta)
 =b_H+a_A\cos\Theta-b_A\sin\Theta-1-W(\Theta),
\]
which proves (2). Every original H and A coordinate was retained.

A strict composite slack of this kind can later be converted into
strict A-corner loss by a sufficiently small decrease of \(a_A\),
once AB is aligned: the AB sum then depends only on the transverse
coordinates. Such a later use must still check its other retained
constraints; it is not asserted automatically here.

## 4. Restore a crossed GA frame, for every transverse magnitude

Now allow any \(0\le b_A<9/10\), and suppose the original \(t<0\).
For \(t\le z<0\), the formula in (4) gives
\(U_A(z)\le2/5\). At every point with \(F(z)\ge0\), (6)--(10)
therefore imply
\[
 F'(z)>
 (K-\tfrac25)\frac34-\frac25\frac{13}{20}
 =\frac{101}{400}>\frac14.                                   \tag{15}
\]
The same forward-barrier argument proves
\[
 F(0)>-\frac t4.
\]
It keeps the original H and A coordinates and supplies the exact
HG0--GA0 necessary system with G's frame moved to A's frame zero.

For clarity, that necessary system has a concrete sorted G
realization. When \(q\ge q_L=19577/5000\), set
\[
 a'_G=\frac7{12},\qquad b'_G=a_A-1,\qquad \theta'_G=0.          \tag{16}
\]
Equations (6) and \(a_A<U\) give
\[
 \frac1{10}<b'_G<\frac{83}{200}<a'_G.
\]
Its circle lies strictly below \(q_L\), since
\[
 (a'_G+1/2)^2+(b'_G+1/2)^2
 <\frac{169}{144}+\left(\frac{183}{200}\right)^2
 =\frac{723901}{360000}<q_L.
\]
It is on the true core side. GA0 becomes an equality, and HG0
holds with strict slack by \(F(0)>-t/4\). No other retained
neighboring constraint uses G. Thus the stated necessary cycle
may use \(0\le\theta'_G\le\theta_H\) before an AB cap comparison.
Its other centers and all their own-frame corner values remain
unchanged. No nonneighbor or physical-gap condition is claimed
for this auxiliary G replacement.

This is a frame-order restoration within the stated hard-owner
class, not full outer-zero alignment when \(b_A>1/2\).

## 5. The negative-outer shared chain retains E's boundary reduction

Suppose AB is aligned, its original transverse witness gives
\(b_A+b_B\ge1\), and its common frame is zero. Let H and D have
frames \(\Theta\ge0\) and \(-\Upsilon\le0\), with
\[
 \alpha=\Theta+\Upsilon\le7/10.
\]
On each outer two-edge path, assume either its aligned composite
already holds, or it has the negative noncanceling owner treated
above. In the latter case first use Section 4 if its intermediate
frame crosses zero. Thus its nonnegative angles satisfy
\[
 t,e\ge0,\qquad t+e=\Theta
\]
on the H side, and the reflected relation on the D side.
All original H, A, B and D anchors remain unchanged.

For the H-side negative path, (5) gives the useful unsigned
primary inequality
\[
\begin{split}
 b_H
 &\ge\frac12+(1-V(t))\cos e+K\sin e\\
 &=2-a_A+(b_A+\tfrac12)\sin t
       +(a_A-\tfrac12)(1-\cos t)\\
 &\hspace{14mm}+K\sin e-(1-V(t))(1-\cos e).
\end{split}                                                     \tag{17}
\]
At feasibility \(V(t)>3/5\). Also
\((1-\cos e)/\sin e\le13/35\) for \(e>0\), by (8).
Hence the last line of (17) is at least \((9/10)\sin e\);
indeed \(K-(2/5)(13/35)=1963/2100>9/10\).
The same assertion at e zero is immediate.

In particular \(b_H+a_A\ge2\). The reflected argument gives
\(b_D+a_B\ge2\), including the already-aligned alternatives.
Since \(b_H,b_D<.9\), this forces \(a_A,a_B>1.1\), hence
\(b_A,b_B<.665\). AB then supplies \(b_A,b_B>.335\).
Dropping the nonnegative cosine term from (17), and using
\(\sin t+\sin e\ge\sin(t+e)\), proves
\[
\begin{split}
 b_H+a_A&\ge2+\frac{167}{200}\sin\Theta,\\
 b_D+a_B&\ge2+\frac{167}{200}\sin\Upsilon.
\end{split}                                                     \tag{18}
\]
An already-aligned path satisfies (18) directly.

The original A/B circles and their unchanged AB sum now give
exactly the shared concavity calculation from Section 3 of
[the E-interior reduction](HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md):
\[
 \boxed{\quad
 a_H+a_D<1.9968-.718\sin\alpha<2.
 \quad}                                                        \tag{19}
\]
This estimate has not assumed either remaining negative zero error
is small or zero.

Also \(b_H+b_D<1.8\), while (18) and
\(a_A+a_B\le2f_Q(1/2)<2(1.20752)\) give
\[
 \frac{167}{200}\sin\alpha<.21504.
\]
Since
\(\sin(.27)\ge.27-.27^3/6>.258\), it follows that
\[
                         0\le\alpha<.27.                       \tag{20}
\]

Retain the same original hard mixed owners DE3 and EH1, with
E nonpositive and its frame between D and H:
\[
 \delta,\epsilon\ge0,\quad\delta+\epsilon=\alpha,
\]
\[
 a_D+a_E\sin\delta+b_E\cos\delta\ge W(\delta),\qquad
 a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge W(\epsilon).
\]
Fix the non-E data and minimize E's own corner within the actual
containing circle. If \(\alpha=0\), the mixed sum contradicts
(19). For \(\alpha>0\), the argument in that earlier E note,
now using \(\tan(\alpha/2)<.137\) and
\(\cos(\alpha/2)>.99\), gives at every relaxed feasible E point
\[
 a_E-\frac12>
 [\, .718-1.4(.137)\,](.99)>.52.
\]
Thus \(a_E>1.02>b_E\), so neither the diagonal nor the core
primary boundary can minimize. The one-contact directions from
the earlier note remain valid because \(\delta<.27<\pi/4\).

At an interior two-contact point the exact same orientation
function (12)--(14) of that note applies. Its cotangent
factorization, with \(\alpha<.27\) in place of .22, gives
\[
\begin{split}
 \sin\alpha\,q_E''
 &<5(.135)+2(.135)^2+2(.27)+2
                        -4(1-.27^2/2)\\
 &=-\frac{2411}{4000}<0.
\end{split}
\]
Consequently this larger necessary class still has an E minimizer
on one of the three boundaries
\[
                  b_E=0,\qquad\delta=0,\qquad\epsilon=0.       \tag{21}
\]
Every retained A/B corner value, including an earlier strict loss,
is unchanged by this E minimization.

Unlike the fully aligned theorem, (21) does not yet exclude the
E-zero or epsilon-zero alternatives: those endpoint systems may
still carry a negative noncanceling outer error. They are genuine
remaining cases. This note supplies continuous signed transport,
order restoration and a shared variational reduction only in the
precise owner and frame classes stated above.

