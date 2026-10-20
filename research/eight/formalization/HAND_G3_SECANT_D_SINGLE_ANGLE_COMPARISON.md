# The secant D force with one remaining actual angle

## 1. A uniform signed-angle estimate

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,\quad K=13/12,
 \quad c_0=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2,
\]
and use the actual sorted outer-circle support
\[
 S(f,g)=\max_{0\le b\le c_0}
 \left[f\left(\sqrt{Q-(b+1/2)^2}-1/2\right)+gb\right].
\tag{1}
\]
The support branches and their matching first derivatives are
given in [the sorted-D lemma](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md).
Write
\[
 W(t)=(1+\cos t+|\sin t|)/2,
\]
\[
 V_{k,1}(n)=\cos n-1
 -R\left(\sqrt{1+k^2-2k\sin n}-\sqrt{1+k^2}\right).
\tag{2}
\]
Assume throughout
\[
 1\le q\le\sec h<1.308,\qquad .862\le c\le1.2,
 \qquad 1/2\le k\le\min(c,.85).
\tag{3}
\]
For the remaining actual D angle t, define
\[
 \Delta(q,c;t)=c\{W(t)-1\}+S(q,c)
                         -S(q+c\sin t,c\cos t).
\tag{4}
\]
Then, on the entire signed interval,
\[
 \boxed{\quad
 \Delta(q,c;t)\ge
 \begin{cases}
  -.545\max(q,c)t,&0\le t\le h,\\
  V_{k,1}(-t),&-h\le t\le0.
 \end{cases}\quad}
\tag{5}
\]
All terminating decimals denote exact rational constants.
This estimate is for one actual angle, with its original sign.
It makes no assertion that a geometric angle can be changed.

For the positive case with \(c\le q\), the zero-angle support
is the interior branch: \(c/q>.659>1/[2(a_0+1/2)]\).
Replacing only the final support in (4) by the full-circle
upper bound gives
\[
 \Delta(q,c;t)\ge U_{c,q}(t),
\]
where U is the ordinary positive increment from
[the scalar envelopes](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
Its whole-interval estimate \(U_{p,r}(t)\ge-.545rt\), for
\(p/r\ge1/2\), proves (5).

If \(c\ge q\), divide (4) by c and put r=q/c. The expression is
\[
 W(t)-1+(r+1)c_0-S(r+\sin t,\cos t).
\tag{6}
\]
Its derivative in r is \(c_0-a_{\rm support}\le0\), since every
sorted outer support point has \(a\ge c_0\). At r=1 it is
exactly \(U_{1,1}(t)\): the force ratio
\(\cos t/(1+\sin t)>.46\) is above the axis cutoff.
Thus (6) is at least \(U_{1,1}(t)\), proving the other positive case.

For \(t=-n\le0\), first vary q while holding c,n fixed.
The final force has positive first coordinate, since
\(q-c\sin n\ge1-1.2(.645)>0\). Also
\[
 \frac{c\cos n}{q-c\sin n}\ge\frac cq,
 \qquad
 \frac cq\ge\frac{.862}{1.308}>\tan(h/2).
\tag{7}
\]
The selected a coordinate of a sorted support point decreases
as the force ratio g/f increases. Consequently
\[
 \partial_q\Delta(q,c;-n)
 =a_{\rm support}(q,c)
       -a_{\rm support}(q-c\sin n,c\cos n)\ge0.
\tag{8}
\]
The support is continuously differentiable through both
endpoint transitions, so this also proves global monotonicity.
It suffices to set q=1.

If \(c\le1\), the full-circle comparison gives
\[
 \Delta(1,c;-n)\ge c(\cos n-1)
 -R\left(\sqrt{1+c^2-2c\sin n}-\sqrt{1+c^2}\right)
 \ge V_{c,1}(n)\ge V_{k,1}(n).
\tag{9}
\]
The last comparison is the proved monotonicity of V in its
smaller coefficient. If \(c\ge1\), both actual supports at
q=1 are diagonal, and
\[
 \Delta(1,c;-n)
 =c\{(c_0+1/2)\sin n+(c_0-1/2)(1-\cos n)\}.
\tag{10}
\]
Its derivative in n is greater than 1.327c, by the endpoint
calculation in Section 2 of the sorted-D lemma. On the other
hand V is concave and
\[
 V'_{k,1}(n)\le\frac{Rk}{\sqrt{1+k^2}}<1.284<1.327.
\tag{11}
\]
Positive squaring at k=.85 proves the middle strict bound.
Both sides vanish at zero. This finishes (5), including all
weak support ties.

## 2. The pure positive secant endpoint is increasing

For fixed c satisfying (3), define the exact negative-DE
secant gain
\[
 F_c(s)=\frac{\sec s-1}{2}+K\tan s
                  -\{S(\sec s,c)-S(1,c)\}.
\tag{12}
\]
For every fixed \(0\le\theta\le h\), the function
\[
 F_c(s)-.545\max(\sec s,c)(s-\theta)
\tag{13}
\]
is strictly increasing on \(\theta\le s\le h\). Thus the
positive-D lower alternative furnished by (5) is minimized
at the intrinsic equal-angle endpoint s=θ.

On a diagonal branch, \(c\ge\sec s\), put \(d_0=c_0-1/2<.4\).
Then
\[
 F'_c(s)=\frac{K-d_0\sin s}{\cos^2s}>1.045.
\tag{14}
\]
Indeed the quadratic numerator for this last inequality has
positive minimum because
\[
 4(1.045)(K-1.045)-.4^2=7/30000>0.
\]
The derivative of the subtracted term in (13) is at most
\(.545c\le.654\), so (13) increases on this branch.

On the interior branch, \(q=\sec s\ge c\), direct
differentiation gives
\[
 F'_c(s)=\sec^2s
 \left[K+\sin s-\frac{R\sin s}{\sqrt{1+c^2\cos^2s}}\right].
\tag{15}
\]
There is no axis branch under (3). After multiplication by
\(\cos^2s>0\), the derivative of (13) is at least
\[
 H_c(s)=K+\sin s-
 \frac{R\sin s}{\sqrt{1+c^2\cos^2s}}
                     -.545(\cos s+s\sin s).
\tag{16}
\]
This increases in c, so it is enough to take d=.862. Moreover
\[
 H'_d(s)=\cos s\left[
 1-.545s-\frac{R(1+d^2)}{(1+d^2\cos^2s)^{3/2}}\right]<0,
\tag{17}
\]
since the last fraction is at least \(R/\sqrt{1+d^2}>1\).
The single far endpoint has the strict rational bound
\[
                         H_d(h)>.00066.
\tag{18}
\]
Here is an explicit positive-square certificate for (18).
Let \(C_j,S_j\) be the usual cosine and sine Taylor polynomials
ending in degree j, evaluated at h, and set
\[
 A=K-.545C_{12}(h)+(1-.545h)S_{11}(h),
 \qquad D=1+d^2C_{10}(h)^2.
\]
Alternating Taylor bounds on [0,h] give
\[
 H_d(h)\ge A-\frac{R S_9(h)}{\sqrt D}.
\]
Exact rational expansion gives
\[
 A>1,\qquad
 (A-.00066)^2D-QS_9(h)^2>.0000082>0.
\tag{19}
\]
Both sides to be squared are positive, so (19) proves (18).
Equations (14)--(18) prove strict increase on each support
branch. The values in (13) agree at \(\sec s=c\); its one-sided
derivatives both have the proved positive lower bounds.
This proves the claim on the whole interval.

The statements here are local analytic ingredients for the
negative core-DE, positive-BT case. They do not by themselves
assert exclusion of that entire owner domain, nor do they
replace the other angle-concentration and endpoint obligations.
