# One radial channel, a horizontal return unit and its actual root force an empty cap

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_COMMON_HORIZONTAL_RETURN_CERTIFICATE_REDUCTION_RECOVERY_2026_10_26.md. This proof is a shorter common replacement for the
missing separate horizontal-return pocket arguments.

## 1. Complete physical statement

Let \(0<\delta<1/60\), \(d=1+\delta\), and
\(R^2=(d+1)^2+1/4\). Retain four actual interior-disjoint unit squares
A,B,V,C in the same disk, with
\[
\begin{gathered}
A=[D-1,D]\times[-H,1-H],\quad D\le d,\quad37/50<H<1,\\
B=[K-1,K]\times[-H-1,-H],\quad
z_B=(K,-H-1),\quad K>1/2,\quad |z_B|=R,\\
n=(-x,t),\quad f=(-t,-x),\quad
x>0,\ t\ge0,\ x^2+t^2=1,\\
C=[d,d+1]n+[-1/2,1/2]f,\quad
Q=dn+f/2,\quad G=(K-1,-H)=Q+g,\\
g=(u,-v)=-\alpha n+\beta f,\quad
u,v,\alpha,\beta>0,\quad u^2+v^2=\alpha^2+\beta^2=1.
\end{gathered}
\tag{1}
\]
V is the original side transmitter with its actual reserve one.
The unchanged root support and original proper direct mean satisfy
\[
(1-D)x+(1-H)t=\delta,
\tag{2}
\]
\[
0<p,\quad\zeta=p+1-K\in[0,1],\qquad
p(H+1)=K\left(H+\zeta\frac vu\right).
\tag{3}
\]
No individual radial circle weight or V transverse slider is prescribed.

Define the actual channel frame by g and \(N=(-v,-u)\), with
\[
h=d\beta+\alpha/2,\qquad z=1-d\alpha+\beta/2.
\tag{4}
\]
Then \(N\cdot G=h\), \(g\cdot G=z\).
**Theorem.** There is no further whole unit E in the same disk, disjoint
in interior from the actual A,B,V,C, and satisfying \(N\cdot E\ge h\).
Every inequality is for the entire unit, with arbitrary orientation.

## 2. The whole true-mean interval gives u >= v

First \(K<H+1\): otherwise the circle equation in (1) would give
\(R^2\ge2(H+1)^2>2(87/50)^2>15541/3600>R^2\).
The last bound is exactly \(d<61/60\) and the stated radius equation.

Substituting \(p=K-1+\zeta\) in (3) gives
\[
\zeta K(1-v/u)=(1-\zeta)(H+1-K).
\tag{5}
\]
If \(\zeta=0\), the positive right side is impossible. Thus
\(\zeta>0\), and (5) proves \(u\ge v\).
No endpoint \(\zeta=1\) or equality \(u=v\) is dropped.

## 3. The two actual circles force beta > 1/3

Subtract the actual circle equation of \(z_B=Q+g+(1,-1)\)
from \(R^2=(d+1)^2+1/4\), using the unchanged reserve-one equation.
The exact result is
\[
d(1+\alpha+x+t)
=1+\alpha(x+t)+\beta(x-t)+\frac{\beta+x-t}{2}.
\tag{6}
\]
Write \(x=\cos\theta,t=\sin\theta\), \(0\le\theta<\pi/2\).
At d=1, the left side minus the right side in (6) is
\[
F(\theta)=(1/2-\alpha-\beta)\cos\theta
 +(3/2-\alpha+\beta)\sin\theta+\alpha-\beta/2.
\]
Its derivative is strictly positive throughout this interval:
\(\alpha+\beta\ge1\) and \(3/2-\alpha+\beta>0\).
For the actual \(d>1\), (6) therefore implies
\[
0>F(\theta)\ge F(0)=\frac{1-3\beta}{2},
\qquad\boxed{\beta>1/3.}
\tag{7}
\]

From \(u\ge v\) and \(t\ge0\), the angle of g in this chart is at most
\(\pi/4\), so
\[
\alpha\ge u\ge1/\sqrt2,\qquad
1/3<\beta\le v\le1/\sqrt2,\qquad
u\le\alpha<2\sqrt2/3<33/35.
\tag{8}
\]
These follow equally by writing
\(u=\alpha x-\beta t,v=\alpha t+\beta x\);
the inequality \(\beta\le v\) follows since
\(v-\beta=t(\alpha-\beta t/(1+x))\ge0\).
The last fixed square comparison has reserve \(1/11025\).

The concavity of \(\beta+\frac12\sqrt{1-\beta^2}\) on
\([1/3,1/\sqrt2]\), evaluated at its two endpoints, gives
\[
h>\frac45,\qquad
h\le\sqrt{d^2+1/4}<\frac{23}{20}.
\tag{9}
\]
The lower endpoint uses \(\sqrt2>7/5\); the upper squared reserve is
\(7/180\).

Also \(z=1-d\sqrt{1-\beta^2}+\beta/2\) increases with beta. Hence
\[
z>\frac76-\frac{61\sqrt2}{90}>\frac15,
\tag{10}
\]
where the final comparison reduces to \(87^2-2\cdot61^2=127>0\).

Put \(s_1=u+v\), \(r_1=u-v\ge0\). The actual B circle equation,
now in the same channel frame, is exactly
\[
z(1+s_1)+h r_1=d.
\tag{11}
\]
Since \(v>1/3\) and \(u\ge v\), the positive unit-circle arc gives
\(s_1>(1+2\sqrt2)/3>5/4\). Consequently
\[
z<\frac{61/60}{1+5/4}=\frac{61}{135}<\frac12.
\tag{12}
\]
No root parameter is independently relaxed to obtain these bounds.

## 4. The actual V face must protrude into the outward cap

Put \(\eta=D-K\). Combining (2) with the actual relation \(G=Q+g\)
gives
\[
x\eta=1+t-\alpha>0,\qquad
v-u\eta=\frac{\beta-(1-\alpha)u}{x}>\frac1{30}>0.
\tag{13}
\]
The last inequality follows from (7), \(\alpha>7/10\), \(u<1\).
Thus \(\eta>0\) and \(u\eta/v<1\).

On V's actual right face, move inward from G in direction \(-N=(v,u)\).
At parameter \(\tau=\eta/v\), the point
\[
G-\tau N=(D-1,-H+u\eta/v)
\]
is in the interior of A's left side. A slightly larger parameter enters
\(A^\circ\). Write the original full V slider as \(\sigma\in[-1/2,1/2]\):
in the channel frame
\[
V=[z-1,z]\times[h+\sigma-1/2,h+\sigma+1/2].
\tag{14}
\]
If \(\sigma<1/2-\eta/v\), the actual right face of V would meet
\(A^\circ\), and a nearby point would belong to both interiors.
Thus original A--V nonoverlap forces
\[
\sigma\ge1/2-\eta/v.
\tag{15}
\]

The original point G also gives
\(\eta=D-1-uz+vh\). Therefore the actual upper face of V satisfies
\[
h+\sigma+1/2
\ge1+h-\eta/v
=1+\frac uv z-\frac{D-1}{v}
>\frac{19}{20}+z.
\tag{16}
\]
Here \(D-1\le\delta<1/60\), \(v>1/3\), and \(u/v\ge1\).
Its lower face is at most h, which is strictly less than
\(23/20<19/20+z\).
Consequently the entire fixed segment
\[
\Sigma=[z-1,z]\times\{19/20+z\}
\tag{17}
\]
lies in V, strictly between its two horizontal faces. The endpoints
are allowed to be on its vertical faces. Every original slider,
including either limiting face contact, has been retained.

## 5. A cap extra cannot have its center at or to the right of z

Suppose E is a whole unit beyond the actual cap line. Its center \((X,Y)\)
satisfies the exact center bound and halfwidth bound
\[
Y\ge h+1/2>13/10,\qquad
X^2+Y^2\le(d+1/2)^2<(91/60)^2.
\tag{18}
\]
Hence \(|X|<4/5\), with squared reserve \(107/3600\).

The actual B center is
\[
c_B=(z+s_1/2,h+r_1/2).
\]
Its first coordinate is greater than \(1/5+5/8=33/40>4/5\).
If \(X\ge z\), the horizontal center gap is at most \(s_1/2\).
The vertical gap is nonnegative and at most
\[
B_*-\frac{r_1}{2},\qquad B_*=d+1/2-h.
\]
Existence of the cap center gives \(h\le d\), hence
\(1/2\le B_*<43/60\). Thus
\[
|c_E-c_B|^2\le\frac12+B_*^2-B_*r_1.
\tag{19}
\]

If \(r_1\ge1/50\), this is strictly less than
\[
\frac12+(43/60)^2-(43/60)(1/50)
=1-\frac{13}{18000}<1.
\]
The expression increases with \(B_*\) on the stated interval because
\(2B_*-r_1>0\).

If \(r_1<1/50\), (11), \(h<23/20\), and \(s_1\le\sqrt2<10/7\)
give
\[
z>\frac{1-(23/20)(1/50)}{1+10/7}
=\frac{6839}{17000}>\frac25.
\]
Since the actual Q has channel coordinates \((z-1,h)\),
\[
h^2+(1-z)^2=d^2+1/4
\]
gives \(h>9/10\). Therefore \(B_*<37/60\), and (19) is
less than \(1/2+(37/60)^2=1-431/3600<1\).

Both cases contradict the necessary distance at least one between
centers of interior-disjoint unit squares. Therefore every possible
cap extra must have \(X<z\).

## 6. Its open incircle meets the actual forced V segment

For \(X<z\), the horizontal distance to the segment (17) is less than
\(3/10\): if X is left of it, use \(X>-4/5\) and \(z<1/2\).
By (10),(12),(18),
\[
\left|Y-(19/20+z)\right|<11/30.
\]
Indeed the upper difference is bounded by
\(91/60-23/20=11/30\), and the lower difference is smaller than
\(29/20-13/10=3/20\).
Thus
\[
\operatorname{dist}(c_E,\Sigma)^2
<(3/10)^2+(11/30)^2
=\frac14-\frac{23}{900}<\frac14.
\tag{20}
\]
The open radius-one-half incircle of E meets \(\Sigma\).
If the closest point is an endpoint, the strict inequality permits a
nearby point in the interior of V, because (17) is strictly between
its horizontal faces. This contradicts physical E--V nonoverlap.

The entire cap is empty. The proof uses the original direct mean only
through the exact proper identity (3), and the original root only through
its actual rectangle, support equation and forced V-face contact.
It does not alter a force or select a new normal, mean, circle corner,
transmitter slider or extra orientation.

