# A tilted strict root contact cannot be strict at B

Date: October 26, 2026.

**Recovery status: newly reconstructed, with a shorter whole-domain
proof; fresh independent full-source review passed in
REVIEW_TILTED_DIRECT_VERTEX_AND_UNIFORM_LONG_C6_RECOVERY_2026_10_26.md.
Root integration remains separate.** Historical review of a missing
previous file is not acceptance evidence for this version.

This source excludes the full original tilted S-leaf C5 load-13
feature with u>0 at the root and a strict original direct normal at
B. It keeps both original channel forms, every actual return
support and mean, both transmitter sliders, all physical circle
masks and weights, and all nine physical units.

## 1. Original chart and the entire physical circle cover

Use the surviving accepted tilted far-endpoint and direct/channel
half-plane theorems. In the actual orthonormal root frame, with
the circle origin unchanged,

\[
\begin{gathered}
d=1+\delta,\quad0<\delta<1/60,\quad
R^2=(d+1)^2+1/4\le1105/256,\\
D_0=da,\quad h=db,\quad E=1-D_0,\quad H=1-h,\\
a^2+b^2=1,\quad a>59/61,\quad0<b<16/61,\\
P=p_{AB}=(E,H),\quad m=(u,v),\quad0<u\le v,\quad u^2+v^2=1,\\
n=(x,-t),\quad x>0,\quad t\ge0,\quad x^2+t^2=1,\quad
Ex+ht=\delta,\\
Q=p_{CV}=(dx+t/2,-dt+x/2).
\end{gathered}
\tag{1}
\]

The original V channel has reserve one. For its unchanged unit
direction g from C to B,

\[
                         g\cdot(z-Q)\ge1\quad(z\in B).
\tag{2}
\]

The support equation gives

\[
-\delta\le E\le\delta,\quad h^2\le4\delta<1/15,\quad
h<13/50,\quad H>37/50.
\tag{3}
\]

For completeness, E>delta would give
\(h^2=d^2-(1-E)^2>4\delta\); both E and h would exceed
delta, contrary to \(Ex+ht=\delta\) and \(x+t\ge1\).

Every point of a physical radial square has norm at least d.
But
\[
|P|^2=d^2+2-2d(a+b)<d^2,
\]
so B is unique. Also
\[
|P|<\sqrt{1+1/3600}<1+1/7200,\qquad R>103/50.
\]
No adjacent vertex of B can be a circle point, since its norm
would be at most \(|P|+1<R\). P itself is strictly inside.
Thus the physical unique circle corner is necessarily the
opposite vertex:
\[
                        B=P+[0,1]e+[0,1]w,\qquad z=P+e+w.
\tag{4}
\]
This is the entire physical cover in the feature under study.

The retained far-endpoint theorem proves that B's two actual
forces are nonparallel. Lemma 1.1 of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md therefore gives a proper
positive unique concurrence inside B:

\[
                  q_B=\tau z=P+\lambda m,\qquad
                  0<\tau\le1,\quad\lambda\ge0.
\tag{5}
\]

In fact lambda is positive. If it were zero, P would be a
positive multiple of its opposite circle corner, hence
\[
|P|=R-\sqrt2<133/64-7/5=217/320<37/50<H,
\]
a contradiction. The fixed comparisons use
\((133/64)^2-1105/256=9/4096>0\).

The actual root concurrence \(q_A>0\) lies on the original
genuine-leaf ray. Its absolute root-frame coordinates are
\((-a q_A,-b q_A)\), and its direct coefficient is positive.
Thus
\[
\det(P,m)=-q_A(av-bu)<0,\qquad Hu-Ev>0.
\tag{6}
\]
This uses a>b, u<=v and v>0; it is not a properness assumption
at a fictitious root circle load.

## 2. The original B orientation has one small nonnegative angle

Write S=z-P=e+w. Equation (5) says
\[
                     \tau S=(1-\tau)P+\lambda m.
\tag{7}
\]
Since \(H>|E|\), \(v\ge u>0\), and lambda>0, (7) gives
\[
S_y-S_x\ge0,\qquad S_y+S_x>0.
\]
After interchanging the two actual inward sides if necessary,
their exact representation is therefore
\[
 e=(k,p),\qquad w=(-p,k),\qquad
 k>0,\quad p\ge0,\quad k^2+p^2=1.
\tag{8}
\]
Indeed k=(S_x+S_y)/2, p=(S_y-S_x)/2, and the two inward sides
of a unit square with sum S are precisely the vectors in (8).

Equations (5),(6), with lambda>0, give
\[
0>\det(P,z)=-(H-E)k+(H+E)p,\qquad
\frac pk<\frac{H-E}{H+E}<\frac{11}{10}.
\tag{9}
\]
The last comparison follows from \(H>37/50>21\delta\).

We first have p<k. Otherwise \(1\le p/k<11/10\), and
\[
k+p\ge\frac{21}{\sqrt{221}}>\frac75.
\]
The squared reserve for the last comparison is \(196/5525\).
Then
\[
z_y=H+k+p>107/50>133/64>R,
\]
impossible. The middle rational gap is \(99/1600\).
Consequently \(0\le p<k\).

For fixed E,H the squared norm of the opposite corner is
\[
f(p)=E^2+H^2+2+
 2\big((E+H)\sqrt{1-p^2}+(H-E)p\big).
\tag{10}
\]
Its derivative has the sign of
\((H-E)-(H+E)p/\sqrt{1-p^2}\).
By (9), it is positive all the way from zero to the actual p.
This monotonicity is on a connected full interval.

Two useful consequences follow.

First, h>1/10. Otherwise H>=9/10, and
\[
R^2=f(p)\ge f(0)
=(E+1)^2+(H+1)^2>
(59/60)^2+(19/10)^2>1105/256.
\]
The final exact gap is \(15007/57600\). Therefore the original
support equation gives
\[
 ht\le\delta(1+x)<1/30,\qquad t<1/3.
\tag{11}
\]
This also includes t=0 and its full original A-side mean.

Second, p<1/4. Otherwise monotonicity of f gives
\[
\begin{split}
R^2&\ge f(1/4)\\
&>(\sqrt{15}/4-4/15)^2+
  (\sqrt{15}/4+99/100)^2\\
&>(841/1200)^2+(783/400)^2>1105/256.
\end{split}
\]
Here \(\sqrt{15}>387/100\), with squared reserve \(231/10000\);
the last gap is \(9457/1440000\). Hence
\[
                         p<1/4,\qquad k>29/30.
\tag{12}
\]
For k the squared reserve is \(15/16-(29/30)^2=11/3600\).

## 3. One actual B corner violates the original reserve-one support

Use the actual adjacent corner
\[
                          W=P+e=(E+k,H+p).
\tag{13}
\]
It satisfies
\[
                  19/20<W_x<61/60,\qquad37/50<W_y<1.
\tag{14}
\]
Only the upper height needs proof. If W_y>=1, then
\[
z_x=E+k-p>7/10,\qquad z_y=W_y+k>59/30,
\]
so
\[
R^2>(7/10)^2+(59/30)^2>1105/256.
\]
The fixed squared gap is \(2383/57600\), a contradiction.

Equation (11) gives \(x>\sqrt{8/9}>14/15\). Therefore the
unchanged C application in (1) satisfies
\[
                  14/15<Q_x<71/60,\qquad23/180<Q_y\le1/2.
\tag{15}
\]
From (14),(15),
\[
|W_x-Q_x|<7/30,\qquad0<W_y-Q_y<157/180.
\]
Consequently
\[
|W-Q|^2<(7/30)^2+(157/180)^2
=\frac{26413}{32400}
=1-\frac{5987}{32400}<1.
\tag{16}
\]

But W is an actual point of B, so (2) requires
\[
1\le g\cdot(W-Q)\le|W-Q|<1.
\]
This contradiction excludes the entire stated direct-vertex feature.

Nothing about the return support feature was selected: its exact
original normal only enters through the necessary support inequality
(2). No return mean, transmitter slider, individual radial weight,
force or physical unit was discarded. Together with the separately
reconstructed tilted direct-side-owner theorem, this covers all
original u>0 tilted root contacts. The u=0 family and the original
S-leaf parent gate require their separate completion assembly.
