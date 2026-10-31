# The entire tilted double-axis family has one of three B features and a positive upper mean

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_TILTED_DOUBLE_AXIS_FEATURE_RECOVERY_BLOCK_2026_10_26.md. No old review is
asserted for the present text.

Keep the original component A--B--V--C--U--A and genuine S leaf L,
all original forces and actual normals, true degrees, physical masks,
individual radial corner weights, both actual root means and both
transmitter sliders, and all nine physical unit squares.
This source covers exactly the original tilted double-axis feature
\[
m=f_2,\qquad n=f_1.
\]
Neither normal nor either mean is reselected.

## 1. Exact linked means and the whole endpoint domain

Use S_LEAF_C5_TILTED_FAR_ENDPOINT_RADIAL.md and
S_LEAF_C5_TILTED_DIRECT_AND_CHANNEL_HALFPLANES.md. In their global
leaf frame, \(L=[d,d+1]\times[-1/2,1/2]\), \(d=1+\delta\),
\(0<\delta<1/60\), and
\[
R^2=(d+1)^2+1/4\le1105/256,\qquad
f_1=(-a,-b),\quad f_2=(-b,a).
\]
The actual support equality for \(n=f_1\) gives
\[
D:=da=1-\delta,\qquad h:=db=2\sqrt\delta,\qquad H=1-h>37/50.
\tag{1}
\]
Here \(a^2+b^2=1\), \(a>59/61\), \(0<b<16/61\), and
\(h<13/50\).

Let the actual root concurrence be \((q_A,0)\) in the global frame.
Its proven positive sign and the two original axis lines give
\[
0<q_A\le d,\qquad
Y=b(d-q_A),\quad Z=a(d-q_A),\quad
T=h-Y=bq_A,\quad p=D-Z=aq_A.
\tag{2}
\]
The nonnegative means imply the weak upper endpoint \(q_A=d\).
It is retained: it has \(Y=Z=0\). Neither mean is independently
varied in the argument.

In the reflected root basis \((a,b),(b,-a)\), the actual squares
and applications are
\[
\begin{gathered}
A=[-\delta,1-\delta]\times[-H,h],\qquad
C=[-d-1,-d]\times[-1/2,1/2],\\
p_{AU}=(-\delta,T),\quad p_{CU}=(-d,T),\quad
F=p_{AB}=(p,-H),\quad Q=p_{CV}=(-d,-1/2),\\
G=p_{BV}=Q+g,\qquad g=(u,-v),\qquad
u,v>0,\quad u^2+v^2=1.
\end{gathered}
\tag{3}
\]
The signs in (3) are the actual radial-C return signs, not a new
reflection at B. Both loaded endpoints have the nonparallel proper
positive concurrences established in the far-endpoint theorem.

We prove that the complete B cover is:

| Original direct support at B | Physical B mask | Actual return |
| --- | --- | --- |
| Horizontal top face, with its full original mean | Unique lower-right circle corner | Strict upper-left vertex |
| Strict top vertex | Unique right-adjacent circle corner | Strict left-adjacent vertex |
| Strict top vertex | Radial right face, both corners and weights retained | Strict left-adjacent vertex |

Throughout all three rows,
\[
p>1/2,\qquad q_A>d/2,\qquad T>\sqrt\delta.
\tag{4}
\]

## 2. Horizontal B: complete physical mask and a single mean equation

If the original direct normal is a side axis of B, write
\[
B=[K-1,K]\times[-H-1,-H],\qquad F=(p,-H).
\tag{5}
\]
The positive concurrence on the line \(X=p>0\) forces the circle
resultant to have positive horizontal coordinate. Since \(H>0\),
the bottom corners are farther out than their corresponding top
corners. Thus a unique circle corner must be \((K,-H-1)\), and
comparison with the other bottom corner gives \(K>1/2\).
A radial horizontal B would instead have \(K=1/2\) and inward face
height H=d, impossible because H<1<d. These observations exhaust
the physical masks of the actual axis-aligned square.

The original positive return direction \((u,-v)\) has its unique
minimum on B at
\[
G=(K-1,-H),\qquad u=K+\delta,\qquad v=1/2-h.
\tag{6}
\]
Consequently \(K<1\). The actual circle equation and unit reserve
are
\[
K^2+(2-h)^2=(d+1)^2+1/4,\qquad
(K+\delta)^2+(1/2-h)^2=1.
\]
Subtracting and using \(\delta=h^2/4\) gives the exact identity
\[
\frac12=3h+4\delta+2\delta^2+2\delta K.
\tag{7}
\]
In particular \(h<1/6\). If \(h\le3/20\), then K<1 would give
\[
\frac12<3h+\frac32h^2+\frac18h^4
\le\frac12-\frac{20719}{1280000},
\]
a contradiction. Hence
\[
\frac3{20}<h<\frac16,\qquad
\frac13<v<\frac7{20},\qquad H>\frac56.
\tag{8}
\]
The exact squared comparison
\[
1-(7/20)^2-(281/300)^2=\frac7{45000}>0
\]
gives \(u>281/300\). Since \(\delta<1/144\),
\[
K>\frac{3347}{3600}>\frac{13}{14},\qquad
\frac{3347}{3600}-\frac{13}{14}=\frac{29}{25200}.
\tag{9}
\]
Also \(r:=v/u<1\), and \(r>v>1/3\).

The actual top mean is \(\zeta=p+1-K\in[0,1]\). It is in fact
positive because p>0 and K<1. The proper positive concurrence has
both unchanged descriptions
\[
q_B=\frac pK(K,-H-1)
=(K-1,-H)+\frac{\zeta}{u}(u,-v).
\]
Thus its exact scalar equation is
\[
p(H+1)=K\{H+(p+1-K)r\}.
\tag{10}
\]
Its denominator \(H+1-Kr\) is positive. Solving (10), the sign
of \(2p-1\) is the sign of
\[
(2K-1)H-1+K(3-2K)r.
\]
Here \(K(3-2K)\ge1\), since
\(K(3-2K)-1=(1-K)(2K-1)\ge0\). Equations (8)--(9) give the
uniform strict lower bound
\[
\frac57-1+\frac13=\frac1{21}>0.
\tag{11}
\]
Therefore p>1/2 throughout the entire original mean interval,
including \(\zeta=1\) whenever physically realized.

## 3. Strict top vertex: exhaustive return and circle alternatives

If the original direct normal is strict at B, its actual inward
sides have the unique chart
\[
e=(k,-l),\quad w=(-l,-k),\quad
k,l>0,\quad k^2+l^2=1,\qquad
B=F+[0,1]e+[0,1]w.
\tag{12}
\]
The equality endpoints k=0 or l=0 are already the original
horizontal owner feature in Section 2.

Because \(g\cdot e=uk+vl>0\), the full return support is F,
the side \(F+[0,1]w\), or \(F+w\).
Also F is strictly inside the circle:
\[
|F|^2\le D^2+H^2<d^2+1<R^2.
\]
The left-adjacent corner F+w cannot be a circle point, because
adding e increases its squared norm by \(2(pk+Hl)+1>0\).
Thus the unique-circle alternatives are F+e and F+e+w.
For physical radial B, an outward axis w would put
\(F=dw-e/2\) at negative horizontal coordinate. Hence its only
possible mask is the right face
\[
F=de-w/2,\qquad\text{circle corners }F+e,\ F+e+w.
\tag{13}
\]
Both individual circle weights, including zero endpoints, remain.

First the coincident return G=F is impossible. Proper nonparallel
concurrence would make F a positive multiple of its circle resultant.
For unique z=F+e, this gives \(F\cdot w=0\); the actual corner z+w
then has squared norm \(R^2+1\). For unique z=F+e+w, it gives
\[
|F|=R-\sqrt2<133/64-7/5=217/320<37/50<H\le|F|.
\tag{14}
\]
The fixed squared and rational reserves are \(9/4096\), \(1/25\),
and \(99/1600\), respectively.
For (13), collinearity with a positive radial resultant
\((d+1)e+\omega w\), \(|\omega|\le1/2\), would require
\(\omega=-(d+1)/(2d)<-1/2\).

The remaining whole return interval is therefore
\[
G=F+\zeta w,\qquad 0<\zeta\le1,\qquad
u=p+d-\zeta l,\quad v=H-1/2+\zeta k.
\tag{15}
\]
It is strict with \(\zeta=1\) when \(g\cdot w<0\); otherwise
\(g=e\) and \(\zeta\) is the original full side mean.
An endpoint mean at a vertex keeps its owner label.

## 4. The opposite unique circle cannot occur

Suppose z=F+e+w is unique. Put
\[
A_*=z\cdot e>1/2,\quad B_*=z\cdot w>1/2,\quad q_B=\tau z,\quad\tau>0.
\]
The unchanged proper lines give
\[
q_B=F+\sigma(0,-1)=F+\sigma(le+kw),\quad \sigma\ge0,
\qquad q_B=G+\frac{\zeta l}{u}g.
\tag{16}
\]
Since \(g\cdot w\le0\), the w coordinate gives \(\tau\le1\).
Equality would force \(\zeta=1,g=e\); the horizontal coordinate
then gives k=l, whereas (15) gives \(l=H-1/2+k>k\).
Thus
\[
\tau<1,\quad k>l,\qquad
(1-\tau)(A_*-B_*)=\sigma(k-l)\ge0,\quad A_*\ge B_*.
\tag{17}
\]
No concurrence is assumed to lie inside the body.

For a strict return, \(\zeta=1\), so v<1 and (15) give
\(k<1/2+h<19/25\). Equations (17) give
\(k>1/\sqrt2>7/10\) and \(l>16/25\).
The actual circle corner consequently has vertical magnitude
\[
H+k+l>37/50+7/10+16/25=52/25>133/64>R,
\]
with final rational gap \(3/1600\), a contradiction.

For an owned return, g=e and \(G=Q+e\), so
\[
A_*=2-dk+l/2<2-k+l/2
\le2-\frac1{2\sqrt2}<\frac53.
\tag{18}
\]
For fixed S, the function
\[
f(A,S)=(A-1)^2+(\sqrt{S-A^2}-1)^2
\]
has derivative \(2A/\sqrt{S-A^2}-2\) and is nondecreasing
for \(A\ge\sqrt{S/2}\). Apply (17), increase A to 5/3 at the
actual \(S=R^2\), and then increase S to \(15541/3600\).
The latter derivative \(1-1/\sqrt{S-A^2}\) is positive, since
\(S-A^2\ge53/36>1\). The remaining square root is between
1 and 5/4, with squared reserve 7/300. Hence
\[
|F|^2=f(A_*,R^2)<\frac49+\frac1{16}=\frac{73}{144}
<(37/50)^2<H^2\le|F|^2.
\tag{19}
\]
The last fixed reserve is \(3659/90000\).
This excludes every owned opposite mean as well.

## 5. The right circle face and the original q bound

Only the unique adjacent circle z=F+e or radial face (13) remains.
Comparison with its actual second corner gives
\[
pl-Hk\ge1/2,\qquad p>1/2.
\tag{20}
\]
If the actual return were owned, g=e and (15) would give
\[
p+d=k+\zeta l\le\sqrt2,
\]
whereas \(p+d>3/2>\sqrt2\). Therefore the actual return is
strict:
\[
G=F+w,\qquad ul>vk.
\tag{21}
\]
For the physical unique mask one may additionally use properness
at its circle corner to obtain \(u(l-k)>v(k+l)\); that stronger
inequality is not needed to prove the feature cover.

The coordinate of z along e is at most d+1 because its absolute
transverse circle coordinate is at least one half. Therefore
\[
p^2+H^2=R^2-2z\cdot e+1\ge d^2+1/4.
\tag{22}
\]
This includes the radial equality without changing either weight.

Sections 2 and 5 prove p>1/2 for every original B feature.
Since \(p=aq_A\) and \(ad=1-\delta<1\), it follows that
\[
q_A>d/2,\qquad T=bq_A>bd/2=\sqrt\delta.
\]
This proves (4) with the full linked-mean endpoint \(q_A=d\)
retained. The result is an exact feature and parameter reduction;
it does not assert that the six-body core is impossible.

