# The entire double-axis unique-right B-C pocket is empty

Date: October 26, 2026.

**Status: complete at its stated scope; independently reviewed and
accepted in the current S-leaf proof chain.** See
REVIEW_S_C5_DOUBLE_AXIS_STRIP_CENTRAL_BC_RECOVERY_BLOCK_2026_10_26.md.

Keep the entire original tilted double-axis feature \(m=f_2,n=f_1\),
its two linked root means, all positive forces and original normals,
true degrees, the actual physical-unique right-circle B mask, both
individual radial C weights, both U,V sliders and all nine units.
The physical radial B row has its separate accepted two-radial
endpoint cap exclusion.

Apply S_LEAF_C5_TILTED_DOUBLE_AXIS_B_FEATURE_REDUCTION.md. In its
unchanged reflected root frame,
\[
\begin{gathered}
d=1+\delta,\quad0<\delta<1/60,\quad h=2\sqrt\delta<13/50,\quad
D=1-\delta,\quad H=1-h,\\
R^2=(d+1)^2+1/4,\quad
A=[D-1,D]\times[-H,h],\quad F=(p,-H),\quad p=D-Z>1/2,\\
Q=(-d,-1/2),\quad g=(u,-v),\quad
u,v>0,\quad u^2+v^2=1,\\
e=(k,-l),\quad w=(-l,-k),\quad k,l>0,\quad k^2+l^2=1,\\
B=F+[0,1]e+[0,1]w,\quad G=F+w=Q+g,\qquad z=F+e,\quad |z|=R.
\end{gathered}
\tag{1}
\]
Here \(0\le Z<1\), including the original endpoint Z=0 linked
to the other root mean. In particular p<=D; strictness is not used.

## 1. Exact properness and a uniform direction bound

The original concurrence has
\[
q_B=(p,-H-k-lv/u)=\tau z,\qquad \tau=p/(p+k)\in(0,1).
\]
In outward channel direction \(N=(-v,-u)\), the actual line has
positive height \(H_c=dv+u/2\). Since \(N\cdot q_B=N\cdot G=H_c\),
\[
N\cdot(z-G)=(1-\tau)H_c/\tau>0.
\]
Equivalently,
\[
u(l-k)>v(k+l),\qquad u>v,\qquad l>k.
\tag{2}
\]
Equating the two concurrence coordinates gives the exact torque
identity
\[
p\{l(u-v)-uk\}=k\{u(H+k)+vl\}.
\tag{3}
\]
The actual vertical channel and adjacent-circle equations give
\[
k=h-\frac12+v,\qquad
p^2+H^2\ge d^2+\frac14,\qquad
p^2>\frac14+2h-\frac12h^2.
\tag{4}
\]
For the last strict comparison use
\(d^2-1=h^2/2+h^4/16>h^2/2\).

We claim v>2/5 on the whole domain. Suppose v<=2/5. Then
\[
h>1/10,\quad k\le h-1/10<4/25,\quad H+k=1/2+v\le9/10,
\quad u>9/10,\quad l>49/50.
\tag{5}
\]
The last two squared reserves are \(3/100\) and \(7/500\).
The increasing lower bound in (4) gives
\[
p^2>89/200>4/9,\qquad p>2/3,
\]
with rational reserve \(1/1800\).
The left side of (3) is consequently greater than
\[
\frac23\left(\frac{49}{50}\frac12-\frac4{25}\right)=\frac{11}{50},
\]
whereas its right side is less than
\[
\frac4{25}\left(\frac9{10}+\frac25\right)=\frac{26}{125}.
\]
Their difference is \(3/250>0\), a contradiction. Thus
\[
\frac25<v<\frac1{\sqrt2}.
\tag{6}
\]
This uses one complete parameter range, without splitting means
or isolating roots.

## 2. The entire actual cap has uniform coordinates

Use \(g=(u,-v)\) as the horizontal channel direction and N as its
outward vertical direction. The original contact points become
\[
Q=(x_G-1,H_c),\quad G=(x_G,H_c),\qquad
H_c=dv+u/2,\quad x_G=1-du+v/2.
\tag{7}
\]
Equation (6) gives
\[
\frac67<H_c<\frac{13}{12},\qquad
\frac4{15}<x_G<\frac23.
\tag{8}
\]
For clarity, the lower height follows from the increasing function
\(v+\sqrt{1-v^2}/2\):
\[
H_c>\frac25+\frac{\sqrt{21}}{10}>\frac67,
\]
with squared reserve \(21-(32/7)^2=5/49\).
The upper bound follows from
\(H_c<(d+1/2)/\sqrt2<(91/60)(5/7)=13/12\).
The function \(1-d\sqrt{1-v^2}+v/2\) increases; hence
\[
x_G>\frac65-\frac{61\sqrt{21}}{300}>\frac4{15},
\]
with fixed integer square reserve \(280^2-61^2\cdot21=259\).
Its upper bound is \(x_G<1-1/(2\sqrt2)<2/3\).

## 3. Both actual root-entry faces force the original V slider outward

The actual transmitter, with its unchanged \(-1/2\le\sigma\le1/2\),
is
\[
V=[x_G-1,x_G]\times
[H_c+\sigma-1/2,H_c+\sigma+1/2].
\tag{9}
\]
Put
\[
\Delta=Z+l-1,\qquad M=\max(k/u,\Delta/v).
\tag{10}
\]
In the original root frame the ray from G toward A is
\[
G-\rho N=(p-l+\rho v,-H-k+\rho u).
\]
Its bottom-face entry time is k/u and its left-face entry time
is \(\Delta/v\); the latter may be negative. Both actual entries
are retained by the maximum.

We prove \(H_c-M>7/20\). From \(h<13/50\), (4) and (6),
\(k<v-6/25\) and \(u>1/\sqrt2\), so
\[
H_c-\frac ku>
v+\frac12\sqrt{1-v^2}-\sqrt2(v-6/25).
\]
This decreases for \(2/5\le v\le1/\sqrt2\); its minimum is
\(99\sqrt2/100-1>193/500>7/20\). The final reserve is
\(9/250\), using \(\sqrt2>7/5\).

For the other entry time, the exact channel-coordinate identity is
\[
H_c-\Delta/v=(u/v)x_G-(D-1)/v=(u/v)x_G+\delta/v.
\tag{11}
\]
If \(v\le1/2\), then \(u/v\ge\sqrt3>3/2\), so (8) makes
(11) greater than \(2/5>7/20\).
If \(v\ge1/2\), then \(u\le\sqrt3/2<7/8\), whence
\[
x_G>\frac54-\frac{61}{60}\frac78
=\frac{173}{480}>\frac7{20},
\]
with reserve \(1/96\). Since u/v>1, (11) again exceeds 7/20.
The common endpoint v=1/2 is covered by both comparisons.
Consequently
\[
H_c-M>7/20,\qquad 0<M<11/15<1.
\tag{12}
\]

At a left-face entry, the height above A's bottom is
\(uM-k\in[0,1)\). At a bottom-face entry, its horizontal coordinate
is \(p-l+vk/u<p\le D\), by (2); the maximum in (10) places it
at or to the right of A's left face. Just beyond M the ray
therefore enters the actual root interior, including an exact
lower-left-corner tie.

If the actual V bottom extended farther inward, its actual right
edge would meet \(A^\circ\), and a neighborhood of that point
would meet \(V^\circ\). The original nonoverlap thus forces
\[
\sigma\ge1/2-M.
\tag{13}
\]
No sign of sigma was assumed.
Equations (8)--(9),(12)--(13) give
\[
V_{\rm top}>27/20,\qquad V_{\rm bottom}\le H_c<7/6.
\]
Its horizontal interval strictly contains \([-4/15,4/15]\).
Thus the actual occupied transmitter contains
\[
[-4/15,4/15]\times\{27/20\}\subset V^\circ.
\tag{14}
\]

## 4. Every whole actual return-pocket extra overlaps V

S_LEAF_C5_RADIAL_BC_POCKET_CAPACITY.md gives the complete actual
B--V--C cap routing, with the genuine root and leaf unchanged.
Every whole extra there lies beyond the line of height Hc.
Its center therefore has
\[
Y\ge H_c+1/2>19/14,\qquad |c_E|<91/60.
\]
The latter is the sharp universal center bound \(d+1/2<91/60\)
in the original radius window. It follows that
\[
|X|<41/60,\qquad Y<91/60,
\]
with exact squared reserve \(5/588\) for the horizontal comparison.
Its distance to the occupied segment (14) is less than
\[
\sqrt{(41/60-4/15)^2+(91/60-27/20)^2}
=\sqrt{29/144}<1/2.
\]
Its open inscribed disk meets \(V^\circ\), contradicting the
physical packing; the squared reserve is \(7/144\).
Hence \(n_{BC}=0\) throughout the original double-axis unique
top-vertex row.

All original mean endpoints and both actual V-slider endpoints
were retained. The conclusion concerns the whole physical pocket
and all orientations of a possible extra, not a selected center
sector or an isolated core diagnostic.

