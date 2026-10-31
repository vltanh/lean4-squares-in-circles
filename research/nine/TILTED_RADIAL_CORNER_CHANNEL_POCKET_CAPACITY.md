# Four actual squares bound a tilted radial corner-channel pocket by two

Date: October 26, 2026.

**Recovery status: reconstructed complete geometric theorem; fresh
independent full-source review passed in
REVIEW_TILTED_DIRECT_VERTEX_AND_UNIFORM_LONG_C6_RECOVERY_2026_10_26.md.
Root integration remains separate.** The current proof combines the freshly
reviewed large-ratio comparison with a complete small-ratio proof
below. Historical reviews of missing manuscripts are not reused.

This theorem has no force, graph-degree, load-mask or direct-neighbor
premise. Its hypotheses are four actual unit squares and an explicitly
specified occupied crosscut. An application must establish those
geometric hypotheses without erasing any of its actual forces.

## 1. Exact four-square hypotheses

Let L,A,U,C be actual unit squares with disjoint open interiors,
contained in the closed disk \(D_R\). Suppose

\[
\begin{gathered}
d=1+\delta,\quad0<\delta<1/60,\quad
R^2=(d+1)^2+1/4\le1105/256,\\
p_0=(d,0),\quad L=[d,d+1]\times[-1/2,1/2],\\
f_1=(-a,-b),\quad f_2=(-b,a),\quad
a^2+b^2=1,\quad a>59/61,\quad0<b<16/61,\\
A=p_0+[0,1]f_1+[0,1]f_2,\qquad P=p_0+f_1,\\
n=x f_1-t f_2,\quad f=t f_1+x f_2,\quad
x>0,\quad t\ge0,\quad x^2+t^2=1,\\
C=[d,d+1]n+[-1/2,1/2]f,\quad
P+n=dn-Tf,\quad0<T<13/50,\quad[P,P+n]\subset U.
\end{gathered}
\tag{1}
\]

Both global components of n are negative. Thus, if
\(a=\cos\phi,b=\sin\phi,x=\cos\psi,t=\sin\psi\), then

\[
                  0<\theta:=\phi+\psi<\pi/2.
\tag{2}
\]

The t=0 endpoint is allowed only with the actual corner P in (1).
A general side mean \(P+Yf_2\) is not one of these hypotheses.

Join the following actual points in order:

\[
\begin{split}
z_C=(d+1)n-f/2,\quad dn-f/2,\quad P+n,\quad P,\quad p_0,\\
(d,-1/2),\quad z_L=(d+1,-1/2).
\end{split}
\tag{3}
\]

Every segment lies in C,U,A or L. The C segment has n projection
at least d, the open U segment has projection between delta and d,
and the root segment has projection at most delta. The U and C
pieces have global x coordinate below d, whereas the leaf pieces
have x at least d; the open root segment meets that line only at
p0. These facts make (3) an occupied simple crosscut, with harmless
zero-length or collinear pieces omitted.

Let \(\gamma=\arctan(1/[2(d+1)])\), and let \(\Omega\) be the closed
bounded side of (3) and the circle arc

\[
                     \pi+\theta+\gamma\le\vartheta\le2\pi-\gamma.
\tag{4}
\]

The arc has length in (0,pi). The theorem concerns additional
whole physical unit squares contained in this explicit region and
disjoint from the four actual squares.

**Theorem.** The region \(\Omega\) cannot contain three such
pairwise interior-disjoint unit squares. Its capacity is at most two.

## 2. Geometric identities and the complete ratio split

Taking projections in (1) gives

\[
\begin{gathered}
(1-da)x+dbt=\delta,\qquad
T=dbx+(da-1)t,\qquad Tx=db-\delta t,\\
d(bx+at)-T=t,\qquad
d(1+\cos\theta)=1+x .
\end{gathered}
\tag{5}
\]

No force equation is involved. Define the auxiliary geometric ratio

\[
                         \kappa=\frac{at}{bx+at}\in[0,1).
\tag{6}
\]

It is not assumed to be an application mean. The split
\(\kappa\ge1/4\) or \(\kappa\le1/4\) is exactly the split
\(3at\ge bx\) or \(3at\le bx\). Both include the equality.

Also every point of \(\Omega\) satisfies

\[
                 f_2\cdot(z-P)\le0,\qquad f\cdot(z-P)\le0.
\tag{7}
\]

For the path this follows directly from (3), \(T<1/2\),
\(f_2\cdot n=-t\), \(f\cdot(p_0-P)=-t\), and the signs of
both normals on the lower leaf segments. Their directions are
outside the southern arc (4), so the maximum of either linear
projection on that arc occurs at an endpoint. The bounded side
is in the convex hull of its boundary.

## 3. The whole large-ratio range \(\kappa\ge1/4\)

This is precisely the force-free geometry used in Sections 2--7
of S_LEAF_C5_TILTED_DIRECT_AXIS_STRICT_CHANNEL_LONG_POCKET.md.
That source has a fresh full review in
REVIEW_S_C5_TILTED_LARGE_MEAN_LONG_RECOVERY_BLOCK_2026_10_26.md.
Here are its complete inputs and decisive identities, making the
absence of an extra force premise explicit.

Set
\[
\varepsilon=\max\{0,Tx-t+(1-x)/2\}
=\max\{0,db-dt+(1-x)/2\},\qquad P'=P+\varepsilon f_2.
\]
The condition \(3at\ge bx\) gives
\[
                     0\le\varepsilon<7b/10<1/5.
\tag{8}
\]
If epsilon is positive then t<1/3. The exact outer endpoint
reserves in the disk of squared radius \(17/4\) are

\[
\begin{split}
\mathcal L&=2(1-a)+b-(a+2b)\varepsilon-\varepsilon^2
                                      >47b/750>0,\\
\mathcal C&=T-T^2-[4t+(1-2T)x]\varepsilon-\varepsilon^2>0.
\end{split}
\tag{9}
\]

For positive epsilon, writing \(w=T-1/2\), the latter equals

\[
t\{(3-w^2)t-1-4wx\},\qquad
(3-w^2)t-1-4wx>11179/248400 .
\tag{10}
\]

For epsilon zero it is \(T(1-T)>0\).
All estimates use only (1),(5) and \(3at\ge bx\).
In particular \(d(bx+at)-T=t>0\) replaces the direct-concurrence
phrase of the original application.

The global y coordinate of P' is negative. The linear projection
\(P'\cdot z\) has its minimum on (4) at an endpoint. Thus (9)
puts the whole arc strictly in the smaller disk centered at P'.
The other path vertices have distances at most epsilon,
\(1+\varepsilon\), \(\sqrt{1+\varepsilon^2}\), or the strictly
smaller inner radial endpoint distances. Hence the whole region
is in that open disk.

Every actual extra disjoint from a physical radial terminal has
radial projection strictly below its outer face. This is the
geometric outer-face screen of RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1, using the sharp center bound \(d+1/2\).
It applies to both actual L and C, independently of circle weights.

In the frame \((-f_1,f_2)\), (7) puts every translated extra in
\(f_2\)-height at most \(-\varepsilon\). The same unchanged extra
avoids the two opposite canonical terminals

\[
                 [1,2](-f_1)+[-1/2,1/2]f_2
                 \quad\hbox{and its negative}.
\tag{11}
\]

For the first, a hypothetical intersection has relative root
coordinates
\[
a(X-1)-b(Y+\varepsilon),\qquad
b(X-1)+a(Y+\varepsilon),
\]
strictly inside the actual L after the original outer screen.
For the second, its actual C coordinates satisfy
\[
X_C>1+\varepsilon t,\qquad
T-\varepsilon x-1/2<Y_C<T-\varepsilon x+1/2.
\]
The lower transverse inequality is exactly
\(\varepsilon\ge Tx-t+(1-x)/2\); the original C outer screen
supplies \(X_C<2+\varepsilon t\).
This is a comparison with fixed actual extras, not independent
motion of the terminals.

After one reflection, all extras lie in the same upper half of
the strict smaller disk and avoid (11). HALF_POCKET_TRIPLE_RIGIDITY.md
would force any triple to have a vertex on its outer circle,
a contradiction. Thus the large-ratio range has capacity two.

## 4. The whole small-ratio range \(\kappa\le1/4\)

Now \(3at\le bx\). If t is positive,
\[
t/x\le b/(3a)<16/177<1/10,\qquad t<1/10,\qquad x>99/100.
\]
Put
\[
r=\tan(\psi/2)=t/(1+x),\qquad
v=\tan(\theta/2),\qquad c_0=(1+v^2)^{-1/2},\quad s_0=vc_0 .
\]
The same definitions are valid at t=0. We have
\[
\tan(\phi/2)=b/(1+a)<2/15<1/7,\qquad 0\le r<1/19,
\]
and therefore
\[
                     0<v<13/66<1/4.
\tag{12}
\]

The last identity of (5) gives the exact relations
\[
d=\frac{1+v^2}{1+r^2},\qquad
\delta=\frac{v^2-r^2}{1+r^2}.
\]
Define
\[
h_*=\delta/v,\qquad P_*=(\delta,-h_*),\qquad
e_*=(c_0,s_0),\qquad j_*=(s_0,-c_0).
\tag{13}
\]
Thus
\[
0<h_*\le v<1/4,\quad P_*=(\delta/s_0)j_*.
\tag{14}
\]
The inequality is strict when t>0; equality occurs at the allowed
t=0 corner endpoint.

### 4.1. The same full region lies above the comparison axis

Let \(Y(z)=j_*\cdot(z-P_*)\). The exact path heights are

\[
Y(p_0)=\frac{1-x}{2s_0}\ge0,\qquad
Y(P)=\frac{1-a}{2s_0}>0,\qquad
j_*\cdot n=s_0>0,\quad j_*\cdot f=-c_0.
\tag{15}
\]

Also \(Y(dn)=Y(p_0)\). The two inner terminal vertices have
height \(Y(p_0)+c_0/2>0\), and the two outer endpoints add
\(s_0>0\). Thus every path segment lies in \(Y\ge0\).
The selected minor arc is symmetric about j*, with its j*
projection minimized at its endpoints. Its entire bounded side
therefore satisfies
\[
                              Y(z)\ge0.
\tag{16}
\]

This is containment of each whole additional square, not just
its center.

### 4.2. Exact simultaneous shifted-terminal comparison

In the frame \((e_*,j_*)\), after the single translation by P*,
the two actual radial terminals are

\[
\begin{split}
L-P_*&=[1,2](c_0,s_0)
 +[-1/2-h_*,1/2-h_*](-s_0,c_0),\\
C-P_*&=[1,2](-c_0,s_0)
 +[-1/2-h_*,1/2-h_*](s_0,c_0).
\end{split}
\tag{17}
\]

This keeps their full actual transverse intervals. The radial
projections of P* on both original outward axes are delta.
The actual outer-face screen therefore gives, for every unchanged
translated extra, projection strictly below 2 on both tilted axes.

The linked terminal screen UNIT_TILTED_RADIAL_TERMINAL_SCREEN.md
applies with shift v. Its upper-half-plane interior is contained
in that of the actual shift h*, because \(0<h_*\le v<1/4\).
Indeed for a point
\[
z=\rho(c_0,s_0)+\tau(-s_0,c_0),\quad1<\rho<2,\quad
-1/2-v<\tau<1/2-v,
\]
the upper actual transverse bound is automatic. If the lower
one failed, then
\[
y/c_0=v\rho+\tau<2v-1/2-h_*<0,
\]
contrary to (16). Hence avoidance of the actual terminal implies
avoidance of the linked one in this half-plane.

The screen and its reflection now make each fixed translated
extra avoid both
\[
[1,2]\times[-1/2,1/2],\qquad[-2,-1]\times[-1/2,1/2].
\tag{18}
\]
All orientations and tangencies remain; this is not pointwise
replacement of the original obstacles.

### 4.3. Exact strict smaller-disk containment

Both original outer endpoints have translated squared norm
\[
                  |z_L-P_*|^2=|z_C-P_*|^2
                  =4+(h_*-1/2)^2<17/4.
\tag{19}
\]
The reserve is \(h_*-h_*^2>0\), including t=0.
Since \(P_*\) is a positive multiple of j*, its projection on
the minor arc is minimized at those endpoints. Thus every point
of the entire arc has squared distance at most the value in (19).

The other path vertices satisfy
\[
\begin{split}
|p_0-P_*|^2&=1+h_*^2<17/16,\\
|P-P_*|^2&=2(1-a)+h_*^2-2bh_*<4/61+1/16<1,\\
|P+n-P_*|^2&=1+(h_*-T)^2<1+(13/50)^2<2.
\end{split}
\tag{20}
\]
The two inner terminal vertices have squared norm
\(1+(h_*-1/2)^2\), smaller than (19). Convexity contains every
path segment. Its compact boundary and bounded side therefore
lie strictly inside the same open disk of radius \(\sqrt{17}/2\).

The same translated extras are now whole units in its upper
half-plane and avoid the two opposite canonical terminals (18).
HALF.3 would force an outer vertex for any triple, contradicting
strict containment. This proves capacity two on the complete
small-ratio range.

## 5. Endpoint and application scope

The two ratio ranges overlap at kappa=1/4 and together exhaust
(1). At t=0, the same actual corner P forces
\[
x=1,\quad da=1-\delta,\quad db=2\sqrt\delta,\quad
T=2\sqrt\delta,\quad v=h_*=\sqrt\delta.
\]
Equations (15)--(20) still hold; only \(Y(p_0)=0\) and
\(h_*=v\) become equalities. The screen permits this exact
linked equality. Thus the genuine corner endpoint is included.

A general t=0 application with an additional side mean is not
identified with that corner. It requires its own geometric
premises or separate theorem.

The proof uses no root direct force, no load count, no
concurrence, and no degree-two force deletion. It can therefore
be applied to higher-degree or additionally loaded configurations
only after their unchanged actual four-square geometry and
containing side have been proved. It does not by itself close a
larger original graph/load family.
