# A long square-to-square gap covers the entire center disk

**Date:** October 30, 2026 UTC. **Status:** complete new hand derivation,
awaiting separate independent review and adoption. No original roadmap flag
or coarse parent is changed by this manuscript alone.

This theorem concerns the actual squares, independently of any stress. Its
channel corollary applies to endpoints of arbitrary true degree and to every
physical circle mask. It excludes a whole retained-channel triangle whenever
one internal reserve is at least two and the other two are at least one.

## 1. Geometric statement

Put

\[
Q=\frac{1105}{256},\qquad M=\frac{91}{60}.
\]

For a unit square S with center c and orthonormal side axes u,v, write

\[
h_S(d)=\frac{|d\cdot u|+|d\cdot v|}{2}
\]

for its halfwidth in a unit direction d. Let A,B be two actual unit squares
contained in the disk of squared radius Q, centered at the origin. Suppose
there is one signed unit direction d such that

\[
d\cdot(c_B-c_A)\ \ge\ 2+h_A(d)+h_B(d).                 \tag{1}
\]

**Theorem 1 (expanded-square cover).** Every point z in the closed disk
\(\|z\|\le M\) satisfies

\[
\boxed{\quad \operatorname{dist}(z,A)<\frac32
\quad\hbox{or}\quad
\operatorname{dist}(z,B)<\frac32.\quad}                 \tag{2}
\]

All directions, endpoint tilts, transverse positions and boundary cases
allowed by (1) are included. Neither endpoint is required to touch the
containing circle. No contact mean, force or torque is used in Theorem 1.

**Corollary 1 (three-square gap obstruction).** There cannot also be an
actual unit square C in the same disk and signed unit directions n_A,n_B
such that

\[
\begin{aligned}
n_A\cdot(c_C-c_A)&\ge1+h_A(n_A)+h_C(n_A),\\
n_B\cdot(c_C-c_B)&\ge1+h_B(n_B)+h_C(n_B).
\end{aligned}                                                   \tag{3}
\]

The three directions d,n_A,n_B are completely independent. The statement
is equivalently a metric implication: if the Euclidean distance between
two contained unit squares is at least two, no third contained unit square
can be at distance at least one from each. The support-gap form (1),(3)
is sufficient for every application below; the metric equivalence follows
from nearest-point separation of two compact convex sets.

## 2. Universal center bound and the long-gap frame

For any contained unit square,

\[
\begin{aligned}
\max_{p\text{ a corner}}\|p\|^2
 &=\|c\|^2+\frac12+|c\cdot u|+|c\cdot v|\\
 &\ge\|c\|^2+\|c\|+\frac12.
\end{aligned}                                                   \tag{4}
\]

Since

\[
M^2+M+\frac12-Q=\frac{31}{57600}>0,
\]

every actual center has norm strictly less than M.

Choose d as the horizontal axis and write the endpoint centers as

\[
c_A=(-X_A,y_A),\qquad c_B=(X_B,y_B).
\]

The signs displayed here follow from (1): every square has halfwidth at
least 1/2, so the horizontal center gap is at least three, whereas each
center coordinate has magnitude less than M. Consequently

\[
X_A,X_B>3-M>1,
\qquad |y_i|^2<M^2-(3-M)^2=\frac1{10}.                \tag{5}
\]

In particular \(X_i>|y_i|\).

For each endpoint choose its unoriented near-horizontal side axis and put

\[
a_i\ge b_i\ge0,\qquad a_i^2+b_i^2=1,\qquad
m_i=a_i+b_i=2h_i(d),\qquad \delta_i=m_i-1.
\]

Thus a_i and b_i are the absolute cosine and sine of its smaller angle
to the horizontal or vertical axes. Define

\[
E=\frac{\delta_A+\delta_B}{2}\ge0.
\]

Equation (1) and the center bound give

\[
3+E\le X_A+X_B<2M=3+\frac1{30}.
\]

Hence

\[
0\le E<\frac1{30},\qquad 0\le\delta_i<\frac1{15}.       \tag{6}
\]

## 3. A coupled height budget, retaining both endpoint tilts

First,

\[
1-a_i\le\frac{15}{26}\delta_i^2.                         \tag{7}
\]

Here is an elementary proof with no angle approximation. Since
\(0\le b_i\le1/\sqrt2<4/5\), squaring gives
\(a_i\ge1-b_i/2\). Thus \(\delta_i=a_i+b_i-1\ge b_i/2\),
so (6) implies \(b_i<2/15\). The exact identity

\[
\delta_i^2=2(1-a_i)(1-b_i)
\]

now proves (7).

Let \(Y_i=|y_i|\), \(h_i=m_i/2\), and \(k_i=(a_i-b_i)/2\).
Containment and (5) imply the following useful actual-corner bound:

\[
\boxed{\ (X_i+k_i)^2+(Y_i+h_i)^2\le Q.\ }              \tag{8}
\]

To check it for every tilt sign, reflect coordinates so the center is
\((X,Y)\), with X>=Y>=0. One tilt sign has frame-coordinate absolute
sum

\[
aX+bY+|aY-bX|\ge(a-b)X+(a+b)Y.
\]

If aY>=bX this is equality; if aY<=bX the difference is
\(2(bX-aY)\ge0\). The other tilt sign has sum
\((a+b)X+(a-b)Y\), which is at least the same lower bound because
X>=Y. Insert this into (4), and use \(k^2+h^2=1/2\), to obtain (8).

Write \(U_i=X_i+k_i\), \(V_i=Y_i+h_i\). These are positive. The
triangle inequality for the two vectors in (8) gives

\[
(U_A+U_B)^2+(V_A+V_B)^2\le4Q.                            \tag{9}
\]

Meanwhile, (1),(7) give

\[
\begin{aligned}
U_A+U_B
&\ge2+a_A+a_B\\
&\ge4-\frac{15}{26}(\delta_A^2+\delta_B^2)\\
&\ge4-\frac{30}{13}E^2.
\end{aligned}                                                   \tag{10}
\]

Thus, using \(Q-4=81/256\),

\[
\begin{aligned}
V_A+V_B
&\le2\sqrt{Q-(2-15E^2/13)^2}\\
&\le2\sqrt{\frac{81}{256}+\frac{60}{13}E^2}\\
&\le\frac98+\frac{320}{39}E^2.
\end{aligned}                                                   \tag{11}
\]

The last step is the tangent inequality for the concave square root at
81/256. All radicands are positive; the interval (6) makes the positive
lower bound in (10) immediate. Subtract \(h_A+h_B=1+E\) from (11):

\[
\boxed{\quad
Y_A+Y_B\le F(E):=\frac18-E+\frac{320}{39}E^2
\le\frac18.\quad}                                             \tag{12}
\]

For the last inequality, \((320/39)E\le32/117<1\). This coupled
budget, rather than two independent coarse height bounds, is the key.

## 4. Axis-parallel rectangles lying inside the actual endpoints

The actual endpoint square i contains the centered axis-parallel square
with halfwidth

\[
r_i=\frac{1}{2m_i}=\frac{1}{2(1+\delta_i)}.               \tag{13}
\]

Indeed every point of that smaller square has absolute projection at
most \(r_i(a_i+b_i)=1/2\) on either original side axis. This is an
inscribed set; no original square is moved or reoriented.

Denote the upper inward corners of these two inscribed squares by

\[
P_A=(-X_A+r_A,y_A+r_A)=(\alpha,t_A),\qquad
P_B=(X_B-r_B,y_B+r_B)=(\beta,t_B).
\]

Their entire geometry is bounded by three short estimates:

\[
\boxed{\quad
\beta-\alpha<L:=\frac{1921}{930},\qquad
\frac{t_A+t_B}{2}\ge H:=\frac{13}{30},\qquad
|t_A-t_B|\le D:=\frac2{15}.
\quad}                                                        \tag{14}
\]

Here are complete derivations. Convexity of the reciprocal, or clearing
positive denominators, gives

\[
r_A+r_B\ge\frac1{1+E},\qquad
|r_A-r_B|\le\frac{E}{1+2E}.                               \tag{15}
\]

For the difference, use
\(|\delta_A-\delta_B|\le2E\) and
\((1+\delta_A)(1+\delta_B)\ge1+2E\).

Since \(X_A+X_B<2M\) and \(E<1/30\),

\[
\beta-\alpha<\frac{91}{30}-\frac{30}{31}=\frac{1921}{930}.
\]

Equations (12),(15) give

\[
\begin{aligned}
\frac{t_A+t_B}{2}
&\ge\frac12\left(\frac1{1+E}-F(E)\right)\\
&=\frac7{16}+\frac{E^2}{2(1+E)}-\frac{160}{39}E^2\\
&\ge\frac7{16}-\left(\frac{160}{39}-\frac{15}{31}\right)\frac1{900}
 =\frac{75467}{174096}>\frac{13}{30}.
\end{aligned}                                                   \tag{16}
\]

The last strict margin is \(127/870480\). Similarly,

\[
\begin{aligned}
|t_A-t_B|
&\le F(E)+\frac{E}{1+2E}\\
&=\frac18+E^2\left(\frac{320}{39}-\frac2{1+2E}\right)\\
&\le\frac18+\left(\frac{320}{39}-\frac{15}{8}\right)\frac1{900}
 =\frac{1483}{11232}<\frac2{15}.
\end{aligned}                                                   \tag{17}
\]

The last strict margin is \(73/56160\). The constants in (14) were
rounded only in the explicitly safe directions.

Two additional coarse bounds will cover the ends and the middle band:

\[
\frac{15}{32}\le r_i\le\frac12,\qquad
\frac{11}{32}\le t_i\le\frac58.                         \tag{18}
\]

They follow directly from (6),(12),(13). The bottom heights of both
inscribed squares are at most \(-11/32\). From (5),(18),

\[
\alpha<0<\beta,
\qquad -X_A-r_A<-M,
\qquad X_B+r_B>M.                                      \tag{19}
\]

For example \(X_A+r_A>3-M+15/32>M\); the right endpoint is the
reflection. Thus the outward horizontal ends of the inscribed squares
extend beyond the entire center disk.

## 5. The two expanded endpoints cover the whole upper half of the center disk

Let \(z=(x,y)\) with \(x^2+y^2\le M^2\) and y>=0.

### 5.1. Left and right horizontal strips

If x<=alpha, (19) puts x in the horizontal projection of A's inscribed
square. Its bottom is negative and its top is at least 11/32, so

\[
\operatorname{dist}(z,A)
\le\max(0,y-t_A)
\le M-\frac{11}{32}<\frac32.
\]

If x>=beta, use B in exactly the same way. Both statements include
their closed strip boundaries.

### 5.2. Central horizontal strip at height at most 5/8

Suppose alpha<=x<=beta and 0<=y<=5/8. Choose the corner P_A or P_B
whose horizontal coordinate is closer to x. The horizontal difference
is at most \((\beta-\alpha)/2<L/2<31/30\). By (18), the vertical
difference is at most 5/8. Hence the squared distance to that actual
point of A or B is less than

\[
\left(\frac{31}{30}\right)^2+\left(\frac58\right)^2
<\frac94.
\]

This covers the entire central lower band, including y=0 and y=5/8.

### 5.3. Central horizontal strip at height from 5/8 to M

It remains to consider alpha<=x<=beta and 5/8<=y<=M. At this height
the open radius-3/2 disks about P_A and P_B have horizontal halfwidths

\[
s_A(y)=\sqrt{\frac94-(y-t_A)^2},\qquad
s_B(y)=\sqrt{\frac94-(y-t_B)^2}.
\]

These are defined and positive: (18) gives
\(0\le y-t_i\le M-11/32<3/2\). We claim

\[
s_A(y)+s_B(y)\ge
\frac{\sqrt{371}}{20}+\frac{\sqrt{4379}}{60}
>\frac{1921}{930}=L.                                   \tag{20}
\]

For the first inequality, initially increase y to M; this decreases
each halfwidth since y>=t_i. Next decrease the average of t_A,t_B to
H, preserving their difference; this again decreases each halfwidth.
Finally increase the absolute difference to D. The function
\(t\mapsto\sqrt{9/4-(M-t)^2}\) is concave, so the sum of its
values at H plus and minus half a difference decreases as that
difference increases. The entire comparison interval has

\[
0<M-H-D/2\le M-t\le M-H+D/2<3/2,
\]

after the average has been set to H; during the preceding average
decrease each radicand lies between actual admissible and final
admissible values. Thus no invalid radical branch is crossed. Using
\(M-H+D/2=23/20\), \(M-H-D/2=61/60\) gives the first part of (20).

For the strict algebraic comparison in (20), put

\[
A_0=\frac{371}{400},\quad B_0=\frac{4379}{3600},\quad
C_0=L^2-A_0-B_0=\frac{3671983}{1729800}>0.
\]

Direct exact arithmetic yields

\[
4A_0B_0-C_0^2
=\frac{2473200289}{374026005000}>0.                       \tag{21}
\]

All quantities being positive, taking square roots twice proves
\(\sqrt{A_0}+\sqrt{B_0}>L\). This is a single rational comparison,
not a numerical interval or pose certificate.

The two open horizontal disk sections therefore overlap strictly,
because their center separation beta-alpha is less than L. Each
contains its own horizontal center alpha or beta. Their union contains
the entire closed interval [alpha,beta]. Thus z is strictly within
distance 3/2 of P_A or P_B, and hence of A or B.

Sections 5.1--5.3 cover every point in the upper half of the center
disk. Reflection in the horizontal axis repeats the identical proof
with the lower inward corners of the same two inscribed squares;
the hypotheses (1),(4)--(12) and all constants are invariant. This
covers the lower half too and proves Theorem 1.

## 6. Three-square consequence, without any contact assumptions

Every actual C center satisfies \(\|c_C\|<M\) by (4). If the first
inequality of (3) holds, then for every p in A,

\[
n_A\cdot(c_C-p)
\ge n_A\cdot(c_C-c_A)-h_A(n_A)
\ge1+h_C(n_A)\ge\frac32.
\]

The Cauchy--Schwarz inequality gives \(\|c_C-p\|\ge3/2\), so
\(\operatorname{dist}(c_C,A)\ge3/2\). The B inequality gives the
same conclusion for B. This contradicts Theorem 1. Corollary 1 follows.

## 7. Full original-channel applications

Use the physical transmission theorem of
[PHYSICAL_CONTACT_STRESS.md](PHYSICAL_CONTACT_STRESS.md), Sections 5--6,
or [PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md](PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md),
Section 1. A path whose internal bodies are actual unloaded
true-positive-degree-two transmitters gives, for its original signed
unit normal n and unchanged actual endpoint bodies U,V,

\[
n\cdot(c_V-c_U)=L+h_U(n)+h_V(n),                          \tag{22}
\]

where L is the sum of the original internal widths, each 1 or sqrt(2).
All original full application means remain in the derivation of (22).

**Theorem 2 (long-channel triangle exclusion).** Suppose three distinct
actual endpoint squares A,B,C are connected pairwise by such actual
channels, with reserves

\[
L_{AB}\ge2,\qquad L_{AC}\ge1,\qquad L_{BC}\ge1.
\]

Then the configuration is impossible at squared radius at most Q.

Apply (22) to the three paths. They give exactly (1),(3), contrary to
Corollary 1. Endpoint degrees, positive circle weights, additional
endpoint forces and all physical circle masks are arbitrary. The
channels may not be created by deleting a positive edge from an
internal body. No planarization or change of normal is made.

The theorem is a single geometric obstruction for every component size,
including chorded or attached components whenever these three genuine
channels occur. No premise says the entire positive component is a
simple cycle. All other physical squares remain present.

### 7.1. The whole seven-body three-load simple-cycle family

In an entire positive simple cycle with exactly three loaded bodies,
[LONG_CHANNEL_ENDPOINT_MATCHING.md](LONG_CHANNEL_ENDPOINT_MATCHING.md),
Section 3 proves that a seven-body component has exactly the unloaded
run pattern (2,1,1). The two-body run has reserve 2, because both
transmitters are side-normal; each one-body run has reserve 1 or sqrt(2).
The three actual loaded bodies are distinct, and every internal body
is unloaded of true degree two in the whole component. Thus Theorem 2
excludes **every realization of the complete seven-body (2,1,1) family**.

This application includes all four permitted side/diagonal type choices
for the two short single-transmitter runs, all endpoint degrees
allowed by the stated full simple cycle, every physical one-/two-circle
mask, individual zero corner coefficients, and every shared-contact mean.
No proper-concurrence or nonparallel-load theorem is needed.

Together with the existing long-channel matching theorem, the entire
simple-cycle family with exactly three loaded bodies and at least seven
total bodies is excluded by the same geometry. The alternating six-body
three-load pattern has reserves (1,1,1) and is **not covered by this new
lemma**; existing independent six-cycle closures are unchanged.

### 7.2. What is not claimed

The theorem does not establish that every large biconnected block has
such a channel triangle. It does not close all seven-body graphs, the
last six-body coarse parent, the full sharp n=9 theorem, equality
classification, or the downstream common-normal-selection audit.
The original inventory and its identities remain unchanged pending
independent source review and exact caller adoption.

## 8. Verification boundary

The proof uses the exact corner formula, a two-endpoint coupled norm
budget, actual inscribed rectangles, and one exact rational radical
comparison. No numerical pose search, mesh, new packing certificate,
Lean compilation, CI run, or altered stress is a premise. The earlier
near-diameter axial theorem is consistent with these estimates but is
not needed as an input to this proof.
