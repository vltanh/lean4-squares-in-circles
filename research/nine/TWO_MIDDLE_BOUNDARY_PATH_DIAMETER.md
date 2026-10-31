# Two middle boundary units suffice for a three-edge path diameter below three

Date: October 26, 2026.

**Status: accepted complete geometric scope extension after full independent
reviews in REVIEW_C6_PATH_DIAMETER_EXTENSIONS_CERTIFICATE_REDUCTION_2026_10_26.md
and REVIEW_C6_PATH_DIAMETER_AND_FOUR_LOAD_JOIN_ROOT_2026_10_26.md.**
The middle bodies alone need physical circle
contacts. The endpoint bodies retain their actual independently oriented
frames and may be physically circle-clear. No force or angular-order
premise is required.

## 1. Whole local theorem

Let \(S_0,S_1,S_2,S_3\) be four distinct interior-disjoint actual unit
squares contained in the disk \(D_R\), where
\[
79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Suppose consecutive bodies have actual contacts
\[
p_0\in S_0\cap S_1,\qquad
p_1\in S_1\cap S_2,\qquad
p_2\in S_2\cap S_3.
\tag{2}
\]
Assume only \(S_1,S_2\) physically touch the containing circle.
Then their endpoint centers obey
\[
\boxed{|c_3-c_0|<3.}
\tag{3}
\]

The original bodies may have arbitrary positive degrees, circle weights,
additional physical contacts and support owners. In particular neither
endpoint is assigned a circle load or a physical circle contact.

Put
\[
Q=1105/256,\quad R_0=\sqrt{17}/2,\quad
M=91/60,\quad m=89/60,\quad w=\arctan(23/16).
\tag{4}
\]

## 2. Endpoint sectors need containment, not circle equality

Every contained unit with center radius \(r\) and radial frame tilt
\(\psi\in[0,\pi/4]\) satisfies
\[
r^2+2rh+\frac12\le R^2\le Q,\qquad
h=\frac{\cos\psi+\sin\psi}{2}\ge\frac12.
\tag{5}
\]
Thus \(r<M\), since
\[
M^2+M+\frac12-Q=\frac{31}{57600}>0.
\tag{6}
\]
If \(R<R_0\), (5) gives \(r<3/2\) for every center and proves (3)
immediately.

Suppose henceforth \(R\ge R_0\) and, for contradiction,
\(|c_3-c_0|\ge3\). Both endpoint radii then satisfy
\[
m<r_i<M\qquad(i=0,3).
\tag{7}
\]
Both endpoint squares avoid the origin. Write
\[
k=\frac{\cos\psi-\sin\psi}{2},\qquad h^2+k^2=\frac12.
\]
The largest angular distance of a point of the actual endpoint square
from its center direction is
\[
t(r,\psi)=\arctan\frac{h}{r-k}.
\tag{8}
\]
Indeed the four actual vertices, in radial coordinates, are
\((r+k,h),(r+h,-k),(r-k,-h),(r-h,k)\). Comparing their four slopes gives
(8), using \(r>1\ge h+k\).

Sections 3--4 of BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md now apply
unchanged with the inequality (5). Here is the exact hypothesis check.
That proof obtains
\[
\frac12\le h<\frac{11}{20},\qquad
\frac{11}{25}<k\le\frac12,\qquad
0<w+t<\frac\pi2
\tag{9}
\]
solely from (5) and \(r\ge m\). It then defines
\(\overline Q=M^2+M+1/2>Q\), and at fixed frame tilt increases \(r\)
to the unique positive solution of
\[
\bar r^2+2\bar r h+\frac12=\overline Q.
\tag{10}
\]
Containment (5) is exactly what is needed for \(r<\bar r\le M\).
Neither the enlargement nor either derivative in that proof uses
equality in (5).

More explicitly, for
\[
x_0=\frac{26026}{60\sqrt{3627485}},\qquad
y_0=\frac{171353}{60\sqrt{3627485}},
\tag{11}
\]
put
\[
E(r,\psi)=r^2-2x_0r\cos(w+t(r,\psi))+x_0^2.
\]
The imported calculations give
\[
\frac{\partial E}{\partial r}>\frac{167}{80}>0,\qquad
\left.\frac{dE}{d\psi}\right|_{(10)}
<-\frac{272}{675}<0.
\tag{12}
\]
The whole interpolation interval remains in (7)--(9), and at
\((r,\psi)=(M,0)\) the value is \(y_0^2\). Consequently every endpoint
sector point
\[
(r\cos\delta,\ \pm r\sin\delta),\qquad
0\le\delta\le w+t(r,\psi),
\tag{13}
\]
lies in the closed disk centered at \((x_0,0)\) of radius \(y_0\).
The strict radius reserve is
\[
\frac94-y_0^2=\frac{20777891}{13058946000}>0.
\tag{14}
\]
This establishes the precise endpoint-sector extension needed here.
The old proof's physical circle equality at an endpoint has been
replaced only by the weaker actual containment inequality it used.

## 3. Angular distance replaces the boundary-order requirement

The two middle squares physically touch the circle and \(R\ge R_0\).
Section 2 of BOUNDARY_SEVEN_CYCLE_CENTER_DIAMETER.md therefore gives
their actual angular-shadow widths
\[
\omega(S_1)<w,\qquad\omega(S_2)<w.
\tag{15}
\]
Each middle square avoids the origin: every point in it is within
distance \(\sqrt2\) of a circle point, and \(R>\sqrt2\).
Hence the three contacts in (2) are nonzero.

Use the ordinary minor angular distance on the unit direction circle,
denoted \(d_{\mathbb S^1}\). It satisfies the triangle inequality and
does not require a consistent increasing lift of the four center
directions. The actual contacts lie in their corresponding square
shadows, so
\[
\begin{aligned}
\gamma
&:=d_{\mathbb S^1}(c_0,c_3)\\
&\le d_{\mathbb S^1}(c_0,p_0)
 +d_{\mathbb S^1}(p_0,p_1)
 +d_{\mathbb S^1}(p_1,p_2)
 +d_{\mathbb S^1}(p_2,c_3)\\
&<t_0+2w+t_3<\pi .
\end{aligned}
\tag{16}
\]
Here \(t_i\) is the endpoint half-shadow (8); the first and last
distances are at most \(t_i\), and the two middle distances are
bounded by (15). The last strict inequality follows from (9).
Every direction in (16) is that of an actual center or contact.

Choose \(\delta_0,\delta_3\ge0\) such that
\[
\delta_0+\delta_3=\gamma,\qquad
\delta_i\le w+t_i.
\tag{17}
\]
Such a split exists by (16). Rotate the common reference axis along
the minor arc so the endpoint directions are
\(-\delta_0,+\delta_3\). The two endpoint-sector conclusions (13)
place both actual centers in the same disk of radius \(y_0<3/2\).
Therefore
\[
|c_3-c_0|\le2y_0<3,
\]
contradicting the assumption and proving (3).

## 4. Exact reusable scope

This argument strengthens the local metric theorem in
BOUNDARY_THREE_EDGE_PATH_DIAMETER.md by removing physical circle
contact at its two endpoint bodies. It also removes any need to
infer an angular order for a path containing circle-clear endpoints.
The proof retains the two actual middle circle contacts; it does
not permit a circle-clear middle body without a further theorem.

The bound uses actual containment and contact geometry only. It does
not delete any positive forces, change a support normal, contract
physical squares, or prescribe a circle mask at an endpoint. No
sampling, finite parameter packet, Lean compilation or CI is used.
