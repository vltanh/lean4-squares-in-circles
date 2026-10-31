# Complete return-owner domain of the low-radius H-owned negative endpoint with a unique far endpoint

**Status: complete whole-domain analytic reduction; root and separate independent full source/prerequisite audits passed.**

Use the common preselected physical certificate and
\[
79/40\le R<\sqrt{17}/2.
\]
H--A--B--C--H is an actual positive four-cycle. A,B,C retain their true positive pair degrees two and positive total circle loads; A,C have one physical circle corner, and B has two. HA is an H-owned singleton and \(c_H\cdot z_A<0\). H retains every other positive force, its actual petal when present, and every completion square. No HB chord is assumed.

NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md already excludes the complementary high-radius interval and every other AB owner. Its complete tangential chart, including all original B-weight endpoints and the original H-side offset, is used below. This source gives a full return-owner classification; it does not yet exclude the remaining low-radius SUU family.

## 1. One common reflected radial frame, with the original H side

In A's original frame write
\[
z_A=(a,b),\quad a>b>3/5,\quad a>3/2,\quad a^2+b^2=R^2,
\]
\[
d=\sqrt{R^2-1/4}-1,\quad N=\sqrt{R^2-9/4},\quad
t=\sqrt{R^2-2a+3/4},\qquad d<t<N.
\]
Let the actual radial and tangential axes of B be \(e=(c,s)\) and \(Je=(-s,c)\), where \(c,s>0\), \(c^2+s^2=1\). The unchanged A/B contact is
\[
T_{AB}=t e-\tfrac12Je=(a-1,b),
\quad a=1+tc+s/2,\quad b=ts-c/2.
\]
Apply the orthogonal reflection \(X\mapsto(e\cdot X,-Je\cdot X)\) about the true circle origin. In these coordinates the entire actual data are
\[
B=[d,d+1]\times[-1/2,1/2],\quad T_{AB}=(t,1/2),
\]
\[
P:=B\cap C=(d,-1/2),\quad
Q:=H\cap A=(t-s,1/2+c),\quad
Z:=z_A=(t+c,1/2+s).
\tag{1}
\]
Thus \(P-Q=(d-t+s,-1-c)\). In particular Q is a relative H-side-interior point, not an H vertex.

The actual H-to-A unit normal is
\[
\nu=\frac{(1,M)}{\sqrt{1+M^2}},\qquad
M=\frac{b}{s(t+c)}-\frac cs.
\tag{2}
\]
Indeed the original proper concurrence is \(\kappa Z\), with \(\kappa=t/(t+c)\), and
\[
\kappa Z-Q=\left(s,\frac b{t+c}-c\right),
\]
a positive multiple of \(\nu\). The entire actual H is
\[
H=Q+[-1,0]\nu+[-1/2-\eta,1/2-\eta]J\nu,\qquad |\eta|<1/2.
\tag{3}
\]
Here \(\eta\) is the negative of the old transverse parameter under the reflection. It has not been selected or reset. The closed interval \(|\eta|\le1/2\) may be retained when taking necessary bounds. The original negative premise remains exactly
\[
\left(Q-\tfrac12\nu-\eta J\nu\right)\cdot Z<0.
\tag{4}
\]

For useful complete bounds, put
\[
E=\frac{4d^2-1}{4d^2+1},\qquad F=\frac{4d}{4d^2+1}.
\]
The circle equation \((t+c)^2+(s+1/2)^2=(d+1)^2+1/4\), together with \(t>d\), gives \(s<2d(1-c)\). Squaring positive quantities yields
\[
0<c<E<3/5,\qquad s>F>4/5,\qquad -c/s<M<1.
\tag{5}
\]
The final lower bound uses b>0. For the upper bound,
\((s+c)(t+c)-b=c(s+t+c+1/2)>0\).
All these inequalities hold throughout the original chart, with no C return assumption.

Let \(g=(p,q)\) be the original C-to-B unit normal. Section6 of the radial-middle theorem gives
\[
p,q>0,\quad p^2+q^2=1,\qquad
\frac{d+1-t}{2(d+1)(t-d)}
\le\frac qp\le
\frac{d+1+t}{2(d+1)(t-d)}.
\tag{6}
\]
Equivalently the original reflected B resultant is
\[
F_B=\Lambda(d+1,\omega),\quad\Lambda>0,\quad
\omega=\frac{d+1}{t}\left((t-d)\frac qp-\frac12\right),
\quad -1/2\le\omega\le1/2.
\tag{7}
\]
Both zero individual circle-weight endpoints remain included.

## 2. The full physical HC owner partition

BC is the singleton P in(1). Its actual normal g is strictly oblique to B's axes, so B cannot own BC.

If HC has positive length, BC may be C-owned or genuinely free. The HC mean remains its original point in the full actual overlap. A fixed-tip selection cannot be applied to that variable mean merely because BC is fixed. This entire shared-HC branch is retained.

Suppose HC is a singleton. Its C application cannot coincide with P. The complete coincident-application theorem in GENERAL_FIXED_TIP_NORMAL_SELECTION.md would require C to be radial D with P its inner vertex, of norm \(R-\sqrt2<7/10\); but \(|P|>d>91/100\).

Thus C has two distinct fixed physical applications. The compatible selection made before multiplier extraction removes free BC and free HC. Since B does not own BC, BC is C-owned. The only remaining singleton HC owners are C and H. This is the complete partition:
\[
\begin{array}{c|c}
\text{physical HC feature}&\text{retained BC/HC owners}\\ \hline
\text{positive-length shared side}&
\text{BC C-owned or free; original HC mean retained}\\
\text{singleton}&
\text{BC C-owned; HC C-owned or H-owned}.
\end{array}
\tag{8}
\]
No new normal choice is made after extraction.

## 3. Complete C frame whenever BC is C-owned

Put \(j=Jg=(-q,p)\). The strict singleton convention gives the actual frame
\[
C=P+[-1,0]g+[-k,1-k]j,\qquad0<k<1.
\tag{9}
\]
The full geometric calculation of FREE_NEGATIVE_C4_FAR_TIP_OWNED_RETURN_EXCLUSION.md, Section1, applies verbatim here. That calculation uses only P=(d,-1/2), p,q>0, (9), and C's physical unique circle mask. It uses neither a free HA contact nor the former free-module location of Q.

Explicitly, set
\[
h=dp-q/2,\quad L=dq+p/2,\quad\delta=1-k.
\]
The j-coordinate of C's center is negative because \(L>1/2\). If h>1/2, the circle equation of the other possible farthest corner would force L>d and hence \(h^2<1/4\), a contradiction. At h=1/2 the physical circle mask has two corners. Consequently
\[
z_C=P-g-kj,\quad -1/2<h<1/2,\quad L>d,\quad
k^2+2Lk=2(d+h).
\tag{10}
\]
Writing
\[
m=\frac{L+hk}{L+k},
\]
the same complete comparison gives
\[
1/2<m<1,\quad 0<\delta<d+1-N,\quad q>E.
\tag{11}
\]
For m use \(k<(d+h)/L\) and
\(L^2-(d+h)(1-2h)=(d+h-1/2)^2\).
For delta, the positive root k of(10) increases with h on[-1/2,1/2), beginning at \(N-d\).

C's true degree-two concurrence is
\[
O_C=P-mg=\frac{L}{L+k}z_C.
\tag{12}
\]
Its true force equation makes the j-component of the C-to-H normal positive. Therefore a C-owned HC contact uses +j and has its unchanged application or mean at
\[
T_0=P-mg+\delta j.
\tag{13}
\]
This also applies when HC is shared and BC is C-owned: (13) must be the original mean in its original overlap; it is not a replacement mean.

If HC is an H-owned singleton, its C support is exactly one of
\[
K_+=P+\delta j,\qquad K_-=P-g+\delta j.
\tag{14}
\]
Their actual C-to-H normal directions are respectively
\[
W_+=mg+\delta j,\qquad W_-=-(1-m)g+\delta j.
\tag{15}
\]
These directions follow by subtracting (12) from (14). Their signs lie in the respective strict C-vertex normal cones. The other two C vertices cannot support a normal with positive j-component. Thus the full H-owned feature cover has exactly these two alternatives.

## 4. Every actual H side and the original offset remain

For either candidate \(K=K_+\) or \(K=K_-\), put
\[
\lambda=\nu\cdot(Q-K),\qquad \tau=J\nu\cdot(K-Q).
\]
Membership in the unchanged H requires
\[
0\le\lambda\le1,\qquad
-1/2-\eta\le\tau\le1/2-\eta.
\tag{16}
\]
Let \(\widehat W=W_\pm/|W_\pm|\) be its actual C-to-H normal. Since H owns HC, exactly one of the four actual H side possibilities occurs:
\[
\begin{array}{c|c}
\widehat W&\text{actual side equation}\\ \hline
-\nu&\lambda=0\\
+\nu&\lambda=1\\
-J\nu&\tau=1/2-\eta\\
+J\nu&\tau=-1/2-\eta.
\end{array}
\tag{17}
\]
The other coordinate remains in its full interval(16); the actual singleton is in the corresponding relative side interior. Using the closed intervals only enlarges the necessary domain.

Equations(1)--(17) preserve the full low-radius return domain, including every original H offset, B individual-weight endpoint, shared HC mean and free-BC possibility in the shared branch. In particular no argument requiring Q to be an H vertex has been imported from the free-HA theorem.

The shared, C-owned-singleton and H-owned-singleton return branches still require exits in this new domain. H retains all its true forces and intact petal. No body motion, HB chord, numerical angle subdivision, Lean compilation or CI is used.
