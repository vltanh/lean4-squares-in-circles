# The entire lower free/shared endpoint of a four-load house is excluded

**Status: complete hand whole-domain exclusion; root and separate
independent full hand audits passed.** Work in
\[
                 79/40\le R\le\sqrt{1105}/16
\]
with the four-load house
\[
 H=5,\quad A=3,\quad B=1,\quad C=4,\quad D=2.
\]
The positive boundary path is A--B--C--D. H is clear and has exactly
the three positive spokes HA,HB,HD; HC is absent. A,D have degree two,
B has degree three, and C has degree two. Every physical mask, actual
shared mean and all four completion squares remain.

**Theorem.** The remaining domain in which HD is a genuinely free
contact, D has a unique physical circle corner and DC has a positive-
length shared side is impossible. Together with
`HOUSE_FOUR_LOAD_COLLINEAR_WALL_EXCLUSION.md` and the complete
`HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md`, this excludes the
entire four-load house orbit at its stated certificate scope.

The proof begins with the complete physical reduction
`HOUSE_LOWER_FREE_SHARED_PINNED_MODULE.md`. Its incident/opposite
free-vertex cases are both needed; no triangle HDC is assumed.
In its coordinates, relative to the true disk origin, write
\[
 \begin{gathered}
 N=\sqrt{R^2-9/4},\quad T=\sqrt{R^2-1/4},\quad h=T-1,
 \quad t=T-N=\frac2{T+N},\\
 D=[N-1,N]\times[1/2,3/2],\quad
 C=[h,h+1]\times[-1/2,1/2],\\
 Q=H\cap D=(N-1,1/2),\qquad P=B\cap C=(h,-1/2).
 \end{gathered}
 \tag{1}
\]
The HD normal from H into D is (a,b), a>=b>0. The BC normal g from
B into C has both components positive. BC is a singleton, C has
both circle weights positive, and all of its DC means remain.
Useful exact bounds from that source are
\[
 \frac{32}{25}<N\le\frac{23}{16},\quad h>\frac9{10},
 \qquad\frac12<t<\frac{200}{319}<\frac{32}{51}<\frac23.
 \tag{2}
\]

## 1. The H-owned HA case: retain the actual long path and origin

Suppose HA is H-owned. For this case only, use H contact coordinates
\[
 H=[0,1]^2,\quad P_A=(p,1),\quad n_A=e_y,\quad
 Q_D=(0,0),\quad n_D=(-a_0,-b_0),
 \qquad0<p\le1,\quad a_0,b_0>0.
 \tag{3}
\]
The true origin is O=(X,Y). The whole endpoint-set separation theorem
makes every actual HA contact coordinate strictly positive; p is its
actual mean, including an endpoint-valued mean.

The one inner HB application is distinct from Q_D because B,D are
nonconsecutive physical boundary bodies and are closed-disjoint.
Consequently the full long-arc argument in
`HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md`, Section2, applies
unchanged to this physically unique free D: that part of the argument
needs only the absence of an inner application at Q_D. On the short
top/left H arc, the three real hub normals have respectively zero,
nonpositive and strictly negative horizontal components, impossible
under positive hub balance. The p=1 coincident-mean limit is exactly
the complete local check of `FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md`,
Sections2--3: A's true boundary neighbor is B, and the proof uses no
second inner spoke. Thus the actual path A--B--C--D is clockwise,
along the long top/right/bottom arc. The actual A endpoint torque gives
\[
                                 X>p>0.
 \tag{4}
\]

The three true H neighbors give the geometric origin estimate
\[
 R^2+|O-(1/2,1/2)|^2\le9/2,
                  \qquad-3/10<Y<13/10.
 \tag{5}
\]
This is the positive geometric reweighting of the actual B--C--D
resultants established in the owner reduction; no multiplier or
torque equation is replaced.

Proper concurrence at the two genuine degree-two endpoints gives
positive multiples of their resultants at
\[
 q_A=(p-X,1-Y)+\ell_A e_y,
 \qquad q_D=(-X,-Y)+\ell_D(-a_0,-b_0),
                    \qquad\ell_A,\ell_D\ge0.
 \tag{6}
\]
Both horizontal components are negative. The endpoint resultant
minor angle is greater than120 degrees. If the A vertical component
were nonpositive, (6) would make Y>=1 and both resultants southwest.
If the D vertical component were nonnegative, it would make Y<=0
and both northwest. Both alternatives violate that angle separation.
The directions are therefore, more precisely,
\[
             \arg F_A\in(90,150)\text{ degrees},\qquad
             \arg F_D\in(210,270)\text{ degrees}.
 \tag{7}
\]

The all-mask H-axis support calculation of
`HOUSE_FOUR_LOAD_COLLINEAR_WALL_EXCLUSION.md`, Section3, puts A's
center in the northwest quadrant. It uses only its actual minimum
height1, X>p, Y<13/10 and (F_A)_x<0. In particular it applies to
every A frame and both circle masks; it uses no D support assumption.

## 2. The exact pinned-D height adapter

Return temporarily to the module coordinates (1) and put x=N-1.
Its unique circle corner and center are
\[
                  z_D=(x+1,3/2),\qquad c_D=(x+1/2,1).
\]
Let r=|c_D| and e=c_D/r. Resolve its free point Q=(x,1/2) as
\[
 Q=q_r e+q_tJe,\qquad
 q_r=\frac{x^2+x/2+1/2}{\sqrt{x^2+x+5/4}},\quad
 q_t=\frac{1/4-x/2}{\sqrt{x^2+x+5/4}}.
 \tag{8}
\]
Since7/25<x<=7/16, these exact coefficients obey
\[
                          q_r>9/16,\qquad0<q_t<9/100.
 \tag{9}
\]
For completeness q_r is strictly increasing for x>0: its derivative
has positive numerator
\(x^3+(3/2)x^2+(9/4)x+3/8\). At x=7/25 its value is
\(898/(25\sqrt{4021})>9/16\), since
\((16\cdot898)^2-225^2\cdot4021=2876299>0\).
The other numerator is positive and less than11/100, while r>5/4;
thus q_t<11/125<9/100.

The C-to-D path direction in the module frame is counterclockwise.
Moreover
\[
                         \det(z_D,c_D)=3/4-N/2>0.
 \tag{10}
\]
Thus D's center is counterclockwise from its unique resultant by
less than15 degrees. On changing to the clockwise H frame (3), both
signs reverse: D's center is clockwise from F_D. By (7) its direction
is strictly between195 and270 degrees, hence strictly southwest.
The sign of the transverse term in (8) reverses too. Write the actual
endpoint center directions in the H frame as
\[
 c_A-O=(-r_A\sin\delta_A,r_A\cos\delta_A),\qquad
 c_D-O=(-r_D\sin\delta_D,-r_D\cos\delta_D),
 \qquad\delta_A,\delta_D\ge0.
 \tag{11}
\]
The actual three-contact clockwise path, not an arbitrarily chosen
shorter arc, has length pi+delta_A+delta_D. Each boundary contact has
center gap less than theta=arccos(9/25). Therefore
\[
 \delta_A+\delta_D<\alpha:=3\theta-\pi<\pi/6,
                  \qquad\cos\alpha>89/100,
                  \qquad\sin\alpha<9/20.
 \tag{12}
\]
In the H frame, the transformed (8) is
\(Q_D-O=q_r e-q_tJe\). Its vertical coordinate gives the exact
adapter
\[
                         Y=q_r\cos\delta_D-q_t\sin\delta_D.
 \tag{13}
\]

Apply the completely frame-uniform
`BOUNDARY_UNIT_SUPPORT_HEIGHT.md` to A's actual lower support y=1:
\[
 1-Y\ge f_R(\delta_A),\qquad
 f_R(u)=(R-\sqrt2)\cos u-\frac9{40}\frac{\sin^2u}{\cos u}.
 \tag{14}
\]
On[0,alpha], f_R and
\(g(u)=q_r\cos u-q_t\sin u\) are positive, decreasing and strictly
concave. For g, positivity follows already from (9),(12), and
g''=-g. Their fixed-sum minimum lies at an endpoint allocation;
enlarging the angle sum to alpha only decreases it. The exact two
endpoint estimates, using R-sqrt(2)>11/20, are
\[
 \begin{split}
 f_R(\alpha)+g(0)
 &>\frac{11}{20}\frac{89}{100}
       -\frac9{40}\frac{81/400}{89/100}+\frac9{16}
   =1+\frac{287}{356000},\\
 f_R(0)+g(\alpha)
 &>\frac{11}{20}+\frac9{16}\frac{89}{100}
                  -\frac9{100}\frac9{20}
   =1+\frac{81}{8000}.
 \end{split}
 \tag{15}
\]
Equations(13)--(15) contradict
\(1=(1-Y)+Y\ge f_R(\delta_A)+g(\delta_D)>1\).
This excludes the entire H-owned HA case, including every actual
HA side mean and every physical A mask.

## 3. Non-H-owned HA: a fixed HB contact can be avoided simultaneously

Suppose now HA is not H-owned. The existing owner reduction has
already removed every physically unique free A. Thus HA is either
tip-side-owned or radial-free. In either case it is a singleton at
an H vertex. The endpoint-set distance greater than1 makes that
vertex opposite Q. Use H coordinates just for this selection step:
\[
 H=[0,1]^2,\quad Q=(0,0),\quad P_A=(1,1),
 \qquad n_A\text{ strictly northeast},
 \quad n_D\text{ strictly southwest}.
 \tag{16}
\]

Suppose HB is a singleton at a fixed point R_B, with outward H
normal n_B. It is distinct from Q because B,D are physically
closed-disjoint. Set
\[
       \tau_A=\det(P_A,n_A),\qquad
       \tau_B=\det(R_B,n_B).
\]
Every positive candidate has tau_A!=0. To prove this, suppose
tau_A=0; then n_A is the outward northeast diagonal. The H torque
forces tau_B=0. A fixed H support whose normal line passes through Q
can only be an adjacent vertex with an axis normal or the opposite
vertex P_A with its northeast diagonal. An adjacent-vertex axis
would either violate the strict point-only vertex convention or
give a positive-length shared HB side, contrary to this premise.
The remaining possibility is R_B=P_A and n_B=n_A.

That possibility is physically impossible. If P_A is in an A-side
interior, A occupies the whole inward half-plane of n_A, leaving
no room for B. If it is an A vertex, its free contact normal is
strict in A's vertex cone. Its90-degree tangent sector lies strictly
inside that same180-degree half-plane. Each remaining sector has
angle less than90 degrees and cannot contain B's tangent sector.
This proves tau_A!=0 without restricting B's mask.

The true unloaded H equations now imply
\[
 \mu_A\tau_A+\mu_B\tau_B=0,\qquad
 \mu_A n_A+\mu_B n_B+\mu_D n_D=0,
\]
and hence the necessary condition
\[
 \det(n_D,V)=0,
                 \qquad V=\tau_B n_A-\tau_A n_B.
 \tag{17}
\]
If V=0, these same equations contradict mu_D>0 and tau_A!=0.
Otherwise (17) excludes all but one unoriented line for the free
HD normal. The parameters at Q and at P_A,R_B are independent,
including possible coincidence of the latter two: neither A nor B
can contain Q. Prelist every physical house candidate of this
singleton-HB type. The nonzero analytic conditions (17), together
with the zero-torque degeneracies already excluded, can be avoided
simultaneously with the module selection and all previous finite
open choices before KKT extraction. A four-junction matching cannot
couple these distinct physical applications. Uncrossing preserves
surviving free point normals and only adds shared sides; thinning
deletes atoms. Any newly shared HB belongs to Section4 below.

No selected positive house in this case therefore has singleton HB.
It remains to treat a genuine shared HB side with its actual mean
unrestricted.

## 4. Shared HB must be shifted away from the opposite H vertex

Let u,v be inward H side axes at Q. Since HA is supported at the
opposite vertex and its normal is strict in that vertex cone, the
actual triangle H,A,B makes the H-owned HB axis point toward one
of those two positive axes. A negative axis would have negative
dot product with n_A, contrary to the owned-normal triangle theorem.
Label the axes so the complete shared contact is
\[
 H=Q+[0,1]u+[0,1]v,
 \qquad B=Q+[1,2]u+[s,s+1]v,
 \qquad-1<s<1,
 \quad P_A=Q+u+v.
 \tag{18}
\]
We claim
\[
                                  s<0.
 \tag{19}
\]

Use the u,v frame for this claim: H=[0,1]^2, B=[1,2]x[s,s+1]
and P_A=(1,1). If s>0, the B half-plane and H southwest quadrant
at P_A leave only the northwest quadrant. Any unit occupying it
would share H's top side, contrary to non-H-owned HA. No A-side
interior can occupy that remaining90-degree sector.

If s=0, H and B fill the lower half-plane at P_A. An A-side-interior
contact would need the vertical normal, contrary to n_A being strict
northeast. At an oblique A vertex, both inward side directions must
have positive vertical component. Its unique lowest point is P_A,
so its actual contacts with both H and B coincide there. This is
impossible for a loaded degree-two body with a boundary neighbor,
by the complete coincidence lemma cited in Section1. The aligned
northwest possibility shares HA. The only remaining aligned square
is A=[1,2]x[1,2].

For this final aligned possibility, B=[1,2]x[0,1]. Equality of their
physical containing-circle radii forces the true origin's vertical
coordinate to be1. A's true force is mu_A n_A+gamma e_y, with both
coordinates positive. If its horizontal center relative to the
origin were negative, this would contradict the horizontal sign of
every physical circle corner. At zero horizontal center its radius
would have square5/4, outside the window. Therefore the unique A
circle corner is (2,2), and the true origin is (X,1) with X<3/2.
If its actual AB mean is (zeta,1), 1<=zeta<=2, torque about P_A gives
\[
                       \gamma(\zeta-1)+\lambda(1-X)=0.
 \tag{20}
\]
Hence X>=1 and R^2=(2-X)^2+1<=2, again impossible. This covers the
full s=0 limit and proves (19), with every A mask and AB mean kept.

## 5. The actual BC application determines the remaining H/B frame

Return to the module frame (1). Since P belongs to B and
P-Q=(t,-1), the u-coordinate in (18) obeys
\[
                              (t,-1)\cdot u\ge1.
 \tag{21}
\]
If u_x<=0, the left side is at most1, with equality only for
u=(0,-1). Strict support at Q by the positive HD normal then forces
v=(-1,0). Since both components of g are positive, its B support
has the minimum u and v coordinates. Thus s=-t and
\[
                          B=[h-1,h]\times[-3/2,-1/2].
\]
Its largest corner norm squared is h^2+9/4, strictly smaller than
R^2=(h+1)^2+1/4 because h>1/2. This is impossible for boundary B.

Otherwise u_x>0. Equation(21) makes u_y<0. Write
\[
                   u=(c,-d),\quad v=(-d,-c),
             \qquad c,d>0,\quad c^2+d^2=1,\quad c<d.
 \tag{22}
\]
Indeed the strict HD support gives ac-bd<0, and a>=b implies c<d;
the other choice of v has positive HD projection and is inadmissible.
Put
\[
                    \xi=tc+d,\qquad\eta=c-td.
\]
Then
\[
                         1<\xi<2.
 \tag{23}
\]
For the lower inequality use
\(\xi-1=c(t-c/(1+d))>0\), since
c/(1+d)<sqrt(2)-1<1/2<t. The upper inequality follows from
\(\xi\le\sqrt{1+t^2}<2\).

Because g_x,g_y>0, (22) gives g dot v<0. At the B support P its
v-coordinate must consequently be s. Its u-coordinate is strictly
interior by (23), so g dot u=0. Thus BC is B-owned, and exactly
\[
                  s=c-td<0,\quad g\parallel(d,c),
                       \qquad0<r:=c/d<t<2/3.
 \tag{24}
\]
No B orientation or contact owner has been assumed before this step.

## 6. Every corner of B is strictly inside the circle

The B center has strictly positive u-coordinate:
\[
                  Q\cdot u+3/2=(N-1)c-d/2+3/2>0.
\]
Its v-coordinate is
\[
                Q\cdot v+s+1/2=\tfrac12(1+c)-hd<0.
 \tag{25}
\]
Here is a uniform exact check of the strict sign. Divide by d and
use r<t, so it suffices to prove
\[
             h>\tfrac12\bigl(\sqrt{1+t^2}+t\bigr).
\]
But h=1/t+t/2-1, and this inequality is equivalent to
\(2(1-t)>t\sqrt{1+t^2}\). By (2), t<16/25 and t<32/51. Also
\(\sqrt{1+t^2}<19/16\), since
\(881/625<361/256\) with cross-product gap89. Therefore
\(t(2+\sqrt{1+t^2})<(51/16)t<2\), as required.

The true farthest B corner is consequently its outer-u, lower-v
corner. Since P has coordinates (xi,s) in the translated B frame,
this corner is
\[
                 z_B=P+\ell u,
                  \qquad\ell=2-d-tc>0.
 \tag{26}
\]
Put k=2d-1>0. From r<t and c=rd,
\[
                    \ell<2-1/d,
                  \qquad\ell c\le rk,
                  \qquad\ell d\le k.
\]
The two signed components in (26) give
\[
                         |z_B|^2\le(h+rk)^2+(1/2+k)^2.
 \tag{27}
\]
On0<r<2/3,
\[
                 k\le1,\quad
                 k^2(1+r^2)=(2-\sqrt{1+r^2})^2\le1,
                           \qquad rk<4/9.
 \tag{28}
\]
For the last bound,
\(r(2/\sqrt{1+r^2}-1)\) is increasing up to2/3 because
its derivative is \(2/(1+r^2)^{3/2}-1>0\), using2197<2916.
Its endpoint value is
\(4/\sqrt{13}-2/3<4/9\), using1296<1300.

Subtract R^2=(h+1)^2+1/4 from (27), and use (28):
\[
 \begin{split}
 |z_B|^2-R^2
 &\le k^2(1+r^2)+k+2hrk-2h-1\\
 &<1-\frac{10}{9}h<0.
 \end{split}
 \tag{29}
\]
The signs in (25) show that every other B corner is no farther than
z_B. Thus B is circle-clear, contradicting its prescribed positive
boundary load. This excludes the entire shared-HB case.

## 7. Exhaustive conclusion and selection scope

Section2 excludes every H-owned HA. In the remaining full HA domain,
Section3 excludes a singleton HB by a compatible finite selection,
and Sections4--6 exclude every shared HB directly, retaining its
actual mean. These are all physical HB contacts. The initial module
already covered both free D-vertex positions, every BC contact type
and every physical C mask before forcing the exact radial C.

All finite selections are imposed simultaneously before extracting
the necessary physical certificate; no existing positive force is
changed afterward. Every selected candidate tuple and all zero
corner-weight endpoints were included. No HC contact or force, no
degree-two equation for B and no alignment of an unproved frame is
introduced. The four arbitrary extra squares remain fixed throughout.

The entire lower unique-free/shared alternative is therefore empty.
Together with the complete collinear-wall exclusion and the exhaustive
owner reduction, the full four-load house is excluded. This is a core
exclusion, so no exterior packing-capacity argument is required.
The other house load orbits remain separate until their own complete
proofs are assembled. No numerical parameter cover, Lean compilation
or CI is used.
