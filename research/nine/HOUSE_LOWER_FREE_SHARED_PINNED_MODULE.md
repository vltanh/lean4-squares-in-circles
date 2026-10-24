# The lower free/shared house endpoint forces one exact pinned two-body module

**Status: complete hand physical-mask and generic-selection reduction;
root and separate independent full hand audits passed.** Use the
four-load house labels
\[
 H=5,\quad A=3,\quad B=1,\quad C=4,\quad D=2,
\]
with positive boundary path A--B--C--D and exactly the three hub spokes
HA,HB,HD. Work throughout79/40<=R<=sqrt(1105)/16. H is clear; the
four path bodies are loaded. All four completion squares remain.

Assume the sole remaining free-endpoint domain from
`HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md`: HD is genuinely free,
D has one physical circle corner, and DC has a positive-length shared
side. Its actual shared-side force mean is retained.

**Theorem.** A compatible necessary certificate has the following entire
physical module, after one rigid choice of orthonormal coordinates about
the true disk origin:
\[
 \begin{gathered}
 N=\sqrt{R^2-9/4},\quad T=\sqrt{R^2-1/4},\quad
 h=T-1,\quad t=T-N,\\
 D=[N-1,N]\times[1/2,3/2],\qquad
 C=[h,h+1]\times[-1/2,1/2],\\
 Q=H\cap D=(N-1,1/2),\qquad
 P=B\cap C=(h,-1/2).
 \end{gathered}
 \tag{1}
\]
C has two physical circle corners, both with strictly positive circle
weights. BC is a singleton; its normal from B into C has both components
strictly positive. The normal from H into D is (a,b), with a>=b>0.
No missing HC contact or force is inserted.

The distinction between a free D vertex incident to the DC side and
one opposite that side is essential. Sections2--3 cover both before
any radial-C conclusion is used. In particular the triangle HDC is
never assumed.

## 1. A uniform bound on every point of the true hub

The three actual hub neighbors A,B,D give the geometric origin estimate
in `HOUSE_FOUR_LOAD_ENDPOINT_OWNER_REDUCTION.md`, Section1:
\[
                  |c_H|^2\le9/2-R^2<3/5.
\]
Every point of H is within1/sqrt(2) of its center. Consequently
\[
                  |q|<\sqrt{3/5}+1/\sqrt2<3/2
                        \qquad(q\in H).
 \tag{2}
\]
For the final exact comparison, square once and use
\(\sqrt{6/5}<23/20\), since6/5<(23/20)^2. This is a geometric
reweighting of the three true neighbors, not a replacement stress.

All nonconsecutive boundary bodies among A,B,C,D are physically
closed-disjoint, as proved in the same source. In particular B and D
cannot share even a vertex.

## 2. Incident free vertex: a shared BC side is impossible

Suppose first that the free HD vertex Q is incident to the DC side.
Choose its two inward D axes and reflect the picture if needed to get
\[
 \begin{gathered}
 Q=(X,Y),\quad D=Q+[0,1]^2,\quad
 C=Q+[t,t+1]e_x+[-1,0]e_y,\quad-1<t<1,\\
 n_{HD}=(a,b),\qquad a,b>0.
 \end{gathered}
 \tag{3}
\]
This chart is being used only in the stated incident case; it is not
inferred from an absent HDC triangle. D's full force equation is
\(F_D=\mu(a,b)+\gamma e_y\). Thus its unique circle corner is
\(z_D=(X+1,Y+1)\), with X,Y>-1/2. If the actual shared mean is
\(Q+\tau e_x\), the equations are
\[
 \lambda(X+1)=\mu a,\quad
 \lambda(Y+1)=\mu b+\gamma,\quad
 \lambda(Y-X)=\gamma\tau,
 \qquad\lambda,\mu,\gamma>0.
 \tag{4}
\]

For t<0, Q is in a relative C-side interior. Its half-plane, the D
quadrant and the H quadrant fill the whole tangent turn, forcing HD
to share a side, contrary to the free premise. For t=0, the exact
two parallel circle equations force Y=0 and X+1=sqrt(R^2-1)>1.
Then the last equation in (4) has negative left side and nonnegative
right side. Therefore
\[
                    0<t\le\tau\le1,\qquad Y>X,
                           \qquad a\ge b>0.
 \tag{5}
\]
The last comparison follows by eliminating mu,lambda in (4), exactly
as in the local calculation of
`FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md`, Sections2.1--2.2. That
calculation uses no triangle once the incident chart has been supplied.

C's center has positive first coordinate. Its full physical farthest-
corner equation, compared with D's, gives
\[
 R^2=(X+1)^2+(Y+1)^2,
 \qquad
 Y=\begin{cases}
 (t/2)(X+1)+t^2/4,&Y\le1/2,\\
 t(X+1)+t^2/2-1/2,&Y\ge1/2.
 \end{cases}
 \tag{6}
\]
Both expressions agree at the physical two-corner transition, and
Y>0 in both cases. They also give the uniform bound
\[
                                t>12/25.
 \tag{7}
\]
Indeed t<=12/25 would put the transition Y=1/2 at
\(X=1/t-1-t/2\ge253/300>1/2\), whereas Y>X and R^2<9/2 force
X<1/2. In the lower branch, the crossing Y=X has
\(X+1=Y+1=(4+t^2)/(4-2t)\). Both actual positive quantities are
smaller than this crossing value, which increases with t. Hence
\[
 R^2<2(661/475)^2<(79/40)^2,
 \qquad (79/40)^2-2(661/475)^2=399137/14440000>0,
\]
a contradiction.

Now suppose BC shares a positive-length side. B is parallel to C,D.
Every physical C circle corner has positive first coordinate, so
\((F_C)_x>0\). The DC force on C is downward. Thus BC must be
vertical, with force on C to the right, and
\[
 B=Q+[t-1,t]e_x+[r-1,r]e_y,\qquad-1<r<1.
 \tag{8}
\]
Physical closed-disjointness of B,D forces r<0. The C force equation
also gives \((F_C)_y<0\), so Y<=1/2, including a two-corner mask
with unequal weights. Equation(6) and the disk bound imply
\[
               X>0,\qquad X+1\ge\sqrt{R^2-9/4}>32/25.
\]
B consequently has positive horizontal and negative vertical center
coordinates. Its farthest corner is \((X+t,Y+r-1)\), while C has
the physical circle corner \((X+t+1,Y-1)\). With k=-r in(0,1),
equal radii give
\[
            k^2+2k(1-Y)=2(X+t)+1<3-2Y,
                    \qquad X+Y+t<1.
 \tag{9}
\]
But X,Y>0 and R^2>=R_0^2 imply X+Y>7/10: otherwise
\(R^2=2+2(X+Y)+X^2+Y^2\le389/100<R_0^2\), where R_0=79/40.
Together with (7), this contradicts (9). Thus BC cannot share a
side when Q is incident to DC.

## 3. Opposite free vertex: a shared BC side is also impossible

Suppose Q is on the D side opposite DC, and suppose BC shares a
side. All three bodies B,C,D are parallel.

First the two C contact axes cannot be collinear. If they were, the
nonzero C circle resultant would be along a common frame axis. Its
physical mask would therefore be radial S in that direction, with
both circle weights equal. A neighbor on its outer radial face
cannot fit in the disk; a neighbor on its inner radial face is
circle-clear by `C7_FORCE_POLYGON.md`, Lemma2.1. This covers equal
as well as opposite C faces and contradicts a boundary neighbor.

The two axes are therefore perpendicular. Reflect and interchange
axes so that their forces into C point right and up, respectively:
\[
 \begin{split}
 C&=[x,x+1]\times[y,y+1],\\
 D&=[x-1,x]\times[y+s,y+s+1],\\
 B&=[x+t,x+t+1]\times[y-1,y],\qquad -1<s,t<1.
 \end{split}
 \tag{10}
\]
Both C resultant coordinates are positive, so x,y>=-1/2 and its
northeast corner is a physical circle corner:
\[
                         R^2=(x+1)^2+(y+1)^2.
 \tag{11}
\]
Q lies on the left D side, at first coordinate x-1, and the HD
inward normal has positive first coordinate. At a strict vertex of
H with such a normal, at most one inward side axis has positive
first coordinate, and that coordinate is strictly less than1.
Thus every H point has first coordinate strictly less than x.
Since H touches B, (10) forces
\[
                                  t<0.
 \tag{12}
\]
The B,D horizontal intervals now overlap in positive length. Their
physical noncontact consequently makes s>0.

We next show y<0. If x,y>=0, every B horizontal endpoint lies strictly
between x-1 and x+1, while its vertical absolute coordinates are
at most y+1. Every B corner is then strictly inside the C circle.
If x<0 and y>=0, (11) implies y>7/10 because
\(\sqrt{R_0^2-1}>17/10\). Every B corner instead satisfies
\[
 |z|^2<(1-x)^2+y^2,
\]
whose difference from (11) is
\(-4x-2y-1\le2-2y-1<0\). This is again impossible.
Hence
\[
                           -1/2\le y<0,
                              \qquad x>7/10.
 \tag{13}
\]

D has positive horizontal and vertical center coordinates: x>7/10
and y+s+1/2>0. Its unique farthest corner is
\((x,Z)\), where
\[
                      Z=\sqrt{R^2-x^2}=y+s+1>y+1.
\]
The bound s<1 gives Z<y+2, and comparison with (11) yields
x<y+1. Consequently
\[
 R^2<(y+2)^2+(y+1)^2,
\]
which, for y<=-1/5, is at most97/25<R_0^2. We have proved
\[
                    -1/5<y<0,\qquad7/10<x<1,
                               \qquad Z>17/10.
 \tag{14}
\]

The upper left D vertex has height Z>17/10 and violates (2).
The free HD vertex must therefore be
\[
                         Q=(x-1,Z-1),
                      \qquad n_{HD}=(a,b),\quad a,b>0.
\]
Write the actual DC mean as \((x,Z-1+\tau)\). The full overlap
gives \(\tau\le y+2-Z<1\). If the C force on D has magnitude
gamma, the genuine D force and torque equations are
\[
 \mu a-\gamma=\lambda x,\quad
 \mu b=\lambda Z,\quad
                   \gamma\tau=\lambda(Z-x)>0.
 \tag{15}
\]
In particular0<tau<1, and
\[
                 \frac ab=\frac{x+(Z-x)/\tau}{Z}>1.
 \tag{16}
\]
Every H point now has first coordinate strictly less than
\(Q_x+b/\sqrt{a^2+b^2}<Q_x+1/\sqrt2\). Indeed any inward
H axis with positive first coordinate is (c,-d), with ac-bd<0;
orthogonality makes the other axis have negative first coordinate.
If neither axis has positive first coordinate, the bound is immediate.

On the other hand B has positive first and negative second center
coordinates. Put F=x+t+1. Its circle equation and (11) give
\[
 F=\sqrt{R^2-(y-1)^2}>3/2,
 \qquad x+1>17/10,
 \qquad t=\frac{4y}{F+x+1}>-1/4.
 \tag{17}
\]
Here the lower bound on F uses y>-1/5 and
\(R_0^2-36/25>9/4\). To meet B, H needs a horizontal advance
from Q of at least1+t>3/4>1/sqrt(2), contradicting (16).
This excludes the entire opposite-vertex/shared-BC family, including
every actual shared mean and all physical C masks.

Together Sections2--3 prove that BC is a singleton without any
incident-side premise on Q.

## 4. A shared-block selection for every free D vertex

Let z_D be D's unique physical circle corner. We first have
\[
                              \det(Q,z_D)\ne0.
 \tag{18}
\]
Indeed the only non-circle square vertex collinear with its unique
circle corner is the inner vertex of a radial D square. If Q were
that vertex, torque about Q would force the actual DC mean P_DC to
obey \(\det(P_{DC}-Q,n_{DC})=0\). If P_DC=Q, the two actual
applications of the loaded degree-two D coincide, impossible with a
boundary neighbor by `FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md`, Section2.
If P_DC!=Q, the full side/vertex/mean calculation of
`GENERAL_FIXED_TIP_NORMAL_SELECTION.md`, Section2, excludes that
normal line: a side-interior point cannot have this projection from
Q, and a different vertex would use the outer support
R/sqrt(2)>R-1. That calculation does not require P_DC to have been
fixed before selection. Thus (18) holds for every surviving mean.

Suppose C's circle force uses at most one physical corner. This
includes a unique physical corner and either one-active mask of a
radial C. Choose that active corner z_C. In common D,C side axes,
take the DC normal to be vertical. Each component of either physical
circle corner has absolute value at least1/2. Define
\[
                w_D=Jz_D,\qquad
                w_C=\frac{(z_D)_x}{(z_C)_x}Jz_C.
 \tag{19}
\]
These translations annihilate each circle force and give equal
normal velocities across DC, for every actual mean. Rigid rotation
of the two-body block about the true origin is a second virtual
motion annihilating the same internal forces.

Let P be the fixed BC point and n,m the outward block normals at
Q,P. Eliminating their two positive magnitudes from the two virtual-
work equations gives
\[
 \det(Q,n)(m\cdot w_C)-\det(P,m)(n\cdot w_D)=0.
 \tag{20}
\]
The actual boundary-pair moment det(P,m) is nonzero. By (18), Q and
z_D are noncollinear. The coefficient
\[
                    (m\cdot w_C)JQ-\det(P,m)Jz_D
 \tag{21}
\]
is therefore nonzero for every fixed genuine m. The free HD normal
can avoid (20) in its nonempty strict interval.

Prelist all ordered physical house candidates, both free D-vertex
types and both possible one-active C corners. The Q and P parameters
are independent: a common junction or opposite-pair matching would
put physically disjoint B,D at one point. After clearing the nonzero
denominators, (20) is a nontrivial analytic equality on the permitted
product of intervals. Avoid it with every earlier finite strict and
generic condition before obtaining multipliers. Uncrossing preserves
surviving free directions and only adds shared-side forces; thinning
deletes atoms. Every possible final block was prelisted, and
Sections2--3 exclude a newly shared BC directly. No actual DC mean
has been frozen.

It follows that C has two physical circle corners and both weights
strictly positive.

## 5. Radial C forces the module and the incident free vertex

Choose the radial C frame so
\[
                     C=[h,h+1]\times[-1/2,1/2],
                 \qquad h=\sqrt{R^2-1/4}-1.
\]
The shared DC contact cannot be a radial C side: the outer face
leaves insufficient disk width, and the inner face makes D
circle-clear by `C7_FORCE_POLYGON.md`, Lemma2.1. Reflect vertically
so D lies along the top tangential side. Its horizontal overlap with
C makes its horizontal center positive. Its circle equation gives
exactly
\[
                         D=[N-1,N]\times[1/2,3/2],
                            \qquad N=\sqrt{R^2-9/4}.
 \tag{22}
\]
Write t=h+1-N. The full window gives0<t<1, so the lower right D
vertex (N,1/2) belongs to a relative C-side interior. At that point
the C half-plane and D quadrant leave precisely the other quadrant;
any third unit would share a positive D-side segment, contrary to
the free HD premise. The upper right vertex is D's unshareable
circle corner. The upper left vertex has norm greater than3/2 and
is excluded by (2). The only free vertex left is therefore
\[
                             Q=(N-1,1/2).
 \tag{23}
\]
This proves incident-side routing as a conclusion, rather than
borrowing it from a nonexistent HDC triangle. The exact equations
(4)--(5) now give n_HD=(a,b), a>=b>0.

C's full degree-two force equation gives a positive first component
of the BC normal g from B into C. If g_y<0, its C support is the
upper inner vertex (h,1/2), which belongs to the relative interior
of D's lower side; this violates physical noncontact BD. If g_y=0,
the radial-inner-face contact makes B circle-clear by the same
shallow-contact lemma. Hence g_y>0, and its support is exactly
\[
                              P=(h,-1/2).
 \tag{24}
\]
BC is a singleton by Sections2--3. All assertions in (1) follow.

The following exact bounds will be used in the final exclusion:
\[
 \frac{32}{25}<N\le\frac{23}{16},\qquad
 T>\frac{191}{100},\qquad h>\frac9{10},\qquad
 \frac12<t=\frac2{T+N}<\frac{200}{319}<\frac{32}{51}<\frac23.
 \tag{25}
\]
The lower comparisons follow by squaring at79/40; the N upper
bound is exact atR^2=1105/256. For t>1/2 use T+N<4, for example
T<33/16 and N<=23/16. No numerical root or parameter box is used.

This source proves the full module reduction, not its final exclusion.
Every actual DC mean remains in its full overlap interval, both C
circle weights remain positive, and A,B keep arbitrary physical masks
and all their true forces. The necessary finite choices occur before
certificate extraction. No Lean compilation or CI is used.
