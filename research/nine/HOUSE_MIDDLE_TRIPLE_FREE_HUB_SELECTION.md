# The middle-triple house needs an owned hub interface

**Status: complete hand geometric and finite-selection implication; root and
separate independent full hand audits passed.** This extends the earlier
all-unique mask reduction to **every physical circle mask**, by removing the
variable-mean alternatives geometrically before making a local selection.

Work with the exact positive middle-triple house
\[
                        AD,\ AT,\ DT,\ AB,\ BC,\ CD,
\tag{1}
\]
where A,D are unloaded exact-degree-three hubs and T,B,C are loaded.
The existing strict point-normal and planar uncrossing convention is retained.
Every application on a shared side is its actual aggregate mean.

**Theorem.** The necessary physical certificate can be selected so that AD
cannot be a genuine free vertex/vertex edge in (1). This covers all physical
one-/two-circle-corner masks and all actual means. Combined with
HOUSE_MIDDLE_TRIPLE_SHARED_HUB_EXCLUSION.md, every remaining middle-triple
house has a singleton AD contact whose normal is owned by exactly one hub.
The latter whole owner family is not excluded here.

All geometric steps below are radius-free. The circle masks and the four
completion squares are unchanged. The final normal selection uses only one
unloaded hub's local force and torque, not unknown circle weights.

## 1. Two elementary point-contact facts

Assume for now that AD is free, at p. Its normal is strict in both
vertex cones, so p is a vertex of each hub and their intersection is
only p. Their inward right-angle sectors at p have no common boundary
ray: such a ray would give a positive common side segment.

If another unit touching both A and D meets A at a non-axis support
vertex opposite p, the strict support-span argument excludes its D
contact. Indeed the two A normals are in strictly opposite vertex
cones, and a unit attached at the opposite vertex has projection span
strictly less than1 in the AD direction, whereas the AD vertex has
projection separation strictly greater than1. This is the same complete
opposite-vertex fact in FAN_HUB_OWNED_ENDPOINT_EXCLUSION.md, Section2.
An A-owned normal in the triangle A,D,T instead has nonnegative dot
product with the AD normal, by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md.
Both facts retain every actual contact feature.

We also use a local consequence of zero load. If an unloaded square has
two positive forces applied at one vertex p, one of them strict in that
vertex cone, and only one other positive force, that third force strictly
exposes the opposite vertex. Its line of action passes through p, by
torque about p. It is therefore the outward diagonal at the opposite
vertex. To see the strict support claim, express the first two outward
normals in the inward side frame at p: both coordinates are nonpositive,
and the strict force makes their positive sum negative in both. The third
normal is strictly positive in both coordinates.

## 2. A shared roof side is impossible with a free AD edge

We prove the entire AT shared-side alternative. Reflection exchanges
A,D and B,C for DT. Normalize
\[
 A=[0,1]^2,\qquad p=(1,1),\qquad n_0=(a,b),\qquad a,b>0,
                  \quad a^2+b^2=1,
\tag{2}
\]
where n_0 points from A to D. The owned-normal triangle fact makes the
shared AT normal either +e_x or +e_y. Interchange the coordinate axes
if necessary and take it to be +e_y. Then
\[
                 T=[s,s+1]\times[1,2],\qquad -1<s<1.
\tag{3}
\]
The complete unloaded A balance gives an outward AB force proportional to
\[
                             -\gamma n_0-\mu e_y,
                          \qquad\gamma,\mu>0.
\tag{4}
\]
It is strictly southwest, acts at (0,0), and puts B in
\[
                            \gamma n_0\cdot x+\mu x_y\le0.
\tag{5}
\]
The strict support-span lemma also gives max_B x_x<1.

### 2.1. The roof shifted away from the free junction

If 0<s<1, p is in the relative interior of T's bottom side. Its local
upper half-plane and A's southwest quadrant leave only the southeast
quadrant for D. D must then be the aligned square [1,2] times [0,1],
which shares A's right side. This contradicts free AD.

Suppose -1<s<0 and put c=-s in (0,1). The actual DT contact requires
D to reach strictly left of p, whereas nonoverlap with A keeps that
leftward inward direction strictly above its top side. Consequently
D's two inward axes have the form
\[
                   u=(-c',d'),\qquad v=(d',c'),
                   \qquad c',d'>0,\quad c'^2+d'^2=1.
\tag{6}
\]
This is an exhaustive quadrant choice: an inward left-and-down ray
would enter A, and a horizontal left ray would share an AD side.

The leftmost D vertex is p+u=(1-c',1+d'). If c'<c, D and T are
separated horizontally. If c'>c, this vertex lies strictly inside T,
since 0<1-c'<1-c and1<1+d'<2. Thus physical contact and nonoverlap
force
\[
                              c'=c.
\tag{7}
\]
The DT contact is exactly p+u, in the relative interior of T's right
side, so the D-to-T normal is -e_x.

Write v=(d',c) and u=(-c,d') from now on. Strictness of the original
AD normal at D gives n_0 dot u>0 and n_0 dot v>0. The complete
unloaded D balance makes its outward DC vector proportional to
\[
                              \gamma n_0+\nu e_x,
                              \qquad\nu>0.
\tag{8}
\]
This vector has both global components positive. Its v-coordinate is
strictly positive, so every actual DC application has the form
\[
                              q=p+v+\tau u,
                              \qquad0\le\tau\le1.
\tag{9}
\]
This includes its entire shared-face mean interval when the u-coordinate
of the normal vanishes. In particular
\[
                         q_y\ge1+c>1,
                 \qquad n_0\cdot q>n_0\cdot p=a+b>1.
\tag{10}
\]
Use the support-span lemma at the minimum-DC support point q of C,
first in direction -e_y and then in direction -n_0. Both scalar
products with (8) are strictly negative. Equations(9)--(10) yield
\[
                         \min_C x_y>0,
                     \qquad\min_C n_0\cdot x>0.
\tag{11}
\]
These two inequalities make every C point violate (5), so B and C
are disjoint. This contradicts their physical edge.

### 2.2. The roof endpoint at the free junction

It remains to keep s=0 in (3). A and T then fill the left half-plane
locally at p. Since D is a vertex contact, its whole inward quadrant
is in the right half-plane.

If a D inward side is vertically downward, D shares A's right side,
contrary to free AD. If one is vertically upward, then
D=[1,2] times [1,2] and DT is a full shared vertical side. Its clear
force balance makes DC strictly northeast, applied at (2,2).
The support-span lemma gives min_C x_x>1, while (4) gives max_B x_x<1.
Again BC is impossible.

In every remaining frame both inward D axes have strictly positive
horizontal components. Then D meets T only at p. Its two forces from
A and T are applied at p, with the first strict in D's vertex cone.
The local zero-load fact in Section1 makes DC the outward diagonal
at D's opposite vertex. The two inward horizontal components have sum
strictly greater than1, by orthogonality. Thus that vertex has first
coordinate greater than2, and the support-span lemma gives min_C x_x>1.
The same B/C separation follows.

All shifts in (3) have been covered. Hence neither AT nor DT can be a
positive-length shared side in a positive free-AD house. No roof mean
was fixed during this argument.

## 3. The roof singleton applications cannot coincide with AD

Both roof intersections are now singletons. If AT contains p, then T
and D both contain p, so DT must also be the singleton p. The local
zero-load fact of Section1 then makes AB and DC diagonal forces at the
opposite vertices of A and D, respectively.

Translate p to0. Let e_A,e_D be their unit inward diagonal directions,
so those opposite vertices are sqrt(2)e_A and sqrt(2)e_D. Since the
closed inward quadrants of A and D are disjoint except at their vertex,
the minor angle between their diagonals is strictly greater than pi/2.
Thus
\[
                              e_A\cdot e_D<0.
\tag{12}
\]
At B's minimum-e_A support point sqrt(2)e_A, the strict support-span
lemma in direction e_D gives
\[
                   \max_{x\in B}e_D\cdot x
                         <\sqrt2(e_A\cdot e_D)+1<1.
\tag{13}
\]
But C lies in e_D dot x>=sqrt(2). This prevents BC contact. Therefore
the two roof singleton applications are each distinct from p.

## 4. The two external shared sides cannot coexist

Suppose both AB and DC have positive-length shared sides. In the A
frame (2), let its AB axis be n_B. An axis +e_x or +e_y would force
AT strictly southwest by the unloaded A balance, giving the forbidden
opposite-vertex roof contact. If n_B=-e_x, the AT y-component is
strictly negative. Its x-component cannot be negative (the same
opposite-vertex obstruction) or zero (the owned-normal triangle fact).
Thus, after an axis interchange if necessary, the exhaustive possibility is
\[
 n_B=-e_x,\qquad A\cap T=\{p-e_y\},
             \qquad n_{AT,x}>0>n_{AT,y}.
\tag{14}
\]
In particular B is an aligned square in x<=0.

At D use its inward orthonormal frame at p. Its DA force has both
coordinates strictly negative. The same force and triangle argument
shows that DC must be one of its positive side axes, say u, and the
roof singleton must be the adjacent vertex p+v, where u,v are the
two inward D axes. The roof normal there is strictly negative in its
u-coordinate and strictly positive in its v-coordinate. A nonpositive
DC axis would instead force the forbidden roof vertex opposite p.

The unit roof T contains both p-e_y and p+v. Its diameter bound gives
\[
                          |v+e_y|^2=2+2v_y\le2,
                         \qquad v_y\le0.
\tag{15}
\]
The equality case cannot be silently removed. If v=-e_x, either D
shares A's top side or its interior overlaps A. If v=e_x, the downward
other D axis would share A's right side. The only remaining equality
frame is D=[1,2] times [1,2], with roof points (1,0) and (2,1).
They are a full square diagonal, forcing T=[1,2] times [0,1]. This
would share A's right side, contrary to the strict roof normal (14).
Thus
\[
                                    v_y<0.
\tag{16}
\]
Nonoverlap with A and free AD now force v_x>0. The other perpendicular
inward axis u must point northeast; its opposite choice would enter A.
Consequently u_x,v_x>0.

Since DC is a positive-length shared side in direction u, the exact
square C is
\[
                         C=D+u+\delta v,
                              \qquad -1<\delta<1.
\tag{17}
\]
Its minimum first coordinate obeys
\[
                     \min_C x_x
                       \ge1+u_x-v_x>0,
\tag{18}
\]
because u_x>0 and v_x<1. But max_B x_x=0 by (14), contradicting BC.
Thus at least one of AB and DC is a singleton.

## 5. A fixed unloaded-hub star supplies the nonzero determinant

Choose the hub with singleton external edge, say A. By Sections2--4
its two other applications q=A intersect T and r=A intersect B are
fixed physical singleton points, and q!=p. Let n_T,n_B be their actual
outward normals from A. Define their moments about p by
\[
                         t_T=\det(q-p,n_T),
                   \qquad t_B=\det(r-p,n_B).
\tag{19}
\]
The roof moment is nonzero. Indeed a non-axis A normal puts q at an
adjacent vertex, by Section1; its strict tangential component makes
t_T nonzero. An A-owned roof normal selects a side containing p by
the triangle theorem, and q!=p on that unit side again makes its
normal line miss p. Hence
\[
                                      t_T\ne0.
\tag{20}
\]

The complete positive unloaded A equations are
\[
                \gamma n_0+\mu n_T+\nu n_B=0,
                      \qquad\mu t_T+\nu t_B=0.
\tag{21}
\]
A positive star necessarily has t_B!=0. Eliminating its two other
magnitudes gives the necessary condition
\[
 \det(n_0,V)=0,
              \qquad V=t_Bn_T-t_Tn_B.
\tag{22}
\]
If V=0, (21) would force gamma n_0=0 and no positive star exists.
Otherwise (22), with the other two normals fixed, permits only finitely
many free directions at AD.

The free AD parameter is independent of the other two parameters in
(22). Their relevant applications are distinct from p: q!=p was
proved above, and r=p would make t_B=0 and already prevent a positive
star. Matched four-junction choices couple only opposite pairs at the
same physical point. They therefore do not identify this AD parameter
with either of those at q,r. The latter two points need not be assumed
distinct from one another.

## 6. One finite simultaneous selection, without circle-weight premises

Before KKT, prelist every ordered physical house with free AD and the
fixed-singleton alternative of Section5, including both choices of hub.
This is a finite list in the given packing. If V vanishes identically
on a permitted product of the other normal intervals, (21) already
rules out a positive star there. Otherwise fix parameters with V!=0
and vary the independent AD direction. Equation(22) is then not an
identity. It is a nontrivial real-analytic equality with zero set of
empty interior, so it can be avoided together with all existing finite
strict/nonradial and matched-junction conditions, inside their already
required open domains.

The purely geometric Sections2--4 dispose of every shared-side or
coincident-roof alternative before this selection is invoked. Thus the
argument has not treated any variable mean as a fixed application.
It has made no assumption about one physical circle corner, equal
corner weights, or an unknown global circle-load ratio.

After physical uncrossing, every surviving free AD normal retains its
chosen direction. Added forces occur only on actual shared sides;
thinning only removes atoms. Any final middle-triple free-AD house
would either violate one of Sections2--4 or satisfy a prelisted
forbidden condition (22). This proves the theorem for all its physical
masks and every completion square.

The remaining AD side-owner alternative is not a free parameter and
is not removed by (22). Its full geometry and force equations still
require a whole-family exit. No numerical pose sample, circle-angle
subdivision, Lean compilation or CI is used here.
