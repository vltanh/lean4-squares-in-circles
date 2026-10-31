# A closed-origin outside unit excludes a genuine leaf-decorated triangle

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope
after full root and separate independent source/scope reviews.** See
REVIEW_C2_34_THREE_BRIDGES_NEW_UNIFORM_TOOLS_AND_COVER_ROOT_2026_10_27.md
and REVIEW_CLOSED_ORIGIN_DECORATED_TRIANGLE_MIXED_BLOCKS_2026_10_27.md.
Their mathematical source pins precede this acceptance-only header.
No original ID or whole coarse-cell status is changed by this source.

Retain all nine original physical unit squares, their disjoint open
interiors, the common compatible selected certificate, and

    79/40 <= R <= sqrt(1105)/16,
    d = sqrt(R^2-1/4)-1,
    epsilon = max(d-1,0) < 1/60.

Let H,A,B be an actual positive triangle. A has true positive degree
three, consisting of AH,AB and its genuine radial leaf AL. B has true
positive degree two, consisting of BA,BH. H keeps every original
force, its possible circle mask, and arbitrary true degree. Each
triangle body's complete external system has zero origin moment.

Suppose an actual unit E, distinct from H,A,B,L, contains O in its
closed square.

**Theorem.** This entire original configuration is impossible.

No physical square, positive force, actual application mean, selected
normal, physical circle corner or individual zero weight is removed.
In particular H is not assigned a leaf-only external resultant.

## 1. A contact base through O traps the actual outside unit

We first state the exact physical barrier used at boundary origins.

Let K,P_1,P_2 denote a unit K and two distinct actual K contacts with
the other two units X,Y of a physical triangle. Suppose O belongs to
the relative interior of the segment [P_1,P_2], and E contains O
closed and is distinct from K,X,Y.

Because E contains O, interior disjointness implies O is not in int K.
A supporting line of K at O therefore has zero support after
translation to the origin. Since O is a strict convex combination of
P_1,P_2, both contacts lie on that same line. It is an actual K side,
and O is in its relative interior. After rotation/reflection write

    K on x<=0,
    P_1=(0,y_-), P_2=(0,y_+),    y_-<0<y_+.            (1)

The entire actual E lies in x>=0. Otherwise its segment from O to a
point with x<0, together with interior-point approximation if needed,
would enter int K arbitrarily near its relative side-interior O.

These are precisely the hypotheses of the radius-free contact-triangle
barrier in
GLOBAL_CLOSURE_INTACT_ROOT_D_LEAF_CENTRAL_DISK_EXCLUSION.md, Section 1.
That lemma is purely geometric; its use does not require an intact
petal, a D leaf, or any force equation.

For completeness choose any actual X--Y contact Q. If Q_x<0, a segment
from Q to one of P_1,P_2 enters int K. If Q_x=0 and Q!=O, the two
actual segments Q--P_1 and Q--P_2 cover the base; O belongs to the
relative interior of at least one. That segment lies in its original
X or Y. Since K already occupies the local half-plane x<0, this
other unit must have O in a relative side interior and occupy the
opposite local half-plane x>0. No distinct E containing O can fit.
If Q=O, the three actual units X,Y,E all contain O on the x>=0
side of K; their tangent cones each have angle at least pi/2,
which cannot fit in one half-plane. If Q_x>0, int E has points
near O inside the contact triangle P_1,P_2,Q. Its connected open
interior cannot cross that triangle's occupied boundary, so the
entire E lies in the closed triangle.

The base length is at most one and the altitude at most sqrt(2),
because each edge is contained in its corresponding original unit.
Its area is at most sqrt(2)/2<1, contrary to area(E)=1. This includes
every coincident Q, weak junction and side endpoint.

Thus

    O cannot lie strictly between the two actual triangle
    applications on any one of H,A,B.                  (2)

This geometric statement requires no nonzero-moment premise.

## 2. All low and critical radii are already impossible

B is physically boundary: a true unloaded degree-two vertex whose
two neighbors touch would transmit across a positive width and
separate those neighbors. A is physically clear by its genuine
radial-leaf theorem.

An actual point of E in the open interior of any other unit would
force open-interior overlap. Hence

    O is not in int H, int A, or int B.                 (3)

A genuine D leaf puts O in int A, contrary to (3).

Suppose the genuine leaf is S. If A is tilted relative to its leaf,
choose its actual own axes toward the exposed leaf vertex:

    e_A = a u_A + b v_A,
    a>=b>0, a^2+b^2=1,
    A=[da-1,da] times [db-1,db].                        (4)

For d<=1 both da and db are strictly between zero and one, so O is
in int A, again impossible.

For an aligned A, the whole chart and actual full A equations are

    A=[d-1,d] times [h-1,h],       0<=h<=1,
    alpha e_x + mu_1 n_1 + mu_2 n_2 = 0,
    mu_1 det(p_1,n_1)+mu_2 det(p_2,n_2)=0.              (5)

The full endpoint-slider lemma in
TWO_S_TIP_TRIANGLES_LOW_RADIUS_EXCLUSION.md, Section 1, uses exactly
A3, physical boundary B, and arbitrary H. It gives 0<h<1. For d<1,
(5) then puts O in int A, excluded by (3).

At d=1 the same complete normal cover says either both triangle
normals point west, with their actual mean heights having positive
weighted average zero, or their actual applications are the two
left vertices (0,h),(0,h-1). In the parallel case the B application
has norm at least r=R-sqrt(2)>1/2, hence nonzero height, and its
other actual mean has the strictly opposite sign. Thus in both
alternatives O lies strictly between the actual two A applications.
Section 1 excludes the actual E.

This handles the whole critical endpoint, including both genuine
side-mean endpoints, without applying a high-radius result there.
The only remaining domain is therefore

    L is S, d=1+epsilon>1, 0<epsilon<1/60.              (6)

## 3. The actual triangle has nonzero moment and no origin port base

A has the actual point epsilon e_A in its closed square. E supplies
the actual point O, of norm at most epsilon, in a distinct unit.

The complete local theorem in
TERMINAL_FOUR_BLOCK_NEAR_ORIGIN_TRANSFER_AND_BROKEN_TRIANGLE_CHAIN_EXCLUSION.md,
Section 3, applies to A3, B2, arbitrary H and this second near unit E.
Its second unit needs no leaf, load, force, frame or degree premise.
It proves H physically circle-clear and proves that the actual
triangle's common directed cycle moment is nonzero.

Every complete external resultant F_I is therefore nonzero and the
three are noncollinear. At most one triangle body has parallel cycle
normals, and a parallel pair has the same outward sign. Each genuine
nonparallel concurrence and its original proper ports satisfy

    q_I=t_I F_I, t_I>0,
    P=q_I+l n_I, l>=0.                                (7)

These are the unchanged full-aggregate conclusions of
RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md,
RADIAL_TRIANGLE_CONCURRENCE.md, and the inputs stated in
TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md.

No actual triangle application is O: its positive edge magnitude
times its origin determinant equals the nonzero cycle moment.
If O belonged to any actual port-base segment, it would consequently
be strictly between its two nonzero endpoints, contradicting Section 1.
Thus, for each original triangle unit I with adjacent applications
P_I,Q_I and center c_I,

    O is outside [P_I,Q_I],
    O is outside conv(c_I,P_I,Q_I).                    (8)

For the second assertion, c_I is in int I and O is not. A convex
combination involving c_I with positive coefficient belongs to int I.
The only possible remaining combination is on the excluded base.
This also covers an origin vertex and all degenerate center triangles.

Let u,v be the original positive H-to-A and H-to-B force vectors.
Summing the true private A,B equations, without changing H, gives

    M=u+v=F_A+F_B,      F_H=-M,                         (9)
    F_A=lambda e_A, lambda>0.

At a nonparallel H its actual concurrence is q_H=-tM, t>0.

## 4. The private-center homotopies remain safe at a boundary origin

For B the full original circle resultant has

    F_B.x>0 for every x in B.                           (10)

Indeed every physical circle corner z of B satisfies
z.x>=R^2-R sqrt(2)>0 throughout B, and the actual circle weights
are nonnegative with positive total. If B is nonparallel then
F_B.q_B>0 as well. Its entire center/port/concurrence hull lies
in this strict half-plane.

For an aligned A, (6) gives epsilon<=e_A.x<=d throughout A, and
e_A.q_A>0 whenever A is nonparallel. The same strict-half-plane
argument applies.

For a tilted A use the actual chart (4). Since db<d/sqrt(2)<1 and
both upper endpoints are positive, (3) implies

    da>=1.                                             (11)

Strict inequality is not imposed. The actual whole A lies in the
closed half-plane u_A.x>=da-1>=0, whereas

    u_A.c_A=da-1/2>0,
    u_A.q_A=t_A lambda a>0.                            (12)

Consider only the hull actually needed for the path homotopy,

    conv(c_A,P_A,Q_A,q_A).                             (13)

Every point has nonnegative u_A projection. A representation of O
could use neither c_A nor q_A by (12); it would put O on the actual
base [P_A,Q_A], already excluded in (8). Hence (13) avoids O even
when da=1 and O lies on the original A side.

We do not claim that conv(A union {q_A}) avoids O when da=1.
The smaller hull (13) is sufficient to replace the two real
center-to-port strands by their genuine concurrence strands.
This preserves all original actual contacts and means.

## 5. The root correction uses the full zero-support cap

Suppose H is nonparallel. Let P,Q be its actual applications and
q=q_H=-tM, t>0. The actual force lines through q avoid O:
relative to the independent u,v directions, O-q has the two
strictly positive coordinates t,t, so it is on neither single line.

The difference between the actual root return and the one through q
is the oriented chain

    c_H--P--q--Q--c_H
      =(c_H--P--Q--c_H)+(P--q--Q--P).                  (14)

The first triangle avoids O by (8) and has zero winding. The second
has no O on any edge: the two force lines avoid O and its base is
excluded by (8).

If O is outside that second triangle, including any degenerate case,
its winding is zero. The actual and auxiliary loops have equal winding.

If O is strictly inside, write

    P=q+d_1 u,       Q=q+d_2 v.

In affine u,v coordinates relative to q the triangle has vertices
(d_1,0),(0,0),(0,d_2), while O has coordinates (t,t). Therefore
d_1,d_2>0. Both original root ports are strictly proper in this
alternative.

Since O is not in int H, an actual own axis can be reflected to give

    H=[a,a+1] times [b,b+1],       a>=0.                (15)

The strict-interior relation at O and the nonnegative first
coordinates of P,Q force q_x<0. If both port coordinates were zero,
the x=0 line would already support their entire triangle at O;
strict two-dimensional interiority would be impossible. Thus this
step also includes a=0 without assuming an off-origin H.

Use the exact zero-height geometric cap in
TRIANGLE_ROOTED_FOUR_BLOCKS_CLOSED_ORIGIN_AND_PAIR_EXCLUSION.md,
Section 2. Its hypotheses are nonparallel actual H normals,
positive auxiliary coefficients, a negative-cone q, strictly proper
actual ports, and (15) with q_x<0. They hold with the auxiliary
positive coefficients equal to t times the actual u,v magnitudes.
No auxiliary coefficient replaces an original force equation.

The cap includes a=0 and gives the actual two neighbor centers a
common rectangle of squared diameter

    52124381/53582400 < 1,

contradicting their disjoint unit incircles. The strict-interior
alternative is impossible. Thus every winding-one auxiliary loop
below gives winding one for the original triangle loop.

## 6. All nonparallel/parallel alternatives retain winding one

### 6.1. All three bodies nonparallel

The actual AB contact lies on [q_A,q_B] by properness at both ends.
Choose the orientation with

    angle(F_A)=0, angle(F_B)=theta, 0<theta<pi,
    angle(M)=phi, 0<phi<theta.

The auxiliary triangle q_H--q_A--q_B--q_H has consecutive argument
lifts

    phi-pi, 0, theta, phi+pi.

Each successive gap is strictly between zero and pi. Its winding
is one. Section 4 gives the two private path homotopies; Section 5
gives either the already impossible cap or winding one for the
actual center/contact triangle loop.

### 6.2. H parallel

Write its two positive forces as mu n,nu n, with mu,nu>0. The
independent F_A,F_B have strictly opposite transverse components,
and their proper concurrences give H actual ports at opposite,
nonzero heights. Thus n is an actual H side axis and

    H=[h-1,h]n+[b,b+1]Jn, b<0<b+1,
    P=(h,y_-), Q=(h,y_+), y_-<0<y_+.                  (16)

The absence of O from int H gives h<=0 or h>=1. If h=0, its
actual port base contains O strictly, contrary to (8).
If h>=1, both original neighboring centers have n-projection at
least3/2 and norm strictly below91/60. Their common rectangle has
squared diameter at most

    1/3600 + 4(181/3600) = 29/144 < 1.

This excludes the full height-one endpoint as well as h>1.
Hence h<0.

Let a_0,b_0 be the arguments of the lower/upper ports and a_1,b_1
those of their genuine concurrences. Properness and the positive
resultant cone give

    -pi<a_0<-pi/2, pi/2<b_0<pi,
    a_0<=a_1<0<b_1<=b_0,
    0<b_1-a_1<pi.

The root center return may be replaced by Q--P using (8).
The two horizontal pieces, the actual private concurrence segment
and the root side then have total argument change

    (a_1-a_0)+(b_1-a_1)+(b_0-b_1)+(a_0+2pi-b_0)=2pi.

Section 4 justifies the unchanged private homotopies. Zero proper
lengths contribute zero horizontal increments, not omitted cases.

### 6.3. Exactly one private body parallel

Let I be the parallel one of A,B and J the other. H is nonparallel.
Write F_I=lambda e, and its two true outward pair forces as
-alpha e,-beta e, with alpha,beta>0 and lambda=alpha+beta.
The actual ports toward H and J, after reflection, are

    P=(h,y_-), X=(h,y_+), y_-<0<y_+,
    alpha y_- + beta y_+ = 0.                         (17)

They are distinct and their transverse heights nonzero by the
common nonzero cycle moment. If I=A, its genuine aligned S chart
gives h=epsilon>0. If I=B, (10) gives h>0. No physical leaf shape
or leaf equation is imposed on B.

The actual proper lines have

    P=q_H+l_H e, X=q_J+l_J e, l_H,l_J>=0.

Thus q_H is weakly left of P at negative height and q_J weakly
left of X at positive height. Set

    angle(e)=0, angle(F_J)=theta in (0,pi),
    angle(F_I+F_J)=phi in (0,theta).

The auxiliary loop q_H--P--X--q_J--q_H increases its argument from
phi-pi to theta along its right-going lower piece, its upward side
at h>0, and its left-going upper piece. Its closing increment is
phi+pi-theta in (0,pi), so its winding is one.

The original I center path may be replaced by P--X through the
O-free center/base triangle (8); the nonparallel J uses Section 4.
The root return uses exactly (14), with the full unchanged root
force pair and genuine q_H. Section 5 completes the winding-one
conclusion. Both choices I=A and I=B, all actual side means,
and every zero proper-length endpoint are covered.

These are all actual alternatives, since at most one body is parallel.

## 7. Closed containment still forces the entire E into a contact triangle

The actual center/contact loop is compact, avoids O, and has winding
one. Hence it has positive distance from O and winding one on a
whole neighborhood of O. Interior points of the original E approach
its closed point O, so some point of int E lies in that neighborhood.

The connected open int E is disjoint from the closed H,A,B and all
their occupied center/contact strands. Its winding is consequently
one everywhere. This is the precise replacement for the earlier
open-origin argument; E is never assumed to contain an origin ball.

Move each of the three representative centers to the midpoint of
its two actual adjacent contacts within its own convex unit. This
path homotopy avoids all of int E. Its final loop is the triangle
of the three original contacts, with side midpoints inserted.

A degenerate final triangle has zero winding, already impossible.
Otherwise its interior contains all of int E, and closure contains
the full actual E. Each of its three sides lies inside one original
unit and has length at most sqrt(2). Its area is at most
sqrt(3)/2<1, contradicting the original unit area of E.

All weak physical junctions, coincident path segments and real
application endpoints are retained. No new free face or physical
motion is introduced by these representative-loop homotopies.

## 8. Reusable original scope

The theorem forbids any actual unit outside H,A,B,L from containing
O closed, while keeping arbitrary genuine H degree and its full
external system. Its additional content over the accepted open
version is exactly Sections 1--3's critical/base cover, Section 4's
closed-half-plane homotopy, Section 5's zero-support root cap, and
Section 7's approach from int E.

In particular, suppose a genuine two-edge pendant arm R--T--M is
disjoint from H,A,B,L. Its internal T is bridge-only and genuinely
unloaded in the common minimum-support certificate. If T contains O
closed, take E=T. Otherwise the accepted off-origin transmitter
theorem makes its actual incoming neighbor contain O closed.
The genuine leaf M is physically boundary and cannot contain O,
so that incoming neighbor is R. Taking E=R again contradicts the
theorem. No leaf type, transmitter width, or R degree has been fixed.

Thus an outside genuine two-edge arm cannot coexist with this
leaf-decorated triangle. The statement concerns their complete
original degrees; it does not turn an internal body into a leaf
or drop another branch at A or B.

No whole coarse cell is declared closed here. No new gate ID,
numerical certificate, Lean compilation, CI, remote action or
shared-ledger edit is used.

