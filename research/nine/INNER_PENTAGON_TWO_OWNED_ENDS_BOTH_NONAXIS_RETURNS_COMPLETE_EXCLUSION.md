# Two owned unloaded ends cannot both have nonaxis boundary returns

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed hand owner-interface theorem, frozen for
separate full independent and root review.** This excludes the whole
two-owned-end feature in which neither end's return to B or C is an
axis of that end. The proof retains the actual occupied rim, all four
hub forces, both entire unloaded degree-three stars, and the genuine
loaded E2. No whole original fine family is declared closed.

The common-side argument below is uniform over all actual frames and
all physical circle masks. Its main quantitative step bounds the
entire C square, rather than only a selected C contact or corner.

## 1. Exact statement and complete physical contract

Keep all nine actual interior-disjoint closed unit squares, the
unchanged containing circle, the original compatible selected
physical certificate, and

    79/40 <= R <= sqrt(1105)/16.

The original component has precisely the positive edges

    HA, HB, HC, HD, AB, BC, CD, DE, EA.

H is unloaded with its whole degree four. A and D are unloaded
with their full degree-three stars H/B/E and H/C/E. E is genuinely
loaded with its true two pair forces. The original B3 and C3
equations and every extra square remain. The actual H is inside
the occupied outer rim A-B-C-D-E-A, in the compatible physical
embedding and its full weak-contact sense.

Assume D owns DH and A owns AH. Assume also that the unchanged
DC normal is not a D side axis and the unchanged AB normal is
not an A side axis.

**Theorem.** This complete feature is impossible.

The existing full shared-unloaded-end theorem excludes every
positive-length HD or HA contact. Under the retained strict
singleton convention their actual applications are therefore
strict H vertices and relative interior points of the owned D
and A sides. The entire proof concerns those original points,
normals and magnitudes. It does not choose normals after the
stress has been extracted.

We repeatedly use two complete physical facts. First, in an actual
triangle of unit squares, an owned-side normal at one square has
nonnegative dot product with its other normal in that triangle.
Second, if a unit K has minimum-n support at Q and v is unit with
n.v<0, then

    max_(Z in K) v.(Z-Q) <= sqrt(1-(n.v)^2) < 1.       (1)

For completeness, at a vertex use its two inward orthonormal
edges. Their n components are nonnegative. At most one can have
positive v component, and that component is at most the displayed
semicircle maximum. At an open side, the normal displacement has
nonpositive v component and the tangent interval of length one
gives the same bound. This includes side endpoints and every
original shared mean.

One consequence used below is that neighbors at opposite strict
vertices of H cannot touch. In H=[0,1]^2, a strict southeast
neighbor at (1,0) lies in x>0,y<1, and a strict northwest neighbor
at (0,1) lies in x<1,y>0 by (1). A common point would lie in the
open H. The other opposite pair follows by reflection.

Another elementary consequence of the strict singleton convention
is that a side-interior/strict-vertex contact admits no third
actual unit at that same point. The owned side supplies an occupied
half-plane locally. The other unit's strict right-angle sector
lies inside the remaining half-plane, with neither bounding ray
on its boundary. The two remaining gaps each have angle less
than pi/2. No unit square's local sector can fit in either gap.

## 2. The complete first-end chart and its actual external owners

Normalize the actual D frame and, if necessary, reflect the whole
packing vertically so that

    D=[0,1]^2,
    F_DH=(-gamma,0) at P=(0,t), 0<t<1,
    F_DC=(-c,c+gamma*t) at Q_C=(0,1),
    F_DE=(gamma+c,-c-gamma*t) at Q_E=(1,0),
    gamma,c>0.                                        (2)

Here is the full derivation. The D-owned DH axis and triangle DHC
give (F_DC)_x<=0. Its assumed nonaxis character makes its two
components nonzero, so the x component is strictly negative.
The whole reflection makes its y component positive. Its actual
support is the upper-left D vertex. Full force balance gives a
strict southeast E force at the lower-right D vertex. The full
moment about the lower-left D corner gives its displayed y
coefficient c+gamma*t. Thus (2) uses every original D3 term.

All three physical D ports are distinct singletons. The common
pre-extraction three-singleton selection rule therefore excludes
free normals at each of them. The two strict D-vertex normals
are not D axes, so C owns CD and E owns DE, at relative interior
points of their real sides. Write

    n_C=(-u_0,v_0), 0<u_0<v_0,
    n_E=(p_0,-q_0), 0<q_0<p_0,
    u_0^2+v_0^2=p_0^2+q_0^2=1.                        (3)

These are the original inward normals of C and E. Their entire
side positions remain. In particular (1) at Q_E gives

    min_E x >= 1-q_0 > 0.                             (4)

The actual H has its unique maximum-x point P and can be written

    H=P+[0,1]e_0+[0,1]f_0,
    e_0=(-a_0,-b_0), f_0=(-b_0,a_0),
    a_0,b_0>0, a_0^2+b_0^2=1.                         (5)

The no-third-unit fact at P applies to every other actual unit.

## 3. Both owned ends fix the complete four-corner hub pattern

Let N be the unchanged inward H-to-C normal at its original
application S. Since C contains Q_C and H contains P, support
gives N.(Q_C-P)>=0. Therefore N_y>=0. Equality with N=East
would make S=P, forbidden by the no-third-unit fact. Equality
with N=West is impossible because H's westward support is
a_0+b_0>0 relative to P whereas Q_C has westward coordinate zero.
Thus N_y>0.

More generally the actual support height of H relative to P
satisfies

    h_H(N)=N.(S-P) <= (1-t)*N_y < 1.                  (6)

This excludes either positive own axis +e_0,+f_0, whose support
height is one, and the strict opposite vertex e_0+f_0, whose
unit-normal support height is the sum of two positive components
and is greater than one. The strict vertex e_0 and axis -f_0
have negative y normals. The vertex P admits no third unit.
The only remaining HC features are consequently the H-owned
axis -e_0 on the P-to-f_0 side, or the strict vertex P+f_0.
This is the entire side/vertex cover, including every mean.

A owns HA, so HA strictly exposes an H vertex. It is not P.
It cannot be the opposite vertex P+e_0+f_0: its normal would
have strictly negative x component, and (1) would put the whole
A in x<-(a_0+b_0)+1<0, contradicting AE and (4).

If HA were P+f_0, an HC contact at that same vertex would be a
forbidden third unit at the A-owned side-interior contact. If
instead HC used -e_0, the e_0 components of HA, HC and HD would
all be negative. Full H4 force balance would make HB's e_0
component positive, while the H-owned HC axis and triangle HBC
require that component to be nonpositive. Hence

    P_HA=P+e_0.                                       (7)

If HC still used -e_0, triangle HBC would again give
(n_HB).e_0<=0. The vertex P is unavailable; P+e_0 is unavailable
to B by A's side-interior contact; and the opposite strict
vertex P+f_0 cannot be used by B because A and B touch. The
strict opposite H vertex has positive e_0 component. Among the
four own axes, -e_0 and +f_0 contradict triangle HAB, while
+e_0 contradicts HBC. Only -f_0 remains. But then HA, HB and
HD have negative f_0 components and HC has zero f_0 component,
contrary to the entire H4 force equation. Therefore

    P_HC=P+f_0, with N.e_0<0, N.f_0>0.                (8)

Now every own axis for HB contradicts either triangle HAB or
HBC. The two endpoint-owned contacts exclude P and P+e_0; the
opposite-vertex fact excludes P+f_0. Thus the remaining actual
HB feature is exactly

    P_HB=P+e_0+f_0,
    n_HB=x*e_0+y*f_0, x,y>0, x^2+y^2=1.              (9)

All four original H forces were retained in excluding the axis
alternative. No H3 or H2 equation was substituted.

## 4. The entire second-end torque restricts its E direction

Put V=P+e_0 and let n be the original H-to-A unit normal, so
n_y<0 by its strict H-e_0 support. Let j=J n and write the full
actual A pose

    A=V+[0,1]n+[-kappa,1-kappa]j, 0<kappa<1,
    F_AH=-Gamma*n, Gamma>0.                           (10)

Triangle AHB gives F_AB.n<=0. Since AB is assumed nonaxis in
A, there are rho,sigma>0 and a sign epsilon in {-1,1} with

    F_AB=-rho*n+epsilon*sigma*j,
    F_AE=(Gamma+rho)*n-epsilon*sigma*j.                (11)

These strictly expose opposite A vertices. The full torque about
V gives, respectively,

    sigma=kappa*Gamma+rho       if epsilon=+1,
    sigma=(1-kappa)*Gamma+rho   if epsilon=-1.          (12)

In either case 0<sigma<Gamma+rho. Thus the unchanged AE normal
makes an angle strictly less than pi/4 with n. These three A
ports are distinct physical singletons, so the same already
common selection rule makes B own AB and E own AE.

The E-owned AE axis is one of n_E, -n_E, j_E, -j_E, where

    n_E=(p_0,-q_0), j_E=(q_0,p_0), 0<q_0<p_0.          (13)

The choice j_E is impossible. Its angle is strictly between
pi/4 and pi/2, and its angular distance from every vector with
negative y component is strictly greater than pi/4. This
contradicts n_y<0 and (12).

For the choice -j_E, write the whole E as

    E=Q_E+[0,1]n_E+[-s,1-s]j_E, 0<s<1.

Its original minimum-(-j_E) contact with A is on the side
j_E=1-s. Because AE strictly exposes an A vertex, its E-owned
application is in the relative interior of that side. Thus

    T=Q_E+lambda*n_E+(1-s)*j_E, 0<lambda<1,
    T_x>1.                                            (14)

If n_x<=0, A's owned n-axis and its unit tangent interval give
max_A x<=V_x+1<1, contrary to (14). Hence n=(c,-d) with c,d>0
and j=(d,c). The normal -j_E has negative j component. By
(11) its A support must therefore be

    T=V+n-kappa*j,
    T_x=-a_0+c-kappa*d<1,

again contrary to (14).

The choice -n_E is impossible for the full loaded E2. Here the
two actual E applications lie on opposite owned sides and are
distinct, and their force directions would be opposite parallel.
We give the complete circle argument so no boundary-neighbor
properness premise is being imported. A loaded contained unit
has either one physical circle corner Z=(a,b), with a,b>=1/2,
or two adjacent circle corners (a,+/-1/2), with a>1. This follows
by comparing the squared norms of adjacent actual corners. In
the first case the full resultant F is a positive multiple of
Z; in the second it is k*(a,eta), k>0, |eta|<=1/2, retaining
zero individual corner coefficients. Since the two opposite
pair forces sum to -F, their axis is the F axis, and one would
point along +F. If the mask has one corner, or eta is nonzero,
this outward direction strictly supports a physical circle
corner. Such a point cannot be shared by two contained squares:
each of their inward edge vectors w at that point satisfies
Z.w<=-1/2, so a short segment in direction -Z lies inside both.
For the remaining two-corner eta=0 case, the +F force is East
at an outer-face point T with x=a. Its actual neighbor contains
T+East, whose x coordinate a+1 exceeds R because
a=sqrt(R^2-1/4)>R-1. This contradicts containment. Thus an
opposite parallel pair is impossible, including all physical
two-corner masks and zero coefficients.

Only the common owned-side alternative remains:

    n_AE=n_DE=n_E.                                     (15)

Their applications on this same E side are distinct. If they
coincided, the strict A and D vertex sectors would both contain
the inward direction -n_E in their interiors, giving immediate
open-interior overlap. Both applications are relative interior
points of the real E side, so their tangent distance is strictly
less than one. No concurrency or equal-circle-weight conclusion
is needed for the remaining argument.

## 5. The occupied rim fixes the two end orientations

Rotate the complete packing so (15) points East. The real E
side is now x=d. Write its D and A contacts as

    Q_D=(d,h_D), Q_A=(d,h_A).                          (16)

The following orientation uses the actual occupied rim, not an
assumed drawing of the six centers. The complete occupied-rim
homotopy contracts each rim center to the midpoint of its two
original rim applications, inside its own square. Its limiting
contact polygon has winding only zero or one, and every point
of the open H retains winding one. At either present end the
two rim contacts are opposite strict vertices. Their open
diagonal is in the open end square and no other polygon strand
can enter that open square. Across this directed diagonal the
positive winding jumps from zero on its right to one on its
left.

The hub application is in the relative interior of an adjacent
end side and off that diagonal. No third unit contains it, as
proved in Section 1. A sufficiently small neighborhood of that
point therefore meets no other polygon strand. The actual open
H approaches it and has winding one. Consequently this hub
point is on the left side of the directed end diagonal in the
positive rim traversal. This remains valid at every other weak
junction, since the homotopy and winding were established for
the complete original contact polygon before taking this local
neighborhood.

At D the local chart (2) puts H on the left of its E-to-C
diagonal. Hence the positive traversal is

    E -> D -> C -> B -> A -> E.                       (17)

At A its H point must accordingly lie on the left of its
B-to-E diagonal. Its orientation is therefore the mirror of
the D orientation in the East frame. The full two end poses
are exactly

    u_D=(-p_D,-q_D), v_D=(-q_D,p_D),
    D=Q_D+[0,1]u_D+[0,1]v_D,
    P_D=Q_D+u_D+t_D*v_D,
    Q_C=Q_D+u_D+v_D,

    u_A=(-p_A,q_A), v_A=(-q_A,-p_A),
    A=Q_A+[0,1]u_A+[0,1]v_A,
    P_A=Q_A+u_A+t_A*v_A,
    Q_B=Q_A+u_A+v_A,                                 (18)

where, for each i=A,D,

    p_i>q_i>0, p_i^2+q_i^2=1, 0<t_i<q_i/p_i.          (19)

For clarity these magnitude restrictions follow from each
original unloaded equation, rather than from (17) alone. At D
write its strict C force X*u_D+Y*v_D. Its owned H force is
gamma*u_D and its E force is lambda*East. Then

    X,Y,gamma,lambda>0,
    X+gamma=lambda*p_D, Y=lambda*q_D,
    gamma*t_D+X-Y=0.

Thus with r_D=X/Y in (0,1),

    t_D=q_D*(1-r_D)/(p_D-r_D*q_D),
    1-t_D=(p_D-q_D)/(p_D-r_D*q_D).                    (20)

This proves p_D>q_D and t_D<q_D/p_D. At A the identical reflected
calculation proves (19)--(20) with its own r_A in (0,1). These
are the complete actual end stars. The orientation alternatives
are exactly the two choices of which adjacent side contains the
H port; their diagonal determinants are opposite, so (17)
selects precisely (18).

The contact-polygon edge in E runs from Q_A to Q_D. The whole
E is on its right and H is on its left. Equivalently applying
the same positive-winding argument in the open E side strip
gives h_D>h_A. One can also obtain the strict order directly
from (7): after the rotation taking (3)'s n_E to East, the
vector P_A-P_D=e_0 still has negative y component; formulas
(18)--(19) then give the same strict order. In either proof,

    0<h_D-h_A<1.                                     (21)

## 6. A uniform small tilt of the actual hub

Put

    X_i=p_i+t_i*q_i,
    g_i=q_i-t_i*p_i>0.

Then

    P_D=(d-X_D,h_D-g_D),
    P_A=(d-X_A,h_A+g_A),
    1/sqrt(2)<X_i<sqrt(2),
    X_i^2+g_i^2=1+t_i^2>1.                           (22)

The two H applications are adjacent vertices by Section 3.
Name the end with the rightmost H application D. If this
interchanges A and D, reflect the entire configuration across
a horizontal line and simultaneously interchange B and C.
The graph, both nonaxis hypotheses, full stars and the preceding
mirror chart are all preserved. Section 3 already proved that
P_A is below P_D before such an interchange; after the whole
reflection the same remains true. Translate P_D to zero. The
actual hub frame is now

    e=(-a,-b), f=(-b,a),
    P_A=e, P_HC=f, P_HB=e+f,
    a>=0, b>0, a^2+b^2=1,
    a=X_A-X_D,
    h_D-h_A=b+g_D+g_A<1.                              (23)

In particular a cannot be zero, since then b=1. Also (22)
gives a<1/sqrt(2). We prove the stronger uniform estimate

    0<a<3/7, b>9/10.                                 (24)

Suppose 3/7<=a<1/sqrt(2). By (22),

    0<X_D=X_A-a<sqrt(2)-a<1,
    g_D>sqrt(1-X_D^2)>sqrt(1-(sqrt(2)-a)^2).

The function

    F(a)=sqrt(1-a^2)+sqrt(1-(sqrt(2)-a)^2)

is concave on [3/7,1/sqrt(2)], as the sum of two concave
upper-semicircle functions. At the right endpoint F=sqrt(2)>1.
At the left endpoint its first term sqrt(40)/7 exceeds 9/10.
Since sqrt(2)<99/70, its second term exceeds
sqrt(1-(69/70)^2)>1/10. Thus F>1 throughout that interval.
But (23) would give 1>b+g_D>F(a)>1, a contradiction. This
proves a<3/7; then b>sqrt(40)/7>9/10.

## 7. The entire C has height greater than -1/8

Keep the rightmost D chart and abbreviate p=p_D,q=q_D,t=t_D,
r=r_D,L=1-t. Equations (18)--(20), relative to P_D=0, give

    Q_C=L*(-q,p),
    0<r<1, L=(p-q)/(p-r*q) in (0,1),
    n_C=(-u,v)=(-(p*r+q),p-q*r)/sqrt(1+r^2),
    j_C=(-v,-u),
    C=Q_C+[0,1]n_C+[-rho_C,1-rho_C]j_C,
    0<rho_C<1.                                       (25)

Let N be the actual H-to-C normal at f. The C-owned CD axis
and triangle CDH give N.n_C>=0. Also

    N.j_C<=0.                                        (26)

To prove (26), suppose N.j_C>0. If N.n_C>0, its minimum on
C is Q_C-rho_C*j_C. Relative to P_D this point has strictly
negative u_D coordinate: Q_C.u_D=0, while
(-j_C).u_D=-(p*v+q*u)<0. But every point of H has nonnegative
u_D coordinate, since u_D is its unchanged inward D-to-H
normal at P_D. This is impossible. If N.n_C=0, then N=j_C.
Its minimum C coordinate is Q_C.j_C-rho_C, whereas

    (P_D-Q_C).j_C=L*r/sqrt(1+r^2)>0.

This violates the H-to-C supporting inequality at P_D.
These exhaust the contradiction cases and prove (26).

There are exactly three support features compatible with (26):
the bottom C vertex, the CD side, or the other bottom C side,
including their endpoints. If both own components are strict,
f is the bottom vertex and min_C y=f_y=a>0. If N.n_C=0,
then N=-j_C=(v,u). Write

    f=Q_C+(1-rho_C)*j_C+xi*n_C, 0<=xi<=1.

Its strict H-f support gives -b*v+a*u>0, hence u>b and v<a.
Therefore min_C y=a-xi*v>=a-v>0.

The remaining case N.j_C=0 has N=n_C and

    f=Q_C+eta*j_C,
    -rho_C<=eta<=1-rho_C.

Write a=sin(phi), b=cos(phi), p=cos(theta),q=sin(theta),
with 0<phi<pi/2 and 0<theta<pi/4. The strict inward D-to-H
normal at its H vertex implies

    V=b*p-a*q=cos(phi+theta)>0,
    U=a*p+b*q=sin(phi+theta),
    theta<phi+theta<pi/2.

The exact two contact-coordinate equations now give

    L=U+r*V,
    eta=V*sqrt(1+r^2)>0.                              (27)

The positive function sin(alpha)+r*cos(alpha) is strictly
concave on [theta,pi/2]. Since L<1 and alpha=phi+theta
is strictly between the endpoints, (27) forces

    L>q+p*r.                                         (28)

Indeed strict concavity gives a value strictly above the
smaller endpoint; if q+p*r>=1 it would instead force L>1.

Substitute (25) into (28) and multiply by its positive
denominator. The resulting exact polynomial inequality is

    Delta(r)=p*(1-q)-q-(p^2-q^2)*r+p*q*r^2>0.

This polynomial is convex on [0,1], and

    Delta(1)=(p-q)*(1-p-q)<0.

The chord bound for a convex function therefore forces
Delta(0)>0, that is q<p/(1+p). Consequently p>7/8. Otherwise
q>=sqrt(15)/8>7/15>=p/(1+p), a contradiction. Equations
(25) and (28) also imply u<q+p*r<L. The whole C height is
thus bounded by

    min_C y=L*p-(1-rho_C)*u
           >L*p-u
           >-(1-p)*L
           >-(1-p)>-1/8.                             (29)

All strict and axis support features, their endpoints, the
entire CD side position and the actual HC mean have been
included. Combining the three cases proves

    min_(Z in C) Z_y>-1/8.                            (30)

## 8. The unchanged A3 and actual AB contact force southwest HB

In the final East frame, (18) gives the inward H-to-A owned
normal n=(c,-d_0), where c=p_A>d_0=q_A>0. Put
j=(d_0,c). Its actual H application is e, and write the full
pose again as

    A=e+[0,1]n+[-kappa,1-kappa]j,
    F_AH=-Gamma*n.

The original AE direction is East, so its j component is
positive. The assumed nonaxis AB therefore takes exactly
the negative sign case of (11):

    F_AB=-rho*n-sigma*j,
    F_AE=(Gamma+rho)*n+sigma*j,
    rho,sigma>0,
    sigma=(1-kappa)*Gamma+rho<Gamma+rho,
    R=P_AB=e-kappa*j.                                (31)

Every term and the unchanged torque were retained. The strict
H-e support of HA says

    n=delta*e-eta_0*f,
    delta=b*d_0-a*c>0,
    eta_0=b*c+a*d_0>0,
    delta^2+eta_0^2=1.

By (9), HB strictly exposes e+f and has its unchanged unit
direction x*e+y*f, with x,y>0 and x^2+y^2=1. Apply (1) to
A at e in direction f and to B at e+f in direction -f.
Their actual AB intersection gives

    delta+x>=1.                                      (32)

Since c>1/sqrt(2)>1/2,

    delta+a=b*d_0+a*(1-c)
            <=sqrt(d_0^2+(1-c)^2)
            =sqrt(2-2*c)<1.

Thus x>a and y<b. In the actual East coordinates this says

    (n_HB)_x=-a*x-b*y<0,
    (n_HB)_y=-b*x+a*y<0.                             (33)

The original HB direction is strictly southwest.

## 9. The full actual B support gives a positive reserve

The B-owned AB conclusion from Section 4 is unchanged. Its
inward unit normal from A, obtained from (31), is also strictly
southwest. Indeed its x component is negative and
rho*d_0-sigma*c<rho*(d_0-c)<0 by (31). Write

    n_AB=(-k,-h), k,h>0, k^2+h^2=1.                   (34)

This is an own axis of B, with R on its minimum-n_AB side.
Since n_HB.n_AB>0 by (33)--(34), every minimum-n_HB support
of B must have that same minimum n_AB coordinate. At the
actual HB application Z=e+f this gives the exact equality

    n_AB.(Z-R)=0.                                    (35)

But BC and (30) require max_B y>-1/8. The complete sharp
span (1) from its unchanged R under (34) is at most k in
the upward direction. Since R_y=-b-kappa*c, it follows that

    k>b-1/8+kappa*c>31/40,
    h<13/20,
    kappa*c<9/40,
    kappa*d_0<9/40.                                  (36)

For h, use k>31/40 and 1-(31/40)^2=639/1600<169/400.
For the two kappa bounds use k<=1, b>9/10 and d_0<c.

The actual vector Z-R=f+kappa*j has components

    Z-R=(-b+kappa*d_0, a+kappa*c).

All factors in the following comparison are positive, by
(24) and (36). They give

    n_AB.(Z-R)
      =k*(b-kappa*d_0)-h*(a+kappa*c)
      >(31/40)*(27/40)-(13/20)*(183/280)
      =1101/11200>0.                                 (37)

This contradicts (35). The complete common-E-side feature
is impossible, and Section 4 excluded all its other owned
E axes. The theorem is proved.

## 10. Exact scope, dependencies and review boundary

This excludes the entire original interface where both HA
and HD are owned by their unloaded endpoint units and both
AB and DC are nonaxis normals in those endpoints. It also
includes the graph-preserving reflection. It assumes no
boundary status for A or D and no artificial boundary neighbor
for E. Both physical circle corners and either zero individual
coefficient at E were explicitly covered in the only circle
argument. Every B3/C3 force, every other physical circle mask,
all extra units and all original means remain unchanged.

The other return features at either end, and a free opposite
hub-end normal, remain outside this theorem. No whole L124
fine flag, no coarse parent and no ledger count changes here.

| Direct source | SHA-256 | Exact use |
| --- | --- | --- |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 | Complete positive-length HA/HD exclusion with both true unloaded stars |
| GENERAL_UNLOADED_THREE_DISTINCT_SINGLETON_PORTS_HAVE_NO_FREE_NORMAL_SELECTION.md | 7700a4547542af9fc25b0e0b3d14f2113529069df0b007443c18d690da1137bb | Existing common selection at each original three-distinct-singleton end |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Entire actual owned-axis triangle implication |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Sharp unit-support span, fully restated in Section 1 |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 | Complete Sections 1--2 contact-polygon homotopy, winding zero/one and whole-H winding one at all weak junctions |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original strict point convention and compatible physical embedding |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full forces, torque, actual supports and all means |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal original graph, degrees, loads and occupied-H contract |

No numerical pose sample, mesh, computational exclusion, substitute
body, deleted force, reselected normal, changed mean, Lean edit,
build, CI, workflow, metadata mutation, commit or remote action
is part of this proof. These exact new bytes require separate
full independent review and root mathematical adoption.
