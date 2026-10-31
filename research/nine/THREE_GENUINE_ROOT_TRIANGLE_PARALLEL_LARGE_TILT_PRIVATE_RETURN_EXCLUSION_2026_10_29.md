# Parallel three-genuine-root triangles: every large-tilt feature is excluded

Date: October 29, 2026. Author: root_triangles continuation.

**Status: complete proposed uniform hand theorem, saved for independent
review.** This closes the entire large-tilt part of the remaining
parallel-middle feature. The small-tilt part is kept explicit. No original
flag is changed by this source.

## 1. Full original scope

Retain all nine actual interior-disjoint unit squares, the same selected
physical certificate, every positive force, actual mean, physical circle
corner and individual zero coefficient, in

    79/40 <= R <= sqrt(1105)/16.

Let T,H,K be three genuine roots, with three distinct real degree-one
leaves and all three original positive root edges TH,TK,HK. T has true
degree three, consisting of H,K and its leaf. The two outer roots retain
their actual full degrees. At each outer root separately assume either:

1. Every external positive neighbor, other than T, the other root and
   its real leaf, is physically boundary, at arbitrary degree; or
2. There is exactly one such external positive neighbor, of true degree
   two. Its load and physical circle mask are initially arbitrary.

The same actual external unit may meet both roots. No common neighbor
is assumed, and no neighbor is duplicated into two physical units.

The accepted complete three-genuine-root entry eliminates D leaves and
the low/critical radius. The remaining parameters are

    d=sqrt(R^2-1/4)-1=1+epsilon,  0<epsilon<1/60.

Each root contains its actual point epsilon times its real leaf direction.
Thus each root is physically circle-clear and has its full unloaded
force/moment equation, at its original true degree.

Consider the full parallel alternative at T of the complete two-near-
neighbor theorem. Rotate T's real leaf East. Both T-to-outer normals are
West, and their unchanged means, after whole-data reflection if needed,
are

    P_H=(epsilon,t), P_K=(epsilon,-u),
    t,u>0, t+u<=1, mu_H*t=mu_K*u.                    (1)

An outer root either owns its East normal toward T or strictly exposes
its unique rightmost vertex there. The parallel/both-owned case was
already excluded at arbitrary outer degree. The remaining geometry has
one or two tilted outer roots.

The theorem below excludes every large branch in the complete charts:

* **One tilted root:** normalize the owned upper root and tilted lower
  root as in Section 2. The branch with s>999/1000 is impossible.
* **Two tilted roots:** use the chart of Section 3. The branch with
  c<1/4 or C<1/4 is impossible.

The complement has the small charts recorded in Section 7. The statement
does not reassign a degree-three equation to an outer root or substitute
an effective edge for an unloaded actual unit.

## 2. Complete one-tilted geometry and its large branch

Reflect and exchange all original upper/lower labels so the owned root
is upper. Its actual chart is

    H=[epsilon-1,epsilon] x [q,q+1],
    K=P_K+[0,1]f+[0,1]j,
    f=(-c,s), j=(-s,-c), c,s>0, c^2+s^2=1.            (2)

The physical triangle owned-axis theorem gives a nonnegative horizontal
component for H-to-K. A positive component would expose H on x=epsilon,
where K has only P_K. A right-side interior or either right-side endpoint
of H overlaps K's two strictly tilted leftward axes at that same point.
Hence H-to-K is vertical. North is impossible since P_K lies below its
actual H-to-T mean. Thus H-to-K is South and its actual contact is

    Q=P_K+f=(epsilon-c,q), q=s-u.                    (3)

This is in the relative interior of H's bottom side; every original
H-to-T mean remains unchanged. The genuine near points give
-epsilon<=q<=epsilon. Examining the four H sides and four vertices for
its real radial S application leaves only owned North or the strict
upper-right vertex. Hence

    q=epsilon  or  q=sqrt(1+2epsilon)-1,
    (59/60)*epsilon<q<=epsilon.                     (4)

No root force equation is used in this cover. For a near point of K
write its relative coordinates at Q as alpha*(-f)+beta*j, alpha,beta in
[0,1]. Its actual x and y bounds give

    c*(1-alpha)+s*beta<=2epsilon,
    s*alpha+c*beta<=q+epsilon<=2epsilon.

Consequently c*s<=2epsilon*(c+s). With m=min(c,s), M=max(c,s), first
m<4epsilon<1/15 and M>99/100, then

    m<2epsilon*(1+20/297)<9epsilon/4<3/80,
    M>999/1000.                                    (5)

The entire one-tilted feature therefore has exactly a small-s branch
and the present large-s branch s>999/1000, c<9epsilon/4.

We record the whole real K-leaf cover before restricting it. Put

    E=epsilon*c+u*s>0, V=-epsilon*s+u*c.

The rightmost vertex P_K and all near-axis supports have height below d.
The far +f height 1-E is below one. A radial leaf at P_K+f would give
u^2-2su=2epsilon(1+c)>0 and u*c<=epsilon*s; since u<1 these conditions
are incompatible. Thus the complete remaining cover is the strict
P_K+j vertex, owned +j side, or strict opposite vertex P_K+f+j.

In the large-s branch the P_K+j vertex has both coordinate magnitudes
greater than 999/1000-epsilon, so its norm exceeds d. The real K leaf
therefore is owned +j or the opposite vertex. Its actual direction is
within angle 1/9 of West. For the owned case this follows from c<3/80;
for the opposite vertex its radial point is

    Z=(epsilon-c-s,q-c),

whose x coordinate is negative and whose absolute y coordinate is
below max(q,c)<3/80. Divide by d>1 and use
sin(1/9)>=1/9-(1/9)^3/6>3/80.

For the later complete fourth-force identity we need the sign of the
unchanged H-to-K application. In both real-leaf cases

    c>epsilon.                                     (6)

For owned +j, u*c=epsilon(1+s) and u<1 give (6). For the opposite
vertex, c<=epsilon would make |Z_x|<=s<=1 and |Z_y|<=epsilon, hence
|Z|^2<=1+epsilon^2<d^2, a contradiction.

Now reflect the full packing vertically and relabel the South-leaf
root as K. In the fixed world axes w=East, v=North its actual square is

    K=[p-1,p]w+[k-1,k]v,
    p=epsilon, k=-q, -epsilon<=k<0.                 (7)

Its real leaf direction e satisfies e_w>=0,e_v<0. Its middle-root
force is mu*w at (p,-t), with mu,t>0 and 0<=t+k<=1. Its other-root
force is tau*v at the unchanged point

    (q_0,k)=(epsilon-c,k), q_0<0.                   (8)

The other root has the real West leaf just proved. All external forces
at the true K degree remain.

## 3. Complete two-tilted geometry and its large branch

Use the actual frames

    H=P_H+[0,1]f+[0,1]j,
    f=(-c,-s), j=(-s,c),
    K=P_K+[0,1]F+[0,1]J,
    F=(-C,S), J=(-S,-C),
    c,s,C,S>0, c^2+s^2=C^2+S^2=1.                    (9)

The complete physical root-triangle interface cover, independent of
every external force, is:

* Both strict facing corners coincide, giving c=C, s=S, t+u=2s.
* H owns HK: Q_K=P_H+eta*f, eta=C/c in (0,1], with
  C<=c, S>=s and t+u=S+eta*s.
* K owns HK: Q_H=P_K+eta'*F, eta'=c/C in (0,1], with
  c<=C, s>=S and t+u=s+eta'*S.

Here Q_H=P_H+f and Q_K=P_K+F. To see completeness, an owned H
normal toward K can only be -j: -f points upward toward a side whose
support excludes P_K. The strict P_H vertex cannot contain K's distinct
rightmost P_K; the upper adjacent vertex excludes P_K by its upward
support; and the opposite vertex separates the actual touching T,K.
Thus the only strict H port is Q_H. Reflect for K. Both cannot own the
same interface since their outward owned candidates both have positive
horizontal components. These alternatives retain the whole original
owned mean and both endpoints.

The strict other-end vertex cone in either owned case gives

    Sigma=atan(s/c)+atan(S/C)<pi/2.                   (10)

Both-strict also gives (10), using t+u<=1. The actual near points give

    t<=epsilon+2epsilon*s/c,
    u<=epsilon+2epsilon*S/C.                         (11)

Suppose c<1/4, after whole-data reflection and exchange if necessary.
Both strict would give c=C and t+u=2s>1. H-owned would give C<=c and
Sigma>pi/2. Thus K owns the interface, and

    Q_H=P_K+(c/C)*F,
    t+u=s+(c/C)*S,
    S<c, C>s>24/25.                                 (12)

From (11), u<(8/5)epsilon<2/75, hence t>14/15.

The real H-leaf cover is precisely the upper adjacent strict vertex
P_H+j, owned +j side, or opposite strict vertex P_H+f+j, by the same
eight-feature check as Section 2 with the vertical sign reflected.
The upper adjacent vertex now has x magnitude >283/300 and y>14/15,
so has norm greater than d. Hence only owned +j or opposite remains.

For opposite, its radial norm d gives c+s<=1+2epsilon. With c<1/4
and s>1-c^2 this implies c<8epsilon/3. For owned +j the exact identity
t*c=epsilon(1+s), t>14/15 gives c<15epsilon/7. Therefore throughout
this whole branch

    0<S<c<8epsilon/3<2/45,
    s,C>999/1000, u<11epsilon/10.                    (13)

The last bound follows by substituting the improved S/C in (11).

Use the actual lower-root own frame

    w=-F=(C,-S), v=-J=(S,C),
    p=P_K.w=epsilon*C+u*S,
    k=P_K.v=epsilon*S-u*C.

Then

    K=[p-1,p]w+[k-1,k]v,
    0<p<21epsilon/20<7/400,
    -11epsilon/10<k<epsilon*S.                       (14)

Its real leaf must be South: the near vertex and near-axis supports
are too central, West ownership requires p=-epsilon, and the upper-left
vertex has squared norm <1+(11epsilon/10)^2<d^2. The lower-left
vertex has both coordinate magnitudes >9/10 and norm >d. Thus only
owned South or the strict lower-right radial vertex remains. The actual
radial equation sharpens (14) to

    -epsilon<=k<0, e_w>=0, e_v<0.                    (15)

The original K-to-T force is mu*(C,S), mu>0, at (p,k). The original
K-to-H force is tau*v, tau>0, at

    (q_0,k), q_0=p-c/C.                             (16)

We prove q_0<0 without replacing this original application. Write

    L=sin(Sigma), Z=cos(Sigma), 0<Z<c,
    j=(-L,Z) in the K frame.

For H's owned +j leaf, Q_H.j=epsilon, so
-q_0*L+k*Z=epsilon>0; (15) gives q_0<0. For H's opposite radial
leaf its actual point is (q_0-L,k+Z). If q_0>=0, then q_0<p<7/400,
L>s*C>(999/1000)^2, so |q_0-L|<=1. Also |k+Z|<8epsilon/3. Its
squared norm would consequently be <1+(64/9)epsilon^2<d^2. Again

    q_0<0.                                         (17)

The real H leaf is within angle 1/9 of West in the actual K frame.
For owned +j, its v component is Z<c<2/45. For opposite its actual
radial point has v component k+Z in (-epsilon,c), so after division
by d its absolute v component is <2/45. Its w component is negative
in both cases, and sin(1/9)>2/45.

## 4. A degree-free actual West-leaf return cap

Both large branches now have a real West leaf with actual center ell
and a South root (7) or (14), satisfying

    0<p<7/400, -epsilon<=k<0,
    -91/60<ell_w<-161/108<-7/5,
    |ell_v|<91/540<1/5.                              (18)

The center statements follow from the real leaf radius d+1/2 in
(3/2,91/60), angular deviation <1/9 and cos(1/9)>161/162.

Every actual contained unit center has norm <91/60, since its farthest
own corner has squared norm at least r^2+r+1/2. Every physically
boundary unit center has squared norm >11/6: its center norm is at
least R-1/sqrt(2), and

    (sqrt(17)/2-1/sqrt(2))^2=19/4-sqrt(17/2)>11/6.

These are actual physical statements and keep every circle mask.

The middle-root force at K has positive w component. Its other-root
force is +v, and its real South leaf has nonnegative w component.
Thus the entire horizontal K equation at its true degree requires
at least one original external force with strictly negative w component.

A strict Southwest such force is impossible for any actual neighbor.
It exposes K's lower-left vertex (p-1,k-1), both negative coordinate
magnitudes >9/10. For the actual inward unit normal n=(-c_0,-s_0),
c_0,s_0>0, that neighbor contains the actual point (p-1,k-1)+n.
Its squared norm is >221/50>1105/256. This follows also at a side:
the full unit normal segment from any actual minimum-support point
belongs to the same square. No neighbor equation is needed.

For a West external normal, its actual neighbor E lies in w<=p-1,
so its center satisfies c_E.w<=p-3/2<-37/25. The center bound gives
|c_E.v|<1/3, using

    1/9-[(91/60)^2-(37/25)^2]=37/30000>0.

Both west coordinates of c_E and ell lie in (-91/60,-7/5), so their
squared distance is <(7/60)^2+(8/15)^2<1. Distinct unit incircles
cannot overlap. This excludes West regardless of E's load or mask.

Finally let the external normal be strict Northwest and E physically
boundary. Its actual K point is

    P=(p-1,k)=(-X,Y), 49/50<X<1, |Y|<1/50.

Put z=c_E-P. The actual unit gives |z|<=1/sqrt(2)<71/100. Its physical
boundary-center lower bound and |P|^2<1+1/2500 give

    P.z>1/6-1/5000,
    -X*z_w>1/6-9/625>3/20,
    z_w<-3/20.

For a=ell-P, (18) gives -27/50<a_w<-53/108 and |a_v|<19/100.
Consequently

    |c_E-ell|^2
      <1/2+(27/50)^2+(19/100)^2
        -2*((3/20)*(53/108)-(71/100)*(19/100))
      =3421/3600<1.                                (19)

This is an actual incircle contradiction. E is distinct from the real
West leaf, which has genuine positive degree one at the other root.
This proves the entire boundary-Northwest cap with every frame and mask.

If every external K neighbor is physically boundary, the preceding
complete normal cover contradicts its required negative horizontal
force immediately, at arbitrary true degree. In particular multiple
external forces in a true5 star have all been retained.

## 5. One true2 external neighbor: both complete fourth-force identities

It remains that K has exactly one external E and E has true positive
degree two. K therefore has its full true degree four. Southwest and
West are already excluded, so write its original K-to-E force

    F*(-c_0,s_0), F,c_0,s_0>0, c_0^2+s_0^2=1,

at the unchanged upper-left point (p-1,k). Put

    eta=e_w/(-e_v)>=0.

### 5.1. The one-tilted geometry

Keep (7),(8) and the original middle point (p,-t). The complete K4
force and origin-moment equations are

    mu+alpha*e_w=F*c_0,
    tau+alpha*e_v+F*s_0=0,
    mu*t+tau*q_0+F*((p-1)*s_0+k*c_0)=0.

The actual radial leaf has zero origin moment, and all other moments
are taken at the same original applications. Eliminate alpha to get

    F*(c_0*(t+k)-s_0*(1-p+eta*t))
       =tau*(eta*t-q_0)>0.                          (20)

Here t>0, q_0<0 and 0<=t+k<=1. Thus
c_0>(1-p)s_0>(59/60)s_0 and c_0>2/3. The unchanged support obeys

    h_K(-c_0,s_0)=(1-p)*c_0+k*s_0
       >(59/60)*(2/3)-1/60=23/36>3/5.              (21)

### 5.2. The two-tilted geometry

Keep (14)--(17). The middle force mu*(C,S) applies at (p,k), the
other-root force tau*v at (q_0,k), and the same external force at
(p-1,k). Write A=alpha*(-e_v)>0 for the real South-leaf vertical
magnitude. The complete four-force equations are

    mu*C+A*eta=F*c_0,
    mu*S+tau-A+F*s_0=0,
    mu*(p*S-k*C)+tau*q_0+F*((p-1)*s_0+k*c_0)=0.

Substitute A=mu*S+tau+F*s_0, preserving all four terms. The exact
origin-moment identity becomes

    mu*S*(p+k*eta)+tau*(q_0+k*eta)
       +F*s_0*(p-1+k*eta)=0.                       (22)

The actual real leaf gives p+k*eta>0. For owned South eta=0, so this
is p>0. For the strict lower-right radial leaf eta=p/(1-k), so it
equals eta>0. Since k<0 and q_0<0, (22) implies

    F*s_0*(1-p-k*eta)<mu*S*(p+k*eta).

The full horizontal equation gives mu*(C+eta*S)<=F*c_0. Equality is
retained for the owned-South endpoint eta=0; the preceding moment
inequality remains strict because tau*(-q_0-k*eta)>0. Therefore

    s_0/c_0
       < S*(p+k*eta)/((C+eta*S)*(1-p-k*eta))
       <=S*p/(C*(1-p))
       <14000/(45*999*393)<1/1000.                 (23)

In particular c_0>2/3, and the actual support satisfies

    h_K(-c_0,s_0)>(393/400)*(2/3)-1/60
                =383/600>3/5.                     (24)

The small original HK mean q_0 has not been replaced by K's upper-right
or upper-left vertex. Its strict negative sign is essential in (20)
and (22), and was established from the real opposing leaf.

### 5.3. The actual external E must be loaded

If E were unloaded, its full true2 force balance would send its other
positive force in the same direction n=(-c_0,s_0), with the same
magnitude. Its actual width in direction n is at least one. Hence the
actual far neighbor of E would have minimum n-support at least

    h_K(n)+1>8/5>61/60>d.

Every actual contained unit has minimum support at most d in every
unit direction: its center norm is at most d+1/2 and its halfwidth
at least 1/2. The displayed inequality is impossible. E is therefore
positively circle-loaded and physically boundary. Section 4's complete
Northwest cap now gives the final contradiction.

This uses E's original true degree two only. No equation or load is
imposed on its far neighbor, and no original edge is contracted.

## 6. Literal original transfers

For the original house ADT, retain exactly AT,DT,AD,AB,BC,CD and the
three real leaf edges at A,D,T. Its true degrees are A4,D4,T3,B2,C2.
Middle T and outer A,D satisfy alternative 2 independently: their
external neighbors are respectively the actual B and C. They are
distinct, connected to each other, and were never replaced by a common
unit. All load sets enter before the deductions in Section 5. Thus
every large-tilt parallel-middle feature of this whole original house
assignment is excluded.

For the original fan H12, retain hub H, path 1--2--3--4, all four H
spokes, and real leaves at H,1,2. Its true degrees are
H5,1_3,2_4,3_3,4_2. The accepted unloaded diamond-hub theorem makes
the actual private3 loaded at its true degree three, because its H
neighbor touches both 2 and 4. The actual true2 triangle tip4 is also
loaded. Thus all external neighbors of roots H and 2 are physically
boundary: H has the actual 3 and 4, and 2 has the same actual 3.
Use middle1. Section 4 applies at whichever outer root is the South
root, with all of its actual private forces present. The entire large
parallel feature is excluded even when that root is true5. Reflection
of the path gives the literal fan H34 assignment with the same scope.

The complete nonparallel theorem and parallel/both-owned companion
remain separate accepted inputs. This source plus those inputs leaves
only the parallel small-tilt features; no whole original row is yet
declared closed.

## 7. Exact residual small charts for a physical capacity join

For one tilted root, the complement of Section 2 has

    c>999/1000, 0<s<9epsilon/4,
    q=sqrt(1+2epsilon)-1 or epsilon,
    19epsilon/20<u<11epsilon/10,
    H=[epsilon-1,epsilon] x [q,q+1],
    K=(epsilon,-u)+[0,1](-c,s)+[0,1](-s,-c).

Here u=s-q first gives 0<u<19epsilon/15. The complete small-tilt
chart has E=epsilon*c+u*s<21epsilon/20<1/50 and
V=-epsilon*s+u*c>-epsilon*s. Thus the opposite vertex has both
far own coordinate magnitudes greater than 9/10, so its norm exceeds
d. The complete small-tilt leaf cover at K consists only of its strict P_K+j vertex or owned
+j side. Their respective exact radial identities are

    u^2+2cu=2epsilon(1+s),
    u*c=epsilon(1+s).

The upper bound follows from c>999/1000 and s<3/80, since
(1+3/80)/(999/1000)=2075/1998<11/10. If the quadratic identity had
u<=19epsilon/20, its left side divided by epsilon would be at most
19/10+(361/400)epsilon<2, contrary to the right side >=2. In the
owned case u>=epsilon gives the lower bound directly. Thus both
complete radial types, including their axis endpoint, give the stated
19epsilon/20<u<11epsilon/10.

For two tilted roots, if c,C>=1/4, the full root-interface cover gives
max(s,S)<=t+u. Apply (11) first with c,C>=1/4 and then with its
improved cosines. This yields

    0<s,S<9epsilon/4<3/80,
    c,C>999/1000,
    19epsilon/20<t,u<11epsilon/10.

For clarity, the upper height bounds follow already from (11) and
s,S<9epsilon/4, c,C>999/1000. At each tilted root the two own
coordinates of its near vertex are (-E,V), with
E=epsilon*c+t*s<21epsilon/20<1/50 and V>-epsilon*s (and the
reflected formulas at K). Again both opposite-vertex own magnitudes
are greater than 9/10, so that leaf feature is excluded physically.
Each root has only its outward adjacent radial vertex or owned
transverse leaf. The same two exact radial identities and lower-bound
argument just given, with t or u as appropriate, prove the strict
19epsilon/20 lower bounds independently at both roots.

Each real outer leaf in these small charts is its owned far transverse
side or the strict outward adjacent vertex. Its direction differs
from North or South respectively by less than arcsin(3/80). Each
outer root has its actual near vertex of norm <3epsilon/2<1/40.
The original T remains [epsilon,d] x [-b,a], a+b=1, t<=a, u<=b;
its slider has not been centered or assumed balanced.

These residual facts are purely geometric and retain arbitrary outer
degrees and full original means. A capacity proof may use them directly,
but if it needs a,b>=1/4 that condition must be established or its
complement treated separately. This source supplies no such balance.

## 8. Inputs and audit boundary

The following complete sources were read. The local geometric scopes
of the two diamond antecedents were reproduced in Sections 2--3 above;
their common-private-unit premises, D2 loading step, and final shared-D
contradictions are not imported. Sections 4--5 are the new general
private-return argument.

* PHYSICAL_CONTACT_STRESS.md: original full force/moment equations.
* THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md: full original low,
  critical and D-leaf cover, with actual high-S near points.
* GENUINE_S_THREE_FORCE_ROOT_TWO_NEAR_NEIGHBORS_FRESH_DOMAIN.md:
  original true-T3 parallel feature and strict mean signs.
* UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md: physical owned-axis
  implication only, without deleting an exterior force.
* THREE_LEAF_DIAMOND_PARALLEL_ONE_TILTED_HUB_FRESH_EXCLUSION.md:
  complete physical one-tilted chart and real-leaf cover.
* THREE_LEAF_DIAMOND_PARALLEL_TWO_TILTED_HUBS_FRESH_EXCLUSION.md:
  complete physical two-tilted chart, root mean alternatives and bounds.
* THREE_GENUINE_ROOT_TRIANGLE_NONPARALLEL_MIDDLE_PRIVATE_RETURN_EXCLUSION_2026_10_29.md:
  accepted distinct-private original graph transfers; separate
  nonparallel and parallel/both-owned exclusions.

This manuscript does not add a normal selector or establish the prior
global common-domain compatibility. It keeps that original assumption
at its existing scope. No pose search, numerical angle mesh, packing
certificate, Lean/Lake compilation, CI, remote mutation or original
inventory edit is used.
