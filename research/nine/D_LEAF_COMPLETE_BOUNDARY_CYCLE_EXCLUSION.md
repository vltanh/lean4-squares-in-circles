# One D leaf excludes every complete cycle whose other bodies touch the circle

Date: October 26, 2026.

**Status: complete uniform hand proof; full root and separate independent
reviews accepted.** The new whole original caller is the four-load
C5 with a D leaf. No pentagonal-hole capacity estimate is needed.

## 1. Complete original scope

Keep the same original nine interior-disjoint unit squares, containing
circle, and common compatible physical certificate. Work in

    79/40 <= R <= sqrt(1105)/16.

Suppose an entire positive component is the actual simple cycle

    H--B_1--B_2--...--B_k--H

and one genuine D leaf L at H, where 2<=k<=7. Every B_i has positive
total circle load and retains its true positive degree two. H has
exactly its three actual positive edges, including HL. All physical
circle masks and individual zero corner weights, original forces,
normals, contact owners and shared-side means remain. The other 7-k
physical units remain arbitrary and present. There is no additional
positive chord or attached force in this component.

**Theorem.** This entire family has no nine-square completion.

The same-nine lower bound NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md
reduces to R>2, retaining all its declared arithmetic dependencies.
If k=7, the eight distinct boundary units B_i,L already contradict
the eight-arc argument of Section 2. Hence assume k<=6 below. The
possible seven-cycle exception of the physical boundary graph is
not discarded by the embedding argument.

Use the already established compatible fixed-point selection
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md. Its stated
theorem applies to any radial-leaf root with exactly two other
positive neighbors, both physically boundary, when its two actual
intersections are distinct singletons. It has no C4 or fixed cycle
length premise. This is the only owned-contact selection used below.
No normal is rotated after obtaining a certificate.

## 2. A geometric exit unless a horizontal H side is shallow

Orient the actual D leaf east. The unchanged full D chart is

    r=R-sqrt(2), s=1-r,
    H=[-s,r] times [-b,a],  a,b>0, a+b=1,
    p_HL=(r,0), n_HL=e_x.

The exact margins proved in
D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Section 2, give

    1/2<r<2/3, 1/3<s<r, r^2-s^2>1/16.                 (1)

Every point of every physical boundary unit has norm at least r.
The origin is in int(H). If a,b>1/4, a slightly larger concentric
disk than the closed D_(1/4) lies inside int(H). Every other actual
closed square avoids that disk: any point in int(H) would force
interior overlap. Thus all eight other original units have distance
strictly greater than 1/4.

For each such convex unit T, its nearest point z to O gives

    (z/|z|).x >= |z|>1/4 for every x in T.

GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1, assigns it an
open-interior radius-5/4 arc longer than pi/4. Eight such arcs
are disjoint, by the unchanged square interiors, and cannot fit
on one circle. This proves the theorem if a,b>1/4 and also gives
the k=7 exit above, since physical boundary units satisfy |x|>=r.

For the remaining family reflect the entire packing if necessary
and retain the complete shallow-side domain

    0<a<=1/4,       b=1-a>=3/4.                        (2)

We will exclude this family by the actual root and endpoint
equations, independently of all completion-square positions.

## 3. Actual endpoint moments locate one upper root contact

All B bodies are physical boundary units. Their positive path has
strict circular order and the actual outer-face order is
H,B_1,...,B_k,H. The real boundary leaf is in its exterior face.
No other physical unit can contain its H contact (r,0): H occupies
one tangent half-plane and the D leaf the opposite symmetric
quadrant, leaving only two pi/4 tangent gaps.

Cut the H boundary at (r,0) and label the actual B path in
counterclockwise occupied-arc order. Its two original H applications
are p_1,p_k, with outward normals n_1,n_k and positive magnitudes
mu_1,mu_k. Their normal lifts have

    0<=theta_1<=theta_k<=2pi.                           (3)

This is the geometric port-order argument of
GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md, Section 1; its use here
does not import that source's zero-total-hub-force equation. The
path endpoints retain true degree two, while all middle bodies and
their original loads remain. The physical corner/center order
agrees with the occupied H-arc order, including weak junctions.

The degree-free boundary-pair moment theorem in
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1, gives strictly
positive origin moment to each boundary-path edge directed in
this order. Each endpoint circle force has zero origin moment.
Its true two-edge torque therefore gives

    det(p_1,n_1)>0,       det(p_k,n_k)<0.                (4)

The full H equations are

    alpha e_x+mu_1 n_1+mu_k n_k=0,
    mu_1 det(p_1,n_1)+mu_k det(p_k,n_k)=0, alpha>0.     (5)

Every actual H force occurs in (5).

The two H normals cannot both be horizontal under (2). If the
first lift is 0, its application is (r,y) with y>0, so its moment
is -y<0, contradicting (4). If its lift is pi, its application
(-s,y) satisfies s^2+y^2>=r^2; by (1),(2), y<-1/4 and its moment
is y<0, again impossible. If its first lift is 2pi, both normals
are east and cannot balance the east leaf in (5). These exhaust
all horizontal cases, including opposite normal signs.

The vertical part of (5) consequently gives strict opposite signs.
The order (3) makes n_1 the upper one and n_k the lower one. Their
H applications are respectively on y=a and y=-b. The northwest H
vertex has norm squared s^2+a^2<r^2 by (1),(2), so cannot belong
to B_1. Thus the upper normal is either exactly north or strictly
northeast. In particular (n_1)_x>=0. The horizontal part of (5)
then makes n_k strictly southwest, at the fixed application
(-s,-b). It is a singleton contact.

The two nonparallel H force lines intersect on the horizontal
leaf line, by the full force and torque equations. Write that
intersection as (q,0). The first equation in (4) gives

    q=det(p_1,n_1)/(n_1)_y>0.                          (6)

Also q<=r: if p_1=(x,a), then
q=x-a(n_1)_x/(n_1)_y<=x<=r. No concurrence is asserted to lie
inside any radial two-corner square.

The loaded degree-two endpoint B_1 has the actual boundary neighbor
B_2, or B_k when k=2. The full proper-concurrence lemma
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, therefore gives

    Q_1=tau F_1=p_1+ell n_1, tau>0, ell>=0,             (7)

where F_1 is the actual nonzero circle resultant. When B_1 has one
physical circle corner z_1, absorb its positive weight into tau;
then Q_1=tau z_1 lies in B_1 and 0<tau<=1. Every physical two-corner
mask and individual zero weight remains until the explicit norm
exclusion below. No equation at an internal body is replaced.

## 4. A strict northeast upper contact cannot reach the circle

Suppose n_1=(cos(phi),sin(phi)), 0<phi<pi/2. Then
p_1=(r,a). Both original H intersections are distinct singletons,
so the fixed-point selection in Section 1 gives actual side-axis
owners. This northeast normal is not an H axis, hence is owned
by B_1 with p_1 in its relative side interior. Put

    n=n_1, k=(-sin(phi),cos(phi)), P=(r,a),
    B_1=P+[0,1]n+[-rho,1-rho]k, 0<rho<1.

By (1),(2),

    |P|^2<4/9+1/16=73/144<9/16.                       (8)

A physical two-circle-corner unit is radial S and every one of
its points has norm at least d=sqrt(R^2-1/4)-1>9/10. Thus B_1
has exactly one physical circle corner. Equation (7) makes its
n coordinate positive and its k coordinate P.k negative, since

    P.k=-det(P,n)<0

by (4). The actual far circle corner is consequently

    z_1=P+n-rho k.                                    (9)

The actual side P-t k meets the inner upper D-leaf edge y=x-r at

    t_0=a/(sin(phi)+cos(phi))<1/4.

At that meeting point, x-r=y=t_0 sin(phi) is in (0,1/sqrt(2)),
so it is in the relative interior of the leaf edge. If rho>t_0,
this side enters int(L) immediately afterwards, forcing interior
overlap. Thus rho<=t_0<1/4. Using (8),(9),

    R=|z_1| <= |P|+sqrt(1+rho^2)
             <3/4+sqrt(17)/4<15/8<2,

contrary to R>2. This is the local right-contact argument of
D_FOUR_CYCLE_NONPARALLEL_SINGLETON_EXCLUSION.md, Section 4, now
proved directly from the present shallow-side premise; its lower
tip height theorem and its middle-body equations are not used.

## 5. A north upper singleton also cannot reach the circle

Suppose n_1=e_y and the upper intersection is a singleton. Its
actual point is P=(q,a), with 0<q<=r by (6). Its boundary norm
and (1),(2) give

    q>=sqrt(r^2-a^2)>sqrt(6)/5>2/5,   |P|<3/4.         (10)

Here r>11/20 is already true throughout the original radius
window. Again B_1 has a unique physical circle corner, since a
radial S unit has no point of norm below 9/10. The singleton
north contact makes P the bottom vertex of a genuinely oblique
B_1. An aligned alternative would have a positive shared side
or a point-only vertex contact with a forbidden nonstrict axis
normal. Write its actual inward axes as

    u=(c,d), w=(-d,c), c,d>0, c^2+d^2=1,
    Delta=c-d, Sigma=c+d=sqrt(2-Delta^2).

Each adjacent vertex has norm at most |P|+1<7/4<R. The actual
circle corner must therefore be

    z_1=P+u+w=(q+Delta,a+Sigma).

The unique-mask version of (7) has x coordinate q and is a
multiple tau z_1 with 0<tau<=1. Thus q=tau(q+Delta), so Delta>=0.
Put g=r-q>=0. By (10), r+q>1 and

    g<=a^2/(r+q)<1/16.                                (11)

If Delta>=1/2, the actual B_1 side P+t u meets y=x-r at

    t_0=(a+g)/Delta<5/8<1.

Its height there is (ca+dg)/Delta, strictly between zero and
5/8<1/sqrt(2). Hence this is again an inner D-leaf edge point,
and the side enters the open leaf immediately afterwards. This
contradicts disjoint interiors, so

    0<=Delta<1/2.                                     (12)

For fixed q,a, the squared norm of z_1 has derivative

    2(q-a Delta/sqrt(2-Delta^2))>0

on [0,1/2], using q>2/5 and a<=1/4. Therefore (1),(2),(12) give

    R^2 < (2/3+1/2)^2+(1/4+sqrt(7)/2)^2
         =49/36+29/16+sqrt(7)/4
         <553/144<4,

where sqrt(7)<8/3. This contradicts R>2. All actual singleton
owner endpoints and physical circle masks were retained until
their stated exclusions. No lower-contact owner was needed.

## 6. The full shared north side is impossible as well

Finally suppose the upper intersection has positive length. Its
north normal is e_y and B_1 is aligned:

    B_1=[x,x+1] times [a,a+1].

The unchanged actual mean (q,a), with 0<q<=r, belongs to that
shared side. Consequently

    x>=q-1>-1,       x<=q<=r.

Actual disjointness from the D leaf forces x+1<=r+a. Otherwise
choose y=a+epsilon<1/sqrt(2) with x+1>r+y. Since x<=r, B_1's
interior at height y would meet the leaf interval (r+y,R-y).
This includes every tangency endpoint by the strict perturbation.

Every point of B_1 therefore satisfies

    -1<X<11/12,       0<Y<=5/4.

Every actual corner has squared norm below 1+25/16=41/16<4,
contradicting physical circle contact at R>2. The original mean
was not fixed to an endpoint or midpoint; the conclusion includes
all possible B_1 circle masks and individual weights. In particular
the other singleton H contact could be free: no owned-contact
inference was used in this shared branch.

Sections 4--6 exhaust the north/northeast alternatives of Section 3.
The reflected shallow bottom family is identical. Section 2 had
already excluded the remaining deep-side family in the actual nine
squares. This completes the theorem for the entire original scope.

## 7. Exact C5 gate and larger-domain limits

Take H=0 and (B_1,B_2,B_3,B_4)=(1,2,3,4) in the original C5.
The full block-load set 1234 makes each path body loaded with its
true degree two. The root has true degree three, its actual D
leaf has degree one, and the three arbitrary completion squares
remain. The theorem closes the whole original gate

    M6.B5L.C5.L1234.D.

It retains the complete original D-root transverse slider, every
radius endpoint after the accepted same-nine lower-bound join,
all physical corner masks and individual zero weights, every
owner and shared mean, and the full three-extra completion domain.
Its S alternative and the other C5 load sets are not claimed here.

The same proof applies to every longer complete simple cycle with
one genuine D leaf and all its other original cycle bodies loaded,
within the nine-body budget. It is also an alternative route for
the previously closed all-boundary D triangle and C4. No old
dependency or arithmetic certificate is declared retired.

The exact root degree three is essential to the nonparallel force
line and fixed-point arguments. Additional hub spokes, additional
positive leaf forces, unloaded endpoint bodies or other positive
attachments are not deleted to fit this theorem. No pentagonal
hole capacity, sampled pose, new scalar certificate, Lean
compilation, CI or shared-checklist mutation is used.
