# A physical-two-corner loaded triangle tip has no transverse-side port between two unloaded hubs

Date: October 29, 2026 UTC. Author: roof_review.

**Status: complete proposed uniform local exclusion and exhaustive
necessary-domain theorem, frozen for full independent review.** Every
original transverse-side port is excluded at once by an actual support
contradiction. The remaining nonparallel physical-two mask has precisely
two inner-face force features, with its full circle-weight endpoints
retained. Neither remaining feature is claimed impossible here.

This is not the terminal-axis two-circle theorem for D02.L01345.
Its two unloaded triangle hubs and full original stars are different.
No original fine/coarse flag or existing source is changed.

## 1. Actual local scope and all original forces

Retain the same actual interior-disjoint closed unit squares, unchanged
circle origin O=0 and original compatible selected physical certificate.
For the uniform local theorem assume

    R>sqrt(2), d=sqrt(R^2-1/4)-1<3/2.

In particular d>0. The entire original interval
79/40<=R<=sqrt(1105)/16 satisfies these bounds and d<61/60.
There is no restriction to a high-radius subinterval in this theorem.

Let A,V,D be distinct actual squares with all three original positive
triangle edges AV,DV,AD. V is positively circle-loaded of true positive
pair degree two, with exactly A,D as its positive neighbors. A and D
are unloaded of true positive pair degree three, with exact neighbor
sets

    A: {V,D,B}, D: {V,A,C}.

The actual exterior units B,C are distinct from the triangle and each
other. They have arbitrary true degree, load, physical circle mask and
other forces. All further actual units remain contained and present.
Zero total load at a hub does not mean its physical mask is removed.

Assume V has TWO PHYSICAL circle corners and its two original pair
normals are nonparallel. Each physical circle corner is retained even
when its individual coefficient is zero. Write the original outward
V normals as n_A,n_D, their positive magnitudes as mu,nu, and their
unchanged applications as P_A,P_D. Write g for the original A-to-D
unit normal, gamma>0 for its magnitude and W for its actual application.
At a positive-length physical contact every displayed application is
its full original aggregate mean, including either allowed endpoint.

The complete original equations at V are

    F_V+mu*n_A+nu*n_D=0,
    mu*det(P_A,n_A)+nu*det(P_D,n_D)=0.

Let F_AB and F_DC be the actual positive vectors directed from the
hubs to their real exterior neighbors. The full unloaded equations are

    F_AB=mu*n_A-gamma*g,
    F_DC=nu*n_D+gamma*g,
    -mu*det(P_A,n_A)+gamma*det(W,g)+det(P_B,F_AB)=0,
    -nu*det(P_D,n_D)-gamma*det(W,g)+det(P_C,F_DC)=0.

P_B,P_C are their unchanged actual applications or means. No exterior
force, original hub moment or positive AD term is deleted. The proof
below needs only one of the full hub force equations in each transverse
case; the other full star remains. In fact that local exclusion permits
arbitrary degree and load at the opposite hub, as stated in Section 5.

**Theorem.** In the actual radial-S frame of V, every original pair
application lies on its inner side. Up to reflection and relabeling
the two actual hubs together with their exterior neighbors, the entire
remaining nonparallel force domain is exactly the following necessary
union:

1. One original West normal at an actual inner-side mean of strictly
   negative height, and one strict Northwest normal at the upper inner
   corner.
2. A strict Northwest normal at the upper inner corner and a strict
   Southwest normal at the lower inner corner.

Sections 7--8 give the complete V2 equations for both rows, including
either individually zero physical circle coefficient. No assumption is
made that their normal-line concurrence belongs to V.

## 2. Full physical mask and contained-unit support facts

For completeness, the physical mask itself gives the actual frame.
Choose a farthest physical corner and its inward own axes so the unit
has own coordinates [a-1,a] x [b-1,b], with that corner (a,b).
Comparing each adjacent corner with it gives a,b>=1/2. An adjacent
corner is on the same circle exactly when the corresponding own
coordinate is 1/2. An opposite equal-radius corner would force
a+b=1, hence a=b=1/2 and R=1/sqrt(2), which is excluded here.
The two physical corners are therefore adjacent, and after a rigid
circle-centered orthonormal coordinate choice the same actual V is

    a=sqrt(R^2-1/4)=d+1,
    V=[d,a] x [-1/2,1/2],
    Z_+=(a,1/2), Z_-=(a,-1/2).

With its unchanged original coefficients lambda_+,lambda_->=0 and
lambda_++lambda_->0, its full circle force is

    F_V=k*(a,eta), k=2*(lambda_++lambda_-)>0,
    eta=(lambda_+-lambda_-)/(2*(lambda_++lambda_-)),
    -1/2<=eta<=1/2.

The endpoint eta=-1/2 is lambda_+=0; eta=1/2 is lambda_-=0.
Neither endpoint changes the physical-two mask into a unique mask.
Each individual circle atom has zero origin moment, giving exactly
the full V2 torque in Section 1.

No physical circle point belongs to two actual squares. At a contained
corner Z and either inward unit edge u, containment of Z+u gives
Z.u<=-1/2. Thus -Z has strictly positive components along both inward
edges, and Z-t*Z is inside that square for sufficiently small t>0.
Two squares containing Z would have intersecting open interiors.

For any actual contained unit K with center c and orthonormal own
axes u,v, a farthest corner has squared norm

    |c|^2+1/2+|c.u|+|c.v|>=|c|^2+|c|+1/2.

The right side increases for |c|>=0 and equals R^2 at |c|=d+1/2.
Therefore |c|<=d+1/2. If K lies beyond an actual unit-normal support
n.z>=h, its directional halfwidth is at least 1/2, so

    h+1/2<=c.n<=|c|<=d+1/2, hence h<=d.          (1)

This applies to every original support owner and every actual mean,
with no degree or boundary premise at K.

We also use the actual inward-unit-segment fact. If Q minimizes a
unit direction n on a unit square K, then

    Q+[0,1]*n is contained in K.                  (2)

At a vertex the two inward own components of n are nonnegative and
at most one. At a relative side-interior point n is the inward own
axis, so the entire segment reaches the opposite actual side. A side
endpoint is included in the vertex case. This is point membership
in the unchanged physical unit, not a changed application.

## 3. Pure physical triangle tools, with full original means

Two facts about three actual pairwise-touching unit squares are used
at their purely geometric scopes.

First, two parallel outward normals at one triangle vertex cannot
have opposite signs. Their two neighboring units would lie beyond
opposite supports separated by the positive width of that square,
so they could not physically touch.

Second, if two original outward normal lines at a triangle vertex
are nonparallel and meet at q, their actual applications have the
form

    P=q+alpha*n, Q=q+beta*m, alpha,beta>=0.        (3)

Here the lines run through the original applications in their
original normal directions. They are force lines, not the supporting
lines perpendicular to those normals. The complete pure physical
proof of (3) is Section 2 of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md.
It includes both own axes with arbitrary means, one own axis with a
strict vertex, identical vertices and adjacent strict vertices;
opposite strict vertices are excluded by actual unit reach. It has
no external-radial-moment, circle-load or root-degree premise.

We also use the complete physical side-normal obstruction: if one
of the two normals is an own side axis of the triangle vertex, its
dot product with the other is nonnegative. Its full support-span
proof is UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. No degree-two
equation at a hub is part of this physical input.

## 4. The complete V support cover before the transverse exclusion

An original pair application cannot be either outer corner Z_+,Z_-
by Section 2. This excludes every strict right-vertex normal.
An East-normal contact is impossible too: its actual neighbor would
lie beyond support a=d+1>d, contradicting (1).

The complete remaining outward support features of V are therefore

    West, North, South,
    strict Northwest at (d,1/2),
    strict Southwest at (d,-1/2).

The actual North or South mean has d<=x<a; the outer endpoint is
an unshareable physical circle point. The West mean remains in its
whole closed interval -1/2<=y<=1/2. No shared segment is classified
as a singleton because its mean happens to be an endpoint.

Suppose one original V normal is North. The side-normal triangle
obstruction excludes every other normal with negative vertical
component, including South and strict Southwest. Another North
or strict Northwest normal has positive origin moment, just as
the North application does: x>=d>0 for the North moment, and
d*s+c/2>0 for a strict Northwest normal (-c,s). Two such positive
moments cannot satisfy full V2 torque. East and the right vertices
were already excluded. Thus the other normal must be West.

The North application is Q=(x,1/2), with positive magnitude nu.
Write the West application P=(d,-t) and its magnitude mu. Full
V2 torque and force give

    0<t<=1/2, d<=x<a,
    mu*t=nu*x,
    mu=k*a, nu=-k*eta, eta<0.                    (4)

The strict t>0 follows from the positive North moment; its lower
endpoint cannot be retained as a possible balanced star. The closed
endpoint t=1/2 remains. Both original circle coefficients remain
in (4), including lambda_+=0. Reflection covers South, with its
other actual application strictly above height zero.

Thus every possible original transverse-side port reduces to one
complete West/North feature or its reflection, with the unchanged
means in (4). No normal was reselected to obtain this cover.

## 5. Every West/North feature contradicts an actual exterior support

For this entire feature name the actual West neighbor A and North
neighbor D. The original outward A-to-V direction is East and
the original D-to-V direction is South. Keep the unchanged positive
AD normal g from A to D, its magnitude gamma and its actual mean W.

We first prove

    g_x>=0, g_y>=0.                              (5)

If the two triangle normals at A are parallel, the first physical
fact in Section 3 excludes opposite signs, so g=East. If the two
triangle normals at D are parallel, their directions South and -g
must have the same sign, so g=North. These exhaust every case in
which one of the two hub concurrences is undefined. Both are
included in (5), with every original AD mean retained.

Otherwise both hub triangle pairs are nonparallel. Their pure
physical properness (3) gives their actual concurrences

    q_A=P-alpha*East=(d-alpha,-t), alpha>=0,
    q_D=Q+beta*North=(x,1/2+beta), beta>=0.

At their common AD application W, properness gives

    W=q_A+s*g=q_D-u*g, s,u>=0,
    q_D-q_A=(s+u)*g.

The left side has horizontal coordinate x-d+alpha>=0 and vertical
coordinate 1/2+t+beta>0. Hence s+u>0 and (5) follows, with g_y>0
in this nonparallel-hub subcase. Zero proper lengths are permitted
individually. The same original AD application appears in both
expressions, including an endpoint of a positive shared contact.

Now use the complete unloaded true-D3 force equation. Its forces
toward V and A are -nu*North and -gamma*g. Its actual third force
toward its real C is therefore

    F_DC=nu*North+gamma*g.

Its normalized original direction n satisfies n_x>=0 and n_y>0
by nu,gamma>0 and (5). There is no shortened degree or omitted
external term here: C is precisely the true third neighbor of D.

Since Q is D's actual minimum-North point, (2) gives the actual
point Q+North=(x,3/2) in D. The original D/C support height obeys

    h_D(n)>=n.(Q+North)
           =x*n_x+(3/2)*n_y
           >=d*n_x+(3/2)*n_y
           =d*(n_x+n_y)+(3/2-d)*n_y>d.           (6)

The last inequality uses n_x,n_y>=0, |n|=1, hence n_x+n_y>=1,
and the strict n_y>0, d<3/2. It includes n=North and the full
parallel-AD endpoints. But actual C lies beyond this original
support, so (1) requires h_D(n)<=d. This is a contradiction.

Only D's actual full three-force equation was needed in this
support contradiction. The opposite hub A may in fact have
arbitrary true degree, load and additional forces; its two triangle
ports and physical geometry still supply the same q_A or parallel
alternative. No equation or boundary condition at actual C was
used beyond its containment and original D contact.

Consequently every transverse V port fails when its actual
transverse-side neighbor is unloaded true3. In the main theorem
both actual hubs have that property, so either possible assignment
and the South reflection are excluded.

## 6. Exhaustive surviving original features

There is now no original East, North or South normal at V, and
neither outer circle corner can be a contact. Its only remaining
normal features are West and the two strict inner corners.

Both West normals are parallel, outside the present nonparallel
feature. Two strict normals at the upper inner corner both have
positive origin moment; two at the lower inner corner both have
negative origin moment. Either coincident-corner alternative fails
the full V2 torque. Thus the actual applications are necessarily
distinct.

If one normal is West, the other is strict at one inner corner.
Reflect so it is the upper one. Its moment is positive, so the
West mean has strictly negative height. This is row 1 of the
theorem. If neither is West, the two strict normals must be at
the two different inner corners. This is row 2.

This is the entire support-feature cover. A strict corner contact
may be owned by its actual hub or may be a genuine free contact.
No assertion about that other owner, any AD type, or an exterior
mean is made. Both original hub stars remain exactly those in
Section 1. The following formulas record the full V2 domain rather
than applying a unique-physical-corner selector to it.

## 7. Row 1: a West mean and the upper inner corner

Use the unchanged actual data

    P_A=(d,-t), n_A=West, mu>0, 0<t<=1/2,
    P_D=(d,1/2), n_D=(-c,s), nu>0,
    c,s>0, c^2+s^2=1, p=s/c>0.

The full V2 force and torque equations are exactly

    mu+nu*c=k*a, -nu*s=k*eta,
    mu*t=nu*(d*s+c/2).                           (7)

Equivalently,

    mu/nu=c*(d*p+1/2)/t,
    eta=-a*t*p/(d*p+1/2+t)<0.                   (8)

The physical circle-weight interval is exactly the additional
necessary inequality

    [2*a*t-d]*p<=1/2+t.                         (9)

Indeed (9) is equivalent to eta>=-1/2 after multiplication by
the positive denominator in (8). Its equality is the retained
lambda_+=0 endpoint. The other zero-coefficient endpoint is
represented by the reflected row. No inequality is divided by
2*a*t-d, whose sign can change across the original mean interval.

The actual nonparallel normal lines have concurrence

    q_V=(d+(1/2+t)/p,-t).                        (10)

Its horizontal coordinate is strictly greater than d and its
height is the original West mean. Equations (8)--(10) give
q_V,y/q_V,x=eta/a, so it lies on the full original circle-resultant
line through O with positive scalar coefficient. This is a direct
identity for this physical-two feature. It does not imply q_V is
in V: its horizontal coordinate may exceed a, and no upper bound
q_V,x<=a has been proved or used.

Both the full mean endpoint t=1/2 and the physical coefficient
endpoint eta=-1/2 remain in the domain. Any simultaneous endpoint
would have to satisfy the same exact equations and all the actual
hub and exterior equations; this theorem does not assert its
physical realizability.

## 8. Row 2: the two different strict inner corners

Write the unchanged data as

    P_A=(d,1/2), n_A=(-c,s), mu>0,
    P_D=(d,-1/2), n_D=(-C,-S), nu>0,
    c,s,C,S>0, c^2+s^2=C^2+S^2=1,
    p=s/c>0, q=S/C>0.

All components here belong to the actual original selected normals.
The full V2 equations are

    mu*c+nu*C=k*a,
    nu*S-mu*s=k*eta,
    mu*(d*s+c/2)=nu*(d*S+C/2).                   (11)

Putting u=mu*c>0 and v=nu*C>0, the last identity gives

    v/u=(d*p+1/2)/(d*q+1/2).

Consequently the exact full-circle parameter is

    eta=a*(q-p)/(2*(1+d*(p+q))).                 (12)

Its full closed physical-weight interval is equivalent to

    a*|q-p|<=1+d*(p+q),
    q-(2*d+1)*p<=1,
    p-(2*d+1)*q<=1.                             (13)

The last two inequalities together are equivalent to the first.
Their positive denominators and both signs of q-p are explicit.
Equality in the first signed inequality is eta=1/2; equality
in the second is eta=-1/2. Thus neither individual-zero physical
corner coefficient has been lost. Equal physical weights occur
exactly when p=q; they are permitted even though the two actual
pair normals remain nonparallel.

The actual normal-line concurrence is

    q_V=(d+1/(p+q),(q-p)/(2*(p+q))).             (14)

Both original ports are proper from this point, and its height
lies strictly between -1/2 and 1/2. Formula (12) gives its same
positive radial proportionality to (a,eta). As in row 1, no
upper bound on q_V,x is imposed. In particular physical-two
radial membership is not borrowed from a unique-corner theorem.

Equations (7)--(14) only eliminate variables from the complete
original V2 equations. They do not replace an actual force with
a selectable resultant, change a physical mask, or claim a new
packing certificate. Every original A3/D3 and exterior equation
continues to constrain these necessary domains.

## 9. Literal D02.L135 and D02.L1345 transfer

In each original caller retain the six-body rim 01,12,23,34,45,50,
the original positive chord02 and all three completing squares.
Use the literal roles

    A=0, V=1, D=2, C=3, N=4, B=5.

A and D are unloaded true3 with the exact neighbors stated in
Section 1. V,B,C are positively loaded true2. N is unloaded
true2 in L135 and positively loaded true2 in L1345. Their full
original equations and every physical circle mask remain. The
two possible graph-preserving exchanges of A,D also exchange
B,C and leave the correct true degrees unchanged.

The present result applies to the entire original physical-two,
nonparallel-V2 feature at every original radius. It excludes all
North/South support ports and leaves precisely the two necessary
inner-face charts above. It makes no boundary-neighbor assumption
at either triangle hub, and it assigns no degree-two equation
to an actual A3 or D3.

No step used the total-load equation at B,C or N; their extra
forces are retained rather than removed. No completing square
was assigned to a pocket or discarded. The original unloaded
and loaded N alternatives remain distinct.

The whole physical-two feature, the nonparallel unique-mask feature,
the original D02 rows and their coarse parents are not excluded
by this necessary-domain theorem. No original count or flag is
earned here. A further proof must handle both surviving charts
with their actual original hubs, exterior units, means and all
three completing squares.

## 10. Exact complete inputs and review boundary

| Complete input | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force/torque signs, positive pair magnitudes and unchanged shared means |
| LOADED_PARALLEL_FULL_STAR_WITH_DISTINCT_NEIGHBORS_FORCES_RADIAL_S_2026_10_29.md | f0e7b44a8d7e0eff5654384bf20bb5a99c3809d57a92bbb16afba6ee7ac1c96c | Only its complete Section 2 physical-mask and inward-unit-segment facts, reproduced here; no force-parallelity conclusion is used |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Pure physical triangle dot-product obstruction at a V-owned North/South axis, including its zero-dot endpoint |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Only the complete pure physical proper-port theorem of Section 2, with every actual mean and no boundary/resultant premise |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load labels and true degrees for the two D02 callers |

All five exact source pins match. Their complete operative scopes
were read before use; the new V2 feature cover, actual support
contradiction and all residual equations are proved above. The
separate radial-resultant and boundary-tip conclusions of the
end-triangle source are not applied at the unloaded hubs here.

The preliminary working note was explicitly unadopted. This is
the first complete frozen statement of the new theorem and needs
its own full noncontributor independent review before adoption.

All nine actual units, original positive forces, true degrees,
physical circle corners, individual zero coefficients, selected
normals and full original means remain. No numerical pose search,
angle mesh, new packing certificate, force deletion, selected-normal
change, Lean/Lake compilation, CI/workflow, remote mutation,
original flag edit or merge was used.
