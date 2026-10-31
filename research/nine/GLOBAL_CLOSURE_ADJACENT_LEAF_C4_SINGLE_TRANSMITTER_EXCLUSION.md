# An adjacent genuine-leaf four-cycle with one true transmitter is impossible

Date: October 27, 2026.

**Status: accepted complete hand theorem or reduction after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `6ce7dbc6fba926489136d37253e44ff2e053299e0309b1c2f7820735553f9910`. Root review: REVIEW_C3_334_B1_C4_ROOT_2026_10_27.md. Separate review: REVIEW_ADJACENT_LEAF_C4_SINGLE_TRANSMITTER_C6_2026_10_27.md. No shared ledger or fine label is
changed.

Keep the common canonical nine-square radius/Phi minimizer and its
compatible selected physical certificate. Work throughout

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 < 61/60,
    epsilon=max(d-1,0) < 1/60,
    M_*=91/60.

Every contained unit center has norm strictly less than M_*. This follows
from the farthest-corner lower bound |c|^2+|c|+1/2 and the exact reserve

    M_*^2+M_*+1/2-1105/256 = 31/57600 > 0.              (1)

The sharp contained-neighbor support bound is h<=d, from
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md Section 1. Distinct actual
unit centers are at distance at least one.

## 1. Exact original graph and full force systems

The original family is the following C3.334.b1 incidence and load row:

* A has an intact end triangle, so O belongs to int A.
* A-H-C-A is the middle positive triangle; C has its true degree two
  and positive circle load.
* H-X-U-V-H is the terminal positive four-cycle.
* X-L is the genuine leaf edge. X has precisely the three neighbors
  H,U,L.
* U has its true degree two and zero total circle weight.
* V has its true degree two and positive total circle weight.
* H keeps both middle-triangle forces and both four-cycle forces,
  initially together with its entire possible circle force.

These are the actual nine units: the three intact-petal units including
A, the additional middle units H,C, the private units X,U,V, and L.
All original positive magnitudes, contact owners, shared means, one-
and two-circle-corner masks, zero individual corner weights and
unstressed physical contacts are retained.

Every closed unit other than A avoids O. In particular X avoids O.
The genuine-leaf reduction therefore makes L an S leaf with d>1,

    epsilon=d-1>0,
    p_XL=d e,              |e|=1,
    F_L=lambda e,          lambda>0,
    dist(O,X)<=epsilon.                                (2)

Here F_L is the actual leaf force on X, equivalently the full radial
circle resultant of the real L. The genuine radial-edge theorem also
makes X physically circle-clear. These are physical conclusions, not
loads removed by convention.

The true U equations give a normal channel from X to V. H physically
touches both endpoints. If H were a physical boundary unit, the full
degree-free leaf-root detour theorem of
LEAF_ROOT_BOUNDARY_DETOUR_HOUSE_LOAD_EXCLUSIONS.md Sections 1--2 would
exclude it. Hence H is physically circle-clear as well.

Write G for V's full original positive circle resultant and put

    M=F_L+G.                                           (3)

Summing the unchanged equations at X,U,V cancels the internal forces.
The actual H-to-X and H-to-V vectors sum exactly to M. Thus M is H's
complete external resultant relative to the middle triangle; no H
circle force remains only because clearance was just proved.

The entire external system at each middle-triangle body has zero
origin moment, by summing the actual attached branches. Since
O belongs to int A, ROOTED_ORIGIN_TRIANGLE_EXTERNAL_RAY_RESTRICTION.md
proves that the middle moment is nonzero and M is nonzero. The full
positive-ray lemma in
GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md Section 1
therefore supplies an actual point

    D=s M in H,                 s>0.                  (4)

This statement concerns the full M in (3). It does not assign H a
two-force equation or replace the terminal block by a leaf.

The four-cycle likewise has one common directed weighted edge moment
k. Its external systems are complete: the genuine radial leaf at X,
the full circle system at V, and H's entire middle branch. If k=0,
the actual XU contact is radial. Both closed X,U avoid O, and U is
distinct from L, contradicting
ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md Section 3. Consequently

    k!=0.                                             (5)

## 2. The complete side-channel and bypass chart

UNIT_BYPASS_NORMAL_CHANNEL.md applies to the true U channel and the
physical bypass H. It proves reserve one, side alignment of U, and
transverse projection separation, including every tilted H. Rotate
and reflect about O so that

    U=[a-1,a] times [alpha,alpha+1],
    H subset {x>=a+g},       min_H x=a+g,       g>=0,
    X subset {y<=alpha},
    V subset {y>=alpha+1}.                             (6)

H's vertical projection contains [alpha,alpha+1]. The unchanged U
moment equation gives its two original applications as

    P=(x,alpha),             P_V=(x,alpha+1),
    a-1<=x<=a,                                          (7)

with the same actual x, not an imposed midpoint. Their common positive
force magnitude is gamma. In this chart n=e_y is X's outward channel
normal, and -n is V's outward channel normal.

The point of X within D_epsilon gives alpha>=-epsilon. The contained
neighbor V beyond height alpha+1 gives alpha+1<=d. Therefore

    -epsilon<=alpha<=epsilon.                          (8)

If w is H's vertical width, w<=sqrt(2). Its projection containment
gives

    (c_H)_y>=alpha+1-w/2
             >1-1/60-17/24=11/40,
    (c_U)_y=alpha+1/2>29/60>11/40.                    (9)

We used sqrt(2)/2<17/24, whose squared reserve is 1/576.
For later use,

    (3/2)^2+(11/40)^2-M_*^2=73/2880>0.               (10)

## 3. A positive bypass gap with a>=1/2 would force both private resultants west

Assume for this section that

    g>0,                    a>=1/2.                   (11)

### 3.1. The channel height is strictly positive

If alpha<=0, the U vertical interval contains zero, since
alpha+1>0. As U avoids O and a>0, its horizontal interval must
also avoid zero, forcing a-1>0. Then every H point has x>a>1,
so (c_H)_x>3/2. Equations (9)--(10) contradict |c_H|<M_*.
Thus

    0<alpha<=epsilon.                                (12)

### 3.2. The loaded V is nonparallel and G points west

First exclude all parallel V alternatives. If its two actual outward
normals have opposite signs, one points along G. With one physical
circle corner, or unequal weights on two physical circle corners,
that direction strictly exposes an actual circle corner, which cannot
be shared. With the equal two-corner resultant, it exposes the outer
radial face of support sqrt(R^2-1/4)>R-1; an outward unit neighbor
has width at least one and cannot fit in the containing disk. This
is the complete opposite-sign argument in
ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md Section 2.

If the two normals have the same sign, both are -n. The full
parallel-star classification, Lemma N.4 of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, makes V radial S or D
pointing upward. In D its unique inner application has height
r=R-sqrt(2)<7/10, contrary to alpha+1>1. In S,

    V=[-1/2,1/2] times [d,d+1],      alpha=epsilon.

Its actual VH contact then has x<=1/2, whereas every H point has
x>=a+g>1/2. Thus this alternative is impossible too.

V's pair is nonparallel. The conditional loaded-endpoint theorem in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md Lemma 2.1, explicitly restated
at its boundary-neighbor-free scope in
ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md Section 3,
gives

    q_V=t G,                  t>0,
    P_V=q_V-ell_U n,          ell_U>=0,
    Q_VH=q_V+ell_H m,         ell_H>=0,                 (13)

where m is the original outward V-to-H unit normal. This conditional
fact uses only V's true degree two, its positive circle load and the
nonparallelism just proved. It retains both physical corner masks
and does not assume that q_V lies in V.

By (7),(13), (q_V)_x=x. Every Q_VH belongs to H, so

    (Q_VH)_x>=a+g>a>=x.

Therefore ell_H>0 and m_x>0. The complete V force equation is

    G+nu m-gamma n=0,                  nu>0.

It follows that

    G_x<0,             x=t G_x<0.                     (14)

Let Q be the original XH application. Equations (6),(11),(14) give
the strict horizontal separation

    Q_x-P_x>1/2.                                     (15)

### 3.3. Complete own-frame geometry of the genuine X

Choose own orthonormal axes u,v for X so that

    X=[delta,1+delta]u+[-beta,1-beta]v,
    e=A_0 u-B_0 v,
    A_0>60/61,   B_0>=0,   A_0^2+B_0^2=1,
    0<delta<=epsilon,              0<=beta<=1/2.       (16)

Here is the complete origin-free leaf justification. If the real
S contact is side-normal, u=e, delta=epsilon, A_0=1,B_0=0;
its actual transverse interval contains zero. Reflect v so its
lower magnitude beta is at most 1/2. The whole slider remains.
If it is a vertex contact oblique to both own axes, choose u along
the larger absolute component of e and choose v with negative
component. Then

    delta=d A_0-1,             beta=d B_0.

The minor interval contains zero because d B_0<=d/sqrt(2)<1.
Since X avoids O, delta>0. Hence A_0>1/d>60/61,
B_0<11/61, and 0<beta<11/60<1/2. Its actual leaf application
is the far-bottom vertex d e. These are all radial S support features,
including the side endpoints in the aligned alternative.

We first record a physical exclusion valid throughout (16):

    No other actual neighbor of X can have outward normal +u. (17)

Indeed the actual leaf center is (d+1/2)e, and its u coordinate
is strictly greater than 91/61. In the tilted case,

    (d+1/2)A_0>(d+1/2)/d>1+30/61=91/61;

the aligned case has that coordinate d+1/2>3/2>91/61.
Any contained neighbor beyond X's far u side has center u
coordinate at least 1+delta+1/2>3/2>91/61. Both centers would
belong to one cap rectangle whose squared diameter is

    (M_*-91/61)^2+4(M_*^2-(91/61)^2)
          =803257/2679120<1.                          (18)

This contradicts their incircle separation. No force or radiality
at that other contact was introduced.

Write n=n_u u+n_v v for the actual upward channel normal, and
write w for the original X-to-H unit normal. The true X equation is

    mu w=-lambda e-gamma n,              mu>0.         (19)

It includes exactly the genuine three positive edges; physical
clearance of X was established in Section 1.

### 3.4. The upward normal has n_u<0 and n_v!=0

If n_u,n_v>=0, its support on X is at least
(n_u+n_v)/2>=1/2, contrary to alpha<=epsilon<1/60.

If n_u>0 and n_v<0, its support is

    alpha=(1+delta)n_u+beta|n_v|.

Thus n_u<epsilon<1/60, |n_v|>59/60 and beta<1/59.
The XU application is its unique far-bottom vertex. In the tilted
case this is d e, the relative interior of L's radial inner side,
and n.e=A_0 n_u+B_0|n_v|>0. The actual inward segment
P+t n in U therefore enters int L for small t>0.
In the aligned case P=d u-beta v also lies in the relative interior
of that L side, because beta<1/59<1/2; n_u>0 gives the same
overlap. The argument remains valid when P is an endpoint of a
U side: P+t n is still in closed U, and a closed point of U in
int L implies interior overlap of the two full units.

If n_u=0,n_v=-1, then alpha=beta. Equation (19) has
w_u<0,w_v>0, so Q is the near-upper vertex. Its global height
is alpha-1. But H also touches V at height at least alpha+1.
This requires H to have vertical width at least two, impossible.

These cases exhaust n_u>=0. Therefore n_u<0. If n_v=0,
n=-u would have support -delta<0, contrary to (12).

### 3.5. The case n_v<0 forces the genuine leaf west

Write

    n=-c u-s v,        c,s>0,       c^2+s^2=1.

Then P is the near-bottom vertex. Equation (19) has
w_v=(lambda B_0+gamma s)/mu>0. Thus Q is on the upper
own face, with

    Q-P=t_0 u+v,                      0<=t_0<=1.

Its global height is alpha-t_0 c-s. Since H has another actual
point in V at height at least alpha+1, its vertical width gives

    t_0 c+s<=sqrt(2)-1<1/2.

In particular s<1/2 and c>s. The global right axis has own
components either (-s,c) or (s,-c). In the latter orientation,

    Q_x-P_x=t_0 s-c<0,

contradicting (15). Hence the actual global right axis is
-s u+c v. The genuine leaf direction satisfies

    e_x=-A_0 s-B_0 c<0.                              (20)

The full top-side mean t_0 was retained.

### 3.6. The case n_v>0 also forces the genuine leaf west

Write

    n=-c u+s v,        c,s>0,       c^2+s^2=1.

Now P is the near-upper vertex, and its support equation is

    (1-beta)s=alpha+delta c<2 epsilon.

Since beta<=1/2, this gives s<4 epsilon<1/15. Write the actual
point Q, without any feature assumption yet, as

    Q-P=t_0 u-z v,                    0<=t_0,z<=1.

If the global right axis were s u+c v, then
Q_x-P_x=t_0 s-z c<=s<1/15, contrary to (15).
Therefore it is -s u-c v, and

    -t_0 s+z c>1/2,                  z>1/2.            (21)

In particular Q is not on the upper own face or either upper
vertex. An interior point of its far u face would have outward
normal +u, excluded by (17). Its far-bottom vertex would have
global height alpha-c-s; H's point in V would then require
vertical width at least 1+c+s>=2, again impossible.

Every remaining actual boundary feature of Q is the near u face,
the bottom v face, or their common vertex. Including their axis
endpoints and all side means, its outward normal obeys

    w_u<=0,                 w_v<=0.

Equation (19) consequently gives

    gamma c<=lambda A_0,       lambda B_0<=gamma s,
    B_0 c<=A_0 s.

Equality in the last comparison would force equality in both
preceding comparisons, and then w_u=w_v=0, impossible for a
unit normal. Thus B_0 c<A_0 s. In the actual right orientation,

    e_x=-A_0 s+B_0 c<0.                              (22)

This exhausts the entire n_v>0 domain, including B_0=0.

### 3.7. The full original resultant contradicts its positive point in H

Equations (20),(22) give (F_L)_x=lambda e_x<0 in every remaining
genuine-leaf feature. Equation (14) gives G_x<0. Therefore

    M_x=(F_L)_x+G_x<0.

But every actual H point has x>=a+g>1/2, while (4) gives the
actual H point D=sM with negative first coordinate. This is a
contradiction. We have proved the full implication

    g>0  implies  a<1/2.                             (23)

No origin-free body was assumed to have a positive concurrence
at its leaf pair. The X argument used its actual three forces
and complete physical support features only.

## 4. Canonical minimality now forces actual H-U contact

Suppose g>0. The four original cycle applications are distinct:
the U ports differ by the unit vertical reserve; the H ports
have heights at most alpha and at least alpha+1; and any adjacent
or opposite coincidence would lie in both H and U, contrary to
their positive horizontal gap.

The four-center/contact loop is therefore Jordan. The complete
horizontal-slice proof in FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md
Section 3 uses only the chart (6): the X,V strands are absent
at heights in (alpha,alpha+1), and the H,U strands each cross
each such height exactly once. It puts the entire open rectangle

    (a,a+g) times (alpha,alpha+1)                      (24)

on the bounded side of the loop.

No other actual unit can occupy its bounded region. The precise
degree-free input is FOUR_CYCLE_LEAF_HOLE_EMPTY.md Sections 1--3:
an occupied four-cycle hole forces equality in the four-chord
area bound, hence the aligned four-neighbor cross. At the true
unloaded U, its two opposite positive normals must be parallel
to the unit side joining its two contact applications. Both
contacts in that cross are point-only vertex/vertex contacts, so
those axis normals violate the existing strict selected convention.
This uses only U's true degree two; neither X nor H is shortened
to degree two. Every other actual unit's connected open interior
is disjoint from the cycle and lies wholly on one side. Thus none
enters (24), including L,A and all intact/middle units.

By (23), c_Ux=a-1/2<0. Choose

    0<t<min(g,1/2-a).

Translate only U by t e_x, keeping its frame and all eight other
actual squares fixed. It remains between X,V and strictly left
of H. Every newly occupied interior point outside its old closure
lies in (24), so all original nonoverlaps remain valid. Points
of its old boundary cannot lie in another actual open unit either,
by the original interior-disjointness.

Its center first coordinate remains negative. For this aligned
unit the maximal corner squared radius is exactly

    (|c_Ux|+1/2)^2+(|c_Uy|+1/2)^2.

The translation strictly decreases that value, even if U originally
had a physical circle corner with zero weight. It also strictly
decreases |c_U|^2, and hence Phi, with every other term unchanged.
This contradicts the already chosen minimum of Phi among radius
minimizers. Consequently

    g=0.                                             (25)

This gives an actual physical H-U contact. For completeness, if
H is parallel to U, its height-one projection is exactly
[alpha,alpha+1], so their transverse support sides meet. If H
is tilted, its unique leftmost vertex has vertical distances
strictly less than one from both its top and bottom vertices.
Because its projection contains [alpha,alpha+1], that leftmost
vertex lies strictly between alpha and alpha+1, on U's right
side. No positive H-U multiplier is inferred.

## 5. Every possible actual H-U contact is impossible

Choose an actual common point p=(a,y_0), with its geometric
separating normal -e_x directed H to U. Put

    h=det(p,-e_x)=y_0.

This is a geometric choice on an unstressed physical pair; it
does not reselect or add a positive normal in the certificate.

If h has the sign of k in (5), the physical triangle H-U-V-H
has all three directed normal-line moments strictly of that sign.
If h has the opposite sign, H-X-U-H has all three strictly of
the sign of k. Original edge magnitudes are positive, so replacing
weighted k by their normal-line moments preserves signs. The
complete ROOTED_GEOMETRIC_TRIANGLE_MOMENT_CIRCUIT_EXCLUSION.md
excludes either triangle beside the actual origin-interior A.
Its auxiliary positive coefficients are geometric parameters,
not a fabricated physical stress on HU.

It remains h=0, so p=(a,0). If a=0, O belongs to H and U,
already impossible. If a>0, U is the inner radial unit and H
the outer unit. Both avoid O. The pure radial-contact geometry
in ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md Section 1
therefore gives a>1. Hence (c_H)_x>=a+1/2>3/2,
contradicting (9)--(10) and |c_H|<M_*.

If a<0, H is the inner radial unit in direction -e_x and U
is outer. The same origin-free support theorem gives -a>1.
Thus (c_U)_x=a-1/2<-3/2. Its positive vertical coordinate
in (9), together with (10), again contradicts |c_U|<M_*.

These are all actual geometric contact possibilities, including
shared sides, endpoints and y_0=0. Thus (25) is impossible.

## 6. Whole original-row conclusion and scope

The entire adjacent-leaf row

    H-X-U-V-H,      X-L genuine,
    U true unloaded degree two, V true loaded degree two,

is excluded in the original C3.334.b1 R3 graph. The proof kept
H's full middle-triangle system, proved H physically clear before
identifying its external M, and used the actual positive-M point
from that unchanged triangle. It kept X's true degree three,
both V circle masks, both actual U means, every side endpoint,
every genuine S slider/orientation and all nine physical units.
The D and d<=1 possibilities were removed only by the actual
outside origin-interior A and the complete genuine-leaf theorem.

No minimum-support strengthening beyond the common canonical
radius/Phi selection was needed. The sole motion was the explicit
counterfactual translation contradicting that preexisting minimum;
the obtained packing and physical stress remain unchanged. The
extra H-U edge was used only as a physical geometric contact.

This proves this entire original R3 load row. Its sibling opposite-
leaf and adjacent-both-loaded rows remain separate source joins;
no broader C3.334.b1 closure or fine-ledger change is claimed here.

No numerical pose, Lean compilation, CI, workflow, remote action
or shared-ledger edit is used.
