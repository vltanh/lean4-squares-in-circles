# An actual inner-circle crosscut closes the entire common-hub-axis L0134 interface

Date: October 28, 2026 UTC. Author: pentagon_resume.

**Status: complete new hand proof, frozen for full root and separate
independent review.** The first theorem is a force-free geometric
crosscut and arc-capacity statement. The second covers a complete
partially unloaded path with nonparallel first tip and common hub
axis. The final theorem excludes the entire original D02.L0134
feature in which the UV and UW normals are the same own axis of U,
including the full parallel/shared and nonparallel/singleton cover.
It does not claim closure of the whole original L0134 row.

All original units, the containing-circle origin, positive forces,
actual physical contact sets, applications and full side means,
circle masks, individual zero corner coefficients and true positive
degrees stay fixed. The real unloaded internal path body is never
contracted into a boundary-to-boundary edge.

Put Q=1105/256 and rho=9/8.

## 1. A degree-free actual inner-circle crosscut theorem

Let U,X,Y be three distinct actual closed unit squares in the same
disk D_R about the unchanged O, with pairwise disjoint open interiors.
Let 0<r<R and suppose

    U is contained in int D_r,
    R^2>r^2+2.                                         (1)

X and Y are physically closed-disjoint and touch U at the respective
gap-facing actual contact extremes A_X,A_Y. An actual outer U boundary
arc joins those extremes and lies strictly in y>0. The two actual
physical circle corners chosen on the gap side are Z_X,Z_Y. These
are physical corners, regardless of their individual force weights.

Write theta_X,theta_Y for the actual center directions and put

    Q_X=r*c_X/|c_X|, Q_Y=r*c_Y/|c_Y|.

Assume Q_X belongs to int X and Q_Y to int Y. Assume Q_X,Z_X lie
in the strict first quadrant and Q_Y,Z_Y in the strict second
quadrant. The actual closing circle arc is the upper minor arc from
Z_X to Z_Y, with its original exterior-face assignment.

No degree, force, normal owner, mean, circle load or other-neighbor
premise is imposed in this section. The enclosing physical
configuration may have any additional units and contacts.

**Crosscut theorem.** There is an actual occupied simple crosscut,
through these same endpoint units and the same outer U arc, whose
Jordan boundary meets the radius-r circle exactly at Q_X,Q_Y.
Its bounded side intersects that circle in precisely the upper
open interval

    theta_X<theta<theta_Y.                              (2)

Every open-interior circle arc of a whole actual extra assigned to
this closing side is therefore contained in (2).

### 1.1. The endpoint paths cross the test circle exactly once

Use the endpoint paths

    A_X--Q_X--Z_X,   A_Y--Q_Y--Z_Y.                     (3)

The first open segment on each path is in the corresponding unit
interior: its final endpoint Q is interior and its initial endpoint
A is an actual point of that convex unit. By (1), A is strictly
inside D_r, so that segment is inside int D_r except at Q.

For the second segment, the two actual points Q,Z are in the same
unit, so |Z-Q|^2<=2. Since |Q|=r and |Z|=R,

    Q.(Z-Q)=(R^2-r^2-|Z-Q|^2)/2
             >=(R^2-r^2-2)/2>0.                       (4)

It follows that Q+s(Z-Q) has norm strictly greater than r for
every s>0. Thus Q is the path's unique intersection with the
test circle. The open second segment is in the actual endpoint
unit interior as well, since Q is interior.

Each path meets U only at its initial actual extreme; an interior
point of X or Y cannot belong to the closed U without forcing
an overlap of open interiors. The same fact prevents every other
actual unit's open interior from meeting these paths. Their
disjointness follows from the actual closed-disjointness of X,Y.
Within either path the two segments cannot cross except at Q,
because one is inside D_r and the other outside.

Together with the actual outer U arc, (3) forms a simple occupied
crosscut. It meets the containing circle only at Z_X,Z_Y:
the endpoint interiors lie in int D_R and U is inside D_r.
Add the actual upper closing circle arc. This is a Jordan
boundary J, and

    J intersect {z:|z|=r}={Q_X,Q_Y}.                    (5)

No original mean or chosen normal has changed. Any previously used
endpoint path can be replaced by (3) through the same actual convex
endpoint square, preserving the prescribed contact extreme and
gap-facing physical corner. The routing remains occupied and
cannot pass through any other unit's open interior. Thus the
bounded-side label of each whole closing extra is unchanged.

### 1.2. Which of the two test-circle intervals is bounded?

The whole J lies in the strict upper half-plane. The U arc does
by assumption, the points A do because they lie on that arc,
and the paths in (3) and upper circle arc do by convexity and
their stated quadrants. Therefore the lower test-circle interval
from Q_Y around through (0,-r) to Q_X belongs to the unbounded
side of J.

The point (0,r), on the other test-circle interval, lies on the
bounded side. Indeed the vertical segment

    {(0,s): r<=s<R}

misses the whole crosscut: its U portion and both first path
segments lie strictly inside D_r, while both second path segments
are respectively in the strict first and second quadrants.
The vertical ray from (0,r) to infinity meets J exactly once,
transversely at (0,R), an interior point of the upper closing
circle arc. The Jordan inside/outside crossing rule therefore
places (0,r) on the bounded side.

Each of the two open test-circle intervals in (5) is connected
and disjoint from J. Its inside/outside label is constant.
The preceding two points establish exactly (2).

For a whole closing extra, every point of its connected open
interior avoids J and keeps the original bounded-side label.
At a weak physical junction, first fix a compact subset of
that open interior and use the compatible original routing
in sufficiently small junction neighborhoods. Taking closure
retains its whole actual square on the same closed side.
Any of its open-interior points on the test circle thus lies
in (2). This is an actual occupied-region statement, not a
location inferred from an auxiliary force polygon.

### 1.3. The complete reusable arc-capacity consequence

Suppose additionally that X and Y each contain their closed
test-circle arcs of halfwidth alpha>0 centered at theta_X and
theta_Y in their open interiors. Suppose each whole extra under
consideration has a connected open-interior test-circle arc of
length strictly greater than beta>0.

Such an extra's arc avoids the endpoint squares and by (2)
is contained in the interval

    theta_X+alpha<theta<theta_Y-alpha.                 (6)

If that interval is empty there is no extra. Otherwise n distinct
extras would give disjoint arcs of total length greater than
n beta. Consequently

    theta_Y-theta_X-2 alpha<=n beta                   (7)

implies that the closing region contains at most n-1 such extras.
The weak inequality in (7) is sufficient because every occupied
extra arc is strictly longer than beta. This statement includes
all actual circle masks and contact means and every endpoint
of the length bound.

## 2. Entire partially unloaded common-axis path domain

Now retain the original nine actual unit squares and the common
compatible selected physical certificate in

    2<R<=sqrt(Q).

An entire positive component consists of U and the path

    B_1=V, B_2=W, B_3,...,B_(k-1),B_k=T, k>=3,

with precisely the actual path edges and the three actual spokes

    B_i B_(i+1) (1<=i<k),    UV,UW,UT.                 (8)

The actual exterior cycle is U,V,W,...,T,U, with its original
simultaneous exterior physical circle spokes and compatible
weak-junction routing. Every positive force in the component
is retained.

U is unloaded and physically circle-clear. The endpoints V,T
are positively loaded, have their true positive degree two,
and are physically closed-disjoint. Their respective actual
other neighbors W and B_(k-1) physically touch the circle.
Internal path bodies, including W, may have zero or positive
circle load. The component has at least three positively loaded
bodies. No internal unloaded body is deleted.

Suppose the two original normals n_UV,n_UW are the same own
side axis of U. Retain the strict point-contact convention and
already common fixed-tip selection at its exact premises.

**Theorem A.** If V is nonparallel to U, the actual closing exterior
pocket through U between V,T contains at most two whole additional
unit squares.

There is no one-circle assumption at V or W, no T-frame or owner
assumption, and no restriction on any original side mean. The
complete local all-mask theorem6a388f0c supplies the mask and
frame consequences used next. T's actual boundary other neighbor
is needed here only for its genuine endpoint moment/properness,
exactly as in the full modular partially unloaded-path theorem.

## 3. Literal use of the whole local common-face theorem

The full local theorem6a388f0c applies to the unchanged true U3,
loaded V2, physical boundary W and contained T. Its statement
allows arbitrary degrees and loads at W,T and does not require
a loaded path.

For a nonparallel V it first proves the complete original owner
normal form: the UV point is V's actual unique left vertex;
every V-owned VW case, including the whole shared-mean interval,
is excluded; the physical-two free case is excluded directly;
and the unique-circle free case enters the already common selector
only after its two actual fixed singleton applications are proved
distinct. The remaining VW contact is a V-vertex/W-side-interior
singleton owned by W. W may be aligned.

For clarity record its full actual chart, after one rotation and
reflection about O:

    U=[a-1,a] times [b,b+1],
    P=(a,t),
    V=P+[0,1](c,-s)+[0,1](s,c),
    c,s>0, c^2+s^2=1.                                 (9)

The whole minimum-x W support is below P. Its geometric upper
left support point is

    P_W=(a,t-delta),    0<delta<=1,

and belongs to the actual U side. At aligned W this is its
upper-left corner; its original UW mean may lie anywhere at
or below it in the actual shared contact interval. It is not
substituted into a torque equation.

The local source proves t>0 directly from V's entire actual
circle resultant and its genuine interior line intersection.
The contained T supplies a>-1/60. Those two signs make the
physical V-mask split exhaustive: the two-corner and unique
upper-adjacent masks have complete local contradictions; the
remaining mask is exactly the unique opposite corner

    Z_V=(a+c+s,t+c-s),    c>s.                          (10)

The full W-mask calculation then proves its unique right
physical circle corner and its whole square strictly below O.
In particular c_V is in the first quadrant, while c_W is in
the fourth quadrant. Every initially possible zero corner
coefficient remains in the proved mask cover.

The complete local support bounds are

    3/10<a<2/3,
    t>1/8,    t-delta<-1/8,
    D_(1/8) is contained in int U.                     (11)

These conclusions require no T moment, no path order and no
allocation of any completing square. They are the literal
entire nonparallel conclusion of the independently reviewed
source, not a unique-mask theorem applied before that mask
has been proved.

The actual vertical U interval contains both t and t-delta.
Thus

    b>=t-1>-7/8,
    b+1<=t-delta+1<7/8.

Together with (11), every actual U point satisfies

    |x|<7/10, |y|<7/8,
    |z|^2<2009/1600<2025/1600=rho^2.                 (12)

Hence the entire actual U lies strictly inside D_rho.
Every other original closed unit has distance strictly greater
than 1/8 from O: a point in the closed D_(1/8) would be in
int U and, by density of that unit's own interior, would force
open-interior overlap. Compactness makes the distance strict.

The full mask/source proof and its full independent record
24fae6c7 were read before this invocation. Its exact original
U3/V2 and all-mean hypotheses are present in (8)--(9).

## 4. The actual T height and complete endpoint mask

Write the unchanged UW mean as (a,z), with z<t, and its positive
magnitude mu_W. Full original U force balance gives

    n_UT=West,    mu_T=mu_V+mu_W>0,
    P_T=(a-1,h).

Its complete original torque is

    mu_T h=mu_V t+mu_W z.                              (13)

No sign of h is inferred from this average alone.

The physical V--W pair begins clockwise in circle-center
order by the first/fourth quadrants above. The original protected
exterior cycle gives this order to its physical boundary
subsequence, with every unloaded internal path body still
present. At the genuine last boundary pair B_(k-1),T, the
degree-free boundary-edge moment has the corresponding clockwise
sign. The full true-T2 torque therefore gives h>0, exactly
f0220431 Section1. Together with z<t in (13),

    0<h<t.                                             (14)

The actual loaded T2 has physical boundary other neighbor
B_(k-1). Its full proper-concurrence lemma gives

    q_T=(a-1-lambda_T,h),
    lambda_T>=0,
    q_T is a positive multiple of F_T.                 (15)

This is the whole original F_T, including either zero individual
circle coefficient. An exterior two-corner concurrence is allowed.

Put u=1-a, so by (11)

    1/3<u<7/10.

The whole T has maximum x=-u<0. We now rederive at this changed
path scope the complete T-mask argument in ffddf725 Section6.

### 4.1. One physical T circle corner

In the unique-circle case, the full proper lemma additionally
puts q_T in T. Thus q_T=k Z_T, with 0<k<=1.
Reflect x only for this local calculation. The actual port
becomes (u,h), and its inward direction into T is East.

If East is a T axis, the vertical center coordinate must be
positive: the unique farthest vertical coordinate has the
same sign as that center coordinate, and (15) makes its
physical circle corner height h/k>0. A zero vertical center
would give two physical corners instead.

If East is nonaxis, its actual minimum-x point is the vertex
(u,h). Write its inward axes as (c_0,s_0),(s_0,-c_0),
with c_0,s_0>0 and c_0^2+s_0^2=1. The port itself cannot
be a circle corner because it is shared with U.
The lower-adjacent corner has height h-c_0<h, so cannot
have h=k(Z_T)_y with 0<k<=1 and h>0.

If the physical corner is opposite, its height is
h+s_0-c_0>=h, giving s_0>=c_0 and actual center height
h+(s_0-c_0)/2>0. If it is the upper-adjacent corner,
containment of its adjacent opposite corner gives

    u s_0-h c_0<=-1/2.

Consequently h>1/(2c_0), and again
h+(s_0-c_0)/2>0. These are all actual unique-circle
corner choices. After reflecting back, c_T is in the
strict second quadrant and its unique Z_T has positive
y by (15); its x is negative because the whole T does.

### 4.2. Two physical T circle corners

For two physical corners, T has its actual radial-S form.
In the locally reflected coordinates write

    D=sqrt(R^2-1/4)-1>7/10,
    T=D e+[0,1]e+[-1/2,1/2]Je,
    c_T=(D+1/2)e.

The whole T lies in x>=u>0, so e_x>0. If e_y<0,
its unique minimum-x vertex has height

    -D |e_y|-e_x/2<0,

contrary to its original port height h>0. If e_y=0,
its minimum-x side is x=D, forcing u=D>7/10,
contrary to u<7/10. Thus e_y>0, and its actual
center has positive height.

In the original coordinates the center is again in the
strict second quadrant. The physical corner facing the
closing V-to-T gap is the clockwise one of the two.
Its height is the positive center-radial contribution plus
one half the absolute horizontal radial component, hence
strictly positive. Its x is negative because T has maximum
x=-u<0. Thus this actual gap-facing Z_T is also in the
strict second quadrant. This is a geometric corner choice
for the occupied crosscut, with both original physical
corners and both coefficients retained.

No assertion that the two-corner q_T belongs to T was used.
Equations (14)--(15), actual T containment and its two
complete physical masks prove all conclusions above.

## 5. The actual upper endpoint center gap is shorter than seven pi eighths

Write

    theta_V=alpha_0 in (0,pi/2),
    theta_T=pi-beta_0, beta_0 in (0,pi/2).

The actual boundary center radii satisfy

    |c_V|,|c_T|>=R-1/sqrt(2)>31/24.

Their opposite actual horizontal supports are x=a and
x=a-1. Hence

    (c_V)_x-(c_T)_x
      =1+[width_V(East)+width_T(East)]/2
      <=1+sqrt(2)<29/12.                              (16)

If theta_T-theta_V>=7pi/8, then alpha_0+beta_0<=pi/8,
so

    (c_V)_x-(c_T)_x
      >(31/24)[cos(alpha_0)+cos(beta_0)]
      >=(31/24)[1+cos(alpha_0+beta_0)]
      >=(31/24)[1+cos(pi/8)]
      >(31/24)(19/10)=589/240>29/12.                  (17)

The cosine-sum inequality follows from the half-angle identity.
The strict bound cos(pi/8)>9/10 follows by squaring its
positive radical sqrt(2+sqrt(2))/2. The final reserve is
3/80. Thus (16)--(17) prove

    0<theta_T-theta_V<7pi/8.                           (18)

The boundary-center lower estimate uses only R>2 and
1/sqrt(2)<17/24. The width upper estimate retains all
actual endpoint frames and both T masks.

## 6. The genuine closing crosscut satisfies every inner-circle premise

The actual UV intersection is the singleton P=(a,t).
Choose the gap-facing upper extreme of the actual UT
contact set:

    A_V=P,    A_T=(a-1,h_ext),    h_ext>=h>0.          (19)

Only geometric routing uses this extreme. The original
h stays unchanged in (13)--(15). The outer U arc goes
up the right side from P, left along the top side, and
down the left side to A_T. Every point of that actual
arc has positive y, and (12) places the whole arc
strictly inside D_rho.

The endpoint units are physically closed-disjoint by
Section2. Both actual center-direction points

    Q_V=rho*c_V/|c_V|,
    Q_T=rho*c_T/|c_T|

belong to their open unit interiors. One may see this
directly from the open radius-1/2 incircles:

    rho<31/24<|c_V|,|c_T|<91/60,
    |c_i|-rho<47/120<1/2.

The universal strict center upper bound follows from
r_c^2+r_c+1/2<=Q and the reserve31/57600 at r_c=91/60.

The points Q_V and the actual unique Z_V lie in the first
quadrant by (9)--(11). The points Q_T and the actual
gap-facing Z_T lie in the second quadrant by Section4.
Also

    R^2>4>rho^2+2=209/64.                              (20)

The original protected exterior order is clockwise along
V,W,...,T, so its complementary closing circle arc
from V to T is exactly the counterclockwise upper minor
arc between these gap-facing physical corners.

The occupied-pocket construction in f0220431 Section2
places every whole actual closing extra on the bounded
side of the outer U arc and endpoint paths to these
same physical corners. Replacing those endpoint paths
by (3) keeps them inside the original endpoint units
and preserves that side label; it crosses no extra's
open interior. Additional physical contacts, including
zero-weight corners at unloaded internal path bodies,
only refine the region. The full actual corner intervals
and weak-junction routing remain as in that source.

Thus every premise of the force-free crosscut theorem
in Section1 is literal. It puts each closing extra's
open-interior radius-rho arc in

    theta_V<theta<theta_T.                            (21)

This is the new routing step. The former all-loaded-path
argument that consecutive boundary-contact centers are
consecutive among all eight arcs is not used across an
unloaded internal vertex.

## 7. Whole nonparallel common-axis closing capacity is two

Every actual unit other than U has distance greater than
1/8 from O by (11). The whole theorem5c0da364 therefore
gives its open-interior radius-rho intersection as one
connected open arc longer than 2pi/9. It includes all
unit orientations and both entire coordinate regimes
of that arc theorem. The center-direction point belongs
to this same actual arc.

The two actual boundary endpoints V,T additionally contain
their closed centered radius-rho arcs of halfwidth pi/9
in their open interiors, by the full force-free theorem
d575e663. Hence every closing extra's whole connected
arc lies in

    theta_V+pi/9<theta<theta_T-pi/9.

By (18) this interval has length strictly less than

    7pi/8-2pi/9=47pi/72<48pi/72=3(2pi/9).             (22)

Three disjoint arcs each longer than 2pi/9 cannot fit.
Section1.3 with n=3 proves Theorem A: the entire actual
closing pocket contains at most two whole extra units.

Every internal path square and force remains. No physical
boundary status, properness or selected load is assigned
to an unloaded internal body. The result uses the whole
V-mask cover in6a, the entire T-mask proof in Section4,
every original UW/UT mean and the actual occupied
closing side.

## 8. The literal original L0134 common-axis feature

Keep the exact original graph and load set

    rim01,12,23,34,45,50,    positive chord02,
    positive circle-load set {0,1,3,4}.

Use the unchanged physical labels

    U=2, V=1, W=0, N=5, B=4, T=3,
    (B_1,...,B_5)=(1,0,5,4,3).

The true positive neighborhoods are

| Body | Original positive neighbors | Degree | Circle load |
| --- | --- | --- | --- |
| U2 | V1,W0,T3 | 3 | zero |
| V1 | U2,W0 | 2 | positive |
| W0 | V1,U2,N5 | 3 | positive |
| N5 | W0,B4 | 2 | zero |
| B4 | N5,T3 | 2 | positive |
| T3 | B4,U2 | 2 | positive |

All six original component units, its seven positive
edges, the three actual completion squares and every
additional physical contact are retained.

The entire feature under consideration is

    n_UV=n_UW, both the same own side axis of U.       (23)

The full original same-nine lower-window theorem supplies
R>2 without applying a nine-square assertion to a smaller
component. Thus every original R<=2 was already covered;
the present proof includes R=sqrt(Q).

All modular hypotheses hold on (23), exactly as f022
Section7 proves at every U interface. U is physically
circle-clear by the physical boundary triangle012
obstruction. The full true-U3 touching-return theorem406
with touching V,W makes T closed-disjoint from V and W.
V and T are genuine loaded2 endpoints, with their actual
physical boundary other neighbors W and B. The protected
boundary subsequence is V,W,B,T, with unloaded N still
present between W and B. Summing every original body
equation gives

    F_V+F_W+F_B+F_T=0.

No W3 force is dropped and no W--B contact is inserted.

### 8.1. Entire parallel V branch

The complete local common-face theorem6a388f0c proves
that parallel V forces parallel W. In the original
strict certificate, each retained side-axis normal
between parallel units has a positive-length physical
contact: an isolated vertex/vertex contact cannot carry
an endpoint of the strict vertex normal cone.

Thus both physical UV and UW contacts have positive
length on the same actual U side. The entire29cc0e27
same-face partially unloaded-path theorem applies.
It proves closing capacity one, retains the actual
central/channel/closing allocation, and excludes the
forced (1,1,1) using the actual U,N and central extra.
All original shared means are included. This excludes
the entire parallel V branch of (23).

### 8.2. Entire nonparallel V branch: central and channel occupancy vanish

For nonparallel V, the whole local theorem gives

    D_(1/8) is contained in int U,
    every other original unit has distance>1/8.       (24)

Its all-mask and owner proof is already complete; no
chosen physical V mask is assumed in this case split.
Theorem A gives closing capacity at most two.

Use the exact physical allocation in47c524c9 Section11.
The actual occupied exterior spokes from V,W,B,T
divide the exterior into the two direct-boundary-pair
pockets V--W and B--T, the real channel W--N--B,
and the closing T--U--V pocket. Every completion's
connected open interior has one actual central or
exterior label. The original chord and all compatible
weak subdivisions remain.

The two direct-pair pockets are empty. If any actual
completion E were central, the full finite-ring and
enclosed-unit restrictions in47c Section12 would give

    dist(O,E)<sqrt(2)*121/7200<1/40<1/8,

contradicting (24). Thus the actual bounded central
union contains no completion.

If the actual W--N--B channel pocket contained any
completion, the full occupied-channel results in the
same source give, at the original true unloaded2 N,

    dist(O,N)<1/40

in the width-one side case, or O in int N in the
diagonal case. These cover its whole real side/diagonal
transmission classification and original port means.
The side theorem permits W's true degree three.
The diagonal theorem uses properness only at the
actual loaded B2, whose real other neighbor is the
boundary T. Either conclusion contradicts (24),
because N is a distinct original unit. Hence the
actual channel pocket is empty as well.

This argument does not need to infer a channel capacity
from a fictitious boundary edge. It uses the entire
conditional occupied-channel proximity theorem on the
actual N transmitter, with the literal one-proper
endpoint where required.

All three completion units must therefore be in the
one actual closing pocket. Its capacity is at most two
by Theorem A, a contradiction. Every original
allocation has been covered: any central or channel
occupancy contradicts (24), while an all-closing
allocation contradicts (22).

### 8.3. Complete exact conclusion

The V frame is either parallel or nonparallel to U.
Sections8.1--8.2 exclude both entire alternatives.
Therefore:

**Theorem B.** In the original M6.B6.HEXAGON.D02.L0134
family, the two original U-to-V and U-to-W normals
cannot be the same own side axis of U.

This is the whole common-U-axis feature, including
every initial V,W,T physical circle mask and every
zero individual coefficient, all shared and singleton
contacts, every original mean endpoint, all actual
owners, and all three original completion squares.
All graph-preserving reflected images are handled by
transporting the whole physical configuration.

The opposite axis at UT was derived from full U3
balance, not imposed as a convenient added condition.
The perpendicular UV/UW feature and the three possible
sole-U-axis features are separate remaining original
domains. The previously proved zero-U-axis feature
also keeps its exact scope. No entire L0134, D02
graph parent or coarse six-body flag is claimed here.

## 9. Exact inputs, full reading and independent-review boundary

The new contribution is the actual test-circle
crosscut theorem, its complete changed-path
nonparallel capacity-two implication, and the
whole original common-U-axis allocation union.
The older all-loaded-path eight-arc argument is
not applied after silently deleting N.

The whole local all-mask theorem6a and its full
independent review24fa, the whole ffdd opposite
source and its full independent reviewe6fb, the
complete f022 modular source and full da39 review,
the complete47c source and full13d6 review, and
both entire actual-arc theorems were read at
their exact scopes. The unique-T concurrence
inside-square conclusion is the one-circle part
of the full Lemma2.1 in29e; it is not extended
to a physical-two mask. All direct source pins
below were checked before freezing.

| Complete source | SHA256 | Exact use |
| --- | --- | --- |
| COMMON_HUB_FACE_ALL_TIP_MASKS_NEAR_ORIGIN_INJECTION.md | 6a388f0c506ca5733b78f42eb1e7f63469e908ca72d100cfe57cdd6362ce3dde | Whole true-U3/V2, arbitrary-W/T local mask/owner theorem; actual contained one-eighth disk and explicit support margins |
| SINGLE_HUB_BOUNDARY_ENDPOINTS_PARTIALLY_UNLOADED_PATH_POCKET.md | f0220431e78cf36c61d2594a5e2aa53aa9cf0d7a2ead4ebc92b0a72d3bd1c572 | Exact actual partially unloaded component, endpoint moments/properness, protected circle order, occupied crosscut assignment and literal L0134 entry |
| COMMON_HUB_FACE_W_OWNED_OPPOSITE_CIRCLE_NINE_ARC_EXCLUSION.md | ffddf725faa8b5b8475ad78bf7f903de10f964a9ae051b5a6dfda5edbf1a84f5 | Full Sections6--7 endpoint mask and gap arguments, rederived above at f022's actual endpoint hypotheses; no old all-boundary path arc-order step |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Entire Lemma2.1 at the real loaded T2 with its actual physical boundary neighbor, including unique-circle inside q and all two-circle exterior q |
| FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md | 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517 | Whole connected actual >40-degree arc at strict one-eighth clearance, with center point and all orientation endpoints |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Whole closed centered endpoint arcs of halfwidth pi/9, every actual boundary mask |
| SAME_FACE_SHARED_TRIANGLE_PARTIALLY_UNLOADED_POCKET_AND_ORIGIN_EXCLUSION.md | 29cc0e27f93f46d97d479213baaf0e6770de304cb567e68b77b920406663ba01 | Whole parallel/shared common-face L0134 feature, every original mean and completion allocation |
| PARTIALLY_UNLOADED_HUB_PATH_TIP_OWNED_CAPACITY_AND_D02_ZERO_AXIS_EXCLUSION.md | 47c524c9570c516d730721433a07427549e1a67a9e361e62e5b7e2579a018789 | Complete Sections11--12 actual central/channel/exterior partition and conditional central/occupied-channel proximity; no zero-axis U bound is used here |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original D02.L0134 graph, load mask, degrees and all three completion units |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Complete same-nine R>2 entry on the original unchanged configuration |

The separate complete prior independent records are:

| Complete review | SHA256 |
| --- | --- |
| REVIEW_COMMON_HUB_FACE_ALL_MASKS_INJECTION_ROOT_2026_10_28.md | 24fae6c7c677fe4a40796660642132e521b6e85fddecef21c022adfe4891c70e |
| REVIEW_RESTORED_COMMON_HUB_W_OWNED_OPPOSITE_CIRCLE_NINE_ARC_PENTAGON_2026_10_28.md | e6fb5f0d3b33a4af2468888f80d5d375ad616ea3ed52c9ded89849e84f292415 |
| REVIEW_SINGLE_HUB_PARTIALLY_UNLOADED_PATH_POCKET_HOUSE_2026_10_28.md | da39a1c2f92a616b914444f1518833869df5f7d137b00ada1a575c5333949708 |
| REVIEW_PARTIALLY_UNLOADED_TIP_CAPACITY_AND_ZERO_AXIS_L0134_ROOT_2026_10_28.md | 13d6185ac5c7bce376c902b7dbd3bfe2622aa608f1199c9d113eac29cce8dd23 |

The newly frozen29cc source has a separate complete independent
audit request. Its acceptance is not inferred from a historical
review. The present source also requires its own complete
independent review, including Section1's exact actual routing
and both original frame/allocation branches.

No frozen source or old review is changed. The proof uses hand
geometry and whole continuous-domain inequalities, with no pose
mesh, optimizer, numerical exclusion certificate, normal
reselection, moved mean, suppressed positive force, invented
boundary neighbor, Lean/Lake operation, build, CI/workflow,
metadata or ledger edit, original flag credit, commit or
remote write.
