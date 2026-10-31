# A sole triangle cannot have an outside fork in its bridge forest

Date: October 26, 2026.

**Status: accepted complete theorem after full-source root review in REVIEW_BRIDGE_MATCHING_TRIANGLE_FORESTS_ROOT_2026_10_26.md and separate review in REVIEW_TRIANGLE_FOREST_OUTSIDE_FORK_GLOBAL_2026_10_26.md.** The original nine physical squares and their common canonical
radius/Phi-minimizer pose are retained. No ledger or original gate is changed
by this source.

## 1. Exact theorem and common certificate

Work in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0),
    r=R-sqrt(2).

Use the common selected physical normal system and, among compatible
normalized planar stresses on this same pose, a stress with the fewest
positive original scalar atoms. This is the proved selection of
`GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`. Every surviving original
mean, circle mask, individual zero circle weight, and zero-stress physical
contact remains in force.

**Theorem.** Suppose a selected positive component has exactly one cyclic
block, a triangle, with arbitrary bridge forests attached at any of its
three vertices. Then no vertex outside that triangle has positive degree
at least three. Thus every attached tree is a union of simple pendant
paths from its actual triangle root. All degrees, forces, loads and all
nine physical bodies in this statement are the original ones in the
selected minimum-support stress.

The proof uses the already accepted theorem
`GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md`: a bridge forest all
attached to one triangle vertex is impossible at this common canonical
pose. It does not assume that theorem for multiple roots.

The articulation selection and the complete at-most-five-body exclusions
give the following exact facts:

* Every loaded all-bridge body is a genuine radial S/D leaf.
* Every outside nonleaf is genuinely unloaded and has only bridge edges.
* Every outside branching vertex has degree exactly three.
* At an unloaded articulation, three branch resultants cannot be collinear.

The last statement follows from the same branch scaling: their vectors
(f_j,a_j), with positive private circle masses a_j, lie in a space of
dimension at most two when the f_j are collinear. A nonnegative scaling
preserves all original force and moment equations and normalization while
removing a positive atom. This contradicts the chosen minimum support.

For every actual positive outward radial bridge application t e, t>0,
the actual neighbor lies in e dot x>=t. The sharp contained-unit support
bound gives

    t<=d.                                                   (1)

At d=1 equality forces that neighbor to be the unique physical radial
square

    S(e)={a e+b Je : 1<=a<=2, -1/2<=b<=1/2}.                 (2)

No circle-load or leaf equation is inferred for this neighbor from its
physical shape alone.

## 2. Deepest forks have two complete short terminal arms

Root the bridge trees at the triangle and suppose an outside branching
vertex exists. Choose one, H, farthest from the triangle. It has one parent
edge and exactly two child branches. Neither child branch has a branching
vertex, so each is a simple terminal arm ending at a genuine leaf, with
only true unloaded degree-two transmitters in between.

Each arm has length one or two. Here is the local argument, also proved in
`GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md`, Section 2. Every
unloaded all-bridge body meets D_delta, delta=max(R-2,0), and consequently

    |c_H|<19/24.

An arm of at least three edges has at least two intermediate transmitter
widths, each in {1,sqrt(2)}. In its actual leaf direction e its root
application is (r_L-W)e, with r_L in {r,d}, r_L<=d and W>=2. Thus

    c_H dot e <= d-2-1/2 < -89/60,

contradicting the center bound. No force has been removed before using a
transmitter equation.

The complete force-free two-arm geometry is already established in the
same source, Section 3, using the full original geometric sections of the
two-direct-leaf, mixed-arm and two-two-edge-arm theorems. It gives

    D_epsilon subset H,                                   (3)

with the origin strictly interior to H when d!=1. More precisely:

| Terminal arms | Exact geometric conclusion |
| --- | --- |
| Two direct leaves | For d<1, zero is interior. For d>1, the entire closed D_epsilon is in the open interior. At d=1, zero is interior or H has zero as a vertex and its two leaves are S in its two inward side directions. |
| Direct D plus length two | Necessarily d>1; the length-two arm is S of width one. In the arm frame H=[epsilon-1,epsilon] times [r-1,r]. Its only tangency to D_epsilon is epsilon e in the actual arm direction. |
| Direct S plus length two | Necessarily d>=1; the length-two arm is S of width one. If d>1, H=[epsilon-1,epsilon] times [2sqrt(epsilon)-1,2sqrt(epsilon)] after reflection. Again its only tangency to D_epsilon is epsilon e in the actual arm direction. At d=1 the original arm application is zero. |
| Two length-two arms | Necessarily d>=1; both are S of width one in orthogonal directions e_1,e_2, and H=[epsilon-1,epsilon]^2 in those directions. |

For the two mixed rows every other side distance is strictly greater than
epsilon. These are whole geometric classifications and do not use any
triangle equation at H.

The last row is in fact impossible at a genuine unloaded fork. The two
child forces are positive multiples of e_1 and e_2. Its parent force is
therefore strictly southwest. Its unique support point on H is

    P=-(1-epsilon)(e_1+e_2).

Radiality makes the parent application exactly P, so its positive support
radius is sqrt(2)(1-epsilon). But epsilon<1/60, d<61/60, and

    59sqrt(2)/60 > 61/60,

as 2*59^2>61^2. This contradicts (1), including epsilon=0. Hence a deepest
fork has either two direct leaves or a direct leaf and one length-two arm.

## 3. Every outside fork is impossible when d differs from one

First assume d<1. Only the two-direct-leaf row can occur and zero is
interior to H. Every genuine leaf root contains zero: a D leaf makes zero
interior, while an S leaf has radial support d e and its whole unit inward
segment contains zero. A third genuine leaf would have a root K distinct
from H, because H's two child arms already use two edges and its parent
leads to the triangle. Such a K would contain zero, impossible because H
contains it in its open interior.

Now assume d>1. If H has two direct leaves, D_epsilon is strictly inside
H. Every genuine leaf root K meets D_epsilon: a D root contains zero, and
an S root contains the point epsilon e at the inner end of the unit inward
segment from its actual support d e. No third genuine leaf root distinct
from H can therefore occur.

In either mixed-arm row, zero is interior to H and

    boundary(H) intersect D_epsilon = {epsilon e},          (4)

where e is the direction of the existing length-two S arm. A third D leaf
would have a root containing zero and is impossible. If a third S leaf has
direction f and root K, its point epsilon f belongs to K. Since K and H
have disjoint interiors, that point cannot lie in the open interior of H.
Equations (3)--(4) force epsilon f=epsilon e, hence f=e. The new physical S
leaf would be the already present S leaf in that arm, impossible for a
distinct genuine leaf.

Thus the entire component has only the two genuine leaves at the ends of
H's child arms. Any bridge tree attached at a different triangle vertex
would contain another genuine leaf. Consequently every bridge tree is
attached to the same triangle vertex as H. The complete one-root triangle
forest theorem excludes this case.

This proves the present theorem for all d!=1. The argument retains all
outside graph loads: it establishes a physical uniqueness of genuine
leaves, rather than removing a third force from H.

## 4. Exact physical tools at the critical radius

For the rest let d=1, so R^2=17/4. Two independent local consequences will
be used without a whole-tree premise.

First, every outside nonleaf contains zero. The complete uniform theorem
`GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md` proves this at d<=1:
an unloaded all-bridge body avoiding zero would require an outward bridge,
whose application has 1<t<=d, impossible. Every genuine leaf root also
contains zero, by its original S/D radial geometry.

Second, the following completion facts are purely physical.

1. Three unit squares with zero as a vertex cannot occur in a nine-square
   packing at R^2=17/4. This is the complete theorem
   `THREE_VERTEX_ORIGIN_CAPACITY.md`; it imposes no stress or graph premise.
2. The nonaligned five-square Y skeleton of `Y_ALL_COMPLETION.md` cannot be
   completed to nine. Its two central squares are a vertex-origin unit
   [0,1]u+[0,1]v and a side-origin unit in the opposite half-plane, aligned
   to a direction e with e dot u<0 and e dot v<0. Its three actual outer
   units are S(u), S(v), S(e). The side-origin contact must be a relative
   side interior and the two displayed strict signs give the full open
   angle range of that physical theorem. No terminal's positive graph
   degree is a premise of the capacity statement.
3. Two vertex-origin squares meeting only at zero, together with the four
   distinct physical S units in their four side directions, have capacity
   at most eight. This is the physical content of Sections 3--4 of
   `TREE02_POINT_CONTACT_COMPLETION.md`, after the four terminals have
   actually been supplied. It does not require those terminals to be graph
   leaves. To recall the complete capacity: the two complementary cone
   gaps have lengths g,h>0 with g+h=pi. The four terminals screen all gap
   boundary rays. Assume g<=h. Nonoverlap of the gap terminals gives
   g>=2 arctan(1/2), hence h<=2 arctan(2). If g<pi/2, its screened pocket
   is empty and the other holds at most two units. If g=pi/2, each right
   angle holds at most one. Thus the six actual core units leave room for
   at most two more. These are the full physical pocket theorems of
   `RADIAL_SECTOR_POCKET_CAPACITY.md`.

In every use below, the relevant physical terminals are proved to be the
original actual bodies before these completion theorems are invoked.

## 5. A direct S leaf and a length-two arm give a physical Y

At d=1 the mixed-D row is impossible. In the mixed-S row let the actual
direct leaf be S(u), and let e be the direction of the original length-two
arm. Its intermediate U is an actual width-one side transmitter, with
applications zero and e, and its terminal is the physical S(e). Its force
on H points along e with positive magnitude. The other positive force is
the unchanged parent force.

Because zero is an actual support application on H, it lies on its
boundary. If it lies in a relative side interior, H's only outward radial
support of norm one is the opposite side foot. Thus u=-e. The parent force
is collinear as well, contradicting the three-branch minimum-support rule.

Otherwise write H=[0,1]u+[0,1]v, with u the direct leaf direction.
The arm force at zero satisfies e dot u<=0 and e dot v<=0. If e dot v=0,
then e=-u and again all three original forces are collinear. Hence
e dot v<0. Write their exact equilibrium as

    alpha u + beta e + gamma n = 0,
    alpha,beta,gamma>0,                                  (5)

where n is the original parent normal outward from H. Then n dot v>0.
The parent application is radial. A normal with negative u component
would expose v, which is radial only for n=v. A normal with two positive
components exposes u+v, whose norm sqrt(2)>1 contradicts (1). Thus the
only possibility is n=v, with parent application v. Sharp support equality
forces the parent body to be the actual physical S(v). Equation (5) also
gives e dot u<0.

The contact H--U at zero strictly exposes H's vertex because both own
components of e are negative. If zero were a vertex of U, this would be a
point-only vertex/vertex contact whose normal is a side axis of U,
contrary to the retained strict point-normal convention. A shared side is
impossible because H's support face in direction e is just its vertex.
Therefore zero is in the relative interior of U's near side.

The five actual bodies

    H, U, S(u), S(v), S(e)

are precisely the full physical nonaligned Y skeleton. Its parent S(v)
may have further positive neighbors; the capacity theorem does not care.
All five are distinct: they occupy the original distinct fork/arm bodies,
and e has negative projections on both orthogonal directions u,v.
The Y completion theorem excludes the same nine-square packing.

Thus no deepest mixed-arm fork occurs at the critical radius.

## 6. A two-direct-leaf fork leaves at most two origin-containing bodies

The only remaining deepest fork has two direct leaves. If zero is interior
to H, every other genuine leaf root is impossible, exactly as in Section 3.
All bridge trees are then attached at one triangle root and the one-root
theorem excludes them.

Otherwise the complete two-leaf classification gives

    H=[0,1]u+[0,1]v,

with the two actual leaves S(u) and S(v). The true unloaded equation of H
makes its parent normal a strictly negative combination of u and v. Its
unique support application is therefore zero. Let K be this actual parent
body; K contains zero.

**Origin-isolation claim.** No third physical square contains zero in the
same nine-square packing.

If zero is in a relative side interior of K, its tangent cone is the
half-plane opposite H through the parent separator. Since the parent
normal has two strictly negative own components on H, the two angular gaps
between H's right-angle cone and K's half-plane cone are each strictly less
than pi/2. Any further square containing zero would have a tangent cone of
angle at least pi/2. It cannot fit in either gap.

If zero is a vertex of K, H and K meet only there: H's supporting face for
the parent normal is the singleton zero. Their two complementary angular
gaps are therefore both positive and sum to pi. Each is strictly less
than pi. A third square containing zero cannot have zero in a side interior
or its interior, because that would require a cone of angle at least pi.
It would have zero as a vertex. The physical three-vertex capacity theorem
then excludes the nine-square packing.

Zero cannot be interior to K, because H contains it. These alternatives
prove the origin-isolation claim, including every zero-weight physical
contact and extra square.

If K is already a triangle vertex, every bridge tree attached to a different
triangle vertex would end at a genuine leaf whose root is distinct from
both H and K. That root would contain zero, contrary to the claim. A bridge
tree rooted at another triangle vertex cannot pass through H or K: doing
so would either return to the same cyclic block or merge the two rooted
trees, giving an additional cycle. Thus all bridge trees are attached to
K, and the complete one-root theorem excludes the component.

It remains that K is an outside body. It is genuinely unloaded and
all-bridge. Along its path to the triangle there cannot be another outside
nonleaf, since every such body contains zero. Therefore K is adjacent
directly to a triangle vertex A. Its positive degree is two or three.

## 7. Both possible degrees of the outside parent are excluded

### 7.1. The outside parent has degree two

K is then its original unloaded degree-two transmitter. Its H application
is zero. The opposite application has radial distance equal to its actual
width, either one or sqrt(2). Equation (1) excludes sqrt(2), so its width
is one and the other application is e, where e is the strict opposite
direction to H's inward quadrant. Sharp support equality makes A the
physical S(e).

As in Section 5, zero cannot be a vertex of K: its side-axis transmitter
normal would be a non-strict separator at a point-only vertex/vertex
contact, while H has a unique vertex support. Thus zero is in K's relative
side interior. The five original bodies H,K,S(u),S(v),A=S(e) form the
physical nonaligned Y skeleton. Its completion theorem excludes all nine.

### 7.2. The outside parent has degree three

The third branch of K must be a direct genuine leaf L. Otherwise it would
contain another outside unloaded nonleaf, contradicting origin isolation;
it cannot return to the triangle through another vertex because the edges
are bridges. Since zero lies on K's boundary, L cannot be D and is S.

If zero is in a relative side interior of K, the S leaf uses the sole
norm-one radial support on the opposite side. Its force and the force from
H at zero are opposite parallel. The unchanged third force is parallel too,
contradicting the three-branch minimum-support rule.

Otherwise K=[0,1]w+[0,1]z with its genuine S leaf S(w). The H--K contact is
point-only, so its actual normal n_H outward from K strictly exposes zero
on K; both n_H dot w and n_H dot z are negative. The full K equation is

    alpha w + beta n_H + gamma n_A=0,
    alpha,beta,gamma>0.                                  (6)

Thus n_A dot z>0. The same radial-support cover used in Section 5 forces
n_A=z: a negative w component would give a nonradial support at z, and two
positive components would expose w+z at radius sqrt(2)>1. The actual parent
application is z and sharp support equality makes A the physical S(z).

Now H and K are the two original vertex-origin units meeting only at zero.
Their four side rays are distinct. The four actual physical terminal units
in those directions are

    S(u), S(v), S(w), A=S(z).

They and H,K satisfy precisely the six-square physical two-gap capacity
statement of Section 4. It allows every other original square and does not
require A to have degree one. At most two further units fit, whereas the
same packing has three other squares. This is a contradiction.

Both possible degrees of K have now been excluded. This completes the
critical-radius fork argument.

## 8. Whole-forest conclusion and remaining task

Every finite bridge forest with an outside branch point has a deepest
fork. Section 2 gives its complete original arm cover. Section 3 excludes
all noncritical radii, and Sections 4--7 exclude the full d=1 geometry.
The stated theorem follows: outside the sole triangle, every nonleaf has
positive degree two and every attached branch is a genuine simple pendant
path.

The graph may still have pendant paths attached at two or three distinct
triangle vertices. The theorem does not remove a path, combine equations
from different stresses, or close C1.3.b4, C1.3.b5 or C1.3.b6 on its own.
Those finite remaining path families require their complete original
equations or a uniform geometric exclusion.

The only new stress selection is the proved minimum-support choice on the
unchanged canonical pose. Every physical completion theorem used above is
applied to actual original squares, including a cyclic body only after its
full radial S geometry has been proved by sharp support equality. No
numerical sampling, Lean compilation, CI or remote action is used.
