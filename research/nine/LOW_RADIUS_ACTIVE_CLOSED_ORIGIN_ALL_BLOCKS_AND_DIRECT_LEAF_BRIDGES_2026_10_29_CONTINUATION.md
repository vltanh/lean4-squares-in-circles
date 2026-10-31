# At low radius every cyclic block contains every active origin unit, and every bridge is a direct leaf

Date: October 29, 2026 UTC. Author: pentagon/global continuation.

**Status: complete proposed hand theorems, frozen for separate full independent
review.** The complete zero-moment residual in the reviewed active-central-unit
restriction is excluded below. The argument uses every original force at its
actual degree. Its new full-star classification retains all physical circle
masks, individual zero coefficients and original shared means.

The main conclusion is that an active unit containing the circle center even
on its boundary belongs to every cyclic block of its positive component. A
further consequence excludes every nontrivial attached bridge tree throughout
the entire low and critical radius range: in a component containing a cycle,
every positive bridge is a direct genuine leaf attached to a vertex common to
all its cyclic blocks. With one cyclic block, different leaves may have
different actual roots in that block. No high-radius or whole original
fine/coarse closure is claimed.

## 1. Exact original data and statements

Retain all nine actual closed unit squares, with pairwise disjoint open
interiors, in the unchanged origin-centered disk, with

    79/40<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1, 0<d<=1.

Use one common compatible selected physical certificate with its original
normal, positive magnitude and actual application for every positive pair.
Positive shared sides retain their entire original mean, including either
endpoint. Every physical circle corner and individual zero coefficient remains.
All unstressed squares and all zero-weight physical contacts remain as actual
packing obstacles.

The selected certificate includes the compatible nonradial avoidance at every
nonzero isolated vertex/vertex contact: its original normal is strictly in both
actual normal cones and is not parallel to that contact point. This is the
pre-extraction selection in PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section 2,
preserved by its uncrossing and thinning. It is not a new choice made during
this proof. The theorem does not purport to hold for an arbitrary unselected
stress with radial vertex/vertex point normals.

Let G be a connected component of the original simple positive body-pair
graph. A cyclic block means a maximal biconnected block with at least three
vertices. A genuine leaf has exactly one original positive pair neighbor.
Here an active unit is incident to at least one original positive pair edge.
Isolated physical completion squares are not assigned a positive path or a
force equation from another component.

For an oriented original edge i--j, write its original application p_ij,
normal n_ij from i to j and magnitude mu_ij>0. Its origin moment is

    M_ij=mu_ij*det(p_ij,n_ij), M_ji=-M_ij.

All full original equations are retained:

    F_i+sum_j mu_ij*n_ij=0,
    sum_j M_ij=0,
    F_i=2*sum_z lambda_(i,z)*z, lambda_(i,z)>=0.

Each circle atom is radial and has zero origin moment. Statements involving
subgraphs below are identities or ordinary graph consequences of these full
equations, not shortened substitute certificates.

**Theorem A: closed-origin block theorem.** If E is an active unit of G and
O belongs to the actual closed E, every cyclic block of G contains E.

**Theorem B: complete low-radius bridge forest.** If G contains any cyclic
block, every original positive bridge joins a genuine leaf to an actual unit
containing O. That nonleaf endpoint belongs to every cyclic block of G. Thus
every such bridge is directly attached to every cyclic block; there is no
outside bridge path with at least two edges and no outside branching bridge
tree. This statement does not require any private degree or load assignment
inside the cyclic blocks.

Theorem A is proved in Sections 2--7. Theorem B follows in Section 8. Both
include the closed critical radius R=sqrt(17)/2.

## 2. Two complete retained inputs and their exact scope

### 2.1. Sharp minimum support of an actual contained unit

For any actual unit with center c and own orthonormal axes u,v, its largest
corner squared norm is

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Containment gives |c|<=d+1/2. Its width in any unit direction f is
|f.u|+|f.v|>=1. Consequently

    min_(z in U) f.z <= |c|-1/2 <= d <= 1.          (1)

This includes every actual frame and support mean, with no stress, boundary
or degree hypothesis at U. It is the complete force-free Section 1 input in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, rederived here at the exact scope
used below. In particular a unit beyond a support height t has t<=d.

Also every unit containing O is physically circle-clear. Its points are at
distance at most its diameter sqrt(2) from O, while R>=79/40>sqrt(2).
All its original circle coefficients are therefore zero.

### 2.2. The complete reviewed low-radius block restriction

Use Section 4 of the complete source
ACTIVE_CENTRAL_UNIT_ALL_BLOCKS_AND_BRANCH_MASS_WITHOUT_LEAF_2026_10_29.md,
SHA256 4a402273a45a7780effc38b622ed88a6dd68ac1c80755a415a1491e7139f390b,
with its complete independent review8097a34f.

Its exact statement is:

> If an active E contains O closedly and a maximal cyclic block Q of the same
> positive component omits E, every original Q edge has zero origin moment.
> No Q edge has two origin-free actual endpoint squares. Equivalently, the
> origin-containing vertices of Q form a vertex cover of its actual edges.

There is no leaf, private-degree or circle-load premise at E. Its proof uses
the entire deletion-branch circle mass to obtain an actual path to a loaded
boundary unit, the complete low-radius port/cycle theorem including origin
vertices and side-interior origins, and the one common selected embedding.
Both its actual center/port strands and equality-neighbor restrictions are
retained. No positive force on a zero-moment edge is removed.

This input proved a restriction and explicitly left its all-zero-moment
residual open. The remaining sections exclude that complete residual. The
input's stronger central-disk-interior bridge conclusion is not assumed at a
mere boundary-origin E.

## 3. Complete physical origin-unit cover for all nine squares

### 3.1. Three origin vertices are impossible, including below the critical radius

The complete force-free theorem THREE_VERTEX_ORIGIN_CAPACITY.md says that
three actual unit squares having O as a vertex inside the critical disk allow
at most eight total squares. Its proof has no stress, common-frame, graph or
private-degree premise. For clarity, the full capacity mechanism is recorded
here, including its closed endpoints.

At the critical radius every center has norm at most 3/2 by (1), and distinct
centers have distance at least one by their disjoint open inscribed disks of
radius 1/2. For a vertex-origin U=[0,1]^2, any other center in its closed
first quadrant must be (3/2,0) or (0,3/2). Indeed its distance from U must be
at least 1/2. If both coordinates are at most one the distance is zero. If
only one exceeds one, distance>=1/2 and the center radius force the stated
endpoint. If both exceed one, the squared distance to U is

    x^2+y^2+2-2(x+y)<9/4+2-4=1/4,

a contradiction. Thus the three disjoint open right-angle tangent sectors
at O leave all additional center directions in three closed angular gaps of
total length pi/2. A zero-length gap permits at most one center, the unique
radius-3/2 point on its ray. Different gaps have disjoint endpoints, since
a positive-width origin quadrant separates them.

The three central centers have radius a=1/sqrt(2). Successive bisector gaps
are pi/2+g_i<=pi, so any direction has nonnegative dot product with at least
one central center. An additional center of norm below a would then be at
distance strictly below one from that central center. Hence every additional
center has radius in [1/sqrt(2),3/2].

Two such centers at angular distance at most pi/6 have squared distance at
most r^2+s^2-sqrt(3)*r*s. Separate convexity in r,s puts its maximum at a
corner of the closed radius rectangle. The three values are

    1-sqrt(3)/2,
    (9/2)*(1-sqrt(3)/2),
    (11-3*sqrt(6))/4,

all strictly below one. The last two comparisons follow from sqrt(3)>14/9
and 3*sqrt(6)>7. Thus consecutive additional centers within any one gap have
angular distance strictly greater than pi/6. If at least six additional
centers occupied k<=3 gaps, summing their within-gap consecutive differences
would give

    pi/2 > (6-k)*pi/6 >= pi/2,

a contradiction. There are at most five additional squares, and at most
eight total. Every comparison includes the actual closed center and gap
endpoints; no orientation sampling is involved.

For any smaller radius in the current domain, the same unchanged nine
squares lie in the critical disk. The force-free capacity theorem therefore
still excludes three origin vertices. No force certificate is transferred to
a larger-radius minimization problem in this argument.

### 3.2. All possible triples through O

At O a vertex contributes tangent angle pi/2, a relative side-interior point
angle pi, and an interior point angle2pi. Open tangent sectors of different
actual squares are disjoint. A unit containing O openly excludes every other
closed origin-containing unit, by interior approximation.

There are at most four origin-containing units by the angle sum. Four would
all have origin vertices, contradicting Section 3.1. Hence there are at most
three. If exactly three occur, they cannot all have origin vertices, and two
side-interior origins would exceed the total angular budget. They consist of
exactly one side-interior origin and two vertex origins. Their angles sum to
the full turn; their sectors therefore tile it with no gap.

An origin-preserving common rotation/reflection puts their entire actual
frames in the following form:

    S_0=[0,1] times [-a,b], a,b>0, a+b=1,
    V_+=[-1,0] times [0,1],
    V_-=[-1,0] times [-1,0].                        (2)

The common axes are forced by the side-interior half-plane and the two
right-angle sectors tiling its complementary half-plane. They are not imposed
on any other actual square. All three units are physically circle-clear.

## 4. A block omitting E forces every moment of the entire component to vanish

Suppose, toward Theorem A, that a maximal cyclic block Q omits the given
active E containing O. The complete restriction in Section 2.2 makes every
Q edge moment zero and the origin-containing Q vertices a vertex cover.

There must be at least two origin-containing vertices in Q. If there were
none, Q would have no edge. If there were only one, every other Q vertex would
have at most that one Q neighbor, contrary to the minimum degree of a cyclic
biconnected block. A simple cyclic block has at least three vertices.

Together with the distinct E outside Q, Section 3 permits exactly three
origin-containing actual units globally. Q contains two of them, E is the
third, and all are active in G. Their actual geometry is exactly (2). Every
other actual unit, including every other vertex of G, avoids O closedly.

Let Q' be any other maximal cyclic block of G. Distinct maximal biconnected
blocks meet in at most one vertex. Q' therefore omits at least one of Q's two
active origin-containing units. Apply the complete same low-radius restriction
with that omitted actual unit as E'. It makes every Q' edge moment zero.
This is a literal same-component application; E' is not an unstressed extra.

For each original positive bridge, sum the complete origin-torque equations
on one whole cut component. Internal moments cancel at their same original
application and every radial circle moment is zero. Its bridge moment is
therefore zero. Every edge of a finite simple graph belongs to a maximal
cyclic block or is a bridge. Consequently

    every original positive edge of G has zero origin moment.   (3)

No edge or original force was deleted to establish (3). It now applies to the
entire actual star of every G vertex, including all branches outside Q.

## 5. Complete classification of an origin-free full zero-moment star

The following local proposition is useful beyond the present block argument.

**Full-star proposition.** In the current low-radius window and common selected
certificate, let U be an origin-free active unit whose every original positive
pair edge has zero origin moment. If at least two distinct actual squares of
the packing contain O, then U is an actual radial side unit

    S(f)=[d,d+1]f+[-1/2,1/2]Jf,

for a unit vector f. All its original positive applications are its actual
nearest point d*f, all its outward pair normals are -f, and its complete
circle load uses both physical outer corners with equal positive weights.
There is no bound on U's actual positive degree.

### 5.1. Every actual contact is inward radial at the same nearest point

For a zero-moment edge at U, its actual application p is not O. Suppose first
its outward U normal is n and p=t*n, t>0, so U is the inner unit. Choose an
own coordinate interval of U missing zero and reflect it to [h,h+1], h>0.
The positive coordinate of p=t*n makes that component of n positive. Since
p maximizes n on U, its corresponding coordinate is h+1>1. Thus |p|=t>1.
But the actual neighbor beyond that contact has minimum n support t, so (1)
gives t<=d<=1. This is impossible. It includes any original shared mean.

The edge must therefore be inward radial at U. Write p=t*f, t>0, with outward
U normal -f. U lies in f.z>=t and contains p. For every z in U,

    |z|>=f.z>=t=|p|,

and equality forces z=t*f=p. Thus p is the unique nearest point of U to O.
Every original positive edge at U has this same application p_U and the same
outward normal -f, where f=p_U/|p_U|. The full original force equation gives

    F_U=sigma*f, sigma=sum_(all original neighbors) mu>0.         (4)

U has positive circle load and physically touches the circle. This follows
from its whole star; it does not make U a genuine leaf or remove any neighbor.

### 5.2. The entire physical unique-corner mask

Reflect and reorder the actual own coordinates so that

    U=[A-1,A] times [B-1,B], A>=B>=1/2.

The farthest-corner rule shows that a unique physical circle corner occurs
when both own center coordinates are positive. In that case A,B>1/2,
the actual circle corner is z=(A,B), and A^2+B^2=R^2. Its positive full
circle resultant is parallel to z. Because R>sqrt(2), A>1.

If B<=1, the actual nearest point of U is (A-1,0), whose radial direction
cannot be parallel to z with B>0. Hence B>1. The nearest point is then
(A-1,B-1), and (4) requires

    det((A-1,B-1),(A,B))=A-B=0.

Therefore A=B. The actual unit is radial diagonal, with nearest point

    p_U=r*f, r=R-sqrt(2), 0<r<1.                   (5)

Its nearest point is a strictly exposed vertex in direction -f. At any one
of its original positive contacts, the intersection is therefore physically
the singleton {p_U}. It cannot also be a vertex of the other square: its
actual normal is radial at the nonzero p_U, forbidden by the retained
pre-extraction nonradial isolated-point selection.

The other actual unit must have p_U in a relative side interior and own
the normal f. Its complete own-frame chart is

    [r-1,r]f+[t-1,t]Jf, 0<t<1.

Since 0<r<1, this square contains O openly. There are at least two distinct
actual origin-containing squares by the proposition's hypothesis, so at
least one of them is a different square. Its closed occurrence at O would
overlap that open-origin square. This contradiction excludes the entire
unique physical circle mask, at every actual degree of U.

### 5.3. Every physical tie and zero circle coefficient

A contained unit has more than one farthest corner only when one or both own
center coordinates vanish. Both zero would give farthest radius1/sqrt(2),
incompatible with the current R. Thus the remaining complete physical mask
has exactly two adjacent outer corners and one own center coordinate zero.
After reflecting its positive radial axis, its actual geometry is

    U=[d,d+1]f+[-1/2,1/2]Jf,
    p_U=d*f,
    z_+=(d+1)f+(1/2)Jf,
    z_-=(d+1)f-(1/2)Jf.

Here d>0 and the circle equation is R^2=(d+1)^2+1/4. The full original
resultant is 2*lambda_+*z_++2*lambda_-*z_-. Its parallelism to p_U in (4)
forces lambda_+=lambda_-. Positive total load makes both positive. In
particular an attempted zero coefficient at just one physical outer corner
is excluded by the original full equation, not silently dropped as a mask.

These cases exhaust every physical circle mask. No selected corner or
single-corner torque ratio has been imposed on a physical tie. This proves
the full-star proposition.

In the assumed Q counterexample, (3) and the three actual origin units in (2)
supply every premise. Thus every origin-free active unit of G is one actual
radial S(f), with the full conclusions above and its actual degree unchanged.

## 6. Every zero-moment cyclic block in the three-unit tiling has one possible shape

Q has exactly two origin-containing vertices. Its other vertices are
independent by the retained vertex-cover conclusion. Each of them has at
least two neighbors inside Q, so it is adjacent to both of those origin
vertices. At least one such other vertex exists because Q is cyclic and
simple. Every one is an actual radial S(f) by Section 5.

At any positive contact from an origin-containing H to S(f), Section 5 gives
the original point d*f and normal f. Thus

    d*f belongs to H and maximizes f on H.          (6)

For V_+=[-1,0] times [0,1], (6) requires f_x<=0 and f_y>=0. If both signs are
strict, the maximum is the actual corner(-1,1), so d=|d*f|=sqrt(2)>1,
impossible. If f_x<0,f_y=0, then f is West and its maximizing point is(-1,0),
so d=1. If f_x=0,f_y>0, then f is North and d=1. These are the entire
unit-direction possibilities. The reflected argument applies to V_-.

Q's two origin units include at least one of V_+,V_-, since there is only
one side-origin S_0. A non-origin Q neighbor touching it therefore forces

    d=1, R=sqrt(17)/2.                              (7)

This already excludes the entire strict-low-radius residual.

At the critical endpoint, the complete possible radial S neighbor lists are

| Actual origin unit | Every possible positive radial S neighbor |
| --- | --- |
| V_+ | S(West), S(North) |
| V_- | S(West), S(South) |
| S_0 | S(East) |

For the last row, (6) has d=1. If f_x<0 the point f is not in S_0. If f_x=0,
the support in either vertical axis is a or b, strictly below one. If f_x>0
and f_y!=0, the unique support corner is(1,b) or(1,-a), whose norm is
strictly greater than one. Only f=East remains. These arguments retain both
vertical interval endpoints and every possible shared contact mean.

A fixed direction f specifies one entire actual square S(f); two distinct
original squares cannot occupy that same unit because their open interiors
would coincide. If the two origin vertices of Q included S_0, the table would
leave no common radial S neighbor, contradicting the required other vertex.

Consequently Q's origin vertices are V_+,V_-, and the omitted E is S_0.
Their sole possible common radial S neighbor is

    W=S(West)=[-2,-1] times [-1/2,1/2].

There can be only one such actual W. Therefore Q has exactly the three
vertices V_+,V_-,W and, as a cyclic simple block, all three triangle edges.
All their positive magnitudes and original zero-moment means remain.

## 7. Full horizontal balance contradicts the block's maximality

Every positive edge of G has zero moment by (3), and all origin-free G
vertices have the radial S form. The complete possible active neighbors of
V_+ are therefore the other two origin units S_0,V_- and the two units
S(West)=W,S(North) from the table. A listed physical unit need not be present
or carry a positive edge unless subsequently forced by the full equation.

V_+ is physically circle-clear. Its mandatory Q edge to W has normal West
and strictly positive magnitude. A possible edge to V_- has normal South,
because their actual physical intersection is the positive horizontal
segment[-1,0] times {0}. A possible edge to S(North) has normal North.
Their horizontal components vanish. The only possible positive horizontal
component is the normal East to S_0, whose actual intersection with V_+ is
the positive vertical segment{0} times [0,b].

Its full original horizontal force balance therefore reads

    -mu_(V_+,W)+mu_(V_+,S_0)=0,

where a nonexistent second edge would contribute zero. The first magnitude
is strictly positive, so the actual S_0--V_+ edge must be positive. This is
an inference from the entire original star, not an imposed extra contact.

The reflected complete star at V_- similarly has the mandatory West force
to W, only vertical possible forces to V_+ and S(South), and its only East
possibility to S_0. Thus the actual S_0--V_- edge is positive as well.

Both original shared means in these forced side contacts remain. Condition
(3) would fix their transverse mean to zero, an allowed common endpoint;
the horizontal argument has not assumed a nonzero or interior mean. The
original V_+--V_- mean and both W means are likewise retained at their
possible zero-moment endpoints. No extra strict moment sign is inserted.

S_0 lies outside Q but is joined positively to two distinct vertices of Q.
Adding this two-edge ear to the biconnected triangle enlarges its biconnected
block. Equivalently, the connected component outside Q containing S_0 has
two Q attachments, impossible for a maximal block. This contradicts the
choice of Q and completes Theorem A.

Every origin-interior, origin-side and origin-vertex alternative and the
entire zero-moment residual has now been covered. The argument never removes
the origin unit E, a zero-moment edge, an individual physical circle corner
or any of the nine physical squares.

## 8. Every bridge in a cyclic component is a direct genuine leaf

Assume G contains a cyclic block Q, and let i--j be any actual positive
bridge. The complete cut-side torque sum gives its original moment zero,
as in Section 4.

If its application were O, both endpoint units would contain O. Theorem A
would put both into Q. A bridge cannot join two vertices of a cyclic
biconnected block, which supplies an alternate path. Thus its application
is nonzero.

Orient the unchanged bridge as p=t*f, t>0, with inner endpoint H maximizing
f and outer endpoint L minimizing f. The actual support cap (1) gives
t<=d<=1. For every unit maximizing f at p, the entire inward segment

    p-s*f, 0<=s<=1,

lies in that same actual unit. In its own coordinates, each nonzero f
component starts at the corresponding support endpoint and moves inward by
at most one; a zero component does not move. This proves the assertion at a
vertex, side-interior point and every original shared mean. Taking s=t
shows O belongs to H. Conversely L lies in f.z>=t>0 and avoids O.

Theorem A places H into every cyclic block of G. The origin-free outer
endpoint L cannot belong to a cyclic block Q': that block would also contain
H and provide a path from H to L avoiding the bridge. Thus L has no incident
edge belonging to a cyclic block.

Suppose L had another incident edge. It must be another bridge. The same
radial argument makes at least one of its endpoints origin-containing. L
is origin-free, so its other endpoint K contains O and hence belongs to Q.
The first H also belongs to Q. K cannot equal H in the simple positive graph
because that would repeat the same edge. A path within Q from H to K,
together with H--L--K, contradicts the claim that H--L is a bridge.

L therefore has exactly one original positive neighbor: it is a genuine
leaf. Its actual full one-force equation forces positive circle load, since
a nonzero positive pair force cannot balance a zero circle resultant. Its
physical presence and every other zero-weight contact remain.

This proves Theorem B, including zero application, all shared-mean endpoints,
arbitrary originally possible outer degree, every circle mask and the closed
critical radius. A single cyclic block may have direct leaves at different
origin-containing vertices. If two distinct cyclic blocks exist, their common
vertices number at most one, so every such leaf root is their same vertex.
No assertion is made about bridges in a component with no cyclic block.

## 9. Whole-family consequences and precise limits

Theorems A and B are independent of cyclic-block size, chord pattern, load
pattern, actual private degrees and every extra positive branch. In particular,
whenever a connected positive component contains any cycle, its entire
low/critical domain cannot have a bridge tree extending two or more edges
from a cyclic block. Every outside positive vertex incident to a bridge is
already a genuine direct leaf.

For a one-block component this excludes, simultaneously and at every root
assignment, every arm of length at least two, every arm-plus-leaf forest
(same or distinct block roots), two short arms, and every outside fork. No
outside vertex is made unloaded or degree two in order to invoke the theorem.
In the original C1.5.b3 and C1.6.b3 domains it removes every low/critical
three-bridge forest except the forest of three direct leaves on the actual
cyclic block. In particular the entire critical same-root short-arm plus
direct-leaf domain is excluded, with all nine actual units retained.

This is a whole radius-and-forest conclusion. It does not remove the remaining
high-radius versions of those original rows, does not classify all private
forces within a surviving block, and does not declare the remaining direct-
leaf forests or a global packing impossible. Root assignments of the surviving
direct leaves must still satisfy their own original physical theorems.

For Theorem A the actual E must be a vertex of the same positive component.
An isolated completion square containing O is not silently given the branch
mass or positive boundary path used by the input. The complete graph and all
outside physical squares remain unchanged.

## 10. Exact inputs, full reading and independent-review boundary

All complete direct records below have been read at the stated exact pins.
The actual support bound, full three-origin-vertex capacity mechanism and
radial bridge argument have also been reproduced above. The only imported
structural conclusion is the complete Section 4 low-radius restriction of
4a402273, at its actual same-component and closed-origin scope.

| Complete source or review | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Every original full force/torque equation, actual support, original shared mean and complete physical mask |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Already common compatible strict/nonradial point selection, preserved through uncrossing/thinning; the selected embedding retained in the imported block theorem |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Only the entire force-free contained-unit minimum-support bound of Section 1, rederived here; no loaded-tip theorem |
| THREE_VERTEX_ORIGIN_CAPACITY.md | 1388d83f7ecfa70ac7c86585fd6412f3187fa5e65cb4c3116411c8452ad0293d | Complete critical physical capacity for all actual units and all remaining frames, with the unchanged-packing lower-radius inclusion |
| ACTIVE_CENTRAL_UNIT_ALL_BLOCKS_AND_BRANCH_MASS_WITHOUT_LEAF_2026_10_29.md | 4a402273a45a7780effc38b622ed88a6dd68ac1c80755a415a1491e7139f390b | Complete Section 4 zero-moment and origin-vertex-cover restriction for a block omitting any active closed-origin unit |
| REVIEW_ACTIVE_CENTRAL_UNIT_ALL_BLOCKS_NO_LEAF_PENTAGON_GLOBAL_2026_10_29_CONTINUATION.md | 8097a34f24ea63ec51a1c837a77a93881d972e75ac71154d7299c3536fe2adc2 | Complete independent review of root's preceding source, retaining the disclosed author boundary of its cycle input |
| REVIEW_LOW_RADIUS_CLOSED_ORIGIN_CYCLES_DOUBLE_LEAF_FORK_ROOT_2026_10_29.md | bef4bf9c79d022bfded764a768475751fdf8abeed1e5ee8b69915d1849ca2dc2 | Retained separate full independent review of my earlier boundary-origin cycle theorem and the exact three-origin capacity input |

I authored the earlier boundary-origin cycle input867a7a and independently
reviewed root's later active-unit source4a402273 at8097a34f. Those records
remain unchanged. Root's separate complete bef4 review of the earlier cycle
theorem remains its independent check. The present new work is the exhaustive
zero-moment full-star/mask classification, the whole-component propagation,
the exact three-unit block contradiction, and the resulting complete bridge
forest theorem. It requires its own genuinely separate full independent review;
neither my earlier review nor an authored-input reread substitutes for that.

The prior proof-route checkpoint82791eea remains unchanged as a historical
unadopted checkpoint. This complete new manuscript proves its missing joins
and additionally supplies Section 8's broader bridge conclusion. No old source,
review, pin, graph, original flag, ledger or metadata is rewritten.

No pose enumeration, numerical optimization, angle mesh, new computational
packing certificate, changed normal, moved mean, deleted force or physical
square, Lean/Lake execution, build, CI/workflow, commit, remote mutation or
merge was used. No original fine/coarse count changes are made here.
