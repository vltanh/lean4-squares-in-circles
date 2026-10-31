# Low-radius moment cycles with boundary-origin units, and every genuine double-leaf bridge fork

Date: October 29, 2026 UTC. Author: pentagon_global continuation.

**Status: complete proposed hand theorems, frozen for a separate full
independent review.** The first new proposition is a complete physical
port-order theorem for every unit whose open interior avoids the
origin, at radius R<=sqrt(17)/2. It includes the previously exceptional
origin-vertex and origin-side-interior units, arbitrary actual neighbor
degrees, every original mean and the entire coincidence cover. It
gives a new directed-moment-cycle theorem on that full low-radius
domain. The final theorem excludes every genuine double-leaf bridge
fork in an actual positive component containing a cyclic block.

No original source, review, fine/coarse flag or count is changed here.
All original physical units and their true force systems remain.

## 1. Standalone low-radius physical support equality

For Sections 1--4, let actual closed unit squares have disjoint open
interiors and lie in one disk centered at O=0, with

    R<=sqrt(17)/2.                                    (1)

No force equation or positive degree is assumed in the local physical
propositions. An actual contact normal means a common separating unit
normal at an unchanged actual common point, including any mean of a
positive-length shared side.

Every actual unit has center c with |c|<=3/2. In its orthonormal own
axes u,v the farthest corner has squared norm

    |c|^2+1/2+|c.u|+|c.v|
        >=|c|^2+|c|+1/2.

The last expression equals 17/4 at |c|=3/2 and is strictly increasing
for |c|>=0. If a contained actual unit lies beyond a support
n.x>=h, its half-width in the unit direction n is at least 1/2. Thus

    h<=1.                                             (2)

If h=1, equality throughout forces c=(3/2)n and half-width 1/2 in
direction n. That direction is an own side axis, and the entire
actual unit is exactly

    S(n)=[1,2]n+[-1/2,1/2]Jn.                         (3)

Its farthest corners have squared radius 17/4, so equality also
forces R=sqrt(17)/2. In particular all actual neighbors beyond the
same height-one support are the same physical unit S(n); two distinct
packing units cannot occupy those identical open interiors.

This is the complete geometric support equality, not an assertion
that the physical S(n) has positive degree one or prescribed circle
weights. It is also the literal scope of Section 1 of the pinned
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md.

## 2. Complete port order when O is outside the open unit

Let K be any actual unit with O not in int(K). Let N_- and N_+ be
two distinct actual neighbors, both different from K. Keep their
actual applications p_-,p_+ and outward common unit normals n_-,n_+
at K. Suppose their origin moments have strict opposite signs:

    det(p_-,n_-)<0<det(p_+,n_+).                      (4)

The points p_-,p_+ are consequently nonzero. Retain the actual broken
path from p_- through c_K to p_+ inside K. Both open center-to-boundary segments are
in int(K), so this path avoids O even when O is on K's boundary.
Its angular increment is measured on the angular interval of
K minus {O}: an interval of length less than pi if O is outside K,
pi/2 if O is a vertex, and pi if O is side-interior. In the last
case the closed semicircle branch includes both endpoint directions.

**Port-order proposition.** This angular increment is nonnegative.
The complete equality alternatives are as follows.

* If O is outside K, equality requires p_-=p_+=q, where q is K's
  unique nearest point to O.
* If O is a vertex of K, the increment is strictly positive.
* If O is side-interior, choose actual coordinates
  K=[0,1]e+[-a,b]f, f=Je, a,b>0, a+b=1. Equality requires
  p_-=p_+=e+b*f or e-a*f, and one of the two neighbors is the
  actual physical S(e). That common point is not the nearest
  point e of S(e). Equality is possible only at R=sqrt(17)/2.

The necessary equality statements retain all actual physical
endpoints. In the last alternative, belonging to S(e) additionally
requires the stated nonzero transverse coordinate to have magnitude
at most 1/2, with equality included. No actual point or normal is
reselected to achieve an equality alternative.

Rotations preserve the proposition. Reflection reverses determinant
sign and angular orientation; interchanging the two port labels
after a reflection preserves the asserted order and its equality
statement. The following complete own-frame reductions are therefore
legitimate for the original actual square.

### 2.1. O is outside K and one own interval contains zero

Choose a missing own interval as [t,t+1], t>0, and write

    K=[t,t+1] times [b,c], b<=0<=c, c=b+1.

The right-side axis is impossible by (2), because its support is
t+1>1. At the upper-right vertex (t+1,c), an outward normal has
nonnegative components (u,v). A negative determinant would give

    (t+1)v<c*u.

For v>0 this implies u>0 and

    h=(t+1)u+c*v>(t+1)(u+v^2/u)=(t+1)/u>1.

For v=0 the same impossible support is t+1. Thus no negative port
occurs at this upper-right vertex. The reflected lower-right vertex
has no positive port. The calculation includes every axis endpoint.

The top side and upper-left cone have nonnegative moment; the bottom
side and lower-left cone have nonpositive moment. A left-side West
normal has moment equal to its actual y coordinate. Consequently
every strict negative port has y<=0 and every strict positive port
has y>=0. All x coordinates are positive, so their angular order
is nonnegative.

It is in fact strict. Equality would force both y coordinates to be
zero. If b<0<c, the only permitted boundary point at y=0 is on the
left side and has zero moment. If b=0, all nonzero moments at the
lower y=0 features are negative, with no positive counterpart. If
c=0, all nonzero moments at the upper y=0 features are positive,
with no negative counterpart. These exhaust the zero endpoints.

### 2.2. O is outside K and both own intervals miss zero

Reflect their signs to write

    K=[t,t+1] times [s,s+1], t,s>0.

Both outward far-side axes are impossible by (2). Every normal at
the far corner (t+1,s+1) has nonnegative components and support
strictly greater than one, so that whole corner has no actual
contact. No relative-size assumption on t and s is needed.

Set theta_0=arg(t,s). Every bottom-side port and lower-right cone
has negative moment and angular coordinate at most theta_0.
Every left-side port and upper-left cone has positive moment and
angular coordinate at least theta_0. The only remaining feature is
the near vertex (t,s), whose normal cone can have either sign.
Thus the increment is nonnegative, and equality requires both
applications to be exactly (t,s), the unique nearest point of K.

These two cases give the entire origin-free conclusion without any
origin-clearance hypothesis on either actual neighbor. In particular
they apply when a neighbor contains O on its boundary.

### 2.3. O is a K vertex

Write K=[0,1]^2 in its actual inward own axes. At (1,1), a normal
with both components positive has support greater than one. An axis
normal would require S(East) or S(North) by (3), neither of which
contains (1,1). Hence the far corner admits no actual contact.

Every actual right-side axis contact has its one possible neighbor
S(East), so its actual application (1,y) has 0<=y<=1/2. Every
actual top-side axis contact similarly has application (x,1) with
0<=x<=1/2. These statements include the two endpoints of each
physical common segment.

The bottom side and lower-right cone have only nonpositive moments;
the left side and upper-left cone have only nonnegative moments.
At O every moment is zero. Therefore, for the strict signs in (4),

    arg(p_-)<=arctan(1/2)<arctan(2)<=arg(p_+).

This proves a strict angular increment for the complete origin-vertex
domain, including all vertex-normal endpoints and variable side means.
No degree or circle status is imposed on a possible radial neighbor.

### 2.4. O is in the relative interior of a K side

Use the full actual chart

    K=[0,1]e+[-a,b]f, f=Je, a,b>0, a+b=1.            (5)

Every actual far-side e contact at x=1 has the same possible physical
neighbor S(e), by (3). This unit need not be a positive leaf.

At the upper far corner (1,b), an outward normal has coordinates
(u,v), u,v>=0. If its determinant v-bu is negative and v>0, then
u>0 and its support satisfies

    h=u+bv>u+v^2/u=1/u>=1,

contrary to (2). The only negative-moment exception is v=0, the
far-side normal e, with its unique physical neighbor S(e).
At the lower far corner (1,-a), the reflected argument says that
the only positive-moment exception is again the far-side normal e
with that same S(e). All weak normal endpoints are included.

The rest of the complete side and vertex cones give the following
precise separation:

    every negative port not belonging to S(e) has
        arg(p_-)<=-arctan(a);
    every positive port not belonging to S(e) has
        arg(p_+)>= arctan(b).                         (6)

Indeed the first features are the lower side, lower-left cone,
negative part of the near side and lower far corner. The second
features are their upper counterparts. The near-side origin itself
has zero moment. These exhaust every remaining actual support feature.

If neither neighbor is S(e), (6) gives a strict positive increment.
If the negative port belongs to S(e), it is (1,y) with 0<y<=b;
the other positive port is not at S(e) because the two neighbors
are distinct. Thus

    arg(p_-)=arctan(y)<=arctan(b)<=arg(p_+).

Equality requires both actual applications to be (1,b). This point
is different from the unique nearest point (1,0) of S(e), since
b>0. If the positive port belongs to S(e), its y coordinate is
negative and the reflected comparison requires both applications
to be (1,-a) in the equality case. It also differs from (1,0).
Both ports cannot belong to S(e), because it is one actual unit
and the two neighbor labels are distinct.

This proves the full side-interior assertion, all equality neighbor
identities and all shared-mean endpoints. The path through c_K is
essential to the stated angular interpretation: a direct chord between
two near-side points can pass through O, while the actual center
strands always avoid it. No such origin-crossing chord is used.

## 3. A whole low-radius directed moment cycle must wind

Retain any actual simple cycle with at least three vertices in the
common compatible positive body graph. Suppose (1) holds, O lies
in the open interior of none of its actual units, and its original
directed edge forces have strictly positive origin moments:

    det(p_i,F_i)>0.                                   (7)

**Cycle theorem.** The original center/contact cycle has strictly
positive winding about O. Its realization in the common compatible
plane embedding is a simple Jordan cycle with that same winding.

At each cycle body the incoming outward force is the negative of
the incoming directed force, and the outgoing one has the outgoing
sign. Their two actual neighbors are distinct, so Section 2 applies.
Keep the genuine center-to-port strands. They all avoid O because
their ports are nonzero and their open portions are in the open
unit. Their angular increments are nonnegative.

They cannot all be zero. If a cycle unit has O as a vertex, Section
2.3 already gives a strict increment. If a cycle unit has O in a
relative side interior, its equality alternative in Section 2.4
requires one adjacent cycle unit to be S(e), with their unchanged
application a far corner different from e. But S(e) avoids O;
equality at that adjacent cycle unit would require that same
application to be its unique nearest point e, by the full origin-free
conclusion of Sections 2.1--2.2.
This is a contradiction. Equivalently Section 2.1, which contains
the actual radial S(e) chart, gives strict increment directly.

If all cycle units avoid O, equality at every one identifies its
two applications as its nearest point. Following the cycle makes
all its original edge applications the same q!=O. Every cycle unit
then lies in the common half-plane

    q.x>=|q|^2.

At q each of at least three distinct units contributes a connected
inward tangent sector of angle at least pi/2. Their disjoint open
sectors cannot all fit into that one half-plane of angle pi.
Thus this last all-zero alternative is impossible as well.

The total angular increment is therefore strictly positive. It is
an integer multiple of 2*pi because the original center/contact walk
is closed and avoids O. This proves its positive winding.

For clarity about the possible boundary-origin units, the proof does
not require positive distance from O to every whole cycle square.
It uses the positive distance from O to the finitely many actual
center/port strands in this cycle. That distance is positive by the
preceding paragraph. The compatible embedding construction permits
the junction disks and parallel strand tubes to be arbitrarily small.
Choose them within this positive clearance, while keeping the same
complete physical graph and its protected exterior spokes. The
resulting realization of a simple graph cycle is a Jordan curve
homotopic to these strands away from O and has the same winding.

No force equation or degree reduction at a cycle body is needed for
this theorem. Zero-moment edges may remain elsewhere in the original
graph; the theorem concerns a directed cycle satisfying (7).

## 4. The whole genuine double-leaf bridge-fork statement

Return to the common unchanged nine-square canonical selected pose
and compatible physical certificate in the full declared window

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.                          (8)

Suppose U has true positive degree three with exactly the neighbors
L_1,L_2,H. The units L_1,L_2 are distinct genuine positive leaves,
and H is their distinct nonleaf parent-side neighbor. Thus these
three displayed edges are actual bridges. Suppose the same positive
component has any actual maximal cyclic block Q. It may have any
size, chord pattern, original loads, genuine degrees or additional
attachments allowed by the original nine actual units.

**Fork theorem.** This entire configuration is impossible. In
particular every three-edge double-leaf fork attached to a cyclic
block of any size is excluded, without an additional genuine leaf
elsewhere or an unloaded degree-two hypothesis at H.

The conclusion does not infer that a two-leaf root with further
positive neighbors has this true degree-three star. Its full-degree
premise at U is essential in the critical force calculation below.
No star at H or at a Q vertex is shortened.

## 5. The existing central-disk theorem removes every noncritical case

The complete geometric central-disk lemma for two genuine leaves
in TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Section 1,
allows arbitrary other root neighbors and retains all leaf types,
physical masks and means. It gives:

* For d<1, O is in int(U), which is D_epsilon subset int(U).
* For d>1, the entire closed D_epsilon is in int(U).
* For d=1, either O is in int(U), or U has O as a vertex and both
  actual leaves are the radial S units in its two side directions.

In the first three interior alternatives, the complete central-disk
leaf-root theorem in CENTRAL_DISK_LEAF_ROOT_AND_DOUBLE_LEAF_TRIANGLE_BLOCK_EXCLUSION.md,
Section 2, applies to U and its actual leaf L_1. It says that every
actual cyclic block in this component contains U. But a body with
exactly two genuine leaves and only one other positive neighbor
cannot belong to a cycle. This is a contradiction.

Only the exact critical corner configuration remains, after one
common coordinate change of the entire packing:

    R^2=17/4, d=1, epsilon=0,
    U=[0,1]u+[0,1]v, u,v perpendicular,
    L_1=S(u), L_2=S(v).                               (9)

This entry includes every critical physical and weight endpoint;
it is the complete exception in the pinned central-disk proof.

## 6. Full critical force and complete origin isolation

Since O belongs to U, all its points have norm at most sqrt(2)<R.
It is physically circle-clear. The two actual leaf forces at U are
alpha*u and beta*v, with alpha,beta>0. Its complete true U3 force
equation therefore makes the H direction strictly negative in both
own coordinates. Its actual support is U's unique origin vertex:

    p_UH=O,
    U intersect H={O}.                               (10)

H contains O on its boundary; it cannot contain O openly because
its interior would then overlap U. It is physically circle-clear
as well, but all of its actual positive pair forces remain.

**Origin isolation.** No third actual square can contain O in the
original nine-square packing.

If O is in a relative side interior of H, its tangent sector is a
half-plane. Its outward normal toward U is a strictly positive
combination of u,v by the full U3 equation. U's closed right-angle
sector is strictly inside the opposite angular half-plane. The two
remaining angular gaps each have opening strictly below pi/2. A
third square through O would need a connected tangent sector of
angle at least pi/2 in one of those gaps, which is impossible.

If O is a vertex of H, its right-angle sector and U's sector share
no nonzero ray, by the physical singleton (10). Their complementary
gaps are both positive and sum to pi, so each is strictly narrower
than pi. A third unit containing O could not have O interior or
side-interior. It would have O as a vertex. The full physical
THREE_VERTEX_ORIGIN_CAPACITY.md theorem, exactly at R^2=17/4,
then permits at most eight actual units. That contradicts the
unchanged nine-unit packing. No degree or stress premise is used
in that capacity theorem.

This covers the two entire possible H boundary positions. Thus H
is the only actual square other than U that can contain O. Every
other actual closed square has strictly positive distance from O.

## 7. The original Q moments form a nonempty circulation

U and its two genuine leaves belong to no cyclic block. Hence Q
avoids all three of them. By Section 6, at most one Q unit can
contain O, namely H if it belongs to Q. All other Q units avoid O.

Q has an edge joining two origin-free units. If H is not in Q,
this is immediate. If H is in Q, Q minus H is connected and has
at least two vertices, by biconnectivity and |Q|>=3. It therefore
has an edge with both endpoints different from H.

No actual contact between two origin-free units at this radius can
have zero origin moment. For a contrary nonzero application write
p=t*n with t>0, reversing the edge orientation if necessary. The
outer unit lies beyond n.x=t, so (2) gives t<=1. The inner unit
maximizes n at p. Choose one of its own intervals missing zero and
reflect that axis to [a,a+1], a>0. Since p=t*n, its positive own
coordinate makes the corresponding component of n positive. Thus
that support coordinate of p is a+1>1, and |p|=t>1, a contradiction.
The application cannot be O because both units avoid O. This proof
also covers every original side mean and its endpoints.

Consequently at least one original positive Q edge has a nonzero
origin moment. The full original Q moments form a circulation:
each component outside a maximal cyclic block attaches to Q at
at most one vertex. Sum its unchanged original origin-torque
equations. All internal pair moments cancel at their identical
actual applications, and all circle forces have zero origin moment.
The complete exterior moment at its sole Q attachment is zero.
Subtract these full zero contributions from the actual Q equations.
What remains is exactly the original Q-edge moment circulation.

This retains every physical force, including every other branch or
cyclic block outside Q, and no false degree is assigned to any root.
Orient each nonzero Q edge in its positive-moment direction and use
its positive moment magnitude as the circulation weight. Zero-moment
edges are ignored only in this auxiliary directed circulation; they
remain in the complete original physical certificate. A nonempty
finite circulation contains a directed simple cycle C of at least
three vertices.

Every actual C unit has O outside its open interior. Indeed U
contains O and is a different actual square, so any other square
containing O openly would overlap U. The full new low-radius cycle
theorem in Section 3 therefore applies at R^2=17/4, even when C
contains H with O on its vertex or side. It gives positive winding.

## 8. That cycle obstructs the unchanged outside leaf path

Keep the common compatible embedding with the small routing chosen
in Section 3. It realizes C as a simple Jordan cycle enclosing O.
The compact segment from O to c_U is disjoint from the original
cycle center/port strands: except at O it lies in int(U), while
all cycle units differ from U; the strands themselves avoid O.
The finite routing neighborhoods can also be chosen within this
positive segment clearance, simultaneously with their O clearance.
Thus c_U is on the same bounded side of C as O.

The actual positive edge U--L_1 has neither endpoint on C, since
Q avoids U and the genuine leaf L_1. In this one plane embedding
it cannot cross C, so c_(L_1) is on the bounded side as well.
But the full genuine leaf force makes L_1 physically circle-touching,
and the common compatible embedding protects its access to the
unbounded face. This is the required contradiction.

The original force application UH at O was never moved. The cycle
may pass through the body vertex H, but its selected nonzero-moment
ports and its center strands avoid O. This is precisely why the
boundary-origin extension and the careful strand-based winding
argument are needed; one cannot substitute a theorem requiring
every whole cycle body to avoid the origin.

Together with Section 5 this proves the fork theorem throughout
the full original radius window and every genuine S/D leaf choice.

## 9. Literal forest applications and limits

In the original one-cyclic-block/three-bridge profiles, the single
fork-shaped outside branch is

    H--U, U--L_1, U--L_2.

The complete original forest reductions make U a true unloaded
degree-three body and L_1,L_2 genuine leaves. H keeps degree
deg_Q(H)+1 and every original circle or other pair term. This is
a literal caller for every block size, in particular the full
double-leaf-fork shape of C1.5.b3 and C1.6.b3. No classification
of the five- or six-body block or its loads is required.

The theorem also applies whenever this same true fork appears
elsewhere in a larger original positive component with a cyclic
block, subject to the unchanged nine-body and selected-certificate
scope. It does not close a three-bridge coarse row while its other
forest shapes, such as three direct leaves or a short arm plus a
direct leaf, remain unproved. No such whole-parent closure or count
change is asserted here.

The standalone low-radius port and cycle theorems in Sections 1--3
have the broader purely physical radius premise R<=sqrt(17)/2
and no private-degree or circle-load condition. Their actual cycle
must have O outside each open body and nonzero directed moments.
Those hypotheses, including the equality-neighbor identities and
one common compatible embedding, remain obligations of any caller.

## 10. Exact operative inputs and preservation boundary

The six complete direct input manuscripts below were read in this
continuation and their exact bytes checked. The new low-radius port
cover and cycle equality argument are proved in full above; they do
not import the stronger neighbor-clearance premise of an older
origin-free-only cycle theorem into a false boundary-origin caller.

| Complete operative source | SHA256 | Literal use |
| --- | --- | --- |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Full Section 1 contained-unit support and equality, also independently rederived in Section 1 above |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force/torque, actual support applications and full shared means |
| TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md | 0cb8877bc74397213f4bf5a0768037a6e2650b812e55a41c2b793410c9f964de | Entire force-free Section 1 central-disk and critical corner cover at any genuine two-leaf root |
| CENTRAL_DISK_LEAF_ROOT_AND_DOUBLE_LEAF_TRIANGLE_BLOCK_EXCLUSION.md | dd03214ab5e0100bd35211993591baabd5fd0578191cc2ad2d4c1e344b8a5411 | Complete Section 2 arbitrary cyclic-block obstruction from an actual central-disk leaf root; none of its specialized triangle force equations is used |
| THREE_VERTEX_ORIGIN_CAPACITY.md | 1388d83f7ecfa70ac7c86585fd6412f3187fa5e65cb4c3116411c8452ad0293d | Entire physical critical-radius capacity for any three actual origin-vertex units, with all other independent frames retained |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Same compatible body graph, arbitrarily small actual-strand routing, and protected exterior access of every physical boundary body |

All original nine physical units, positive forces, true degrees,
physical circle masks, individual zero weights, complete application
sets and selected common normals remain. No normal is reselected,
no shared mean is changed, and no zero-moment physical force is
discarded to create a smaller star. No pose sampling, angular mesh,
new packing certificate, Lean/Lake compilation, CI/workflow, source
or metadata edit, staging, commit or remote mutation was performed.
Separate full independent review of this exact new source is required
before adoption or any whole-family ledger use.
