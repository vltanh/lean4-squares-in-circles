# Degree-free angular order of actual moment ports and every block outside an intact root

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem and whole original
C3.335 chain join, frozen for full root and separate independent review.**
No original ID, checkbox, shared ledger, Lean file, workflow or remote
branch is changed. The three remaining common-root five-block bouquets
are not declared excluded by this source.

Keep the same nine actual interior-disjoint closed unit squares, their
compatible selected physical graph, and the complete original radius
window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 <61/60,
    epsilon=max(d-1,0)<1/60.                            (1)

All pair magnitudes, original common normals and applications, shared
means, physical circle masks, individual zero weights, true degrees and
additional physical contacts remain. The local geometric result below
does not assume any body-force equation or any bound on positive degree.

## 1. Two complete physical support facts and one strict cap

Every actual contained unit V with center c satisfies

    |c| <= d+1/2 <91/60.                               (2)

Indeed its farthest-corner squared norm is at least
|c|^2+|c|+1/2. Solving this quadratic gives (2). If V lies in
n.x>=h for a unit n, its halfwidth along n is at least1/2, and so

    c.n>=h+1/2,       h<=d.                            (3)

These are the full, degree-free bounds in Section1 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, current SHA-256
`20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf`.
No end-triangle force conclusion from that source is used here.

If p is any actual minimum-n support point of a unit V, then

    p+[0,1]n subset V.                                 (4)

To prove the full unit length, write V in its own orthonormal axes.
At a vertex support, every nonzero component of n points from the
appropriate interval endpoint inward; it has absolute value at most
one. A step t<=1 therefore stays in both unit intervals. At a side
support n is an own axis and the other coordinate stays fixed. This
includes every actual side mean and its endpoints.

Here is the cap used in the complete feature cover. No actual contact
can have, on one side, an actual neighbor V in n.x>=h=p.n satisfying

    h>1,       |p|^2>=2.                              (5)

If it did, (3) gives h<=d<61/60 and c.n>3/2. Thus

    |p.Jn|>sqrt(3479)/60,
    |c.Jn|<sqrt(181)/60.

The first inequality uses |p|^2-h^2>2-(61/60)^2=3479/3600;
the second uses (91/60)^2-(3/2)^2=181/3600. Consequently

    |p-c| > (sqrt(3479)-sqrt(181))/60
          > (58-14)/60 =11/15 >1/sqrt(2).              (6)

But every point of the real unit V is at distance at most1/sqrt(2)
from its own center. This proves the cap, including every support
owner, physical frame and actual shared mean.

## 2. The uniform actual-port angular-order theorem

Let K,N_-,N_+ be actual units, with K different from each neighbor.
Both actual contacts retain their real separating outward normals
n_-,n_+ at K and real applications p_-,p_+. Assume

    K,N_-,N_+ are disjoint from the closed disk D_epsilon,
    det(p_-,n_-)<0<det(p_+,n_+).                       (7)

The two neighbors may have arbitrary degrees, forces and circle masks.
They need not touch each other and no triangle equation is assumed.

**Port-order theorem.** On the unique angular branch of the origin-free
convex K, the counterclockwise angular change from p_- to p_+ is
nonnegative. Equality is possible only when

    p_-=p_+=q,
    q is the unique nearest point of K to O.            (8)

We give the entire own-square feature cover. Orthogonal coordinate
changes and reflection merely transform both determinants and angular
orientation. Under a reflection interchange the positive and negative
labels as well; the claimed order and its equality statement are
unchanged. Thus the following normal forms lose no orientation case.

Because K avoids O, reflect a missing own interval to write its first
interval as [a,a+1], a>0. If its other interval misses zero as well,
reflect it positively and exchange own axes so a>=b>0. There are exactly
the two main cases below. All vertices include axis-normal endpoints.

### 2.1. The other own interval contains zero

Write

    K=[a,a+1] x [b,b+1],
    b<=0<=b+1,       a>epsilon.                        (9)

The last inequality follows from dist(O,K)=a and closed-disk avoidance.
An actual right-side axis normal would put its neighbor beyond height
a+1>d, impossible by (3).

At the upper-right vertex p=(a+1,c), c=b+1>=0, the normal has the form
n=(u,v), u,v>=0, u^2+v^2=1. A negative determinant would give

    (a+1)v<c u.

Here u>0, and, if v>0,

    p.n=(a+1)u+c v
        >(a+1)(u+v^2/u)=(a+1)/u>=a+1>d.

For v=0 the same impossible support is exactly a+1. Thus no negative
port occurs at that upper-right vertex. Reflection in y=0 gives the
full counterpart: no positive port occurs at the lower-right vertex.

Every other actual feature is immediate from its complete normal cone.
The top side and upper-left vertex have positive determinant whenever
it is nonzero; the bottom side and lower-left vertex have negative
determinant whenever nonzero. On the left side the determinant is its
y coordinate. Hence every negative port has y<=0 and every positive
port has y>=0.

Equality of their angular coordinates would require both y=0. For the
same square this cannot happen: if its lower side is y=0, only its
negative features can lie there, while if its upper side is y=0 only
its positive features can lie there; if zero is strictly between the
sides, its left/right ports at y=0 have zero determinant. The two sides
cannot both be y=0. Thus the angular change in this case is strictly
positive.

### 2.2. Both own intervals are positive

Now write

    K=[a,a+1] x [b,b+1],       a>=b>0.                 (10)

The far corner (a+1,b+1) has no actual contact at all. Its outward
normal has nonnegative components, and therefore h=p.n>1 while
|p|^2>2. The cap (5) excludes its whole normal cone, including either
axis endpoint.

First suppose a>epsilon. The right-side axis normal is impossible
by a+1>d. The bottom side and lower-right vertex have negative
determinant; the left and top sides and upper-left vertex have
positive determinant. Only the near vertex (a,b) can have either
sign. Put

    theta_0=arg(a,b).

All negative-feature angles are at most theta_0. All positive-feature
angles are at least theta_0, since in particular

    (b+1)/(a+1)>=b/a.

The far corner has already been excluded. Thus equality of one
negative and one positive angle requires both applications to be the
near vertex (a,b). This is precisely the unique nearest point of K.

It remains the complete small-corner alternative

    0<b<=a<=epsilon.                                  (11)

At its near vertex p=(a,b), every outward normal is n=(-u,-v) with
u,v>=0 and u^2+v^2=1. The actual neighbor contains p+[0,1]n by (4).
Set t_0=min(a/u,b/v), omitting a zero denominator. Then

    0<t_0<=sqrt(a^2+b^2)<=sqrt(2)epsilon<1.

At p+t_0 n one own coordinate is zero and the other is in
[0,max(a,b)]. The neighbor therefore meets closed D_epsilon, contrary
to (7). Thus no actual contact uses this near vertex. This proof
includes both side-axis normal limits.

Use the ray of angle pi/4 as the separator for the other features:

- A negative bottom-side port p=(x,b) cannot have angle at least pi/4.
  That would give 0<x<=b<=epsilon. Its actual neighbor contains
  p-[0,1]e_y and hence (x,0), contrary to disk avoidance.
- A negative right-side port p=(a+1,y) cannot have angle at least pi/4.
  That would give y>=a+1>1, so |p|^2>2 and h=a+1>1, excluded by (5).
- A positive left-side port p=(a,y) cannot have angle at most pi/4.
  That would give 0<y<=a<=epsilon. Its actual neighbor contains (0,y)
  by (4), again impossible.
- A positive top-side port p=(x,b+1) cannot have angle at most pi/4.
  That would give x>=b+1>1 and the same cap contradiction.

The lower-right vertex has only negative determinants and angle less
than pi/4. The upper-left vertex has only positive determinants and
angle greater than pi/4. The other two vertices have already been
excluded. This is the entire normal/feature cover, and gives strict
negative-to-positive angular increase in (11).

Sections2.1--2.2 prove the theorem and its exact equality classification.
No local force equation, radial-concurrence claim, chosen midpoint or
private degree was used.

## 3. A directed positive-moment physical cycle must wind

Let an actual simple positive graph cycle have at least three vertices.
Suppose all its actual units avoid closed D_epsilon, and orient the
cycle so that each original directed edge vector f_i at its original
application p_i has

    det(p_i,f_i)>0.                                   (12)

At a cycle body the incoming outward normal is the negative of its
incoming directed force, while its outgoing normal has the outgoing
force direction. Thus its two original ports satisfy (7). Both actual
neighbors belong to the cycle and also avoid the disk.

Replace the center-to-port strands within each actual convex body by
the straight chord between its two original applications. This homotopy
avoids O and changes no physical square or original contact. The angular
change on each chord is nonnegative by Section2.

They cannot all be zero. If they were, (8) would identify the two
applications at every cycle vertex, hence every cycle edge would have
one same actual point q. Each of the at least three distinct units
would have q as its nearest point to O. In particular q!=O, and all
those units would lie in the same half-plane

    q.x>=|q|^2.

At q each unit has an interior tangent sector of angle at least pi/2.
Three such sectors with pairwise disjoint open interiors cannot fit
inside this one half-plane of angle pi. This is a contradiction.

The total angular change is therefore strictly positive. It is an
integer multiple of 2pi, so the actual center/contact cycle has
strictly positive winding about O. In the retained compatible physical
embedding it is a simple Jordan cycle with that same winding. All weak
junctions and coincident contact strands are included by choosing its
finite routing neighborhoods within the positive O clearance.

This directed-cycle theorem needs neither equal edge moments nor a
body-force equation. In particular it applies at loaded or unloaded
degree-three or higher-degree original vertices without dropping any
of their other forces.

## 4. No actual radial contact lies entirely outside an intact root

Suppose E has an actual intact triangle E-P-Q-E, with P,Q true positive
degree two. The complete theorem
ROOTED_INTACT_PETAL_CENTRAL_DISK_INTERIOR.md, SHA-256
`8a2fda961a9d9f76191add305ff65d4942e9e583a611448ec51d77df313035a8`,
gives

    closed D_epsilon subset int E.                    (13)

Every distinct actual closed square is consequently disjoint from
closed D_epsilon: a closed point of that unit in int E would force
open-interior overlap by interior-point approximation.

For completeness take an actual radial contact between two such units.
Its application is nonzero. Write p=t e, t>0, with inner U in
e.x<=t and outer V in e.x>=t. Then t<=d by (3). In an own interval
of origin-free U that misses zero, reflect to [a,a+1], a>0. At its
radial support,

    p.u=a+1>1,       t>1,       a<=t-1<=epsilon.        (14)

If its other own interval also missed zero, the same support argument
would put both absolute coordinates of p above one, giving t>sqrt(2),
contrary to t<=d. Thus that other own interval contains zero, and U
has the actual point (a,0) of norm at most epsilon. This contradicts
(13). Hence every actual positive edge with both endpoints distinct
from E has nonzero origin moment in its original direction.

## 5. Every cyclic block must contain the actual intact root

Let B be any actual biconnected positive block with a cycle, and
suppose E is not one of its vertices. All of its actual units avoid
closed D_epsilon, by (13). Every original edge moment is nonzero,
by Section4.

The full origin torque equations restrict to a circulation on this
actual block. Here is the complete outside-force justification.
Every component of the positive graph outside a biconnected block
attaches to that block at at most one vertex; a second attachment
would put its joining path in the same biconnected block. Sum all
unchanged original torque equations in each such outside component.
Its internal pair moments cancel, and every physical circle atom
has zero origin moment. Its entire moment at the sole attaching
block vertex is therefore zero. This includes arbitrarily many
actual branches and other cyclic blocks, not just genuine leaves.
Subtracting those complete zero moments from each original vertex
torque leaves exactly its full original B-edge moments summing to
zero. Circle moments at B itself are zero as well.

Orient each B edge in the direction of its positive original moment.
At each vertex the sum of positive incoming moment weights equals
the sum of positive outgoing moment weights. A finite nonempty
directed graph with this circulation has a directed cycle: follow
an outgoing edge after each incoming one until a vertex repeats,
and take its simple directed subcycle. The original graph is simple,
and each undirected edge has just one selected direction, so this
cycle has at least three vertices.

Section3 gives positive winding about O for that actual cycle C.
The original intact tips P,Q are not vertices of B: a true degree-two
tip on E-P-Q cannot belong to another cyclic block. Thus the actual
positive E-P path is disjoint from C, and P is a physical boundary
unit by the true loaded-tip theorem.

Use the same compatible physical embedding and protected exterior
boundary access as PHYSICAL_BODY_GRAPH_UNCROSSING.md. The compact
segment from O to c_E lies in int E and is disjoint from all C bodies.
Choose the close routing neighborhoods smaller than this clearance.
The actual and embedded cycle then have equal positive winding at O
and c_E, so c_E lies strictly inside its Jordan curve. The retained
positive edge E-P puts c_P inside the same curve. This contradicts
P's incidence with the unbounded face of the full physical graph.

This is exactly the purely topological outside-branch argument of
GLOBAL_CLOSURE_TERMINAL_SIMPLE_CYCLE_ORIGIN_BRANCH_EXCLUSION.md Section2,
whose complete mathematical review pin is
`c9b040bc50888a87511c5b79d38a6fe1af034e2ad7b0ee0dfdec79a38ebcc672`.
Its current acceptance-header version is
`026b2f76676efa36a3b5ebebb303cbba92ad6be0ed93fd1e2114c0b6795bf4f1`.
No private-degree-two or force-polygon part of that source is used here.

Therefore every actual cyclic positive block contains E. This is a
uniform whole-block theorem, with arbitrary true block degrees and
all full outside systems retained.

## 6. Exact full C3.335 chain caller and remaining scope

The accepted complete original cover is
MIXED_C3_335_COMPLETE_ATTACHMENT_REMAINDER.md, current SHA-256
`7ee5b3b12165e9b30ad279a43fdce76720bc850c429b882d7c4a8b0a0ac2ea36`.
Its original middle-triangle chain has intact E-P-Q, actual middle
triangle E-H-W, and a five-body terminal block at H. All nine actual
units are distinct except their displayed articulation identifications.
The five-block contains H and its four private vertices, and does not
contain E.

Section5 therefore excludes the entire actual five-block at once.
In particular it covers C5, each of the three marked house roots,
and each of the three marked fan roots in the accepted seven-chain
remainder. It also covers the denser positive five-block types before
their earlier accepted exits. Every original private/root load mask,
true degree, chord, shared mean and extra physical contact stays.
The roof-house one-loaded-hub/full-lower-load case is included without
a proper-star assertion at the loaded hub or a shortened cycle equation.

Combining this whole-chain theorem with the accepted unchanged exits
of the displayed cover leaves only its three common-root bouquets:
house at the roof, house at a lower vertex, and fan at a path endpoint.
They contain the intact root E itself and hence do not satisfy the
excluded-block hypothesis. No claim about their root-origin cycle
corrections is inferred from this theorem.

The unrestricted radius bound, the entire C3.335.b0 coarse cell and
the original equality classification remain open until those whole
remaining domains and every other original obligation are closed.
