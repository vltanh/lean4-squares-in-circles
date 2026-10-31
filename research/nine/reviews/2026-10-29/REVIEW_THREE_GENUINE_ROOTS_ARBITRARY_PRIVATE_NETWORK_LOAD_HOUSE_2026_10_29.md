# Independent full review: arbitrary private-network load and unique root-pair classes

Date: October 29, 2026 UTC. Reviewer: house continuation.

**Decision: PASS unchanged at the exact stated scope.** The radius-free
full-degree virial theorem, the load conclusion for every complete
root-deleted component, the repeated-pair exclusion, the arbitrary-block
join, and the literal six-body consequences are all correct. Types I--III
and the connected three-private-vertex case remain open as the source
states. This review does not close an original coarse cell.

The exact frozen reviewed source is

    THREE_GENUINE_ROOTS_ARBITRARY_PRIVATE_NETWORK_LOAD_AND_UNIQUE_PAIR_CLASS_2026_10_29.md
    be54ef6e20015c3841606d0b7779ba17fe319d2aa886ad9adfd376e985995a20
    374 lines.

I read the entire frozen source and reconstructed its proofs independently.
I did not contribute to the new virial or theta-access strategy. I also
read the complete seven direct inputs in this continuation, including the
new 384-line small-vertex/neighbor-budget source at a81845be. For that new
input I additionally read its full 428-line physical cap and the complete
214-line independent cap review, and checked the new chart transfer and
angular argument directly. The earlier structural source at 3aed6244
already received my separate complete independent review; its exact
root-deletion and pair-cover statements were checked again here.

## 1. Original physical and graph hypotheses are retained

The caller uses the actual connected positive body-pair component G.
Its three distinct genuine roots A,B,C lie in an actual maximal
biconnected block Q and have their distinct original genuine leaves.
The roots have at least their two block neighbors and their real leaf;
no smaller positive degree is assigned to them.

The complete high-S input excludes every low/critical and genuine-D
alternative and supplies the three actual points

    z_i=epsilon e_i in R_i,
    d=1+epsilon>1, 0<epsilon<1/60.

These points all lie in the same closed disk. They are not force
applications invented for the new proof. They are used only to bound
actual support values. All additional physical units, original positive
edges, circle masks, individual zero circle coefficients, singleton
applications and aggregate means remain in the original certificate.

The selection required by the diamond and plane-embedding inputs is the
one compatible certificate selected before multiplier extraction. The new
proof does not choose new normals or make a selection depending on the
unknown circle weights.

## 2. The radius-free virial lemma passes at arbitrary actual degree

Let T be any set of original units meeting D_delta, with 0<=delta<1/2,
and K the nonempty set in the source's Section 1. No connectedness of K
is needed for this lemma. The condition that all edges leaving K end in
T is the exact condition required to control every cut contribution.

For a unit direction n, the centered support of any actual unit square
is at least 1/2. At an original contact U--V, with n directed from U
toward V, the tight physical support relation is

    (c_V-c_U).n=h_U(n)+h_V(n).

The use of h_V(n) is legitimate because every centered square is centrally
symmetric, so h_V(-n)=h_V(n). This equality holds at the unchanged actual
aggregate mean on a shared segment as well as at a singleton contact.

Dotting every full force equation for U in K with -c_U gives the internal
edge contribution

    -mu c_U.n+mu c_V.n
       =mu(h_U(n)+h_V(n))>=mu>0.

Every internal edge is counted exactly twice before combining its two
endpoint terms, and exactly once after that combination.

For a cut edge U--r with r in T, the actual contact satisfies

    p.n=min_(x in r) x.n<=z_r.n<=delta,
    p.n=c_U.n+h_U(n).

Consequently

    -mu c_U.n>=mu(1/2-delta)>0.

This has the correct sign: the K-side center has negative projection
toward a near root, relative to the original common origin. Each cut
edge is counted once. All other edges incident to K have already appeared
as internal edges, so no positive force is omitted.

The resulting identity is precisely

    2 sum_(U in K,k) lambda_(U,k) c_U.p_(U,k)
      =sum_internal mu(h_U+h_V)-sum_cut mu c_U.n.

The source's lower bound and its strict positivity follow. A positive
internal or cut edge is enough; the delta endpoint zero also causes no
difficulty. If every body in K had zero total circle load, every individual
nonnegative lambda would be zero, contradicting this positive right side.
No assumption that every product c_U.p_(U,k) is positive is required.

The force identity is a necessary consequence of the full physical system.
The torque equations remain satisfied and unchanged; using this necessary
force consequence does not shorten a branching body's star. In particular,
the proof is valid for arbitrary private degrees, branches and chords.

## 3. Every complete root-deleted component has a positive circle load

For a component K of G-{A,B,C}, its only cut neighbors are in {A,B,C}.
Because G is connected and contains the roots, K has at least one actual
positive cut edge. The general lemma therefore applies with
delta=epsilon<1/2. It supplies an original circle-loaded body in K.

The conclusion includes the genuine-leaf singleton components and also
components containing several blocks. It does not assert that an
arbitrarily chosen subcomponent after a further graph deletion is loaded.
At least one original positive circle coefficient is present, hence the
supplied body physically touches the containing circle.

If a complete component touched all three roots, choose one incident
edge to each root and connect their endpoints by a tree inside K. Prune
to the tree whose leaves are exactly A,B,C. This tree has one nonroot
branch point and three internally disjoint positive paths to the roots.
No genuine positive degree-one leaf can be internal on these paths.
The complete positive-three-arm input applies to these original paths
without deleting other forces. It excludes every three-root component.

Thus all complete root-deleted components have either one or two root
neighbors, exactly as used later. The theorem does not incorrectly force
the genuine-leaf singleton to have two root neighbors.

## 4. The theta obstruction and all three physical accesses pass

For three internally disjoint A-to-B paths in a plane graph, their union
is a subdivided theta. Its unbounded boundary consists of exactly two
bridges. Internal vertices of the third bridge lie strictly inside the
outer Jordan cycle and cannot have an access to the exterior whose
interior avoids the theta. The source's Jordan-cycle proof covers both
possible placements of the third path relative to the first cycle.

Suppose two distinct complete root-deleted components K_1,K_2 both have
neighbor set {A,B}. Their connectedness supplies the two required paths
P_1,P_2, each with a nonempty private interior.

The third path uses the accepted A--C and C--B pair classes inside Q.
Each class can be either a direct root edge or an actual private network.
If both private portions exist, they cannot meet or be connected in G
after deleting the roots: otherwise their complete component would touch
all three roots, already excluded. Neither can lie in K_1 or K_2.
Their concatenation is therefore a simple third A-to-B path with C as
an internal vertex, disjoint from P_1,P_2 except at A,B.

Theorem A supplies an actual loaded Z_i in each K_i. Take a path inside
K_i from Z_i to P_i and stop at the first meeting. Its interior avoids
P_i by construction and the other bridges by component disjointness.
If Z_i is already on P_i, the length-zero first part is valid.

The full physical embedding input protects the center-to-circle spoke of
every actual boundary body. The entire chosen graph and every contact
junction lie strictly inside the containing disk. Distinct actual units
cannot share a circle point; the input proves this from their inward
corner directions. The local junction routings can be chosen to avoid
all protected spokes simultaneously. Appending the spoke at Z_i and its
outward radial continuation therefore gives genuine exterior access from
an internal vertex of P_i, meeting the theta only at that vertex.

The third access is C--L_C followed by the real leaf's protected spoke.
Its true degree one excludes that leaf from every bridge interior. This
path avoids the entire theta except at C in the same fixed embedding.
The three accesses need not be introduced as new stress edges, and are
not altered by any extra graph edges. Their existence contradicts the
theta's Jordan boundary. This proves the whole repeated-pair exclusion.

The argument covers all private circle masks and all choices of which
actual private body carries the positive load; it does not need a load
at a specified vertex of either A-to-B path.

## 5. The maximal-block join and outer-boundary conclusion pass

If a component outside the maximal biconnected Q met two distinct Q
vertices, a path through that component would add an external ear to Q.
The union is biconnected: removing a Q vertex leaves the other ear end
attached, and removing an internal ear vertex leaves its two parts
attached to the connected Q. This contradicts maximality. The statement
concerns components of G-V(Q), not just individual outside vertices.

It follows that distinct private components of Q-{A,B,C} cannot join
outside Q after deleting the roots. The complete extension of one such
component adds only outside components attached to its own vertices and
has the same root-neighbor set. In particular an extension cannot acquire
a third root through an outside block. The accepted two-terminal cover
and Theorem B now give all assertions of Theorem C.

If the load supplied by Theorem A lies outside Q, a path from it to its
first Q vertex has interior outside Q. That first vertex lies in the
original private component. Its path followed by the protected spoke
gives exterior access to that private vertex. The source correctly avoids
claiming that the load must lie in the private component of Q itself.

The outer boundary of a biconnected plane graph is a simple cycle. Each
root is on it by its real leaf access; each private component meets it by
the preceding extension argument. The cycle splits into three arcs at
the roots. A private component with neighbor pair A,B can occur only on
the A-to-B arc with no root in its interior, since either other arc would
give it a different root-neighbor pair. Thus that component occupies its
pair arc. An additionally present direct A--B edge is an interior chord.
This conclusion uses the inherited embedding and never replaces Q by a
contracted triangle.

## 6. The new small-vertex input has the exact scope required here

I checked all of a81845be, including its continuous angular proof.
For three actual units meeting D_delta, delta<1/10, each supplies an
open arc of length 2acos(1/4)-pi/2 on the circle of radius 4delta.
A unit with no vertex in that disk supplies at least 2acos(1/4), in
every position of the origin. Two such units would exceed total angular
measure 2pi together with the third unit. The strict radical comparison
acos(1/4)>5pi/12 is valid. Thus at least two roots have small vertices.

The high-S root chart then excludes the closed origin. In the strict
vertex case the real S application must be adjacent to the small vertex:
their distance cannot be sqrt(2), and they cannot coincide. If O lay in
the root, its squared application norm would be at most
1+16epsilon^2<d^2, a contradiction. In the aligned case the whole root
lies beyond its positive inward support epsilon.

The resulting aligned and tilted charts satisfy the physical cap's exact
premises 0<a<=epsilon and 0<=beta<=4epsilon<1/10, with the original real
leaf center. The full cap covers every normal quadrant, both owner types,
side means and endpoints, and counts physical boundary neighbors even
when they have zero circle load. It supplies at most one other boundary
neighbor besides the genuine leaf. Hence at most one of the three roots
can have two other such neighbors. The source's six-private-edge count
also correctly excludes the whole independent-private partition 1+1+1.

No stronger conclusion is silently imported: a root with two other
boundary neighbors is the unique possible exception to the small-vertex
property, and the other two roots must each have small vertices and avoid
the closed origin. This is exactly the implication used in Types I/III.

## 7. The literal six-body graph cover and all load joins pass

The caller now has exactly the six block vertices and three genuine
leaves, exhausting the nine positive bodies. Thus the private degrees
in the table are their full original positive degrees. Other physical
zero-weight contacts remain allowed.

After exclusion of 1+1+1, the private-component partitions are 3 and
2+1. In 2+1, uniqueness forces distinct pair classes. Relabeling gives
{P,Q} on A,B and N on B,C, with the direct A--C edge forced. Both P
and Q need a root neighbor by biconnectivity. Their nonempty neighbor
sets, whose union is {A,B}, have exactly the four unordered possibilities
printed in the source. Direct A--B and B--C edges remain optional at this
stage. No chord is lost from the cover.

N is loaded by Theorem A. In Type I it also gives at least one load in
{P,Q}. In Types II/III, P is a true degree-two triangle tip. Were it
unloaded, the full transmitter theorem would separate its two touching
neighbors by positive width, which is impossible. In Type IV each of
P,Q is a true degree-three diamond hub whose central neighbor physically
touches the two other neighbors. The complete selected diamond theorem
therefore forces both loaded, without any assumption on the roots' degrees.

Type IV gives two other boundary neighbors at both A and B and is wholly
excluded by the physical neighbor budget. This is a complete graph-domain
exit and includes zero-stress physical contacts and all original masks.

In Type II, a physically boundary Q, even with zero circle load, would
give A the pair P,Q and B the pair Q,N. The budget excludes this, so Q
is physically clear and has zero load. If the original root edge A--B
were present, Q would be a true degree-three diamond hub with central
neighbor A touching B and P. The diamond theorem would force Q loaded.
Thus the stated physical clearance and absence of A--B both follow.

In Type III, P,N make B the unique possible heavy root, so A,C each have
an actual vertex in D_(4epsilon) and avoid closed O. In Type I the same
follows when Q is physically boundary; otherwise Q has zero load and
Theorem A forces the load in {P,Q} to occur at P. These conclusions keep
the exact distinction between positive circle load and physical boundary.

For partition 3, the one connected private component has a positive
circle load, and the other two pair classes are direct root edges.
Its geometric exit and those of Types I--III remain unproved by this
source, exactly as acknowledged.

## 8. Verification and closure boundary

All seven direct source hashes match their printed pins. The new proof
requires no numerical pose sample or packing certificate. I reconstructed
the support signs, all contributions to the full virial identity, all
paths and accesses in one compatible embedding, every external-block
attachment, and every true-degree/physical-load transfer in the finite
caller. The new a818 input was read completely; its operative physical
cap and existing independent acceptance were also read completely.

The accepted result is uniform over complete private networks and
repeated root-pair classes. Its proof makes no post-extraction normal
change, no force deletion, no two-force substitution at a higher-degree
unit, no chosen circle mask and no mean replacement. Every original
square remains in the same physical packing.

The frozen 374-line source is accepted without amendment. This review
does not alter a ledger, original identifier, denominator, source header,
Lean file, CI state, remote object or whole-cell flag. Its remaining
geometric obligations are those explicitly retained above.
