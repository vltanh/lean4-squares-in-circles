# Every private network carries a real circle load, and each root pair has at most one

Date: October 29, 2026 UTC. Author: block_forests continuation.

**Status: complete proposed arbitrary-degree force theorem and whole
repeated-pair exclusion, with an exact six-body graph consequence; submitted
for independent review.** No original coarse cell is declared closed.
Every statement retains the actual nine squares and the complete compatible
selected physical certificate. Graph paths used in the topological proof
are not replacements for any original force equation.

Keep the original radius window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Let G be the actual connected positive body-pair component containing
three distinct genuine roots A,B,C and their distinct actual positive
degree-one leaves L_A,L_B,L_C. Suppose A,B,C belong to one actual
biconnected block Q. Each root then has true positive degree at least
three, since its two or more block neighbors and its own genuine leaf
are distinct. All other positive edges, blocks, body loads, individual
zero circle coefficients, physical corner masks and side-contact means
are retained.

The complete high-S reduction first excludes the low/critical radius
domain and every genuine D leaf. Hence any remaining configuration has

    d=1+epsilon>1, 0<epsilon<1/60,
    z_A=epsilon e_A in A,
    z_B=epsilon e_B in B,
    z_C=epsilon e_C in C,

where the actual genuine leaves have their full S charts in the directions
e_A,e_B,e_C. In particular all three original roots meet D_epsilon.

**Theorem A (arbitrary private-component load).** Every nonempty connected
component K of the complete graph G-{A,B,C} contains an actual body with
strictly positive total circle load. This includes arbitrary private
degrees, branches, chords and other attached blocks. It is stronger than
the former true-degree-two path load argument.

**Theorem B (unique two-root class).** At most one connected component of
G-{A,B,C} can have root-neighbor set {A,B}. The same holds for {B,C} and
{C,A}. Thus every repeated pair class is excluded at once, with no private
load mask or internal network type prescribed in advance.

**Theorem C (literal block consequence).** Every nonempty component of
Q-{A,B,C} attaches to exactly two roots. For each pair there is at most
one such private component. Each of the three pair classes remains
nonempty after an original direct root edge is allowed as a class member.
If a pair has no private component, its actual direct positive root edge
is therefore forced. If a pair has a private component, its direct root
edge may also be present. There are at most three private components.

An original private component of Q need not itself contain the positive
circle load when Q has outside attachments. The load then belongs to its
complete root-deleted extension in G, and there is a genuine graph path
from a private vertex of Q to that physical circle-loaded body avoiding
the rest of Q. This distinction is essential to the arbitrary-block
statement and is proved below.

## 1. A radius-free virial lemma for the actual full force equations

The following statement does not require three roots or biconnectivity.
Let T be any set of original units, each containing an actual point of the
same closed disk D_delta, where 0<=delta<1/2. Let K be a nonempty set of
other original units such that every positive edge leaving K ends in T.
Assume at least one positive edge is internal to K or leaves K. Then K
cannot have zero total circle load at every one of its bodies.

For each original square U, let c_U be its actual center and let

    h_U(n)=max { n.(x-c_U) : x in U }

be its centered support function in a unit direction n. A unit square
has h_U(n)>=1/2 for every unit n, independent of its frame. The complete
physical force equation has the unchanged form

    2 sum_k lambda_(U,k) p_(U,k)
       + sum_(V positive neighbor of U) mu_UV n_UV = 0,       (1)

where n_UV points from U toward V. Each original positive pair has its
actual common support point or its actual aggregate mean on the shared
segment, and mu_UV>0. In particular n_VU=-n_UV.

Dot (1) with -c_U and sum over all U in K. For an internal edge U--V,
orient n=n_UV. Its two contributions are exactly

    -mu c_U.n + mu c_V.n
       = mu (c_V-c_U).n
       = mu (h_U(n)+h_V(n))
       >= mu > 0.                                      (2)

The middle equality is the actual tight support relation at the original
contact. It holds for side means and all point-contact features alike.

For a cut edge U--r, with U in K and r in T, put n=n_Ur and let p be
its actual application mean. The entire root r is on the n side of its
support line, so for any actual z_r in r intersect D_delta,

    p.n=min_(x in r) x.n <= z_r.n <= delta.

On the U side, p.n=c_U.n+h_U(n). Consequently

    c_U.n <= delta-h_U(n) <= delta-1/2,
    -mu c_U.n >= mu(1/2-delta)>0.                       (3)

Every internal and every cut force has been included exactly once in
(2)--(3). If every lambda_(U,k) were zero, the summed equation (1) would
say that the sum of these nonnegative quantities is zero. The assumed
positive incident edge makes that sum strictly positive, a contradiction.

Equivalently, the original complete equations give the quantitative
identity and bound

    2 sum_(U in K,k) lambda_(U,k) c_U.p_(U,k)
       = sum_internal mu(h_U+h_V) - sum_cut mu c_U.n_Ur
       >= sum_internal mu + (1/2-delta) sum_cut mu > 0.  (4)

Only the strict positivity conclusion is needed here. No torque equation
has been discarded from the certificate; the force identity alone is a
necessary consequence of the full system. In particular a branching
private unit has not been treated as a two-force transmitter, and a
network has not been contracted to an effective square or edge.

## 2. Apply the lemma to complete root-deleted components

Put T={A,B,C} and delete only these three vertices in the graph-theoretic
sense. Let K be a nonempty connected component of G-T. Any positive edge
from K to outside K ends in T by the definition of a connected component.
There is at least one such edge: G is connected and contains T, while K
is a proper nonempty vertex set. Thus Section 1 applies with
delta=epsilon<1/60<1/2 and proves Theorem A.

This assertion includes the singleton components consisting of the three
genuine leaves. It also covers a large private network with arbitrary
positive degrees and arbitrary further blocks inside that network.
The positive circle-loaded body supplied by the proof is an actual unit,
not an auxiliary boundary label. At least one of its actual circle-corner
coefficients is strictly positive, so it physically touches the containing
circle. All of its other coefficients, including zeros, remain unchanged.

The same complete positive-three-arm argument used in the structural
source shows that no K can have all three roots as neighbors. If it did,
choose one K-to-root edge for each root, join their endpoints by a tree
inside K and prune to the minimal subtree with root leaves A,B,C. Its
unique branch vertex is an original nonroot body, and its three root paths
meet only at that vertex. They cannot contain a genuine leaf internally.
The accepted full-star three-arm theorem excludes this physical pattern.
Thus a component of G-T has either one or two root neighbors.

## 3. A plane theta cannot give all three bridges exterior access

Here is the precise elementary topological fact used next. Let P_1,P_2,P_3
be three simple paths between distinct vertices A and B in a plane graph,
pairwise disjoint except for their ends. Each path is called a bridge of
this theta subgraph. The unbounded face of their union has boundary made
from exactly two of the three bridges. The internal vertices of the third
bridge are incident only to bounded faces of that theta subgraph.

One proof is to take the simple Jordan cycle P_1 union P_2. The interior
of P_3 lies wholly on one side of that cycle, because it is connected and
cannot cross the cycle. If it is in the bounded side, P_3 is the interior
bridge. If it is in the other side, P_3 divides that side into a bounded
region and the unbounded face; exactly one of P_1,P_2 then bounds the
unbounded face together with P_3. In every case exactly one bridge is
absent from the unbounded boundary. The argument also covers graph
subdivisions of the paths and paths whose original drawings have bends.

It follows that there cannot be, for every j, a path from an internal
vertex w_j of P_j to the outside of a disk containing the theta, whose
interior is disjoint from the theta. Such a path from the interior bridge
would have to cross the simple outer cycle. The access paths do not need
to be edges of the theta; an actual attached tree and a protected physical
circle spoke are valid accesses.

## 4. The whole physical embedding supplies the three forbidden accesses

Suppose there are two distinct complete components K_1,K_2 of G-T whose
root-neighbor sets are both {A,B}. Connectedness supplies a simple actual
positive A-to-B path P_i with all internal vertices in K_i. The two paths
are internally disjoint, and each has at least one internal vertex.

There is a third actual A-to-B path P_3 through C, avoiding K_1 and K_2.
To see this without assuming a direct root edge, use the already proved
pair cover inside Q. Choose a simple A-to-C path using either its direct
root edge or one private Q-T component attached to {A,C}. Choose a
simple C-to-B path using either its direct edge or one component attached
to {B,C}. Their private vertices are in distinct root-deleted components:
if those two private parts could be joined in G-T, that complete component
would have all three roots as neighbors, which Section 2 excludes. They
also cannot belong to K_1 or K_2, whose root-neighbor sets are {A,B}.
Thus their concatenation P_3 is simple and is disjoint from P_1,P_2
apart from A,B. The root C is an internal vertex of P_3.

By Theorem A, each K_i contains an actual circle-loaded vertex Z_i.
Since K_i is connected, choose a path inside K_i from Z_i to the nonempty
set of internal vertices of P_i. Stop on its first meeting w_i with P_i.
Its interior avoids the entire theta: it avoids P_i by the first-meeting
choice, and it avoids P_2,P_3 because their internal vertices are outside
K_i. If Z_i already lies on P_i, the initial path has length zero and
w_i=Z_i. This is allowed.

Use the fixed compatible plane embedding of the entire selected positive
body graph. Its contact-junction routing preserves the actual geometric
cyclic order and the spokes from every physical boundary body to its own
circle corner. By PHYSICAL_BODY_GRAPH_UNCROSSING.md, Sections 5--6, those
spokes meet no graph edge except at their incident body centers. Distinct
circle corners belong to distinct physical squares, and the local
junction perturbations can all be chosen to avoid the protected spokes.
In particular a shared three- or four-body contact is already routed in
this one full embedding; no new incompatible routing is being requested.

Append Z_i's protected spoke and a radial continuation outside the
containing disk to the path w_i--Z_i. This gives the genuine exterior
access from the internal vertex w_i of P_i required by Section 3. The
graph lies strictly inside the containing disk, so the outward continuation
cannot meet it. The two bodies Z_1,Z_2 are distinct because K_1,K_2 are.

The third bridge has the access C--L_C followed by L_C's protected circle
spoke and outward continuation. The leaf L_C is distinct from all roots
and has true positive degree one, so it is on none of the three paths.
This access meets the theta only at C. It cannot pass through K_1 or K_2:
the genuine leaf's only original positive neighbor is C.

We have therefore given every one of the three theta bridges an exterior
access, contradicting Section 3. This proves Theorem B. Every original
edge not in the theta remains in the complete physical force system.
Additional edges in the plane graph can create more obstacles; they
cannot provide an escape through the theta's Jordan boundary.

## 5. Join the complete-component result back to an arbitrary actual block

Here Q is an actual maximal biconnected block of G, with at least three
vertices. Every connected component of G-V(Q) has at most one neighbor
in Q. Indeed, two distinct such neighbors would supply a path between
two distinct vertices of Q whose internal vertices are outside Q. The
union of that path with Q is biconnected: deleting a Q vertex leaves Q
connected and any surviving path pieces attached to an undeleted end;
deleting an internal path vertex leaves its two pieces attached to the
connected Q. This strictly enlarges the biconnected block, a contradiction.

Consequently two different components of Q-T cannot become joined by
a path outside Q in G-T. Their complete root-deleted extensions are
different components of G-T. More precisely, the extension of one
private component K consists of K together with outside components
attached to its own vertices. It has exactly the same root-neighbor set
as K. An outside component cannot also attach to a distinct root in Q,
by the preceding one-attachment fact.

The structural theorem gives exactly two root neighbors for every such
K and a nonempty direct-edge-or-network class for every root pair.
Theorem B now proves that at most one K can belong to any one pair
class. This establishes all assertions of Theorem C while allowing
arbitrary outside stars at the original private vertices.

For completeness, let Z be the loaded body in the complete extension of
K given by Theorem A. If Z is in K, its own protected spoke gives a
private vertex of Q access to the exterior. Otherwise, take a path from
Z to K inside the extension and stop at its first Q vertex. The path
interior is outside Q. Appending Z's protected spoke gives that first
private vertex a genuine exterior access avoiding all of Q.

This also describes the outer boundary of Q in its inherited embedding.
Because Q is biconnected, its outer face boundary is a simple cycle.
The three roots lie on it, using their actual leaf accesses, and every
private component meets it by the preceding paragraph. In the cyclic
order of A,B,C, the boundary segment between a consecutive pair is either
their direct edge or a path in their unique private component. A private
component attached to that pair must occupy that segment; if a direct
edge is additionally present, that edge is an interior chord. This is
an embedding consequence, not a replacement of the original block.

## 6. Exact six-body consequence after the accepted neighbor-budget theorem

Now impose the literal finite caller: the entire positive component is
a six-body biconnected Q plus precisely the three genuine leaves at
A,B,C. There are no additional positive vertices. All nine physical
units are still present. The earlier small-vertex theorem has already
excluded the entire private-component partition 1+1+1. Thus the three
private vertices have partition 3 or 2+1.

Theorem C excludes every repeated-pair choice in the partition 2+1.
Relabel its two distinct pair classes as follows:

    {P,Q} is the two-vertex private component, attached to A,B;
    {N} is the singleton private component, attached to B,C.

The original edge P--Q is present. The original edges B--N and C--N
are present, and N has true positive degree exactly two. The root edge
A--C is forced because its class has no private component. Root edges
A--B and B--C may be present or absent. Biconnectivity gives each of
P,Q at least one root neighbor. Their root-neighbor sets are nonempty
subsets of {A,B}, with union {A,B}. Up to interchanging P and Q,
there are exactly the following four possibilities:

| Type | Root neighbors of P | Root neighbors of Q | Exact initial conclusion |
| --- | --- | --- | --- |
| I | A | B | P,Q are true degree two; at least one is loaded |
| II | A | A,B | P is a true degree-two triangle tip and is loaded |
| III | B | A,B | P is a true degree-two triangle tip and is loaded |
| IV | A,B | A,B | P,Q are true degree-three diamond hubs and both are loaded |

In every row N is loaded by Theorem A applied to its singleton complete
component. For Type I, Theorem A applies to {P,Q}. For Types II and III,
the true two-force triangle-tip obstruction forces P loaded: an unloaded
transmitter would separate its two touching neighbors by width at least
one, which is impossible. In Type IV, the complete selected degree-three
diamond theorem applies separately to P and Q. For P, its neighbors are
A,B,Q and Q physically touches both A and B; the other application is
the same with P,Q exchanged. No root degree has been reduced.

Type IV is impossible in its entirety. Both A and B have the distinct
physical boundary neighbors P,Q, and B additionally has N. The accepted
small-vertex neighbor theorem allows at most one of the three genuine
roots to have two other physical boundary neighbors, in addition to its
own leaf. This contradicts the actual A and B counts. Thus only Types
I, II and III remain in the partition 2+1.

Type II has the stronger necessary conditions

    Q is physically circle-clear;
    the root edge A--B is absent.                         (5)

Indeed, if Q were physically boundary, A would have the two boundary
neighbors P,Q and B the two boundary neighbors Q,N. Their own genuine
leaves are additional distinct boundary neighbors, contradicting the
same theorem. Hence Q has zero circle load. If A--B were present, the
true degree-three Q would have neighbors A,B,P, with A touching B and P.
The diamond theorem would force Q loaded, a contradiction. This proves
(5), including physically boundary candidates with zero load.

For Type III the distinct loaded neighbors P,N make B the unique possible
root with two other physical boundary neighbors. Thus A and C each have
an actual vertex in D_(4epsilon) and avoid the closed origin, by the full
small-vertex theorem. Type I has the same conclusion for A,C whenever
Q is physically boundary, because B then has Q,N. Otherwise the load
in {P,Q} must occur at P. No whole exit for Types I--III is claimed.

The partition 3 likewise remains a genuine geometric problem. Its one
private component carries a positive actual circle load by Theorem A,
and the other two root pair classes are direct positive root edges.
The roots' true degrees, all internal private contacts and every original
physical mask continue to matter in its remaining geometric analysis.

## 7. Exact inputs, novelty and closure boundary

| Complete source | SHA256 | Consumed scope |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full actual force equations and tight physical support relation; true unloaded2 transmitter only in Section 6 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | One compatible plane drawing and protected spokes for all physical boundary vertices |
| THREE_GENUINE_LEAF_ROOTS_HIGH_S_REDUCTION.md | 41c6686127871c7c99ab69c84292f04c995a8530eb02cde0235cdacc181ae73f | Complete low/critical and D-leaf exit, with the actual common epsilon near points |
| THREE_GENUINE_LEAF_ROOTS_POSITIVE_THREE_ARM_TREE_EXCLUSION.md | c9ffa9834fbb5e018122552487256693148e0d45d6b69eef21c68bf577b5cf89 | Full-star obstruction to one nonroot component meeting all three genuine roots |
| THREE_GENUINE_ROOTS_BLOCK_TWO_TERMINAL_NETWORK_COVER_AND_DENSE_FIVE_EXCLUSION_2026_10_29.md | 3aed6244d69913b6eecb61ff9b8985688e723da3ec4a57ffaadc8e5d92dd7b66 | Exactly two root neighbors in every private block component and the complete pair cover |
| THREE_GENUINE_ROOTS_TWO_SMALL_VERTICES_AND_BOUNDARY_NEIGHBOR_BUDGET_2026_10_29.md | a81845be499f5eafb45c796cb057a46c6c85f81e59279fdac6859753079bc98b | Entire independent-private six-body exit and the at-most-one-heavy-root physical count |
| NO_UNLOADED_DIAMOND_HUB.md | 82b546953a927a09d8ccabdefd8ffc10eac3e4efc5d8a122840f1343f80a7e2d | Exact true-degree-three load consequences in Section 6 |

The new mathematical steps are the complete-degree virial lemma, its
application to full root-deleted components, the three-access theta
exclusion, the maximal-block join retaining outside attachments, and the
resulting literal six-body cover and Type II/IV consequences. Each is
proved above over the whole continuous physical domain.

This excludes every repeated-root-pair private-network class and all
Type IV six-body attachments uniformly. It does not declare the entire
six-body three-leaf cell or any of the seven remaining five-body families
closed. No original identifier, coarse denominator, load mask ledger,
status flag or remote file is edited by this manuscript.

No force deletion, normal change after stress extraction, radius grid,
numerical pose sample, new packing certificate, Lean compilation, CI
dispatch or merge was used.
