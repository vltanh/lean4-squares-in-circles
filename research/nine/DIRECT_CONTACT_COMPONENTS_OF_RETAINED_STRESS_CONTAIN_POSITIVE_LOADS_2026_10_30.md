# Every direct-contact component of the retained stress graph contains a positive circle load

Date: October 30, 2026 UTC.

**Status: complete proposed graph-size-independent hand theorem,
awaiting full independent review. No original closure, graph, ledger
or roadmap flag is changed here.**

Suppress only genuinely unloaded true-positive-degree-two runs of one
physical translational stress. In the resulting retained graph, delete
every channel with one or more internal bodies. Every remaining direct-
contact component must still contain a positively circle-loaded body.
Thus unloaded retained hubs cannot be separated from all positive loads
by subdivisions. The proof preserves every original force and requires
no torque or plane embedding.

## 1. Actual packing, full stress, and retained vertices

Let a finite family of actual unit squares have pairwise disjoint open
interiors and lie in a disk centered at O with squared radius at most

    Q=1105/256.

Retain one nonnegative physical contact/circle stress satisfying the
full translational force equation on every body. A positive body pair
carries a positive magnitude, a true common supporting unit normal,
and an application in its actual common intersection. Parallel side
atoms may be aggregated; their actual shared-side mean remains in
the original intersection. Circle atoms have nonnegative weights and
occur at actual circle corners.

Let G be the full positive body-pair graph. Its true degree counts all
positive neighbors of a body in this same stress. A body is unloaded
when its total selected circle weight is zero.

Use the following precise retained vertex set R:

- every positively circle-loaded body; and
- every unloaded body incident to at least one positive body force
  whose true positive degree is different from two.

All unloaded true-degree-two bodies are transmission vertices to be
suppressed. An unloaded body with no positive pair force is not a
retained graph vertex. Such unstressed bodies remain actual physical
squares of the packing; the theorem makes no graph-load assertion
about their isolated zero-edge vertices.

Every unloaded retained vertex has a positive incident force. In fact
its degree is at least three, because a single nonzero pair force
cannot balance with zero circle load. Positively loaded isolated
vertices, if allowed by a more general packing size, cause no problem:
their direct-contact component already contains a positive load.

## 2. The suppressed channels retain full endpoint forces

Every actual center c satisfies

    |c|<M=91/60<2.                                       (1)

Indeed the farthest actual corner has squared norm at least
|c|^2+|c|+1/2, and the expression at M exceeds Q by 31/57600.
Every actual support halfwidth h_S(n) of a unit square is at least
1/2.

At an unloaded true-degree-two body, the full force equation makes
its two positive forces equal in magnitude and opposite in direction.
Along a maximal run of these bodies, this propagates one signed common
unit normal n and one positive magnitude mu. Its endpoint contact
forces are exactly the original forces on the retained endpoints.

Such a run cannot close to itself. If it did, the same normal would
orient all its consecutive support contacts; their strictly positive
center-projection gaps would telescope to zero. This excludes both
an entire component made of unloaded true-degree-two bodies and a
run returning to its own retained endpoint. In the finite graph,
every maximal transmission run therefore has two distinct retained
endpoints.

Replace each such run by one channel in a retained multigraph H on R.
An original direct contact between retained bodies is also a channel.
Different runs with the same endpoints are retained as parallel
channels. For a channel e from i to j, denote its internal body count
by k_e, its actual common signed normal by n_e and its propagated
positive magnitude by mu_e. Its exact endpoint support gap is

    g_e=n_e.(c_j-c_i)
        =h_i(n_e)+h_j(n_e)
             +sum_(internal S on e) 2*h_S(n_e)
        >=1+k_e>0.                                      (2)

The same center bound implies k_e<=2, since k_e>=3 would require
g_e>=4>2M. The theorem below uses only that every non-direct channel
has k_e>=1 and hence g_e>=2; it does not discretize the internal
orientations or use their moment equations.

At a retained unloaded body i, the full endpoint force equation is

    sum_(channels e incident to i) mu_e*n_(i,e)=0,        (3)

where n_(i,e) points along that actual channel away from i.
Equation (3) is the original equation, with the unchanged first or
last force of each suppressed run. No other endpoint force has been
removed. The opposite endpoint sees the opposite normal and the same
positive magnitude.

## 3. The direct-contact component theorem

Let H_0 be the spanning subgraph of H containing exactly the channels
with k_e=0. These are direct actual positive contacts between retained
bodies. It has all retained vertices, including any positively loaded
isolated vertex.

**Theorem 1.** Every connected component of H_0 contains a positively
circle-loaded vertex.

**Proof.** Suppose a component S of H_0 contains only unloaded retained
vertices. Dot (3) at each i in S with its actual center c_i, then sum.
The result is zero. Group the channel contributions into internal
channels, whose two endpoints are in S, and outgoing channels with
exactly one endpoint in S.

For an internal channel e from i to j, its two terms combine exactly
to

    mu_e*n_e.c_i-mu_e*n_e.c_j=-mu_e*g_e<0.              (4)

This grouping includes every internal channel. In particular, a
subdivided channel whose two endpoints happen to belong to the same
direct-contact component is still present and contributes (4).
Arbitrary parallel channels are each included with their own positive
magnitude and actual support gap.

For an outgoing channel, orient its normal from its endpoint i in S
toward its endpoint j outside S. It cannot be a direct channel:
otherwise j would belong to the same component of H_0. Therefore
k_e>=1 and g_e>=2. Equations (1),(2) give its single contribution

    mu_e*n_e.c_i
       =mu_e*(n_e.c_j-g_e)
       <mu_e*(M-2)<0.                                   (5)

All channel terms in the summed equations are therefore strictly
negative whenever they occur. At least one term occurs, because S
is nonempty and every unloaded retained vertex is incident to a
positive force. The total cannot be zero, a contradiction. QED.

The proof is a sum of the actual complete force equations at vertices
of S. It does not replace the component by a single body, drop a
channel that leaves and returns to S, or infer an internal force
balance from a graph drawing.

## 4. Uniform graph consequences

Let b be the number of positively circle-loaded retained vertices,
h the number of unloaded retained vertices, and c_0 the number of
components of H_0. Then Theorem 1 gives

    c_0<=b.                                              (6)

Choose a spanning tree within each component of H_0. The resulting
forest has

    b+h-c_0>=h

edges. In particular, if e_0 is the total number of direct retained
positive contacts, then

    e_0>=h.                                              (7)

Parallel channels do not invalidate the spanning-forest count. A
direct original contact is counted once after body-pair aggregation;
non-direct parallel channels are absent from H_0 but remain in the
force sum used to prove the theorem.

Equivalently, every unloaded retained body is connected to a
positively circle-loaded body by a path of direct retained contacts.
Taking the first positive load along such a path makes every preceding
vertex an unloaded retained hub. No genuinely unloaded true-degree-two
body is hidden inside one of those direct edges.

Several immediate whole-family exclusions follow:

- An unloaded retained hub cannot have every incident channel
  subdivided. Its singleton H_0 component would have no positive load.
- A nonempty connected group of unloaded retained hubs cannot have
  only subdivided channels joining it to all remaining retained
  vertices, even if the hubs are directly joined to one another.
- A proposed retained graph with fewer direct positive contacts than
  unloaded retained vertices cannot support the stated full physical
  translational stress.

These statements allow arbitrary endpoint degrees, graph size,
parallel transmission runs, circle masks and actual application means.
They apply across all blocks and articulations. No specific original
coarse-row identifier is credited without its complete caller.

## 5. Relation to the positive-long-endpoint theorem

The separately proved theorem
`UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md`
shows that a channel with two internal genuine unloaded true-degree-two
bodies has positively loaded endpoints. The present theorem adds a
different restriction: after deleting all channels with even one
internal body, every retained direct-contact component still has a
positive load.

Both may be used on the same unchanged full physical stress. The
two-internal restriction concerns its individual long endpoints;
Theorem 1 concerns entire connected groups of unloaded retained hubs.
Neither asserts that an arbitrary shorter channel has loaded ends,
nor that every large block contains a long channel. Unstressed
physical completing squares remain outside this retained-graph claim
and inside the actual packing throughout.

The optional comparison in this section uses the positive-endpoint
source frozen at SHA256
`d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705`.
The direct-contact component theorem and its edge-count consequence
are self-contained and do not depend on that source.

## 6. Verification boundary

The only geometric inputs are actual contact support equalities,
unit support widths at least one and the exact center bound M<2.
All force equations, true degrees, unloaded predicates and channel
labels refer to one retained certificate. No torque, physical plane
embedding, minimum circle-load count, graph enumeration or lower-radius
window is assumed.

No numerical pose search, Lean compilation, CI, new finite proof
certificate, original ledger edit, repository metadata change or
remote publication was used or claimed in this hand theorem.
