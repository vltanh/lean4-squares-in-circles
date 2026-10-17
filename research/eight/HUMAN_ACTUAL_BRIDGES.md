# Actual-contact bridges are radial and incident to the central square

## Theorem

Choose an eight-square radius minimizer with the fewest actual contacting
pairs. Its radius satisfies R<2 and it has a unique square C containing
the disk origin in its open interior. The analytical dependencies for
these statements are indexed in SMALL_STEP_ROADMAP.md.

Every bridge of the actual-contact graph is incident to C. More precisely,
choose either orientation of a bridge pair and any separating unit side
normal n supplied by the separating-axis theorem. If its contact line is

    n dot x=d,

then the perpendicular foot `d n` of the disk origin belongs to the actual
common contact set of that pair. In particular the line of action through
that point in direction n is radial.

This extends the physical stress-bridge lemma to actual bridges. It does
not require a positive stress weight on the bridge, or any particular
stress to be chosen.

## 1. Rotate one component about the disk origin

Let A-B be an actual bridge. Removing it partitions its connected component
into two nonempty sets of squares I and J, with A in I and B in J. The
only actual contact between the two sets is A-B. No square in this
component meets a square in another component. Thus every other relevant
cross-pair has a strictly positive distance between its closed squares.

Let K=A intersection B. For a separating unit side normal n directed from
A to B, K is the intersection of their support faces on the line
`n dot x=d`. It is a point or a segment. If the foot d n were not in K,
the continuous affine quantity `z cross n` would have one strictly
nonzero sign throughout K: it vanishes on that line only at the foot.

Rotate every square in J rigidly about the disk origin through a small
angle `epsilon t`, where epsilon is either 1 or -1 and t>0. All internal
pair relations in J are exactly preserved, as is disk containment. Leave
all other squares fixed. At a point z initially on the A-B contact, the
relative velocity is

    V_B(z)-V_A(z)=epsilon Jz,

and its separating normal component is

    n dot (V_B(z)-V_A(z)) = -epsilon (z cross n).          (1)

Choose epsilon to make (1) strictly positive on K. The strict contact
velocity lemma in HUMAN_CONTACT_EQUILIBRIUM.md, section 2, then makes the
pair strictly separated for all sufficiently small t>0. Only the pairwise
part of that lemma is used: circle containment here is preserved exactly
by rotation, so no strict circle derivative is required.

To recall its boundary justification, at a nonparallel edge-vertex contact
all active separating-branch derivatives equal the negative of (1) at
the common point. At a parallel edge contact, (1) is affine on the common
support line and is positive at both endpoints of K. If the two support
intervals are I_A,I_B, then for any affine L,

    min_(I_A intersection I_B) L
       = max(min_(I_A) L, min_(I_B) L).

One full support interval therefore has positive L. Choosing the rotating
normal with the corresponding owner gives strictly negative derivatives
for all active vertex inequalities of that branch. This includes a
single-point intersection of parallel edges and retains the normal-owner
rotation term. Inactive vertex inequalities persist by continuity.

Every other cross-pair stays at positive distance for sufficiently small
t, because it originally had positive distance and there are finitely many
pairs. The sole bridge contact has disappeared, no new contact appears,
and all squares remain in D_R. The packing still has minimum radius R,
or else contradicts minimality of R itself; in the former case its
contact count contradicts the chosen minimum. Hence the foot must be in K.

## 2. A radial actual contact below radius two has a central endpoint

For completeness, here is the geometric fact used to identify that endpoint.
Write the radial common point as `z=d n` with d>0 by changing the sign of
n and interchanging the endpoint labels if necessary. The outer square
lies in `n dot x>=d`, and the inner square lies in `n dot x<=d`.

Let rho=sqrt(R^2-1/4). The exact farthest-vertex formula for a square
of center p and frame e,f implies

    |p|^2+|p dot e|+|p dot f|+1/2 <= R^2,
    |p| <= rho-1/2.                                     (2)

Indeed `|p dot e|+|p dot f|>=|p|` and completing the square gives (2).
The radial point z is the nearest point of the outer square to zero.
Its inscribed disk of radius 1/2 therefore gives

    d <= |p_outer|-1/2 <= rho-1 < 1.                    (3)

Suppose the inner square omitted zero. In one of its signed side-frame
coordinates, its center has coordinate a>1/2. Call that signed axis e.
Every point of the inner square has strictly positive e coordinate,
so `n dot e=(z dot e)/d>0`. Since z supports the inner square in direction
n, its e coordinate must be maximal:

    z dot e=a+1/2>1.

This contradicts |z|=d<1. Thus the inner square contains zero in its
closed set.

There cannot be two distinct closed squares containing zero once C
contains it in its open interior: any such second square has interior
points arbitrarily close to zero, creating an open overlap with C.
Therefore the inner endpoint is C.

The case d=0 is impossible, since the foot would be zero and would belong
to both endpoint squares. This completes the theorem.

## 3. There are only eight possible central directions for a bridge

The theorem also gives a finite list of possible bridge directions in the
central square's frame, without discretizing any square orientation.
Direct the bridge normal n from C toward the outer square. Its radial
common point z supports C in direction n and satisfies z=d n, d>0.

If C's support face is an edge, n is one of its four signed side normals.
If the support face is a vertex v, radiality gives

    n=v/|v|.

There are four central vertices. Thus a bridge must use one of the four
central side-normal directions or one of the four radial directions to
its vertices. These are geometric directions determined by the actual
central square. Their values change with its center; no numerical angle
bins have been introduced.

Distinct bridges incident to C cannot have intersecting contact sets on C.
If their other endpoints A and B shared any such point, then A and B
would themselves touch, giving the cycle C-A-B-C and contradicting that
either incident edge is a bridge.

In particular no two bridges use the same radial foot. In the vertex case,
the separating normal is not a side normal of C; it must therefore be
owned by the outer square. In the edge case, no orientation agreement of
the outer square is asserted.

## 4. Interaction with a positive physical stress

Suppose an actual bridge has positive weight in a chosen physical stress.
It is then a bridge of the positive-stress graph as well, and its moment
is zero. Delete it and take the side J omitting C.

If J contains any positive-stress edge between its own squares, that edge
has nonzero moment. Otherwise its effective contact point would be radial
and section 2 would place C at one of its endpoints, impossible inside J.
The moment balance on J has no contribution from its single bridge to C.
Its nonzero internal moments consequently form a nonnegative circulation
and contain a directed exterior cycle. By the previously proved cross
exclusion, such a cycle uses at least five squares of J.

It follows that each positively stressed actual bridge has one of two
precise alternatives on its outer side:

* its outer endpoint is a leaf of the positive-stress graph; other actual
  contacts on that side, if present, may all have zero chosen weight; or
* its outer side contains at least five distinct squares and a directed
  exterior positive-moment cycle.

There can be at most one outer side of the second kind in an eight-square
packing, since different bridge sides are disjoint once their common
central endpoint is removed. This is an additional small branch reduction.
It does not bound zero-weight actual contacts by counting stress leaves.

## 5. What is still not a consequence

Together with HUMAN_CONTACT_COMPONENTS.md, every actual contact lies in
one connected cluster, and every bridge of that cluster attaches directly
to C. Every edge with two noncentral endpoints therefore belongs to an
undirected cycle of the full actual-contact graph.

Deleting C can destroy such a cycle. The resulting exterior graph is not
asserted to be connected or bridgeless. The central square may still be
isolated, and isolated exterior squares must still be included in the
packing constraints. Neither this bridge theorem nor the eight-direction
list proves the twin motif or the five projected inequalities.
