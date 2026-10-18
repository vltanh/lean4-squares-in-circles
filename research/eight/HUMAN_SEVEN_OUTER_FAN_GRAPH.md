# Complete actual-contact graph reduction when all seven exterior centers are outer

**Scope.** Consider an eight-square radius minimizer with the fewest
actual contacting pairs, and suppose its radius is below 2 and
all seven noncentral squares have center norm at least one.
The analytic central-square theorem supplies a unique central
square C containing the disk origin in its open interior.
An *actual edge* means the two closed squares meet, regardless
of any chosen contact stress multiplier.

**Theorem.** Exactly one of the following holds.

**Cycle case.** The induced graph of the seven outer squares
is the full seven-cycle in circular order. The entire
actual-contact graph consists of this ring, possibly with
some spokes to C; C may also be isolated. The ring's actual
contact polygon winds once about C, as established in
HUMAN_OUTER_GRAPH_REDUCTION.md.

**Path case.** The induced graph of the seven outer squares
is a disjoint union of simple paths and isolated vertices,
with at least one path containing an edge. Both endpoints
of every nontrivial outer path have actual contact with C.
Every simple cycle in the complete actual-contact graph
contains C and consists of C together with a subpath of
one of these outer paths whose endpoints contact C.
The one nontrivial actual-contact component contains C
and all nontrivial outer paths. Any other outer square
is either an isolated global vertex or is attached to C
by a single actual edge.

No assumption that an outer square touches the disk circle,
has a positive stress weight, or possesses a common frame
with another square is made.

## Proof

The private-ray and angular-order theorem
HUMAN_OUTER_CENTER_VISIBILITY.md proves that actual contacts
among outer squares join only circular neighbors.
Consequently their induced graph is a subgraph of
the simple seven-cycle. A subgraph is either the full
cycle or a union of paths and isolated vertices.
In the full-cycle case the only eighth vertex is C,
so the asserted graph description is immediate;
the winding statement is the previously proved
outer-cycle assertion.

Suppose the full seven-cycle is absent. Take an
endpoint A of any nontrivial induced outer path.
It has exactly one actual outer neighbor. If A had
no actual contact to C, then its degree in the
complete graph would be exactly one, with another
outer square as its unique neighbor. This
contradicts the actual-leaf theorem of
HUMAN_STRESS_GRAPH.md: in a minimum-contact
radius minimizer, the unique actual neighbor of
every leaf is the square containing the disk
origin in its open interior. Thus both endpoints
of every nontrivial outer path contact C.

There must be at least one outer edge. Otherwise
every actual edge has C as an endpoint, since there
are no other inner squares. Every nontrivial
component of the resulting actual-contact graph
would therefore be a star, hence a tree.
HUMAN_STRESS_GRAPH.md proves that a nontrivial
actual-contact component of a contact-minimal
radius minimizer contains a cycle. Such a
component exists by its shrinking argument.
This contradiction proves that the path case
contains at least one nontrivial outer path.

Each nontrivial outer path and C form a connected
subgraph: both endpoints are adjacent to C.
The uniqueness of the nontrivial actual-contact
component, established in HUMAN_CONTACT_COMPONENTS.md,
then puts all such paths in that same component.
A remaining outer vertex has no outer neighbors
by definition of an isolated vertex of the
induced graph. It can therefore be adjacent only
to C or to no vertex at all. This proves the
component statement.

Finally any simple cycle in the complete graph
which does not contain C would lie entirely
in the union of outer paths, impossible because
each is acyclic. A cycle containing C leaves
C along an edge into an outer path and cannot
move from one outer path to another without
returning to C, since there are no cross-path
outer edges. Simplicity forbids this intermediate
return. Hence its outer vertices form a single
subpath, and its two endpoints are C-neighbors.
Conversely each such subpath whose endpoints
are C-neighbors forms a simple cycle with C.
This proves the exact cycle description. QED.

## What this does not imply

The two C-neighbors at the ends of a path need
not carry positive stress; further contacts
from interior path vertices to C can occur.
Some whole outer vertices may be isolated in
the complete graph; they still occupy geometric
space. The theorem does not assert that the
cycle case is impossible below the candidate,
that a path has all its frames parallel,
or that the projected five-corner chain follows.

Thus the sharp unrestricted lower bound
R8>=Rhat still needs a quantitative inequality
for the seven-outer ring or these centrally
closed path components.


## Additional exact degree and bridge restrictions

The central square C **cannot have actual degree one** in
the chosen minimum-contact minimizer. Otherwise C itself
would be an actual leaf, whereas the leaf theorem makes
every leaf a square wholly omitting the origin. This
contradicts that C contains the origin in its open interior.

Consequently, in the seven-outer cycle case, C is either
isolated or has at least two distinct actual spokes to
the ring. There is no one-spoke version of that case.

In the path case, an outer vertex isolated in the induced
outer graph and adjacent to C is a leaf of the full graph.
The leaf theorem therefore gives its exact radial
configuration relative to C:

    center(leaf)= (sqrt(R^2-1/4)-1/2)*n,
    center(C)= (sqrt(R^2-1/4)-3/2)*n + t*Jn,  |t|<1/2,

where n is a signed side normal of C. In particular
there are at most **two** such isolated-outer C-leaves
in the entire graph, and if two exist their normals
are perpendicular. These statements concern all actual
edges, even when a contact has zero chosen stress weight.

There may nevertheless be additional **globally isolated**
outer squares; no upper bound on their count is deduced
from the leaf formula. Thus these refinements do not
assert a universal seven-cycle or the candidate's
interior twin motif.
