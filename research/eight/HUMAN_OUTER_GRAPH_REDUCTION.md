# A contact-graph reduction at center radius one

## Scope and statements

Call a square outer when its center has norm at least one, and inner when
its center has norm less than one. These definitions refer to the disk
origin, not to another square's center. They are not synonymous with
circle-contact and circle-free. In particular some circle-free squares are
outer, and an exterior square can be inner.

For any packing of eight unit squares in D_R with R<=sqrt(98/25), the
following assertions hold:

1. There is at least one inner square: the unique open central square C.
2. The actual-contact graph induced by all outer squares is either a
   disjoint union of paths and isolated vertices, or a single cycle.
3. In the cycle case there are exactly seven outer squares. The remaining
   unit is C, its center has norm strictly less than 1/2, and its open
   interior has winding number one about the contact polygon.
4. Every actual contact cycle of at most six squares includes an inner
   square. If such a cycle is exterior, this is a noncentral square at
   distance strictly less than 1/2 from zero.

For a minimum-radius packing chosen to have the fewest actual contacts,
there is the additional assertion:

5. Each endpoint of every nontrivial outer path touches at least one inner
   square. Every inner square is strictly inside the containing circle.
   An internal outer-path vertex with no inner neighbor has actual degree
   two; when it is circle-free, the existing opposite-contact alignment
   theorem applies to it.

These are exhaustive graph alternatives, not a completed radius bound.
An isolated outer vertex can have inner neighbors or can be isolated in the
whole actual graph. The statements do not discard it.

The earlier version of this note retained a six-outer cycle enclosing two
units. HUMAN_RADIAL_ESCAPE.md now excludes that case. The proof below
incorporates its stronger enclosure bound; it does not assume that two
interior squares can be replaced by a solid convex hull.

## 1. Central square and cyclic order

The analytic central-square theorem supplies C containing zero in its open
interior. In its own frame its center has both absolute coordinates below
1/2, so |p_C|<1/sqrt(2)<1. Thus C is inner and the number k of outer squares
is at most seven.

HUMAN_OUTER_CENTER_VISIBILITY.md proves that an outer square's positive
center ray misses every other outer square. It also proves that the segment
from zero to any packed center misses every different outer square.
Consequently, for k>=3, an outer square can touch only its two circular
neighbors in the order of the outer center directions. The induced graph
is a subgraph of that k-cycle. A proper subgraph consists of paths and
isolated vertices; if it contains a cycle, it is the full k-cycle.
For k<=2 it has no graph cycle and is already of the stated path form.

When the full cycle exists, select one common contact point z_i for each
successive pair. Each z_i is in the open angular gap between the two
corresponding center directions. All these gap intervals are distinct,
so all contact-point directions are distinct as well. Inside each square,
join its two successive contact points by their chord. Their angular
difference is positive and at most pi/2, since both are in the square's
angular shadow, which has length at most pi/2. In particular their angular
difference is less than pi, and argument strictly increases along each chord.

The chords occupy disjoint successive angular sectors, except for their
common endpoints. They therefore form a simple polygon P with winding one
about zero. This proves simplicity here; it is not an assumption about
arbitrary square contact graphs or about arbitrary moment cycles.

Every noncycle square has its center joined to zero by a segment missing
all cycle squares. Its open interior is connected and avoids every closed
cycle square. Hence the winding is one throughout its open interior.
All 8-k noncycle units lie inside P, up to boundary points.

## 2. Radial escape leaves exactly seven outer units

The radial-escape theorem applies to a unit square S in D_2 and a disjoint
open disk of radius 1/2 centered at p with |p|>=1/2. It says that the closed
square S misses the entire outward ray {t p:t>=1}.

Apply it to the inscribed disk of any noncycle square T and to each square
used by P. If |p_T|>=1/2, this ray would connect p_T to infinity without
meeting P. The winding number of P at p_T would then be zero, contradicting
section 1. Thus every noncycle unit satisfies

    |p_T|<1/2.                                           (1)

Two different noncycle units would have center distance less than one by
the triangle inequality. Their open inscribed radius-1/2 disks would
intersect, contradicting the packing condition. Consequently

    8-k<=1.

Since k<=7 already, k=7. The sole remaining unit is C and (1) gives the
stated bound on its center.

This argument is stronger than the earlier area-capacity calculation,
which gave only k>=6. It excludes all k<=6 at once, in particular the
six-outer-cycle case with two enclosed units. It relies on a clear ray
of points, not on an asserted collision-free translation of a whole square.

## 3. Attachments in a contact-minimal radius minimizer

The existing analytic radius bounds place the attained eight-square
minimum in

    sqrt(2)+1/2 < R_8 < 2.

If a center has norm less than one, every point of its unit square has
norm less than 1+1/sqrt(2). Since

    1+1/sqrt(2) < sqrt(2)+1/2,

every inner square is strictly inside the containing circle.

Now take a nontrivial path component of the induced outer graph and one
of its endpoints S. It has exactly one outer neighbor. If it had no inner
neighbor, it would have actual degree one in the whole packing, with an
outer square as its sole neighbor. The actual-leaf theorem in
HUMAN_STRESS_GRAPH.md says that every actual leaf in this contact-minimal
representative has the central square C as its neighbor. Since C is inner,
this is a contradiction. Thus each path endpoint has an inner neighbor.

An internal vertex of such a path has exactly two outer neighbors. With
no inner neighbor it therefore has actual degree two. If it is strictly
inside the circle, HUMAN_CYCLE_ANALYSIS.md, section 8, makes its separating
normals opposite and aligns its own side normal with them.

The same observation applies to an outer-cycle vertex having no inner
neighbor: circle-free vertices of actual degree two are transmitters.
A vertex with an inner attachment need not have degree two, whether or not
that attachment has positive weight in a chosen stress.

## 4. Every cycle of at most six units includes a near-center square

Suppose an actual contact cycle of length at most six contained only
outer squares. It would be a cycle in the induced outer graph. By section 1
it would have to be that entire graph's cycle, so k would be at most six.
Section 2 excludes this. Therefore every such actual cycle has an inner
vertex S with center norm less than one.

If the cycle is exterior, S is not C and its closed square omits zero.
Its inscribed disk of radius 1/2 lies in S, so

    0 < dist(0,S) <= |p_S|-1/2 < 1/2.                    (2)

In a radius minimizer this square is also strictly inside D_R, by section 3.
This strengthens HUMAN_CYCLE_BOUNDARY_COUNT.md: it applies to an exterior
six-cycle as well as a five-cycle, and the guaranteed interior vertex has
center norm below one, not merely a square missing the containing circle.

The distinction matters for the earlier transmitter argument. Throughout
the relevant radius range,

    sqrt(R^2-1)-1 > 1/2,

since R>sqrt(2)+1/2 implies R^2>13/4. Thus the square in (2) is on the
opposite side of the distance threshold in
HUMAN_OUTER_INTERIOR_TRANSMITTER.md. That theorem cannot be applied to this
guaranteed vertex. Its actual degree might be two or might be larger;
the near-center attachment and occupancy argument remains necessary.

There is no alternative in which a short all-outer cycle sits inside a
longer induced outer cycle: a subgraph of a simple cycle has no proper
cycle. This is why the inner vertex conclusion is unconditional under
the displayed packing hypotheses.

## 5. Unused exterior units have winding zero for every exterior moment cycle

The same radial-escape argument sharpens
HUMAN_CYCLE_INTERIOR_CAPACITY.md independently of the center-one graph.
Let gamma be a directed positive-moment cycle of exterior units. Its
winding number is positive throughout the open central square C, by
HUMAN_GLOBAL_CYCLE_CLOSURE.md. Every unused exterior unit T has
|p_T|>=1/2 because its inscribed disk does not contain zero. Its outward
center ray misses every unit used by gamma. Therefore

    winding(gamma,int(T))=0.                            (3)

This holds for any length of exterior moment cycle, including six.
It improves the old allowance of a second enclosed whole unit in the
six-cycle case. It does not bound repeated winding about C: the radial
argument counts distinct enclosed units, not winding multiplicity.

For completeness, in the present setting |p_T|=1/2 would already put
zero in the closed inscribed disk of T and hence in T, impossible since
C contains zero in its open interior. The weak inequality above is enough
for the radial-escape theorem.

## 6. What is now reduced, and what remains

The reduction replaces a general exterior-contact graph by a cyclic graph
on outer centers together with the inner units and their attachments.
The two exhaustive alternatives are:

* a seven-outer cycle enclosing C, whose center has norm less than 1/2;
* outer paths and isolated outer vertices, with every nontrivial path
  attached to inner units at both ends in the contact-minimal representative.

The path alternative does not assert a particular number of inner units.
Isolated outer units, inner-inner contacts, repeated inner attachments,
and zero-weight actual contacts are retained. Every exterior actual cycle
of length at most six must pass through a noncentral inner unit, and all
unused exterior units have winding zero about an exterior moment cycle.

To obtain R8>=Rhat one must still prove the sharp bound for the seven-cycle
and for the paths with inner attachments, or a single inequality covering
both. None of (1)--(3) supplies those sharp estimates. This note records
the graph reduction, not closure of the unrestricted theorem.
