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
3. In the cycle case there are exactly six or seven outer squares. Every
   remaining unit is inside its contact polygon, with winding number one.
4. Every actual contact cycle of at most five squares includes an inner
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

## 2. The short-cycle capacity bound applies without a chosen stress

The needed geometric estimates from HUMAN_CYCLE_INTERIOR_CAPACITY.md do
not require stress weights once the polygon and winding assertions above
have been established. For completeness, their application here is short.

Let d_i<=sqrt(2) be the length of the chord in the i-th cycle square. Each
piece cut off by its chord line has area at least

    (d_i^2-1)_+/2.                                        (1)

For a chord joining adjacent square sides, with endpoint distances a,b
from their common corner, use a^2+b^2-ab<=1 on [0,1]^2. The corner
triangle has area ab/2, and the other piece has area at least 1/2.
For a chord joining opposite sides, write endpoints (0,a),(1,b). Its
smaller cut piece has area

    min(a+b,2-a-b)/2 >= |a-b|/2 >= (a-b)^2/2.

These prove (1); for d_i<=1 it merely says that area is nonnegative.

If d_i>1, the chord crosses its square's open interior. No other polygon
edge enters that interior. The open piece on the left of the oriented
chord therefore lies inside P: winding increases by one across that chord,
and a simple positively oriented polygon has winding zero or one.
The left pieces are mutually interior-disjoint, and disjoint from the
8-k whole noncycle units. Consequently

    8-k + (1/2) sum_i (d_i^2-1)_+ <= area(P).            (2)

The polygonal area inequality proved by the finite Fourier calculation in
HUMAN_CYCLE_INTERIOR_CAPACITY.md is

    area(P) <= C_k sum_i d_i^2,
    C_k=(1/4)cot(pi/k).                                  (3)

That calculation applies to any closed polygonal path and thus certainly
to P. Combining (2)--(3), with 0<=d_i^2<=2, gives

    8-k <= k max(C_k,2C_k-1/2).                          (4)

For k=3,4,5, the right side is respectively less than one, equal to one,
and less than two. For the last comparison, tan(pi/5)>5/8 implies
C_5<2/5<1/2. The elementary proof uses

    tan x >= x+x^3/3,       pi/5>3/5,
    tan(pi/5)>84/125>5/8.

In every case k<=5, (4) contradicts 8-k>=3. A cycle must therefore have
k=6 or k=7. No positive-moment orientation assumption has been used.

For k=6, (4) permits two inner units; it does not exclude them. For k=7
there is just the central unit inside. These two alternatives must still
be handled quantitatively in a sharp proof.

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

## 4. The five-cycle case necessarily includes a near-center square

Suppose an actual contact cycle of length at most five contained only
outer squares. It would be a cycle in the induced outer graph. By section 1
it would have to be that entire graph's cycle, so k would be at most five.
Section 2 excludes this. Therefore every such actual cycle has an inner
vertex S with center norm less than one.

If the cycle is exterior, S is not C and its closed square omits zero.
Its inscribed disk of radius 1/2 lies in S, so

    0 < dist(0,S) <= |p_S|-1/2 < 1/2.                    (5)

In a radius minimizer this square is also strictly inside D_R, by section 3.
This strengthens HUMAN_CYCLE_BOUNDARY_COUNT.md for exterior five-cycles:
the guaranteed interior vertex can be taken to have center norm below one,
not merely to miss the containing circle.

The distinction matters for the earlier transmitter argument. Throughout
the relevant radius range,

    sqrt(R^2-1)-1 > 1/2,

since R>sqrt(2)+1/2 implies R^2>13/4. Thus the square in (5) is on the
opposite side of the distance threshold in
HUMAN_OUTER_INTERIOR_TRANSMITTER.md. That theorem cannot be applied to this
guaranteed vertex. Its actual degree might be two or might be larger;
the near-center attachment and occupancy argument remains necessary.

There is no additional alternative in which a short all-outer cycle sits
inside a longer induced outer cycle: a subgraph of a simple cycle has no
proper cycle. This is why the inner vertex conclusion is unconditional
under the displayed packing hypotheses.

## 5. What is now reduced, and what remains

The reduction replaces a general exterior-contact graph by a cyclic graph
on outer centers together with the inner units and their attachments.
The cases are exactly:

* a six-outer cycle enclosing two inner units;
* a seven-outer cycle enclosing C;
* outer paths and isolated outer vertices, with every nontrivial path
  attached to inner units at both ends in the contact-minimal representative.

The cases do not assert a particular number of inner units in the path
alternative. Isolated outer units, inner-inner contacts, repeated inner
attachments, and zero-weight actual contacts are retained.

To obtain R8>=Rhat one must still prove the sharp bound in the two long-cycle
cases and for the paths with inner attachments, or a single inequality
covering them. None of (1)--(5) supplies those sharp estimates. This note
records the graph reduction, not closure of the unrestricted theorem.
