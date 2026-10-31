# Boundary chords preserve the physical exterior-cycle order

**Status: complete proposed geometric theorem and complete original
`M6.B6.HEXAGON.D03.L0134` exit; frozen for full root and independent
review.** This source does not change any shared ledger.

Work in the declared radius window

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
 \tag{1}
\]

All squares are actual unit squares with disjoint open interiors in
the same containing disk. A boundary square means a physically
circle-touching square, including one whose circle multiplier is zero.
Use the selected compatible positive body-graph embedding of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Sections 5--6.

## 1. Statement, with the embedding premise retained

Let \(C\) be a simple cycle in that actual plane embedding. Assume
that every physical boundary vertex of \(C\) has its chosen circle
spoke on the exterior side of \(C\). This premise holds in particular
when \(C\) is the actual exterior boundary cycle of a biconnected
positive component.

**Theorem.** The circular order of the boundary-square center
directions is the order of those vertices along \(C\), up to a common
reversal. Consequently, if two boundary vertices \(i,j\) of \(C\)
physically touch, at least one of the two open \(i\)-to-\(j\) cycle
arcs contains no other boundary vertex.

In particular a positive chord between two boundary vertices cannot
have another boundary vertex on each of its two exterior-rim arcs.
No force equation at a chord endpoint is shortened. Indeed, after the
compatible selected embedding has been fixed, the argument uses only
actual circle contacts and actual pair contacts.

The theorem does not assert a cyclic order for an arbitrary drawing
of the abstract graph. The simultaneous physical spokes in the
selected embedding are part of its premise and proof.

## 2. The selected embedding has simultaneous unshared circle spokes

Here are the precise facts supplied by
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Sections 5--6.

Draw each positive pair edge initially from one actual square center
to its actual aggregate contact point and then to the other center.
Each open half-edge is in its square's open interior. The selected
junction graphs admit compatible local resolutions in their actual
sector order. Small junction disks and center-to-contact tubes then
give a plane embedding of the positive body graph.

A circle point cannot be shared by two packing squares. To see this,
at a circle corner \(z\), let \(w_1,w_2\) be the two orthonormal
inward side directions. Containment of the adjacent corners gives
\(z\cdot w_j\le-1/2\). Thus \(-z\) has strictly positive
components in both inward directions, and a short radial segment
from \(z\) toward the origin lies in the square's open interior.
Two squares sharing \(z\) would therefore overlap openly.

For each physical boundary square in the positive graph, choose any
one of its physical circle corners \(z_i\). Join its center \(c_i\)
to \(z_i\). The open spoke lies inside that square. Two such spokes
are disjoint. A spoke meets the initial center/contact drawing only
at its own center: distinct rays from that center are disjoint, and
a contact endpoint on the same ray would have to be the unshared
circle corner itself.

The finitely many local junction disks and tube perturbations can be
chosen to avoid all these spokes away from their incident centers.
The completed plane graph lies strictly inside the containing disk,
and the same simultaneous spokes remain disjoint from it except at
their incident centers. This is the stronger construction explicitly
proved in Section 6 of the cited source; merely knowing that every
boundary vertex is incident to an exterior face would not replace it.

The construction retains a physical two-corner square and permits an
arbitrary choice of either corner. It does not depend on which of
those circle multipliers are positive.

## 3. Disjoint spokes preserve the boundary order

The embedded simple cycle \(C\) is a Jordan curve contained strictly
inside the containing circle. Its exterior within that circle is a
closed annulus, with the two boundary curves understood separately.
For every chosen boundary vertex on \(C\), its spoke starts there,
ends on the containing circle, and otherwise avoids \(C\). Since
the endpoint is outside the Jordan curve, the entire open spoke is
on the exterior side. The spokes are pairwise disjoint.

Disjoint arcs across an annulus preserve the cyclic endpoint order.
For completeness, cut the annulus along one of the spokes. The result
is a topological disk with an inner-boundary interval and an
outer-boundary interval. If two of the remaining disjoint arcs
reversed their endpoint order between those intervals, one such arc
together with the relevant boundary interval would separate the two
endpoints of the other. The latter arc would have to cross it, by
the Jordan separation theorem. This is impossible. The resulting
linear order, and hence the original cyclic order, is preserved.

Therefore the chosen physical circle corners \(z_i\), for boundary
vertices of \(C\), occur on the containing circle in the same cyclic
order as those vertices on \(C\), up to orientation.

This argument is applied to the already resolved compatible embedding.
Coincident physical contact points do not create coincident cycle
vertices or a crossing of the spokes. There is no limiting assumption
that would discard weak contact junctions or shared-side endpoints.

## 4. Circle-corner order is actual center order

Two previously proved force-free estimates have exactly the required
scope:

1. `CIRCLE_CONTACT_ANGULAR_ORDER.md`, Lemma 2.1: distinct physical
   boundary centers have minor angular separation strictly greater
   than \(\pi/5\).
2. `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`, Section 1: every
   physical circle corner has angular distance strictly less than
   \(\pi/12\) from its own center direction. That section is a
   one-square theorem and uses no path, force, or degree premise.

The latter estimate can also be checked directly here. Choose outward
own-axis coordinates at a circle corner and exchange the axes so that

\[
 z=(a,b),\quad a\ge b\ge\frac12,\quad
 a^2+b^2=q=R^2,\quad c=(a-\tfrac12,b-\tfrac12).
\]

The acute angular deviation satisfies

\[
 \tan\delta=\frac{a-b}{2q-a-b}.
\]

For fixed \(q\), putting \(t=a+b\) writes the last quotient as
\(\sqrt{2q-t^2}/(2q-t)\). Its derivative has the sign of \(1-t\),
which is negative throughout the nondegenerate interval. The maximum
is therefore at \(b=1/2\), and equals
\(1/(2\sqrt{q-1/4})\). Since the whole window has
\(q>2+\sqrt3\), this is strictly below
\(2-\sqrt3=\tan(\pi/12)\). Continuity includes \(a=b\).

Around each actual boundary center direction put its open interval
of radius \(\pi/12\). These intervals are pairwise disjoint,
because two such radii total \(\pi/6<\pi/5\). Every chosen circle
corner lies in its own interval. Moving each chosen direction within
its own interval to the center direction cannot change their cyclic
order. Section 3 therefore proves the first assertion of the theorem.

Additional physical boundary squares outside \(C\) do not affect
this subsequence argument. Additional boundary vertices of \(C\)
with zero circle weight are included throughout.

## 5. A boundary contact cannot skip boundary vertices on both rim arcs

`CIRCLE_CONTACT_ANGULAR_ORDER.md`, Lemma 3.1 and Theorem 3.2, prove
that two touching physical boundary squares have minor center angle
strictly below \(2\pi/5\), and the corresponding open minor arc
contains no other physical boundary center direction.

The empty-arc conclusion follows immediately from the two numerical
angle estimates: an intermediate boundary center would have a gap
greater than \(\pi/5\) to each endpoint, while the sum of those gaps
would be less than \(2\pi/5\). These estimates use no force balance,
normal selection, or positive circle multiplier.

If both open cycle arcs from \(i\) to \(j\) contained a boundary
vertex, Section 4 would put a boundary center on each of the two open
circular arcs between their center directions. In particular the
minor arc would contain one, contradicting the empty-arc rule.
This proves the second assertion and the chord consequence.

## 6. Complete original single-long-chord hexagon join

The exact graph and retained-domain source is
`SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`. Its labels are the actual
exterior face \(0,1,2,3,4,5\), not a freely chosen graph drawing.
For the single long chord \(03\), the original four-load representative
\(0134\) has positive circle loads at \(0,1,3,4\).

Thus \(0,1,3,4\) are all actual physical boundary squares. The
positive chord \(03\) is an actual contact. Its two open rim arcs
contain, respectively,

\[
 0-1-2-3:\quad 1,\qquad
 0-5-4-3:\quad 4.
\]

The theorem therefore gives an immediate contradiction. The entire
original gate

\[
 \boxed{\texttt{M6.B6.HEXAGON.D03.L0134}}
\]

is excluded, with every graph-preserving image included. Bodies
\(0,3\) retain their original degree three and the chord force.
Bodies \(2,5\) are not assumed physically circle-clear merely
because their circle loads vanish. Their possible additional circle
contacts only add boundary vertices and do not remove \(1\) or
\(4\) from the two rim arcs.

Every original frame, physical circle mask, individual zero corner
weight, shared-side aggregate mean, selected normal, positive force,
and all three original extra squares remains in the domain. No
completion square is moved or discarded, and no separate cap bound
is needed. The same-nine lower-radius theorem places any prospective
nine-packing counterexample in (1); the geometric argument itself
holds on the full declared window (1).

Only the displayed original gate is assembled here. The other
single-long-chord load representatives, the other chorded graphs,
non-hexagonal embeddings, and the coarse six-body cell are not
declared closed by this source.
