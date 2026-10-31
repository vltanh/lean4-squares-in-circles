# Full independent review: exterior-cycle boundary order and the diameter-chord load orbit

Reviewer: global_closure. Date: October 27, 2026.

**Decision: ACCEPT.** I read the entire source and its substantive
physical-embedding, angular-order, and original graph/load prerequisites.
No correction is required. This is a full mathematical and original-domain
audit, not a check of only the final numerical bounds.

Reviewed source:

    GENERAL_BOUNDARY_CHORD_OUTER_CYCLE_ORDER_EXCLUSION.md

Exact frozen SHA-256:

    13abf52906294b994c078598985d656b65d4267faa67a6b7b17ee8bc25c11273

The accepted new contribution is the stated exterior-cycle order theorem
and the entire original gate M6.B6.HEXAGON.D03.L0134. I have not changed
any ledger or promoted this to a whole six-body cell.

## 1. Sources read at their actual scope

I read all 220 lines of the proposed source, all of
PHYSICAL_BODY_GRAPH_UNCROSSING.md, the complete geometric angular
estimates and contact rule in CIRCLE_CONTACT_ANGULAR_ORDER.md, and
the one-square corner/resultant deviation proof in
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section 1.

I also read the complete actual exterior-face convention and the
single-diameter graph/load enumeration in
SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md, Sections 1--4.3.

The balanced-four-path force assumption of the last deviation source
is not imported: the used Section 1 is expressly a one-square physical
circle-corner statement. No loaded endpoint is assigned a degree-two
equation.

## 2. The simultaneous physical-spoke premise is available

The old uncrossing source provides more than abstract planarity or
exterior-face incidence. Its construction uses actual center/contact
strands, resolves the finitely many physical junctions compatibly with
their sector orders, and simultaneously retains disjoint center-to-circle
spokes for every physical boundary vertex.

I checked the geometric details used in the new restatement:

* A circle point cannot be shared. At a physical circle corner, both
  inward own directions have scalar product at most -1/2 with that
  corner, so the inward radial ray enters the open square.
* A center-to-circle-corner spoke has open part inside its own square.
  It cannot intersect another square's open strand or spoke.
* A pair-contact endpoint on the same center ray would have to be the
  same boundary point as the circle corner, which cannot be shared.
* All actual junctions are strictly inside the disk. Finitely many
  junction disks and parallel tubes can avoid the chosen spokes away
  from the incident centers.
* The resulting plane drawing is strictly inside the containing circle,
  and its chosen spokes connect its boundary vertices to distinct
  actual circle corners without meeting the drawing elsewhere.

These statements include shared-side endpoints, repeated physical
junctions, point-only contacts, and physical boundary bodies with zero
circle weight. No arbitrary drawing of the abstract graph replaces
this actual compatible embedding.

## 3. The topological order argument is complete

For an embedded simple cycle the inner Jordan curve and the containing
circle bound an annulus. Each selected spoke meets the inner boundary
only at its own vertex and ends on the outer circle. It consequently
lies in the exterior component of the cycle.

The pairwise disjoint spokes preserve cyclic endpoint order. Cutting
along one spoke turns the assertion into the noninterlacing property
of crosscuts in a disk; an inversion of endpoint order forces a crossing
by Jordan separation. This is a valid argument for the resolved
embedding and does not require contact points to be distinct before
resolution.

The result proves order of the chosen physical circle corners first.
It does not jump directly from an arbitrary contact drawing to the
order of center directions.

## 4. The center-direction transfer has strict room

Every distinct physical boundary-center pair has minor angular
separation greater than pi/5 by CIRCLE_CONTACT_ANGULAR_ORDER.md,
Lemma 2.1. Every physical circle corner is less than pi/12 from
its own center direction by the one-square estimate.

I reconstructed the latter estimate. With outward own coordinates
(a,b), a>=b>=1/2, a^2+b^2=q, the deviation tangent is

    sqrt(2*q-t^2)/(2*q-t), t=a+b.

Its derivative has the sign of 1-t; the admissible interval has t>1.
The maximum therefore occurs at b=1/2 and is
1/(2*sqrt(q-1/4)). The lower radius makes this strictly smaller than
2-sqrt(3)=tan(pi/12). Equal own coordinates are included by continuity.

The open center intervals of radius pi/12 are disjoint, since
pi/5-pi/6=pi/30>0. Moving each chosen corner direction inside its own
interval to its actual center direction cannot change cyclic order.
This handles wraparound and every physical two-corner choice. Other
physical boundary squares outside the chosen cycle do not affect
the required subsequence.

## 5. The skipped-chord obstruction is exact

The geometric contact rule supplies a strictly shorter than 2*pi/5
minor arc for any touching physical boundary pair, with no other
boundary center in that arc. It is force-free and applies to
zero-weight physical circle contacts as well.

By the preceding order transfer, if both open rim arcs between the
two chord endpoints contain a boundary vertex, both open circular arcs
between their center directions contain one. One of these is the
strict minor arc, contradicting its emptiness.

This use is valid in the stated radius window. The radius-free warning
that an unselected aligned 2x2 diagonal pair can touch while skipping
other centers is irrelevant here: the actual quantitative boundary
angle theorem supplies the empty minor arc, and the positive rim
uses the compatible selected embedding. Neither of those premises
is omitted.

## 6. Entire original D03.L0134 join

The original graph-cover source labels the actual exterior face
0,1,2,3,4,5, and includes positive chord03. This is not a freely
chosen hexagon drawing.

For the full load representative0134, all four of 0,1,3,4 are
physically boundary. The actual chord endpoints0,3 are separated
along the two open exterior-rim arcs by boundary vertices1 and4
respectively. The uniform theorem applies directly.

The complete original orbit is retained under its graph-preserving
symmetries. Endpoints0,3 keep their true degree three and their
original chord forces. Bodies2,5 are not inferred physically clear
from zero circle load. Their possible additional boundary contacts
only add vertices; they cannot remove1 or4 from the two arcs.
Every original mask, weight split, application, normal, and all
three completion squares remain in the contradiction.

No capacity hypothesis, deleted force, auxiliary stress or motion is
needed. This is the entire original gate, not a representative pose.

## 7. Independent exact arithmetic reconstruction

The source's angular comparisons have strict reserves. I independently
checked the following exact rational values:

| Comparison | Exact positive reserve |
| --- | --- |
| (79/40)^2 > 39/10 | 1/1600 |
| ((79/40)^2-2)^2 > 3 | 1567681/2560000 |
| Boundary-center small-angle corner bound 5/8 < 1 | 3/8 |
| Boundary-center mixed bound 1341/1600 < 1 | 259/1600 |
| Boundary-center upper bound 3721/4000 < 1 | 279/4000 |
| Contact-angle contradiction 275/128 > 2 | 19/128 |
| 1/5 > 1/6, in pi units | 1/30 |

The one-variable derivative identity was reconstructed directly.
These checks support the continuous proofs; no numerical pose or
sampled orientation is a premise.

The frozen source is accepted unchanged at its complete stated scope.
No claim is made for the other long-chord masks, other embeddings,
or the entire biconnected six-body parent.

