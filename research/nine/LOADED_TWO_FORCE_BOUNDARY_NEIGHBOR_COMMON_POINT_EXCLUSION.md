# A loaded two-force tip cannot apply its other force at a point of its boundary neighbor

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed uniform hand theorem, submitted for full
independent review.** This strengthens the previously proved common
strict-hub-vertex obstruction throughout the original radius window.
It removes the hub-vertex, hub-owner, and hub-degree premises and
retains every original variable shared-side mean.

## 1. Exact unchanged physical theorem

Let U,V,W be distinct actual closed unit squares with pairwise disjoint
open interiors, contained in the same disk of positive radius R, where

    R^2>=13/4.                                         (1)

The actual V has positive total circle load and its complete positive
pair neighborhood is exactly U,W. The actual W physically touches
the containing circle. Its degree, circle weights and other forces
are arbitrary, as are the degree and load of U. Retain every original
force magnitude, separating normal, singleton application or complete
side mean, all physical circle corners, all individual zero corner
coefficients, additional contacts, and every other packing unit.

Let P be the unchanged original U-V application or shared-side mean.

**Theorem.** P does not belong to the actual W.

In particular, if U has a retained physical contact with W, its
original U-W application cannot coincide with P. This conclusion
has no own-axis or strict-vertex hypothesis at U, V, or W. The U-W
contact need not carry positive force for the first theorem, and
no force or torque equation at U or W is used.

The theorem forbids the original application P from lying in W.
It does not claim that U,V,W can have no other physical common
point when an original U-V side mean is elsewhere on its segment.

## 2. Complete actual intersection cover

Suppose for contradiction that P belongs to W. It already belongs
to U and V by its original contact meaning. The actual convex V-W
intersection is a singleton or a closed segment, because their open
interiors are disjoint.

If the intersection is the singleton {P}, the unchanged positive
V-W application is also P. Both original pair-force applications
of V coincide, and W is physical boundary. The complete theorem
LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md excludes this:
(1) gives R>3/2, with no unproved leaf or normal-owner substitution.

Suppose the intersection has positive length. It lies on a side of
each unit, so their actual frames are parallel. At a point in its
relative interior, the two opposite open half-plane tangent sectors
leave no two-dimensional tangent sector for U. Thus P is an endpoint
of the actual shared segment.

At least one of V,W has P as a vertex. If both do, their unit sides
extend from P in the same direction and hence coincide for their
whole length. The complete full-shared-side boundary lemma, Section 2
of BOUNDARY_TWO_FORCE_TIP_NO_COMMON_STRICT_HUB_VERTEX.md, applies
at true V2 with its original U-V endpoint P and unchanged V-W mean.
Its only radius premise is R>sqrt(2), supplied by (1). It gives a
torque contradiction without a strict-hub-vertex premise. Both
physical boundary units and every circle-weight endpoint remain.

It remains to exclude exactly the two partial shared-side cases:
P is a vertex of V and side-interior in W, or the reverse. The
following arguments cover every original V-W mean on that segment.

## 3. P is a vertex of V and side-interior in W

Rotate and, if necessary, reflect the entire unchanged configuration
about the circle origin. Put the common side horizontally, V above W,
and P at V's left endpoint. The exact actual squares have the form

    V=[a,a+1] x [b,b+1],
    W=[c,c+1] x [b-1,b],
    a-1<c<a, P=(a,b).                                 (2)

The two occupied tangent sectors at P consist of the upper-right
quadrant from V and the lower half-plane from W. A square containing
P has a tangent sector of angle at least pi/2. To avoid those occupied
open sectors, the actual U must occupy exactly the upper-left quadrant
and have their parallel frame. Consequently

    U=[a-1,a] x [b,b+1].                               (3)

Thus the actual V-to-U normal is West, and V-to-W is South. They
are the original normals: a positive-length intersection forces a
supporting normal perpendicular to the whole segment, including when
the original mean is an endpoint. Write their positive magnitudes
as mu,nu. The complete original V force gives its full circle resultant

    m_V=(mu,nu), mu,nu>0.                              (4)

### 3.1. The full circle mask fixes only the needed signs

Equation (4) forces

    a>=-1/2, b>=-1/2.                                 (5)

Indeed, if a<-1/2, every physical farthest corner of the actual V
has negative horizontal coordinate a, so every nonzero positive
circle resultant has negative horizontal component. This contradicts
(4). The same argument excludes b<-1/2. Equality in either coordinate
is retained and corresponds to two actual circle corners, with their
full original coefficients.

For every actual mask allowed by (5), the farthest-corner squared
norm is exactly

    R^2=(a+1)^2+(b+1)^2.                              (6)

There is no unique-corner assumption in (6): at a=-1/2 or b=-1/2,
one may have a tied farthest coordinate, but its squared value is
still the one printed.

### 3.2. The original mean and torque force b>0

The unchanged V-W application is M=(m,b), with

    a<=m<=c+1<a+1.

The unchanged U-V application is P=(a,b), not a newly selected
point on the full U-V side. Every circle atom has zero moment
about the original origin. The full true V2 torque is therefore

    mu*b-nu*m=0.                                      (7)

If b<=0, (7) gives m<=0 and hence a<=0. Equations (5),(6) would
then give R^2<=2, contrary to (1). Consequently b>0. This argument
keeps both endpoints of the entire mean interval and all circle
coefficient endpoints; no selected coefficient is divided out.

### 3.3. Every actual W corner is strictly inside the circle

If a>=0, every horizontal coordinate of W has absolute value
strictly below a+1, by a-1<c<a. Every vertical coordinate of W
has absolute value strictly below b+1, because b>0. Thus every
W corner has squared norm strictly less than (6), contradicting
its physical circle contact.

If -1/2<=a<0, (a+1)^2<1. Equations (1),(6) imply

    (b+1)^2>9/4, so b>1/2.

Every horizontal coordinate of W now has absolute value strictly
below 1-a; its vertical absolute value is at most b. Therefore

    max_(z in W) |z|^2 < (1-a)^2+b^2,

whereas

    R^2-[(1-a)^2+b^2]=4*a+2*b+1>0.                    (8)

The last strict sign holds even at a=-1/2, since b>1/2. Again
the whole W is strictly inside the circle. This contradiction
excludes the entire first partial shared-side case, including all
physical V masks and the endpoint R^2=13/4.

## 4. P is side-interior in V and a vertex of W

Use the same global horizontal convention, now putting P at the
left endpoint of W's upper side. The exact actual squares are

    V=[a,a+1] x [b,b+1],
    W=[c,c+1] x [b-1,b],
    a<c<a+1, P=(c,b).

The remaining tangent sector forces the actual U to be

    U=[c-1,c] x [b-1,b].

Both actual V pair normals are South. Their original magnitudes
remain positive, so full V force gives a nonzero North circle
resultant. The actual V horizontal center must therefore be zero:
otherwise every one of its physical farthest corners has the same
strict horizontal sign, which cannot cancel in a nonzero positive
circle resultant. Hence a=-1/2.

Likewise the vertical center cannot be negative. If it were zero
as well, the entire square would have farthest radius sqrt(1/2),
contrary to (1). Thus b+1/2>0, and actual physical boundary contact
gives

    V=[-1/2,1/2] x [d,d+1],
    b=d=sqrt(R^2-1/4)-1>=sqrt(3)-1>1/2.               (9)

This is a classification forced by the actual full circle resultant,
not an inserted leaf or equality of selected applications. The two
physical outer circle corners remain; their full original coefficients
give the zero horizontal resultant required above.

The original W now has -1/2<c<1/2 and vertical interval [d-1,d].
Its maximum horizontal absolute coordinate is strictly below 3/2,
and its maximum vertical absolute coordinate is d. Consequently

    max_(z in W)|z|^2 < 9/4+d^2
                      < d^2+2*d+5/4=R^2,             (10)

where the strict second inequality is exactly 2d>1 from (9).
Thus W cannot physically touch the circle. This excludes the entire
second partial shared-side case. No torque equation or particular
V-W mean was required here; the full original V force already suffices.

## 5. Whole-domain conclusion and broad original consequences

Sections 2--4 exhaust the actual V-W intersection, including all
singleton contacts, partial or full shared sides, and every possible
location of the original P on them. Each leads to a contradiction.
Therefore the original U-V application P is not a point of W.

The entire PR radius window 79/40<=R<=sqrt(1105)/16 satisfies (1).
The result applies to every twelve-row graph interface listed in
BOUNDARY_TWO_FORCE_TIP_NO_COMMON_STRICT_HUB_VERTEX.md with its
strict-U-vertex restriction removed. In particular:

* Every listed D02, D0203, D0204, D0235, chord-path and central-
  triangle application keeps the real U degree three or four and
  every original normal owner and mean.
* In every lower TDC.S or TDC.D house, take U=A, V=T, W=D.
  The actual AT and AD applications cannot coincide, without any
  near-port, A-owner, root-frame, or concurrence premise. T remains
  true loaded degree two and D remains true loaded degree three.
* More generally, every actual positive triangle with a loaded
  degree-two tip and a physical-boundary return has distinct
  applications of its two hub contacts, even when a V-W side mean
  differs from a shared physical junction.

These are complete original common-application feature exclusions.
They do not exclude an arbitrary noncoincident triangle, do not
assert that every remaining contact is a physical singleton, and
do not supply a fixed-tip selector's missing singleton premise.
No original whole-family gate is closed solely by this new theorem.

## 6. Exact mathematical inputs and proof limits

| Source | SHA256 | Exact use |
|---|---|---|
| LOADED_COINCIDENT_PORT_STAR_NO_BOUNDARY_NEIGHBOR.md | 18ad8dbde48a1c0ef6828ef199a321c54218e5ba3c39c4047025783ffb63bb83 | Complete actual singleton-intersection case with true loaded V2 and physical boundary W |
| BOUNDARY_TWO_FORCE_TIP_NO_COMMON_STRICT_HUB_VERTEX.md | 5edbfff40e364317e83c4111ff3b0c3ed3cae102211d5fc869994e9659fceb70 | Section 2's complete local full-shared-side boundary lemma only; the new theorem does not assume its global strict-vertex premise |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full V force/torque and radial circle atoms |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph/load joins already listed in the strict-feature source |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original lower-house T2,D3,A3 joins |

The two new partial shared-side arguments are proved in full above.
The radius threshold is a convenient uniform sufficient condition;
no claim that it is best possible is made. All other physical units
remain. No numerical pose, angle mesh, computational exclusion
certificate, normal reselection, deleted force, changed mean,
Lean compilation, CI, workflow dispatch, or merge is used.
