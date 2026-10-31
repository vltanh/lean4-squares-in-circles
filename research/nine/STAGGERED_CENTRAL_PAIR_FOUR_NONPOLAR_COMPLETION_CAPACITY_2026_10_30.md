# The central-pair capacity theorem retains arbitrary small vertical stagger

Date: October 30, 2026 UTC.

**Status: proposed exact corollary of the complete near-central rectangle
capacity proof, awaiting independent review. No original gate is changed.**

The two opposite application means of an unloaded true-degree-two
square can lie on one line without that line passing through the
square's center. Consequently neighboring such transmitters need not
have equal center heights. The theorem below explicitly keeps their
two distinct actual heights.

## 1. Statement

Let all actual unit squares be interior-disjoint and contained in the
disk about O of squared radius at most Q=1105/256. In one common
orthonormal frame suppose two of the actual squares are axis-aligned
and have centers

    (s-1/2,y1), (s+1/2,y2),
    |s|<=1/12, max(|y1|,|y2|)<=1/12.                       (1)

Put

    d=max(|y1|,|y2|), delta=1/2-d in [5/12,1/2].            (2)

Then at most four of the other actual units E can satisfy

    max(|c_E.u_E|,|c_E.v_E|)<=1-d.                         (3)

The axes u_E,v_E are E's own axes and the center coordinates are
relative to the unchanged origin O. Every completing square retains
its arbitrary independent orientation, contacts and physical mask.

The assumption y1=y2 is absent. In particular the statement is
available to a genuine axial channel once its two internal centers
have the bounds in (1), without moving either unit or replacing its
actual mean by its center.

## 2. A rectangle covered by the two original units

Let y_hi=max(y1,y2), y_lo=min(y1,y2). The union of the two actual
units contains the rectangle

    C0=[s-1,s+1] x [y_hi-1/2,y_lo+1/2].                    (4)

This follows by taking their actual overlapping vertical interval.
The lower endpoint in (4) is at most -delta and the upper endpoint
is at least delta. Thus D_delta is contained in C0. Its horizontal
half-width is one, and its central horizontal coordinate is s.

Every other square's open interior misses int(C0). An open overlap
would contain a point off the internal line x=s and hence overlap
one of the two original unit interiors. This argument does not claim
that their whole nonconvex union equals its convex hull.

## 3. Exact separating-axis routing

For a separating normal n directed from C0 to E, its full support
value has the bound

    H_C0(n)>=(1-|s|)|n_x|+delta*|n_y|>=delta.               (5)

Since 1-|s|>=11/12>delta, equality requires n_x=0. If the actual
separating axis is owned by E, its minimum-support value is at most
`(1-d)-1/2=delta`, by (3). Thus the separation is possible only at
equality in (5), which is a vertical separator as well.

A horizontal C0-axis separator would require

    |(c_E)_x|>=3/2-|s|>=17/12>sqrt(2).

But (3) gives |c_E|<=sqrt(2)*(1-d)<=sqrt(2), a contradiction.
The rectangle separating-axis theorem therefore puts the same actual
E wholly in one of

    y>=y_lo+1/2       or       y<=y_hi-1/2.                (6)

Both actual half-planes have distance at least delta from O. Their
weak boundary cases are included.

## 4. Apply the complete quantitative two-cap bound

Sections 3--5 of
NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md
prove the following standalone implication. Any actual unit in
D_sqrt(Q) with own-coordinate bound at most 1/2+delta and clearance
at least delta, for 5/12<=delta<=1/2, occupies a connected open arc
on the radius-5/4 circle of length at least

    L_delta=min(max(alpha0,alpha_delta),2*asin(2/5)),
    alpha0=pi/2-2*asin((sqrt(Q/2)-1)/(5/4)),
    alpha_delta=pi/2-2*asin(delta/(5/4)).

The same complete continuous proof establishes

    3*L_delta > pi-2*asin(delta/(5/4)).                    (7)

It uses only those own-coordinate, clearance and radius hypotheses;
neither equal central-square heights nor the equality of a rectangle
with their whole union enters that single-square proof.

Each of the two half-planes in (6) cuts from the test circle a cap
of measure at most the right side of (7). Three distinct E units
assigned to the same half-plane would have three disjoint open arcs
of total measure at least 3*L_delta, a contradiction. At most two
units belong to either half-plane, proving the capacity four.

The frozen complete source for the quantitative arc argument is

    NEAR_CENTRAL_DOMINO_FOUR_NONPOLAR_COMPLETION_CAPACITY_2026_10_30.md
    SHA256 33168fb5ab4605739746348d1425b47da33c6f2a64803357f1f0608515a160b8

In a nine-unit configuration the conclusion gives at least three
other actual units failing (3). It does not extract (1) from every
stress path or bound the capacity of the complementary units. It
retains all original body equations and means and performs no
physical deformation, compilation, numerical pose search or ledger
mutation.
