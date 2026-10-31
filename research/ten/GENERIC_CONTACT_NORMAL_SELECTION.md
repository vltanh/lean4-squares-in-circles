# Select contact normals away from square diagonals

**Status:** independently reviewed exact hand selection theorem
(2026-10-29), checked against the pinned physical-stress and conic
multiplier sources. The pinned physical-stress source permits the
additional finite exclusions below. This selects a certificate at the
minimizer before its components are classified; it does not modify an
arbitrary previously chosen stress while keeping its graph fixed.

## 1. Statement and compatibility with the existing selection

At an unrestricted minimizing packing of unit squares, one may choose a
normalized physical force-and-torque stress with the following property:

> At every point-only vertex/vertex contact, its selected common normal
> is strictly inside both appropriate normal cones and is parallel to
> neither diagonal of either incident square. If the contact is off the
> origin, the normal is also nonradial.

The stress remains physical: every contact application belongs to the
actual intersection of its two squares, and every positive circle atom
is at a circle-contact vertex. Positive-length shared-side contacts still
permit forces at their intersection endpoints and their weighted-average
points.

This strengthens the strict/nonradial convention already used in
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) and
[COMMON_CORNER_MIXED_TRANSMISSIONS.md](COMMON_CORNER_MIXED_TRANSMISSIONS.md).
All earlier arguments that require only that convention apply to the new
selection. No assertion is made that the same positive edges, components,
degrees, or multiplier values survive from an older certificate.

## 2. The admissible directions form an open interval

At a point-only vertex/vertex intersection p, the two right-angle tangent
sectors have disjoint interiors and share no nonzero boundary ray. A
shared ray would supply a positive-length common side segment instead.
There is consequently a nonempty open interval of common supporting
normal directions exposing p uniquely in both squares. This is precisely
Section 2.2 of the pinned
[physical-stress construction](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/PHYSICAL_CONTACT_STRESS.md).

Each incident square has two diagonal lines. Forbid normals parallel to
those four lines, and also to the line through p and the origin when
p is nonzero. This removes only finitely many unit directions from the
open admissible interval, so a choice remains. At p=0 there is no radial
exclusion to impose; the diagonal exclusions still apply.

Make all these choices independently for the finitely many point-only
vertex/vertex contacts, before constructing the local smooth constraints.
The choices are strict, so the selected support corners remain unique in
a sufficiently small common neighborhood of the minimizing pose.

## 3. The stress-existence argument still applies

For each such pair i,j with chosen normal d and contacting corner offsets
`a_i(theta_i), a_j(theta_j)`, use the source's smooth sufficient inequality

```text
B = d dot (c_i+a_i(theta_i)-c_j-a_j(theta_j)) <= 0.
```

The normal d is fixed for this vertex/vertex constraint. The chosen corners
remain unique extrema nearby, so B<=0 separates the whole squares there.
At the base packing both corners are the actual shared point p. Its
center and angle derivatives are therefore exactly the physical contact
derivatives at p stated in Section 1 of the source.

For vertex/relative-side contacts and positive-length shared-side
contacts, retain the other two constructions in Sections 2.1 and 2.3 of
that source. In particular, a shared side uses the two actual overlap
endpoints, whose sufficient local branch also admits either sign of
relative rotation. Noncontacting pairs remain separated in a small
neighborhood. There are finitely many constraints, so all neighborhoods
can be intersected.

The resulting smooth feasible branch is contained in the set of physical
packings and contains the minimizing pose. That pose is a local minimum
of the squared radius on this branch. It is not necessary that every
nearby packing belong to the branch.

The qualification in Section 3 of the source is independent of which
strict common normals were chosen. Use the velocity

```text
dot c_i=c_i,        dot theta_i=0,        dot q=K,
```

with K sufficiently large. Every active circle constraint decreases
strictly. At an active pair constraint, its derivative is

```text
d dot (c_i-c_j) = -(h_i(d)+h_j(d)) <= -1,
```

since each unit square has directional halfwidth at least one half.
Thus the same strict active-direction condition holds simultaneously
for all chosen normals. The source's elementary conic multiplier
argument gives nonnegative contact and circle multipliers, with the
circle multipliers normalized to sum to one, and the same simultaneous
body force and torque equations. Nothing in this construction depends on
there being nine squares rather than ten.

Finally aggregate any two positive side-contact endpoint forces for a
body pair by taking their weighted-average application point in their
actual shared segment. Their normals agree, so force and torque are
preserved. A point-only vertex/vertex pair has just one selected row and
one contact point; aggregation cannot change its normal into a forbidden
diagonal direction. This proves the theorem.

## 4. Every diagonal transmitter meets relative side interiors

Choose this certificate, aggregate its body-pair forces, and only then
inspect its positive components. Suppose an unloaded body U has degree
two and is a diagonal transmitter. The reviewed two-force square lemma
gives equal opposite forces along one of U's diagonals, acting at the
two opposite vertices of U.

At either contact p, the supporting normal is strictly inside U's
vertex normal cone. Its support face on U is therefore the singleton
{p}, and the whole intersection with its neighboring square is {p}.
If p were also a vertex of that neighbor, this would be a point-only
vertex/vertex pair with positive normal parallel to U's diagonal,
contrary to the selection theorem. The contact is on the neighbor's
boundary and is not a vertex, so it belongs to the relative interior
of a side.

Consequently both neighbors of every degree-two D transmitter have
side normals parallel to its transmission direction. Their frames are
parallel to each other and rotated by 45 degrees from U's frame.
The neighbors need not be loaded and need not have degree two.

This is a restriction on the newly selected positive graph. It does not
exclude geometric vertex/vertex contacts carrying zero stress, prescribe
the positions along those neighbor sides, or prove any completion-capacity
bound by itself.

## 5. How to use the selection in an exclusion proof

Assume a strictly subcritical ten-square packing exists and take an
unrestricted radius minimizer. Select the preceding certificate there,
then apply the existing finite component classification to its positive
graph. The selected strict/nonradial convention required by earlier
branches remains satisfied. For a branch involving a degree-two D
transmitter, Section 4 now provides the additional relative-side-interior
condition at both neighbors.

One must not instead start with a classified old certificate and claim
its graph remains unchanged after a new normal choice. The existence
argument is made before case classification. No Lean verification or
global optimality conclusion is claimed by this selection theorem alone.
