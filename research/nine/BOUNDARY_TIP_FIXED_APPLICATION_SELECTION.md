# Fixed-application boundary tips need no free vertex normal

**Status: complete simultaneous-selection hand implication; independent hand audit passed.**
In the declared window `79/40 <= R <= sqrt(1105)/16`, the physical
certificate may be selected so that the following positive degree-two
star never occurs:

- its middle square S has exactly one physical circle corner;
- at least one of its two positive neighbors also touches the circle;
- both pair contacts have fixed geometric application points (neither
  pair shares a positive-length side segment);
- at least one pair is a point-only vertex/vertex contact with a free
  strict common-normal interval.

The other neighbor may be physically circle-clear. Every nonnegative
circle weight, including zero, is retained. This extends the
fixed-application C7 input to triangle tips and other mixed components.
It does not remove variable application means from a shared-side star,
and does not by itself exclude a whole mixed coarse cell.

## 1. Exact local data and two geometric facts

Write the unique physical circle corner in the square's orthogonal
side coordinates as

\[
 z=(a,b),\qquad S=[a-1,a]\times[b-1,b],
 \qquad a,b>\tfrac12,\qquad a^2+b^2=R^2.
 \tag{1}
\]

Let the two actual application points be p and q, with outward common
unit normals n and m. Label the neighbors so the neighbor at q touches
the circle. The normals satisfy the actual supporting-half-plane
conditions; they are not arbitrary algebraic force vectors.

Every genuine common normal between two circle-touching squares has
nonzero origin moment, by CIRCLE_CONTACT_ANGULAR_ORDER.md and the
radial S/D/shallow-face argument used in C7_FORCE_POLYGON.md. Thus

\[
                         \det(q,m)\ne0.
 \tag{2}
\]

A common point of two circle-touching squares has norm strictly larger
than `R-sqrt(2)`. For completeness, each such square has a circle corner
z_i and diameter sqrt(2), so

\[
 R=|z_i|\le |p|+|z_i-p|\le |p|+\sqrt2.
\]

Equality would force both circle corners to be the same point
`R p/|p|`. Two contained unit squares cannot share a containing-circle
point: their inward tangent quadrants both contain the strictly inward
radial direction. Their interiors would overlap. Consequently equality
is impossible for a common point of the two boundary squares.

In particular a vertex q of S shared with a boundary neighbor cannot
be collinear with z. The two adjacent non-circle vertices are never
collinear with z, since a,b are positive. Its opposite vertex is
collinear only when a=b; then a=b=R/sqrt(2)>1, and that vertex has norm
exactly `R-sqrt(2)`, just excluded.

We also use the elementary width obstruction: if a unit neighbor lies
beyond a support line with unit normal n and value h, it has a point
of n-projection at least h+1. Thus `h>R-1` makes that neighbor
impossible in the disk.

## 2. The exact force/moment determinant

Let the two pair-force magnitudes be mu,nu>0 and let lambda>=0 be
the circle-corner multiplier. The necessary equations are

\[
 \mu n+\nu m+2\lambda z=0,
 \qquad
 \mu\det(p,n)+\nu\det(q,m)=0.
 \tag{3}
\]

Taking the determinant of the force equation with z and eliminating
mu,nu with the moment equation gives

\[
 D(n,m):=\det(z,n)\det(q,m)
            -\det(z,m)\det(p,n)=0.
 \tag{4}
\]

No division by lambda is used. The equation is necessary even if the
circle weight is zero or the two force directions are parallel.

If the fixed applications coincide and at least one incident contact
is free vertex/vertex, then p=q is a vertex of S shared with the
boundary neighbor. Section 1 gives det(p,z) nonzero. Taking torque
about p in (3) forces lambda=0. The two remaining positive outward
normals at the same point lie in one pointed square normal cone, so
cannot sum to zero. Thus such a coincident-application star is already
impossible. We may henceforth assume p and q are distinct.

## 3. A free vertex normal toward the possibly clear neighbor

Suppose the normal n at p is free. The application p is a vertex
of S. For any fixed actual normal m at q, write

\[
 D(n,m)=\det(W(m),n),
 \qquad
 W(m)=\det(q,m)z-\det(z,m)p.
 \tag{5}
\]

We prove W(m) is nonzero for every allowed m. If it were zero,
(2) would force p to be collinear with z. By the vertex list in (1),
this requires

\[
 a=b=s=R/\sqrt2>1,
 \qquad p=(s-1,s-1)=\tau z,
 \qquad \tau=(s-1)/s.
\]

Equation W=0 then gives

\[
                           \det(q-p,m)=0.
 \tag{6}
\]

The boundary contact q differs from p and is not z. If q lies in the
relative interior of a side, its normal is perpendicular to that side.
The perpendicular line through the corner p meets each other side at
an endpoint, or meets an incident side only at p; it never reaches
such a side-interior point. This contradicts (6).

If q is another non-circle vertex, it is either (s,s-1) or (s-1,s).
Equation (6) forces its genuine outward normal to be respectively
`e_x` or `e_y`. The corresponding outer support value is s. In this
radius window

\[
                         s=R/\sqrt2>R-1,
\]

since R<2+sqrt(2). The width obstruction excludes the boundary
neighbor, and indeed any unit neighbor, beyond that face. These are
all possible fixed contact features. Thus W(m) is always nonzero.

For each actual m, condition (4) therefore forbids at most two opposite
unit directions of n. It has empty interior in every open strict
normal interval.

## 4. A free vertex normal toward the boundary neighbor

It remains to consider a free normal m at q when n is fixed. Now

\[
 D(n,m)=\det(V(n),m),
 \qquad
 V(n)=\det(z,n)q-\det(p,n)z.
 \tag{7}
\]

If det(p,n) is nonzero and V=0, then q is collinear with z,
contradicting the boundary-vertex fact in Section 1. If det(p,n)=0
but det(z,n) is nonzero, then V is a nonzero multiple of q. The
point q is nonzero because a circle-touching unit square cannot
contain the origin when R>sqrt(2).

The only residual degeneracy is

\[
                      \det(p,n)=\det(z,n)=0.
 \tag{8}
\]

It supplies no positive star at all. The moment equation in (3) would
be `nu det(q,m)=0`, contradicting nu>0 and (2), independently of
any generic choice. Hence every physically possible positive star
in this case also has a nonzero coefficient V, and only finitely many
free m directions can satisfy (4).

If both normals are free, Section 3 already shows that D is a
nonzero bilinear function on their two independent strict intervals.
Its zero set has empty interior. The coincident-point case was
excluded separately, so no unjustified independence at one junction
has been used.

## 5. Simultaneous choice before the physical multiplier theorem

For a fixed physical packing, prelist every square with a unique
physical circle corner, every pair of distinct point-contact
neighbors with at least one boundary neighbor, and all actual feature
assignments described above. This is a finite list. Pair contacts
with positive-length common segments are deliberately outside this
lemma; their full mean coordinates remain in the physical problem.

At a four-square junction, retain the established matched coefficients
for the two opposite vertex pairs. A free normal varies through an
open interval in that junction's single parameter. The two
applications of a candidate star are distinct, so their junction
parameters are distinct if both are free. Equations (5)--(7) remain
nontrivial on the allowed intervals. Fixed owned-axis normals require
no parameter. The exceptional fixed case (8) is impossible for every
parameter choice and imposes no restriction.

Avoid the finitely many closed determinant zero sets simultaneously,
inside all previously required strict open normal intervals. The
intersection is nonempty: each condition has empty interior in the
finite product of parameters, and its complement is open and dense.
This retains the nonradial, diagonal-avoidance, matched-junction,
radial-run and other compatible finite choices already imposed.

Only after these choices take the physical force/torque certificate.
The actual uncrossing operation adds shared-side endpoint forces and
preserves the normals of surviving point-only edges. Subsequent
conic thinning deletes atoms; it adds no new point-only edge type.
If the final positive component had a degree-two star in this lemma's
scope, both geometric applications would be its original fixed
points, and that candidate was prelisted. Equation (4) would
contradict the chosen normal parameters. A newly present shared-side
mean does not evade the statement, because such a star is outside
its explicitly fixed-application premise.

## 6. Complete implication and exact nonclaim

**Theorem.** A necessary planar physical certificate, with the prior
sparsity and unique-component properties, can be selected so that
no degree-two unique-physical-circle-corner body with two fixed
applications and a boundary neighbor has a free vertex/vertex
positive contact.

In particular the theorem applies to either loaded degree-two tip
of an end triangle whenever its two physical pair contacts are
point contacts. The other neighbor, usually an articulation, need
not touch the circle. Every actual shared-side mean must still be
handled by another argument. The theorem is a complete selected
normal implication, not a sharp radius or completion theorem.

No Lean compilation or CI was run.
