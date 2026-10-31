# A selected positive C7 needs no radial-to-radial vertex edge

**Status: complete hand selection argument; independent full hand audit passed.**
In the remaining range `sqrt(17)/2 <= R <= sqrt(1105)/16`, the
simultaneous physical normal choices can be strengthened so that a
positive boundary C7 has no radial/radial vertex edge.

Together with C7_PINNED_VERTEX_CONTACT_TYPES.md, this leaves exactly
two contact domains: all edges have actual side-axis owners, or there
is exactly one free vertex edge and it is the mirror contact between
two pinned blocks of length two. This is a structure theorem, not the
remaining two-square completion bound.

## 1. Inputs and the endpoint with a fixed external contact

Use the physical C7 contact order and maximal positive-length
shared-side blocks from the preceding C7 selection manuscripts.
Their conclusions can be imposed simultaneously before KKT:

1. Each block incident to a surviving free vertex edge has exactly
   one physical radial square, at an endpoint; both its circle-corner
   weights are positive. All other bodies in the block have one
   physical circle corner.
2. A surviving radial/radial edge joins two nonsingleton blocks, by
   the adaptive physical-radial-run selection.
3. The free-edge graph has at most two edges. If there are two, they
   form a three-block path with one radial/radial edge and one
   unique/unique edge. Free cycles, including a two-block cycle with
   two distinct free edges, are excluded by the full block/profile
   theorem.

Consequently any surviving radial/radial edge has an incident block
whose other external edge is owned. Otherwise both its incident
blocks would have another free edge, giving three free edges or a
prohibited all-free cycle. Call such a block K and its radial endpoint
S. The other external edge is a point contact: a positive-length
shared side would extend the maximal block. Because it is owned,
its actual common normal is a fixed side axis. Its actual application
point is also fixed by the two physical squares.

The proof below uses only this fixed external point/axis and the
unique circle corners along K. All internal shared-side application
means remain variable until the exact equilibrium equations determine
them. No choice of a mean is made by hand.

## 2. Moment normalization and exact propagation through the block

Orient the C7 positively. Let a directed edge have normal n_i,
actual application p_i and positive magnitude mu_i. The body torque
equations, since every circle force has zero moment about the origin,
give one common nonzero origin moment

\[
                         \mu_i\det(p_i,n_i)=H.
 \tag{1}
\]

The C7 force-polygon theorem gives the consistent positive orientation
with H>0. Equivalently, each genuine boundary-pair normal has nonzero
origin moment, and the positive cycle fixes the common sign. Divide
the entire stress by H and henceforth take H=1. This merely changes
its scale; force balance, torque and nonnegative circle weights remain.

At the owned external edge of K, both p and n are fixed, so its
moment-normalized force magnitude is

\[
                            \mu=1/\det(p,n).
 \tag{2}
\]

If this has the wrong sign for the oriented physical edge, no positive
C7 exists. Otherwise its full force vector is fixed by geometry.

Now propagate from that external edge along K toward S. At each
nonradial body, one adjacent edge force is already fixed; the other
edge is a shared side and has a fixed axis direction e. The only
circle force is a nonnegative multiple of its unique physical circle
corner z. The two-dimensional force equation determines the two
unknown coefficients of e and z uniquely, because

\[
                               \det(e,z)\ne0.
 \tag{3}
\]

Indeed, in the common side frame every physical circle corner has
both coordinate magnitudes at least1/2, and both are strictly larger
for a unique physical corner. The axis e cannot be parallel to z.
No division by the circle multiplier is used, so its zero case remains
included. A nonpositive pair magnitude or a negative circle multiplier
simply excludes the candidate stress.

For every positive internal magnitude, equation (1) fixes its actual
origin moment and therefore its mean application coordinate on the
known shared segment. The determinant along a side with its normal is
a nonconstant affine coordinate. Thus the whole propagation is unique,
including all shared means. A value outside its actual segment also
excludes the candidate.

In particular the force and application mean on the final shared side
at S are fixed solely by the physical block and its owned external
point/normal. They are **independent of the normal on the radial/radial
edge** at the other end of S. This is uniqueness of a necessary
moment-normalized solution; it is not an assertion that every such
solution exists or has positive weights.

## 3. The fixed radial shared mean is incompatible with a near-axis normal

Rotate and, if necessary, reflect the packing so

\[
 S=[d,d+1]\times[-1/2,1/2],
 \quad a_0=d+1=\sqrt{R^2-1/4},
 \quad c=\sqrt{R^2-9/4},
\]

and the radial/radial contact is at the forward inner vertex
`p_+=(d,1/2)`. Its other contact is the backward tangential shared
side, with the first parallel successor in K. The exact segment is

\[
                   p_-=(x,-1/2),\qquad d\le x\le c.
 \tag{4}
\]

This is the first profile of C7_PINNED_VERTEX_CONTACT_TYPES.md.
Section 2 has fixed x, including either endpoint of this full segment.
The incoming directed normal is e_y, and (1) fixes its magnitude to
1/x.

Choose the radial/radial outward normal from S in its genuine strict
common-normal interval near the forward tangential endpoint:

\[
                   n_+=(-s,v),\qquad s>0,\ v>0,
                   \quad s^2+v^2=1,\quad s\longrightarrow0.
 \tag{5}
\]

The radial-pair contact geometry guarantees a nonempty such interval.
Its moment-normalized magnitude is

\[
                            \mu_+=\frac1{dv+s/2}.
\]

If m is the nonnegative circle-resultant combination at S, force
balance therefore requires

\[
 2m=\frac1x e_y-\frac1{dv+s/2}(-s,v).
\]

Every nonnegative combination of the two circle corners
`(a_0,1/2)` and `(a_0,-1/2)` satisfies

\[
                       |m_y|\le\frac{m_x}{2a_0}.
\]

Substitution, multiplying only positive quantities, gives the exact
necessary inequality

\[
                 |(d-x)v+s/2|\le\frac{x s}{2a_0}.
 \tag{6}
\]

If x>d, the left side tends to x-d>0 as s tends to0, while the right
side tends to0. Thus (6) fails throughout a sufficiently small open
one-sided interval of strict normals in (5).

If x=d, equation (6) instead requires

\[
                         s/2\le d s/(2a_0),
\]

which is false for every s>0 because a_0=d+1>d. This handles the
endpoint at which the limiting axis calculation alone would give a
zero circle resultant. Both positive and zero corner weights have
been included, and the other endpoint x=c belongs to the first case.

Therefore every fixed value x in the actual shared segment admits a
nonempty open near-axis normal interval on which this entire block
cannot support the required positive C7 stress.

## 4. The choices are simultaneous and occur before multipliers

For a fixed packing, all data used here are physical: the boundary
contact graph, its maximal radial runs and shared-side blocks, each
unique physical circle corner, and every owned external point/axis.
The moment-normalized propagation in Section 2 is computed from those
data; it does not use an already obtained stress.

If the physical boundary graph is not C7, it cannot underlie this
all-boundary branch. If it is C7, first treat radial runs of length at
least three and two-runs with an outside point contact by the earlier
open exclusions. These rules already preclude a positive C7 in those
physical cases.

For each remaining physical two-radial run, both outside contacts are
shared sides. Whenever an incident block has an owned far external
point, use that endpoint for the new open interval from Section 3.
If both qualify, either one suffices. This replaces the arbitrary
forward choice on that run; it does not disturb the physical fact
that both outside contacts are shared sides. Distinct maximal runs
have distinct radial/radial edges, so these open choices are
independent. Reflection permits either endpoint of its common cone.

The previously imposed finite open-dense selections are then made
inside these intervals. The length-three unique/unique pair exclusion
uses different edges and remains compatible. At a four-square
junction the matched parameters are retained; a radial/radial pair
has nonparallel frames and cannot be one of those junctions.
Uncrossing and thinning preserve every surviving fixed point normal.

Suppose the final selected positive component were C7 and retained a
radial/radial edge. The already established free-edge graph cover
would give it an incident block with an owned far edge, as in
Section1. That physical candidate was handled by the new choice.
Its required mean is uniquely the fixed x of Section2, and its circle
cone violates (6). This is a contradiction. Physical cases without
such an owned far edge cannot evade the argument: they contradict
the prior exhaustive free-edge graph cover for any final C7.

No normal is changed after multipliers have been taken.

## 5. Whole-branch consequence

**Theorem.** In the residual radius range, the necessary planar
physical certificate can be selected with no radial/radial edge in
an all-boundary positive C7.

Every two-free-edge layout had one radial/radial edge, so it is also
excluded by this stronger selected-certificate theorem. The only
remaining free-edge case is exactly one unique/unique contact between
the two mirror pinned blocks of length two. The three other ring
bodies and every owned complementary contact remain arbitrary.

The companion C7_MIRROR_VERTEX_EDGE_EXCLUSION.md subsequently excludes
that last free-edge type. The complete all-owned capacity problem
remains open, with both additional physical squares retained. No
unrestricted sharp bound, equality classification, Lean compilation
or CI result is claimed here.
