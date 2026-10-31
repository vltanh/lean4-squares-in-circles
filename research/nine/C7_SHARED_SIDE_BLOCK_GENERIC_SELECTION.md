# Generic selection across a whole shared-side block

**Status: complete block virtual-work implication; independent hand audit passed.**
This extends `C7_FIXED_APPLICATION_GENERIC_SELECTION.md` to positive-length
shared sides, retaining every actual application mean on those sides.
It concerns physical circle-touching unit squares in

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\]

Before extracting the physical stress, free point-only vertex/vertex
normals can be chosen simultaneously so that every maximal shared-side
block incident to a free vertex/vertex edge in a selected positive C7
contains a radial endpoint body with both of its circle-corner
multipliers strictly positive. That radial body is unique within its
parallel block.

Here a shared-side block is a connected path of positive-length common
side contacts, including a singleton path. All frames in such a block
are parallel. The assertion does not restrict the shared-side force
application means to endpoints. It retains zero circle multipliers.

Consequently, if every C7 body has at most one positive circle-corner
atom, every surviving edge normal can be chosen along an actual side
axis of at least one of its bodies. In particular this holds when all
seven physical circle corners are unique. This does not assert a
one-owner chart: two-owner and zero-owner body patterns remain.

## 1. No two boundary bodies can share a point at the minimum inner radius

Every point p of a circle-touching unit square satisfies

\[
                            |p|\ge R-\sqrt2,
 \tag{1}
\]

because its distance from any circle corner is at most the square's
diameter \(\sqrt2\).

In fact two interior-disjoint circle-touching squares cannot share a
point of norm exactly \(R-\sqrt2\). If they did, choose a circle
corner z of either square. The inequalities

\[
 R=|z|\le|p|+|z-p|\le(R-\sqrt2)+\sqrt2=R
\]

would all be equalities. Since \(R>\sqrt2\), equality forces
\(z=Rp/|p|\). Thus both squares would share the same containing-circle
point, which is impossible.

It follows that a fixed vertex contact p of a circle-touching body is
never radially collinear with any chosen one of its circle corners z. Indeed,
write that body in its own frame as

\[
 S=[a-1,a]\times[b-1,b],\qquad z=(a,b),
 \qquad a,b\ge1/2.
\]

The two adjacent non-circle vertices are not collinear with z. The
opposite vertex is collinear only when \(a=b=R/\sqrt2\); its norm is
then exactly \(R-\sqrt2\), which has just been excluded. Therefore

\[
                 \boxed{\det(p,z)\ne0}
 \tag{2}
\]

at every vertex contact between two circle-touching squares, for every
chosen circle corner of the first square. This includes bodies with
two physical circle corners.

## 2. Two virtual motions for a path with one selected corner per body

Let \(S_1,\ldots,S_k\) be a path of positive-length shared sides.
Choose one physical circle corner \(z_i\) of each body. Suppose the
circle-load resultant of body i is a nonnegative multiple of this
chosen corner. A zero-loaded body satisfies this condition for either
corner choice. The frames are parallel; fix common orthonormal axes
for all of them. In these coordinates both components of each
\(z_i\) are nonzero, indeed their absolute values are at least
\(1/2\).

For each internal edge i, let \(e_i\) be its unit normal from
\(S_i\) to \(S_{i+1}\). It is one of the two common frame axes,
with a sign. Define nonzero real numbers \(\kappa_i\) recursively by

\[
 \kappa_1=1,\qquad
 \kappa_{i+1}
 =\kappa_i\frac{e_i\cdot Jz_i}{e_i\cdot Jz_{i+1}},
 \qquad w_i=\kappa_iJz_i.
 \tag{3}
\]

Every denominator is nonzero. These vectors obey

\[
                  z_i\cdot w_i=0,
 \qquad e_i\cdot(w_{i+1}-w_i)=0.
 \tag{4}
\]

Thus translating center i with velocity \(w_i\), while holding all
orientations fixed, is a first-order motion that annihilates every
circle-corner force and every internal shared-side force. This is a
virtual-work statement; it does not presume that the velocity
integrates to a finite feasible motion.

The shared-side application mean is irrelevant to (4), because the
velocity is a pure translation on each body. The normal velocity
jump is the same at every point of the common side.

A second virtual motion is rigid rotation of the whole block about
the origin. At an application point p its velocity is Jp. Each circle
force is radial, and the two velocities at an internal application
point agree, so this motion also annihilates every circle force and
internal contact force.

## 3. The two external contact equations

Suppose the path is a block of a positive C7. Its external contacts
are fixed point contacts p on \(S_1\) and q on \(S_k\), with outward
unit normals n and m from the block and positive magnitudes
\(\mu,\nu\). Summing the physical force and torque equations against
the two virtual motions gives

\[
 \mu\det(p,n)+\nu\det(q,m)=0,
 \qquad
 \mu(n\cdot w_1)+\nu(m\cdot w_k)=0.
 \tag{5}
\]

These identities are valid for every internal force magnitude and
every internal shared-side application mean. They also retain bodies
with zero circle load: the corner-force work vanishes whether or not
its multiplier is positive.

Eliminating \(\mu,\nu\) gives the necessary relation

\[
 D(n,m)
 :=\det(p,n)(m\cdot w_k)
   -\det(q,m)(n\cdot w_1)=0.
 \tag{6}
\]

Suppose the edge at p is a free vertex/vertex edge. For fixed m, (6)
is a linear condition on n, with coefficient vector

\[
 W(m)=(m\cdot w_k)Jp-\det(q,m)w_1.
 \tag{7}
\]

By the nonradial circle-pair contact theorem,
\(\det(q,m)\ne0\). Also \(w_1=Jz_1\). If \(W(m)=0\), then
(7) would force p to be collinear with \(z_1\), contradicting (2).
Hence

\[
                            W(m)\ne0.
 \tag{8}
\]

For every fixed choice of the other genuine normal m, at most one
unoriented normal line can satisfy (6). A free normal interval has
an open dense set of choices violating it.

## 4. A block whose external contacts are the same closing edge

The preceding two external normal parameters are independent unless
the shared-side path contains all seven bodies and its two ends are
joined by a single remaining point-contact edge. Handle that case
separately rather than treating its two normals as independent.

Here p=q and m=-n. Equation (6) becomes

\[
              \det(p,n)\,n\cdot(w_1-w_k)=0.
 \tag{9}
\]

The first factor is nonzero for every genuine common normal n. The
vector \(w_1-w_k\) is nonzero as well. Otherwise (3) would give
\(z_1=\kappa_k z_k\). Both circle corners have norm R, so they
would be equal or antipodal. Equal circle corners cannot be shared
by two squares. Antipodal circle corners are also impossible for
these touching end bodies, since their common point p would give

\[
                 2R=|z_1-z_k|
                 \le|z_1-p|+|p-z_k|
                 \le2\sqrt2<2R.
\]

Thus (9) again excludes all but one unoriented line from the free
normal interval. The closing-edge case supplies the same nontrivial
generic restriction.

## 5. Simultaneous choice and preservation

List every prospective shared-side path with two external point
contacts that could be a block of a selected positive C7, and for each
path list every choice of one physical circle corner per body. This
is a finite list in the fixed physical packing: every body has at most
two circle corners. The list uses actual positive-length shared-side
pairs, not only those currently assigned positive multipliers. The
corner choices are made for the finite avoidance argument before the
unknown positive multipliers are extracted.

For each candidate with an incident free vertex/vertex edge, (6)--(8)
exclude a closed set with empty interior in the corresponding product
of independent free normal intervals. If the other external contact
also has a free normal, fix it and vary n to verify empty interior.
The closing-edge candidates use (9) instead. Contacts at two distinct
points have independent local parameters. The no-three-boundary-body
incidence fact prevents a four-square junction from coupling two
different C7 edges; compatible opposite-pair choices at a junction
therefore preserve the same finite avoidance argument.

Choose the normals outside the finite union of all bad sets, inside
the existing open domains for the earlier generic choices and the
radial-block restrictions from `C7_TWO_CIRCLE_CORNER_BLOCKS.md`.
The resulting set of choices is nonempty and open dense relative to
those domains.

Uncrossing adds only shared-side pairs and never changes a surviving
point-contact normal. Thinning deletes atom types. Every possible
final shared-side block and every one-corner mask was prelisted using
the physical shared-side pairs; its external point contacts keep their
chosen normals. If every body of that block has at most one positive
circle-corner atom, choose that corner when there is a positive atom
and choose either physical corner at a zero-loaded body. Its equations
(5) would contradict the corresponding determinant exclusion. Thus no
new block or newly thinned corner mask can evade the generic choice.

## 6. Each surviving free vertex edge requires a doubly loaded radial endpoint

Consider any free vertex/vertex edge in the selected positive C7.
Apply the theorem to the maximal shared-side block at each endpoint,
including a singleton if that endpoint has no shared-side neighbor.
By Section 5, each block must contain a body with two strictly
positive circle-corner multipliers. Such a body has two physical
circle corners and is therefore radial.

That doubly loaded radial body cannot be internal to the shared-side
path. Use its frame (2) from `C7_TWO_CIRCLE_CORNER_BLOCKS.md`:

\[
 S=[a_0-1,a_0]\times[-1/2,1/2],
 \qquad z_\pm=(a_0,\pm1/2).
\]

A shared-side contact on its outer radial face is impossible by
width, since \(a_0>R-1\). A shared-side contact on its inner radial
face cannot reach another circle-touching body, by the shallow-contact
lemma in `C7_FORCE_POLYGON.md`, Section 2. Hence both internal
shared-side contacts would have tangential-axis normals. Their radial
components are zero. The radial component of translation balance
would then give

\[
                         2a_0(\lambda_++\lambda_-)=0.
\]

Nonnegativity forces both circle multipliers to vanish, contrary to
their strict positivity. Thus the doubly loaded radial body is an
endpoint of its block, or is the singleton block itself.

Section 6 of `C7_TWO_CIRCLE_CORNER_BLOCKS.md` also proves that two
parallel radial bodies cannot occur among seven circle-touching
squares. Since every shared-side block has parallel frames, its radial
body is unique.

We have established the strengthened conclusion:

**Pinned-block reduction.** After the simultaneous normal choice,
every maximal shared-side block incident to a surviving free
vertex/vertex edge has exactly one radial body. That body is an
endpoint, or the block is its singleton, and both of its physical
circle-corner multipliers are strictly positive.

In particular, if every C7 body has at most one positive circle-corner
atom, no free vertex/vertex edge survives. Every shared-side edge has
its common side normal, and every point contact has either a genuine
side owner or an isolated common-normal ray. An isolated intersection
ray of the two polygonal normal cones is a boundary ray of at least
one cone, hence an actual side normal of at least one square. All
surviving edges therefore admit actual side owners, while arbitrary
two-owner/zero-owner transitions remain.

This closes the complete all-unique and, more generally, one-active-
corner subfamily of the normal-selection reduction. It does not yet
exclude the pinned blocks described above, classify the remaining
owner patterns, or prove the final C7 two-square completion theorem.
\(\square\)
