# An unloaded full star cannot return a four-neighbor contact chain to one strict corner

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: complete proposed radius-free full-star theorem, frozen for
independent and root review.** The positive degree is arbitrary. Every
original force and actual side mean remains. The neighbor chain needs
only physical contacts, and its units may have any original loads and
degrees.

## 1. Complete physical and force statement

Let U and its actual positive neighbors be distinct closed unit squares
with pairwise disjoint open interiors. U is genuinely unloaded and keeps
its entire original positive star. For every neighbor J let F_J be the
unchanged positive multiple of its actual outward separating unit normal
from U to J. Thus the full original force equation is

    sum_J F_J=0.                                            (1)

Choose four distinct neighbors A,B,C,D such that the physical contacts

    A--B, B--C, C--D                                       (2)

all exist. They need not themselves have positive coefficients. Suppose
the original U-to-A and U-to-D normals strictly expose the same actual
U vertex P. Suppose every other original force, apart from those toward
A,B,C,D, lies in the closed outward normal cone of U at P.

**Theorem.** This entire full-star domain is impossible.

The extra forces may be own-axis normals with their original applications
anywhere on the corresponding actual support sides. No such mean is
replaced by P. The theorem imposes neither a containing circle nor a
torque or normal-selection premise.

## 2. Two degree-free geometric facts, with all support features

Use the actual own chart U=[0,1]^2 and P=(0,0). We record the physical
facts used in the proof, to include both strict and axis endpoints.

If an actual unit K has a minimum-n support point Q and a unit direction
e satisfies n.e<0, then

    max_(z in K) e.(z-Q)<1.                              (3)

At a vertex Q the two inward orthonormal axes have nonnegative n
components. At most one can have positive e component: otherwise n.e
would be nonnegative when e is resolved in those axes. Its positive
component is strictly less than one, since equality would make e an
inward axis. At a side-interior point only its tangent interval can
increase the e coordinate. That interval has length at most one, and
its projected unit component is strictly below one because e has a
nonzero n component. Side endpoints are already covered by the vertex
argument. This proves (3) for the whole actual K and every original
support point or shared mean.

Consequently actual neighbors at opposite strict U corners cannot
touch. For Southwest and Northeast, (3) gives their whole-unit
containments respectively

    {x<1,y<1},       {x>0,y>0}.

Any common point would lie in int U. Even a boundary point of another
actual closed unit cannot lie there, because every neighborhood of that
point meets that unit's open interior and would create interior overlap.
The other opposite-corner pair follows by reflecting the actual chart.

There is also the complete owned-axis triangle restriction. If two
neighbors V,W of U touch and the U-to-V normal is an own axis of U,
its dot product with the original U-to-W normal is nonnegative. For
example take the first axis East. If the other normal had negative
x component, its actual U support would be on x=0, and (3) would
put the whole W strictly in x<1. The whole V lies in x>=1, which
precludes their actual contact. This includes every original axis
side mean and every frame or owner at the external neighbors.

These are the degree-free physical implications of the pinned unit
triangle source; neither uses equation (1).

## 3. The complete sign cover for the two middle neighbors

Normalize P=(0,0) as above. Both original vectors F_A and F_D have
strictly negative x and y components. Every extra vector in the stated
full-star premise has both components nonpositive.

The physical AB contact restricts B as follows. It cannot have both
components positive, since that would strictly expose the opposite
Northeast U corner. It cannot be East or North either: that owned
axis has negative dot product with the strict Southwest A normal,
contrary to the triangle restriction. It follows that

    (F_B)_x>0  implies (F_B)_y<0,
    (F_B)_y>0  implies (F_B)_x<0.                       (4)

Every zero-coordinate endpoint was included in the preceding axis
argument. The actual CD contact with the strict Southwest D normal
gives the identical conclusions

    (F_C)_x>0  implies (F_C)_y<0,
    (F_C)_y>0  implies (F_C)_x<0.                       (5)

The complete x coordinate of (1), including the two strictly negative
end components and every nonpositive extra component, forces

    (F_B)_x+(F_C)_x>0.

Its complete y coordinate likewise forces

    (F_B)_y+(F_C)_y>0.                                  (6)

One of B,C therefore has positive x component. Interchange the names
B,C together with A,D if necessary so that it is B. Formula (4)
then gives (F_B)_y<0; the second inequality in (6) forces
(F_C)_y>0, and (5) gives (F_C)_x<0. Thus B strictly exposes
the Southeast U corner and C strictly exposes the Northwest corner.
Those corners are opposite. The actual BC contact is impossible by
Section 2.

This contradiction covers every original normal, all side means,
and arbitrary additional positive degree. It proves the theorem.

## 4. Literal use and preservation boundary

In a full unloaded H4 with positive neighbors A,B,C,D and actual
rim contacts AB,BC,CD, the two end normals HA and HD therefore
cannot strictly expose the same actual H vertex. No other-force
premise is needed there because those four forces are the entire
positive H neighborhood.

This conclusion permits either end to be externally side-owned or
free, as long as its unchanged H normal is strict at the stated
corner. It does not assert that a normal is strict without a proved
owner hypothesis, and it does not alter a shared-side mean. It is
also not a complete original graph/load exclusion by itself.

No moment equation or original term is deleted. The original torque
equation remains true but is not needed. The neighboring units may
have arbitrary physical circle masks, zero individual corner weights,
other forces, and any actual positive degree. The theorem uses only
the actual contacts in (2), not nonexistent diagonals among them.

## 5. Exact operative input

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete physical support-span and owned-axis triangle facts, with the needed proofs restated in Section 2 |

No frozen source, ledger, metadata, gate count, roadmap or handoff is
changed. No numerical pose search, angle grid, geometric exclusion
certificate, Lean compilation, CI, commit or remote write is used.
