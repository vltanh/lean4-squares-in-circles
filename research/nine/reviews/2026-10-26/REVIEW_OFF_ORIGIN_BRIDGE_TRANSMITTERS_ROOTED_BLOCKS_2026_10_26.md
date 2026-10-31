# Independent full review: off-origin unloaded bridge transmitters

Date: October 26, 2026.
Reviewer: rooted-blocks independent agent.

**Verdict: ACCEPT the complete uniform theorem and its stated corollaries.**
The reviewed full source is
`GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md`, SHA-256
`8c8aa3985802b8fc74332898e1ac581c3b395fec9bfe14d3f83de9b7ec3b6c1f`.
No mathematical correction is required. This is a local theorem for an
actual unloaded body incident only to bridges; it does not suppose the
whole component is a tree and does not assign a leaf equation to its
possibly cyclic outward neighbor.

## 1. Original radial and metric input

The local central-disk argument uses only the actual all-bridge incidence
and zero circle load. An all-bridge body missing D_delta would be outer at
every bridge, with all forces applied at its unique nearest point and in
one direction, contradicting its original force equation. Hence its center
satisfies delta+1/sqrt(2)<19/24. This is the legitimate local content of
`TREE_BODY_LOCALIZATION.md`, not an application of a complete-tree theorem.

At every positive outward radial application t e, the actual other square
lies in e dot x>=t. The sharp contained-square support theorem gives t<=d.
For any square avoiding zero, one own center coordinate has absolute value
strictly larger than 1/2. Positive radial support uses its far face, whose
absolute coordinate is strictly greater than one. Thus t>1. These two
inequalities keep all means and contact owners and immediately exclude an
outward bridge if d<=1.

## 2. Full force classification

Incoming bridges all use the unique nearest point p_* and have outward
direction -p_*/|p_*| on U. They cannot balance alone. The convex nearest-point
inequality gives p_* dot p>=|p_*|^2>0 for every outward application p, so all
outgoing forces have positive projection on p_*. They cannot balance alone
either. Both classes therefore occur before an own-frame form is asserted.

Choose the center coordinate a>1/2. If the other own coordinate also had
absolute value above 1/2, every outward radial support would use both far
faces and have norm greater than sqrt(2), contradicting t<=d<61/60.
Consequently |b|<=1/2 and p_*=(a-1/2,0). Every outgoing application has
first coordinate x_0=a+1/2>1. A nonzero second coordinate is one of the two
actual top or bottom vertex heights and has the same sign as the radial
force's vertical component.

The displayed comparison is exact:

    y^2<=d^2-x_0^2<d^2-1<(61/60)^2-1=121/3600.

Positive and negative outgoing heights would be the two endpoints of an
interval of length one, while the comparison puts their separation below
22/60. Thus at most one nonzero vertical sign occurs. The original vertical
force equation eliminates that sign. All outgoing applications are therefore
(x_0,0), all outgoing normals are horizontal, and rho=x_0-1 satisfies
0<rho<=d-1<1/60. The actual applications differ by exactly one.

This argument includes b=+/-1/2, when one or both original applications are
side endpoints. It does not replace an endpoint mean by an interior mean.

## 3. Neighbor count and minimum-support inheritance

Every outward neighbor has c_x>x_0+1/2>3/2 and center norm below 91/60.
The rectangular-cap diameter calculation is correct:

    (91/60-3/2)^2 + 4((91/60)^2-9/4)
      = 725/3600 = 29/144 < 1.

Two distinct interior-disjoint unit squares have center distance at least
one, so there is exactly one outward neighbor. This conclusion does not
need the neighbor to be loaded or to be a leaf.

An incoming neighbor has actual outward radial support rho e_x with
0<rho<1. A unit inward segment from that support lies in the square for
every side or vertex contact feature: in own axes its decrements are the
nonnegative components of a unit normal, each at most one. The segment
therefore contains zero. This proves that every incoming neighbor contains
the origin without an alignment premise on that neighbor.

Under the common minimum-support selection, deleting U gives one branch
per incident edge because all those edges are bridges. Every branch has
positive circle mass by CY.LOAD.1. All vectors (f_j,a_j) lie in a
two-dimensional subspace because the original f_j are horizontal. With
three or more branches the exact nonnegative branch scaling proved in
`GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md` removes a positive branch
while preserving every original force and angular equation and the total
normalization. It keeps the pose, normal system, surviving means and
planarity. Minimality is contradicted, so U has exactly two neighbors and
is a genuine original degree-two side transmitter.

## 4. Corollaries and scope

The d<=1 origin-containment corollary requires no minimum-support choice:
force balance already requires an outward edge, which would violate
1<t<=d. Under minimum support two off-origin unloaded all-bridge bodies
cannot be adjacent, because one would be the other's incoming neighbor and
would therefore contain zero. If the actual sole outward neighbor is a
genuine radial leaf, radius greater than one forces S and fixes x_0=d.
Without that leaf premise the full interval 1<x_0<=d correctly remains.

All nine physical squares, all masks and zero-weight contacts remain. No
statement is made about a loaded body or a body having a nonbridge edge.
No coarse cell, sharp lower bound or equality theorem follows solely from
this local classification.

The complete source and the actual direct radial/support/minimum-support
inputs were checked. No Lean compilation, CI or numerical pose sampling was
used.
