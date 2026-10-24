# n=9: a planar, boundary-loaded stress core for every unrestricted minimizer

**Status: hand proof of a global structural reduction.**
This strengthens SPARSE_MINIMIZER_STRESS.md: the **translational**
stress can be chosen planar, with all circle-loaded squares on its
outer face. It starts with arbitrary independent square orientations.
No global horizontal/vertical separating frame is assumed.

This is NOT the assertion that the full physical contact graph of
all the squares is planar. Four squares meeting at a corner can
create both diagonals of a contact K4. The proof makes an allowed
choice of separator normals and then **uncrosses the stress**, not
the squares. No packing is moved and the disk radius does not change.

It is also NOT a claim that planarization preserves the angular
stationarity of a separately chosen full-rotation stress. The
27-atom angular certificate in ROTATION_STATIONARY_STRESS.md and
the at-most-19-term planar translational certificate here need not
be the same certificate.

## 1. The only four-body junction is an aligned 2x2 block

**Lemma 1.1.** At any point common to at least two interior-disjoint
closed unit squares, at most four squares can meet. If four meet,
the point is a vertex of all four squares, and the squares form an
exact aligned 2x2 block around it, up to rotation.

*Proof.* No common point can lie in a square's open interior,
since any other square containing that point has interior points
arbitrarily close to it. A square contributes a local interior
angle of either `pi` (side interior) or `pi/2` (vertex). These open
angular sectors are disjoint. Their total angle is at most `2 pi`,
so at most four squares meet. Four meeting squares must each
contribute exactly `pi/2`, using all four consecutive quadrants.
Their side directions are therefore the same two perpendicular
axes, up to signs. As all side lengths are one, their centers in
the local frame are exactly `(+-1/2,+-1/2)` relative to the point.
Adjacent squares share a complete unit side; opposite squares
meet only at that common vertex. QED.

For three squares, the local incidence graph is a subgraph of K3.
For four squares the possible point-contact crossings are exactly
the two edges joining opposite quadrants. A pair with a positive-
length common side can use a point in the relative interior of that
side for a contact drawing, avoiding its endpoint junctions.

## 2. Choose compatible diagonal normals BEFORE extracting stress

At each four-square junction, choose one of its two common unit
axis directions and call it `e`. Label the four squares `SW, SE,
NW, NE` in that local frame. Select normals on the two opposite
pairs parallel to `e`, oriented from the left square to the right:

\[
 SW\longrightarrow NE,\qquad NW\longrightarrow SE. \tag{1}
\]

These are genuine, tight own-square separators. The corresponding
adjacent horizontal pairs

\[
 SW\longrightarrow SE,\qquad NW\longrightarrow NE \tag{2}
\]

also have their unique feasible axis parallel to `e`.
A pair of opposite-quadrant squares touches at only this one
point, so its choice (1) conflicts with no other junction's choice.
Shared-side pairs have the same geometric normal wherever their
contact is viewed. At all other pairs, use the separator selection
of SPARSE_MINIMIZER_STRESS.md: a strict axis for noncontacting
closed squares, and any feasible axis for actual contacts.

The minimizer-to-stress theorem applies to **any** such feasible
selection. Thus there is a normalized nonnegative translational
stress with these prescribed local diagonal choices. It exactly
attains the squared radius in the center-eliminating dual.

## 3. Exact uncrossing preserves every node force

Suppose both opposite edges (1) have positive stress magnitudes
`A,B`. Put `delta=min(A,B)`. Decrease the two diagonal magnitudes
by `delta`, and increase the two side-edge magnitudes (2) by
`delta` each. Missing side edges simply receive this new positive
weight. No negative coefficient is introduced.

**Lemma 3.1 (uncrossing identity).** The change preserves the net
force at **each of the four squares**, preserves all circle
multipliers, and removes at least one of the two diagonal edges.

*Proof.* At SW the two changed edges both point in direction `e`:
`(A-delta)e + delta e = A e`. At NE the corresponding incoming
forces give the same equality with the negative sign. At NW and
SE use `B` in place of `A`. Thus all four net forces are unchanged.
At least one of `A-delta` and `B-delta` is zero. All affected
separator constraints are actual contacts and remain tight.
Their widths are one, so the total separator work also stays
`A+B`; alternatively, this follows from preserved node forces
and the fixed centers. QED.

Circle weights and forces determine the center-eliminating dual
value. Thus this operation preserves its exact attainment, as
well as all translational stationarity and complementarity equations.

Apply the operation at each four-square junction that carries both
opposite edges. A newly added side edge is a positive-length
side contact, not a diagonal contact at any other junction.
Therefore no new crossing diagonal pair is created elsewhere,
and the finite procedure terminates.

**Important scope.** This is a rerouting of the coefficients in a
proved inequality. It is not a motion of packing squares, and it
uses no unsupported claim that tilted squares can be aligned.
Torque equations are not part of the preserved equations here.

## 4. The resulting contact support has a planar drawing

**Lemma 4.1 (contact drawing).** For a family of interior-disjoint
squares, choose any contact-edge subgraph with at most one
opposite-pair edge at each four-square corner junction. Then that
subgraph has a planar embedding consistent with the physical
contact order.

*Proof.* Put a graph vertex at each square center. For each
positive-length side contact select a point in its relative
interior. For a point contact use its actual point. Join the
centers to the selected contact points by segments within their
respective squares. Each segment, except its boundary endpoint,
lies in the open square. Segments belonging to different square
interiors therefore cannot cross.

Several selected pair contacts can use one common contact point.
Temporarily regard this as a junction vertex joined to the incident
square centers. This contact-incidence drawing is planar; multiple
uses of the same segment can be separated into parallel strands in
a small neighborhood inside that square.

Resolve each junction inside a sufficiently small disk that meets
no other junction and no nonincident strands. At a junction of
three or fewer squares, the required pair graph is a subgraph of
a triangle, drawable with the square sectors in their cyclic order.
At a four-square junction the sectors have the cyclic order of a
quadrilateral. Its four sides and at most **one** diagonal admit
an embedding in that order: put the sides around the local disk
and the one diagonal through its interior. This is precisely why
removing one crossing opposite pair is necessary. Attach the local
strands to their original square-center segments. The local disks
are disjoint, so the resolutions do not interfere. The resulting
pair-edge drawing has no intersections between independent edges;
incident strands meet only at their square-center vertex. QED.

Apply this to the uncrossed positive-stress edges from Section 3.
The physical square positions are unchanged.

## 5. Circle-loaded vertices are cofacial

**Lemma 5.1.** A point on the containing circle belongs to at most
one square of an interior-disjoint packing.

*Proof.* A boundary-circle point of a square must be a vertex:
a strict convex combination of two distinct disk points lies
strictly inside the disk. At a square vertex `p` on the circle,
each incident side direction toward its other endpoint is strictly
inward relative to the circle tangent, because for any different
point `z` of the disk,

\[
 p\cdot(z-p)=\tfrac12(\|z\|^2-\|p\|^2-\|z-p\|^2)<0.
\]

Thus its closed right-angle corner sector lies strictly inside
the inward open half-plane. Two disjoint right-angle sectors of
two squares cannot both lie strictly inside the same open
semicircle: their angular lengths already sum to `pi`, leaving
no room at the two strict endpoints. QED.

For every positive-circle-weight corner, its segment to its own
square center lies inside the square and can be included as one
more incident strand. Its endpoint is a unique circle point by
Lemma 5.1. The short radial continuation outward reaches the
exterior of the disk without crossing any contact edge, all of
which can be embedded inside the disk. Therefore every loaded
square vertex is incident to the **same exterior face** of the
contact-support embedding.

This does not make the entire graph outerplanar: unloaded force-
transmitting or branching squares may be interior vertices.

## 6. Recover sparsity and choose one connected core

Uncrossing can increase the number of positive separator terms,
but all its new edges are tight, all node balances are unchanged,
and the resulting active gradient combination still represents
minus the radius-objective gradient. Apply the conic sparsification
argument of SPARSE_MINIMIZER_STRESS.md **using only these planar
support edges and the current circle-contact terms**. It leaves at
most `2n+1` positive terms. Deleting support edges cannot destroy
planarity or the cofacial accessibility of loaded vertices.

Choose any positive-stress connected component and renormalize its
circle weights to sum one. As proved in the companion, such a
component has at least two distinct circle-loaded squares and
still exactly certifies the same radius `q0`. A circle-free positive
self-stress component and an unloaded degree-one leaf are impossible.

**Theorem 6.1 (planar sparse minimizer core).** Every global
minimizing packing of `n>=2` independently oriented unit squares
admits a connected translational stress core such that:

- all its positive edges are actual touching square pairs;
- it has a planar embedding with every circle-loaded square
  incident to the exterior face;
- it has at least two circle-loaded squares;
- unloaded vertices have degree at least two;
- circle-vertex atoms plus edge atoms total at most `2n+1`;
- its center-eliminating dual value equals the minimizing squared
  radius exactly.

For nine squares the term count is **at most 19**. There can thus
be at most 17 positive contact edges, because at least two
circle-vertex atoms are necessary. A 19-term count is still not a
human-sized classification of all possible planar graphs.

## 7. Suppress only genuine unloaded degree-two transmitters

At an unloaded degree-two square, force balance says its two
nonzero incident forces are opposite with equal magnitudes. Thus
both normals are parallel. Orient the corresponding contact
path consistently from its first endpoint toward its second.

For a maximal such path with retained endpoints `A,B` and
`ell` internal unloaded degree-two squares, all its edge normals
are one unit direction `d` and all edge weights agree. Adding
its tight projection gaps gives the exact relation

\[
 d\cdot(c_B-c_A)=h_A(d)+h_B(d)
                    +2\sum_{i\text{ internal}}h_i(d)
                \ge h_A(d)+h_B(d)+\ell. \tag{3}
\]

There is no closed transmission loop: the left side of the sum
around a loop would be zero while all its contact widths are
positive. In particular, suppressing such a path cannot create a
self-loop. Parallel edges between distinct retained vertices are
possible and should be kept as separate paths with their own
normal directions and internal-square counts.

For a nine-square minimizer with `q0<=Q`, every center has norm
less than `61/40`. If `ell>=3`, (3) would give

\[
 d\cdot(c_B-c_A)\ge\ell+1\ge4,
 \qquad
 |d\cdot(c_B-c_A)|<2(61/40)=61/20<4,
\]

a contradiction. Therefore

\[
                         \boxed{\ell\in\{0,1,2\}}. \tag{4}
\]

After suppressing the transmitters, every retained unloaded
junction has degree at least three, every loaded node is still on
the exterior face, and the sum of retained vertices and all
internal-square counts is at most nine. The path reserves in (3)
are derived from actual squares; the squares on those paths are
not assumed aligned. Equality in a bound using the minimal reserve
may subsequently force their widths to one, as in the existing
4+3 stress proof.

## 8. What is actually closed, and what is not

**CLOSED structural implication:** a hypothetical unrestricted
packing with `q<Q` leads to an unrestricted minimizer with a
connected **planar, outer-loaded, sparsely stressed** actual-contact
core. Its unloaded degree-two paths have only 0, 1 or 2 internal
squares. This supplies a genuine geometric graph reduction for
G2.O3.1, not the unfiltered collection of all 36 SAT pair owners.

**STILL OPEN:** prove a short exhaustive terminal classification of
these physically realizable cores **together with the remaining
unstressed packing squares**, and derive the sharp bound `q>=Q`.
Planarity, the 19-term bound, and the finite path labels do not by
themselves establish that bound. In particular, arbitrary stressed
cores of fewer than nine squares need not require radius `sqrt(Q)`;
packing capacity for the other squares cannot be silently discarded.

The separate full-rotation certificate in
ROTATION_STATIONARY_STRESS.md can impose additional angular
necessary conditions, but **no theorem here asserts that its
27-atom torque-balanced stress can simultaneously be made planar
by the translational uncrossing operation**.

**Verification:** explicit hand argument, with the four-junction
force-rerouting identity checked independently using rational
arithmetic in `check_sparse_stress.py`. No Lean, CI or unrestricted
optimality claim.
