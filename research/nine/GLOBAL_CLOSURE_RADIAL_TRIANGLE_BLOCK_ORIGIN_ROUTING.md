# Every positive triangle block must meet the origin once two such blocks exist

Date: October 27, 2026.

**Status: complete proposed structural theorem, pending full root and
separate independent review.** No original label or shared ledger is
changed. The theorem concerns the common selected physical certificate;
it does not assert planarity of the entire physical touching graph.

Keep every actual interior-disjoint unit square in the original radius
window 79/40<=R<=sqrt(1105)/16, together with the compatible selected
normal system, original force magnitudes and actual common means. Use
the physical plane embedding supplied by
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`. All subsequent minimum-support
choices preserve this inherited embedding and its local junction order.

At each positive triangle below, the complete external force system at
each of its three vertices has zero origin moment. This is automatic
for a triangular block of the actual block-cut graph: sum the unchanged
moment equations in each entire component attached outside the block.
All its internal pair moments cancel at their original applications,
and all its circle moments vanish. The body's own circle atoms likewise
have zero origin moment. No external force or original root load is
discarded in this summation.

**Theorem.** Suppose the selected positive graph has at least two
distinct triangular blocks. Then at least one actual physical square
contains O. Moreover every triangular block contains O in at least one
of its three actual closed units. More generally, the same conclusion
holds for every positive triangle whose complete external moments
separately vanish at all three vertices; an arbitrary triangular face
inside a larger block is not asserted to have this property.

In particular, if just one actual unit contains O, that same actual
unit belongs to every triangular block. This is a closed-origin
statement: it neither asserts origin-interiority nor excludes the
possibility that several physical units meet at O.

## 1. The zero-cycle-moment alternative already puts O in two units

Consider any actual positive triangle with complete zero-origin-moment
external systems. The accepted
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md` makes its three
full external resultants nonzero and noncollinear. At most one of its
three cycle pairs is parallel: two parallel pairs would make all
three directed edge forces, and hence all three external resultants,
collinear. The physical same-outward-sign condition also excludes that
possibility directly on an odd three-cycle.

If the common directed cycle moment is zero, the two actual normal
lines at each nonparallel pair pass through O. Choose two such bodies
I,J. Their genuine concurrences are both O. The purely physical
proper-port theorem in `RADIAL_TRIANGLE_CONCURRENCE.md`, Section 1,
retains their mutual original common application p and gives

    p=a n=-b n, a,b>=0,                              (1)

where n points I to J. Therefore a=b=0 and p=O. Both closed actual
units I,J contain O. This argument uses no positive-ray assertion at
zero cycle moment, no load-degree premise, and no reset of an endpoint
mean.

Consequently, if all three closed units of a positive triangle avoid
O, its common cycle moment is necessarily nonzero.

## 2. A triangle whose three closed units avoid O surrounds O

Suppose all three actual units T_1,T_2,T_3 avoid O. Their nonzero
cycle moment was just proved. Apply exactly Sections 1--4 of
`ROOTED_NONZERO_MOMENT_TRIANGLE_ORIGIN_UNIT_EXCLUSION.md`.

For clarity, those sections use the absence of O from the three closed
units, not any separate property of an outside origin-interior unit.
The positive external-ray lemma provides D_i=s_i F_i in T_i, s_i>0.
Strict separation of O from T_i is therefore positive both on its
actual square and on each genuine nonparallel concurrence q_i=t_i F_i,
t_i>0. The convex hull used to replace the two actual port segments
through q_i avoids O. At a parallel pair one uses the unchanged actual
positive-ray point D_i instead; the original two nonzero port heights
have opposite signs, and both correction triangles avoid O.

The complete proper-port and parallel-pair calculations in that source
show that the unchanged actual contact polygon

    P=p_12,p_23,p_31,p_12                            (2)

has winding +1 or -1 about O. All its points and all its original
means remain unchanged. Its three sides lie respectively in the three
actual closed units. In particular (2) is nondegenerate; a repeated
port or collinear triple could only have winding zero away from its
image.

The usual center/contact loop of this triangle has the same winding.
Indeed replacing each actual square chord by its two center-to-port
segments is a homotopy within that square, which avoids O. This
statement does not assign a force or a concurrence to a square center.

## 3. The same contact triangle cannot surround any other whole unit

For any actual positive triangle, let its selected embedded cycle have
nonzero winding about the center c_E of another actual unit E.
We claim this is impossible whenever the local junction and tube
perturbations in the physical embedding are chosen to avoid c_E.

Undo those local drawing perturbations. Each replacement takes place
in a small junction disk or a thin tube which avoids c_E, so its
endpoint-fixed homotopy preserves winding at c_E. This recovers the
actual center/contact loop. Next contract each center-to-port detour
to its actual square chord. Every such homotopy is inside one of the
three triangle units and avoids c_E, because c_E belongs to the open
interior of the distinct E. Thus the original actual contact polygon
(2) also has nonzero winding at c_E.

The entire open interior of E is disjoint from all three closed
triangle units. Otherwise an open ball about an interior point of E
in one of those units would meet that unit's open interior. Hence
int E avoids every edge of (2). It is connected, so the nonzero
winding is constant throughout int E. A degenerate contact triangle
is already impossible. In the nondegenerate case the whole int E
lies inside the actual contact triangle.

Each of that triangle's side lengths is at most sqrt(2), being a
chord of an actual unit. Therefore its area is at most sqrt(3)/2<1,
whereas area(int E)=1. This is the complete contact-triangle area
contradiction of `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md`, with the
unchanged actual ports. No bounded region of a perturbed drawing is
mistaken for an actual geometric triangle.

There are only finitely many actual square centers. The embedding's
junction disks avoid all centers by construction, and its disjoint
tubes can be chosen small enough to avoid every nonincident center.
Thus this conclusion is available simultaneously for every triangle
and every unit outside that triangle.

## 4. Two distinct triangular blocks cannot both avoid O

Suppose two distinct triangular blocks T and U both have all their
closed units avoiding O. Their actual contact loops have nonzero
winding about O by Section 2. Choose the physical embedding with the
junction disks and tubes used by these two cycles small enough also to
avoid O. This is possible: O has positive distance from the finite
closed union of the units in these two blocks. An unrelated graph
junction may itself be at O; its neighborhood does not meet either
chosen cycle and need not avoid O. The local homotopies of the two
cycles preserve both windings. Each
embedded three-cycle is a simple Jordan curve.

Two distinct graph blocks have disjoint vertex sets or share exactly
one articulation. Consequently these two embedded Jordan curves are
disjoint or intersect at only that common vertex, its actual center.
Two such curves have either disjoint bounded interiors or one bounded
interior contained in the other. This elementary Jordan fact follows
by observing that the second curve minus the possible common point is
connected and cannot cross the first curve. If it lies on the bounded
side, it is the inner curve; if it lies on the unbounded side, the
first curve is either inside it or has disjoint bounded interior.

Their interiors both contain O, so disjoint interiors are impossible.
They must nest. Choose a private body vertex on the inner triangle;
there are at least two such vertices even when the blocks share an
articulation. Its center is strictly inside the outer embedded cycle
and is not on that cycle. Section 3 gives a contradiction using its
whole actual unit.

Therefore two distinct triangular blocks cannot both have all their
actual closed units avoiding O. In particular, if two triangular
blocks exist, some actual unit contains O.

## 5. Any actual origin-containing unit forces every triangle to meet O

Suppose an actual unit E contains O, with either an interior or a
boundary occurrence. Let T be any actual positive triangle all of
whose closed units avoid O. Then E is distinct from its three units,
and Section 2 makes its actual contact polygon (2) have nonzero
winding about O.

That polygon's boundary avoids O, so the winding has the same nonzero
value on an open neighborhood of O. Because E is full-dimensional
and O belongs to its closure, this neighborhood contains a point of
int E. The entire connected int E avoids the polygon's boundary,
as in Section 3. It therefore has that same nonzero winding, putting
the whole unit inside a contact triangle of area less than one.
This is impossible.

Thus every positive triangle must contain O in at least one actual
closed unit whenever any actual unit contains O. Combine this with
Section 4 to obtain the theorem.

## 6. Exact scope

The theorem retains each whole triangle's actual external aggregate.
Its zero-moment assumption is supplied by original block-cut branches,
not by dividing an articulation's circle weight or deleting forces.
The two triangles used in Section 4 must be distinct graph blocks;
two overlapping triangles within a diamond are not covered by that
nesting argument. Section 5 itself is a local statement for any
positive triangle with the stated complete external moments.

All shared-side means, coincident-junction drawing resolutions and
original free normals remain. Only the selected graph drawing is
perturbed in arbitrarily small disks and tubes; no square, application
or force is moved. The conclusion does not assert that an actual
origin-boundary configuration is impossible. Its remaining tangent
sectors must be treated in the original caller.

No coarse closure, new fine slice, numerical pose, Lean compilation,
CI, remote mutation or shared-ledger edit is used.
