# Side-patch consolidation preserves an augmented generic certificate

**Status:** reviewed exact hand theorem; root and independent full
mathematical reviews passed on 2026-10-31. This strengthens the certificate class of the two
reviewed consolidation theorems. It does not exclude an original fixed
case family merely because its representative can be consolidated.

The relevant selection conventions are exactly those in
[SEVEN_RING_COMPLETE_CAPACITY.md](SEVEN_RING_COMPLETE_CAPACITY.md), Section 1:
strict/nonradial/nondiagonal point-only VV normals, coherent four-square
junction normals, the finite loaded-VV concurrence exclusions, and the
two compatible circle-loaded VV interval prescriptions. No arbitrary
additional generic convention is covered by this note.

**Theorem.** Those conventions can be augmented by finitely many corner
conditions so that the resulting class of minimizing packing/certificate
pairs is nonempty and is preserved by suitably chosen motions in
[DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md](DOUBLE_SIDE_BUNDLE_CONSOLIDATION.md)
and
[PARALLEL_SIDE_PATCH_CONSOLIDATION.md](PARALLEL_SIDE_PATCH_CONSOLIDATION.md).
Every surviving positive VV normal remains exactly unchanged.

Consequently the minimum-active-body normalization can be made within
this stronger class. Its conclusions (no double-S, no double-SS, a simple
suppressed skeleton, and no unloaded branching region with only two
outside terminals) then coexist with the full original generic selection.
This is an existence statement about a selected minimizing representative,
not a claim that every old packing or positive graph already has these
properties.

## 1. The additional finite corner conditions

Work in the original disk coordinates, with origin the disk center. Let
C be any geometric circle-contact body with a unique circle vertex w.
Let e be any geometric point-only VV contact of C, with contact point P
not on the line spanned by w. For a direction n of e and any fixed point
Q and direction f, write

```text
D(P,n;Q,f)=(P cross n)*(w cross f)
           -(Q cross f)*(w cross n).                 (1)
```

In addition to the actual-contact candidates in
[LOADED_VV_GENERIC_RESTRICTION.md](LOADED_VV_GENERIC_RESTRICTION.md), impose
(1) != 0 for the following finite list:

* Q is any of the four vertices of C;
* f is one of the four unit side normals of any of the ten square frames.

Skip exactly the old identically zero exception

```text
f parallel w,       Q cross f=0.                     (2)
```

These are formal corner candidates, not added physical contacts or stress
rows. There are finitely many bodies, vertices, frames, and VV incidences.

To verify simultaneous selection, rewrite (1) as

```text
[(w cross f)*P-(Q cross f)*w] cross n.                (3)
```

If w cross f != 0, its bracket cannot vanish because P is not collinear
with w. If w cross f=0 and Q cross f != 0, the bracket is nonzero because
w != 0. Thus every included factor is a nonzero linear functional of n.
The existing affine direction chart for each VV normal spans the plane,
so each factor remains a nonzero polynomial in that chart parameter.

At a coherent four-square junction an individual opposite-pair normal is
also parametrized by a spanning chart, either (1,t) or (-1,t). Each new
factor uses only this one normal and fixed geometric frame directions;
coupling the other opposite-pair normal does not make it identically zero.
The old two-normal factors retain their independently reviewed compatibility.
The two circle-loaded interval prescriptions remain nonempty open
restrictions on their original disjoint pair categories. Multiplying the
old and new nonzero factors and avoiding their zero set on the existing
open parameter box therefore selects all conventions jointly.

The physical-stress existence argument and planar junction replacements
are unchanged: the extra conditions merely restrict the initially chosen
VV directions, and surviving VV directions are not altered by replacement.
The complete seven-ring theorem applies to this selection, giving the
nonempty starting class with no entirely loaded positive component.

## 2. The available motion parameters form an open box

Use the reviewed consolidation construction, including its empty-gap,
disk-containment, positive-overlap and wrench arguments. If no square
needs to move, retain the geometric packing and all its chosen normals;
only the positive forces change. Every generic condition then survives.

Otherwise, each moved square is translated parallel to its column by a
strictly positive amount into a positive-height gap. The retained path's
fixed aggregate force height m is required to lie strictly inside its
chosen square interval. The shift can be chosen from a nonempty open
interval: when m lies inside a gap, move the bordering square just beyond
m; when m is at a gap endpoint, use a sufficiently small positive shift
of that bordering square into the gap. The shift is strictly smaller than
the full gap. A zero-height gap requires no motion.

For two moving columns these intervals may be chosen independently.
Their interiors occupy disjoint open column strips, and the reviewed
empty stepped-cavity argument supplies collision-free containment for
every choice in the product of these intervals. Positive terminal and
intercolumn overlaps hold throughout after shrinking the intervals if
necessary. Thus the permissible choices contain a nonempty open box
in one or two real shift parameters. No discrete endpoint choice below
is made until this box has been fixed.

Every moved square becomes strictly circle-clear. Its points are strict
convex combinations of corresponding points of two distinct original
column squares. For corresponding vectors x,y with x != y and 0<lambda<1,

```text
|(1-lambda)*x+lambda*y|^2
 =(1-lambda)*|x|^2+lambda*|y|^2
  -lambda*(1-lambda)*|x-y|^2 < R^2.                  (4)
```

Applying this to its four vertices and using convexity proves the claim
for the whole moved square. All unmoved geometric circle bodies and
their circle vertices are unchanged; no new geometric circle body appears.
All square-frame directions also remain unchanged.

## 3. Remove finitely many corner coincidences

A point-only VV contact involving a moved square requires one of its
moving vertices to coincide with a vertex of another square. Against a
fixed square this holds for at most one value of that square's shift.
Against a second moving square it is either impossible or a proper affine
hyperplane in the two independent shift parameters. It cannot hold on
the whole parameter box, since varying one shift with the other fixed
moves its vertex by a nonzero vector.

Delete these finitely many proper affine hyperplanes. In particular this
also deletes every potential new four-square junction involving a moved
square: four unit-square sectors at one point force all four incidences
to be vertices. All geometric VV pairs that remain are between unmoved
squares, at their old contact points and with their old normal cones.
Keep every one of their old selected directions, including directions
of zero-stress geometric VV pairs.

Their strictness, radial and diagonal exclusions are unchanged. Every
remaining four-square junction is an old junction among unmoved bodies,
so its coherent directions are unchanged too. A former junction that
loses a moved body imposes fewer coupling conditions. The circle-adjacent
and opposite-circle interval prescriptions are also preserved: any VV
pair to which they now apply is an old unchanged pair between two
unchanged geometric circle bodies. No new VV direction needs to be chosen.

## 4. Exhaust the possible contact candidates at an unmoved circle body

Fix an unmoved unique-circle body C, a remaining VV incidence e at P off
the load ray, and its retained normal n. It remains to check (1) for each
actual-contact candidate f in the old loaded-VV selection, now evaluated
in the moved packing. If the other body is unmoved, its intersection with
C and its normal are unchanged, so the original exclusion applies.

If the other body S moved, it has no VV contact by Section 3. Every
possible remaining candidate belongs to the following finite table.

| Intersection of C and S | Candidate application Q | Normal f | Reason for nonvanishing |
| --- | --- | --- | --- |
| Point at a vertex of C and relative side interior of S | Fixed vertex of C | A side normal of S's unchanged frame | Added corner factor, unless exception (2) |
| Point at a vertex of S and relative side interior of C | Moving vertex of S | A side normal of C | Moving-endpoint argument below |
| Positive-length shared side, endpoint supplied by C | Fixed vertex of C | Common side normal | Added corner factor |
| Positive-length shared side, endpoint supplied by S | Moving vertex of S | Common side normal | Moving-endpoint argument below |

This table is exhaustive for two interior-disjoint convex squares. A
singleton intersection must be a vertex of at least one square: distinct
supporting lines at two relative side interiors would make their interior
half-planes overlap locally, whereas coincident supporting lines give a
positive-length side overlap. VV singletons were deleted.
A non-singleton intersection is a shared side segment, whose endpoints
are vertices of at least one incident square. Coincident endpoints were
also deleted when they are vertices of both. A fixed corner candidate
uses a side normal from one of the unchanged frames, precisely as included
in Section 1. The exception (2) is the same one deliberately skipped in
the original actual-contact family, so it requires no new exclusion.

For a moving endpoint, write Q(h)=Q_0+h*v, where v != 0 is the column
translation direction and h its signed scalar parameter. There are only
finitely many choices of moving vertex and side of C. If that vertex's
path is not parallel to the side of C, it meets the side's supporting
line at at most one h. Delete these finitely many parameter values too.
All remaining moving-endpoint candidates therefore have

```text
v perpendicular f,       v cross f != 0.             (5)
```

Here f is a side normal of C in both moving-endpoint rows of the table.
A unique circle vertex w is not parallel to any side normal of its own
square. To see this, choose own orthonormal coordinates with w=(X,Y)
the farthest corner. Uniqueness of that corner gives X>1/2 and Y>1/2;
both components are nonzero. Consequently

```text
w cross f != 0.                                     (6)
```

Substitution in (1) gives the affine expression

```text
D(h)=D(0)-h*(v cross f)*(w cross n).                 (7)
```

If w cross n != 0, (5) makes its slope nonzero, so it has at most one
zero. Delete that parameter value. If w cross n=0, then P cross n != 0
because P is not on the line spanned by w; by (6),

```text
D(h)=(P cross n)*(w cross f) != 0                    (8)
```

for every h. Thus there is no identically zero moving-endpoint factor.

All exclusions in Sections 3--4 are finite unions of proper affine
hyperplanes in the open shift box. Their complement is nonempty, by the
same elementary nonzero-polynomial fact used in the original selection.
Choose the shifts there. This proves the original actual-contact
concurrence exclusions for every remaining unique geometric circle body,
every eligible VV incidence, and every possible other application point.
It includes zero-stress geometric contacts, not just the retained graph.

## 5. The augmented family itself is preserved

The additional corner factors from Section 1 require no further argument
in the new geometry. A geometric circle body in the new packing is an
unchanged old circle body, every remaining VV incidence is old and
unchanged, its own four corners are fixed, and the set of square-frame
directions is fixed. Its entire new corner list is therefore a sublist
of the old identical list. Removing a moved body's circle contacts or
VV incidences only deletes factors. All remaining corner factors keep
their original nonzero values.

Consequently the full augmented normal assignment is available for the
new packing, not merely the original conventions without the extra
conditions needed for another consolidation step.

The reviewed force replacement uses only positive-length shared sides
in the patch. A force at any chosen point in such a segment is a
nonnegative combination of the two physical endpoint atoms. Thus the
new equilibrium is supported on the normal/contact rows allowed by this
assignment; no rerun of the multiplier argument, with a possibly different
positive graph, is needed. Surviving positive VV rows and all circle loads
are unchanged. Four-junction physical planarity and absence of an entirely
loaded component are preserved exactly as in the reviewed consolidation
theorems.

## 6. Stronger minimum-active normalization and its limit

Augment the published normalization class by requiring the full normal
assignment of Section 1, with all the old actual-contact exclusions and
the two loaded-pair interval prescriptions. Section 1 and the complete
seven-ring theorem make this class nonempty. Sections 2--5 and the two
reviewed local consolidation theorems show that it is closed under each
needed consolidation after a permitted generic choice of slide amounts.

Minimize the integer number of active bodies over this class. A double-S
bundle or a three-/four-body parallel side patch would yield a member
with fewer active bodies, a contradiction. The structural consequences
already proved in Section 7 of the parallel-patch theorem therefore hold
inside the original generic selection conventions as well.

This resolves the specific selection-compatibility obstacle and allows
statements proved under those conventions to be used
on the normalized representative. It neither preserves a raw graph ID
under motion nor turns a normalization into an exclusion of all original
realizations of that ID. Regions with three or more outside terminals
and the remaining completion-capacity obligations are not settled here.
