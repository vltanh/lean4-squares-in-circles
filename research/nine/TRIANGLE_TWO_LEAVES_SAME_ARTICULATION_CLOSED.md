# The whole same-articulation two-leaf triangle layout is closed

**Status: complete whole-layout hand assembly; root and separate independent
hand audits passed.**
In the explicit radius window

\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]

the necessary planar physical certificate can be selected so that no
positive component consists of a triangle A,B,C with two pendant
unit squares both joined to A. This excludes the entire
same-articulation attachment layout of C1.3.b2. It excludes the
five-body core itself, independently of the four remaining physical
squares in a nine-square packing.

The length-two pendant-chain layout is separately excluded by
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`. The third layout, with
one leaf at each of two distinct triangle vertices, remains a
separate open parent obligation. This assembly does not claim that
the whole C1.3.b2 cell, or the unrestricted nine-square theorem, is
closed.

## 1. Exhaustive physical leaf types

Apply the existing bridge and loaded-leaf theorem in
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, retaining its full actual
support contacts. Each pendant body is exactly one of:

* S: the radial side-normal unit square, with two equally weighted
  outer circle corners and inner application
  \((\sqrt{R^2-1/4}-1)e\);
* D: the radial diagonal-normal unit square, with its sole outer
  circle corner and inner application \((R-\sqrt2)e\).

The selected nonradial vertex-contact convention makes each D
application lie in the relative interior of a side of A. No unloaded
leaf is possible. A is physically circle-clear, and the other two
triangle vertices B,C are loaded: a clear degree-two transmitter
cannot have touching neighbors. All physical circle-corner masks of
B,C and all positive weights are retained.

Exchanging the two leaves leaves exactly three unordered types.

| Leaf types | Complete source | Whole-family conclusion |
| --- | --- | --- |
| S/S | `TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md` | Every support-face and unique-vertex pair on A is excluded by exact inaccessible-circle-arc bounds and the acute B,C load sum. |
| D/S | `TWO_MIXED_LEAVES_ONE_TRIANGLE_ARTICULATION.md` | The D-aligned articulation and all three possible S applications are excluded by the southwest or 120-degree inaccessible arc. |
| D/D | `TWO_D_LEAVES_ONE_TRIANGLE_ARTICULATION.md` | Adjacent D directions fix A; all radii, coincident applications, side means, corner contacts, and both B--C axis owners are excluded. |

These are exhaustive physical types, not prescribed orientations for
the triangle tips. In particular the S/S source includes aligned
side-mean endpoints and both adjacent/opposite vertex pairs. The D/S
source retains the entire D slider domain before its three-way
support classification. The D/D source explicitly handles every
positive-length side application and does not require a one-owner
normalization.

## 2. One compatible pre-certificate selection

The S/S and D/S exclusions are geometric and force-balance arguments.
They impose no additional choice of a free contact normal.

The D/D proof uses the existing strict, nonradial, matched-junction
normal conventions, the fixed-application tip selection from
`BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md`, and one additional
finite shared-block determinant avoidance. Its Section 4 prelists all
physical candidates before multipliers are extracted. Every new bad
set has empty interior in the corresponding allowed free-normal
interval or product of intervals. The possible coefficient
degeneracy is excluded by the exact articulation-vertex radii.
When both exterior means could vary, the physical aligned geometry
is separately impossible; no continuum of means is silently fixed.

These open dense choices can be imposed simultaneously inside all
earlier permitted open normal intervals. Distinct articulation
applications use distinct junction parameters; the matched opposite
pairs at a four-square junction remain matched. Uncrossing adds only
shared-side forces and preserves surviving fixed point normals, and
conic thinning only deletes atoms. Every possible final physical
candidate was prelisted. Thus the D/D source applies to the same
necessary physical certificate as the two geometric sources and the
previous whole-class exclusions. No normal is chosen or changed in
response to extracted multipliers.

## 3. The exact implication for the parent cell

For any positive component of the stated same-articulation layout,
the exhaustive leaf table puts it in one of the three complete
sources. Each gives a contradiction throughout (1). The layout is
therefore closed with all four completion squares retained: none
is needed for the contradiction, and no pocket capacity is assumed.

For a triangle with exactly two attached bridges, the rooted bridge
forest has only three shapes: a length-two chain from one triangle
vertex, two leaves at one triangle vertex, or leaves at two different
triangle vertices. The first is closed by the chain source and the
second by this assembly. The exact remaining C1.3.b2 obligation is
the entire distinct-articulation two-leaf family, including all its
radial S/D masks, actual contact means, triangle moments, and all four
additional squares. No parent-cell closure follows until that family
has a full exclusion or completion bound.

No Lean compilation, CI, numerical certificate, or unstated
completion assumption is a premise of this assembly.
