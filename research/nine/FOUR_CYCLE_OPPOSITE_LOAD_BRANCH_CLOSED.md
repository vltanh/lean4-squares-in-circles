# The complete opposite-loaded-pair C4-with-leaf branch is closed

**Status: complete conditional hand assembly; root and independent full hand audits passed.**
For a sharp radius lower-bound contradiction, choose a nine-square
radius minimizer which also minimizes the sum of squared center norms
among all radius minimizers. In the window
\[
                     79/40\le R\le\sqrt{1105}/16,
\tag{1}
\]
its necessary physical certificate can be selected so that its unique
positive component is not
\[
                           A-B-U-D-A
\]
with a pendant radial leaf L at A, B and D loaded, and U unloaded.
All radial leaf types, physical circle masks, side owners, actual
application means and the other four physical squares are included.

This closes the **entire opposite-loaded-pair C4 branch**, with the
canonical radius-lower-bound scope stated above. It does not exclude
every arbitrary positive stress on a noncanonical five-square core,
and it does not classify every equality packing. The all-three-loaded
C4 and the diamond branches of C1.4.b1 remain open, so this is not
whole-cell C1.4.b1 closure.

## 1. The secondary choice preserves every necessary radius certificate

At the minimum radius R, the labeled packing space is compact.
The continuous function Phi=sum_i |c_i|^2 has a minimum on that
space. Choose its minimizer before selecting contact normals or
extracting multipliers. It is still a global radius minimizer, so
all previously established necessary radius certificates, lower-window
reductions and complete graph exclusions remain applicable.

The S/D leaf classification and circle-clear articulation conclusion
come from RADIAL_BRIDGE_AND_LEAF_REDUCTION.md. The physical two-load
completion theorem has already excluded components with only two
loaded bodies. In the present branch the positive loaded bodies are
precisely L,B,D. U may be physically circle-touching with zero circle
weight; this possibility is retained.

The secondary choice is a legitimate reduction of a radius lower-bound
contradiction. No assertion that every radius minimizer has this
geometry is required.

## 2. Whole-configuration geometric and owner reductions

The complete prerequisites are:

| Source | Full implication used |
| --- | --- |
| UNIT_BYPASS_NORMAL_CHANNEL.md | U is a single side-normal transmitter of reserve one. A lies wholly on one transverse side and its vertical projection contains the unit channel. All actual channel means remain. |
| FOUR_CYCLE_LEAF_HOLE_EMPTY.md | The bounded C4 hole contains no additional unit square, in every physical load mask. The argument includes coincident contacts and the full contact-area equality case. |
| FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md | A parallel to U is impossible in a compatible selected certificate, including every radial leaf, point/side contact and variable mean. |
| FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, Sections1--6 | At the secondary minimizer the transverse A/U gap is zero. Otherwise translating U into the entire empty-hole strip preserves every one of the nine squares, decreases its farthest corner norm, and decreases Phi. Thus AU is a genuine vertex/side-interior physical contact; AB and AD cannot have positive-length shared sides. |
| RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md | The two distinct singleton A-tip contacts can simultaneously have no free vertex/vertex normal, for every physical circle mask. The leaf-application and radial-vertex degeneracies are fully handled before the fixed-wrench determinant is used. |

The physical AU contact is not assigned positive stress. The two
existing forces on U remain opposite side-axis forces on one vertical
line. No shared-side mean on BU or UD is replaced by a convenient
endpoint or midpoint.

The empty-hole translation is the only step in this branch which
needs information about the four completion squares. Its proof keeps
their connected interiors outside the entire newly occupied strip.
After that reduction, the exact geometric and force contradictions
rule out the core, with every completion square still present.

## 3. The complete physical circle-mask cover

Each loaded tip has either one physical circle corner or two adjacent
physical circle corners. A unit square with more farthest corners
would be centered at the circle center and have containing radius
sqrt(2)/2, outside (1). Thus, up to interchanging B,D, the following
three masks are exhaustive.

| Physical B/D mask | Complete exclusion |
| --- | --- |
| One / one | FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md. It covers both possible unique-circle corners in an oblique lower tip, U-parallel equality means, all mixed owners, and the exact two-A-owned45-degree endpoint. Both radial leaf types are retained. |
| Two / two | FOUR_CYCLE_TWO_RADIAL_TIPS_EXCLUSION.md. Channel geometry forces mirrored radial frames, every possible contact face is covered, and positive concurrence makes the two inner-face parameters exceed1/2. This theorem itself does not need the secondary choice. Every individual two-corner weight split remains. |
| One / two | Sections4--5 below, for both radial leaf types and every owner order. |

A two-physical-corner body with one zero individual circle weight
remains in the two-corner row. It is never silently replaced by a
unique-physical-corner body.

## 4. The mixed mask with a D leaf is completely excluded

FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md covers the entire mixed mask.
The all-mask owner selection makes its four owner alternatives
exhaustive:

* Both A-owned: the complete D-leaf force/side-span contradiction in
  the canonical-contact source, Section7, applies.
* Both tip-owned: the older all-oblique owner theorem applies when
  both tips are oblique. The retained radial U-parallel endpoint has
  a direct circle-corner deficit greater than3/10; no endpoint was
  omitted.
* A owns the unique-tip edge: the D-leaf force and torque equations
  force a short angular domain. The U-parallel unique-tip endpoint
  is separately excluded, and then every corner of the unique tip
  has squared norm less than754/225<R^2.
* A owns the radial-tip edge: its inner-vertex norm forces the unique
  tip's A application to have squared norm less than53/200<r^2,
  where r=R-sqrt(2). No boundary square can contain that point.

The entire D-leaf mixed family is therefore impossible, including
all real side means and radial corner-weight splits.

## 5. The mixed mask with an S leaf is completely excluded

FOUR_CYCLE_MIXED_S_LEAF_EXCLUSION.md covers the entire S-leaf mixed
mask. Its physical radial-tip contact lemma keeps both its exact
inner-vertex norm h^2+1/4 and its positive A-frame projection, with
h=sqrt(R^2-1/4)-1.

Both tip-owned edges are excluded by the leaf-independent endpoint
argument from the D source. For each of the two mixed owner orders,
the S leaf's two possible support vertices and its intervening
support side are all treated. A proposed surviving feature either
has the wrong physical projection, violates global force balance,
or places the unique tip's contact strictly inside radius r.

If A owns both edges, the only possible S support is its right
vertex. Its exact own coordinates satisfy 0<B_0<3/8 and A_0>4/5.
The actual unit channel gap and a complete two-interval Cauchy bound
force the lower contact parameter tau>1/2-B_0. Its squared norm is
then less than29/100<r^2, again impossible. All aligned endpoint
means and all four extra squares remain.

This is a complete owner and leaf-feature cover, rather than a
collection of sampled charts or a restriction to a convenient
physical two-corner weight mask.

## 6. One compatible selected certificate and exact remaining scope

At the fixed canonical packing, prelist all physical assignments,
radial leaf directions, physical circle corners, genuine singleton
applications and allowed strict point-normal variables. The needed
fixed-wrench and finite-direction exclusions have nonzero bad factors
on their independent open parameter intervals. The corresponding
finite open dense conditions are imposed together with the preceding
strict, nonradial, matched-junction and generic choices, before the
physical multiplier theorem.

Uncrossing preserves surviving point normals and adds only actual
shared-side forces. Conic thinning deletes atoms. The source theorems
retain every shared interval which these operations can use; the
canonical physical singleton conclusion is not inferred from a
post-extraction deletion. Thus the selected certificate is compatible
with the planar, sparse, unique-positive-component framework.

The three physical masks, both leaf types and all side owners are
now exhausted. No opposite-loaded-pair C4 component remains at the
canonical minimizer. Together with the already complete adjacent-load
exclusion, this leaves **only the all-three-loaded C4** among the
four-cycle-with-leaf load alternatives. The K4 branch is already
excluded; the remaining diamond branches are not closed here.

The coarse-cell total remains four closed and54 open. C1.4.b1 is
still open. The unrestricted radius lower bound, positive C7
completion, larger mixed components, and equality classification
remain separate gates. No Lean compilation or CI was run, and this
assembly does not claim a new complete audit of the older prerequisite
chain.
