# Two triangle blocks with any intact petal are excluded

Date: October 26, 2026.

**Status: accepted complete original-graph assembly after full-source
root and separate independent reviews in
REVIEW_TWO_TRIANGLE_LAYOUTS_AND_INTACT_ASSEMBLY_ROOT_2026_10_27.md and
REVIEW_TWO_TRIANGLES_ANY_INTACT_PETAL_HEXAGON_2026_10_27.md.**
The S-leaf central-disk dependency has full-source root and
separate independent acceptance. No original coarse label, fine label
or shared ledger is changed here.

Keep all original nine physical squares, the common compatible
radius/Phi-minimizer pose, and the minimum-positive-scalar-support
selection and named small-core prerequisites of
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. Work in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose the entire positive component has exactly two cyclic blocks,
both triangles, and arbitrary bridges, subject to the original
nine-body budget. Suppose at least one triangle is intact: its two
nonroot tips have their true positive degree two and are loaded.

**Theorem.** This entire original family is impossible.

This is an assembly for the full intact-petal domain in every original
C2.33 bridge count. It does not assume that the other triangle remains
intact after its original attachments are retained.

## 1. Common physical and graph consequences

Let H be the root of one actual intact petal. The accepted
ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md gives O in int H. Consequently
every distinct actual unit avoids O even on its boundary.

An intact petal at another actual root is impossible by open-origin
overlap. Two intact petals at H are excluded for the full component
by GLOBAL_CLOSURE_TWO_INTACT_PETALS_CENTRAL_DISK.md.

A genuine direct leaf at H is now impossible for either original
radial type: the accepted D theorem and the new S theorem are

    GLOBAL_CLOSURE_INTACT_ROOT_D_LEAF_CENTRAL_DISK_EXCLUSION.md,
    GLOBAL_CLOSURE_INTACT_ROOT_S_LEAF_CENTRAL_DISK_EXCLUSION.md.

Both are whole all-triangle block-tree theorems with every original
force retained. Their central-disk conclusions also exclude any
distinct genuine leaf root directly.

Every bridge-only internal positive body U is truly unloaded by the
exact articulation split. Because U avoids O, the complete
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md gives exactly two
actual neighbors, of which its unique inward neighbor must be H.
This statement is about the original positive graph; no bridge is
reattached or contracted.

We also use the already accepted complete theorem
GLOBAL_CLOSURE_INTACT_ROOT_BRIDGE_TO_LEAF_ROOT_EXCLUSION.md:
an actual positive bridge from H to any genuine leaf root is
impossible in an all-triangle component with at least two cyclic
blocks. Its far endpoint keeps all its possible cyclic forces.

## 2. The triangles share their articulation

Write the actual triangles as H,C,D (intact) and H,A,B. Their union
has five vertices and is connected. Every bridge component outside
this union is a tree attached at exactly one of these five vertices;
an attachment at two of them would make a further cyclic block.

If a bridge-only internal body U existed, Section 1 makes it adjacent
to H. Its other neighbor V cannot be a different vertex of the cyclic
union, which would give a second route back to H. Nor can V itself
be an internal bridge-only body: V too would have to be adjacent to H,
again making a cycle. Thus V is a true degree-one positive body, hence
a genuine leaf with root U. The actual bridge H--U is therefore the
forbidden bridge to a genuine leaf root. No internal bridge body
exists, and every bridge is a genuine direct leaf at a cyclic vertex.

The intact tips C,D have no such attachment by their true degrees.
The root H has no direct leaf by Section 1. Hence all bridges attach
at A or B.

Neither A nor B can have two genuine leaves. The complete two-leaf-
root geometry in TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md,
Section 1, puts O in any such actual root, including the d=1 boundary
case and arbitrary additional cyclic neighbors. This would overlap
the open-origin H. Thus each of A,B has at most one leaf.

There are exactly three possibilities, retaining all original forces:

* Neither has a leaf. Then H,A,B is a second intact petal at H,
  already excluded by Section 1.
* Exactly one has a leaf. The entire positive graph is the true
  one-tip-leaf bowtie of TIP_LEAF_BOWTIE_EXCLUSION.md. H has its exact
  original degree four here, and the full S/D and physical-mask cover
  of that accepted theorem applies. All three other physical squares
  remain as in its scope.
* Each has one leaf. The full H external system is the actual intact
  C,D petal, with zero origin moment. Its common-side geometry gives
  every H vertex norm greater than 1/40. Therefore the accepted
  GLOBAL_CLOSURE_ORIGIN_ROOT_TWO_LEAF_TRIANGLE_EXCLUSION.md applies
  to H,A,B with both genuine leaf forces retained. It includes both
  actual parallel and nonparallel contact families.

All three possibilities are excluded. This covers every shared-root
attachment forest, without a bridge-count restriction beyond the
original body budget.

## 3. The triangles are disjoint

Their unique block-tree route starts at H: the two private tips of its
intact triangle have no outside edge. It ends at a vertex K of the
other triangle. Intermediate route vertices are bridge-only bodies.

There cannot be two or more intermediate vertices. Every such body
would need H as its actual inward neighbor, whereas the original
simple bridge path cannot revisit H. If there is one intermediate
body, the complete arbitrary-forest theorem
GLOBAL_CLOSURE_INTACT_TRIANGLE_TWO_EDGE_CONNECTOR_EXCLUSION.md
applies to the whole two-edge connector H--U--K and excludes it.

It remains a direct bridge H--K. Every further bridge branch at H is
either a direct genuine leaf or contains a first internal bridge-only
body. The former is excluded by Section 1. In the latter, its first
internal body's other neighbor cannot be internal, since that next
body would also have to be adjacent to H; it cannot reach the other
cyclic block, since H--K is already the unique route. Thus it ends in
a genuine leaf and makes a forbidden bridge from H to a leaf root.
There are no further bridge branches at H.

There can be no nontrivial pendant bridge path rooted at K or either
of the other triangle's private vertices: any internal bridge body
would again need H as its inward neighbor, creating a second route
to H alongside the existing bridge H--K. All their possible further
bridge attachments are genuine direct leaves.

In particular K itself cannot carry any such leaf, by the accepted
bridge-to-leaf-root theorem from Section 1. Therefore K has no bridge
other than KH, while every original attachment at its triangle's other
vertices remains.

These are precisely the complete original hypotheses of Corollary 4
in GLOBAL_CLOSURE_INTACT_ROOT_DIRECT_BRIDGE_REDUCTION.md: H is an
intact root, every further H bridge is a genuine direct leaf (here
there are none), and K has no bridge branch other than KH. That theorem
retains every tip attachment and first proves physical circle clearance
of K from the full H equation. It then contradicts the actual small-disk
intersection of a leaf root at a private tip.

Its R>=2 premise is supplied by the accepted same-nine lower-bound
theorem NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md. The lower-radius finite
arithmetic certificate remains an inherited dependency; this assembly
does not claim that dependency has become table-free.

Thus the direct connector is excluded as well. The disjoint case is
complete, and Sections 2--3 exhaust the two-block incidence types.

## 4. Exact remaining original scope

Every still surviving C2.33.b2, C2.33.b3 or C2.33.b4 component must
therefore have **no intact petal anywhere in its original positive
graph**. For b2 the exact ten-layout cover leaves just the shared-H
attachment with one genuine leaf at a private tip of each triangle.
The full higher-bridge no-intact domains remain to be closed; they
are not removed by calling a decorated tip degree two.

The theorem is a whole-family exit covering all original force ratios,
circle masks, zero individual circle weights, original normals and
actual shared-side means. All nine physical squares remain. No positive
force was deleted to invoke a smaller exact graph, and no additional
normal was chosen after extraction. No sampled pose, numerical sign
packet, Lean compilation, CI, remote action or shared-ledger edit is
used.
