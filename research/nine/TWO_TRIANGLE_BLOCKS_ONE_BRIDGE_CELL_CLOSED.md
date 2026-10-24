# The complete six-body cell with two triangle blocks and one bridge is closed

**Status: complete whole-cell hand assembly; root and separate independent
full assembly audits passed.** This closes C2.33.b1 of
SIX_BODY_CYCLIC_FRONTIER.md, with all three of its attachment layouts.

Work in the common selected necessary physical certificate and the
inherited declared radius window
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The exact positive component has six bodies, two nonbridge blocks
which are triangles, and exactly one bridge. All three other physical
packing squares remain arbitrary and present. Original contact owners,
shared-side means, physical circle masks, individual zero circle weights
and physical zero-weight contacts are retained.

**Theorem.** No selected positive component has this whole coarse cell.
The proof is a core exclusion for every layout; it does not merely
exclude a chosen placement or one load allocation.

## 1. Exactly three attachment layouts

Distinct graph blocks intersect in at most one vertex, and their
block-incidence graph is a tree. If the two triangles share a vertex H,
their union has five vertices. The sixth body is a leaf attached by
the unique bridge to that union. Up to the bowtie symmetry its attachment
is either H itself or one of the four equivalent triangle tips.

If the triangles are disjoint, they already use all six vertices. Their
unique bridge must join one vertex of each triangle. Triangle symmetry
gives one layout. These cases exhaust every relation between the two
triangle blocks and the bridge; no graph-generation table is needed.

| Full attachment layout | Exact changed articulation degrees | Whole exclusion |
| --- | --- | --- |
| Two triangles sharing H, bridge leaf at H | H has degree5; all four triangle tips degree2 | ONE_ARTICULATION_TRIANGLE_LEAF_EXCLUSION.md |
| Two triangles sharing H, bridge leaf at a tip A | H has degree4; A degree3; the other three triangle tips degree2 | TIP_LEAF_BOWTIE_EXCLUSION.md |
| Two disjoint triangles joined by their bridge | Both bridge endpoints degree3; the other four triangle vertices degree2 | OUTER_BRIDGED_TRIANGLE_CAP_EXCLUSION.md, Section5 |

## 2. The shared-articulation leaf layout

The common-articulation theorem applies with k=2 true triangle petals
and l=1 actual radial leaf. Its four triangle tips have exact degree two
and are loaded; the leaf has exact degree one and is loaded; H is clear.
Each real triangle contributes strictly positive pressure at c_H, and
the actual S or D leaf contributes strictly positive pressure there as
well. Their genuine global sum is zero, a contradiction.

The theorem explicitly allows the true degree-five articulation. No
triangle force is dropped and no scalar mean is fixed artificially.

## 3. The tip-attached leaf layout

Use the graph H--A--B--H, H--C--E--H, A--L. Its complete assembly
TIP_LEAF_BOWTIE_EXCLUSION.md now covers the entire leaf classification:
the full D type and both aligned and tilted S articulations.

The aligned and tilted cases retain every actual frame and side mean.
The tilted domain proves the full parallel/nonparallel concurrence
cover and all three remaining owner/frame alternatives before applying
their complete exclusions. In every branch the higher-degree H carries
its actual two incoming forces and the complete C,E petal. It is never
made into an unchanged degree-two triangle tip.

Thus this entire second attachment is excluded, not only its former
D-leaf or aligned-S subfamilies.

## 4. The two disjoint triangles joined by the bridge

Each bridge endpoint is a true degree-three end-triangle root, and its
two other triangle vertices are true loaded degree-two tips. The radial
bridge theorem gives one actual application p=rho n. Reversing the
bridge replaces rho by -rho, so one orientation has rho>=0, including
p=0.

OUTER_BRIDGED_TRIANGLE_CAP_EXCLUSION.md excludes every such outward
end-triangle interface, with an arbitrary external bridge component
still attached. Equivalently each true end triangle requires a strictly
negative dot product between p and its tip resultant. Both ends cannot
meet that condition on the same bridge. This is the complete third
layout, not an inference from pressures at two different body centers.

## 5. Common prerequisites and whole-cell scope

Every source uses the same compatible pre-certificate selection, with
its finite end-triangle, fixed-tip and articulation candidates prelisted
in the whole physical packing. The graph cover does not choose separate
certificates for separate layouts. Uncrossing and thinning retain the
meaning of the original positive degrees and actual means.

The present result inherits the lower-window prerequisite79/40 and the
selected-component construction. It supplies a complete exclusion
inside that declared domain; it does not independently establish the
lower-radius theorem or the global uniqueness/selection machinery.
The already established one-/two-load restrictions, where used in
obtaining the global frontier, are likewise not replaced here.

All three rows of the exact attachment cover are now excluded, with all
three remaining physical squares fixed. Hence C2.33.b1 is closed at the
whole selected-component scope. No claim is made about a larger graph
obtained by adding a positive edge at one of the degree-two tips, or
about any other six-body coarse cell. Original equality classification
and final global prerequisite-chain auditing remain separate obligations.
No Lean compilation, CI, completion motion or numerical angle boxes are
used in this assembly.
