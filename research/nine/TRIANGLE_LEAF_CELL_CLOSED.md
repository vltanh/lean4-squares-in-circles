# The complete four-body triangle-plus-leaf cell is excluded

**Status: complete hand assembly; independent assembly audit passed. The full S proof and both exhaustive D proofs also have independent hand audits.** This closes the entire coarse cell **C1.3.b1**, including all physical contacts, all circle-corner weight masks, arbitrary individual frames, and all five remaining physical squares. The statement concerns the necessary selected certificate of a minimizing packing. It does not exclude every arbitrary stress on a smaller physical core.

## 1. Scope and simultaneous certificate choice

Let nine closed unit squares with pairwise disjoint open interiors be contained in a minimizing disk of radius R, in the declared window

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\]

The lower endpoint is supplied by the explicit n=8 deletion import in `LOWER_WINDOW_FROM_EIGHT.md`. The construction gives the upper endpoint. The inherited dependencies of that import remain as declared there.

At this fixed physical packing, choose the actual supporting normals before invoking the physical force-and-torque multiplier theorem. Impose simultaneously:

1. The strict point-contact, nonradial and diagonal exclusions used by the preceding structural reductions.
2. The matched opposite-pair normal choices at four-square junctions used by `PHYSICAL_BODY_GRAPH_UNCROSSING.md`.
3. The finite D-articulation determinant exclusions of `D_LEAF_GENERIC_CONTACT_SELECTION.md`.
4. The finite exceptional B/C normal exclusions of Section 1 of `D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md`.

These are compatible choices in a finite product of open strict-normal intervals. The articulation determinant exclusions have closed zero sets with empty interior after the variable shared-side case has been resolved. The additional B/C exclusions remove only finitely many directions for each physical candidate. Different articulation vertices are not coupled by one four-junction parameter. The B/C contact of an oblique candidate is distinct from its two side-interior articulation contacts. Thus all required conditions can be retained together; no normal is changed after obtaining a stress.

Apply the physical multiplier theorem, the exact shared-junction uncrossing, and conic thinning. These preserve force, torque, actual contact applications and every surviving preselected point normal. They add only actual shared-side endpoint atoms. The resulting body graph is planar, has at most 27 scalar atoms, and has exactly one positive component by `UNIQUE_POSITIVE_COMPONENT.md`. All other physical squares remain in the packing with zero stress.

## 2. Exhaustive four-body cyclic graph

Suppose this positive component belongs to C1.3.b1. Its graph consists of a triangle A--B--C--A and a single leaf L joined to A. There is no other graph or attachment orbit in this coarse cell.

`TRIANGLE_LEAF_CORE_REDUCTION.md` gives the full necessary structure:

- L is loaded and its bridge is radial.
- A is physically circle-clear.
- B and C are loaded; a circle-clear degree-two transmitter cannot have touching neighbors.
- L is physically closed-disjoint from B and C.
- The circle loads of B and C balance the radial leaf load, and every positive B/C circle corner is in the acute westward cone after rotating the leaf direction to the positive horizontal axis.
- The leaf is exactly radial S or radial D. The articulation has the complete corresponding pose cover, including the full S shared-side slider interval and its two tilted alternatives.

The same reduction retains every completion square and treats both a genuine triangular hole and a common three-body contact junction. This routing is available but will not be needed for a capacity estimate, because the core is excluded in every case.

## 3. The entire S alternative

`S_LEAF_TRIANGLE_EXCLUSION.md` proves that no such positive core has an S leaf anywhere in the radius window. The proof covers every aligned articulation height, both tilted branches, the zero-tilt and diagonal-tilt boundaries, all B/C contact types and every positive circle-corner mask.

Its closed 90-degree forbidden circle arc is inaccessible to any square touching the articulation. The touching pair B,C must have positive circle corners on both sides of that arc to balance the leaf. Such a pair is not acute, contradicting the contact-load cone theorem. This is a whole-core contradiction with no assertion about a separate capacity of either residual region.

## 4. The entire D alternative

Put s=1+sqrt(2)-R. The D articulation is

\[
                 A=[-s,1-s]\times[h-1,h],\qquad0<h<1,
\]

and its bridge applies horizontally at (1-s,0). The strict selected-normal convention accounts for the excluded bridge-endpoint cases; physical limiting packings are not discarded from the global certificate selection.

`D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md` proves that both triangle reactions point strictly left. Its support-span argument retains arbitrary application means on shared sides. The alternatives are exhaustive:

1. Both reactions are horizontal and leftward.
2. They have opposite nonzero vertical components and act at the two left articulation corners, with the exact height determined by their slopes.

`D_LEAF_GENERIC_CONTACT_SELECTION.md` removes point-only vertex/vertex articulation edges from the selected second alternative. Each articulation corner therefore lies in the relative interior of a side of the corresponding loaded neighbor.

`D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md` excludes that entire oblique alternative. Its compatible normal selection handles a remaining B/C vertex/vertex contact; then both actual side-axis owners, all signs, every physical one/two-circle-corner mask and all heights are covered. The required angle bound is derived from force and torque. The argument does not impose a symmetric frame.

`D_LEAF_PARALLEL_LEFT_EXCLUSION.md` excludes the entire horizontal alternative. If a neighbor shares a vertical side with A, the mutual-contact normal and a uniform corner-cap inequality force the other body to be circle-clear. If both wall supports are vertices, exact vertical sections exhaust the contact geometry. The coincident-breakpoint case contradicts torque directly. In the remaining case, geometry forces both circle loads to be unique left corners, and the two torque equations require a wall application height below -1, outside A. All shared-side means, arbitrary frames and circle masks are included.

Thus neither D alternative occurs in the selected certificate.

## 5. Whole-cell conclusion and global consequence

**Theorem 5.1.** The necessary physical certificate of a minimizing nine-square packing in the declared window can be selected, with all the preceding planarity, sparsity and uniqueness properties, so that its positive component is not C1.3.b1.

Indeed, the complete core reduction gives S or D; Section 3 excludes S, and Section 4 excludes both exhaustive D alternatives. Every extra physical square was retained throughout. Since the selected core itself is impossible, there is no need to bound its five extras separately. This proves the entire coarse-cell implication.

The exact positive D core in `D_LEAF_GENERIC_CONTACT_SELECTION.md` remains a valid control. It uses exceptional articulation normals; it is not a minimizing nine-square counterexample and is not an allowed final certificate under the simultaneous selection above.

**Corollary 5.2.** After the completed tree, two-load, isolated-triangle, four-body biconnected and present triangle-plus-leaf exclusions, the unique positive cyclic component has **at least five bodies**. It still has at most nine bodies and three to seven noncollinear circle-loaded resultants. Every one of the 9-m remaining physical squares stays in the completion problem.

To check the new lower bound on component size: the only cyclic simple graph on three bodies is the already excluded triangle; on four bodies the biconnected cases C4, the diamond and K4 were excluded in `FOUR_BODY_CYCLIC_CELL_CLOSED.md`, and the only remaining cyclic connected graph is the triangle plus one leaf, excluded here. Smaller positive components are trees, already excluded.

The coarse inventory now has **three whole cells closed and 55 open**. The four five-body frontier cells are C1.3.b2, C1.4.b1, C1.5.b0 and C2.33.b0. General C7 completion, those mixed cells and the larger mixed cells remain open. The unrestricted sharp theorem and complete equality classification are not claimed here.

This is a hand-proof assembly at the explicitly listed prerequisites. The independent full prerequisite-chain audit and standard-kernel formalization remain separate gates. No Lean compilation or CI was run.
