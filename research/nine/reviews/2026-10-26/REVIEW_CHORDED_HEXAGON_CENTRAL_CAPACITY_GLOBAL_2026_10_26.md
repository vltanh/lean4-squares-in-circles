# Independent full review: chorded-hexagon central capacity

Date: October 26, 2026.

Reviewer: global-closure subagent.

**Decision: ACCEPT, at the stated whole central-capacity scope.** No correction is required. This review does not close a graph/load parent, the HEXAGON.BOUND parent, or the coarse C1.6.b0 cell.

## 1. Exact reviewed source and dependencies

The complete source reviewed is `CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`, SHA-256

    bf4d69e73cdb008f093b47c6e86dc3d7c767a5c0d03bd24d046aef62a314f1b8

The audit read every section and checked the original inheritance against `CONTACT_RING_HOLE_AREA.md`, the complete equality proof in Sections 1--2 of `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`, the independent degree-free formulation in Section 2 of `SPANNING_K23_LEAF_BLOCK_EXCLUSION.md`, and the eight-type/34-orbit cover in `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md`.

The actual six units, actual positive chords, physical plane embedding, all loads and true endpoint degrees are retained. No cycle equilibrium equation is introduced at a chord endpoint. In particular the equality lemma used below has no hidden three-boundary, leaf, degree-two, or circle-load hypothesis.

## 2. Complete face cover and physical routing

All eight face lists agree with the original noncrossing chord cover. The single short chord leaves a triangle and pentagon; the single diameter leaves two quadrilaterals; each two-chord type leaves two triangles and one quadrilateral; and the three triangulated types leave four triangles. This includes the central-triangle triangulation and both non-central triangulation types.

Every central extra has its open interior disjoint from the closed core units. The occupied center/contact paths therefore separate its connected interior into one actual face side. The compact-interior routing argument retains the same face label at weak junctions, then recovers the whole unit area by closure. Further physical contacts can subdivide a face but cannot remove the occupied barriers or merge bounded sides. Thus the argument controls the whole bounded free union, not merely one preferred hole.

The use of the contact-ring area theorem is valid for each of these actual face rings. For triangles its bound is sqrt(3)/4<1. For pentagons, cot(pi/5)^2=1+2sqrt(5)/5<2<(3/2)^2 gives area<15/8<2, hence at most one unit in the whole face union. These strict inequalities require no load or radius assumption.

## 3. Four-ring equality inheritance

I checked the complete equality chain, including coincident-contact exits, rather than assuming that the title of the older three-boundary source described the lemma being imported.

A whole enclosed unit forces equality throughout the area and chord-cut bounds. Opposite coincident contacts have zero winding; consecutive coincident contacts give a triangle of area below one. The four contacts are therefore distinct. Every original chord has length one, because the individual chord contribution has its unique maximum at that length. Equality in the four-sided polygon-area estimate then makes the contact polygon a unit square. Any original ring chord entering the interior of its own unit would remove positive area from that polygon, so every ring chord is a full side of its actual unit. The four original units lie on the exterior sides and the enclosed unit fills the central square. This is precisely the full aligned cross stated in the new source.

The original three-boundary hypothesis first enters the later radius contradiction in Section 3 of `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`. It is not used in the contact, chord, area, or alignment arguments of Sections 1--2. The independent statement in `SPANNING_K23_LEAF_BLOCK_EXCLUSION.md`, Section 2, confirms the same radius-free, degree-free conclusion. All weak contacts are resolved by the equality argument itself.

## 4. Two occupied quadrilateral faces

The only possible sum of individual face capacities exceeding one is the single diameter chord 03. Applying the aligned-cross lemma to the first face fixes the actual four units 0,1,2,3, including the unique intersection p of 0 and 3. Applying it to the second face preserves those same actual units and therefore the same frame; it does not introduce an independent orientation choice.

At p, units 0 and 3 occupy the northeast and southwest quadrants, and the first central unit occupies the northwest quadrant. The second central unit must occupy the southeast quadrant, on the actual second face side. Its center is (1,-1) in the displayed first-cross coordinates, and the actual remaining centers are c4=(1,-2), c5=(2,-1), up to the stated reflected/reversed relabeling. Hence the original pair c1,c4 has squared distance 10.

The universal contained-center bound remains about the original disk origin. Translating coordinates to display the crosses does not affect the forced pair distance, and no translated center-norm estimate is asserted. The exact comparisons

    (91/60)^2 + 91/60 + 1/2 - 1105/256 = 31/57600 > 0,
    10 - (91/30)^2 = 719/900 > 0

therefore give a strict contradiction. This excludes simultaneous occupation of the two quadrilaterals, including every actual shared-contact endpoint.

## 5. Exact accepted conclusion and remaining parents

The proof establishes central capacity at most one for all eight positive-chord outer-hexagon graph types. For the three triangulated types it establishes central capacity zero. The load-free geometry is uniform over the complete 34 original graph/load orbits, with no artificial degree or physical-mask restriction. Consequently at least two of the three additional units in a nine-packing must be exterior, or all three for a triangulated type.

The source accurately leaves the exterior joint-capacity problem open. This necessary allocation theorem alone excludes no whole graph/load orbit, no HEXAGON.BOUND parent, and no coarse C1.6.b0 cell. Non-hexagonal six-body embeddings are outside its theorem. No positive chord, positive load, or actual extra is removed in the proof or in this review.

No Lean compilation, CI, numerical sampling, remote mutation, or shared-ledger edit was used.

