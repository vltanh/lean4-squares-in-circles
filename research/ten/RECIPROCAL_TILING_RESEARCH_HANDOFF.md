# Reciprocal polygons tile the external force polygon

**Status: unreviewed research note, not promoted.** Preserved at the
2026-10-30 handoff. No theorem or case closure is inferred from this draft.

The force-normal-order embedding and circle-edge merging from
TWO_LOADED_PARALLEL_FORCE_REDUCTION extend to any loaded count k.
After separately merging the circle atoms of each loaded body, its
nonzero resultant direction stays within pi/12 of its center ray.
The loaded center rays are separated by more than pi/5, so the
resultants retain their strict circular order. At the exterior ground
vertex they occur in reverse order. Their sum is zero.

For k>=3 this produces a clockwise convex ground polygon Q; each body
has a counterclockwise convex reciprocal polygon P_i, possibly
degenerate. The same reciprocal face potentials give these polygons
simultaneously. Every primal edge contributes one reciprocal segment
to each endpoint polygon in opposite directions.

Therefore for every point z off all reciprocal edges,

    sum_i winding(P_i,z) + winding(Q,z) = 0.

This follows by adding the angle increments along each directed edge;
opposite copies cancel. Convexity then gives

    sum_i 1_{z in interior(P_i)} = 1_{z in interior(Q)}.

Consequently the positive-area body polygons have pairwise disjoint
interiors and fill Q up to finitely many polygon boundaries. No prior
embedding or disjointness of reciprocal polygons was assumed. This
argument alone does not control possible degenerate reciprocal cells.

It also does not bound the number of unloaded positive-area cells by
k-2. A reciprocal-only counterexample respecting the ground incidence
rule is obtained from an inner homothetic triangle inside a triangular
ground polygon. Partition the annular region into three convex
trapezoids, each containing one entire ground side, and regard these
as the loaded cells. Subdivide the inner triangle from its centroid
into three convex triangles, regarded as unloaded cells. This gives
k=3 but three unloaded positive-area cells. It is a counterexample to
that inference from convex tiling, not a physical unit-square packing.

Any stronger numerical bound must also use the physical square geometry,
torque equations, body budget, or minimum-active-certificate reductions.
