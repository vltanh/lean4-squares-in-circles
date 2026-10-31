# n=9: C1.4.b0 CLOSED — every four-body cyclic positive component is excluded

**Status:** whole coarse-cell hand exclusion, independent audit and Lean verification pending. The proof covers every allowable load allocation, every square orientation and every completion by the other five physical squares. It does not close P.ALL, Y.ALL, or larger cyclic cells.

**Dependencies and radius premise:** use the selected physical force-and-torque certificate in

    79/40 <= R <= sqrt(Q),  Q=1105/256.

The lower endpoint is an explicit imported n=8 dependency or a separate coarse-bound obligation, not newly proved here. Sources: ACUTE_LOADED_CONTACT_GRAPH.md, PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, and the new TWO_LOAD_RECIPROCAL_RIGIDITY.md.

## 1. Exactly three abstract adjacency cases, with no graphs omitted

Coarse cell C1.4.b0 means a connected simple positive body-pair graph whose single maximal cyclic block has four vertices, with no bridges. Hence the whole selected component is biconnected on exactly four bodies; the other five squares stay in the physical packing hypothesis.

Every biconnected simple four-vertex graph has minimum degree at least two. It therefore has 4, 5 or 6 edges:

- with four edges, every degree is two and the connected graph is exactly C4;
- with five edges it is K4 minus one edge, the **diamond**;
- with six edges it is K4.

These are a complete finite disjoint list up to relabeling. No body-graph planarity assumption is used.

## 2. Full load-pattern exclusions

### Case C4 — CLOSED by the preceding whole-cycle theorem

The component has at least two loaded bodies. Exactly two would, by Theorem N.5 of PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, require a six-body simple cycle at R^2=17/4. Exactly three or four loaded bodies have a disconnected physical loaded-noncontact graph: three give a touching path with a contact-universal middle vertex, and four give a complete touching join across the two opposite pairs. Both contradict ACUTE_LOADED_CONTACT_GRAPH.md, Theorem A.3.

Thus every possible loaded cardinality is excluded. This result was committed before the present continuation; it is not counted again as a new proof.

### Case K4 — CLOSED by the loaded noncontact theorem

Every positive pair is a true physical contact. The loaded subset is therefore a touching clique. Its noncontact graph has no edges but has at least two vertices, contradicting connectedness from Theorem A.3. All load patterns are excluded.

### Case DIAMOND — NEW complete closure

Label the nonadjacent degree-two tips A,B and the adjacent degree-three bodies U,V. The positive edges are AU,AV,BU,BV,UV.

By Theorem A.3, the loaded noncontact graph is connected. If exactly two bodies are loaded, they must be noncontacting; the only nonadjacent pair in the positive graph is A,B. If three or all four bodies are loaded, U or V is a loaded body touching every other loaded body, producing an isolated vertex of the loaded noncontact graph. Thus the **only remaining load pattern** is:

    A,B loaded; U,V unloaded.

Theorem R.1 of TWO_LOAD_RECIPROCAL_RIGIDITY.md now forces every positive pair force in this entire component to be parallel. Consequently every positive touching pair has disjoint interiors of its projection intervals on that common direction and those closed intervals meet at their supporting endpoint.

But the three positive edges AU,AV,UV form a triangle. Three positive-length intervals on a line cannot be pairwise interior-disjoint and pairwise intersecting: after ordering their interiors, the first and last are separated by the positive length of the middle interval. This contradicts the three positive physical contacts.

Equivalently, the high-radius two-loaded structure theorem forces a bipartite three-edge source-to-sink layer graph, while a diamond contains triangles. The direct interval argument above needs only the parallelism conclusion.

Therefore the last diamond load pattern is impossible. The square centers, angles, normal choices and the other five physical squares were never specialized or discarded. QED.

## 3. Gate and finite-inventory consequences

- [x] **C1.4.b0.C4:** all simple four-cycle components excluded (prior channel result).
- [x] **C1.4.b0.K4:** all complete four-body components excluded (loaded noncontact rule).
- [x] **C1.4.b0.DIAMOND:** the only residual loaded-tip pattern excluded by reciprocal-area parallelism.
- [x] **C1.4.b0:** the ENTIRE coarse cell is now excluded, for all complete nine-square realizations in the stated window.

The prior coarse inventory has exactly 58 cells. With C1.3.b0 already excluded, this makes **two closed coarse cells and 56 open**, not 57. This is a coverage count, not a percentage of the proof.

The two-loaded reciprocal theorem also restricts many load subfamilies across larger cells: every selected component with exactly two loaded bodies has R^2=17/4, aligned layers, and at most six bodies under the strict point-contact normal convention. Components with more loaded bodies, five/six-body two-loaded completion capacities, and all zero-stress geometric constraints remain explicit obligations. Do not tick a larger coarse cell merely because one load subfamily is excluded.

## 4. Scope, provenance and verification

The analytic new step is the force-polygon signed-area theorem applied to the planar **physical incidence** graph with exactly two external load ports. It proves parallelism without assuming a planar body graph or conflating the 19-term translational and 27-atom physical certificates.

The general packing argument needs independent audit, especially cyclic direction orders, aggregation of adjacent circle atoms into an exterior port, and recovery of pair forces at multiple junctions. Finite exact stress/graph regressions are additional evidence only. No Lean compilation, CI, independent full audit or unrestricted n=9 optimum is claimed.