# Planar-order and diagonal-forest filters for the fixed branching catalog

**Status:** independently reviewed exact finite consequences of the
selection and graph theorems, including every certificate and count
(2026-10-29). These two
filters take the fixed C05 `b=0` ledger to **42,532 excluded records** and
**3,134 remaining records**, out of its unchanged 45,666. C05 and the
unloaded-branch subclasses remain open.

## 1. Select one compatible certificate before classifying

Use [PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md)
to choose a physical stress with a planar positive body-pair graph. Its
normal choices also satisfy generic diagonal avoidance and the loaded-VV
polynomial restrictions: their compatibility is proved there. Classify
the graph only after the local force replacements and aggregation.

In the `b=0` subclass every retained skeleton vertex is loaded. Its planar
disk embedding puts those vertices on the boundary in their loaded-center
radial order. Suppressed paths are internally vertex-disjoint, and
suppression preserves the planar multigraph embedding.

If two skeleton edges have four alternating boundary endpoints, their
two disjoint arcs would cross by Jordan separation. This is impossible.
The raw catalog had already excluded every such alternating pair except
two single D paths. Thus the new condition excludes the remaining D-D
alternations without deleting or relabeling raw records.

The certificate in
[branching_planar_rejections.tsv](branching_planar_rejections.tsv) gives
`case_ID, edge_index_1, edge_index_2` as three tab-separated fields. The
indices are zero-based in lexicographic unordered-pair order. They name
two present edges with alternating endpoints. Each witness is therefore
a complete finite contradiction to the selected planar disk embedding.

This is a restriction on the chosen certificate used in the lower-bound
reduction. It is not an assertion that every possible physical stress
graph of a packing is planar, nor that an old graph stays fixed during
the selection.

## 2. The D-edge graph is a forest of paths

[DIAGONAL_PATH_GRAPH_RESTRICTIONS.md](DIAGONAL_PATH_GRAPH_RESTRICTIONS.md)
proves that the digit-4 subgraph is acyclic with maximum degree two.
Its proof applies to all retained endpoint degrees. Generic selection
forces D contacts into relative side interiors, so frames propagate
between endpoint bodies. Two D paths cannot leave the same or opposite
sides of one body. Successive D edges therefore use perpendicular axes.
Odd cycles cannot alternate those axes, while an even cycle's two axis
matchings contradict the universal center-radius bound.

[branching_d_forest_rejections.tsv](branching_d_forest_rejections.tsv)
contains four tab-separated fields:

```text
case_ID   witness_kind   pivot   comma-separated_witness
```

For `degree`, the pivot is a vertex index, and the witness lists three
distinct incident digit-4 edge indices. For `cycle`, the pivot is -1,
and the witness lists distinct vertex indices in cyclic order; every
successive pair, including last-to-first, is a digit-4 edge. Either form
directly contradicts the reviewed D-graph theorem.

## 3. Exact counts and overlap

The preceding [SS-bridge ledger](BRANCHING_SS_BRIDGE_FILTER.md) excluded
40,336 raw records. The planar-order list has 9,349 records, of which
2,071 are new. The D-forest list has 2,814 records. It contributes 402
new records relative to the preceding ledger alone, or 125 new records
after the planar-order list is also included. Thus

```text
40,336 + 2,071 + 125 = 42,532 excluded,
45,666 - 42,532 = 3,134 remaining.
```

The per-loaded-count table is:

| Loaded k | New planar exclusions | New D-forest exclusions after planarity | Total union excluded | Remaining |
| --- | ---: | ---: | ---: | ---: |
| 3 | 0 | 0 | 16 | 19 |
| 4 | 79 | 7 | 939 | 295 |
| 5 | 700 | 43 | 9,277 | 1,028 |
| 6 | 1,026 | 63 | 21,096 | 1,311 |
| 7 | 266 | 12 | 11,204 | 481 |
| Total | 2,071 | 125 | 42,532 | 3,134 |

All raw and overlap counts are in
[branching_selected_graph_summary.json](branching_selected_graph_summary.json).
The fixed raw catalog and every earlier certificate are preserved.
Passing these necessary graph tests asserts neither geometric feasibility
nor existence of a positive stress. Counts do not measure proof effort.

## 4. Verification and reproduction

The [builder](build_branching_selected_graph_filters.py) prints explicit
witnesses. The [checker](check_branching_selected_graph_filters.py) does
not import it: it validates every alternating pair, degree witness, and
simple cycle, then independently reconstructs the complete predicate ID
sets using an interval-side test and union-find cycle detection. It
checks every printed count and the combined union with earlier results.
An independent auditor reproduced the full rejected-ID sets by enumerating
boundary quadruples and checking component ranks, without importing the
builder or checker, and independently reconstructed the earlier bridge
cuts. All counts and witnesses agreed.

```sh
python3 research/ten/build_branching_selected_graph_filters.py --check
python3 research/ten/check_branching_selected_graph_filters.py
```

The raw catalog retains its separate Python/C++ coverage verification.
None of these checks is Lean verification.
