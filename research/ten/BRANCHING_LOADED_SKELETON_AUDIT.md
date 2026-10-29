# Independent audit of the loaded-branch skeleton catalog

**Result: PASS, 2026-10-29.** This audit checks the finite `b=0`
overclassification and both printed exclusion predicates. It does not
exclude the retained records, the `b>0` subclass, or C05 as a whole.

## Mathematical coverage

The reviewed suppression theorem retains every loaded body and suppresses
only unloaded bodies of degree two in the whole positive component.
Consequently `b=0` has precisely its loaded bodies as retained vertices.
With two such vertices the entire component is a union of internally
disjoint transmission paths between them, so the two-terminal theorem
applies. This use of that theorem does not extend to `b>0`.

The seven symbols exhaust the reviewed distance, width, and bundle
restrictions. Their multiplicities and body costs are counted separately;
in particular double-S and SS are distinct. Connectivity, positive body
cost, at least k multiedges, maximum degree between three and eight, and
the body budget are necessary for the stipulated mixed branching cyclic
component. The loaded-neighbor contact restriction applies at k>=4. At
k=3 every pair is a circular neighbor, while two direct edges would create
a loaded contact star containing all component loads, which is forbidden.

For alternating transmission chords, the two represented paths have
disjoint retained endpoints and disjoint internal bodies. The local S
and SS junction exclusions use no restriction on the degrees of their
loaded endpoints, so their use here is valid. The D-D crossing possibility
is retained. No planarity assertion or simple-cycle-only D-D theorem has
entered this catalog.

All loaded rays are distinct. Choosing their cyclic order leaves exactly
the dihedral changes of starting point and orientation as label symmetries.
Both implementations take the same lexicographically least code under
this group; neither quotients by arbitrary graph isomorphisms.

## Angular and bridge deductions

The minor separation of any loaded pair exceeds 36 degrees. A touching
pair's minor separation is less than 72 degrees. A direct neighbor gap
must be that minor arc, even at k=3: its complementary arc contains at
least two other gaps and therefore exceeds 72 degrees.

The path-width argument gives endpoint center distance at least `1+W`
independently of endpoint degree. The reviewed radius bounds then give
half-angle lower bounds `asin(16/25)`, `asin(328/425)`, and `asin(24/25)`
for S, D, and SS. The exact comparisons with 36, 45, and 72 degrees give
the catalog's full-angle bounds 72, 90, and 144. Both arcs between the
endpoints exceed the minor-angle lower bound. Thus all integer strict
difference inequalities reconstructed by the checker are valid in this
branching scope.

Every stored angular witness is checked to be a directed simple cycle
of actual case inequalities. Its bounds sum to at most zero, so summing
the strict inequalities gives `0<sum(bounds)<=0`. No floating-point
optimization result is a proof premise. There are 3,587 such witnesses,
using 60 bound multisets.

The loaded bridge theorem also passes: every original edge of a bridge
path is a bridge, its common force line is radial, and the endpoint
contacts must lie on opposite rays. The S width contradicts the endpoint
radial lower bounds. For D, the selected nonradial vertex/vertex-normal
convention forces relative side-interior contacts on both loaded
endpoints. The explicitly imported n=8 lower window then makes their
two positive radial distances sum to more than the D width. Direct
bridges are excluded by the circle-clear bridge endpoint theorem.
SS remains allowed. The graph checker supplies an actual singleton
cut for each forbidden bridge; parallel symbols are never treated as
bridges of a single copy.

## Reproduction

Re-ran the Python enumerator with `--verify`, independently compiled and
ran the C++ enumerator, and compared every canonical code after sorting.
Both produce exactly 45,666 codes, with k-counts
`35, 1234, 10305, 22407, 11685`. The individual code sets agree, not only
their totals.

Re-ran the integer-cycle and bridge checker. It verifies 36,828 forbidden
bridge records, 2,466 also in the angular list, hence 37,949 distinct
exclusions and 7,717 retained codes. The retained k-counts are
`26, 612, 2840, 3251, 988`.

The audit added checks that generated catalog metadata and hashes match
the published inventory, that count tables cover every k exactly once,
and that inventory totals and bridge-witness type counts match the
reconstructed predicates. No geometric case was removed or relabeled.
These checks are exact combinatorial verification, not Lean verification.
