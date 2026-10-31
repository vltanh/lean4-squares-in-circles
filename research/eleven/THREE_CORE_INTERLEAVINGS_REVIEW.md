# Independent review of the seventeen three-core interleavings

**PASS as a coarse geometric cover.** The assignment to ring gaps follows
from the split-gap theorem, the connected open ring arcs, and physical
interior disjointness. A positive-length core hull cannot cross a positive-
length ring arc, so it belongs to one ring gap. Ignoring tangent-only cores
enlarges the cover and retains their physical constraints; it does not omit
a packing. Zero-length ring gaps cannot receive a positive-length core hull.

I independently enumerated the words using multisets of zero through three
gap positions, rather than the generator's Cartesian-product traversal.
For each multiset I formed its length-eight multiplicity word and applied
the sixteen explicit index permutations `i -> offset +/- i`. This recovered
all **165** raw words, exactly **17** canonical words, every serialized orbit
size, and row counts **1, 1, 5, 10** for zero through three active cores.
The manuscript's displayed words match the JSON exactly. Retaining reflection
as a relabeling of cyclic order is legitimate for this coarse cover; the
manuscript correctly preserves actual physical orientation data.

The candidate illustration was checked separately on the existing exact
rational root rectangle. Its maximum corner squared norms obey the strict
bounds

- core 4: between `2.0350` and `2.0351`, above `rho^2=1.8225`;
- core 8: between `1.6219` and `1.6220`, below `rho^2`;
- core 1 at slider endpoint `H`: between `1.7193` and `1.7195`, below `rho^2`;
- core 1 at slider endpoint `a`: between `1.8536` and `1.8538`, above `rho^2`.

For core 1 the relevant far-corner norm is strictly increasing in its positive
slider coordinate, and its other three corners stay inside the auxiliary
circle. Thus it has one transition from inactive to active. Exact interval
cross products confirm cyclic ring order `(7,6,5,3,2,0,10,9)` and active-arc
points in the claimed `5 -> 3` and `2 -> 0` gaps. Those gaps have cyclic
distance two, confirming candidate rows `00000001` and `00000101`. The
candidate feasibility and existence remain conditional on the separately
reviewed exact root certificate; this review does not reprove it.

Reviewed SHA-256 digests:

| Artifact | SHA-256 |
| --- | --- |
| `THREE_CORE_INTERLEAVINGS.md` | `cbd7a31d129b9576380e151d506c99f86f417bff5edf288370bbd794939a3e0d` |
| `enumerate_three_core_interleavings.py` | `37b30901cb0c178a714a218a83c5f92a062afd4ea6237840ed59efec40a649b0` |
| `THREE_CORE_INTERLEAVINGS.json` | `9e00bca4004fb0b098a37cd202e8c00c817488b6b7bcf6862682651b3bc61ffd` |

No row is excluded by this enumeration, and neither candidate capture nor
global sharpness follows from it. Continuous poses, all corner inequalities,
and all physical pair constraints must still be retained in each row.
