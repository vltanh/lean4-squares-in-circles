# Root physical review: coupled four-center conversion

The root reviewed the complete conversion proof, the generator, independent
checker and fixture driver on 4 November 2026. This review does not claim
human or proof-kernel verification. The accepted geometric premise is bound
in `PREMISE_BINDINGS.json`; no stronger packing conjecture is installed.

## Mathematics and source review

The six difference normals match the six physical pairs of the same four
centers. The first three bounds make the three-dimensional polytope bounded.
At a vertex the active normals span all three dimensions, so exhaustive
intersection of triples of its twelve boundary planes finds every vertex,
including lower-dimensional domains. The independent Gaussian reconstruction
checks the vertex list without using the generator's precomputed inverses.

The projected energy is a sum of six squares and hence convex. Every emitted
majorant is checked at every exact vertex. Convexity extends the inequality
to the whole closed domain. Floating hull calculations only nominate exact
planes; omitted proposals weaken the relaxation and cannot strengthen an
unproved row. Empty vertex sets yield an explicit contradiction only after
complete vertex enumeration.

The two perpendicular energies sum to the common squared projection norm
times the physical four-center energy. The direct row therefore has threshold
8 times that norm. The lifted auxiliary has the exact physical definition
'z equals the first projected energy', and its nonnegative upper bound is
the exact maximum at the vertices. The two lifted row signs and constant
terms expand to the direct Cartesian-product conversion. Every rational dual
using an auxiliary must pay its coefficient residual with this absolute bound.

## Caller obligations and replay scope

The guard checker proves the abstract polygon/polytope arithmetic for the
printed intervals. A physical caller must independently establish those
intervals from its original witness, check projection normalization, and
ensure auxiliary indices begin after every existing physical/auxiliary
variable. It must then check the literal weighted rows and their complete
case cover. A guard list alone does not establish a physical cell closure.

The relocated fixture replay passes 31 empty, point, segment, planar,
full-dimensional and varied rational cases; 449 vertices, 605 planes,
10,256 exact majorant comparisons and 21,410 conversion evaluations are
checked. The hand argument supplies the general proof; these fixtures
check the implementations. Run `python -B check_four_fixtures.py` here.

Both current D6 and B exploratory pilots remain OPEN. The accepted ledgers
remain 219/231 current-mask original cells and 8/32 masks CLOSED. This
conversion adds zero original-cell and whole-mask credit. No Lean, Lake
or CI was run.
