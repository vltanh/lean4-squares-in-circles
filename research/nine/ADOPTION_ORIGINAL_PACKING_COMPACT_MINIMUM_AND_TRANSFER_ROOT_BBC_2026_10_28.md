# Root adoption: original Packing attainment and complete G4.2.a

Date: October 28, 2026 UTC. Author and adopter: root.

**Accepted unchanged after a complete independent review by a
noncontributor. The entire original G4.2.a is closed mathematically.**
The proof covers every finite family in the exact original Packing
predicate, obtains a global minimum and a finite continuous canonical
refinement, and proves the stated conditional transfers back to arbitrary
original packings. The sharp lower bound, simultaneous certificate selection
and equality classification remain separate obligations.

## 1. Exact source, independent review and original definitions

| Object | Bytes | SHA256 | Git blob |
| --- | ---: | --- | --- |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | 15756 | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | `78056e2005e0c2a01c0a4d0c466830edee9ed05c` |
| `REVIEW_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_COMPLETE_INDEPENDENT_BBC_2026_10_28.md` | 22755 | `65024715d38edd24c303c280ddbb5a4496044be04c5ab4a324d1de85e01f912c` | `fd1c4bcf5fe23ac39b17271c18b2ce7ac20b1eef` |
| `INDEPENDENT_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_EXACT_RECORD_BBC_2026_10_28.json` | 21839 | `db06a50d9782dfe572783daa9699cc2923c6a4b62efbab72f6bdbdfd403639d4` | `2ca47a65c2dc40260c72ac3582a33b58d87449fa` |
| `SquaresInCircles/Geometry.lean` | 20319 | `64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94` | `14e10cb5be282f490ad46ac2cac63185de4ff566` |
| `research/nine/SPARSE_MINIMIZER_STRESS.md` | 16597 | `b182276dace03bf64d9903145e8861022712b05f7ff7317ad62f30f97850e9ac` | `5ee6d10f5e7a2770ae1916f0f65cf7ca73b4e868` |

The comparison is `bbc1e87f65168bba704d2b21a91faf0e313945c2`.
Root authored the complete312-line source and is not its independent
reviewer. `broad_s_families` contributed no discovery or repair, and read
all312 source lines, all525 lines of the exact Geometry file and all419
lines of the provenance manuscript. Root then read all463 lines of the
frozen independent report and the entire446-line exact record. The six
named payloads were rehashed; the actual definition, provenance, roadmap
and checkpoint blobs match the exact current tree.

The record checks eleven literal definition blocks,27 exact coordinate
identities, four endpoint facts and the whole continuous proof. The
finite identities corroborate the displayed algebra; compactness, strict
limit stability, globality and the equality quantifiers are proved on the
whole continuous domain, without a pose enumeration.

## 2. The exact original predicate is retained

An original UnitSquare consists of a real center c and real C,S with
`C^2+S^2=1`. Set `u=(C,S)` and `v=(-S,C)`. Orthonormal inversion gives
exactly the original localX/localY coordinates and identifies its closed
and open square with `c+xu+yv`, with the respective weak and strict
half-side bounds. Both directions of this equivalence are used.

Packing retains its full conjunction: a nonnegative real radius, whole
closed-square containment in the squared disk, and absence of a common
open-square point for every pair of distinct original labels. Closed
square sets need not be disjoint. All side-sharing, vertex, multiple-contact
and tangency endpoints remain. Each frame ranges over its own entire unit
circle. No angular chart, common orientation, contact type or quotient by
frame representation is imposed.

One common translation subtracts the actual containing-circle center from
every square center and physical point. It leaves all actual local
coordinates, strict/weak memberships, disk displacement and labels
unchanged; translation back proves equivalence. This removes the otherwise
unbounded circle-center coordinate without restricting the original
problem. Every center-energy comparison is consequently relative to that
same actual containing-circle center.

## 3. Closed feasibility gives compact global attainment

For any supplied original feasible radius R0, use the finite-dimensional
product

    [0,R0] x product_i (closed_disk_R0 x unit_frame_circle).

It is compact. Every original packing of radius at most R0 translates
into it because each actual center lies in its own closed square and
therefore in the disk. The product retains every original label. For
zero squares the empty coordinate product is one point.

The feasible subset is nonempty at the translated witness. Whole square
containment is exactly the conjunction of the four actual corner
inequalities: the nonnegative weights
`(1+2 epsilon x)(1+2 eta y)/4` sum to one and reconstruct every closed
square point from those four vertices. Convexity of the closed disk gives
the equivalence, including zero radius and side/corner weights equal to
zero. Each corner inequality is closed and continuous in all coordinates.

Nonoverlap is closed directly from the original strict predicate. If a
coordinate limit had a common open-interior point p in two distinct
labels, all four absolute local coordinates at that fixed point would
have maximum m<1/2. Continuity and the positive margin `(1/2-m)/2`
would make the same point belong to both open interiors for every
sufficiently late feasible tuple. This contradicts their original
nonoverlap. No separating-normal choice, moving witness or stable contact
stratum is needed. The feasible subset is thus compact. No two labels
can merge into the same nonempty physical square, although new boundary
contacts are allowed at the limit.

The continuous radius attains R*. This is a global minimum: any original
packing at radius R<=R0 translates into the compact family, while any
R>R0 already satisfies R>R0>=R*. The artificial compactness ceiling is
not an extra physical constraint in a later stress problem. On the
original nonnegative domain, the factorization
`R^2-R*^2=(R-R*)(R+R*)` gives the same global squared-radius minimum.

## 4. Canonical refinement and every endpoint

The full radius-minimum fiber is compact and nonempty. Successively
minimizing any prescribed finite list of continuous real functionals
leaves compact nonempty fibers and gives the stated lexicographic minimum.
The empty list is included; no uniqueness or infinite selector process
is asserted. In particular the finite continuous sum

    Phi = sum_i |c_i|^2

has a minimum among all original origin-translated radius minimizers,
before any graph, stress or normal selection. A motion contradiction at
this canonical packing requires a feasible competitor for the entire
original Packing predicate at the same radius and a strictly lower total
Phi. Verifying a motion against only a stressed core is insufficient.
Preserving an earlier chosen stress certificate is unnecessary for this
specific global-minimization comparison.

For n=0 the attained radius and Phi are zero. For n>=1, the average of
the four squared vertex norms is `|c_i|^2+1/2`, so R^2>=1/2 and R>0.
At equality all centers are zero. For n>=2 even the origin is then in
two open interiors, impossible; hence R^2>1/2. The n=1 equality endpoint
is retained. Radius R=R0, full frame-circle limits and all original weak
contact endpoints are included throughout.

## 5. Transfers and the distinction needed for equality classification

An original counterexample R^2<Q gives, by the same construction, a
radius/Phi minimizer with `0<=R*<=R` and `R*^2<Q`. The counterexample
itself supplies R0; no sharp upper construction is needed for this
contradiction entry. Once a separate theorem excludes all such canonical
subcritical minima, the original universal lower bound follows.

Equivalently, an actual proof of R*^2>=Q implies R^2>=Q for every
original packing. If this universal lower bound and an actual upper
witness with squared radius at most Q are both supplied, the least radius
is sqrt(Q). The proof is conditional on those stated premises and does
not produce the missing sharp bound or witness by compactness.

After the universal bound is established, each particular original
equality packing R^2=Q is itself a radius minimizer. It need not minimize
Phi. Replacing it by a different canonical minimizer can change its
unstressed bodies and physical geometry. A strict Phi-motion exclusion
therefore cannot automatically classify every original equality packing.
The exact original congruence predicate and every equality unit remain;
the source claims no uniqueness of frame, labeling, stress or optimum
model.

## 6. Literal original G4.2.a closure and precise accounting

At the exact current checkpoint, original index2457 is
`{"id":"G4.2.a","checked":false}`. Its roadmap statement is:

> Start from the original nine-square Packing predicate and obtain a compact
> minimizer with no extra orientation/contact hypothesis.

Sections2--3 of the accepted source prove this entire original statement
at n=9, without a narrower geometric feature. This is full gate coverage.
Root adopts precisely that existing original update, false to true, for
the next exact-base local package. No new identifier or subdivision is
introduced, and the published checkpoint itself is left unchanged.

The conditional transfer toward G4.2.f is proved, but its sharp minimum
bound premise remains open. No whole G4.2.f credit is assigned here.
G4.2.b lower-window entry in its complete literal scope, G4.2.c simultaneous
selection, G4.2.d complete branch exclusions, G4.2.e sharp minimum bound,
the G4.2 parent, all original equality classification gates and the full
G6.1 audit remain outside this closure.

SPARSE_MINIMIZER_STRESS Section1 is provenance, not an imported proof
premise: the new source supplies the whole compactness proof itself.
No later translational sparsity statement, nineteen-term specialization,
torque-stationary certificate, strict normal selector, planar embedding,
uncrossing or thinning conclusion is imported. Those compatibility
interfaces require their own complete arguments.

This chain adds exactly one accepted original fine update, G4.2.a,
zero parent/coarse updates, zero computational certificates and zero
retirements. Together with the three earlier accepted but unpublished
D02 updates at indices2068,2069,2073, the prospective original array at
unchanged BBC has2359 checked and154 open fine entries; the coarse array
remains34 closed and24 open. These counts describe heterogeneous original
tasks and are not a mathematical completion percentage.

No source repair was needed. No authoritative flag, old review or Lean
definition was altered by this adoption. No Lean compilation, numerical
geometry checker, CI/workflow dispatch, remote write or merge was run.
The exact original-gate plan carries the source, review and root-adoption
hashes separately so integration can verify this one new whole update.
