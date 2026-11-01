# n=9 — actual proof progress

**Unrestricted optimality OPEN. Complete equality classification OPEN.
Full hand/table manuscript OPEN. Active gate: A.2.**

[Canonical roadmap](DEEP_GATED_ROADMAP.md) · [gate registry](gates/ACTIVE_ROADMAP.json) ·
[new containment theorem and tables](computer_assisted/DISK_SUPPORT_CERTIFICATES.md) ·
[actual independent replay summary](computer_assisted/disk_support_verification_summary.json).

## Same cover: 3,100 additional exact exclusions

The original **7,915** canonical positional root IDs, masks and cell lists are
unchanged. The new disk-support certificates add **3,100 exclusions** to the
previous 886: **3,986 EXCLUDED, 3,929 OPEN**. Every previous exclusion retains
its proof reference. These counts are not a percentage of mathematical effort;
OPEN does not assert feasibility, uniform difficulty or a completed solver run.

The new mathematical ingredient is an exact support formula for the center
region of a square contained in the disk. Maximizing it over a complete closed
orientation interval gives exact necessary halfplanes. Intersecting them with
the positional triangle contracts the continuous state before applying the
square-owned separating-axis tests. Polygon degeneracies and all weak contacts
are retained. This is stronger containment geometry, not angular sampling.

The selected **176 new cores have 4,182 propagation rows**. A separately written
implementation reconstructs the contracted polygons by feasible supporting-line
intersections rather than clipping, reproduces every compatibility edge, and
checks every propagation row candidate-by-candidate. It also independently
reconstructs and replays all **83 prior square-pose cores** and the original root
cover. Every current exclusion holds throughout the closed range q<=1105/256.

| Gate | Current status |
|---|---|
| A.0 / A.1a | Original physical-model source available; final independent source audit remains |
| A.1b / A.1c | Same exhaustive closed root cover and all stable IDs retained |
| A.2 | **ACTIVE: 3,986 excluded, 3,929 open** |
| A.3 | Global completion OPEN; all current and retained prior core certificates replayed |
| B.1 | Same equality-domain cover; attaining root 7820 remains OPEN |
| B.2 / B.3 | Full necessary-and-sufficient equality families OPEN |
| C.1 / C.2 | Full hand/table manuscript and independent human audit OPEN |

## One four-cell obstruction excludes 2,023 roots

Core mask 2118 occupies cells **1,2,6,11**. Four exact propagation rows reduce
cell 1's complete retained domain from 1,240 states to zero. Its twelve physical
symmetry images exclude 2,023 canonical roots, including **1,351 previously
open roots**. This is a theorem about those four specified occupied cells, with
arbitrary independent square orientations, not an assertion that four squares
cannot fit anywhere in the disk. The exact table, geometry and soundness proof
are in `computer_assisted/DISK_SUPPORT_CERTIFICATES.md`.

## Controls and verification boundary

All three geometry families preserve the oblique attaining packing under all
twelve dihedral symmetries. They also preserve 99 genuinely side-touching pair
controls in total, covering every orientation-interval endpoint and midpoint.
Additional rational physical-square controls check the support halfplanes.
Fourteen deliberate certificate/domain mutations are rejected. All proof
comparisons use integers and rationals; array operations have explicit bounds
excluding int64 overflow. No numerical solver result is used as a proof.

The repository contains the complete source, explicit selected core list,
mathematical derivation and execution summary. The continuation archive also
contains the full generated certificate, unchanged-ID root manifest and full
verification report. Their hashes are pinned in the summary. Reproduction
reconstructs every graph; exploratory caches are not trusted or required.
No separate human review, global UNSAT result, Lean, Lake or CI is claimed.

## Remaining A.2 task

Close groups of the **3,929 original physical root predicates** still OPEN.
The new tests exclude closed-Q domains; they cannot exclude a domain containing
an attaining packing. Such domains require a sharp proof for every q<Q, not
endless attempts to make their feasible q=Q portions empty. Preserve the same
cover, root IDs, exact boundary accounting and closure evidence. No new gates
or alternative progress denominator are introduced.
