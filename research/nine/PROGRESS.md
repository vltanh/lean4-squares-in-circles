# n=9 — actual proof progress

**Unrestricted optimality OPEN. Complete equality classification OPEN.
Full hand/table manuscript OPEN. Active gate: A.2.**

[Canonical roadmap](DEEP_GATED_ROADMAP.md) · [gate registry](gates/ACTIVE_ROADMAP.json) ·
[new square-pose proof and tables](computer_assisted/SQUARE_POSE_CERTIFICATES.md) ·
[actual independent replay summary](computer_assisted/square_pose_verification_summary.json).

## Fixed cover, new exact exclusions

The 7,915 canonical positional roots and their IDs are unchanged. The nineteen
closed hexagons still cover every q<=1105/256 packing with arbitrary square
orientations. The new square-pose certificates exclude **886 entire roots**,
including all 81 previous exclusions: **805 additional exclusions, 7,029 OPEN**.
These counts are not a percentage of mathematical effort. OPEN is not a claim
of physical feasibility or uniform ease.

The new relaxation includes exact corner-containment bounds and all candidate
square-owned separating axes over twelve CLOSED continuous orientation arcs.
Two independent graph implementations agree on every edge. The separate
candidate-by-candidate verifier replays **83 cores and 2,059 propagation rows**,
then checks every transfer to the fixed canonical roots. Each exclusion holds
for all q<=Q, not merely for a fixed Q-epsilon.

| Gate | Current status |
|---|---|
| A.0 / A.1a | Physical-model source available; final independent source audit remains |
| A.1b / A.1c | Same exhaustive closed root cover; all root IDs retained |
| A.2 | **ACTIVE: 886 excluded, 7,029 open** |
| A.3 | Global completion OPEN; all current square-pose certificates independently replayed |
| B.1 | Same closed-q=Q cover; equality root 7820 remains OPEN |
| B.2 / B.3 | Full necessary-and-sufficient equality families OPEN |
| C.1 / C.2 | Full hand/table manuscript and independent human audit OPEN |

## A reusable five-row obstruction

Core mask 143 occupies cells 0,1,2,3,7. Five exact propagation steps reduce
cell 3's complete pose domain from 1,356 possibilities to zero. The full table
and its soundness proof are in `computer_assisted/SQUARE_POSE_CERTIFICATES.md`.
The old finite center-distance graph still has a compatible assignment for
this core; the new square constraints genuinely strengthen that relaxation.
That center assignment is not asserted to be an actual physical packing.

## Controls and verification boundary

On each of the two meshes, the known oblique attaining packing survives all
twelve dihedral symmetries, and 25 genuinely touching pairs survive, including
every angle-interval endpoint. The verifier rejects nine deliberate mutations,
including an omitted proof row and a false exclusion of equality root 7820.
All arithmetic is exact integer/rational, with explicit bounds ruling out int64
overflow in NumPy operations. No floating-point proof comparison is used.

The repository has the complete producer, separately implemented verifier,
core list, mathematical derivation, and execution summary. The full generated
certificate, updated root manifest and full report are supplied in the
continuation archive and regenerate deterministically from committed sources.
Their hashes are pinned in the summary. No separate human review, unrestricted
solver UNSAT result, Lean, Lake or CI is claimed.

## Next mathematical obligation — A.2 remains active

Close groups of the remaining **7,029 exact physical root predicates**. The
finite pose graphs are necessary relaxations, not a guarantee that uniform
refinement will prove sharpness. Roots approaching the known equality family,
including 7820, need a sharp all-q<Q argument. Preserve the same cover, IDs,
closed boundary accounting and per-root closure evidence. No new roadmap or
extra gate tree is introduced.
