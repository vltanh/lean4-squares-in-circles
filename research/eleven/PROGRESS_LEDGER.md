# Eleven-square progress ledger

The [roadmap](DEEP_GATED_ROADMAP.md) is the current status authority. This
history records checkpoints without overwriting their original scope.
Commit timestamps and hashes are recorded after the commit exists.

## Initial roadmap checkpoint

- Base: main `4bea747b3efa13c869b956cb28435efaf21526fa`.
- G0.1 H: read repository physical semantics, PR #9 n=8 hand proof and
  roadmap, PR #10 source/verification distinction, and PR #11 n=9 residual
  coverage discipline through the GitHub connector.
- Added the full G0–G9 roadmap with separate exact-construction, raw-cover,
  reduced-classification, sharp-inequality, equality, audit, and Lean gates.
- No n=11 optimality claim. No Lean changes or Lean execution.
- Commit: `0a4a86e87c11a346a895c8d3c9a3c00a9c84041e`,
  2026-10-23 12:35:51 UTC. Draft PR #13 opened from this checkpoint.

## Exact feasible upper-bound checkpoint

- G1.1 H: elementary q=5 witness; tighter rational witness at
  U=49013/10000. All frames are exactly unit, all 44 vertices are contained,
  and all 55 pairs have an explicit separating own axis.
- G1.2.a H: pinned Friedman source credits Milan Kovacic, May 2006,
  with printed radius 2.21386+; its exact target and sharpness stay open.
- Validation: `python3 research/eleven/check_rational_witness.py` passed.
  An independent reviewer recomputed projection interval endpoints directly,
  checked all 11 printed coordinate rows against JSON, and found no gap.
- Independent minimum squared disk slack:
  229555019504308385673653663/2655897936042190250000000000000,
  greater than 1/20000. Minimum pair gap (7,8):
  64682720004556517/65138723819620100000000, greater than 1/2000000.
- Evidence: `EXACT_UPPER_BOUND.md`, `RATIONAL_WITNESS.json`, and
  `check_rational_witness.py`. This certifies one packing, not an optimality
  theorem, exact published contact system, or equality classification.
- Commit: `6ed9b0b2dac83413c3f54bb201fa1e59acf78105`,
  2026-10-23 12:38:04 UTC.

## Exact physical cover and compactness checkpoint

- G0.2–G0.4 H: four-corner containment equivalence, own-axis nonoverlap
  equivalence, orientation-sorted normalization, center bound, and compact
  minimizer existence.
- G2.1–G2.3 H: all 55 pair choices, eight signed owner axes per pair,
  and the exact 8^55 closed quadratic cell cover. Closed charts and overlap
  retain perpendicular/parallel frames, touching boundaries and owner ties.
- G4.1 H (generic): a completed-square stress identity conditional on
  supplied nonnegative weights; zero-loaded squares and equality residues
  are explicit. No sharp n=11 stress has been found.
- Review: separate mathematical audit checked the normalized support
  threshold, Minkowski-sum converse, compactness and dual signs; no
  substantive error found. No assumption of a common separating frame,
  a central square, or a boundary cycle enters the cover.
- Evidence: `FINITE_SEPARATOR_COVER.md`. The useful reduced cover G2.4,
  sharp terminal inequalities, and global equality remain open.
