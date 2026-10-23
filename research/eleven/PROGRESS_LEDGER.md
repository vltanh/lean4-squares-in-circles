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
