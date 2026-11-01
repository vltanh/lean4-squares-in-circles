# n=9 — proof status, not a case counter

[Single proof-first roadmap](DEEP_GATED_ROADMAP.md) · [structured proof gates](gates/ACTIVE_ROADMAP.json) · [source proof and executable evidence](computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md).

## Actual mathematical status

| Deliverable | Status |
|---|---|
| Exact attaining nine-square construction at squared radius 1105/256 | Rechecked in the new unrestricted emitter |
| Unrestricted polynomial model, equivalence proof and boundary controls | Implemented, source proof written, separate exact test implementation passes |
| Sharp certificate for the entire continuous four-over-three parallel-row subfamily | Exact rational identity verified by a separately implemented checker |
| Unrestricted lower bound for ALL nine-square packings | **OPEN** |
| All equality packings classified | **OPEN** |
| Compact full hand/table manuscript | LATER |
| Lean / CI | DEFERRED |

## What was actually completed

D.1.a-D.1.d now have source artifacts: `emit_unrestricted_nine.py`, the geometric equivalence proof, emitted-text tests, and recorded model dimensions. The formula contains only square geometry: no stresses, graph hypotheses, generic normal choices, or assumed circle loads. All expressions are quadratic after substitution. There are 37 real variables in variable-radius mode, or 34 after exact radius elimination and a legal global rotation gauge.

`test_unrestricted_nine.py` independently parses all six emitted variants and compares 744 exact pair predicates with polygon-intersection area, plus 1,488 containment predicates. It accepts the actual oblique equality witness and rejects deliberate overlap, escaped-corner, missing-pair and strict-tangency mutations. These finite tests are regression evidence, not a universal proof by sampling.

The first exact pilot reconstructs the sharp bound for EVERY packing in the stated parallel four-over-three row profile, with free gaps, offsets, row heights, and two arbitrary additional squares. Its certificate writes q-1105/256 as ten nonnegative hypothesis multiples plus six weighted squares. The exact independent-implementation checker expands to zero residual. Equality forces the seven-row core inside this profile.

**Neither result proves that arbitrary packings have that row structure.** No separate human reviewer or general SMT run is claimed: a general solver was not installed and installing one failed because network name resolution was unavailable. The exact rational tests and certificate replay DID run successfully. No Lean, Lake or CI ran.

## One active next task

**D.3.c — obtain a transferable certificate covering unrestricted relative orientations, or record a concrete limitation and deliberate pivot.** Do not keep subdividing the already certified parallel-row profile. The full Boolean separator cover exists, but no tractable exhaustive certificate over it has been obtained.

The primary route remains the unrestricted physical model. The selected-stress route is only the documented fallback. The global sharp lower bound and equality classification remain OPEN. Old case-count fractions remain retired.
