# n=9 — actual proof progress

**Current proof status: unrestricted lower bound OPEN; equality OPEN; full hand/table proof OPEN.**

Canonical roadmap: [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md). Machine-readable gate state: [gates/ACTIVE_ROADMAP.json](gates/ACTIVE_ROADMAP.json).

## Known exact inputs

- The model `computer_assisted/emit_unrestricted_nine.py` records all nine independent square frames, 36 disk-corner inequalities, 36 pairwise nonoverlap disjunctions. Its geometric equivalence argument and exact finite regression controls are in `computer_assisted/UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md`. Full independent source audit is still needed.
- A q=1105/256 physical witness is checked in the unrestricted emitted formula and an independent rational polygon-clipping oracle.
- An independently replayed nonnegative polynomial identity proves the sharp bound for the **specific continuous parallel four-over-three row profile**, retaining two arbitrary additional squares. This is not a global cover.
- Historical hand lemmas on 4+3 projection chains and stress cases are conditional tools. The proposed arbitrary-angle two-direction theorem is **draft pending repair**, not a closed global result.

## Live gates

| Gate | Status | Meaning |
| --- | --- | --- |
| A.0 | SOURCE AVAILABLE | Correct unrestricted model; independent audit outstanding |
| A.1b | **OPEN / ACTIVE** | Obtain a genuinely exhaustive, practical cover of all potential q<Q counterexamples |
| A.1c | OPEN | Preserve zero/touching and singular faces through the cover |
| A.2 | OPEN | Prove all the cover's terminal inequalities |
| A.3 | OPEN | Independently replay all terminals and root coverage uniformly for q<Q |
| B.1–B.3 | OPEN | Necessary-and-sufficient equality classification |
| C.1–C.2 | OPEN | Reconstruct and audit the full human/table manuscript |

There is **no defensible finite remaining-case count or completion percentage** yet. A finite exact Boolean encoding is not a solved finite case partition. Do not revive the old numerator/denominator or count special subfamilies as global closures. No global solver UNSAT certificate exists. No Lean/CI runs are claimed.

**Active work:** A.1b global cover. The alternative direct-vs-stress method selection is an implementation decision under A, not another theorem gate.
