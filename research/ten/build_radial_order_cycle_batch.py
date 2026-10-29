#!/usr/bin/env python3
"""Build the exact integer-selected radial-order cycle batch (not a proof search)."""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def select(m, t, s, d):
    return (
        m == 10
        or (m == 9 and (t >= 1 or d >= 1))
        or (m == 8 and (t >= 2 or (t >= 1 and d >= 1)))
        or (m == 8 and t == 0 and (d >= 3 or (d == 2 and s == 2)))
    )


def main():
    manifest = json.loads((ROOT / "cycle_cases.json").read_text())
    cases = []
    totals = Counter()
    for family in manifest["families"]:
        for case in family["transmitter_cases"]:
            word = case["word"]
            first = word.index("L")
            rotated = word[first:] + word[:first]
            runs = rotated.split("L")[1:]
            assert all(run in ("", "S", "D", "SS") for run in runs)
            t, s, d = (runs.count(run) for run in ("SS", "S", "D"))
            k, m = word.count("L"), len(word)
            assert k == family["loaded_count"]
            assert m == family["cycle_length"] == k + 2 * t + s + d
            totals[m] += 1
            if select(m, t, s, d):
                cases.append({
                    "id": case["id"], "word": word,
                    "cycle_length": m, "loaded_count": k,
                    "ss_runs": t, "s_runs": s, "d_runs": d,
                })
    counts = Counter(case["cycle_length"] for case in cases)
    assert len(cases) == 206
    assert counts == Counter({8: 17, 9: 64, 10: 125})
    payload = {
        "schema_version": 1,
        "evidence": "RADIAL_ORDER_CYCLE_BUDGET.md",
        "status": "independently_reviewed_hand_proof",
        "meaning": "Exact integer selection; geometric exclusions and the full ID selection received independent mathematical review.",
        "case_count": len(cases),
        "counts_by_length": [
            {"cycle_length": m, "inventory": totals[m], "selected": counts[m],
             "remaining": totals[m] - counts[m]} for m in sorted(totals)
        ],
        "cases": cases,
    }
    (ROOT / "radial_order_cycle_batch.json").write_text(json.dumps(payload, indent=2) + "\n")
    print("Selected 206/279 signatures by exact integer conditions; 73 remain.")


if __name__ == "__main__":
    main()
