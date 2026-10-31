#!/usr/bin/env python3
"""Select the exact cap-angle batch; no numerical geometric proof search."""
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def select(m, t, s, d):
    return 2 * m + 3 * t + s + 2 * d >= 20


def main():
    manifest = json.loads((ROOT / "cycle_cases.json").read_text())
    previous = json.loads((ROOT / "radial_order_cycle_batch.json").read_text())
    previous_ids = {case["id"] for case in previous["cases"]}
    assert len(previous_ids) == 206
    cases = []
    totals = Counter()
    all_ids = set()
    for family in manifest["families"]:
        for case in family["transmitter_cases"]:
            assert case["id"] not in all_ids
            all_ids.add(case["id"])
            word = case["word"]
            first = word.index("L")
            rotated = word[first:] + word[:first]
            runs = rotated.split("L")[1:]
            assert all(run in ("", "S", "D", "SS") for run in runs)
            t, s, d = (runs.count(run) for run in ("SS", "S", "D"))
            k, m = word.count("L"), len(word)
            assert k == family["loaded_count"]
            assert m == family["cycle_length"] == k + 2 * t + s + d
            assert t + s + d <= k
            totals[m] += 1
            if select(m, t, s, d):
                cases.append({
                    "id": case["id"], "word": word,
                    "cycle_length": m, "loaded_count": k,
                    "ss_runs": t, "s_runs": s, "d_runs": d,
                    "integer_budget": 2 * m + 3 * t + s + 2 * d,
                })
    selected_ids = {case["id"] for case in cases}
    counts = Counter(case["cycle_length"] for case in cases)
    assert len(all_ids) == 279
    assert len(cases) == len(selected_ids) == 234
    assert counts == Counter({7: 4, 8: 34, 9: 71, 10: 125})
    assert previous_ids <= selected_ids
    new_ids = [case["id"] for case in cases if case["id"] not in previous_ids]
    assert len(new_ids) == 28
    payload = {
        "schema_version": 1,
        "evidence": "SHARP_TRANSMISSION_CYCLE_BUDGET.md",
        "status": "independently_reviewed_hand_proof",
        "meaning": "Exact integer selection; geometric bounds, cycle budget, and selected IDs received independent mathematical review.",
        "predicate": "2*m+3*ss_runs+s_runs+2*d_runs>=20",
        "case_count": len(cases),
        "previous_batch": "radial_order_cycle_batch.json",
        "previous_case_count": len(previous_ids),
        "additional_case_count": len(new_ids),
        "additional_case_ids": new_ids,
        "counts_by_length": [
            {"cycle_length": m, "inventory": totals[m], "selected": counts[m],
             "remaining": totals[m] - counts[m]} for m in sorted(totals)
        ],
        "cases": cases,
    }
    (ROOT / "sharp_transmission_cycle_batch.json").write_text(
        json.dumps(payload, indent=2) + "\n"
    )
    print("Selected 234/279 signatures by the exact cap-angle budget; 45 remain.")
    print("All 206 previous selections retained; 28 additional stable IDs selected.")


if __name__ == "__main__":
    main()
