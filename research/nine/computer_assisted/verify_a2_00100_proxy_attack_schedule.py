#!/usr/bin/env python3
"""Exact rational audit of the saved 178 numerical proxy attacks.

The decimal center coordinates in dense_original_cell_report.json are treated
as exact rationals, and each proposed pair is checked. This does NOT exclude
the entire original nine-square domain for any registered cell.
No optimizer, Lean, Lake, or CI.
"""
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
report = json.loads((HERE / "dense_original_cell_report.json").read_text(), parse_float=Fraction)
schedule = json.loads((HERE / "a2_00100_proxy_attack_schedule.json").read_text())
register = json.loads((HERE.parent / "gates" / "A2_00100_FIXED_FRONTIER.json").read_text())

open_ids = {r["id"] for r in register["cells"] if r["status"] == "OPEN"}
records = {r["id"]: r for r in report["results"]}
entries = schedule["entries"]
assert schedule["status"] == "DISCOVERY_ONLY_ZERO_CELL_CLOSURES"
assert len(entries) == len(records) == len(open_ids) == 178
assert {e["id"] for e in entries} == open_ids == set(records)
assert len({e["id"] for e in entries}) == len(entries)

counts = Counter()
for entry in entries:
    row = records[entry["id"]]
    assert row["status"] == "OPEN"
    c = [Fraction(z) for z in row["relaxed_centers"]]
    assert len(c) == 18
    options = [
        (max(abs(c[2*i]-c[2*j]), abs(c[2*i+1]-c[2*j+1])), i, j)
        for i in range(9) for j in range(i+1, 9)
    ]
    _, i, j = min(options)
    assert entry["pair"] == [i, j], (entry["id"], entry["pair"], [i,j])
    dx = abs(c[2*i]-c[2*j])
    dy = abs(c[2*i+1]-c[2*j+1])
    assert dx < Fraction(7, 10) and dy < Fraction(7, 10)
    assert dx*dx + dy*dy < Fraction(1, 2)
    counts["ABCDEFGHI"[i] + "ABCDEFGHI"[j]] += 1

assert dict(counts) == {
    "HI": 114, "FH": 25, "FI": 14, "DI": 11,
    "CI": 4, "BH": 4, "GI": 4, "CH": 2,
}
print(json.dumps({
    "exact_decimal_rational_proposals_rejected": len(entries),
    "original_cells_closed": 0,
    "pair_counts": dict(sorted(counts.items())),
    "whole_masks_closed_by_this_audit": 0
}, indent=2))
