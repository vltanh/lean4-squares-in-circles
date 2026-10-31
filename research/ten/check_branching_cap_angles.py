#!/usr/bin/env python3
"""Verify the stronger C05 cap-angle certificate without trusting its search.

Each stored list must be a directed cycle of the case's actual strict
integer inequalities, with total bound at most zero. The builder is not
imported. Catalog coverage is separately checked by the raw enumerator.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, read_witnesses, bridge_witness

ROOT = Path(__file__).resolve().parent


def inequalities(k, code):
    # (u,v,b) represents theta_v-theta_u < b in degrees.
    rows = [(i + 1, i, -36) for i in range(k - 1)]
    rows.append((0, k - 1, 324))
    for (u, v), symbol in zip(combinations(range(k), 2), code):
        if symbol == "1":
            if v == u + 1:
                rows.append((u, v, 72))
            elif u == 0 and v == k - 1:
                rows.append((v, u, -288))
            else:
                raise ValueError("Direct edge does not join circular neighbors")
        elif symbol != "0":
            lower = {"2": 90, "3": 90, "4": 108, "5": 162, "6": 162}[symbol]
            rows.append((v, u, -lower))
            rows.append((u, v, 360 - lower))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="Print one code and its exact contradiction if present")
    args = parser.parse_args()
    catalog = read_catalogs()
    old = read_witnesses()
    witnesses = {}
    patterns = Counter()
    for line in (ROOT / "branching_loaded_cap_angle_rejections.tsv").read_text().splitlines():
        cid, raw = line.split("\t")
        if cid in witnesses:
            raise ValueError(f"Duplicate certificate ID: {cid}")
        k, code = catalog[cid]
        rows = inequalities(k, code)
        indices = list(map(int, raw.split(",")))
        if not 1 <= len(indices) <= k or any(i < 0 or i >= len(rows) for i in indices):
            raise ValueError(f"Invalid indices: {cid}")
        cycle = [rows[i] for i in indices]
        if len({u for u, _, _ in cycle}) != len(cycle):
            raise ValueError(f"Witness cycle is not simple: {cid}")
        if any(cycle[i][1] != cycle[(i + 1) % len(cycle)][0] for i in range(len(cycle))):
            raise ValueError(f"Witness cycle does not close: {cid}")
        if sum(bound for _, _, bound in cycle) > 0:
            raise ValueError(f"Witness bounds do not contradict: {cid}")
        witnesses[cid] = cycle
        patterns[tuple(sorted(bound for _, _, bound in cycle))] += 1
    if not old.keys() <= witnesses.keys():
        raise ValueError("Earlier angular exclusions are not all included")
    bridges = {cid for cid, (k, code) in catalog.items() if bridge_witness(k, code) is not None}
    union = witnesses.keys() | bridges
    prior = old.keys() | bridges
    summary = json.loads((ROOT / "branching_loaded_cap_angle_summary.json").read_text())
    bounds = {"ordinary_gap": 36, "direct_upper": 72, "S": 90, "D": 108, "SS": 162}
    if summary["bounds_degrees"] != bounds:
        raise ValueError("Printed angular constants differ")
    totals = {"initial_cases": len(catalog), "angular_exclusions": len(witnesses),
              "bridge_exclusions": len(bridges),
              "intersection": len(witnesses.keys() & bridges),
              "distinct_exclusions": len(union), "remaining_cases": len(catalog) - len(union),
              "previous_distinct_exclusions": len(prior),
              "new_distinct_exclusions": len(union - prior)}
    if any(summary[key] != value for key, value in totals.items()):
        raise ValueError("Printed global totals differ")
    if (len(summary["by_loaded_count"]) != 5
            or {r["k"] for r in summary["by_loaded_count"]} != set(range(3, 8))):
        raise ValueError("Printed loaded counts must cover exactly k=3,...,7")
    for row in summary["by_loaded_count"]:
        k = row["k"]
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        expected = {"k": k, "total": len(ids), "angular": len(ids & witnesses.keys()),
                    "bridge": len(ids & bridges),
                    "intersection": len(ids & witnesses.keys() & bridges),
                    "union": len(ids & union), "retained": len(ids - union),
                    "new_exclusions": len(ids & (union - prior))}
        if row != expected:
            raise ValueError(f"Printed counts differ at k={k}")
    printed = {tuple(row["bounds"]): row["cases"] for row in summary["patterns"]}
    if (len(printed) != len(summary["patterns"]) or printed != patterns
            or any(sum(row["bounds"]) != row["sum"] for row in summary["patterns"])):
        raise ValueError("Printed bound patterns differ")
    print(f"PASS: {len(witnesses)} exact angular contradictions in {len(patterns)} patterns; "
          f"{len(union)} excluded with bridges; {len(catalog) - len(union)} retained; "
          f"{len(union - prior)} newly excluded.")
    if args.case:
        k, code = catalog[args.case]
        print(json.dumps({"id": args.case, "loaded_vertices": k, "code": code,
                          "angular_cycle": witnesses.get(args.case),
                          "bridge_cut": bridge_witness(k, code)}, indent=2))


if __name__ == "__main__":
    main()
