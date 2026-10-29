#!/usr/bin/env python3
"""Print graph-cut witnesses for SS bridges incident to a double bundle.

The raw catalog and both earlier angular certificates are unchanged.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, bridge_witness

ROOT = Path(__file__).resolve().parent


def witness(k, code):
    pairs = list(combinations(range(k), 2))
    for edge, (a, b) in enumerate(pairs):
        if code[edge] != "5":
            continue
        mask = 1 << a
        while True:
            old = mask
            for j, (u, v) in enumerate(pairs):
                if j != edge and code[j] != "0" and mask & ((1 << u) | (1 << v)):
                    mask |= (1 << u) | (1 << v)
            if mask == old:
                break
        if mask & (1 << b):
            continue
        for bundle, (u, v) in enumerate(pairs):
            if code[bundle] in "36" and {a, b} & {u, v}:
                return edge, bundle, mask
    return None


def build():
    catalog = read_catalogs()
    cap = {line.split("\t")[0] for line in
           (ROOT / "branching_loaded_cap_angle_rejections.tsv").read_text().splitlines()}
    bridges = {cid for cid, (k, code) in catalog.items() if bridge_witness(k, code) is not None}
    prior = cap | bridges
    witnesses = {cid: result for cid, (k, code) in catalog.items()
                 if (result := witness(k, code)) is not None}
    union = prior | witnesses.keys()
    counts = []
    for k in range(3, 8):
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        counts.append({"k": k, "total": len(ids), "ss_bridge": len(ids & witnesses.keys()),
                       "new_exclusions": len(ids & (witnesses.keys() - prior)),
                       "union": len(ids & union), "retained": len(ids - union)})
    summary = {
        "schema_version": 1,
        "scope": "Fixed C05 b=0 catalog; b>0 remains outside the enumeration.",
        "proof": "BRANCHING_SS_BRIDGE_FILTER.md",
        "initial_cases": len(catalog), "ss_bridge_exclusions": len(witnesses),
        "previous_distinct_exclusions": len(prior),
        "intersection_with_previous": len(witnesses.keys() & prior),
        "new_distinct_exclusions": len(witnesses.keys() - prior),
        "distinct_exclusions": len(union), "remaining_cases": len(catalog) - len(union),
        "by_loaded_count": counts,
        "new_case_ids": sorted(witnesses.keys() - prior),
    }
    tsv = "".join(cid + "\t" + "\t".join(map(str, row)) + "\n"
                  for cid, row in witnesses.items())
    files = {"branching_ss_bridge_rejections.tsv": tsv,
             "branching_ss_bridge_summary.json": json.dumps(summary, indent=2) + "\n"}
    return files, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    files, summary = build()
    for name, content in files.items():
        path = ROOT / name
        if args.write:
            path.write_text(content)
        if args.check and path.read_text() != content:
            raise ValueError(f"Reconstruction differs: {name}")
    print(json.dumps({key: value for key, value in summary.items() if key != "new_case_ids"}, indent=2))


if __name__ == "__main__":
    main()
