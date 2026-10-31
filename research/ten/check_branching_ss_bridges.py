#!/usr/bin/env python3
"""Check explicit SS-bridge cuts and their incident forbidden bundles.

Also reconstruct the entire filter independently by depth-first bridge
search. The builder's connected-component search is not imported.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, bridge_witness

ROOT = Path(__file__).resolve().parent


def has_forbidden_ss_bridge(k, code):
    pairs = list(combinations(range(k), 2))
    neighbors = [[] for _ in range(k)]
    double_vertices = set()
    for edge, ((u, v), typ) in enumerate(zip(pairs, code)):
        if typ != "0":
            neighbors[u].append((v, edge))
            neighbors[v].append((u, edge))
        if typ in "36":
            double_vertices.update((u, v))
    time = 0
    entered = [-1] * k
    low = [-1] * k
    found = False

    def visit(u, parent_edge):
        nonlocal time, found
        entered[u] = low[u] = time
        time += 1
        for v, edge in neighbors[u]:
            if edge == parent_edge:
                continue
            if entered[v] >= 0:
                low[u] = min(low[u], entered[v])
            else:
                visit(v, edge)
                low[u] = min(low[u], low[v])
                # Digit 5 is a single edge. Representing other bundles by
                # one adjacency does not change whether this edge is a bridge.
                if (low[v] > entered[u] and code[edge] == "5"
                        and (u in double_vertices or v in double_vertices)):
                    found = True

    visit(0, -1)
    if any(t < 0 for t in entered):
        raise ValueError("Catalog code is disconnected")
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="Decode a stored SS-bridge certificate")
    args = parser.parse_args()
    catalog = read_catalogs()
    witnesses = {}
    for line in (ROOT / "branching_ss_bridge_rejections.tsv").read_text().splitlines():
        cid, raw_edge, raw_bundle, raw_mask = line.split("\t")
        if cid in witnesses:
            raise ValueError("Duplicate certificate ID")
        k, code = catalog[cid]
        pairs = list(combinations(range(k), 2))
        edge, bundle, mask = map(int, (raw_edge, raw_bundle, raw_mask))
        if not (0 <= edge < len(pairs) and 0 <= bundle < len(pairs)):
            raise ValueError("Invalid edge index")
        if code[edge] != "5" or code[bundle] not in "36":
            raise ValueError("Wrong bridge or bundle type")
        if not set(pairs[edge]) & set(pairs[bundle]):
            raise ValueError("Bundle is not incident to the bridge")
        if not 0 < mask < (1 << k) - 1:
            raise ValueError("Cut is not proper")
        crossing = [j for j, (u, v) in enumerate(pairs) if code[j] != "0"
                    and bool(mask & (1 << u)) != bool(mask & (1 << v))]
        if crossing != [edge]:
            raise ValueError("Selected SS edge is not the unique edge crossing the cut")
        witnesses[cid] = {"bridge_index": edge, "bridge": pairs[edge],
                          "bundle_index": bundle, "bundle": pairs[bundle],
                          "bundle_type": code[bundle], "cut_mask": mask}
    independent = {cid for cid, (k, code) in catalog.items() if has_forbidden_ss_bridge(k, code)}
    if independent != witnesses.keys():
        raise ValueError("Independent depth-first filter differs from certificate IDs")
    cap = {line.split("\t")[0] for line in
           (ROOT / "branching_loaded_cap_angle_rejections.tsv").read_text().splitlines()}
    if not cap <= catalog.keys():
        raise ValueError("Earlier cap certificate contains an unknown catalog ID")
    old_bridges = {cid for cid, (k, code) in catalog.items() if bridge_witness(k, code) is not None}
    prior = cap | old_bridges
    union = prior | witnesses.keys()
    summary = json.loads((ROOT / "branching_ss_bridge_summary.json").read_text())
    expected = {"initial_cases": len(catalog), "ss_bridge_exclusions": len(witnesses),
                "previous_distinct_exclusions": len(prior),
                "intersection_with_previous": len(witnesses.keys() & prior),
                "new_distinct_exclusions": len(witnesses.keys() - prior),
                "distinct_exclusions": len(union), "remaining_cases": len(catalog) - len(union)}
    if any(summary[key] != value for key, value in expected.items()):
        raise ValueError("Printed total differs")
    if summary["new_case_ids"] != sorted(witnesses.keys() - prior):
        raise ValueError("Printed new case IDs differ")
    if (len(summary["by_loaded_count"]) != 5
            or {row["k"] for row in summary["by_loaded_count"]} != set(range(3, 8))):
        raise ValueError("Loaded-count table must cover k=3,...,7 once each")
    for row in summary["by_loaded_count"]:
        k = row["k"]
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        expected = {"k": k, "total": len(ids), "ss_bridge": len(ids & witnesses.keys()),
                    "new_exclusions": len(ids & (witnesses.keys() - prior)),
                    "union": len(ids & union), "retained": len(ids - union)}
        if row != expected:
            raise ValueError("Printed loaded-count total differs")
    print(f"PASS: {len(witnesses)} SS-bridge cuts and matching independent DFS cases; "
          f"{len(witnesses.keys()-prior)} newly excluded; "
          f"{len(union)} excluded in union; {len(catalog)-len(union)} retained.")
    if args.case:
        print(json.dumps({"id": args.case, "code": catalog[args.case][1],
                          "certificate": witnesses.get(args.case)}, indent=2))


if __name__ == "__main__":
    main()
