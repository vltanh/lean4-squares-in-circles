#!/usr/bin/env python3
"""Verify explicit alternating-endpoint, D-degree, and D-cycle witnesses."""
import argparse
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, bridge_witness

ROOT = Path(__file__).resolve().parent


def independent_predicates(k, code):
    pairs = list(combinations(range(k), 2))
    present = [edge for edge, symbol in zip(pairs, code) if symbol != "0"]
    # A chord has alternating endpoints iff exactly one endpoint of the
    # other chord lies in its open boundary interval, with no shared end.
    crossing = any(len({a, b, c, d}) == 4 and ((a < c < b) != (a < d < b))
                   for (a, b), (c, d) in combinations(present, 2))
    degree = [0] * k
    parent = list(range(k))

    def component(v):
        while parent[v] != v:
            v = parent[v]
        return v

    cycle = False
    for (u, v), symbol in zip(pairs, code):
        if symbol == "4":
            degree[u] += 1
            degree[v] += 1
            a, b = component(u), component(v)
            if a == b:
                cycle = True
            else:
                parent[a] = b
    return crossing, max(degree) > 2 or cycle


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="Decode the new graph witnesses for a stable ID")
    args = parser.parse_args()
    catalog = read_catalogs()
    planar = {}
    for line in (ROOT / "branching_planar_rejections.tsv").read_text().splitlines():
        cid, ii, jj = line.split("\t")
        if cid in planar:
            raise ValueError("Duplicate planar witness ID")
        k, code = catalog[cid]
        pairs = list(combinations(range(k), 2))
        i, j = int(ii), int(jj)
        if not (0 <= i < j < len(pairs)) or code[i] == "0" or code[j] == "0":
            raise ValueError("Invalid planar witness edges")
        a, b = pairs[i]
        c, d = pairs[j]
        if not (a < c < b < d or c < a < d < b):
            raise ValueError("Planar witness endpoints do not alternate")
        planar[cid] = [pairs[i], pairs[j]]
    forest = {}
    for line in (ROOT / "branching_d_forest_rejections.tsv").read_text().splitlines():
        cid, kind, raw_pivot, raw_witness = line.split("\t")
        if cid in forest:
            raise ValueError("Duplicate D-forest witness ID")
        k, code = catalog[cid]
        pairs = list(combinations(range(k), 2))
        pivot = int(raw_pivot)
        witness = list(map(int, raw_witness.split(",")))
        if kind == "degree":
            if not 0 <= pivot < k or len(witness) != 3 or len(set(witness)) != 3:
                raise ValueError("Invalid D-degree witness")
            if any(not 0 <= i < len(pairs) or code[i] != "4" or pivot not in pairs[i]
                   for i in witness):
                raise ValueError("D-degree witness is not three incident D edges")
        elif kind == "cycle":
            if (pivot != -1 or not 3 <= len(witness) <= k or len(set(witness)) != len(witness)
                    or any(not 0 <= v < k for v in witness)):
                raise ValueError("Invalid D-cycle vertices")
            edge_index = {pair: i for i, pair in enumerate(pairs)}
            for i, u in enumerate(witness):
                v = witness[(i + 1) % len(witness)]
                if code[edge_index[tuple(sorted((u, v)))]] != "4":
                    raise ValueError("Cycle witness contains a non-D edge")
        else:
            raise ValueError("Unknown D-forest witness kind")
        forest[cid] = {"kind": kind, "pivot": pivot, "witness": witness}
    expected_planar, expected_forest = set(), set()
    for cid, (k, code) in catalog.items():
        cross, bad_d = independent_predicates(k, code)
        if cross:
            expected_planar.add(cid)
        if bad_d:
            expected_forest.add(cid)
    if expected_planar != planar.keys() or expected_forest != forest.keys():
        raise ValueError("Independent graph predicates differ from the certificate IDs")
    prior = {cid for cid, (k, code) in catalog.items() if bridge_witness(k, code) is not None}
    for name in ("branching_loaded_cap_angle_rejections.tsv", "branching_ss_bridge_rejections.tsv"):
        prior.update(line.split("\t")[0] for line in (ROOT / name).read_text().splitlines())
    if not prior <= catalog.keys():
        raise ValueError("An earlier certificate ID is not in the catalog")
    after_planar = prior | planar.keys()
    final = after_planar | forest.keys()
    summary = json.loads((ROOT / "branching_selected_graph_summary.json").read_text())
    totals = {"initial_cases": len(catalog), "previous_distinct_exclusions": len(prior),
              "planar_exclusions": len(planar), "planar_new_exclusions": len(planar.keys() - prior),
              "after_planar_exclusions": len(after_planar),
              "d_forest_exclusions": len(forest),
              "d_forest_new_before_planar": len(forest.keys() - prior),
              "d_forest_new_after_planar": len(forest.keys() - after_planar),
              "distinct_exclusions": len(final), "remaining_cases": len(catalog) - len(final)}
    if any(summary[key] != value for key, value in totals.items()):
        raise ValueError("Printed total differs")
    if (len(summary["by_loaded_count"]) != 5
            or {row["k"] for row in summary["by_loaded_count"]} != set(range(3, 8))):
        raise ValueError("Loaded count table does not cover exactly k=3,...,7")
    for row in summary["by_loaded_count"]:
        k = row["k"]
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        expected = {"k": k, "total": len(ids), "planar": len(ids & planar.keys()),
                    "planar_new": len(ids & (planar.keys() - prior)),
                    "d_forest": len(ids & forest.keys()),
                    "d_forest_new_after_planar": len(ids & (forest.keys() - after_planar)),
                    "union": len(ids & final), "retained": len(ids - final)}
        if row != expected:
            raise ValueError("Printed loaded-count totals differ")
    print(f"PASS: {len(planar)} alternating-endpoint witnesses; {len(forest)} D-forest witnesses; "
          f"{len(final)} excluded in union; {len(catalog) - len(final)} retained.")
    if args.case:
        print(json.dumps({"id": args.case, "code": catalog[args.case][1],
                          "planar_witness": planar.get(args.case),
                          "d_forest_witness": forest.get(args.case)}, indent=2))


if __name__ == "__main__":
    main()
