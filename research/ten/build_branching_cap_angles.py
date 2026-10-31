#!/usr/bin/env python3
"""Build exact strict-cycle witnesses for the stronger C05 b=0 cap bounds.

The raw catalog and earlier angular certificate are never changed.
Use --write to create the new certificate and summary, or --check to
reconstruct them byte-for-byte. Discovery uses only integer arithmetic.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, read_witnesses, bridge_witness

ROOT = Path(__file__).resolve().parent


def constraints(k, code):
    result = [(i + 1, i, -36) for i in range(k - 1)] + [(0, k - 1, 324)]
    for (i, j), symbol in zip(combinations(range(k), 2), code):
        typ = int(symbol)
        if typ == 1:
            if j == i + 1:
                result.append((i, j, 72))
            elif (i, j) == (0, k - 1):
                result.append((j, i, -288))
            else:
                raise ValueError("Nonconsecutive direct edge")
        elif typ >= 2:
            lower = 108 if typ == 4 else 162 if typ in (5, 6) else 90
            result.extend([(j, i, -lower), (i, j, 360 - lower)])
    return result


def contradiction_cycle(k, edges):
    # On a simple cycle with ell<=k edges, sum((k+1)b-1)<0 iff sum(b)<=0.
    distance = [0] * k
    predecessor = [None] * k
    for _ in range(k):
        changed = None
        for index, (u, v, bound) in enumerate(edges):
            candidate = distance[u] + (k + 1) * bound - 1
            if candidate < distance[v]:
                distance[v] = candidate
                predecessor[v] = index
                changed = v
        if changed is None:
            return None
    vertex = changed
    for _ in range(k):
        vertex = edges[predecessor[vertex]][0]
    start = vertex
    indices = []
    while True:
        edge = predecessor[vertex]
        indices.append(edge)
        vertex = edges[edge][0]
        if vertex == start:
            break
    indices.reverse()
    if len(indices) > k or sum(edges[i][2] for i in indices) > 0:
        raise ValueError("Discovery returned no strict contradiction")
    return min(indices[i:] + indices[:i] for i in range(len(indices)))


def build():
    catalog = read_catalogs()
    previous_angles = read_witnesses()
    witnesses = {}
    patterns = Counter()
    bridges = set()
    for cid, (k, code) in catalog.items():
        edges = constraints(k, code)
        indices = contradiction_cycle(k, edges)
        if indices is not None:
            witnesses[cid] = indices
            patterns[tuple(sorted(edges[i][2] for i in indices))] += 1
        if bridge_witness(k, code) is not None:
            bridges.add(cid)
    if not previous_angles.keys() <= witnesses.keys():
        raise ValueError("Stronger certificate lost an earlier angular exclusion")
    union = witnesses.keys() | bridges
    previous_union = previous_angles.keys() | bridges
    counts = []
    for k in range(3, 8):
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        counts.append({"k": k, "total": len(ids), "angular": len(ids & witnesses.keys()),
                       "bridge": len(ids & bridges),
                       "intersection": len(ids & witnesses.keys() & bridges),
                       "union": len(ids & union), "retained": len(ids - union),
                       "new_exclusions": len(ids & (union - previous_union))})
    summary = {
        "schema_version": 1,
        "scope": "Fixed C05 b=0 catalog: all retained vertices loaded; b>0 remains outside.",
        "proof": "BRANCHING_LOADED_CAP_ANGLES.md",
        "bounds_degrees": {"ordinary_gap": 36, "direct_upper": 72,
                           "S": 90, "D": 108, "SS": 162},
        "initial_cases": len(catalog), "angular_exclusions": len(witnesses),
        "bridge_exclusions": len(bridges),
        "intersection": len(witnesses.keys() & bridges),
        "distinct_exclusions": len(union), "remaining_cases": len(catalog) - len(union),
        "previous_distinct_exclusions": len(previous_union),
        "new_distinct_exclusions": len(union - previous_union),
        "by_loaded_count": counts,
        "patterns": [{"bounds": list(bounds), "sum": sum(bounds), "cases": count}
                     for bounds, count in sorted(patterns.items())],
    }
    tsv = "".join(cid + "\t" + ",".join(map(str, indices)) + "\n"
                  for cid, indices in witnesses.items())
    return {"branching_loaded_cap_angle_rejections.tsv": tsv,
            "branching_loaded_cap_angle_summary.json": json.dumps(summary, indent=2) + "\n"}, summary


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
    print(json.dumps({key: value for key, value in summary.items() if key != "patterns"}, indent=2))


if __name__ == "__main__":
    main()
