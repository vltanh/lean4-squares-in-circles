#!/usr/bin/env python3
"""Build separate planar-order and D-forest witnesses for the fixed b=0 catalog."""
import argparse
from itertools import combinations
import json
from pathlib import Path

from check_branching_loaded_angles import read_catalogs, bridge_witness

ROOT = Path(__file__).resolve().parent


def crossing_witness(k, code):
    pairs = list(combinations(range(k), 2))
    for i, (a, b) in enumerate(pairs):
        if code[i] == "0":
            continue
        for j in range(i + 1, len(pairs)):
            c, d = pairs[j]
            if code[j] != "0" and (a < c < b < d or c < a < d < b):
                return i, j
    return None


def forest_witness(k, code):
    pairs = list(combinations(range(k), 2))
    adj = [[] for _ in range(k)]
    for i, ((u, v), symbol) in enumerate(zip(pairs, code)):
        if symbol == "4":
            adj[u].append((v, i))
            adj[v].append((u, i))
    for v in range(k):
        if len(adj[v]) >= 3:
            return "degree", v, [edge for _, edge in adj[v][:3]]
    seen = set()
    for start in range(k):
        if start in seen or not adj[start]:
            continue
        stack = [start]
        component = set()
        for u in stack:
            if u in component:
                continue
            component.add(u)
            stack.extend(v for v, _ in adj[u] if v not in component)
        seen.update(component)
        if all(len(adj[v]) == 2 for v in component):
            start = min(component)
            vertices = [start]
            previous, current = start, min(v for v, _ in adj[start])
            while current != start:
                vertices.append(current)
                following = next(v for v, _ in adj[current] if v != previous)
                previous, current = current, following
            return "cycle", -1, vertices
    return None


def build():
    catalog = read_catalogs()
    prior = {cid for cid, (k, code) in catalog.items() if bridge_witness(k, code) is not None}
    for name in ("branching_loaded_cap_angle_rejections.tsv", "branching_ss_bridge_rejections.tsv"):
        prior.update(line.split("\t")[0] for line in (ROOT / name).read_text().splitlines())
    planar = {cid: w for cid, (k, code) in catalog.items() if (w := crossing_witness(k, code)) is not None}
    forest = {cid: w for cid, (k, code) in catalog.items() if (w := forest_witness(k, code)) is not None}
    after_planar = prior | planar.keys()
    final = after_planar | forest.keys()
    rows = []
    for k in range(3, 8):
        ids = {cid for cid, (kk, _) in catalog.items() if kk == k}
        rows.append({"k": k, "total": len(ids), "planar": len(ids & planar.keys()),
                     "planar_new": len(ids & (planar.keys() - prior)),
                     "d_forest": len(ids & forest.keys()),
                     "d_forest_new_after_planar": len(ids & (forest.keys() - after_planar)),
                     "union": len(ids & final), "retained": len(ids - final)})
    summary = {
        "schema_version": 1,
        "scope": "Fixed C05 b=0 catalog under jointly selected generic planar physical stress.",
        "proof": "BRANCHING_SELECTED_GRAPH_FILTERS.md",
        "initial_cases": len(catalog), "previous_distinct_exclusions": len(prior),
        "planar_exclusions": len(planar), "planar_new_exclusions": len(planar.keys() - prior),
        "after_planar_exclusions": len(after_planar),
        "d_forest_exclusions": len(forest),
        "d_forest_new_before_planar": len(forest.keys() - prior),
        "d_forest_new_after_planar": len(forest.keys() - after_planar),
        "distinct_exclusions": len(final), "remaining_cases": len(catalog) - len(final),
        "by_loaded_count": rows,
    }
    files = {
        "branching_planar_rejections.tsv": "".join(
            f"{cid}\t{i}\t{j}\n" for cid, (i, j) in planar.items()),
        "branching_d_forest_rejections.tsv": "".join(
            cid + "\t" + kind + "\t" + str(pivot) + "\t" + ",".join(map(str, witness)) + "\n"
            for cid, (kind, pivot, witness) in forest.items()),
        "branching_selected_graph_summary.json": json.dumps(summary, indent=2) + "\n",
    }
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
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
