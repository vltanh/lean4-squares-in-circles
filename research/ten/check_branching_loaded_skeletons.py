#!/usr/bin/env python3
"""Enumerate necessary C05 skeletons with no unloaded branching vertices.

This is finite combinatorial bookkeeping, not a geometric feasibility test.
The main C05 branch remains open. Circular order is retained modulo D_k.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent
# 0 absent; 1 direct; 2 S; 3 double-S; 4 D; 5 SS; 6 double-SS.
COST = (0, 0, 1, 2, 1, 2, 4)
MULT = (0, 1, 1, 2, 1, 1, 2)


def crosses(e, f):
    a, b = e
    c, d = f
    return a < c < b < d or c < a < d < b


def connected(k, edges, code):
    reached = 1
    while True:
        old = reached
        for (a, b), typ in zip(edges, code):
            if typ and reached & ((1 << a) | (1 << b)):
                reached |= (1 << a) | (1 << b)
        if reached == old:
            return reached == (1 << k) - 1


def symmetries(k, edges):
    ix = {e: i for i, e in enumerate(edges)}
    rows = []
    for sign in (1, -1):
        for shift in range(k):
            perm = [(sign * v + shift) % k for v in range(k)]
            rows.append(tuple(ix[tuple(sorted((perm[a], perm[b])))]
                              for a, b in edges))
    return rows


def enumerate_k(k):
    edges = list(combinations(range(k), 2))
    n = len(edges)
    budget = 10 - k
    boundary = [i for i, (a, b) in enumerate(edges)
                if b == a + 1 or (a, b) == (0, k - 1)]
    permutations = symmetries(k, edges)
    cross = [[crosses(e, f) for f in edges] for e in edges]
    code = [0] * n
    degree = [0] * k
    trans = []
    answers = set()
    labeled = Counter()

    def finish(cost, edge_count):
        available = [i for i in boundary if not code[i]]
        for mask in range(1 << len(available)):
            direct_count = mask.bit_count()
            if edge_count + direct_count < k or (k == 3 and direct_count > 1):
                continue
            dd = degree.copy()
            selected = []
            for j, edge in enumerate(available):
                if (mask >> j) & 1:
                    code[edge] = 1
                    selected.append(edge)
                    a, b = edges[edge]
                    dd[a] += 1
                    dd[b] += 1
            if min(dd) and 3 <= max(dd) <= 8 and connected(k, edges, code):
                labeled[k + cost] += 1
                canonical = min(tuple(code[i] for i in row)
                                for row in permutations)
                answers.add(canonical)
            for edge in selected:
                code[edge] = 0

    def visit(start, cost, edge_count):
        if cost:
            finish(cost, edge_count)
        for edge in range(start, n):
            a, b = edges[edge]
            for typ in (2, 3, 4, 5, 6):
                new_cost = cost + COST[typ]
                if new_cost > budget:
                    continue
                if any(cross[edge][j] and (typ != 4 or code[j] != 4)
                       for j in trans):
                    continue
                if max(degree[a], degree[b]) + MULT[typ] > 8:
                    continue
                code[edge] = typ
                degree[a] += MULT[typ]
                degree[b] += MULT[typ]
                trans.append(edge)
                visit(edge + 1, new_cost, edge_count + MULT[typ])
                trans.pop()
                degree[a] -= MULT[typ]
                degree[b] -= MULT[typ]
                code[edge] = 0

    visit(0, 0, 0)
    records = []
    counts = Counter()
    for code in sorted(answers):
        m = k + sum(COST[t] for t in code)
        counts[m] += 1
        records.append({"bodies": m, "code": "".join(map(str, code))})
    return {"loaded_vertices": k, "edge_order": edges,
            "labeled_counts_by_bodies": dict(sorted(labeled.items())),
            "orbit_counts_by_bodies": dict(sorted(counts.items())),
            "total_orbits": len(records), "cases": records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, nargs="+", default=list(range(3, 8)))
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    inventory = json.loads((ROOT / "branching_loaded_skeleton_inventory.json").read_text())
    metadata = {row["loaded_vertices"]: row for row in inventory["catalogs"]}
    if len(inventory["catalogs"]) != 5 or set(metadata) != set(range(3, 8)):
        raise ValueError("Inventory must contain exactly one row for each k=3,...,7")
    for k in args.k:
        if k not in range(3, 8):
            parser.error("k must lie between 3 and 7")
        start = time.monotonic()
        row = enumerate_k(k)
        codes = "".join(case["code"] + "\n" for case in row["cases"])
        path = ROOT / f"branching_loaded_skeletons_k{k}.txt"
        row["catalog_sha256"] = hashlib.sha256(codes.encode()).hexdigest()
        if args.write:
            path.write_text(codes)
        if args.verify:
            if path.read_text() != codes:
                raise ValueError(f"Catalog differs: {path.name}")
            # JSON uses string keys for body counts; normalize before comparing.
            actual = json.loads(json.dumps({key: value for key, value in row.items()
                                           if key not in ("cases", "edge_order")}))
            if actual != metadata[k]:
                raise ValueError(f"Inventory metadata differs at k={k}")
            file_info = {"bytes": len(codes.encode()),
                         "sha256": row["catalog_sha256"]}
            if file_info != inventory["files"][path.name]:
                raise ValueError(f"Inventory file metadata differs: {path.name}")
        print(json.dumps({key: value for key, value in row.items()
                          if key not in ("cases", "edge_order")}))
        print(f"k={k}: {time.monotonic()-start:.2f} seconds", flush=True)


if __name__ == "__main__":
    main()
