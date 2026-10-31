#!/usr/bin/env python3
"""Check printed strict-angle contradiction cycles for the C05 b=0 catalog.

No optimization algorithm is trusted: each supplied witness is checked by
membership in the explicit inequality list, cycle closure, and integer sum.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COST = (0, 0, 1, 2, 1, 2, 4)
TYPE = ("absent", "direct", "S", "double-S", "D", "SS", "double-SS")


def constraints(k, code):
    # (u,v,b) means theta_v-theta_u < b, in degrees.
    result = [(i+1, i, -36) for i in range(k-1)]
    result.append((0, k-1, 324))
    for (a, b), symbol in zip(combinations(range(k), 2), code):
        typ = int(symbol)
        if typ == 1:
            if b == a+1:
                result.append((a, b, 72))
            else:
                if (a, b) != (0, k-1):
                    raise ValueError("Direct edge is not radially consecutive")
                result.append((b, a, -288))
        elif typ >= 2:
            lower = 90 if typ == 4 else 144 if typ in (5, 6) else 72
            result += [(b, a, -lower), (a, b, 360-lower)]
    return result


def read_catalogs():
    result = {}
    for k in range(3, 8):
        lines = (ROOT/f"branching_loaded_skeletons_k{k}.txt").read_text().splitlines()
        if lines != sorted(set(lines)):
            raise ValueError(f"Noncanonical code order at k={k}")
        for i, code in enumerate(lines, 1):
            if len(code) != k*(k-1)//2 or any(t not in "0123456" for t in code):
                raise ValueError("Invalid catalog code")
            result[f"C05-B0-K{k:02d}-{i:05d}"] = (k, code)
    return result


def read_witnesses():
    result = {}
    path = ROOT/"branching_loaded_angle_rejections.tsv"
    for line in path.read_text().splitlines():
        cid, raw = line.split("\t")
        if cid in result:
            raise ValueError("Duplicate rejected case ID")
        result[cid] = list(map(int, raw.split(",")))
    return result


def bridge_witness(k, code):
    """Return an explicit forbidden bridge and one side of its cut, or None."""
    pairs = list(combinations(range(k), 2))
    for edge, (a, b) in enumerate(pairs):
        if code[edge] not in "124":
            continue
        mask = 1 << a
        while True:
            old = mask
            for j, (u, v) in enumerate(pairs):
                if j != edge and code[j] != "0" and mask & ((1 << u) | (1 << v)):
                    mask |= (1 << u) | (1 << v)
            if mask == old:
                break
        if not mask & (1 << b):
            crossing = [j for j, (u, v) in enumerate(pairs)
                        if code[j] != "0" and bool(mask & (1 << u)) != bool(mask & (1 << v))]
            if crossing != [edge]:
                raise ValueError("Invalid singleton bridge cut")
            return {"edge_index": edge, "endpoints": [a, b],
                    "type": TYPE[int(code[edge])], "cut_mask": mask}
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", help="Decode one stable case ID after checking all witnesses")
    args = parser.parse_args()
    catalogs = read_catalogs()
    witnesses = read_witnesses()
    patterns = Counter()
    rejected = Counter()
    for cid, indices in witnesses.items():
        k, code = catalogs[cid]
        es = constraints(k, code)
        if not 1 <= len(indices) <= k or any(not 0 <= i < len(es) for i in indices):
            raise ValueError(f"Invalid witness index: {cid}")
        cycle = [es[i] for i in indices]
        if len({u for u, _, _ in cycle}) != len(cycle):
            raise ValueError(f"Nonsimple witness: {cid}")
        if any(cycle[i][1] != cycle[(i+1)%len(cycle)][0] for i in range(len(cycle))):
            raise ValueError(f"Witness does not close: {cid}")
        if sum(b for _, _, b in cycle) > 0:
            raise ValueError(f"No strict contradiction: {cid}")
        patterns[tuple(sorted(b for _, _, b in cycle))] += 1
        m = k + sum(COST[int(t)] for t in code)
        rejected[k, m] += 1
    data = json.loads((ROOT/"branching_loaded_angle_patterns.json").read_text())
    printed = {tuple(r["bounds"]): r["cases"] for r in data["patterns"]}
    if (len(printed) != len(data["patterns"]) or patterns != printed
            or any(sum(r["bounds"]) != r["sum"] for r in data["patterns"])):
        raise ValueError("Printed bound patterns differ")
    if len(data["counts"]) != 5 or {r["k"] for r in data["counts"]} != set(range(3, 8)):
        raise ValueError("Angular counts must cover exactly k=3,...,7")
    for row in data["counts"]:
        k = row["k"]
        actual = Counter(m for cid, (kk, code) in catalogs.items() if kk == k
                         for m in [k+sum(COST[int(t)] for t in code)])
        for m in actual:
            r = rejected[k, m]
            if r != row["rejected"].get(str(m), 0) or actual[m]-r != row["retained"].get(str(m), 0):
                raise ValueError("Printed body-count totals differ")
    print(f"PASS: {len(witnesses)} strict integer-cycle contradictions; "
          f"{len(patterns)} bound patterns; {len(catalogs)-len(witnesses)} not eliminated.")
    bridges = {cid: witness for cid, (k, code) in catalogs.items()
               if (witness := bridge_witness(k, code)) is not None}
    union = witnesses.keys() | bridges.keys()
    counts = json.loads((ROOT/"branching_loaded_filter_counts.json").read_text())
    if (len(counts["by_loaded_count"]) != 5
            or {r["k"] for r in counts["by_loaded_count"]} != set(range(3, 8))):
        raise ValueError("Combined counts must cover exactly k=3,...,7")
    for row in counts["by_loaded_count"]:
        ids = {cid for cid, (k, _) in catalogs.items() if k == row["k"]}
        expected = {"total": len(ids), "bridge": len(ids & bridges.keys()),
                    "intersection": len(ids & witnesses.keys() & bridges.keys()),
                    "union": len(ids & union), "retained": len(ids-union)}
        if any(value != row.get(key, 0) for key, value in expected.items()):
            raise ValueError("Bridge/angle combined counts differ")
    inventory = json.loads((ROOT/"branching_loaded_skeleton_inventory.json").read_text())
    totals = {"initial_cases": len(catalogs), "angular_exclusions": len(witnesses),
              "bridge_exclusions": len(bridges),
              "intersection": len(witnesses.keys() & bridges.keys()),
              "distinct_exclusions": len(union), "remaining_cases": len(catalogs)-len(union)}
    if any(inventory[key] != value for key, value in totals.items()):
        raise ValueError("Inventory exclusion totals differ")
    if inventory["filters_by_loaded_count"] != counts["by_loaded_count"]:
        raise ValueError("Inventory combined counts differ")
    bridge_types = Counter(str(TYPE.index(witness["type"])) for witness in bridges.values())
    if bridge_types != counts["bridge_witness_types"]:
        raise ValueError("Bridge witness type counts differ")
    print(f"PASS: {len(bridges)} forbidden-bridge cuts; "
          f"{len(union)} distinct codes excluded by the two predicates; "
          f"{len(catalogs)-len(union)} retained.")
    if args.case:
        k, code = catalogs[args.case]
        decoded = [{"endpoints": list(e), "type": TYPE[int(t)]}
                   for e, t in zip(combinations(range(k), 2), code) if t != "0"]
        record = {"id": args.case, "loaded_vertices": k,
                  "total_bodies": k+sum(COST[int(t)] for t in code),
                  "code": code, "edges": decoded,
                  "angle_excluded": args.case in witnesses,
                  "bridge_excluded": args.case in bridges}
        if args.case in witnesses:
            es = constraints(k, code)
            record["strict_cycle"] = [es[i] for i in witnesses[args.case]]
        if args.case in bridges:
            record["bridge_cut"] = bridges[args.case]
        print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
