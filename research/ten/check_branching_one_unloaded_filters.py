#!/usr/bin/env python3
"""Classify fixed b=1 codes by exact proof witnesses, without a large row ledger.

--case decodes one canonical code and its proof witness without catalog files.
--catalog-dir checks generated catalogs against the fixed hash manifest and
recomputes the compact progress summary. Add --write to create that summary,
or --open-cases PATH to export the exact remaining stable IDs.
"""
import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path

from check_branching_one_unloaded import setup, necessary, canonical
from build_branching_cap_angles import constraints, contradiction_cycle
from build_branching_selected_graph_filters import forest_witness

ROOT = Path(__file__).resolve().parent
PROOFS = {
    "two_loaded": "ONE_UNLOADED_TWO_LOADED_EXCLUSION.md",
    "loaded_bridge": "BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md",
    "ss_bundle": "BRANCHING_SS_BRIDGE_ENDPOINTS.md",
    "d_forest": "DIAGONAL_PATH_GRAPH_RESTRICTIONS.md",
    "loaded_angle": "BRANCHING_ONE_UNLOADED_FILTERS.md",
}


def bridge_cut(k, code, pairs, edge):
    a, b = pairs[edge]
    mask = 1 << a
    while True:
        old = mask
        for j, ((u, v), typ) in enumerate(zip(pairs, code)):
            if j != edge and typ != "0" and mask & ((1 << u) | (1 << v)):
                mask |= (1 << u) | (1 << v)
        if mask == old:
            break
    if mask & (1 << b):
        return None
    crossing = [j for j, ((u, v), typ) in enumerate(zip(pairs, code))
                if typ != "0" and bool(mask & (1 << u)) != bool(mask & (1 << v))]
    if crossing != [edge] or not 0 < mask < (1 << (k + 1)) - 1:
        raise ValueError("Invalid singleton bridge witness")
    return mask


def first_witness(k, code):
    if k == 2:
        return {"kind": "two_loaded", "evidence": PROOFS["two_loaded"]}
    pairs = list(combinations(range(k + 1), 2))
    for edge, ((u, v), typ) in enumerate(zip(pairs, code)):
        if v < k and typ in "124":
            mask = bridge_cut(k, code, pairs, edge)
            if mask is not None:
                return {"kind": "loaded_bridge", "edge_index": edge,
                        "endpoints": [u, v], "type": typ, "cut_mask": mask,
                        "evidence": PROOFS["loaded_bridge"]}
    for edge, ((u, v), typ) in enumerate(zip(pairs, code)):
        if v < k and typ == "5":
            bundles = [j for j, ((a, b), t) in enumerate(zip(pairs, code))
                       if t in "36" and {a, b} & {u, v}]
            if not bundles:
                continue
            mask = bridge_cut(k, code, pairs, edge)
            if mask is not None:
                return {"kind": "ss_bundle", "edge_index": edge,
                        "endpoints": [u, v], "cut_mask": mask,
                        "bundle_index": bundles[0], "bundle_endpoints": list(pairs[bundles[0]]),
                        "evidence": PROOFS["ss_bundle"]}
    result = forest_witness(k + 1, code)
    if result is not None:
        kind, pivot, witness = result
        if kind == "degree":
            if (len(witness) != 3 or len(set(witness)) != 3
                    or any(code[e] != "4" or pivot not in pairs[e] for e in witness)):
                raise ValueError("Invalid D-degree certificate")
        else:
            if len(witness) < 3 or len(set(witness)) != len(witness):
                raise ValueError("Invalid D-cycle certificate")
            lookup = {pair: i for i, pair in enumerate(pairs)}
            for i, u in enumerate(witness):
                v = witness[(i + 1) % len(witness)]
                if code[lookup[tuple(sorted((u, v)))]] != "4":
                    raise ValueError("D-cycle contains a non-D edge")
        return {"kind": "d_forest", "witness_kind": kind, "pivot": pivot,
                "witness": witness, "evidence": PROOFS["d_forest"]}
    loaded_code = "".join(typ for (_, v), typ in zip(pairs, code) if v < k)
    rows = constraints(k, loaded_code)
    indices = contradiction_cycle(k, rows)
    if indices is not None:
        cycle = [rows[i] for i in indices]
        if (not 1 <= len(cycle) <= k or len({u for u, _, _ in cycle}) != len(cycle)
                or any(cycle[i][1] != cycle[(i + 1) % len(cycle)][0] for i in range(len(cycle)))
                or sum(bound for _, _, bound in cycle) > 0):
            raise ValueError("Invalid strict angular contradiction")
        return {"kind": "loaded_angle", "inequality_indices": indices,
                "strict_cycle": cycle, "evidence": PROOFS["loaded_angle"]}
    return None


def decode(cid):
    parts = cid.split("-")
    if len(parts) != 4 or parts[:2] != ["C05", "B1"] or not parts[2].startswith("K"):
        raise ValueError("Case ID must have the form C05-B1-Kkk-code")
    k = int(parts[2][1:])
    if k not in range(2, 8):
        raise ValueError("Loaded count must lie in 2,...,7")
    code = parts[3]
    digits = tuple(map(int, code))
    pairs, symmetries = setup(k)
    if len(digits) != len(pairs) or any(t not in range(7) for t in digits):
        raise ValueError("Wrong code length or symbols")
    if not necessary(k, pairs, digits) or canonical(digits, symmetries) != digits:
        raise ValueError("Code is not a canonical raw catalog record")
    witness = first_witness(k, code)
    return {"id": f"C05-B1-K{k:02d}-{code}", "loaded_vertices": k,
            "unloaded_retained_vertex": k, "status": "hand" if witness else "open",
            "witness": witness}


def summarize(directory, open_output=None):
    inventory = json.loads((ROOT / "branching_one_unloaded_inventory.json").read_text())
    rows = []
    total = Counter()
    kinds = Counter()
    open_ids = [] if open_output is not None else None
    for metadata in inventory["strata"]:
        k = metadata["loaded_vertices"]
        data = (directory / f"b1_k{k}.txt").read_bytes()
        if (len(data) != metadata["catalog_bytes"]
                or hashlib.sha256(data).hexdigest() != metadata["catalog_sha256"]):
            raise ValueError(f"Raw catalog differs from fixed manifest at k={k}")
        codes = data.decode().splitlines()
        if len(codes) != metadata["canonical_count"]:
            raise ValueError("Raw case count differs")
        count = Counter()
        for code in codes:
            witness = first_witness(k, code)
            count[witness["kind"] if witness else "open"] += 1
            if witness is None and open_ids is not None:
                open_ids.append(f"C05-B1-K{k:02d}-{code}")
        closed = len(codes) - count["open"]
        rows.append({"loaded_vertices": k, "raw_cases": len(codes), "hand_closed": closed,
                     "remaining": count["open"],
                     "closed_by_first_witness": {name: count[name] for name in PROOFS if count[name]}})
        total.update({"raw_cases": len(codes), "hand_closed": closed, "remaining": count["open"]})
        kinds.update({name: count[name] for name in PROOFS})
        print(f"k={k}: {closed}/{len(codes)} excluded; {count['open']} remain", flush=True)
    if open_output is not None:
        open_output.write_text("".join(cid + "\n" for cid in open_ids))
    return {"schema_version": 1, "raw_rule_version": inventory["raw_rule_version"],
            "scope": "Fixed C05 b=1 catalog, selected generic planar stress; b>=2 remains outside.",
            "evidence": "BRANCHING_ONE_UNLOADED_FILTERS.md", **dict(total),
            "closed_by_first_witness": dict(kinds), "proofs": PROOFS,
            "by_loaded_count": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case")
    parser.add_argument("--catalog-dir", type=Path)
    parser.add_argument("--open-cases", type=Path, help="Export remaining code-based IDs to this file")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if args.case:
        if args.open_cases is not None:
            parser.error("--open-cases requires a full --catalog-dir pass")
        print(json.dumps(decode(args.case), indent=2))
        return
    if args.catalog_dir is None:
        parser.error("Supply --case or --catalog-dir")
    summary = summarize(args.catalog_dir, args.open_cases)
    path = ROOT / "branching_one_unloaded_progress.json"
    if args.write:
        path.write_text(json.dumps(summary, indent=2) + "\n")
    elif json.loads(path.read_text()) != summary:
        raise ValueError("Progress summary differs from reconstructed witnesses")
    print(f"PASS: {summary['hand_closed']}/{summary['raw_cases']} excluded; {summary['remaining']} remain")


if __name__ == "__main__":
    main()
