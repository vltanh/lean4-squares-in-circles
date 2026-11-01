#!/usr/bin/env python3
"""Exact two-endpoint/three-parameter variance proof for the transitive
perpendicular-C-owner triangle. The full A exit arc is reduced analytically to
its two endpoints; both are verified here on the entire enlarged chart.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_perpendicular_single_free_triangle import (
    F, I, SQRT_SCALE, TARGET, Undecided, cos_half, encode_box, frac,
    orientation, sin_half, sqrt_enclosure)


def variance_bound(box, mode):
    p, r, z = box
    if cos_half(p.lo) < sin_half(p.lo):
        return "empty_angle", None
    c, s = orientation(p)
    S = r*s
    C = sqrt_enclosure(1-S.square())
    # ell=r+(1-r)z is increasing in each coordinate on the unit square.
    ell = I(r.lo+(1-r.lo)*z.lo, r.hi+(1-r.hi)*z.hi)
    s0 = 1-(1-r)*z*s
    t0 = (1-C+ell*c).intersect(0, 1)
    if t0 is None:
        return "empty_position", None
    eps = (r*(c*C+s*S)).intersect(0, r.hi)
    if eps is None:
        return "empty_original_mean", None
    qa = (1+c+s, s0+s-c)
    if mode == 0:
        wa = (qa[0]+1, qa[1])
    elif mode == 1:
        wa = (qa[0]+s, qa[1]-c)
    else:
        raise ValueError("unknown arc endpoint")
    wb = (t0-2*S+eps*C, 1+2*C+eps*S)
    norm = sqrt_enclosure(t0.square()+s0.square())
    wc = (-t0/norm, -s0/norm)
    total = F(0)
    for first, second in ((wa, wb), (wb, wc), (wc, wa)):
        for axis in (0, 1):
            total += (first[axis]-second[axis]).square().lo
    lower = total/9
    return ("variance" if lower > TARGET else "undecided"), lower


def verify_root(mode, max_nodes, keep_tree):
    root = (I(F(0), F(1, 2)), I(F(0), F(1)), I(F(0), F(1)))
    stats = {"mode": mode, "nodes": 0, "variance_leaves": 0,
             "empty_leaves": 0, "max_depth": 0, "empty_reasons": {}}
    least, tree = None, []
    stack = [(root, 0, "")]
    while stack:
        box, depth, address = stack.pop()
        stats["nodes"] += 1
        stats["max_depth"] = max(stats["max_depth"], depth)
        if stats["nodes"] > max_nodes or depth > 70:
            raise RuntimeError("UNRESOLVED: proof resource limit reached")
        try:
            reason, lower = variance_bound(box, mode)
        except Undecided:
            reason, lower = "undecided", None
        if reason == "variance":
            stats["variance_leaves"] += 1
            margin = lower-TARGET
            least = margin if least is None else min(least, margin)
            if keep_tree:
                tree.append({"address": address, "box": encode_box(box),
                             "reason": reason, "lower_bound": frac(lower)})
            continue
        if reason.startswith("empty_"):
            stats["empty_leaves"] += 1
            reasons = stats["empty_reasons"]
            reasons[reason] = reasons.get(reason, 0)+1
            if keep_tree:
                tree.append({"address": address, "box": encode_box(box),
                             "reason": reason})
            continue
        widths = [v.hi-v.lo for v in box]
        axis = max(range(3), key=lambda i: widths[i])
        v = box[axis]
        middle = (v.lo+v.hi)/2
        left, right = list(box), list(box)
        left[axis], right[axis] = I(v.lo, middle), I(middle, v.hi)
        if keep_tree:
            tree.append({"address": address, "split_axis": axis,
                         "split_at": frac(middle)})
        stack.append((tuple(right), depth+1, address+"1"))
        stack.append((tuple(left), depth+1, address+"0"))
    stats["least_margin"] = None if least is None else frac(least)
    stats["least_margin_gt_1_over_7000"] = bool(
        least is not None and least > F(1, 7000))
    return stats, {"mode": mode, "root": encode_box(root), "nodes": tree}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--certificate", type=Path)
    p.add_argument("--max-nodes", type=int, default=2000000)
    args = p.parse_args()
    roots, trees = [], []
    for mode in range(2):
        stats, tree = verify_root(mode, args.max_nodes,
                                  args.certificate is not None)
        roots.append(stats)
        trees.append(tree)
        print(json.dumps(stats, sort_keys=True), flush=True)
    report = {"theorem": "transitive_perpendicular_triangle_radius_gt_25_over_12",
              "target_squared": frac(TARGET), "sqrt_scale": SQRT_SCALE,
              "roots": roots,
              "total_nodes": sum(x["nodes"] for x in roots),
              "total_variance_leaves": sum(x["variance_leaves"] for x in roots),
              "total_empty_leaves": sum(x["empty_leaves"] for x in roots)}
    if args.certificate:
        args.certificate.parent.mkdir(parents=True, exist_ok=True)
        args.certificate.write_text(json.dumps({"report": report, "trees": trees},
                                               separators=(",", ":"))+"\n")
    print(json.dumps(report, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
