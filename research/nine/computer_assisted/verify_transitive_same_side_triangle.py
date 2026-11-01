#!/usr/bin/env python3
"""Exact three-root proof for the transitive-owner same-C-side triangle.

Uses only the already-audited rational interval primitives in the sibling
verify_perpendicular_single_free_triangle.py. No floating point or third-party
dependency. All three actual B support features and their limiting faces are
enclosed; the original C exit mean is safely relaxed over its entire [0,d].
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_perpendicular_single_free_triangle import (
    F, I, SQRT_SCALE, TARGET, Undecided, encode_box, frac, sqrt_enclosure)


def nonnegative(v):
    return None if v.hi < 0 else I(max(F(0), v.lo), v.hi)


def bound(box, branch):
    c, ell = box
    if ell.hi < 2*c.lo:
        return "empty_geometry", None
    s = sqrt_enclosure(1-c.square())
    S = (ell*s).intersect(0, 1)
    if S is None:
        return "empty_geometry", None
    C = sqrt_enclosure(1-S.square())
    d = (ell*c+C).intersect(0, 1)
    if d is None:
        return "empty_geometry", None
    K = s*C+c*S
    L0 = c*C-s*S
    if L0.lo > 0:
        return "empty_geometry", None
    # On ell>=2c and 0<=c<=1/2, one has S=ell*s>=c and hence L<=0.
    L = I(L0.lo, min(F(0), L0.hi))
    a = (1-ell)/(s-c)
    if branch == 0:
        N, D = nonnegative(K+L), S
        if N is None:
            return "empty_positive_force", None
        qb = (d+S, C)
    elif branch == 1:
        N, D = K, nonnegative(S-C)
        if D is None:
            return "empty_support_branch", None
        qb = (d-C+S, S+C)
    elif branch == 2:
        N, D = K, S
        eps = (-ell*L).intersect(0, 1)
        if eps is None:
            return "empty_original_mean", None
        qb = (d+S-eps*C, C+eps*S)
    else:
        raise ValueError("unknown support branch")
    na = sqrt_enclosure(s.square()+(a+c).square())
    wa = (c-s-s/na, s+c+(a+c)/na)
    # The original positive t=N/D has been cleared homogeneously. D=0 is
    # included as a limiting enclosure; original strict-domain D is positive.
    bx, by = s*D, N-c*D
    nb = sqrt_enclosure(bx.square()+by.square())
    wb = (qb[0]+bx/nb, qb[1]+by/nb)
    # Every actual C mean lies in [0,d]. Keep the entire interval, including
    # endpoints, even when a+t tends to zero in an enlarged boundary chart.
    mean = I(F(0), d.hi)
    horizontal = (F(3, 2)*(wa[0]-wb[0]).square()
                  + 2*(mean-(wa[0]+wb[0])/2).square())
    vertical = ((wa[1]-wb[1]).square()
                + (wb[1]+2).square() + (wa[1]+2).square())
    lower = (horizontal.lo+vertical.lo)/9
    return ("variance" if lower > TARGET else "undecided"), lower


def verify_root(branch, max_nodes, keep_tree):
    root = (I(F(0), F(1, 2)), I(F(0), F(1)))
    stats = {"branch": branch, "nodes": 0, "variance_leaves": 0,
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
            reason, lower = bound(box, branch)
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
        axis = 0 if widths[0] >= widths[1] else 1
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
    stats["least_margin_gt_1_over_3000"] = bool(
        least is not None and least > F(1, 3000))
    return stats, {"branch": branch, "root": encode_box(root), "nodes": tree}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--certificate", type=Path)
    p.add_argument("--max-nodes", type=int, default=1000000)
    args = p.parse_args()
    roots, trees = [], []
    for branch in range(3):
        stats, tree = verify_root(branch, args.max_nodes,
                                  args.certificate is not None)
        roots.append(stats)
        trees.append(tree)
        print(json.dumps(stats, sort_keys=True), flush=True)
    report = {"theorem": "transitive_same_side_triangle_radius_gt_25_over_12",
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
