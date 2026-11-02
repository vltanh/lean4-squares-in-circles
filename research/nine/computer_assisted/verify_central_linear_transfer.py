#!/usr/bin/env python3
"""Independent replay of the compact owner-free central transfer.

Negative and mixed-sign roots are handled by complete hand lemmas. Every
numerical leaf is explicitly required to be in the positive quadrant;
the simplified positive-quadrant formula below has no signed-sum branch.
No producer code or producer interval arithmetic is imported.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys
import time

import verify_joint_five_dyadic as arithmetic


def initial_boxes():
    return [(F(-6), F(0), F(-6), F(0)),
            (F(-6), F(0), F(0), F(6)),
            (F(0), F(6), F(0), F(6))]


def positive_expression(box):
    assert box[0] >= 0 and box[2] >= 0
    x = arithmetic.A(arithmetic.I(box[0], box[1]), [1, 0, 0, 0])
    y = arithmetic.A(arithmetic.I(box[2], box[3]), [0, 1, 0, 0])
    total = x+y
    xx, yy = 1+x.sq(), 1+y.sq()
    dx = arithmetic.length([arithmetic.A(1), x])
    dy = arithmetic.length([arithmetic.A(1), y])
    product_gap = (x*y-1).absolute()
    triangle = arithmetic.least([
        1+total,
        (xx+product_gap+total*(2+x))/(2*dx),
        (yy+product_gap+total*(2+y))/(2*dy),
    ])
    # The first branch pays the outer linear cost. The second contradicts
    # the actual two-central-edge capacity, whose upper bound is strict.
    payment = triangle-1-F(263, 270)*total
    impossible_capacity = triangle+total/10-F(61, 60)*(dx+dy)
    return arithmetic.greatest([payment, impossible_capacity])


def lower(box):
    whole = positive_expression(box)
    midpoints = [(box[0]+box[1])/2, (box[2]+box[3])/2]
    point = tuple(v for middle in midpoints for v in (middle, middle))
    centered = positive_expression(point).x
    for j, middle in enumerate(midpoints):
        centered += whole.der[j] * arithmetic.I(box[2*j]-middle, box[2*j+1]-middle)
    value = max(whole.x.lo, centered.lo)
    return F(value, arithmetic.SCALE) if hasattr(arithmetic, "SCALE") else value


def verify(data, progress=False):
    assert data["type"] == "central_linear_transfer_cover_v1"
    assert data["proof_status"] == "producer_complete_pending_independent_replay"
    assert data["positive_outer_coefficient"] == "29/2"
    assert data["negative_outer_coefficient"] == "16"
    assert data["Q"] == "1105/256" and data["r_upper"] == "133/64"
    assert data["rho_upper"] == "91/60" and data["floor"] == "1/10"
    assert data["root_indices"] == [0, 1, 2] and data["remaining"] == 0
    nodes = data["nodes"]
    pending = [(i, box, 0) for i, box in enumerate(initial_boxes())]
    seen = set()
    ordinary = analytic = deepest = 0
    smallest = None
    reasons = {}
    started = last = time.monotonic()
    while pending:
        index, expected, depth = pending.pop()
        assert isinstance(index, int) and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        deepest = max(deepest, depth)
        node = nodes[index]
        box = tuple(map(F, node["box"]))
        assert box == expected
        if "children" in node:
            assert "lower" not in node and "terminal" not in node
            dimension = node["split"]
            assert isinstance(dimension, int) and dimension in (0, 1)
            children = node["children"]
            assert len(children) == 2 and children[0] != children[1]
            middle = (box[2*dimension]+box[2*dimension+1])/2
            left, right = list(box), list(box)
            left[2*dimension+1], right[2*dimension] = middle, middle
            pending.extend([(children[0], tuple(left), depth+1),
                            (children[1], tuple(right), depth+1)])
        elif "terminal" in node:
            assert "lower" not in node
            name = node["terminal"]
            if name == "nonpositive_signed_sum":
                assert box[1]+box[3] <= 0
            elif name == "mixed_sign_triangle":
                assert (box[1] <= 0 <= box[2]) or (box[3] <= 0 <= box[0])
            else:
                assert name == "signed_sum_strip"
                assert box[0]+box[2] >= -1 and box[1]+box[3] <= 1
            reasons[name] = reasons.get(name, 0)+1
            analytic += 1
        else:
            assert "lower" in node
            # This requirement intentionally rules out the original
            # signed-sum-crossing midpoint formula. Compact proof rows
            # only use the independently reconstructed positive formula.
            assert box[0] >= 0 and box[2] >= 0
            value = lower(box)
            assert value > 0, (index, str(value), box)
            smallest = value if smallest is None else min(smallest, value)
            ordinary += 1
        now = time.monotonic()
        if progress and now-last > 25:
            print("INDEPENDENT CENTRAL TRANSFER", "interval", ordinary,
                  "analytic", analytic, "seconds", round(now-started, 1), flush=True)
            last = now
    assert len(seen) == len(nodes)
    assert ordinary+analytic == data["closed"]
    return {"complete": True, "nodes": len(seen), "interval_leaves": ordinary,
            "analytic_leaves": analytic, "analytic_reasons": reasons,
            "max_depth": deepest, "smallest_replayed_lower": str(smallest),
            "seconds": time.monotonic()-started}


def main():
    global arithmetic
    rational = "--fraction" in sys.argv
    if rational:
        import verify_joint_five_fraction as arithmetic
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    report = verify(json.loads(raw), True)
    report.update({"sha256": hashlib.sha256(raw).hexdigest(),
                   "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "arithmetic_sha256": hashlib.sha256(Path(arithmetic.__file__).read_bytes()).hexdigest(),
                   "arithmetic": "exact Fraction intervals" if rational else "standalone64-bit directed dyadics",
                   "proof_status": "independent_central_transfer_replay_passed"})
    suffix = "_fraction_replay.json" if rational else "_dyadic_replay.json"
    path.with_name(path.stem+suffix).write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
