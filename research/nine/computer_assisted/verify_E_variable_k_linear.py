#!/usr/bin/env python3
"""Independent exact replay of E-owned variable-k linear envelopes.

Imports no producer. The unboxed endpoint contribution, free-shoulder
formula, exact multiplier range and complete one-dimensional cover are
reconstructed here. --fraction selects the separate rational backend.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys
import time

import verify_joint_five_dyadic as arithmetic


def expression(interval, numerator, sign):
    assert sign in ("negative", "positive")
    assert isinstance(numerator, int) and 52992 <= numerator <= 81920
    k = F(numerator, 4096)
    t = arithmetic.A(arithmetic.I(interval[0], interval[1]), [1, 0, 0, 0])
    z = -t if sign == "negative" else t
    # E's support is deliberately unboxed after eliminating its slope.
    endpoint = arithmetic.R * arithmetic.length([arithmetic.A(46), arithmetic.A(k)]) - 46 - k
    b = F(27, 2)
    v = [arithmetic.A(b), k+b*z]
    costs = [[arithmetic.A(b), b*z], [arithmetic.A(0), arithmetic.A(k)]]
    shoulder = arithmetic.unfixed_bound(v, costs, box=(F(23, 30), F(13, 12), F(25, 32), F(21, 16)))
    residual = endpoint + shoulder - F(211, 4)
    return residual + 16*t if sign == "negative" else residual - F(29, 2)*t


def upper(interval, numerator, sign):
    entire = expression(interval, numerator, sign)
    middle = (interval[0]+interval[1])/2
    centered = expression((middle, middle), numerator, sign).x
    centered += entire.der[0] * arithmetic.I(interval[0]-middle, interval[1]-middle)
    ceiling = min(entire.x.hi, centered.hi)
    return F(ceiling, arithmetic.SCALE) if hasattr(arithmetic, "SCALE") else ceiling


def verify(data, progress=False):
    assert data["type"] == "E_owned_variable_k_linear_cover_v1"
    assert data["proof_status"] == "producer_complete_pending_independent_replay"
    assert data["Q"] == "1105/256" and data["a"] == "46"
    assert data["b"] == "27/2" and data["T"] == "211/4"
    assert data["negative_coefficient"] == "16" and data["positive_coefficient"] == "29/2"
    assert data["multiplier_range"] == ["207/16", "20"]
    assert data["multiplier_denominator"] == 4096
    assert data["endpoint_bound"] == "unboxed_r_sqrt_46_squared_plus_k_squared_minus_46_minus_k"
    assert data["local_epsilon"] == "1/16" and data["root"] == 0
    sign = data["sign"]
    assert sign in ("negative", "positive")
    nodes = data["nodes"]
    pending = [(0, (F(1, 16), F(6)), 0)]
    seen = set()
    leaves = deepest = 0
    largest = None
    started = last = time.monotonic()
    while pending:
        index, expected, depth = pending.pop()
        assert isinstance(index, int) and 0 <= index < len(nodes) and index not in seen
        seen.add(index)
        deepest = max(deepest, depth)
        node = nodes[index]
        interval = tuple(map(F, node["box"]))
        assert interval == expected
        if "children" in node:
            assert "k_num" not in node and "upper" not in node
            children = node["children"]
            assert len(children) == 2 and children[0] != children[1]
            middle = (interval[0]+interval[1])/2
            pending.extend([(children[0], (interval[0], middle), depth+1),
                            (children[1], (middle, interval[1]), depth+1)])
        else:
            assert node["den"] == 4096 and "upper" in node
            ceiling = upper(interval, node["k_num"], sign)
            assert ceiling < 0, (sign, index, str(ceiling), interval)
            largest = ceiling if largest is None else max(largest, ceiling)
            leaves += 1
        now = time.monotonic()
        if progress and now-last > 25:
            print("INDEPENDENT E LINEAR", sign, "leaves", leaves,
                  "seconds", round(now-started, 1), flush=True)
            last = now
    assert len(seen) == len(nodes) and leaves == data["leaves"]
    assert deepest == data["max_depth"]
    return {"sign": sign, "complete": True, "nodes": len(seen), "leaves": leaves,
            "max_depth": deepest, "largest_replayed_upper": str(largest),
            "seconds": time.monotonic()-started}


def main():
    global arithmetic
    rational = "--fraction" in sys.argv
    if rational:
        import verify_joint_five_fraction as arithmetic
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    result = verify(json.loads(raw), True)
    result.update({"sha256": hashlib.sha256(raw).hexdigest(),
                   "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "arithmetic_sha256": hashlib.sha256(Path(arithmetic.__file__).read_bytes()).hexdigest(),
                   "arithmetic": "exact Fraction intervals" if rational else "standalone64-bit directed dyadics",
                   "proof_status": "independent_E_linear_envelope_replay_passed"})
    suffix = "_fraction_replay.json" if rational else "_dyadic_replay.json"
    path.with_name(path.stem+suffix).write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
