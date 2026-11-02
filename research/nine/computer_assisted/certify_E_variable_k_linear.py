#!/usr/bin/env python3
"""Discovery producer for the E-owned variable-k one-dimensional envelopes.

Numerical minimization selects rational multipliers only. Every produced
leaf is checked with 96-bit outward intervals. A separate 64-bit/Fraction
replay is required before treating this tree as a certificate.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json
import math
import sys
import time

import numpy as np
from scipy.optimize import minimize_scalar

from joint_five_interval import D, V, S, rad, rho, norm, free_sum, minimum
from explore_fork_dual import min_support

K = F(207, 16)
B = F(27, 2)
T = F(211, 4)
EPS = F(1, 16)
DEN = 4096
KMIN = 52992
KMAX = 81920


def expression(interval, numerator, sign):
    t = D(V(interval[0], interval[1]), [1, 0, 0, 0])
    z = -t if sign == "negative" else t
    k = F(numerator, DEN)
    endpoint = rad * norm([D(46), D(k)]) - 46 - k
    vector = [D(B), k + B*z]
    penalties = [[D(B), B*z], [D(0), D(k)]]
    cost = free_sum(penalties)
    circle = rad * norm(vector) - free_sum([vector, *penalties])
    center = rho * norm(vector) - cost
    xl, xh, yl, yh = F(23, 30), F(13, 12), F(25, 32), F(21, 16)
    rectangle = ((xl+xh)*vector[0] + (yl+yh)*vector[1]
                 + (xh-xl)*vector[0].abs() + (yh-yl)*vector[1].abs()) / 2 - cost
    result = endpoint + minimum([circle, center, rectangle]) - T
    return result + 16*t if sign == "negative" else result - F(29, 2)*t


def ceiling(interval, numerator, sign):
    entire = expression(interval, numerator, sign)
    middle = (interval[0] + interval[1]) / 2
    centered = expression((middle, middle), numerator, sign).v
    centered += entire.g[0] * V(interval[0]-middle, interval[1]-middle)
    return min(entire.v.h, centered.h)


def floating_value(t, k, sign):
    z = -t if sign == "negative" else t
    r = math.sqrt(1105/256)
    rho_float = math.sqrt(1105/256-.25)-.5
    b = 13.5
    v = np.array([b, k+b*z])
    costs = [np.array([b, b*z]), np.array([0., k])]
    penalty = min_support(costs)
    shoulder = min(r*np.linalg.norm(v)-min_support([v, *costs]),
                   rho_float*np.linalg.norm(v)-penalty,
                   max((23/30)*v[0], (13/12)*v[0])
                   + max((25/32)*v[1], (21/16)*v[1])-penalty)
    result = r*math.hypot(46, k)-46-k+shoulder-52.75
    return result + 16*t if sign == "negative" else result - 14.5*t


def choose_multiplier(t, sign):
    anchors = [float(K), 14., 15., 16., 17., 18., 19., 20.]
    choices = list(anchors)
    for low, high in zip(anchors, anchors[1:]):
        result = minimize_scalar(lambda k: floating_value(t, k, sign),
                                 bounds=(low, high), method="bounded",
                                 options={"xatol": 1e-10})
        choices.append(float(result.x))
    selected = min(choices, key=lambda k: floating_value(t, k, sign))
    return max(KMIN, min(KMAX, round(selected*DEN)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sign", choices=("negative", "positive"), required=True)
    args = parser.parse_args()
    sign = args.sign
    output = Path(__file__).with_name(f"E_variable_k_linear_{sign}_cover.json")
    nodes = [{"box": [str(EPS), "6"]}]
    pending = [(0, (EPS, F(6)), None, 0)]
    leaves = deepest = 0
    largest = None
    started = last = time.monotonic()
    while pending:
        index, interval, inherited, depth = pending.pop()
        deepest = max(deepest, depth)
        numerator = inherited
        bound = None if numerator is None else ceiling(interval, numerator, sign)
        if bound is None or bound >= 0:
            middle = (interval[0]+interval[1])/2
            numerator = choose_multiplier(float(middle), sign)
            bound = ceiling(interval, numerator, sign)
        if bound < 0:
            nodes[index].update(den=DEN, k_num=numerator, upper=str(F(bound, S)))
            largest = bound if largest is None else max(largest, bound)
            leaves += 1
        else:
            middle = (interval[0]+interval[1])/2
            point = expression((middle, middle), numerator, sign).v.h
            assert point < 0, (sign, interval, numerator, F(point, S))
            assert depth < 55
            left, right = (interval[0], middle), (middle, interval[1])
            left_index = len(nodes)
            right_index = left_index+1
            nodes.extend([{"box": list(map(str, left))}, {"box": list(map(str, right))}])
            nodes[index]["children"] = [left_index, right_index]
            pending.extend([(right_index, right, numerator, depth+1),
                            (left_index, left, numerator, depth+1)])
        now = time.monotonic()
        if now-last > 25:
            print("E LINEAR", sign, "leaves", leaves, "pending", len(pending),
                  "seconds", round(now-started, 1), flush=True)
            last = now
    data = {
        "type": "E_owned_variable_k_linear_cover_v1", "sign": sign,
        "proof_status": "producer_complete_pending_independent_replay",
        "Q": "1105/256", "a": "46", "b": "27/2", "T": "211/4",
        "negative_coefficient": "16", "positive_coefficient": "29/2",
        "multiplier_range": ["207/16", "20"], "multiplier_denominator": DEN,
        "endpoint_bound": "unboxed_r_sqrt_46_squared_plus_k_squared_minus_46_minus_k",
        "local_epsilon": "1/16", "root": 0, "nodes": nodes,
        "leaves": leaves, "max_depth": deepest,
        "largest_producer_upper": str(F(largest, S)),
        "seconds": time.monotonic()-started,
    }
    output.write_text(json.dumps(data, separators=(",", ":"))+"\n")
    print("COMPLETE E LINEAR", sign, "nodes", len(nodes), "leaves", leaves,
          "depth", deepest, "largest", float(F(largest, S)),
          "seconds", round(time.monotonic()-started, 1), flush=True)


if __name__ == "__main__":
    main()
