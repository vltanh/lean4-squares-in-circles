#!/usr/bin/env python3
"""Independent exact replay for the original E<=A five-frame relaxation.

This module never imports a numerical producer or optimizer.  Its 18 real
variables are the seven original centers, h_B,h_F,g_B,g_F.  Original A,C,D,E,G
frames range over signed rational slope intervals.  The only imported code
consists of the previously reviewed Fraction/radical support formulas.

The caller is the unchanged strict original 001/00 predicate at R^2<=1105/256,
with v_CD>=2/3 and the accepted G-order, C-slant, CG, CF, G-projection and
A-localization consequences.  In particular, the selected-CD sign omissions retain the strict
weak-link premise.  A successful forest is an E-order theorem in that caller;
it does not claim a whole fixed-mask exclusion.
"""
from functools import lru_cache
from itertools import combinations, product
from math import gcd
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import time

from weak_outer_hand_right_lower_verify import (
    F, Q, RHO, A, B, ROOT_BITS, root_bounds, h_bounds, support_lower,
    normal_bounds, pair_support_lower, cap_tilt_bounds,
)

N = 18
V = F(2, 3)
T = F(211, 4)
PHYSICAL = (0, 2, 3, 4, 6)
FRAME_INDEX = {i: k for k, i in enumerate(PHYSICAL)}
H_INDEX = {1: 14, 5: 15}
G_INDEX = {1: 16, 5: 17}
ROOTS = tuple(product(
    ((F(-1, 5), F(0)), (F(0), F(1, 5))),
    *([((F(-1), F(0)), (F(0), F(1)))] * 4),
))
INITIAL_POSE = tuple(
    [(-RHO, RHO)] * 14
    + [(F(1, 2), F(5, 7))] * 2
    + [(F(7, 20), F(1, 2))] * 2
)
SAT_PAIRS = ((0, 4), (2, 3), (3, 6))
INSET_PAIRS = ((1, 5), (1, 4), (0, 4), (2, 4), (3, 5))
ALL_PAIRS = tuple(combinations(range(7), 2))
ACTUAL_PAIRS = ((0, 1), (1, 2), (4, 5), (5, 6))
CONE_PAIRS = ((0, 1), (1, 2), (2, 3), (4, 5), (5, 6))
TANGENTS = tuple(F(k, 32) for k in range(16, 24))

# Reconstruct the direction list exactly, without importing a discovery file.
_directions = {
    (x, y) for x in range(-4, 5) for y in range(-4, 5)
    if (x or y) and gcd(x, y) == 1
}
for _p, _q in ((32, 9), (128, 35), (128, 37), (24, 23), (96, 91), (32, 31)):
    for _x, _y in ((_p, _q), (_q, _p)):
        for _sx, _sy in product((-1, 1), repeat=2):
            _directions.add((_sx * _x, _sy * _y))
INTEGER_DIRECTIONS = tuple(sorted(_directions))
UNIT_DIRECTIONS = tuple(sorted({
    (F(sx * (1024 - k * k), 1024 + k * k),
     F(sy * 64 * k, 1024 + k * k))
    for k in range(33) for sx, sy in product((-1, 1), repeat=2)
}))
DIRECTIONS = INTEGER_DIRECTIONS + UNIT_DIRECTIONS
assert len(INTEGER_DIRECTIONS) == 96 and len(UNIT_DIRECTIONS) == 128

# Fixed row blocks, followed by chosen separating rows and nine final rows.
COORDINATE_ROWS = 2 * N
CIRCLE_ROWS = sum((len(DIRECTIONS) if i in FRAME_INDEX else 2 * len(DIRECTIONS)) + 4
                  for i in range(7))
ENVELOPE_ROWS = 18
ACTUAL_ROWS = 4
CONE_ROWS = 10
CORE_ROWS = 18
DISTANCE_ROWS = len(ALL_PAIRS)
CHOICE_START = (COORDINATE_ROWS + CIRCLE_ROWS + ENVELOPE_ROWS
                + ACTUAL_ROWS + CONE_ROWS + CORE_ROWS + DISTANCE_ROWS)
assert CHOICE_START == 2151
FINAL_ROWS = 9
SCHEMA = "weak-outer-E-order-farkas-v1"


@lru_cache(maxsize=8192)
def context(box, pose):
    """Outward rational bounds derived only from the original physical caller."""
    hs = {i: h_bounds(box[k]) for k, i in enumerate(PHYSICAL)}
    hs[0] = (hs[0][0], min(hs[0][1], F(37, 64)))
    for i in (1, 5):
        upper = min(root_bounds(F(1, 2))[1], pose[H_INDEX[i]][1])
        if i == 1:
            upper = min(upper, F(69, 64) - hs[0][0])
        hs[i] = (max(F(1, 2), pose[H_INDEX[i]][0]), upper)
    gs = {i: F(1, 4) / hs[i][1] for i in range(7)}
    xs = (
        (-RHO, -F(59, 64) - hs[0][0]),
        (-F(31, 60), -F(27, 64)),
        (hs[2][0] - F(1, 60),
         min(RHO - gs[2] - gs[3], F(133, 64) - 1 - gs[2], hs[2][1] + F(5, 64))),
        (max(F(4, 3), hs[2][0] - F(1, 60) + gs[2] + gs[3]),
         min(RHO, F(133, 64) - hs[3][0])),
        (-RHO, min(RHO - hs[4][0] - hs[6][0] - 1,
                   F(31, 60) - hs[4][0] - hs[5][0])),
        (-F(115, 432), F(31, 60)),
        (hs[6][0] + F(101, 432), min(RHO, F(133, 64) - hs[6][0])),
    )
    cb = []
    for i in range(7):
        lo = max(xs[i][0], pose[2 * i][0])
        hi = min(xs[i][1], pose[2 * i][1])
        yl, yu = -RHO, RHO
        if i in FRAME_INDEX:
            hlo, hhi = hs[i]
            jlo = root_bounds(max(F(0), F(1, 2) - hhi * hhi))[0]
            xabs = max(F(0), lo, -hi)
            cap = min(RHO, max(
                root_bounds(max(F(0), Q - (xabs + hlo) ** 2))[1] - jlo,
                root_bounds(max(F(0), Q - (xabs + jlo) ** 2))[1] - hlo,
            ))
            yl, yu = -cap, cap
        cb.extend(((lo, hi), (max(yl, pose[2 * i + 1][0]), min(yu, pose[2 * i + 1][1]))))

    # The contained A inset crosses y=0 by at least 3/40.
    a_inset_upper = F(1, 4) / hs[0][0]
    cb[1] = (max(cb[1][0], -a_inset_upper + F(3, 40)),
             min(cb[1][1], a_inset_upper - F(3, 40)))
    cb[5] = (cb[5][0], min(cb[5][1], -F(7, 32) - F(7, 8) * cb[4][0]))
    clearance = max(gs[3] + gs[6], F(7, 8) * (hs[3][0] + hs[6][0]) - F(41, 120))
    cb[7] = (max(cb[7][0], cb[5][0] + V), min(cb[7][1], cb[13][1] - clearance))
    cb[5] = (cb[5][0], min(cb[5][1], cb[7][1] - V))
    cb[13] = (max(cb[13][0], cb[7][0] + clearance), cb[13][1])
    cb[11] = (max(cb[11][0], cb[5][0] + gs[2] + root_bounds(F(1, 8))[0]), cb[11][1])
    cb[9] = (cb[9][0], min(cb[9][1], cb[1][1]))
    cb.extend((hs[1], hs[5]))
    for i in (1, 5):
        cb.append((max(root_bounds(F(1, 8))[0], F(1, 4) / hs[i][1], pose[G_INDEX[i]][0]),
                   min(F(1, 2), F(1, 4) / hs[i][0], pose[G_INDEX[i]][1])))

    universal, signed = cap_tilt_bounds(box[FRAME_INDEX[3]])
    dmax = min(F(31, 30), 1 - hs[2][0] + universal)
    if signed is not None:
        dmax = min(dmax, 2 - hs[2][0] - signed)
    return hs, gs, tuple(cb), clearance, dmax


def difference_interval(box, pose, i, j, axis):
    hs, gs, cb, clearance, dmax = context(box, pose)
    lo = cb[2 * j + axis][0] - cb[2 * i + axis][1]
    hi = cb[2 * j + axis][1] - cb[2 * i + axis][0]
    if (i, j) == (2, 3):
        lo = max(lo, gs[2] + gs[3] if axis == 0 else V)
        hi = min(hi, dmax)
    if (i, j) == (3, 6):
        if axis == 0:
            lo, hi = max(lo, -F(1459, 1728)), min(hi, F(11, 60))
        else:
            lo = max(lo, clearance)
    if (i, j) == (0, 4) and axis == 1:
        hi = min(hi, F(0))
    return lo, hi


def interval_witness(box, pose):
    hs, gs, cb, clearance, dmax = context(box, pose)
    for i in range(7):
        lo, hi = hs[i]
        if lo > hi:
            return ["width", i], lo - hi
    for k, (lo, hi) in enumerate(cb):
        if lo > hi:
            return ["coordinate", k], lo - hi
    for i, j in ALL_PAIRS:
        for axis in (0, 1):
            lo, hi = difference_interval(box, pose, i, j, axis)
            if lo > hi:
                return ["difference", i, j, axis], lo - hi
    return None, None


def empty_interval_reserve(tag, box, pose):
    assert type(tag) is list and tag
    if tag[0] == "width":
        assert len(tag) == 2 and type(tag[1]) is int and 0 <= tag[1] < 7
        lo, hi = context(box, pose)[0][tag[1]]
    elif tag[0] == "coordinate":
        assert len(tag) == 2 and type(tag[1]) is int and 0 <= tag[1] < N
        lo, hi = context(box, pose)[2][tag[1]]
    else:
        assert len(tag) == 4 and tag[0] == "difference"
        i, j, axis = tag[1:]
        assert all(type(z) is int for z in (i, j, axis)) and (i, j) in ALL_PAIRS and axis in (0, 1)
        lo, hi = difference_interval(box, pose, i, j, axis)
    assert lo > hi, ("false empty interval", tag, box, pose)
    return lo - hi


def _row(box, pose, terms=(), rhs=F(0), widths=(), insets=()):
    hs, gs, cb, clearance, dmax = context(box, pose)
    result = [F(0)] * N
    for k, value in terms:
        result[k] += value
    for i, value in widths:
        if i in H_INDEX:
            result[H_INDEX[i]] += value
        else:
            rhs -= value * (hs[i][0] if value >= 0 else hs[i][1])
    for i, value in insets:
        if i in G_INDEX:
            result[G_INDEX[i]] += value
        else:
            assert value >= 0, "Only lower physical inset bounds are used."
            rhs -= value * gs[i]
    return result, rhs


def rational_row(index, box, pose, choices):
    """Reconstruct one necessary inequality; no claimed producer row is read."""
    assert type(index) is int and 0 <= index < CHOICE_START + len(choices) + FINAL_ROWS
    hs, gs, cb, clearance, dmax = context(box, pose)
    if index < COORDINATE_ROWS:
        k = index // 2
        return _row(box, pose, ((k, 1),), cb[k][1]) if index % 2 == 0 else _row(box, pose, ((k, -1),), -cb[k][0])
    index -= COORDINATE_ROWS
    for i in range(7):
        direction_rows = len(DIRECTIONS) if i in FRAME_INDEX else 2 * len(DIRECTIONS)
        if index < direction_rows:
            direction = index if i in FRAME_INDEX else index // 2
            p, q = DIRECTIONS[direction]
            terms = ((2 * i, p), (2 * i + 1, q))
            norm2 = p * p + q * q
            if i in FRAME_INDEX:
                rhs = root_bounds(Q * norm2)[1] - support_lower(box[FRAME_INDEX[i]], (p, q))
                return _row(box, pose, terms, rhs)
            if index % 2 == 0:
                return _row(box, pose, terms, RHO * root_bounds(F(norm2))[1])
            return _row(box, pose, terms, root_bounds(Q * norm2)[1], insets=((i, abs(p) + abs(q)),))
        index -= direction_rows
        if index < 4:
            axis, sign_index = divmod(index, 2)
            sign = -1 if sign_index == 0 else 1
            return _row(box, pose, ((2 * i + axis, sign),), root_bounds(Q)[1], widths=((i, 1),))
        index -= 4

    if index < ENVELOPE_ROWS:
        square_index, local = divmod(index, 9)
        i = (1, 5)[square_index]
        if local < 8:
            q = TANGENTS[local]
            return _row(box, pose, ((H_INDEX[i], -1 / (4 * q * q)), (G_INDEX[i], -1)), -1 / (2 * q))
        return _row(box, pose, ((G_INDEX[i], 1), (H_INDEX[i], F(7, 10))), F(17, 20))
    index -= ENVELOPE_ROWS
    if index < ACTUAL_ROWS:
        i, j = ACTUAL_PAIRS[index]
        return _row(box, pose, ((2 * i, 1), (2 * j, -1)), widths=((i, 1), (j, 1)))
    index -= ACTUAL_ROWS
    if index < CONE_ROWS:
        pair, sign_index = divmod(index, 2)
        i, j = CONE_PAIRS[pair]
        sign = -1 if sign_index == 0 else 1
        return _row(box, pose, ((2 * i, 1), (2 * j, -1), (2 * i + 1, -sign), (2 * j + 1, sign)))
    index -= CONE_ROWS
    if index < CORE_ROWS:
        universal, signed = cap_tilt_bounds(box[FRAME_INDEX[3]])
        core = (
            (((4, 1), (6, -1)), F(0), (), ((2, 1), (3, 1))),
            (((5, 1), (7, -1)), -V, (), ()),
            (((4, -1), (6, 1)), F(0), ((2, -1), (3, -1)), ()),
            (((9, 1), (1, -1)), F(0), (), ()),
            (((4, -A), (12, -B)), -B / 2, ((2, A), (6, B)), ()),
            (((6, 1), (12, -1)), F(1459, 1728), (), ()),
            (((6, -1), (12, 1)), F(11, 60), (), ()),
            (((7, 1), (13, -1)), -clearance, (), ()),
            (((4, F(7, 8)), (5, 1)), -F(7, 32), (), ()),
            (((5, 1), (13, -1)), -F(97, 4480), ((2, 1), (6, 1)), ()),
            (((5, 1), (11, -1)), F(0), (), ((2, 1), (5, 1))),
            (((5, 1), (11, -1), (10, -1), (4, 1)), -F(1, 25), (), ()),
            (((5, 1), (11, -1), (10, 1), (4, -1)), -F(1, 25), (), ()),
            (((0, -A), (8, -B)), T + F(17, 2), ((0, -29), (4, -B)), ()),
            (((4, -1), (6, 1)), 1 + universal, ((2, 1),), ()),
            (((6, A), (12, B)), T + A * universal, ((6, -B),), ()),
            (((), F(0), (), ()) if signed is None else (((4, -1), (6, 1)), 2 - signed, ((2, 1),), ())),
            (((), F(0), (), ()) if signed is None else (((6, A), (12, B)), T + A - A * signed, ((6, -B),), ())),
        )
        terms, rhs, widths, insets = core[index]
        return _row(box, pose, terms, rhs, widths, insets)
    index -= CORE_ROWS
    if index < DISTANCE_ROWS:
        i, j = ALL_PAIRS[index]
        lx, ux = difference_interval(box, pose, i, j, 0)
        ly, uy = difference_interval(box, pose, i, j, 1)
        assert lx <= ux and ly <= uy, "An empty difference requires an explicit interval terminal."
        return _row(box, pose,
                    ((2 * i, lx + ux), (2 * j, -lx - ux), (2 * i + 1, ly + uy), (2 * j + 1, -ly - uy)),
                    -1 - lx * ux - ly * uy)
    index -= DISTANCE_ROWS
    if index < len(choices):
        kind, i, j, axis, sign, owner = choices[index]
        if kind == "inset":
            return _row(box, pose, ((2 * i + axis, sign), (2 * j + axis, -sign)), insets=((i, 1), (j, 1)))
        normal = normal_bounds(box[FRAME_INDEX[owner]], axis, sign)
        midpoint = tuple(F(round((lo + hi) * (1 << 29)), 1 << 30) for lo, hi in normal)
        error = F(0)
        for xy in (0, 1):
            low, high = difference_interval(box, pose, i, j, xy)
            assert low <= high, "An empty difference requires an explicit interval terminal."
            eps = (normal[xy][0] - midpoint[xy], normal[xy][1] - midpoint[xy])
            error += max(e * d for e in eps for d in (low, high))
        return _row(box, pose,
                    ((2 * i, midpoint[0]), (2 * i + 1, midpoint[1]), (2 * j, -midpoint[0]), (2 * j + 1, -midpoint[1])),
                    -pair_support_lower(box[FRAME_INDEX[i]], box[FRAME_INDEX[j]]) + error)
    index -= len(choices)
    if index == 0:
        return _row(box, pose, rhs=F(69, 64), widths=((0, 1), (1, 1)))
    # Reflect y, including both originals and the actual selected AE normal.
    # This uses the signed-left-cap theorem only when its physical sign premise
    # is certified over the entire selected branch.
    if index == 1:
        if box[FRAME_INDEX[0]][0] >= 0:
            for kind, i, j, axis, sign, owner in choices:
                if kind == "sat" and (i, j) == (0, 4):
                    if normal_bounds(box[FRAME_INDEX[owner]], axis, sign)[1][1] < 0:
                        signed = cap_tilt_bounds(box[FRAME_INDEX[0]])[1]
                        assert signed is not None
                        return _row(box, pose, ((0, -A), (8, -B)), T + A - A * signed, widths=((4, -B),))
        return _row(box, pose)
    # Append-only consequences of the independently completed G projection
    # table.  Old row indices, contexts and secant coefficients are unchanged.
    if index == 2:
        return _row(box, pose, ((12, 1),), F(49, 64), widths=((6, -1),))
    if index == 3:
        return _row(box, pose, ((9, 1), (1, -1)), insets=((0, 1), (4, 1)))
    if index in (4, 5):
        sign = -1 if index == 4 else 1
        return _row(box, pose, ((9, 1), (1, -1), (8, sign), (0, -sign)), -F(3, 20))
    if index == 6:
        return _row(box, pose, ((3, 1), (11, -1)), insets=((1, 1), (5, 1)))
    if index == 7:
        return _row(box, pose, ((3, 1), (11, -1), (10, 1), (2, -1)), -F(1, 7104))
    assert index == 8
    if box[FRAME_INDEX[0]][0] >= 0:
        signed = cap_tilt_bounds(box[FRAME_INDEX[0]])[1]
        assert signed is not None
        return _row(box, pose, ((0, -A), (8, -B)), T + A - A * signed, widths=((4, -B),))
    return _row(box, pose)


def all_options(kind, i, j):
    if kind == "inset":
        assert (i, j) in INSET_PAIRS
        return tuple((kind, i, j, axis, sign, -1) for axis in (0, 1) for sign in (-1, 1))
    assert kind == "sat" and (i, j) in SAT_PAIRS
    return tuple((kind, i, j, axis, sign, owner)
                 for owner in (i, j) for axis in (0, 1) for sign in (-1, 1))


def omitted_option_impossible(box, option):
    kind, i, j, axis, sign, owner = option
    if kind == "inset":
        if (i, j) == (0, 4):
            return (axis, sign) != (1, -1)
        if (i, j) == (1, 5):
            return (axis, sign) != (1, 1)
        return False
    if (i, j) == (0, 4):
        return normal_bounds(box[FRAME_INDEX[owner]], axis, sign)[1][0] >= 0
    if (i, j) == (2, 3):
        return (sign < 0
                or (axis == 1 and box[FRAME_INDEX[owner]][0] >= 0)
                or normal_bounds(box[FRAME_INDEX[owner]], axis, sign)[1][1] <= 0)
    if (i, j) == (3, 6):
        return normal_bounds(box[FRAME_INDEX[owner]], axis, sign)[1][1] <= 0
    return False


def child_states(node, box, pose, choices):
    """Check the complete closed-child union and yield its rational states."""
    if node.get("kind") == "angle":
        assert set(node) == {"kind", "axis", "children"}
        assert set(node["children"]) == {"0", "1"}
        k = node["axis"]
        assert type(k) is int and 0 <= k < len(PHYSICAL)
        lo, hi = box[k]
        midpoint = (lo + hi) / 2
        for side, interval in enumerate(((lo, midpoint), (midpoint, hi))):
            newbox = list(box)
            newbox[k] = interval
            yield node["children"][str(side)], tuple(newbox), pose, choices
    elif node.get("kind") == "pose":
        assert set(node) == {"kind", "axis", "cut_integer", "cut_power", "children"}
        assert set(node["children"]) == {"0", "1"}
        k, integer, power = node["axis"], node["cut_integer"], node["cut_power"]
        assert type(k) is int and 0 <= k < N
        assert type(integer) is int and type(power) is int and power == 20
        cut = F(integer, 1 << power)
        lo, hi = pose[k]
        assert lo < cut < hi, ("pose cut outside parent", k, cut, pose[k])
        for side, interval in enumerate(((lo, cut), (cut, hi))):
            newpose = list(pose)
            newpose[k] = interval
            yield node["children"][str(side)], box, tuple(newpose), choices
    else:
        assert set(node) == {"kind", "pair", "children"} and node["kind"] == "sep"
        pair = node["pair"]
        assert type(pair) is list and len(pair) == 3
        kind, i, j = pair
        assert type(kind) is str and type(i) is int and type(j) is int
        assert (kind, i, j) not in {choice[:3] for choice in choices}, "Repeated separating choice."
        allowed = all_options(kind, i, j)
        children = {}
        for key, child in node["children"].items():
            tail = tuple(map(int, key.split(",")))
            assert len(tail) == 3 and key == ",".join(map(str, tail))
            option = (kind, i, j) + tail
            assert option in allowed and option not in children
            children[option] = child
        for option in allowed:
            if option in children:
                yield children[option], box, pose, choices + (option,)
            else:
                assert omitted_option_impossible(box, option), ("uncovered physical separator", pair, option, box)


def leaf_reserve(weights, box, pose, choices):
    assert interval_witness(box, pose)[0] is None, "Use an explicit empty-interval terminal first."
    coefficients = [F(0)] * N
    right = F(0)
    seen = set()
    assert type(weights) is list and weights
    for index, weight in weights:
        assert type(index) is int and type(weight) is int and weight > 0 and index not in seen
        assert 0 <= index < CHOICE_START + len(choices) + FINAL_ROWS
        seen.add(index)
        row, rhs = rational_row(index, box, pose, choices)
        right += weight * rhs
        for k, value in enumerate(row):
            coefficients[k] += weight * value
    # Every center coordinate, and all four h/g variables, has modulus <rho.
    reserve = (-right - RHO * sum(abs(value) for value in coefficients)) / (1 << 40)
    assert reserve > 0, ("nonpositive exact Farkas reserve", str(reserve), box, pose, choices, weights)
    return reserve


def _path_steps(path):
    steps = []
    while "parent" in path:
        if "angle" in path:
            steps.append(("angle", path["angle"], path["side"]))
        elif "pose" in path:
            steps.append(("pose", path["pose"], path["cut_integer"], path["cut_power"], path["side"]))
        else:
            steps.append(("sep", tuple(path["sep"])))
        path = path["parent"]
    assert set(path) == {"root"} and type(path["root"]) is int and 0 <= path["root"] < len(ROOTS)
    return path["root"], list(reversed(steps))


def _follow_steps(root, steps):
    box, pose, choices = ROOTS[root], INITIAL_POSE, ()
    for step in steps:
        if step[0] == "angle":
            _, k, side = step
            assert type(k) is int and 0 <= k < 5 and type(side) is int and side in (0, 1)
            lo, hi = box[k]
            midpoint = (lo + hi) / 2
            newbox = list(box)
            newbox[k] = (lo, midpoint) if side == 0 else (midpoint, hi)
            box = tuple(newbox)
        elif step[0] == "pose":
            _, k, integer, power, side = step
            assert type(k) is int and 0 <= k < N and type(integer) is int and power == 20
            assert type(side) is int and side in (0, 1)
            cut = F(integer, 1 << power)
            lo, hi = pose[k]
            assert lo < cut < hi
            newpose = list(pose)
            newpose[k] = (lo, cut) if side == 0 else (cut, hi)
            pose = tuple(newpose)
        else:
            option = step[1]
            assert len(option) == 6 and option in all_options(*option[:3])
            assert option[:3] not in {old[:3] for old in choices}
            choices += (option,)
    return box, pose, choices


def pack(discovery, target):
    assert not discovery["frontier"], "The complete forest cannot retain an unresolved frontier."
    roots = [{} for _ in ROOTS]
    for leaf in discovery["leaves"]:
        root, steps = _path_steps(leaf["path"])
        assert root == leaf["root"] and leaf["power"] == 40
        current = roots[root]
        for step in steps:
            assert "w" not in current and "empty_interval" not in current
            kind = step[0]
            if kind == "angle":
                metadata = {"kind": "angle", "axis": step[1]}
                key = str(step[2])
            elif kind == "pose":
                metadata = {"kind": "pose", "axis": step[1], "cut_integer": step[2], "cut_power": step[3]}
                key = str(step[4])
            else:
                metadata = {"kind": "sep", "pair": list(step[1][:3])}
                key = ",".join(map(str, step[1][3:]))
            if current:
                assert {k: v for k, v in current.items() if k != "children"} == metadata
            else:
                current.update(metadata)
                current["children"] = {}
            current = current["children"].setdefault(key, {})
        assert not current, "Duplicate or overlapping terminal paths."
        current["w"] = leaf["weights"]

    def replace_empty(node, box, pose, choices):
        tag, reserve = interval_witness(box, pose)
        if tag is not None:
            node.clear()
            node["empty_interval"] = tag
        elif "w" not in node:
            if node.get("kind") == "sep":
                # Certify a newer sign omission at this parent box before
                # discarding any older partial subtree beneath that option.
                kind, i, j = node["pair"]
                allowed = all_options(kind, i, j)
                for key in list(node["children"]):
                    tail = tuple(map(int, key.split(",")))
                    assert len(tail) == 3 and key == ",".join(map(str, tail))
                    option = (kind, i, j) + tail
                    assert option in allowed
                    if omitted_option_impossible(box, option):
                        del node["children"][key]
            for child, newbox, newpose, newchoices in child_states(node, box, pose, choices):
                replace_empty(child, newbox, newpose, newchoices)
    for node, box in zip(roots, ROOTS):
        replace_empty(node, box, INITIAL_POSE, ())
    data = {"schema": SCHEMA, "root_bits": ROOT_BITS, "weight_power": 40, "roots": roots}
    with gzip.open(target, "wt", compresslevel=9) as handle:
        json.dump(data, handle, separators=(",", ":"))
        handle.write("\n")
    return data


def verify(data):
    assert set(data) == {"schema", "root_bits", "weight_power", "roots"}
    assert data["schema"] == SCHEMA and data["root_bits"] == ROOT_BITS and data["weight_power"] == 40
    assert len(data["roots"]) == len(ROOTS)
    stats = {key: 0 for key in ("nodes", "leaves", "angle_splits", "pose_splits", "separator_splits",
                                "farkas_leaves", "empty_interval_leaves", "max_depth")}
    least = None
    by_root = []

    def visit(node, box, pose, choices, depth):
        nonlocal least
        stats["nodes"] += 1
        stats["max_depth"] = max(stats["max_depth"], depth)
        if "empty_interval" in node:
            assert set(node) == {"empty_interval"}
            reserve = empty_interval_reserve(node["empty_interval"], box, pose)
            stats["empty_interval_leaves"] += 1
        elif "w" in node:
            assert set(node) == {"w"}
            reserve = leaf_reserve(node["w"], box, pose, choices)
            stats["farkas_leaves"] += 1
        else:
            kind = node.get("kind")
            assert kind in ("angle", "pose", "sep")
            stats[{"angle": "angle_splits", "pose": "pose_splits", "sep": "separator_splits"}[kind]] += 1
            for child, newbox, newpose, newchoices in child_states(node, box, pose, choices):
                visit(child, newbox, newpose, newchoices, depth + 1)
            return
        stats["leaves"] += 1
        least = reserve if least is None else min(least, reserve)
        if stats["leaves"] % 10000 == 0:
            print("exact leaves", stats["leaves"], "nodes", stats["nodes"], flush=True)

    for root, (node, box) in enumerate(zip(data["roots"], ROOTS)):
        before = stats["nodes"], stats["leaves"]
        visit(node, box, INITIAL_POSE, (), 0)
        by_root.append({"root": root, "nodes": stats["nodes"] - before[0], "leaves": stats["leaves"] - before[1]})
    assert least is not None
    scaled = least * 10**12
    stats.update(status="PASS", frontier=0, roots=len(ROOTS), minimum_reserve=str(least),
                 minimum_reserve_floor_1e12=str(F(scaled.numerator // scaled.denominator, 10**12)), by_root=by_root)
    return stats


def audit_discovery(discovery, limit=None):
    """Check candidate arithmetic only.  This mode never certifies root coverage."""
    least = None
    checked = 0
    empty = 0
    for leaf in discovery["leaves"]:
        if limit is not None and checked >= limit:
            break
        root, steps = _path_steps(leaf["path"])
        assert root == leaf["root"] and leaf["power"] == 40
        box, pose, choices = _follow_steps(root, steps)
        tag, reserve = interval_witness(box, pose)
        if tag is None:
            reserve = leaf_reserve(leaf["weights"], box, pose, choices)
        else:
            empty += 1
        least = reserve if least is None else min(least, reserve)
        checked += 1
        if checked % 1000 == 0:
            print("candidate exact leaves", checked, flush=True)
    return {"status": "PARTIAL_LEAF_ARITHMETIC_PASS", "whole_domain_proved": False,
            "candidate_leaves_checked": checked, "empty_interval_candidates": empty,
            "discovery_frontier_count": len(discovery["frontier"]),
            "minimum_reserve": str(least)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path, nargs="?")
    parser.add_argument("--pack-discovery", type=Path)
    parser.add_argument("--audit-discovery", type=Path)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    start = time.time()
    if args.audit_discovery:
        assert args.certificate is None and args.pack_discovery is None
        stats = audit_discovery(json.loads(args.audit_discovery.read_text()), args.limit)
        stats["discovery_sha256"] = hashlib.sha256(args.audit_discovery.read_bytes()).hexdigest()
    else:
        assert args.certificate is not None and args.limit is None
        if args.pack_discovery:
            data = pack(json.loads(args.pack_discovery.read_text()), args.certificate)
        else:
            with gzip.open(args.certificate, "rt") as handle:
                data = json.load(handle)
        stats = verify(data)
        stats["certificate_sha256"] = hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    stats["seconds"] = time.time() - start
    stats["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    helper = Path(__file__).with_name("weak_outer_hand_right_lower_verify.py")
    stats["exact_helper_sha256"] = hashlib.sha256(helper.read_bytes()).hexdigest()
    if args.report:
        args.report.write_text(json.dumps(stats, indent=2) + "\n")
    print(json.dumps(stats, indent=2))


if __name__ == "__main__":
    main()
