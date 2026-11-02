#!/usr/bin/env python3
"""Standalone exact dyadic replay of the joint five-square support dual.

No producer, Fraction evaluator, or shared interval package is imported.
The algebra follows the independently audited Fraction reduction, using
outward integer arithmetic with 64 fractional bits for speed. Every return
value used to accept a leaf is converted to an exact Fraction.

The general mapped_upper entry point also handles independently checked
owner-aware lower-dimensional parametrizations supplied by a caller.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import gzip
import hashlib
import json
import sys
import time

BITS = 64
SCALE = 1 << BITS
DIM = 4


def ceil_ratio(a, b):
    assert b > 0
    return -((-a) // b)


class I:
    """Closed interval; lo and hi are integer numerators over SCALE."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, I):
            assert hi is None
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, int) and (hi is None or isinstance(hi, int)):
            self.lo = lo * SCALE
            self.hi = (lo if hi is None else hi) * SCALE
        else:
            low = F(lo)
            high = low if hi is None else F(hi)
            self.lo = low.numerator * SCALE // low.denominator
            self.hi = ceil_ratio(high.numerator * SCALE, high.denominator)
        assert self.lo <= self.hi

    @classmethod
    def raw(cls, lo, hi):
        assert isinstance(lo, int) and isinstance(hi, int) and lo <= hi
        answer = object.__new__(cls)
        answer.lo, answer.hi = lo, hi
        return answer

    def __add__(self, other):
        if isinstance(other, int):
            n = other * SCALE
            return I.raw(self.lo + n, self.hi + n)
        other = other if isinstance(other, I) else I(other)
        return I.raw(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I.raw(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            a, b = self.lo * other, self.hi * other
            return I.raw(min(a, b), max(a, b))
        other = other if isinstance(other, I) else I(other)
        if self.lo == self.hi == 0 or other.lo == other.hi == 0:
            return I.raw(0, 0)
        candidates = (
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi,
        )
        return I.raw(min(candidates) // SCALE,
                     ceil_ratio(max(candidates), SCALE))

    __rmul__ = __mul__

    def __truediv__(self, other):
        if isinstance(other, int):
            assert other != 0
            if other < 0:
                return (-self) / (-other)
            return I.raw(self.lo // other, ceil_ratio(self.hi, other))
        other = other if isinstance(other, I) else I(other)
        assert other.lo > 0 or other.hi < 0
        if other.hi < 0:
            return (-self) / (-other)
        numerators = (self.lo * SCALE, self.hi * SCALE)
        low = min(a // b for a in numerators for b in (other.lo, other.hi))
        high = max(ceil_ratio(a, b) for a in numerators for b in (other.lo, other.hi))
        return I.raw(low, high)

    def __rtruediv__(self, other):
        return I(other) / self

    def sq(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        high = max(self.lo**2, self.hi**2)
        return I.raw(low // SCALE, ceil_ratio(high, SCALE))

    def abs(self):
        low = 0 if self.lo <= 0 <= self.hi else min(abs(self.lo), abs(self.hi))
        return I.raw(low, max(abs(self.lo), abs(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        low = isqrt(self.lo * SCALE)
        radicand = self.hi * SCALE
        high = isqrt(radicand)
        if high**2 < radicand:
            high += 1
        return I.raw(low, high)

    def fractions(self):
        return F(self.lo, SCALE), F(self.hi, SCALE)


def span(values):
    return I.raw(min(v.lo for v in values), max(v.hi for v in values))


def symmetric(value):
    high = max(abs(value.lo), abs(value.hi))
    return I.raw(-high, high)


def overlap(left, right):
    return I.raw(max(left.lo, right.lo), min(left.hi, right.hi))


def constant_zero(value):
    return value.lo == value.hi == 0


class A:
    """An interval value with four enclosures of partial derivatives."""

    __slots__ = ("x", "der")

    def __init__(self, value, der=None):
        self.x = I(value)
        self.der = ((I(0),) * DIM if der is None
                    else tuple(I(q) for q in der))
        assert len(self.der) == DIM

    def __add__(self, other):
        if not isinstance(other, A):
            return A(self.x + other, self.der)
        return A(self.x + other.x,
                 [p + q for p, q in zip(self.der, other.der)])

    __radd__ = __add__

    def __neg__(self):
        return A(-self.x, [-q for q in self.der])

    def __sub__(self, other):
        return self + -(other if isinstance(other, A) else A(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if not isinstance(other, A):
            return A(self.x * other, [q * other for q in self.der])
        return A(self.x * other.x,
                 [p * other.x + self.x * q
                  for p, q in zip(self.der, other.der)])

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, A):
            denominator = I(other)
            assert denominator.lo > 0
            return A(self.x / denominator,
                     [p / denominator for p in self.der])
        assert other.x.lo > 0
        return A(self.x / other.x,
                 [(p - self.x * q / other.x) / other.x
                  for p, q in zip(self.der, other.der)])

    def __rtruediv__(self, other):
        return A(other) / self

    def sq(self):
        return A(self.x.sq(), [2 * self.x * q for q in self.der])

    def absolute(self):
        if self.x.lo > 0:
            return self
        if self.x.hi < 0:
            return -self
        return A(self.x.abs(), [symmetric(q) for q in self.der])


def union(branches):
    return A(span([v.x for v in branches]),
             [span([v.der[j] for v in branches]) for j in range(DIM)])


def least(branches):
    low = min(v.x.lo for v in branches)
    high = min(v.x.hi for v in branches)
    active = [v for v in branches if v.x.lo <= high]
    return A(I.raw(low, high),
             [span([v.der[j] for v in active]) for j in range(DIM)])


def greatest(branches):
    return -least([-v for v in branches])


def length(vector):
    value = (vector[0].x.sq() + vector[1].x.sq()).sqrt()
    lips = [symmetric((vector[0].der[j].sq()
                       + vector[1].der[j].sq()).sqrt())
            for j in range(DIM)]
    if value.lo > 0:
        ders = [overlap((vector[0].x * vector[0].der[j]
                         + vector[1].x * vector[1].der[j]) / value,
                        lips[j]) for j in range(DIM)]
    else:
        ders = lips
    return A(value, ders)


def product(left, right):
    return left[0] * right[0] + left[1] * right[1]


def area(left, right):
    return left[0] * right[1] - left[1] * right[0]


def times(scalar, vector):
    return [scalar * vector[0], scalar * vector[1]]


def support(vector, axis):
    return (product(vector, axis).absolute()
            + area(vector, axis).absolute()) / (2 * length(axis))


def support_total(vectors, axis):
    return sum((support(v, axis) for v in vectors), A(0))


def orientation_min(vectors, endpoint=False):
    if endpoint:
        axes = [[A(1), A(F(-7, 100))], [A(1), A(F(7, 100))]]
    else:
        axes = [[A(1), A(0)]]
    boundaries = [support_total(vectors, axis) for axis in axes]
    candidates = list(boundaries)
    uncertain_zero = False
    for vector in vectors:
        vx, vy = vector[0].x, vector[1].x
        if constant_zero(vx) and constant_zero(vy):
            continue
        ux, uy = vx.abs(), vy.abs()
        if (endpoint and uy.lo > (F(7, 100) * ux).hi
                and ux.lo > (F(7, 100) * uy).hi):
            continue
        if constant_zero(vx):
            direction = [A(0), A(1)]
        elif constant_zero(vy):
            direction = [A(1), A(0)]
        else:
            direction = vector
        if length(direction).x.lo <= 0:
            uncertain_zero = True
        else:
            candidates.append(support_total(vectors, direction))
    high = min(v.x.hi for v in boundaries)
    low = 0 if uncertain_zero else min(v.x.lo for v in candidates)
    universal = sum((length(v).x for v in vectors), I(0)) / 2
    low = max(low, universal.lo)
    assert low <= high
    lips = []
    for j in range(DIM):
        bound = sum(((v[0].der[j].sq() + v[1].der[j].sq()).sqrt()
                     for v in vectors), I(0))
        lips.append(symmetric(bound))
    if uncertain_zero:
        ders = lips
    else:
        active = [v for v in candidates if v.x.lo <= high]
        ders = [overlap(span([v.der[j] for v in active]), lips[j])
                for j in range(DIM)]
    return A(I.raw(low, high), ders)


Q = F(1105, 256)
R = A(I(Q).sqrt())
CENTER_RADIUS = A(I(Q - F(1, 4)).sqrt() - F(1, 2))


def square_center_bound(vector, axis):
    denominator = length(axis)
    p = (product(vector, axis) / denominator).absolute()
    q = (area(vector, axis) / denominator).absolute()
    big, small = greatest([p, q]), least([p, q])
    edge = CENTER_RADIUS * big
    vertex = R * length(vector) - (big + small) / 2
    discriminator = big.sq() - (4 * Q - 1) * small.sq()
    if discriminator.x.lo >= 0:
        answer = edge
    elif discriminator.x.hi <= 0:
        answer = vertex
    else:
        answer = union([edge, vertex])
    magnitude = length(vector).x
    angle_denominator = 1 + axis[1].x.sq()
    ders = []
    for j in range(DIM):
        speed = (vector[0].der[j].sq() + vector[1].der[j].sq()).sqrt()
        turn = (axis[1].der[j] / angle_denominator).abs()
        bound = symmetric(CENTER_RADIUS.x * (speed + magnitude * turn))
        ders.append(overlap(answer.der[j], bound))
    return A(answer.x, ders)


def boxed_bound(vector, axis, box, weights):
    low_x, high_x, low_y, high_y = box
    lx, hx, ly, hy = weights
    moved = [vector[0] + lx - hx, vector[1] + ly - hy]
    return (square_center_bound(moved, axis)
            + hx * high_x - lx * low_x + hy * high_y - ly * low_y)


def unfixed_bound(vector, penalties, endpoint=False, box=None):
    cost = orientation_min(penalties, endpoint)
    vertex = R * length(vector) - orientation_min([*penalties, vector], endpoint)
    radial = CENTER_RADIUS * length(vector) - cost
    bounds = [vertex, radial]
    if box is not None:
        xl, xh, yl, yh = box
        rectangle = ((xl + xh) * vector[0] / 2
                     + (yl + yh) * vector[1] / 2
                     + (xh - xl) * vector[0].absolute() / 2
                     + (yh - yl) * vector[1].absolute() / 2)
        bounds.append(rectangle - cost)
    return least(bounds)


def evaluate_mapped(variables, certificate, owners, central_owned=False,
                    shoulder_central_owned=(False, False), central_owner_side=1):
    """Evaluate a dual whose four slopes are supplied as dual variables.

    The caller is responsible for proving its owner/parameter mapping.
    This function checks all numerical multipliers and evaluates the exact
    five-square formula, including a known central frame when requested.
    """
    assert len(variables) == 4 and owners in ("RR", "RE", "ER", "EE")
    assert len(shoulder_central_owned) == 2
    assert all(isinstance(flag, bool) for flag in shoulder_central_owned)
    assert all(not flag or owners[i] == "E" for i, flag in enumerate(shoulder_central_owned))
    assert central_owner_side in (0, 1)
    wl, wr, zl, zr = variables
    denominator = certificate["den"]
    assert denominator == 4096
    pars = certificate["p"]
    assert len(pars) == 7 and all(isinstance(k, int) and k >= 0 for k in pars)
    kl, kr, ml, mr, floor, ql, qr = [F(k, denominator) for k in pars]
    assert len(certificate["faces"]) == 2
    faces = []
    for row in certificate["faces"]:
        assert len(row) == 4 and all(isinstance(k, int) and k >= 0 for k in row)
        faces.append([F(k, denominator) for k in row])
    answer = A(F(27, 2) - floor / 10 + max(ql, qr) / 8 - F(211, 2))
    for i, w, z, k, mu, q in [(0, wl, zl, kl, ml, ql), (1, wr, zr, kr, mr, qr)]:
        sign = 1 if i else -1
        normal = [-sign * w, A(1)]
        central = [A(sign), z]
        endpoint_vector = [sign * (46 + k * w), A(q - k)]
        shoulder_vector = [sign * (mu - k * w), k + mu * z]
        axis = [A(1), sign * w]
        endpoint_costs = [[A(46), A(0)], times(k, normal)]
        shoulder_costs = [times(mu, central), times(k, normal)]
        endpoint_x = (F(89, 60), F(91, 60)) if i else (F(-91, 60), F(-89, 60))
        shoulder_x = (F(23, 30), F(13, 12)) if i else (F(-13, 12), F(-23, 30))
        endpoint_box = (*endpoint_x, F(-1, 8), F(1, 8))
        shoulder_box = (*shoulder_x, F(25, 32), F(21, 16))
        if owners[i] == "E":
            endpoint = (boxed_bound(endpoint_vector, axis, endpoint_box, faces[i])
                        - support_total(endpoint_costs, axis))
            if shoulder_central_owned[i]:
                central_faces = certificate["central_shoulder_faces"]
                assert len(central_faces) == 2
                weights = central_faces[i]
                assert len(weights) == 4 and all(isinstance(q, int) and q >= 0 for q in weights)
                central_axis = [A(1), sign * z]
                shoulder = (boxed_bound(shoulder_vector, central_axis, shoulder_box,
                                        [F(q, denominator) for q in weights])
                            - support_total(shoulder_costs, central_axis))
            else:
                shoulder = unfixed_bound(shoulder_vector, shoulder_costs, box=shoulder_box)
        else:
            endpoint = unfixed_bound(endpoint_vector, endpoint_costs, True, endpoint_box)
            shoulder = (boxed_bound(shoulder_vector, axis, shoulder_box, faces[i])
                        - support_total(shoulder_costs, axis))
        answer = answer + endpoint + shoulder
    center = [A(ml - mr), floor - ml * zl - mr * zr]
    costs = [[A(-ml), ml * zl], [A(mr), mr * zr], [A(0), A(floor)]]
    center_box = (F(-29, 60), F(29, 60), F(3, 5), F(91, 60))
    if central_owned:
        weights = certificate["central_faces"]
        assert len(weights) == 4 and all(isinstance(k, int) and k >= 0 for k in weights)
        axis = [A(1), zr if central_owner_side == 1 else -zl]
        center_bound = (boxed_bound(center, axis, center_box,
                                   [F(k, denominator) for k in weights])
                        - support_total(costs, axis))
    else:
        center_bound = unfixed_bound(center, costs, box=center_box)
    return answer + center_bound


def independent_variables(box):
    dimensions = len(box) // 2
    assert len(box) == 2 * dimensions and 1 <= dimensions <= DIM
    variables = []
    for j in range(dimensions):
        gradient = [0] * DIM
        gradient[j] = 1
        variables.append(A(I(box[2*j], box[2*j+1]), gradient))
    return variables


def evaluate(box, certificate, owners):
    assert len(box) == 8
    return evaluate_mapped(independent_variables(box), certificate, owners)


def mapped_upper(box, certificate, owners, mapping, central_owned=False,
                 shoulder_central_owned=(False, False), central_owner_side=1):
    """Exact Fraction ceiling for a 1--4 dimensional mapped parameter box."""
    box = tuple(map(F, box))
    dimensions = len(box) // 2
    full = evaluate_mapped(mapping(independent_variables(box)), certificate,
                           owners, central_owned, shoulder_central_owned,
                           central_owner_side)
    mids = [(box[2*j] + box[2*j+1]) / 2 for j in range(dimensions)]
    point = tuple(t for middle in mids for t in (middle, middle))
    at = evaluate_mapped(mapping(independent_variables(point)), certificate,
                         owners, central_owned, shoulder_central_owned,
                         central_owner_side).x
    for j, middle in enumerate(mids):
        at = at + full.der[j] * I(box[2*j] - middle, box[2*j+1] - middle)
    return F(min(full.x.hi, at.hi), SCALE)


def upper(box, certificate, owners):
    assert len(box) == 8
    return mapped_upper(box, certificate, owners, lambda variables: variables)


def initial_roots(owner):
    domains = [(F(-2, 3), F(6)) if letter == "R" else (F(-1, 14), F(1, 14))
               for letter in owner] + [(F(-6), F(6))] * 2
    epsilon = F(1, 64)
    roots = []
    for j in range(4):
        for cut in [(domains[j][0], -epsilon), (epsilon, domains[j][1])]:
            root = []
            for i in range(4):
                root.extend((-epsilon, epsilon) if i < j else cut if i == j else domains[i])
            roots.append(tuple(root))
    return roots


def verify(data, allow_incomplete=False, progress=False):
    assert data["type"] == "joint_five_interval_cover_v2"
    owner = data["owner"]
    assert owner in ("RR", "RE", "EE")
    assert data["Q"] == "1105/256" and data["T_twice"] == "211/2"
    assert data["central_slope_band"] == ["-6", "6"]
    assert data["central_x_band"] == ["-29/60", "29/60"]
    assert data["sharp_cube_epsilon"] == "1/64" and data["roots"] == list(range(8))
    nodes, certificates = data["nodes"], data["certificates"]
    pending = list(zip(range(8), initial_roots(owner)))
    seen = set()
    interval_leaves = analytic_leaves = missing = 0
    largest = None
    started = last = time.monotonic()
    while pending:
        index, expected = pending.pop()
        assert isinstance(index, int) and index not in seen and 0 <= index < len(nodes)
        seen.add(index)
        node = nodes[index]
        box = tuple(map(F, node["box"]))
        assert box == expected
        if "children" in node:
            assert "certificate" not in node and "terminal" not in node
            dimension = node["split"]
            assert isinstance(dimension, int) and 0 <= dimension < 4
            children = node["children"]
            assert len(children) == 2 and children[0] != children[1]
            middle = (box[2*dimension] + box[2*dimension+1]) / 2
            left, right = list(box), list(box)
            left[2*dimension+1], right[2*dimension] = middle, middle
            pending.extend([(children[0], tuple(left)), (children[1], tuple(right))])
        elif "terminal" in node:
            assert node["terminal"] == "positive_joint_triangle" and "certificate" not in node
            assert box[4] >= 0 and box[6] >= 0
            left, right = box[5], box[7]
            assert max(left, right)**2 + 2*left*right <= 1
            analytic_leaves += 1
        elif "certificate" in node:
            identifier = node["certificate"]
            assert isinstance(identifier, int) and 0 <= identifier < len(certificates)
            ceiling = upper(box, certificates[identifier], owner)
            assert ceiling < 0, (owner, index, str(ceiling), box)
            if "upper" in node:
                assert F(node["upper"]) < 0
            largest = ceiling if largest is None else max(largest, ceiling)
            interval_leaves += 1
        else:
            assert allow_incomplete, "unclosed leaf"
            missing += 1
        now = time.monotonic()
        if progress and now - last > 25:
            print("DYADIC REPLAY", owner, "interval", interval_leaves,
                  "analytic", analytic_leaves, "missing", missing,
                  "seconds", round(now - started, 1), flush=True)
            last = now
    assert len(seen) == len(nodes)
    assert interval_leaves + analytic_leaves == data["closed"]
    if not allow_incomplete:
        assert missing == 0 and data["remaining"] == 0
        assert data["proof_status"] == "producer_complete_pending_independent_replay"
    return {"owner": owner, "interval_leaves": interval_leaves,
            "analytic_leaves": analytic_leaves, "unclosed_leaves": missing,
            "largest_replayed_upper": None if largest is None else str(largest),
            "complete": missing == 0}


def main():
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    data = json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)
    report = verify(data, "--allow-incomplete" in sys.argv, True)
    report["sha256"] = hashlib.sha256(raw).hexdigest()
    report["arithmetic"] = "standalone 64-bit directed integer intervals; exact rational coverage"
    report["evaluator_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["proof_status"] = ("independent_cover_replay_passed" if report["complete"]
                              else "incomplete_checkpoint_leaves_replayed")
    output = path.with_name(path.stem + "_dyadic_replay.json")
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
