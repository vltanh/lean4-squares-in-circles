#!/usr/bin/env python3
"""Exploratory seven-body LSLSLSS stress; not an interval certificate."""

import argparse
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    mp.mp.dps = 80
    one = mp.mpf(1)
    half = one / 2
    root2 = mp.sqrt(2)

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b))

    def cross(a, b):
        return a[0] * b[1] - a[1] * b[0]

    def add(a, b):
        return tuple(x + y for x, y in zip(a, b))

    def scale(t, a):
        return tuple(t * x for x in a)

    def reflect(a):
        return (-a[0], a[1])

    def parameters(theta):
        c, s = mp.cos(theta), mp.sin(theta)
        r = (1 + (c + s) / 2) / c
        radius = mp.sqrt((r + half) ** 2 + half ** 2)
        return c, s, r, radius

    def equation(theta):
        c, s, r, radius = parameters(theta)
        return radius - (2 * root2 + c - r * (c + s))

    theta = mp.findroot(equation, (mp.mpf(".10"), mp.mpf(".11")))
    c, s, r, radius = parameters(theta)
    e, f = (c, s), (-s, c)
    center_a = scale(-r, e)
    a = [add(center_a, add(scale(i / 2, e), scale(j / 2, f)))
         for i, j in [(-one, -one), (-one, one), (one, one), (one, -one)]]
    b = list(map(reflect, a))
    top = [(0, radius), (one / root2, radius - one / root2),
           (0, radius - root2), (-one / root2, radius - one / root2)]
    p, q = a[2], a[3]
    n, tangent = (one / root2, one / root2), (-one / root2, one / root2)
    left_s = [add(p, add(scale(i, n), scale(j, tangent)))
              for i, j in [(0, -half), (1, -half), (1, half), (0, half)]]
    right_s = list(map(reflect, left_s))
    left_ss = [(-1, -mp.mpf("1.5")), (0, -mp.mpf("1.5")),
               (0, -half), (-1, -half)]
    right_ss = [add(x, (1, 0)) for x in left_ss]
    bodies = {"A": a, "B": b, "C": top, "U": left_ss, "V": right_ss,
              "S": left_s, "T": right_s}

    mu = (p[1] - p[0]) / (-root2 * q[1])
    g_a = add((-mu, 0), scale(-1, n))
    z0, z1 = a[0], a[1]
    circle_a = mp.lu_solve(mp.matrix([[z0[0], z1[0]], [z0[1], z1[1]]]),
                           mp.matrix(g_a))
    circle_c = root2 / radius

    # A contact record gives the force applied to its first body; the
    # second receives the opposite force at the same physical point.
    contacts = [
        ("A", "U", q, (-mu, 0)),
        ("U", "V", (0, q[1]), (-mu, 0)),
        ("V", "B", reflect(q), (-mu, 0)),
        ("A", "S", p, scale(-1, n)),
        ("S", "C", add(p, n), scale(-1, n)),
        ("B", "T", reflect(p), reflect(scale(-1, n))),
        ("T", "C", reflect(add(p, n)), reflect(scale(-1, n))),
    ]
    circles = [("A", z0, circle_a[0]), ("A", z1, circle_a[1]),
               ("B", reflect(z0), circle_a[0]),
               ("B", reflect(z1), circle_a[1]),
               ("C", top[0], circle_c)]
    force = {k: (mp.mpf(0), mp.mpf(0)) for k in bodies}
    torque = {k: mp.mpf(0) for k in bodies}
    for first, second, point, value in contacts:
        force[first] = add(force[first], value)
        force[second] = add(force[second], scale(-1, value))
        torque[first] += cross(point, value)
        torque[second] -= cross(point, value)
    for name, point, weight in circles:
        force[name] = add(force[name], scale(-weight, point))

    def sat(first, second):
        gaps = []
        for polygon in (first, second):
            for i in range(4):
                edge = add(polygon[(i + 1) % 4], scale(-1, polygon[i]))
                length = mp.sqrt(dot(edge, edge))
                axis = (-edge[1] / length, edge[0] / length)
                aa, bb = [dot(x, axis) for x in first], [dot(x, axis) for x in second]
                gaps.extend((min(aa) - max(bb), min(bb) - max(aa)))
        return max(gaps)

    def membership(point, polygon):
        base = polygon[0]
        v = add(point, scale(-1, base))
        edges = [add(polygon[i], scale(-1, base)) for i in (1, 3)]
        coordinates = [dot(v, edge) for edge in edges]
        return min(coordinates + [1 - x for x in coordinates])

    def string(value):
        return mp.nstr(value, 65)

    edge_set = {frozenset((a, b)) for a, b, _, _ in contacts}
    gaps = []
    names = list(bodies)
    for i, first in enumerate(names):
        for second in names[:i]:
            gaps.append({"bodies": [first, second],
                         "positive_edge": frozenset((first, second)) in edge_set,
                         "sat_margin": string(sat(bodies[first], bodies[second]))})
    contact_records = []
    for first, second, point, value in contacts:
        magnitude = mp.sqrt(dot(value, value))
        inward = scale(1 / magnitude, value)
        first_support = min(dot(add(x, scale(-1, point)), inward) for x in bodies[first])
        second_support = min(dot(add(point, scale(-1, x)), inward) for x in bodies[second])
        contact_records.append({"bodies": [first, second], "point": list(map(string, point)),
                                "force_on_first": list(map(string, value)),
                                "membership_margins": [string(membership(point, bodies[first])),
                                                       string(membership(point, bodies[second]))],
                                "support_margins": list(map(string, (first_support, second_support)))})
    data = {
        "status": "exploratory numerical positive-stress realization; not an interval or exact existence certificate",
        "signature": "C20-M07-L03-B02-T01 LSLSLSS",
        "precision_decimal_digits": mp.mp.dps,
        "theta": string(theta), "radius": string(radius), "radius_squared": string(radius ** 2),
        "equation_residual": string(equation(theta)),
        "ss_force_over_s_force": string(mu),
        "circle_coefficients_A_and_B": list(map(string, circle_a)),
        "circle_coefficient_C": string(circle_c),
        "bodies": {name: {"vertices": [list(map(string, v)) for v in polygon],
                           "center": [string(sum(v[j] for v in polygon) / 4) for j in (0, 1)],
                           "circle_slack": string(radius ** 2 - max(dot(v, v) for v in polygon)),
                           "force_residual": list(map(string, force[name])),
                           "torque_residual": string(torque[name])}
                   for name, polygon in bodies.items()},
        "contacts": contact_records, "pairwise_sat": gaps,
    }
    encoded = json.dumps(data, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded, end="")
    nonedges = [mp.mpf(x["sat_margin"]) for x in gaps if not x["positive_edge"]]
    residual = max([abs(equation(theta))] + [abs(x) for v in force.values() for x in v]
                   + [abs(x) for x in torque.values()])
    print("R =", mp.nstr(radius, 22), "; R^2 =", mp.nstr(radius ** 2, 22))
    print("Maximum equation/force/torque residual:", mp.nstr(residual, 5))
    print("Minimum nonedge SAT gap:", mp.nstr(min(nonedges), 10))


if __name__ == "__main__":
    main()
