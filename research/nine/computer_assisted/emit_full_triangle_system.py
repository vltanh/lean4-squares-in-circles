#!/usr/bin/env python3
"""Exact full-physical nine-square unloaded-triangle constraint emitter.

Emits QF_NRA SMT-LIB with rational constants; runs no solver and claims no
exclusion. Standard library only. See FULL_PHYSICAL_TRIANGLE_SYSTEM_2026_11_01.md.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from typing import Any


Q = F(1105, 256)
HALF = F(1, 2)
SIGNS = ((-1, -1), (-1, 1), (1, -1), (1, 1))
EXIT_CASES = {
    "AAA": (3, 3, 3),
    "AAB": (3, 3, 4),
    "ABA": (3, 4, 3),
    "ABB": (3, 4, 4),
    "ABC": (3, 4, 5),
}


@dataclass(frozen=True)
class E:
    op: str
    args: tuple[Any, ...]


def scalar(x: Any) -> E:
    return x if isinstance(x, E) else E("num", (F(x),))


def expr(op: str, *xs: Any) -> E:
    return E(op, tuple(scalar(x) for x in xs))


def add(*xs: Any) -> E:
    return expr("+", *xs) if xs else scalar(0)


def mul(*xs: Any) -> E:
    return expr("*", *xs) if xs else scalar(1)


def sub(x: Any, y: Any) -> E:
    return expr("-", x, y)


def neg(x: Any) -> E:
    return expr("-", x)


def eq(x: Any, y: Any) -> E:
    return expr("=", x, y)


def le(x: Any, y: Any) -> E:
    return expr("<=", x, y)


def lt(x: Any, y: Any) -> E:
    return expr("<", x, y)


def conjunction(*xs: E) -> E:
    return E("and", tuple(xs))


def disjunction(*xs: E) -> E:
    return E("or", tuple(xs))


def absolute(x: Any) -> E:
    x = scalar(x)
    return E("ite", (le(0, x), x, neg(x)))


def minimum(x: Any, y: Any) -> E:
    x, y = scalar(x), scalar(y)
    return E("ite", (le(x, y), x, y))


def maximum(x: Any, y: Any) -> E:
    x, y = scalar(x), scalar(y)
    return E("ite", (le(x, y), y, x))


def nonzero(x: Any) -> E:
    return disjunction(lt(x, 0), lt(0, x))


def dot(x: tuple, y: tuple) -> E:
    return add(mul(x[0], y[0]), mul(x[1], y[1]))


def rot(x: tuple) -> tuple:
    return neg(x[1]), scalar(x[0])


def vadd(x: tuple, y: tuple) -> tuple:
    return add(x[0], y[0]), add(x[1], y[1])


def vsub(x: tuple, y: tuple) -> tuple:
    return sub(x[0], y[0]), sub(x[1], y[1])


def vscale(a: Any, x: tuple) -> tuple:
    return mul(a, x[0]), mul(a, x[1])


def render(x: E) -> str:
    if x.op == "var":
        return x.args[0]
    if x.op == "num":
        q = x.args[0]
        positive = (str(abs(q.numerator)) if q.denominator == 1 else
                    f"(/ {abs(q.numerator)} {q.denominator})")
        return f"(- {positive})" if q < 0 else positive
    if x.op == "and" and not x.args:
        return "true"
    if x.op == "or" and not x.args:
        return "false"
    return "(" + x.op + " " + " ".join(map(render, x.args)) + ")"


def evaluate(x: E, env: dict[str, F]) -> F | bool:
    if x.op == "var":
        return env[x.args[0]]
    if x.op == "num":
        return x.args[0]
    if x.op == "and":
        return all(evaluate(y, env) for y in x.args)
    if x.op == "or":
        return any(evaluate(y, env) for y in x.args)
    if x.op == "=>":
        return not evaluate(x.args[0], env) or bool(evaluate(x.args[1], env))
    if x.op == "ite":
        return evaluate(x.args[1] if evaluate(x.args[0], env) else x.args[2], env)
    values = [evaluate(y, env) for y in x.args]
    if x.op == "+":
        return sum(values, F(0))
    if x.op == "*":
        answer = F(1)
        for y in values:
            answer *= y
        return answer
    if x.op == "-":
        return -values[0] if len(values) == 1 else values[0] - values[1]
    if x.op == "=":
        return values[0] == values[1]
    if x.op == "<=":
        return values[0] <= values[1]
    if x.op == "<":
        return values[0] < values[1]
    raise ValueError(f"Unknown expression operator {x.op}")


@dataclass
class System:
    variables: list[str] = field(default_factory=list)
    definitions: list[tuple[str, E]] = field(default_factory=list)
    assertions: list[tuple[str, E]] = field(default_factory=list)
    names: set[str] = field(default_factory=set)

    def reserve(self, name: str) -> None:
        assert name not in self.names, name
        self.names.add(name)

    def var(self, name: str) -> E:
        self.reserve(name)
        self.variables.append(name)
        return E("var", (name,))

    def define(self, name: str, value: E) -> E:
        self.reserve(name)
        self.definitions.append((name, value))
        return E("var", (name,))

    def require(self, name: str, value: E) -> None:
        self.reserve(name)
        self.assertions.append((name, value))

    def failures(self, assignment: dict[str, F]) -> list[str]:
        env = {name: F(assignment[name]) for name in self.variables}
        for name, value in self.definitions:
            env[name] = evaluate(value, env)
        return [name for name, value in self.assertions if not evaluate(value, env)]

    def smt2(self, case: str | None, weak_screen: bool) -> str:
        rows = [
            "; Full physical nine-square stress system. No exclusion is claimed.",
            f"; Exit case: {case or 'none'}; analytic weak-edge screen: {weak_screen}",
            "; All constants and arithmetic constraints are exact.",
            "(set-logic QF_NRA)",
        ]
        rows += [f"(declare-fun {name} () Real)" for name in self.variables]
        rows += [f"(define-fun {name} () Real {render(value)})"
                 for name, value in self.definitions]
        rows += [f"(assert (! {render(value)} :named {name}))"
                 for name, value in self.assertions]
        rows += ["(check-sat)", ""]
        return "\n".join(rows)


@dataclass
class Square:
    c: tuple
    u: tuple
    v: tuple
    corners: list[tuple]
    lambdas: list[E]


@dataclass
class Pair:
    i: int
    j: int
    mu: E
    n: tuple
    p: tuple
    eta: E
    contact: E


def halfwidth(s: Square, n: tuple) -> E:
    return mul(HALF, add(absolute(dot(n, s.u)), absolute(dot(n, s.v))))


def make_contact(a: Square, b: Square, n: tuple, p: tuple, eta: E) -> E:
    """Actual same point/support, strict singleton choice, or full side mean."""
    ra, rb = vsub(p, a.c), vsub(p, b.c)
    t = rot(n)
    ta, tb = dot(t, a.c), dot(t, b.c)
    lo = sub(maximum(ta, tb), HALF)
    hi = add(minimum(ta, tb), HALF)
    ai, bi = dot(n, a.u), dot(n, a.v)
    aj, bj = dot(n, b.u), dot(n, b.v)
    strict_a = conjunction(nonzero(ai), nonzero(bi))
    strict_b = conjunction(nonzero(aj), nonzero(bj))
    side_a = disjunction(eq(ai, 0), eq(bi, 0))
    side_b = disjunction(eq(aj, 0), eq(bj, 0))
    interior_a = lt(absolute(dot(t, ra)), HALF)
    interior_b = lt(absolute(dot(t, rb)), HALF)
    # At a singleton vertex/vertex contact both exposed vertices must be strict.
    vv = conjunction(strict_a, strict_b)
    ve = conjunction(side_a, strict_b, interior_a)
    ev = conjunction(strict_a, side_b, interior_b)
    # This permits every true weighted mean, including either endpoint.
    ss = conjunction(
        side_a, side_b, lt(lo, hi), le(0, eta), le(eta, 1),
        eq(dot(t, p), add(mul(sub(1, eta), lo), mul(eta, hi))),
    )
    return conjunction(
        eq(dot(n, n), 1),
        le(absolute(dot(ra, a.u)), HALF),
        le(absolute(dot(ra, a.v)), HALF),
        le(absolute(dot(rb, b.u)), HALF),
        le(absolute(dot(rb, b.v)), HALF),
        eq(dot(n, ra), halfwidth(a, n)),
        eq(dot(n, rb), neg(halfwidth(b, n))),
        disjunction(vv, ve, ev, ss),
    )


def build(case: str | None = "AAA", weak_screen: bool = False,
          gauge: bool = True) -> tuple[System, list[Square], dict[tuple, Pair]]:
    if case is not None and case not in EXIT_CASES:
        raise ValueError(case)
    if weak_screen and case is None:
        raise ValueError("The analytic weak-edge screen requires a triangle case")
    sys = System()
    q = sys.var("q")
    sys.require("radius_lower", le(0, q))
    sys.require("radius_upper", le(q, Q))
    squares = []
    for i in range(9):
        c = sys.var(f"cx_{i}"), sys.var(f"cy_{i}")
        u = sys.var(f"ux_{i}"), sys.var(f"uy_{i}")
        v = rot(u)
        sys.require(f"frame_unit_{i}", eq(dot(u, u), 1))
        corners, lambdas = [], []
        for k, (sx, sy) in enumerate(SIGNS):
            raw = vadd(c, vscale(HALF, vadd(vscale(sx, u), vscale(sy, v))))
            p = (sys.define(f"corner_x_{i}_{k}", raw[0]),
                 sys.define(f"corner_y_{i}_{k}", raw[1]))
            lam = sys.var(f"lambda_{i}_{k}")
            margin = sys.define(f"circle_margin_{i}_{k}", sub(dot(p, p), q))
            sys.require(f"corner_contained_{i}_{k}", le(margin, 0))
            sys.require(f"circle_weight_nonnegative_{i}_{k}", le(0, lam))
            sys.require(f"circle_complementarity_{i}_{k}", eq(mul(lam, margin), 0))
            corners.append(p)
            lambdas.append(lam)
        squares.append(Square(c, u, v, corners, lambdas))
    if gauge:
        sys.require("rotation_gauge_x", eq(squares[0].u[0], 1))
        sys.require("rotation_gauge_y", eq(squares[0].u[1], 0))
    sys.require("circle_weight_normalization", eq(add(
        *(lam for s in squares for lam in s.lambdas)), 1))
    pairs = {}
    for i, j in combinations(range(9), 2):
        a, b = squares[i], squares[j]
        displacement = vsub(b.c, a.c)
        # Four unoriented SAT axes = all eight directed side-axis separators.
        sys.require(f"sat_{i}_{j}", disjunction(*(
            le(add(halfwidth(a, axis), halfwidth(b, axis)),
               absolute(dot(axis, displacement)))
            for axis in (a.u, a.v, b.u, b.v))))
        mu = sys.var(f"mu_{i}_{j}")
        n = sys.var(f"nx_{i}_{j}"), sys.var(f"ny_{i}_{j}")
        p = sys.var(f"px_{i}_{j}"), sys.var(f"py_{i}_{j}")
        eta = sys.var(f"eta_{i}_{j}")
        contact = make_contact(a, b, n, p, eta)
        sys.require(f"pair_weight_nonnegative_{i}_{j}", le(0, mu))
        sys.require(f"positive_contact_{i}_{j}", E("=>", (lt(0, mu), contact)))
        pairs[i, j] = Pair(i, j, mu, n, p, eta, contact)
    for i, s in enumerate(squares):
        fx, fy, torque = [], [], []
        for p, lam in zip(s.corners, s.lambdas):
            fx.append(mul(2, lam, p[0]))
            fy.append(mul(2, lam, p[1]))
            torque.append(mul(2, lam, dot(p, rot(vsub(p, s.c)))))
        for (a, b), edge in pairs.items():
            if i not in (a, b):
                continue
            sign = 1 if i == a else -1
            fx.append(mul(sign, edge.mu, edge.n[0]))
            fy.append(mul(sign, edge.mu, edge.n[1]))
            torque.append(mul(sign, edge.mu, dot(edge.n, rot(vsub(edge.p, s.c)))))
        sys.require(f"force_x_{i}", eq(add(*fx), 0))
        sys.require(f"force_y_{i}", eq(add(*fy), 0))
        sys.require(f"torque_{i}", eq(add(*torque), 0))
    if case is not None:
        for i, j in ((0, 1), (1, 2), (0, 2)):
            sys.require(f"triangle_positive_{i}_{j}", lt(0, pairs[i, j].mu))
        for i, target in enumerate(EXIT_CASES[case]):
            for k, lam in enumerate(squares[i].lambdas):
                sys.require(f"hub_unloaded_{i}_{k}", eq(lam, 0))
            for j in range(3, 9):
                edge = pairs[i, j]
                sys.require(f"hub_exit_{i}_{j}",
                            lt(0, edge.mu) if j == target else eq(edge.mu, 0))
    if weak_screen:
        s3 = sys.var("positive_sqrt3")
        sys.require("sqrt3_positive", lt(0, s3))
        sys.require("sqrt3_square", eq(mul(s3, s3), 3))
        internal = [pairs[0, 1].mu, pairs[1, 2].mu, pairs[0, 2].mu]
        rhs = mul(add(4, mul(2, s3)), add(*internal))
        sys.require("analytic_weak_edge", disjunction(*(
            lt(mul(93, weight), rhs) for weight in internal)))
    return sys, squares, pairs


def rational_record_witness(sys: System) -> dict[str, F]:
    """Committed oblique nine-square Q witness; not a direct-triangle witness.

    Data source: ../check_physical_contact_stress.py at ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91.
    """
    assignment = {name: F(0) for name in sys.variables}
    assignment["q"] = Q
    centers = ([(F(x, 2), F(1, 16)) for x in (-3, -1, 1, 3)]
               + [(F(x), -F(15, 16)) for x in (-1, 0, 1)]
               + [(F(x, 20), F(19, 16)) for x in (-11, 11)])
    for i, (cx, cy) in enumerate(centers):
        assignment[f"cx_{i}"], assignment[f"cy_{i}"] = cx, cy
        assignment[f"ux_{i}"] = F(1) if i < 7 else F(99, 101)
        assignment[f"uy_{i}"] = F(0) if i < 7 else F(20, 101)
    for i, k, lam in ((0, 1, F(23, 64)), (3, 3, F(23, 64)),
                      (4, 0, F(9, 64)), (6, 2, F(9, 64))):
        assignment[f"lambda_{i}_{k}"] = lam
    edges = [(i, i + 1, (F(1), F(0)), F(23, 16),
              (centers[i + 1][0] - HALF, F(45, 128))) for i in range(3)]
    edges += [
        (4, 5, (F(1), F(0)), F(27, 64), (-HALF, -F(115, 96))),
        (5, 6, (F(1), F(0)), F(27, 64), (HALF, -F(115, 96))),
        (0, 4, (F(0), -F(1)), F(207, 512), (-F(5, 4), -F(7, 16))),
        (3, 6, (F(0), -F(1)), F(207, 512), (F(5, 4), -F(7, 16))),
    ]
    for i, j, n, mu, p in edges:
        for prefix, val in (("mu", mu), ("nx", n[0]), ("ny", n[1]),
                            ("px", p[0]), ("py", p[1])):
            assignment[f"{prefix}_{i}_{j}"] = val
        t = -n[1], n[0]
        ta = sum(t[k] * centers[i][k] for k in range(2))
        tb = sum(t[k] * centers[j][k] for k in range(2))
        lo, hi = max(ta, tb) - HALF, min(ta, tb) + HALF
        tp = sum(t[k] * p[k] for k in range(2))
        assignment[f"eta_{i}_{j}"] = (tp - lo) / (hi - lo)
    return assignment


def self_check() -> None:
    sys, squares, pairs = build(None)
    witness = rational_record_witness(sys)
    failures = sys.failures(witness)
    assert not failures, failures
    assert len(pairs) == 36
    assert len([name for name, _ in sys.assertions if name.startswith("sat_")]) == 36
    # Moving an original shared mean along its real segment preserves contact
    # and translation, but must fail both affected original torque equations.
    shifted = witness.copy()
    shifted["py_0_1"] += F(1, 1000)
    shifted["eta_0_1"] += F(1, 1000)
    assert set(sys.failures(shifted)) == {"torque_0", "torque_1"}
    # The two entirely unstressed oblique squares still constrain every SAT.
    overlapped = witness.copy()
    overlapped["cx_8"], overlapped["cy_8"] = witness["cx_7"], witness["cy_7"]
    assert "sat_7_8" in sys.failures(overlapped)
    # A genuine singleton corner/corner contact admits a strict free normal.
    local = witness.copy()
    local.update({"cx_0": F(0), "cy_0": F(0), "cx_1": F(1), "cy_1": F(1),
                  "px_0_1": HALF, "py_0_1": HALF,
                  "nx_0_1": F(3, 5), "ny_0_1": F(4, 5)})
    assert evaluate(pairs[0, 1].contact, local)
    # A boundary normal at that same singleton is not silently accepted.
    local["nx_0_1"], local["ny_0_1"] = F(1), F(0)
    assert not evaluate(pairs[0, 1].contact, local)
    # The upper-bound packing is not a witness for an unloaded triangle.
    for case in EXIT_CASES:
        target, _, _ = build(case)
        assert any(name.startswith("triangle_positive_")
                   for name in target.failures(witness))
    print("Exact self-check passed: known Q witness, all 36 SATs, original shared-mean torque,")
    print("unstressed-square obstacle, strict singleton normal, and five distinct exit roots.")
    print(f"Base model: {len(sys.variables)} real variables, {len(sys.definitions)} definitions,")
    print(f"{len(sys.assertions)} assertions. No solver or exclusion claim.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=tuple(EXIT_CASES) + ("none",), default="AAA")
    parser.add_argument("--weak-screen", action="store_true",
                        help="Add the analytically proved algebraic weak-edge restriction")
    parser.add_argument("--ungauged", action="store_true")
    parser.add_argument("--output", type=Path, help="Write one SMT-LIB file instead of stdout")
    parser.add_argument("--all-cases", type=Path, metavar="DIRECTORY",
                        help="Write all five exhaustive exit-identity roots")
    parser.add_argument("--self-check", action="store_true")
    args = parser.parse_args()
    if args.self_check:
        self_check()
        return
    if args.all_cases is not None:
        args.all_cases.mkdir(parents=True, exist_ok=True)
        for case in EXIT_CASES:
            sys, _, _ = build(case, args.weak_screen, not args.ungauged)
            path = args.all_cases / f"triangle_{case}.smt2"
            path.write_text(sys.smt2(case, args.weak_screen))
            print(path)
        return
    case = None if args.case == "none" else args.case
    sys, _, _ = build(case, args.weak_screen, not args.ungauged)
    content = sys.smt2(case, args.weak_screen)
    if args.output is None:
        print(content, end="")
    else:
        args.output.write_text(content)
        print(args.output)


if __name__ == "__main__":
    main()
