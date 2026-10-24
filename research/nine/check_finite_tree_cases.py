#!/usr/bin/env python3
"""Exact finite regressions for TREE.F1/F2 and TREE.12/TREE.04.

Not a universal proof or Lean certificate. Arithmetic is in Q(sqrt(2));
no floats, numerical optimizer, external packages or angle-grid proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import platform
from datetime import datetime, timezone


@dataclass(frozen=True)
class Q2:
    a: F = F(0)
    b: F = F(0)

    def __post_init__(self) -> None:
        object.__setattr__(self, "a", F(self.a))
        object.__setattr__(self, "b", F(self.b))

    @staticmethod
    def of(x: Q2 | F | int) -> Q2:
        return x if isinstance(x, Q2) else Q2(F(x))

    def __add__(self, other: Q2 | F | int) -> Q2:
        y = Q2.of(other)
        return Q2(self.a + y.a, self.b + y.b)

    __radd__ = __add__

    def __neg__(self) -> Q2:
        return Q2(-self.a, -self.b)

    def __sub__(self, other: Q2 | F | int) -> Q2:
        return self + (-Q2.of(other))

    def __rsub__(self, other: Q2 | F | int) -> Q2:
        return Q2.of(other) - self

    def __mul__(self, other: Q2 | F | int) -> Q2:
        y = Q2.of(other)
        return Q2(self.a*y.a + 2*self.b*y.b, self.a*y.b + self.b*y.a)

    __rmul__ = __mul__

    def __truediv__(self, other: Q2 | F | int) -> Q2:
        y = Q2.of(other)
        den = y.a*y.a - 2*y.b*y.b
        if den == 0:
            raise ZeroDivisionError("zero Q(sqrt(2)) denominator")
        return self * Q2(y.a/den, -y.b/den)

    def sign(self) -> int:
        if not self.b:
            return (self.a > 0) - (self.a < 0)
        if not self.a:
            return (self.b > 0) - (self.b < 0)
        if (self.a > 0) == (self.b > 0):
            return 1 if self.a > 0 else -1
        delta = self.a*self.a - 2*self.b*self.b
        if delta == 0:
            return 0
        return ((self.a > 0) - (self.a < 0)) * ((delta > 0) - (delta < 0))

    def __abs__(self) -> Q2:
        return self if self.sign() >= 0 else -self

    def text(self) -> str:
        return str(self.a) if not self.b else f"({self.a})+({self.b})*sqrt(2)"


V = tuple[Q2, Q2]
ZERO = Q2()
HALF = F(1, 2)
SQRT2 = Q2(0, 1)
W = SQRT2 / 2
Q0 = Q2(F(17, 4))
QSTAR = F(1105, 256)


def vec(x: Q2 | F | int, y: Q2 | F | int) -> V:
    return Q2.of(x), Q2.of(y)


def add(x: V, y: V) -> V:
    return x[0]+y[0], x[1]+y[1]


def sub(x: V, y: V) -> V:
    return x[0]-y[0], x[1]-y[1]


def mul(a: Q2 | F | int, x: V) -> V:
    return Q2.of(a)*x[0], Q2.of(a)*x[1]


def dot(x: V, y: V) -> Q2:
    return x[0]*y[0] + x[1]*y[1]


def rot(x: V) -> V:
    return -x[1], x[0]


def eq(x: Q2, y: Q2 | F | int) -> bool:
    return (x-Q2.of(y)).sign() == 0


def veq(x: V, y: V) -> bool:
    return eq(x[0], y[0]) and eq(x[1], y[1])


@dataclass(frozen=True)
class Square:
    c: V
    u: V = vec(1, 0)
    v: V = vec(0, 1)

    def vertices(self) -> list[V]:
        return [add(self.c, add(mul(F(s, 2), self.u), mul(F(t, 2), self.v)))
                for s in (-1, 1) for t in (-1, 1)]

    def halfwidth(self, e: V) -> Q2:
        return (abs(dot(e, self.u)) + abs(dot(e, self.v))) / 2

    def contains(self, p: V) -> bool:
        z = sub(p, self.c)
        return (abs(dot(z, self.u))-HALF).sign() <= 0 and \
               (abs(dot(z, self.v))-HALF).sign() <= 0


# Directed contacts: (tail, head, normal from tail to head, point, weight).
Contact = tuple[int, int, V, V, Q2]
# Circle atom: (square index, actual corner, positive multiplier).
Atom = tuple[int, V, Q2]


def radial_square(e: V, center_radius: F) -> Square:
    return Square(mul(center_radius, e), e, rot(e))


def circle_pair(i: int, e: V, T: F, force: Q2 | F | int) -> list[Atom]:
    total_weight = Q2.of(force) / (2*T)
    return [(i, add(mul(T, e), mul(s, rot(e))), total_weight/2)
            for s in (-HALF, HALF)]


def check_packing(squares: list[Square], q: Q2) -> dict:
    for s in squares:
        assert eq(dot(s.u, s.u), 1) and eq(dot(s.v, s.v), 1)
        assert eq(dot(s.u, s.v), 0)
        for p in s.vertices():
            assert (q-dot(p, p)).sign() >= 0
    pairs = 0
    for a, b in combinations(squares, 2):
        delta = sub(b.c, a.c)
        gaps = [abs(dot(delta, e))-a.halfwidth(e)-b.halfwidth(e)
                for e in (a.u, a.v, b.u, b.v)]
        assert any(g.sign() >= 0 for g in gaps), "physical SAT failure"
        pairs += 1
    return {"squares": len(squares), "corners": 4*len(squares),
            "physical_SAT_pairs": pairs, "squared_radius": q.text()}


def check_stress(name: str, squares: list[Square], q: Q2,
                 edges: list[Contact], atoms: list[Atom]) -> dict:
    result = check_packing(squares, q)
    total = sum((w for _, _, w in atoms), ZERO)
    assert total.sign() > 0
    atoms = [(i, p, w/total) for i, p, w in atoms]
    edges = [(i, j, n, p, w/total) for i, j, n, p, w in edges]
    force = [vec(0, 0) for _ in squares]
    moment = [ZERO for _ in squares]
    circle_weight = [ZERO for _ in squares]
    graph = [set() for _ in squares]
    assert eq(sum((w for _, _, w in atoms), ZERO), 1)
    for i, p, w in atoms:
        assert w.sign() > 0 and eq(dot(p, p), q)
        assert any(veq(p, v) for v in squares[i].vertices())
        force[i] = add(force[i], mul(2*w, p))
        moment[i] += 2*w*dot(p, rot(sub(p, squares[i].c)))
        circle_weight[i] += w
    for i, j, n, p, w in edges:
        assert w.sign() > 0 and eq(dot(n, n), 1)
        assert squares[i].contains(p) and squares[j].contains(p)
        assert eq(dot(n, sub(p, squares[i].c)), squares[i].halfwidth(n))
        assert eq(dot(n, sub(p, squares[j].c)), -squares[j].halfwidth(n))
        for k, sign in ((i, 1), (j, -1)):
            force[k] = add(force[k], mul(sign*w, n))
            moment[k] += sign*w*dot(n, rot(sub(p, squares[k].c)))
        graph[i].add(j)
        graph[j].add(i)
    assert all(veq(f, vec(0, 0)) for f in force)
    assert all(eq(m, 0) for m in moment)
    visited, todo = set(), [0]
    while todo:
        i = todo.pop()
        if i not in visited:
            visited.add(i)
            todo.extend(graph[i]-visited)
    assert len(visited) == len(squares) and len(edges) == len(squares)-1
    s_count = v_count = interior_count = 0
    unloaded = []
    for i, square in enumerate(squares):
        if circle_weight[i].sign() == 0:
            unloaded.append(i)
            assert square.contains(vec(0, 0))
            coords = [abs(dot(square.c, square.u)), abs(dot(square.c, square.v))]
            boundary = sum(eq(x, HALF) for x in coords)
            if boundary == 2:
                v_count += 1
            elif boundary == 1:
                s_count += 1
            else:
                interior_count += 1
    result.update(name=name, contacts=len(edges), circle_atoms=len(atoms),
                  loaded_bodies=sum(w.sign() > 0 for w in circle_weight),
                  unloaded_bodies=len(unloaded), s=s_count, v=v_count,
                  origin_interior_unloaded=interior_count,
                  all_forces_and_torques_exactly_zero=True,
                  positive_body_graph_is_tree=True)
    return result


def path_witness(t1: F, t2: F) -> dict:
    e = vec(1, 0)
    squares = [Square(vec(F(-3, 2), 0)), Square(vec(-HALF, t1)),
               Square(vec(HALF, t2)), Square(vec(F(3, 2), 0))]
    edges = [(0, 1, e, vec(-1, 0), Q2(1)),
             (1, 2, e, vec(0, 0), Q2(1)),
             (2, 3, e, vec(1, 0), Q2(1))]
    atoms = circle_pair(0, vec(-1, 0), F(2), 1) + circle_pair(3, e, F(2), 1)
    return check_stress(f"two_loaded_path_{t1}_{t2}", squares, Q0, edges, atoms)


def nonaligned_y_tree() -> dict:
    up, down = vec(0, 1), vec(0, -1)
    u, v = vec(W, -W), vec(-W, -W)
    squares = [Square(vec(0, HALF)), Square(mul(HALF, add(u, v)), u, v),
               radial_square(up, F(3, 2)), radial_square(u, F(3, 2)),
               radial_square(v, F(3, 2))]
    edges = [(0, 2, up, up, SQRT2), (0, 1, down, vec(0, 0), SQRT2),
             (1, 3, u, u, Q2(1)), (1, 4, v, v, Q2(1))]
    atoms = circle_pair(2, up, F(2), SQRT2) + \
            circle_pair(3, u, F(2), 1) + circle_pair(4, v, F(2), 1)
    return check_stress("TREE.11_nonstar_nonaligned_five_body_core", squares, Q0, edges, atoms)


def seven_body_tree12() -> dict:
    up, right, down, left = vec(0,1), vec(1,0), vec(0,-1), vec(-1,0)
    squares = [Square(vec(0, HALF)), Square(vec(-HALF,-HALF)),
               Square(vec(HALF,-HALF))] + \
              [radial_square(e, F(3,2)) for e in (up,right,down,left)]
    edges = [(0,3,up,up,Q2(1)), (0,1,down,vec(0,0),Q2(1)),
             (1,2,right,vec(0,0),Q2(1)), (1,6,left,left,Q2(1)),
             (1,5,down,down,Q2(1)), (2,4,right,right,Q2(1))]
    atoms = [a for i,e in enumerate((up,right,down,left),3)
             for a in circle_pair(i,e,F(2),1)]
    return check_stress("TREE.12_feasible_seven_body_core_no_ninth_completion", squares, Q0, edges, atoms)


def below_window_star() -> dict:
    directions = (vec(1,0),vec(0,1),vec(-1,0),vec(0,-1))
    squares = [Square(vec(0,0))] + [radial_square(e,F(1)) for e in directions]
    edges = [(0,i,e,mul(HALF,e),Q2(1)) for i,e in enumerate(directions,1)]
    atoms = [a for i,e in enumerate(directions,1) for a in circle_pair(i,e,F(3,2),1)]
    return check_stress("negative_control_valid_star_below_radius_window", squares, Q2(F(5,2)), edges, atoms)


def run(source_commit: str) -> dict:
    started = datetime.now(timezone.utc).isoformat()
    cases = sorted((s,v) for s in range(5) for v in range(5)
                   if 2*s+v <= 4 and s+v >= 2)
    assert cases == [(0,2),(0,3),(0,4),(1,1),(1,2),(2,0)]
    exact_checks = 0
    def rational_ok(condition: bool) -> None:
        nonlocal exact_checks
        assert condition
        exact_checks += 1
    rational_ok(F(79,40)**2-F(1,4) > F(19,10)**2)
    rational_ok(QSTAR-F(1,4) < F(101,50)**2)
    rational_ok(F(59,40)**2 > 2)
    rational_ok(QSTAR < F(21,10)**2)
    rational_ok(F(7,5)**2 < 2)
    rational_ok(2*F(49,50)**2 > F(51,50)**2)
    rational_ok(F(5,4) < F(9,8)**2)
    rational_ok(F(1,32) < F(1,4))
    for j in range(101):
        t = F(j,250)
        a,b = (1-t*t)/(1+t*t),2*t/(1+t*t)
        rational_ok(a*a+b*b == 1 and a >= b >= 0)
        rational_ok(2*a+b-2 == b*(1+a-2*b)/(1+a))
        rational_ok(a*a+a*b/2-F(3,4) == (a-b)*(a+3*b)/4)
        value=(F(1,2)+a)**2+(1+(a+b)/2)**2
        rational_ok(value == F(3,2)+(2*a+b)+(a*a+a*b/2))
        rational_ok(value > F(17,4))
    for j in range(1,100):
        a=F(j,5000)
        rational_ok(0<a<F(1,50))
        rational_ok(4*a < F(9,100))
        rational_ok((1+a)**2-1 < F(9,100))
        rational_ok((1+a)**2-1-a*a == 2*a)
    # Exact diagonal orientation, not just rational-angle tests.
    diagonal_bound=(Q2(HALF)+W)*(Q2(HALF)+W)+(Q2(1)+W)*(Q2(1)+W)
    assert (diagonal_bound-Q0).sign() > 0
    witnesses=[path_witness(F(0),F(0)), path_witness(F(1,3),F(-2,5)),
               path_witness(HALF,F(0)), path_witness(HALF,-HALF),
               nonaligned_y_tree(), seven_body_tree12(), below_window_star()]
    cardinal=[Square(vec(F(3,2),0)),Square(vec(F(-3,2),0)),
              Square(vec(0,F(3,2))),Square(vec(0,F(-3,2)))]
    central=[Square(vec(x,y)) for x in (-HALF,HALF) for y in (-HALF,HALF)]
    cage=check_packing(cardinal+central,Q0)
    # The diagonal-center conclusion is false if the radius is relaxed to 9/2.
    larger=check_packing(cardinal+[Square(vec(1,1))],Q2(F(9,2)))
    # A count of <=2 squares above an arbitrary staggered row is FALSE.
    row=[Square(vec(F(-3,2),0)),Square(vec(-HALF,-HALF)),
         Square(vec(HALF,-HALF)),Square(vec(F(3,2),0))]
    upper=[Square(vec(-HALF,HALF)),Square(vec(HALF,HALF)),Square(vec(0,F(3,2)))]
    above=check_packing(row+upper,Q0)
    raw=Path(__file__).read_bytes()
    return {"status":"PASS", "started_utc":started,
            "finished_utc":datetime.now(timezone.utc).isoformat(),
            "python":platform.python_version(), "source_commit":source_commit,
            "source_sha256":hashlib.sha256(raw).hexdigest(),
            "source_git_blob_sha1":hashlib.sha1(b"blob "+str(len(raw)).encode()+b"\0"+raw).hexdigest(),
            "exact_rational_checks":exact_checks,
            "exhaustive_integer_incidence_cases":cases,
            "physical_force_torque_tree_witnesses":witnesses,
            "eight_square_cardinal_cage_attainment":cage,
            "negative_control_diagonal_center_at_q_9_over_2":larger,
            "negative_control_three_above_staggered_row_at_q_17_over_4":above,
            "scope":"Finite exact regressions, NOT universal optimality, not an independent full audit, and not Lean verification."}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-commit",default="LOCAL_UNCOMMITTED")
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=run(args.source_commit)
    text=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.write_text(text,encoding="utf-8")
    print(text,end="")


if __name__ == "__main__":
    main()
