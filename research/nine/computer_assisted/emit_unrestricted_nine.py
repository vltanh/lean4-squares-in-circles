#!/usr/bin/env python3
"""Exact, stress-free unit-square packing formula in QF_NRA SMT-LIB.

Default: nine squares, variable 0 <= q < 1105/256. No solver is called.
All pair separators are polynomial: no abs, ite, stress, contact graph,
normal selector, extra real variables, or lower-radius assumption.
See UNRESTRICTED_MODEL_AND_ROW_CERTIFICATE.md for the equivalence proof.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from typing import Union

Term = Union[int, str, tuple]
Q = Fraction(1105, 256)
SIGNS = tuple(product((-1, 1), repeat=2))


def op(name: str, *args: Term) -> tuple:
    return (name, *args)


def add(*args: Term) -> tuple:
    return op('+', *args)


def mul(*args: Term) -> tuple:
    return op('*', *args)


def neg(a: Term) -> tuple:
    return op('-', a)


def sub(a: Term, b: Term) -> tuple:
    return op('-', a, b)


def dot(a: tuple, b: tuple) -> tuple:
    return add(mul(a[0], b[0]), mul(a[1], b[1]))


def render(t: Term) -> str:
    if isinstance(t, bool):
        raise TypeError('Boolean literals are not polynomial terms')
    if isinstance(t, int):
        return str(t) if t >= 0 else f'(- {-t})'
    if isinstance(t, str):
        return t
    return '(' + ' '.join([t[0], *(render(x) for x in t[1:])]) + ')'


@dataclass
class Formula:
    n: int
    radius: str
    gauge: bool
    variables: list[str] = field(default_factory=list)
    definitions: list[tuple[str, Term]] = field(default_factory=list)
    assertions: list[tuple[str, Term]] = field(default_factory=list)
    _names: set[str] = field(default_factory=set)

    def reserve(self, name: str) -> None:
        if name in self._names:
            raise ValueError(f'duplicate name: {name}')
        self._names.add(name)

    def variable(self, name: str) -> str:
        self.reserve(name)
        self.variables.append(name)
        return name

    def define(self, name: str, term: Term) -> str:
        self.reserve(name)
        self.definitions.append((name, term))
        return name

    def require(self, name: str, predicate: Term) -> None:
        self.reserve(name)
        self.assertions.append((name, predicate))

    def stats(self) -> dict:
        return {'squares': self.n, 'radius': self.radius, 'rotation_gauge': self.gauge,
                'real_variables': len(self.variables),
                'definitions': len(self.definitions), 'assertions': len(self.assertions),
                'unit_equations': self.n - int(self.gauge),
                'corner_constraints': 4 * self.n,
                'pair_disjunctions': self.n * (self.n - 1) // 2,
                'directed_branches_per_pair': 8,
                'quadratic_inequalities_per_branch': 4,
                'global_unsat_proved': False}

    def smt2(self) -> str:
        rows = ['; Exact unrestricted square packing; NOT an infeasibility certificate.',
                '; All Real variables are existential for satisfiability.',
                '; ' + json.dumps(self.stats(), sort_keys=True), '(set-logic QF_NRA)']
        rows += [f'(declare-fun {v} () Real)' for v in self.variables]
        rows += [f'(define-fun {v} () Real {render(t)})' for v, t in self.definitions]
        rows += [f'(assert (! {render(t)} :named {v}))' for v, t in self.assertions]
        rows += ['(check-sat)', '']
        return '\n'.join(rows)


def build(n: int = 9, radius: str = 'variable', gauge: bool = False) -> Formula:
    """Build the exact formula. Gauge is equisatisfiable, not posewise identical.

    variable: q >= 0, 256q < 1105, corners <= q.
    strict: remove q; all original corners have norm^2 < Q.
    closed: remove q; all original corners have norm^2 <= Q (control model).
    """
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError('n must be a positive integer')
    if radius not in {'variable', 'strict', 'closed'}:
        raise ValueError('unknown radius mode')
    f = Formula(n, radius, gauge)
    if radius == 'variable':
        q = f.variable('q')
        f.require('q_nonnegative', op('>=', q, 0))
        f.require('q_subcritical', op('<', mul(256, q), 1105))
    squares = []
    for i in range(n):
        x, y = f.variable(f'x_{i}'), f.variable(f'y_{i}')
        if gauge and i == 0:
            a, b = 1, 0
        else:
            a, b = f.variable(f'a_{i}'), f.variable(f'b_{i}')
            f.require(f'unit_{i}', op('=', add(mul(a, a), mul(b, b)), 1))
        u, v = (a, b), (neg(b), a)
        squares.append(((x, y), u, v))
        for k, (s, t) in enumerate(SIGNS):
            # Doubled original corners: integer coefficients, no division.
            X = f.define(f'X_{i}_{k}', add(mul(2, x), mul(s, a), mul(-t, b)))
            Y = f.define(f'Y_{i}_{k}', add(mul(2, y), mul(s, b), mul(t, a)))
            N = add(mul(X, X), mul(Y, Y))
            predicate = (op('<=', N, mul(4, 'q')) if radius == 'variable'
                         else op('<' if radius == 'strict' else '<=', mul(64, N), 1105))
            f.require(f'corner_{i}_{k}', predicate)
    for i, j in combinations(range(n), 2):
        ci, ui, vi = squares[i]
        cj, uj, vj = squares[j]
        displacement = (sub(cj[0], ci[0]), sub(cj[1], ci[1]))
        # C = ui.uj, S = det(ui,uj) = vi.uj.
        C = f.define(f'C_{i}_{j}', dot(ui, uj))
        S = f.define(f'S_{i}_{j}', dot(vi, uj))
        branches = []
        for k, axis in enumerate((ui, vi, uj, vj)):
            P = f.define(f'P_{i}_{j}_{k}', dot(axis, displacement))
            for sign in (-1, 1):
                # 2 sign P >= 1 + |C| + |S| iff these FOUR bounds hold.
                bounds = [op('>=', mul(2 * sign, P),
                             add(1, mul(s, C), mul(t, S))) for s, t in SIGNS]
                branches.append(op('and', *bounds))
        f.require(f'pair_{i}_{j}', op('or', *branches))
    return f


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--radius', choices=('variable', 'strict', 'closed'), default='variable')
    ap.add_argument('--gauge', action='store_true', help='Globally rotate square 0 horizontal')
    ap.add_argument('--output', type=Path)
    ap.add_argument('--stats', action='store_true')
    args = ap.parse_args()
    f = build(radius=args.radius, gauge=args.gauge)
    if args.stats:
        print(json.dumps(f.stats(), indent=2))
    elif args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(f.smt2(), encoding='utf-8')
    else:
        print(f.smt2(), end='')


if __name__ == '__main__':
    main()
