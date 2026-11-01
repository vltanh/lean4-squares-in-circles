#!/usr/bin/env python3
"""Independent exact tests of emitted SMT text, not a global packing proof.

Does not import the emitter, its expression representation, or any stress code.
Parses emitted SMT-LIB and compares predicates with exact polygon clipping.
Standard library only. All arithmetic is Fraction. Deterministic test seeds.
"""
from __future__ import annotations

import hashlib
import json
import random
import re
import subprocess
import sys
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q = F(1105, 256)


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def parse_smt(text):
    tokens = re.findall(r'\(|\)|[^\s()]+', re.sub(r';[^\n]*', '', text))
    stack, output = [], []
    for token in tokens:
        if token == '(':
            stack.append([])
        elif token == ')':
            need(bool(stack), 'unmatched close parenthesis')
            value = stack.pop()
            (stack[-1] if stack else output).append(value)
        else:
            need(bool(stack), 'unexpected top-level atom')
            stack[-1].append(token)
    need(not stack, 'unclosed expression')
    return output


class Parsed:
    def __init__(self, text):
        self.variables, self.defs, self.predicates = [], {}, {}
        commands = parse_smt(text)
        need(commands[0] == ['set-logic', 'QF_NRA'], 'logic')
        need(commands[-1] == ['check-sat'], 'termination')
        for c in commands[1:-1]:
            if c[0] == 'declare-fun':
                need(c[2:] == [[], 'Real'] and c[1] not in self.variables, 'declaration')
                self.variables.append(c[1])
            elif c[0] == 'define-fun':
                need(c[2:4] == [[], 'Real'] and c[1] not in self.defs, 'definition')
                self.defs[c[1]] = c[4]
            elif c[0] == 'assert':
                a = c[1]
                need(a[0] == '!' and a[2] == ':named', 'named assertion')
                need(a[3] not in self.predicates, 'duplicate assertion')
                self.predicates[a[3]] = a[1]
            else:
                raise AssertionError('unexpected command ' + c[0])
        # Inspect all text: no opaque functions/quantifiers, no conditional stress.
        need(not re.search(r'\b(?:ite|abs|lambda|mu|torque|force|forall|exists)\b',
                           re.sub(r';[^\n]*', '', text)), 'nonphysical/unsupported term')

    def value(self, term, env):
        if isinstance(term, str):
            try:
                return F(term)
            except ValueError:
                pass
            if term not in env:
                need(term in self.defs, 'unknown symbol ' + term)
                env[term] = self.value(self.defs[term], env)
            return env[term]
        op, args = term[0], term[1:]
        if op == 'and':
            return all(self.value(a, env) for a in args)
        if op == 'or':
            return any(self.value(a, env) for a in args)
        a = [self.value(x, env) for x in args]
        if op == '+':
            return sum(a, F(0))
        if op == '*':
            out = F(1)
            for v in a:
                out *= v
            return out
        if op == '-':
            return -a[0] if len(a) == 1 else a[0] - a[1]
        if op == '=':
            return a[0] == a[1]
        if op == '<':
            return a[0] < a[1]
        if op == '<=':
            return a[0] <= a[1]
        if op == '>=':
            return a[0] >= a[1]
        if op == '>':
            return a[0] > a[1]
        raise AssertionError('unsupported operation ' + op)

    def failures(self, assignment):
        env = dict(assignment)
        need(set(self.variables) <= set(env), 'incomplete assignment')
        return [name for name, term in self.predicates.items() if not self.value(term, env)]

    def inspect(self, radius, gauge):
        expected = {f'corner_{i}_{k}' for i in range(9) for k in range(4)}
        expected |= {f'unit_{i}' for i in range(int(gauge), 9)}
        expected |= {f'pair_{i}_{j}' for i, j in combinations(range(9), 2)}
        if radius == 'variable':
            expected |= {'q_nonnegative', 'q_subcritical'}
        need(set(self.predicates) == expected, 'missing/extra physical constraint')
        need(len(self.variables) == 36 - 2 * gauge + (radius == 'variable'), 'variable count')
        need(len(self.defs) == 288, 'definition count')
        for i, j in combinations(range(9), 2):
            term = self.predicates[f'pair_{i}_{j}']
            need(term[0] == 'or' and len(term) == 9, 'eight directed axes')
            need(all(b[0] == 'and' and len(b) == 5 for b in term[1:]), 'four bounds')
        degree_cache = {}

        def degree(t):
            if isinstance(t, str):
                try:
                    F(t)
                    return 0
                except ValueError:
                    if t in self.variables:
                        return 1
                    if t not in degree_cache:
                        degree_cache[t] = degree(self.defs[t])
                    return degree_cache[t]
            ds = [degree(x) for x in t[1:]]
            return sum(ds) if t[0] == '*' else max(ds, default=0)

        need(max(degree(t) for t in self.predicates.values()) <= 2, 'degree > 2')


def vertices(pose):
    x, y, a, b = pose
    # Explicit counterclockwise polygon; independent of emitter sign enumeration.
    return [(x + (s * a - t * b) / 2, y + (s * b + t * a) / 2)
            for s, t in ((-1, -1), (1, -1), (1, 1), (-1, 1))]


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def subtract(a, b):
    return a[0] - b[0], a[1] - b[1]


def intersection_area(a, b):
    """Exact Sutherland-Hodgman clipping, not a support-function test."""
    polygon = vertices(a)
    other = vertices(b)
    for A, B in zip(other, other[1:] + other[:1]):
        edge = subtract(B, A)
        old, polygon = polygon, []
        if not old:
            return F(0)
        previous = old[-1]
        dp = cross(edge, subtract(previous, A))
        for current in old:
            dc = cross(edge, subtract(current, A))
            if (dp >= 0) != (dc >= 0):
                w = dp / (dp - dc)
                polygon.append((previous[0] + w * (current[0] - previous[0]),
                                previous[1] + w * (current[1] - previous[1])))
            if dc >= 0:
                polygon.append(current)
            previous, dp = current, dc
    return abs(sum((cross(A, B) for A, B in zip(polygon, polygon[1:] + polygon[:1])), F(0))) / 2


def witness():
    centers = [(F(x, 2), F(1, 16)) for x in (-3, -1, 1, 3)]
    centers += [(F(x), -F(15, 16)) for x in (-1, 0, 1)]
    centers += [(F(x, 20), F(19, 16)) for x in (-11, 11)]
    return [(x, y, F(1) if i < 7 else F(99, 101), F(0) if i < 7 else F(20, 101))
            for i, (x, y) in enumerate(centers)]


def assignment(poses, q=Q):
    out = {'q': q}
    for i, p in enumerate(poses):
        out.update({f'{v}_{i}': z for v, z in zip(('x', 'y', 'a', 'b'), p)})
    return out


def rotate(poses, a, b):
    return [(a*x-b*y, b*x+a*y, a*u-b*v, b*u+a*v) for x, y, u, v in poses]


def run():
    emitter = HERE / 'emit_unrestricted_nine.py'
    models = {}
    digest = {}
    for radius, gauge in product(('variable', 'strict', 'closed'), (False, True)):
        cmd = [sys.executable, str(emitter), '--radius', radius]
        if gauge:
            cmd += ['--gauge']
        text = subprocess.check_output(cmd, text=True)
        parsed = Parsed(text)
        parsed.inspect(radius, gauge)
        models[radius, gauge] = parsed
        digest[f'{radius}_gauge_{gauge}'] = hashlib.sha256(text.encode()).hexdigest()
    poses = witness()
    need(all(intersection_area(poses[i], poses[j]) == 0 for i, j in combinations(range(9), 2)),
         'independent polygon witness failure')
    norms = [x*x+y*y for p in poses for x, y in vertices(p)]
    need(max(norms) == Q, 'attaining radius')
    active = ['corner_0_1', 'corner_3_3', 'corner_4_0', 'corner_6_2']
    for gauge in (False, True):
        need(models['closed', gauge].failures(assignment(poses)) == [], 'closed witness')
        need(models['strict', gauge].failures(assignment(poses)) == active, 'strict corner boundary')
        need(models['variable', gauge].failures(assignment(poses)) == ['q_subcritical'], 'variable boundary')
        need(models['variable', gauge].failures(assignment(poses, Q-F(1, 256))) == active,
             'subcritical witness must escape')
    model = models['closed', False]
    # Rational rotation/reflection/label symmetries, tested on actual emitted text.
    rotated = rotate(poses, F(3, 5), F(4, 5))
    reflected = [(x, -y, a, -b) for x, y, a, b in poses]
    for alt in (rotated, reflected, list(reversed(poses))):
        need(not model.failures(assignment(alt)), 'physical symmetry')
    # Arbitrary two formerly unstressed squares remain physical obstacles.
    overlapping = poses[:]
    overlapping[8] = overlapping[7]
    need('pair_7_8' in model.failures(assignment(overlapping)), 'overlapping last two')
    escaped = poses[:]
    x, y, a, b = escaped[0]
    escaped[0] = (x-F(1, 1000), y, a, b)
    need('corner_0_1' in model.failures(assignment(escaped)), 'out-of-disk corner')
    invalid_frame = assignment(poses)
    invalid_frame['a_7'] = F(1)
    need('unit_7' in model.failures(invalid_frame), 'nonunit frame')
    # Tests are exact, deterministic and finite; they are NOT universal proof.
    rng = random.Random(1105256)
    frames = [(F(1), F(0)), (F(0), F(1)), (-F(1), F(0)), (F(0), -F(1))]
    for t in (F(-2), F(-1, 2), F(1, 3), F(1, 2), F(2)):
        frames.append(((1-t*t)/(1+t*t), 2*t/(1+t*t)))
    trials = []
    # All aligned weak-contact and strict overlap/separation cases at this grid.
    for a, b in product(frames[:4], repeat=2):
        for x, y in product((F(-1), F(0), F(1)), repeat=2):
            trials.append(((F(0), F(0), *a), (x, y, *b)))
    for _ in range(600):
        trial = []
        for __ in range(2):
            a, b = rng.choice(frames)
            trial.append((F(rng.randint(-16, 16), 8), F(rng.randint(-16, 16), 8), a, b))
        trials.append(tuple(trial))
    for a, b in trials:
        env = assignment([a, b])
        truth = model.value(model.predicates['pair_0_1'], env)
        need(truth == (intersection_area(a, b) == 0), 'SAT vs polygon area mismatch')
        for i, p in enumerate((a, b)):
            independent = max(x*x+y*y for x, y in vertices(p)) <= Q
            formula = all(model.value(model.predicates[f'corner_{i}_{k}'], env) for k in range(4))
            need(formula == independent, 'corner containment mismatch')
    # Mutations must be detected, not mistaken for alternative valid emitters.
    original = subprocess.check_output([sys.executable, str(emitter), '--radius', 'closed'], text=True)
    missing = Parsed(original)
    del missing.predicates['pair_7_8']
    try:
        missing.inspect('closed', False)
    except AssertionError:
        pass
    else:
        raise AssertionError('missing-pair mutation escaped')
    strict_contact = Parsed(original.replace('(>=', '(>'))
    need(any(name.startswith('pair_') for name in
             strict_contact.failures(assignment(poses))), 'strict-contact mutation escaped')
    return {'result': 'PASS', 'arithmetic': 'Fraction only',
            'emitted_models_parsed': len(models), 'pair_oracle_cases': len(trials),
            'containment_oracle_cases': 2*len(trials), 'witness_max_norm_squared': str(max(norms)),
            'witness_active_corners': active, 'emitter_sha256': hashlib.sha256(emitter.read_bytes()).hexdigest(),
            'emitted_sha256': digest,
            'oracle': 'independent exact convex-polygon intersection area',
            'separate_human_review_performed': False, 'global_infeasibility_proved': False}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
