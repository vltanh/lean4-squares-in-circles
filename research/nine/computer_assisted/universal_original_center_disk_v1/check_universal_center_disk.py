#!/usr/bin/env python3
"""Portable exact controls for the universal center support lemma and rows."""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import ast
import json

import physical_center_disk_rows as P
import independent_physical_center_disk_rows as I
import physical_center_disk_separation as S

Q, R = F(1105, 256), F(91, 60)
HERE = Path(__file__).resolve().parent


def control_suite():
    # This exact positive reserve is the only numerical constant in the
    # radius deduction, independent of every direction and search state.
    reserve = R * R + R + F(1, 2) - Q
    assert reserve == F(31, 57600) > 0
    units = []
    for t in map(F, ('-3', '-2', '-1', '-1/2', '-1/3', '0', '1/3', '1/2', '1', '2', '3')):
        units.append(((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)))
    units.append((F(-1), F(0)))
    assert len(set(units)) == len(units) == 12
    assert all(x * x + y * y == 1 for x, y in units)
    directions = {(F(0), F(0)), (F(1), F(0)), (F(-1), F(0)),
                  (F(0), F(1)), (F(0), F(-1)),
                  (F(1024), F(-511)), (F(-8, 7), F(3, 11))}
    for a, b in ((F(1), F(1)), (F(3, 5), F(4, 5)),
                 (F(5, 13), F(12, 13)), (F(2, 3), F(7, 11))):
        directions.update((sx * a, sy * b) for sx, sy in product((-1, 1), repeat=2))
    directions = sorted(directions)
    rows = []
    sqrt_checks = 0
    for a, b in directions:
        squared = R * R * (a * a + b * b)
        for bits in (0, 8, 40):
            upper = P.sqrt_upper(squared, bits)
            step = F(1, 1 << bits)
            assert upper >= 0 and upper * upper >= squared
            if upper > 0:
                assert upper >= step and (upper - step) ** 2 < squared
            else:
                assert squared == 0
            sqrt_checks += 1
        for original in range(9):
            literal = P.row(original, a, b)
            assert I.verify_literal(literal) == literal
            rows.append((original, a, b, literal))
    # The independent verifier must not import the producer or its sqrt.
    tree = ast.parse(Path(I.__file__).read_text())
    imports = [node.module for node in ast.walk(tree) if isinstance(node, ast.ImportFrom)]
    assert imports == ['fractions']
    assert not any(isinstance(node, ast.Import) for node in ast.walk(tree))
    disk_centers = {(F(0), F(0))}
    disk_centers.update((factor * R * x, factor * R * y)
                        for factor in (F(1, 2), F(1)) for x, y in units)
    evaluations = boundary = 0
    for original, a, b, (coefficients, rhs, name) in rows:
        for x, y in disk_centers:
            assert x * x + y * y <= R * R
            # Deliberately nonzero unrelated columns ensure literal support
            # really depends only on the selected original center.
            values = [F(1000 + k, 7) for k in range(54)]
            values[2 * original], values[2 * original + 1] = x, y
            got = sum(v * values[k] for k, v in coefficients)
            assert got == a * x + b * y <= rhs
            evaluations += 1
            boundary += x * x + y * y == R * R
    frames = []
    for t in map(F, ('-2/5', '-1/3', '0', '1/3', '2/5')):
        frames.append(((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)))
    expansions = contained = physical_row_evaluations = 0
    for alpha, beta in frames:
        assert alpha * alpha + beta * beta == 1 and alpha >= abs(beta)
        for ux, uy in units:
            for radius in (F(0), F(1, 3), F(1), F(5, 4), F(3, 2), R):
                x, y = radius * ux, radius * uy
                pu, pv = x * alpha + y * beta, -x * beta + y * alpha
                assert pu * pu + pv * pv == radius * radius
                assert (abs(pu) + abs(pv)) ** 2 >= radius * radius
                norms = [
                    (x + (epsilon * alpha - tau * beta) / 2) ** 2 +
                    (y + (epsilon * beta + tau * alpha) / 2) ** 2
                    for epsilon, tau in product((-1, 1), repeat=2)]
                largest = max(norms)
                assert largest == radius * radius + F(1, 2) + abs(pu) + abs(pv)
                assert largest >= radius * radius + radius + F(1, 2)
                expansions += 4
                if radius == R:
                    assert largest - Q >= reserve
                if largest <= Q:
                    assert radius < R
                    contained += 1
                    for original, a, b, literal in rows:
                        assert a * x + b * y <= literal[1]
                        physical_row_evaluations += 1
    # Squared support check deliberately accepts any sufficient upper bound,
    # independently of the producer's rounding algorithm.
    def literal(i, a, b, upper):
        co = tuple((k, v) for k, v in ((2 * i, F(a)), (2 * i + 1, F(b))) if v)
        return co, F(upper), f'{I.PREFIX}{i}_{F(a)}_{F(b)}_{F(upper)}'
    looser = literal(3, F(3, 5), F(4, 5), R + 1)
    assert I.verify_literal(looser) == looser
    exact_axis = literal(8, -1, 0, R)
    assert I.verify_literal(exact_axis) == exact_axis
    assert I.verify_literal(literal(0, 0, 0, 0))[0] == ()
    assert I.verify_literal(literal(0, 0, 0, 1))[1] == 1
    rejected = []
    def reject(name, candidate):
        try:
            I.verify_literal(candidate)
        except (AssertionError, ValueError, TypeError, ZeroDivisionError):
            rejected.append(name)
        else:
            raise AssertionError('Damaged literal accepted: ' + name)
    good = literal(2, F(3, 5), F(-4, 5), R)
    reject('negative rhs with sufficient square', literal(2, F(3, 5), F(-4, 5), -R))
    reject('underestimated support', literal(2, F(3, 5), F(-4, 5), R - F(1, 1 << 20)))
    reject('negative zero-direction rhs', literal(2, 0, 0, -1))
    reject('original below zero', literal(-1, 1, 0, R))
    reject('original above eight', literal(9, 1, 0, R))
    reject('rhs does not match name', (good[0], R + 1, good[2]))
    reject('wrong coefficient sign', (((4, F(-3, 5)), (5, F(-4, 5))), good[1], good[2]))
    reject('wrong original column', (((6, F(3, 5)), (5, F(-4, 5))), good[1], good[2]))
    reject('frame column substituted', (((20, F(3, 5)), (5, F(-4, 5))), good[1], good[2]))
    reject('product auxiliary inserted', (good[0] + ((54, F(1)),), good[1], good[2]))
    reject('duplicate coefficient', (good[0] + ((4, F(3, 5)),), good[1], good[2]))
    reject('missing coefficient', (good[0][:1], good[1], good[2]))
    reject('wrong prefix', (good[0], good[1], 'other_' + good[2]))
    reject('extra name field', (good[0], good[1], good[2] + '_0'))
    reject('noncanonical original', (good[0], good[1], good[2].replace('_2_', '_02_', 1)))
    reject('zero direction with nonzero coefficient', (((0, F(1)),), F(0), I.PREFIX + '0_0_0_0'))
    # Discovery-only numerical controls: all rows are still checked exactly.
    points = []
    for original in range(9):
        point = [0.0] * 54
        point[2 * original], point[2 * original + 1] = float(F(8, 5) * F(3, 5)), float(F(8, 5) * F(-4, 5))
        suggestions = S.violated_parameters(point)
        assert len(suggestions) == 1 and suggestions[0][0][0] == original
        parameters, _ = suggestions[0]
        exact = I.verify_literal(P.row(*parameters))
        violation = sum(v * F(str(point[k])) for k, v in exact[0]) - exact[1]
        assert violation > 0
        points.append(dict(original=original, exact_positive_violation=str(violation)))
    assert S.violated_parameters([0.0] * 54) == []
    return dict(status='PASS_UNIVERSAL_CENTER_DISK_EXACT_CONTROLS',
                original_labels=9, rational_directions=len(directions),
                independently_checked_rows=len(rows), exact_sqrt_upper_checks=sqrt_checks,
                closed_disk_evaluations=evaluations, closed_support_boundary_evaluations=boundary,
                exact_physical_corner_expansions=expansions,
                contained_physical_square_cases=contained,
                physical_row_evaluations=physical_row_evaluations,
                zero_and_nonminimal_support_cases=4,
                positive_radius_boundary_reserve=str(reserve),
                damaged_literals_rejected=rejected,
                discovery_positive_controls=points,
                numerical_solver_called=False, installed_in_running_search=False,
                new_original_closures=0, new_mask_closures=0)


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required for exact controls')
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    sources = {str(Path(x).resolve()): sha256(Path(x).read_bytes()).hexdigest()
               for x in (__file__, P.__file__, I.__file__, S.__file__)}
    report = control_suite()
    assert all(sha256(Path(name).read_bytes()).hexdigest() == expected for name, expected in sources.items())
    report['source_sha256'] = sources
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: report[k] for k in ('status', 'independently_checked_rows',
        'exact_physical_corner_expansions', 'physical_row_evaluations')}))


if __name__ == '__main__':
    main()
