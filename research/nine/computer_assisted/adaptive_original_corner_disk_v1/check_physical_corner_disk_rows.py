#!/usr/bin/env python3
"""Exact identities, original corner indexing, disk faces, and tamper controls."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import physical_corner_disk_rows as P
import independent_physical_corner_disk_rows as I

HERE = Path(__file__).resolve().parent


def main():
    rows = evaluations = contained = boundary = damaged = 0
    directions = [(F(1), F(0)), (F(0), F(-1)), (F(33), F(4))]
    directions += [(F(2 * k - 9, 7), F((3 * k) % 11 - 5, 13)) for k in range(11)]
    for original, epsilon, tau, direction in product(range(9), (-1, 1), (-1, 1), directions):
        a, b = direction
        row = P.row(original, epsilon, tau, a, b)
        I.verify_literal(row)
        rows += 1
        for t, x, y in product((F(k, 8) for k in range(-3, 4)), map(F, (-1, 0, 1)), map(F, (-1, 0, 1))):
            alpha, beta = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
            assert alpha * alpha + beta * beta == 1
            zx = x + (epsilon * alpha - tau * beta) / 2
            zy = y + (epsilon * beta + tau * alpha) / 2
            values = {2 * original: x, 2 * original + 1: y,
                      18 + original: alpha, 27 + original: beta}
            lhs = sum(value * values[index] for index, value in row[0])
            assert lhs == a * zx + b * zy
            assert (a * a + b * b) * (zx * zx + zy * zy) - lhs * lhs == (a * zy - b * zx) ** 2
            if zx * zx + zy * zy <= P.Q:
                assert lhs <= row[1]
                contained += 1
            evaluations += 1
        for sx, sy, swap in product((-1, 1), (-1, 1), (False, True)):
            zx, zy = F(33 * sx, 16), F(sy, 4)
            if swap:
                zx, zy = zy, zx
            assert zx * zx + zy * zy == P.Q
            assert a * zx + b * zy <= row[1]
            boundary += 1
        altered = list(row[0])
        index, value = altered[0]
        altered[0] = (index, value + 1)
        zero_rhs_name = row[2].rsplit('_', 1)[0] + '_0'
        for bad in ((tuple(altered), row[1], row[2]), (row[0], F(0), zero_rhs_name)):
            try:
                I.verify_literal(bad)
            except AssertionError:
                damaged += 1
            else:
                raise AssertionError('Invalid corner row accepted')
    exact_boundary = P.row(0, 1, 1, 33, 4)
    assert exact_boundary[1] == F(1105, 16)
    files = (__file__, P.__file__, I.__file__, HERE / 'ADAPTIVE_ORIGINAL_CORNER_DISK_HAND_PROOF.md')
    report = dict(status='PASS_EXACT_ORIGINAL_CORNER_DISK_ROWS',
                  independently_rebuilt_rows=rows, exact_corner_expansions=evaluations,
                  contained_corner_evaluations=contained, exact_disk_boundary_controls=boundary,
                  damaged_literals_rejected=damaged,
                  source_sha256={str(Path(p).resolve()): hashlib.sha256(Path(p).read_bytes()).hexdigest()
                                 for p in files},
                  new_original_cells=0, new_masks=0)
    (HERE / 'EXACT_CONTROLS.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'source_sha256'}))


if __name__ == '__main__':
    main()
