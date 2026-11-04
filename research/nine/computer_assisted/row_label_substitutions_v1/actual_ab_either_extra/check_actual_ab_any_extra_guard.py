#!/usr/bin/env python3
"""Exact substitution, closed-face, correlation and damaged-literal controls."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product, combinations
from copy import deepcopy
import hashlib
import json
import actual_ab_any_extra_guard as P
import independent_actual_ab_any_extra_guard as I

HERE = Path(__file__).resolve().parent


def main():
    assert hashlib.sha256((HERE / 'ACCEPTED_ACTUAL_AB_HAND_PROOF.md').read_bytes()).hexdigest() == \
        '5573dff780b79d60cbea535e946ce3669a6fcbbe8152779348ba35107909d7cb'
    states = positives = damaged = correlated = 0
    for extra, sign, x, heights, gx, gy in product(
            (7, 8), (-1, 0, 1), map(F, (-1, 0, 1, 2, 3)),
            product((F(-3, 10), F(0), F(3, 10)), repeat=3),
            (F(-1), F(-1, 2), F(0), F(1, 2), F(1)), map(F, (-1, 0, 1))):
        yb, yx, yd = heights
        positions = [(F(0), F(0)) for _ in range(18)]
        for original, xx, yy in ((1, F(0), yb), (3, F(2), yd),
                                  (extra, x, yx), (6, 2 + gx, yd + gy),
                                  (15 - extra, F(20), F(20))):
            positions[2 * original] = (xx, xx)
            positions[2 * original + 1] = (yy, yy)
        angles = [(F(-1), F(1)) for _ in range(9)]
        scalar = [(F(-1), F(1)) for _ in range(36)]
        angles[3] = scalar[12] = (F(sign), F(sign))
        state = dict(positions=positions, angles=angles, scalar=scalar,
                     differences={}, path=[['unchanged_original_path']],
                     id='unchanged_original_id', choices=[['unchanged_choices']])
        before = deepcopy(state)
        printed = P.evaluate(state, extra)
        assert printed == I.evaluate(state, extra)
        assert state == before
        expected = sign >= 0 and abs(gx) < 1 and gy >= 0 and 0 <= x <= 2 \
            and abs(yx - yb) + abs(yd - yx) <= F(3, 5)
        assert (printed['status'] == 'PASS_ACTUAL_AB_ANY_EXTRA_TERMINAL_GUARD') == expected
        states += 1
        if expected:
            I.verify_literal(printed, state)
            positives += 1
            corruptions = []
            changed = deepcopy(printed)
            changed['physical_row'] = [0, 1, 15 - extra, 3]
            corruptions.append(changed)
            changed = deepcopy(printed)
            changed['two_link_variation_upper'] = str(F(printed['two_link_variation_upper']) + F(1, 1000))
            corruptions.append(changed)
            for changed in corruptions:
                try:
                    I.verify_literal(changed, state)
                except AssertionError:
                    damaged += 1
                else:
                    raise AssertionError('Damaged terminal literal accepted')
        if sign == 0 and x == 1 and gx == 0 and gy == 1:
            broad = deepcopy(state)
            broad['positions'] = [(lo - 1, hi + 1) for lo, hi in positions]
            for i, j in combinations(range(9), 2):
                broad['differences'][i, j] = tuple(
                    (positions[2 * j + axis][0] - positions[2 * i + axis][0],) * 2
                    for axis in (0, 1))
            assert P.evaluate(broad, extra) == I.evaluate(broad, extra) == printed
            correlated += 1
    for h in (F(1, 2), F(3, 5), F(2, 3), F(7, 10)):
        assert h + 1 / (4 * h) - 1 == (2 * h - 1) ** 2 / (4 * h) >= 0
    files = (__file__, P.__file__, I.__file__, P.SOURCE.__file__,
             HERE / 'ACCEPTED_ACTUAL_AB_HAND_PROOF.md',
             HERE / 'ACTUAL_AB_ANY_EXTRA_LITERAL_HAND_PROOF.md')
    report = dict(status='PASS_LITERAL_ACTUAL_AB_BOTH_EXTRAS_GUARDS',
                  guard_states=states, positive_guards=positives,
                  correlated_translation_controls=correlated,
                  damaged_literals_rejected=damaged,
                  original_path_and_choices_unchanged=True,
                  unchanged_scalar_domains=28, unchanged_scalar_leaves=103,
                  inherited_coefficients=12875, scalar_replay_required_on_actual_use=True,
                  source_sha256={str(Path(p).resolve()): hashlib.sha256(Path(p).read_bytes()).hexdigest()
                                 for p in files},
                  new_original_cells=0, new_masks=0)
    (HERE / 'EXACT_GUARD_CONTROLS.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'source_sha256'}))


if __name__ == '__main__':
    main()
