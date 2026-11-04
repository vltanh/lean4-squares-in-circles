"""Small exact target-scope and inherited quantitative-guard controls."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
import hashlib
import json
import strict_011_actual_ab_guard as P
import independent_strict_011_actual_ab_guard as I

HERE = Path(__file__).resolve().parent


def rejected(action):
    try:
        action()
    except AssertionError:
        return 1
    raise AssertionError('A damaged literal or wrong caller target was accepted')


def main():
    states = positives = damaged = wrong_target = 0
    for extra, sign, variation, x, gx in product(
            (7, 8), (-1, 0), (F(0), F(3, 5), F(601, 1000)),
            (F(-1, 100), F(0), F(1), F(2), F(201, 100)), (F(0), F(1))):
        positions = [(F(0), F(0)) for _ in range(18)]
        for original, xx, yy in ((1, F(0), F(0)), (3, F(2), F(0)),
                                  (extra, x, variation/2), (6, 2+gx, F(1))):
            positions[2*original] = (xx, xx)
            positions[2*original+1] = (yy, yy)
        angles = [(F(-1), F(1)) for _ in range(9)]
        scalar = [(F(-1), F(1)) for _ in range(36)]
        angles[3] = scalar[12] = (F(sign), F(sign))
        state = dict(positions=positions, angles=angles, scalar=scalar,
                     differences={}, path=['unchanged synthetic guard input'])
        before = deepcopy(state)
        printed = P.evaluate(state, extra, mask='011/00', radius_mode='strict')
        assert printed == I.evaluate(state, extra, mask='011/00', radius_mode='strict')
        assert state == before
        expected = sign >= 0 and variation <= F(3, 5) and 0 <= x <= 2 and gx < 1
        assert (printed['status'] == 'PASS_CONDITIONAL_STRICT_01100_ACTUAL_AB_GUARD') == expected
        assert printed['closed_Q_excluded'] is False
        assert printed['current_00100_CD_equality_blocker_used'] is False
        states += 1
        if not expected:
            continue
        positives += 1
        I.verify_literal(printed, state, mask='011/00', radius_mode='strict')
        for key, value in [('closed_Q_excluded', True), ('mask', '001/00'),
                           ('radius_mode', 'closed'), ('required_actual_links', [[0, 1], [1, 2], [4, 5], [5, 6]]),
                           ('retained_strict_weak_links', [[2, 3]]),
                           ('two_link_variation_upper', str(variation+F(1, 1000)))]:
            changed = deepcopy(printed)
            changed[key] = value
            damaged += rejected(lambda: I.verify_literal(changed, state, mask='011/00', radius_mode='strict'))
        for implementation in (P, I):
            wrong_target += rejected(lambda: implementation.evaluate(state, extra, mask='011/00', radius_mode='closed'))
            wrong_target += rejected(lambda: implementation.evaluate(state, extra, mask='001/00', radius_mode='strict'))
            wrong_target += rejected(lambda: implementation.evaluate(state, extra, mask='011/01', radius_mode='strict'))
    dependencies = json.loads((HERE/'ACCEPTED_DEPENDENCIES.json').read_text())
    for entry in dependencies['literal_copies']:
        assert hashlib.sha256((HERE/entry['copy']).read_bytes()).hexdigest() == entry['sha256']
    files = sorted(path for path in HERE.iterdir()
                   if path.is_file() and path.name not in
                   ('EXACT_APPLICATION_CONTROLS.json', 'PREMISE_BINDINGS.json'))
    report = dict(status='PASS_CONDITIONAL_STRICT_01100_APPLICATION_CONTROLS',
                  synthetic_guard_states=states, positive_conditional_guards=positives,
                  damaged_literals_rejected=damaged, wrong_target_calls_rejected=wrong_target,
                  original_state_unchanged=True, closed_Q_claim=False,
                  scalar_replay_performed=False, accepted_scalar_replay_required_on_actual_use=True,
                  numerical_search_performed=False, new_original_cells=0, new_masks=0,
                  source_sha256={path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in files})
    (HERE/'EXACT_APPLICATION_CONTROLS.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'source_sha256'}))


if __name__ == '__main__':
    main()
