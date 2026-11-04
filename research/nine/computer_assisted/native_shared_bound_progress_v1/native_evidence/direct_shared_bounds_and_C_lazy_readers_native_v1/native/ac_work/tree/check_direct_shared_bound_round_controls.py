#!/usr/bin/env python3
"""Exercise the unchanged exact round contract, including interval terminals.

These are algebraic/schema fixtures, not physical original-cell proofs.
The separate real Cb certificate is replayed with its full physical adapter.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from copy import deepcopy
from types import SimpleNamespace
import hashlib, json
import direct_shared_bound_round as DIRECT
import independent_physical_sat_diagonal_replay as CORE

PREFIX = 'certified_direct_control_'


def ceiling(value):
    value = F(value)
    numerator, denominator = value.numerator * (1 << 20), value.denominator
    return F((numerator + denominator - 1) // denominator, 1 << 20)


def printed(rows, used):
    return [dict(index=index, name=rows[index][2],
        coefficients=[[k, str(v)] for k, v in rows[index][0]], rhs=str(rows[index][1]))
        for index in sorted(used)]


ENGINE = SimpleNamespace(SCALE=1 << 40, GRID=1 << 20,
    ceil_grid=ceiling, stateview=CORE.state_view, printed=printed)


def initial():
    return dict(id='ALGEBRAIC_ROUND_CONTRACT_FIXTURE', path=[],
        angles=tuple((F(-1), F(1)) for _ in range(9)),
        positions=tuple((F(-2), F(2)) for _ in range(18)),
        scalar=tuple((F(-1), F(1)) for _ in range(36)),
        differences={pair: ((F(-2), F(2)), (F(-2), F(2))) for pair in combinations(range(9), 2)},
        diagonal={pair: ((F(-3), F(3)), (F(-3), F(3))) for pair in combinations(range(9), 2)})


class Context:
    def __init__(self, rows, mode='ordinary'):
        self.rows, self.mode = rows, mode
        self.R = SimpleNamespace(infer_angles=self.infer_angles)
        self.K = SimpleNamespace(analytic=self.analytic)

    def collect(self, state):
        return self.rows, (F(2),) * 54, deepcopy(state), None

    def infer_angles(self, angles, scalar):
        if self.mode == 'frame':
            return None, 'literal frame-contract control', [dict(control='frame')]
        return angles, None, []

    def analytic(self, angles):
        answer = [(F(-1), F(1)) for _ in range(36)]
        if self.mode == 'analytic':
            answer[0] = (F(2), F(3))
        return tuple(answer)


class Adapter:
    def __init__(self, context):
        self.context = context

    def rebuild(self, state, literals):
        return ({row['index']: self.context.rows[row['index']] for row in literals},
            (F(2),) * 54, deepcopy(state))

    def infer_angles(self, angles, scalar):
        return self.context.infer_angles(angles, scalar)

    def analytic(self, angles):
        return self.context.analytic(angles)


def main():
    def row(coefficients, rhs, name):
        return tuple((k, F(v)) for k, v in coefficients), F(rhs), PREFIX + name
    fixtures = [
        ('open_signed_grid', 'ordinary', [
            row([(0, 1), (0, 1), (0, -1)], F(1001, 1000), 'scalar_upper'),
            row([(1, -1)], F(-1, 7), 'scalar_lower'),
            row([(2, 1), (0, -1)], F(3, 7), 'difference_upper'),
            row([(16, -1), (14, 1), (17, 1), (15, -1)], F(-1, 3), 'diagonal_lower')], None),
        ('empty_scalar', 'ordinary', [row([(0, 1)], -3, 'empty')], 'proved_empty_scalar'),
        ('empty_difference_last_pair', 'ordinary', [
            row([(2, 1), (0, -1)], -3, 'pair_01'),
            row([(17, 1), (15, -1)], -3, 'pair_78')], 'proved_empty_difference'),
        ('empty_diagonal_last_pair', 'ordinary', [
            row([(2, 1), (0, -1), (3, 1), (1, -1)], -4, 'pair_01'),
            row([(16, 1), (14, -1), (17, -1), (15, 1)], -4, 'pair_78')], 'proved_empty_diagonal'),
        ('frame_terminal', 'frame', [row([(0, 1)], 1, 'upper')], 'proved_frame_contradiction'),
        ('analytic_terminal', 'analytic', [row([(0, 1)], 1, 'upper')], 'proved_empty_analytic_frame'),
    ]
    results, records = [], []
    for name, mode, rows, expected in fixtures:
        state = initial()
        context = Context(rows, mode)
        after, bound, terminal = DIRECT.bound_round(ENGINE, context, state, (PREFIX,))
        assert bound is not None and bound['proposals']
        record = dict(status='CANDIDATE_CLOSED' if terminal else 'OPEN',
            initial=CORE.state_view(state), rounds=[bound])
        if terminal:
            assert terminal['kind'] == expected
            record['terminal'] = terminal
        else:
            assert expected is None
            record['final'] = CORE.state_view(after)
        audit, checked = CORE.check_record(record, state, Adapter(context))
        assert (checked is None) == (terminal is not None)
        if terminal and terminal['kind'] in ('proved_empty_difference', 'proved_empty_diagonal'):
            assert terminal['pair'] == [7, 8] and terminal['axis'] == 1
        results.append(dict(name=name, audit=audit, terminal=terminal))
        records.append((record, state, context))
    record, state, context = records[0]
    damaged = []
    def reject(label, value, test_state=state, test_context=context):
        try:
            CORE.check_record(value, test_state, Adapter(test_context))
        except (AssertionError, KeyError, ValueError):
            damaged.append(label)
        else:
            raise AssertionError(('damaged direct certificate accepted', label))
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['weights'][0][1] += 1
    reject('wrong_unit_multiplier', bad)
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['weights'][0][1] = -1
    reject('negative_multiplier', bad)
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['summed_rhs'] = '99'
    reject('wrong_exact_rhs', bad)
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['residual_correction'] = '1'
    reject('invented_residual_payment', bad)
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['upper'] = str(F(bad['rounds'][0]['proposals'][0]['upper']) - F(1, 1 << 20))
    reject('wrong_downward_grid', bad)
    bad = deepcopy(record); bad['rounds'][0]['proposals'][0]['objective'][0][1] *= -1
    reject('wrong_objective_sign', bad)
    bad = deepcopy(record); bad['rounds'][0]['printed_rows'][0]['rhs'] = '0'
    reject('changed_literal_row', bad)
    for index in (1, 2, 3, 4, 5):
        original, state_i, context_i = records[index]
        bad = deepcopy(original); bad['terminal']['kind'] = 'wrong_terminal'
        reject('wrong_' + fixtures[index][0] + '_witness', bad, state_i, context_i)
    state = initial()
    context = Context([(((0, F(1)),), F(-3), 'unapproved_source_prefix')])
    after, bound, terminal = DIRECT.bound_round(ENGINE, context, state, (PREFIX,))
    assert bound is None and terminal is None and CORE.state_view(after) == CORE.state_view(state)
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
    report = dict(status='PASS_DIRECT_SHARED_BOUND_STANDARD_ROUND_CONTRACT_CONTROLS',
        exact_fixture_cases=results, rejected_damages=damaged,
        explicit_prefix_allow_list_exercised=True, numerical_solves=0,
        physical_original_proof_not_claimed=True,
        real_physical_first_use_replayed_separately=True,
        files={str(Path(p).resolve()):sha(p) for p in (__file__, DIRECT.__file__, CORE.__file__)},
        new_original_cells=0, new_masks=0)
    output = Path(__file__).resolve().parent / 'DIRECT_SHARED_BOUND_ROUND_EXACT_CONTROLS.json'
    assert not output.exists()
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(dict(status=report['status'], cases=len(results), rejected=len(damaged),
        output=str(output), sha256=sha(output)), indent=2))


if __name__ == '__main__':
    main()
