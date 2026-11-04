#!/usr/bin/env python3
"""Exercise checkpoint composition using an already replayed ordinary round.

The numerical callback is deliberately a stub: this is a record-preservation
control, not another physical or LP proof.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import search_with_direct_shared_bound_round as WRAP


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / 'cb882_component1_direct_shared_bound_round/node_00000.json'


def main():
    raw = FIXTURE.read_bytes()
    fixture = json.loads(raw)
    assert fixture['status'] == 'OPEN' and len(fixture['rounds']) == 1
    initial, after = deepcopy(fixture['initial']), deepcopy(fixture['final'])
    ordinary = deepcopy(fixture['rounds'][0])
    assert len(ordinary['proposals']) == 158
    engine = SimpleNamespace(stateview=deepcopy)
    original_round = WRAP.DIRECT.bound_round
    original_precheck = WRAP.PRECHECK.may_improve
    results = []
    try:
        WRAP.PRECHECK.may_improve = lambda *args: True
        WRAP.DIRECT.bound_round = lambda *args: (deepcopy(after), deepcopy(ordinary), None)
        for status in ('OPEN', 'CANDIDATE_CLOSED', 'NO_NUMERICAL_CONCLUSION'):
            seen, calls = [], []
            partial = dict(status='RUNNING', initial=deepcopy(after), rounds=[],
                           latest=deepcopy(after), terminal=None, seconds=2)
            result = dict(status=status, initial=deepcopy(after), rounds=[], seconds=3)
            if status == 'OPEN':
                result.update(final=deepcopy(after), point=[123], phase='fresh-phase')
            elif status == 'CANDIDATE_CLOSED':
                result.update(terminal_state=deepcopy(after), terminal={'kind': 'fixture-terminal'})
            else:
                result.update(diagnostic={'kind': 'solver_no_conclusion'})
            untouched = deepcopy(result)

            def search(state, checkpoint):
                calls.append(deepcopy(state))
                assert state == after
                checkpoint(deepcopy(partial))
                return result, deepcopy(after), [123]

            combined, _, _ = WRAP.run(engine, object(), initial, [], ('source_',), search, seen.append)
            assert calls == [after] and len(seen) == 2
            assert seen[0]['status'] == 'OPEN' and seen[0]['final'] == after
            assert seen[1]['status'] == 'RUNNING' and seen[1]['latest'] == after
            for record in seen + [combined]:
                assert record['initial'] == initial and record['rounds'] == [ordinary]
            assert combined['status'] == status and result == untouched
            if status == 'OPEN':
                assert combined['point'] == [123] and combined['phase'] == 'fresh-phase'
            elif status == 'CANDIDATE_CLOSED':
                assert combined['terminal_state'] == after
            results.append('fresh_callback_' + status)

        seen = []
        def fails(state, checkpoint):
            assert seen and seen[0]['final'] == after
            raise RuntimeError('controlled callback interruption')
        try:
            WRAP.run(engine, object(), initial, [], ('source_',), fails, seen.append)
            raise AssertionError('interruption suppressed')
        except RuntimeError as error:
            assert str(error) == 'controlled callback interruption'
        assert len(seen) == 1 and seen[0]['rounds'] == [ordinary]
        results.append('prefix_persisted_before_interruption')

        for with_round in (False, True):
            seen = []
            WRAP.DIRECT.bound_round = lambda *args: (
                None, deepcopy(ordinary) if with_round else None, {'kind': 'fixture-terminal'})
            def forbidden(*args):
                raise AssertionError('numerical callback after terminal')
            closed, state, point = WRAP.run(
                engine, object(), initial, [], ('source_',), forbidden, seen.append)
            assert state is point is None and seen == [closed]
            assert closed['initial'] == initial and closed['status'] == 'CANDIDATE_CLOSED'
            assert closed['rounds'] == ([ordinary] if with_round else [])
            results.append('direct_terminal_' + str(with_round))

        WRAP.DIRECT.bound_round = lambda *args: (args[2], None, None)
        called = []
        def unchanged(state, checkpoint):
            called.append(state is initial)
            return {'unchanged': True}, state, None
        result = WRAP.run(engine, object(), initial, [], ('source_',), unchanged)
        assert called == [True] and result[0] == {'unchanged': True}
        results.append('no_direct_improvement_preserves_original_search')

        WRAP.PRECHECK.may_improve = lambda *args: False
        WRAP.DIRECT.bound_round = forbidden
        called.clear()
        WRAP.run(engine, object(), initial, [], ('source_',), unchanged)
        assert called == [True]
        results.append('negative_precheck_skips_collection')
    finally:
        WRAP.DIRECT.bound_round = original_round
        WRAP.PRECHECK.may_improve = original_precheck
    assert FIXTURE.read_bytes() == raw
    report = dict(
        status='PASS_DIRECT_SHARED_ROUND_CHECKPOINT_COMPOSITION_CONTROLS',
        scope='DISCOVERY_RECORD_PRESERVATION_NOT_NEW_PHYSICAL_ARITHMETIC',
        cases=results, case_count=len(results), fixture_sha256=hashlib.sha256(raw).hexdigest(),
        wrapper_sha256=hashlib.sha256(Path(WRAP.__file__).read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        fixture_ordinary_deductions=158, fixture_unchanged=True,
        new_numerical_solves=0, new_original_cells=0, new_masks=0)
    output = HERE / 'DIRECT_SHARED_SEARCH_COMPOSITION_CONTROLS.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
