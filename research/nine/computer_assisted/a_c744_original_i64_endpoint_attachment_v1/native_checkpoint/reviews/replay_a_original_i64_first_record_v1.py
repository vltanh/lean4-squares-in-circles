#!/usr/bin/env python3
"""Fresh independent arithmetic on the stored whole-original direct-use record.

The older source proofs and new 813-deduction source are explicitly reused;
their exact identities and whole-original physical attachment are rechecked.
No discovery producer or optimization package is imported.
"""
if not __debug__:
    raise RuntimeError('Exact replay requires assertions.')
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib
import json
import sys

ROOT = Path('/workspace/scratch/f9f48fcfb253')
BASE = ROOT / 'ac_work/recovery_20261105_reset2'
FAMILY = BASE / 'a_c744_original_i64_bounds_v2'
sys.path.insert(0, str(FAMILY))
import independent_original_i64_bounds as I
import independent_direct_use_adapter as A
import independent_physical_sat_diagonal_replay as CORE

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main(output):
    assert not output.exists()
    frozen = FAMILY / 'SOURCE_BINDINGS.json'
    assert sha(frozen) == '93d79d81b6f9f4b2499220b75aca0e6c2c400829261ff783a6ff068fa4301e78'
    source_files = json.loads(frozen.read_text())['files']
    for name, expected in source_files.items():
        assert sha(FAMILY / name) == expected
    producer_report = BASE / 'A_C744_ORIGINAL_I64_FIRST_DIRECT_USE_V3.json'
    assert sha(producer_report) == '3fc7996b0a2571cfd2d232d5b3811f4d27b39ced63c1b4c9330d551c1ad5f481'
    prior = json.loads(producer_report.read_text())
    for name in ('source_sha256', 'independent_loaded_dependency_sha256'):
        for path, expected in prior[name].items():
            assert sha(path) == expected
    binding = I.verify_binding()
    whole = I.read(binding['whole_original_parent']['path'])
    value = whole['record']['final']
    initial = dict(id=value['id'], path=deepcopy(value['path']))
    for name in ('angles', 'positions', 'scalar'):
        initial[name] = tuple(tuple(map(F, interval)) for interval in value[name])
    for name in ('differences', 'diagonal'):
        initial[name] = {tuple(row['pair']): tuple(tuple(map(F, interval)) for interval in row['intervals'])
                         for row in value[name]}
    checker = A.BASE.Checker()
    adapter = A.Adapter(checker, binding)
    initial['choices'] = adapter.choices(initial['path'])
    assert initial['choices'] == (((7, 8), 'inward_row_escape', (4,)),)
    record_path = Path(prior['record']['path'])
    assert sha(record_path) == prior['record']['sha256']
    record = json.loads(record_path.read_text())
    assert record['initial'] == CORE.state_view(initial)
    assert record['original_path'] == I.ORIGINAL_PATH
    audit, final = CORE.check_record(record, initial, adapter)
    assert final is not None and record['status'] == 'OPEN'
    assert CORE.state_view(final) == prior['certified_final_state']
    assert audit == prior['ordinary_exact_audit']
    assert adapter.endpoint_uses == 268 and adapter.height_uses == 0
    assert len(record['rounds']) == 1 and len(record['rounds'][0]['proposals']) == 268
    for proposal in record['rounds'][0]['proposals']:
        assert len(proposal['weights']) == 1 and proposal['weights'][0][1] == CORE.DENOMINATOR
        assert proposal['residual_coefficients'] == [] and proposal['residual_correction'] == '0'
    for name, expected in source_files.items():
        assert sha(FAMILY / name) == expected
    assert not any(name in sys.modules for name in ('numpy', 'scipy', 'highspy', 'original_i64_bound_rows'))
    result = dict(status='PASS_ROOT_FRESH_EXACT_WHOLE_ORIGINAL_I64_DIRECT_RECORD',
        original_id=I.TARGET, original_path=I.ORIGINAL_PATH, scope=I.SCOPE,
        original_initial_and_inherited_choice_preserved=True,
        family_source_binding_sha256=sha(frozen), premise_binding_sha256=I.BINDING_SHA,
        record_sha256=sha(record_path), earlier_direct_report_sha256=sha(producer_report),
        exact_audit=audit, endpoint_row_occurrences=268, positive_unit_weight_deductions=268,
        zero_residual_exact=True, final_state_matches=True, final_status='OPEN',
        fresh_268_deduction_arithmetic=True, historical_sources_reused_explicitly=True,
        old_A1_or_813_source_arithmetic_repeated=False, numerical_producer_imported=False,
        source_review='whole-original I64 implication and all 414 endpoint expansions read in full',
        current_I_slope_interval=['-1', '1'], unconditional_I70_promotion=False,
        helper_sha256=sha(__file__), new_original_cells=0, new_masks=0)
    with output.open('x') as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write('\n')
    print(json.dumps(dict(status=result['status'], report_sha256=sha(output), endpoint_rows=268)))

if __name__ == '__main__':
    assert len(sys.argv) == 2
    main(Path(sys.argv[1]))
