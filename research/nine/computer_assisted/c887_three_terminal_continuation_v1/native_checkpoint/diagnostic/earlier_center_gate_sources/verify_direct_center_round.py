#!/usr/bin/env python3
"""Independent leaf/source attachment and unchanged C ordinary-round replay."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import argparse
import json
import historical_leaf_source as H


def verify_candidate(candidate, core, adapter, initial):
    assert candidate['schema'] == 'C887_leaf47_direct_center_candidate_v1'
    assert candidate['scope'] == 'ONLY_THE_CERTIFIED_C887_LEAF_47_DOMAIN'
    assert candidate['source_leaf_node_sha256'] == H.NODE_SHA
    assert candidate['new_original_cells'] == candidate['new_masks'] == 0
    record = candidate['record']
    assert record['id'] == H.TARGET and record['original_path'] == H.ORIGINAL_PATH
    assert record['initial'] == core.state_view(initial)
    assert record['status'] == 'OPEN' and len(record['rounds']) == 1
    rr = record['rounds'][0]
    assert len(rr['printed_rows']) == 2 and len(rr['proposals']) == 1
    proposal = rr['proposals'][0]
    assert (proposal['kind'], proposal['key'], proposal['sign'], proposal['objective']) == ('scalar', 9, 1, [[9, 1]])
    centers = [r for r in rr['printed_rows'] if r['name'].startswith('physical_center_disk_')]
    old = [r for r in rr['printed_rows'] if not r['name'].startswith('physical_center_disk_')]
    assert len(centers) == len(old) == 1
    assert centers[0]['coefficients'] == [[8, '-807/1024'], [9, '1']]
    assert F(centers[0]['rhs']) == F(2123205927653, 1099511627776)
    assert old[0]['coefficients'] == [[8, '1']] and F(old[0]['rhs']) == initial['positions'][8][1]
    assert proposal['weights'] == [[centers[0]['index'], 1 << 40], [old[0]['index'], 807 * (1 << 30)]]
    audit, after = core.check_record(record, initial, adapter)
    assert audit['status'] == 'PASS_CERTIFIED_PHYSICAL_STATE_OPEN'
    assert (audit['rounds'], audit['deductions'], audit['printed_rows_checked']) == (1, 1, 2)
    assert after is not None and after['id'] == H.TARGET and after['path'] == initial['path']
    assert after['positions'][9][1] == F(1249037, 1048576) < initial['positions'][9][1]
    assert proposal['residual_coefficients'] == [] and F(proposal['residual_correction']) == 0
    return audit, after


def main():
    if not __debug__:
        raise RuntimeError('Exact replay requires assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); here = Path(__file__).resolve().parent
    packet = args.packet.resolve(); output = args.output.resolve(); source = args.candidate.resolve()
    raw = source.read_bytes(); candidate = json.loads(raw)
    core, adapter, initial, evidence, inventory, transport = H.setup(packet, output, here)
    assert candidate['source_evidence'] == evidence
    audit, after = verify_candidate(candidate, core, adapter, initial)
    rejected = []
    changes = (
        ('foreign_original', lambda c: c['record']['initial'].__setitem__('id', 'foreign')),
        ('missing_leaf_restriction', lambda c: c['record']['initial']['path'].pop()),
        ('changed_inherited_x_upper', lambda c: c['record']['initial']['positions'][8].__setitem__(1, '-1')),
        ('changed_center_support', lambda c: c['record']['rounds'][0]['printed_rows'][1].__setitem__('rhs', '1')),
        ('changed_multiplier', lambda c: c['record']['rounds'][0]['proposals'][0]['weights'][1].__setitem__(1, 1)),
        ('overstated_endpoint', lambda c: c['record']['rounds'][0]['proposals'][0].__setitem__('upper', '1')),
        ('deleted_premise', lambda c: c['record']['rounds'][0]['printed_rows'].pop()),
        ('whole_original_scope', lambda c: c.__setitem__('scope', 'WHOLE_ORIGINAL')))
    for label, change in changes:
        damaged = deepcopy(candidate); change(damaged)
        try:
            verify_candidate(damaged, core, adapter, initial)
        except (AssertionError, ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError(('damaged record accepted', label))
    assert len(rejected) == 8
    H.recheck(packet, here, inventory)
    assert source.read_bytes() == raw
    result = dict(status='PASS_FRESH_ORDINARY_C887_LEAF47_DIRECT_CENTER_BOUND',
        original_id=H.TARGET, original_path=H.ORIGINAL_PATH, leaf_index=47,
        scope='ONLY_THE_CERTIFIED_C887_LEAF_47_DOMAIN', full_leaf_path=initial['path'],
        candidate_sha256=H.sha(source), unchanged_arithmetic_core_sha256=H.CORE_SHA,
        independent_center_decoder_sha256=H.CENTER_SHA, source_evidence=evidence,
        fresh_ordinary_round_audit=audit, old_y_upper=str(initial['positions'][9][1]),
        new_y_upper=str(after['positions'][9][1]), exact_improvement=str(initial['positions'][9][1] - after['positions'][9][1]),
        new_center_rows_used=1, existing_proved_coordinate_bounds_used=1, residual_correction='0',
        final_state=core.state_view(after), malformed_controls_rejected=rejected,
        historical_57_round_arithmetic_repeated=False, source_proof_reuse_explicit=True,
        numerical_solver_called=False, whole_original_bound_or_exclusion_claimed=False,
        all_nine_originals_retained=True, original_corners=36, original_pairs=36, marked_cones=5,
        closed_shared_faces_retained=True, new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    path = output / 'EXACT_REPLAY.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(status=result['status'], exact_report_sha256=H.sha(path),
        old_y_upper=result['old_y_upper'], new_y_upper=result['new_y_upper'],
        exact_improvement=result['exact_improvement'], malformed_controls_rejected=len(rejected),
        historical_arithmetic_repeated=False, numerical_solver_called=False)), flush=True)


if __name__ == '__main__':
    main()
