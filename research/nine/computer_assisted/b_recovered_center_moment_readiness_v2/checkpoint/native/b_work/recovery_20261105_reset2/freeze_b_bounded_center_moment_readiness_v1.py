#!/usr/bin/env python3
"""Freeze two held, bounded exact-moment B continuations; start no search."""
from pathlib import Path
import hashlib
import json
import os

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'b_work/recovery_20261105'
DRIVER_SHA = 'ab428e2fd19cb0645b9f609c52a183bfdf3d77ec619e9b3990f9e12be91f8545'
RUNTIME_SHA = 'e5d4a8af92af70607d643f5b81fe78a7cb6710377c2ac0fe33c64433fd09761d'
PARITY_SHA = 'e24f62174bf0f1da13dc1157e8f92341b7a9f0fbd76d14f93a4092a1f97d66d6'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    pins = {}

    def pin(path, expected=None):
        path = Path(path).resolve(); digest = sha(path)
        if expected is not None:
            assert digest == expected, str(path)
        assert str(path) not in pins or pins[str(path)] == digest
        pins[str(path)] = digest
        return path

    def read(path, expected=None):
        return json.loads(pin(path, expected).read_text())

    previous = read(OLD / 'B_ATOMIC_ACCEPTED_CENTER_RUNTIME_SOURCE_FREEZE.json',
        'dbb1fd76098c2868375299c67ba589001d453008109bdf46f7bfc2f72d13b399')
    for path, digest in previous['files'].items():
        pin(path, digest)
    parity = read(HERE / 'B16_ACTUAL_EXACT_MOMENT_LITERAL_PARITY.json', PARITY_SHA)
    assert parity['status'] == 'PASS_COMPLETE_EXACT_MOMENT_LITERAL_PARITY_ON_FRESH_B16_CALLER'
    assert parity['rows_compared'] == 3072 and parity['pair_intervals'] == 36
    assert parity['complete_coefficients_rhs_names_and_order_equal']
    assert len(parity['malformed_callers_rejected']) == 4 and parity['numerical_LP_solves'] == 0
    for path, digest in parity['source_sha256'].items():
        pin(path, digest)
    driver = pin(ROOT / 'b_work/resume_b_center_exact_moment_atomic_tree_v1.py', DRIVER_SHA)
    runtime = pin(ROOT / 'b_work/b_center_exact_moment_runtime_v1.py', RUNTIME_SHA)
    prior_driver = pin(ROOT / 'b_work/resume_b_five_proxy_round_atomic_center_tree_v1.py',
        '02334833b824a58d49fcd316d154a59bc61866b0b3428f8fe7dcac12799af786')
    assert driver.read_text().replace('import b_center_exact_moment_runtime_v1 as RT\n',
        'import b_accepted_center_disk_runtime_v1 as RT\n') == prior_driver.read_text()
    for path in (HERE / 'B_MOMENT_DRIVER_FROM_ACCEPTED_CENTER.diff',
                 HERE / 'B_CENTER_EXACT_MOMENT_BOUNDED_CONTINUATION.md', __file__):
        pin(path)
    configurations = [
        ('B16A', OLD / 'reassembled_B16a_published_prefix_v1',
         HERE / 'B16A_center_exact_moment_prepared_seed_v1',
         HERE / 'RESTORED_B16A_45_ACCEPTED_CENTER_FRESH_EXACT_REPLAY.json',
         '6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa',
         86994, 29887, (45, 2, 28, 21, 2324, 7865),
         'b16a_restored_center_moment_bounded_v1', 'HOLD_EXTERNAL_SAME_ORIGINAL_SEARCH_ACTIVE'),
        ('B462', HERE / 'B462_preserved_two_round_whole_attachment_v1',
         HERE / 'B462_center_exact_moment_prepared_seed_v1',
         HERE / 'B462_PRESERVED_TWO_ROUND_FRESH_EXACT_REPLAY.json',
         '6bbedffa6c286313e4f904cd9a8c134969cb7b22284585a3fd61b627dc2d53ba',
         83098, 17902, (1, 0, 1, 2, 214, 490),
         'b462_restored_center_moment_bounded_v1', 'HOLD_NUMERICAL_CAPACITY_AND_ROOT_LAUNCH_REVIEW')]
    cases = []
    for label, source, seed, report_path, report_sha, exact_session, prepare_session, counts, output_name, hold in configurations:
        a = read(source / 'manifest.json'); b = read(seed / 'manifest.json')
        assert a['parent'] == b['parent'] and a['nodes'] == b['nodes']
        assert a['accepted_geometric_sources'] == b['accepted_geometric_sources']
        assert a['completed'] is b['completed'] is True and a['status'] == b['status'] == 'OPEN'
        assert all(b['sources'][path] == digest for path, digest in a['sources'].items())
        for e in a['nodes']:
            p = pin(source / e['file'], e['sha256']); q = pin(seed / e['file'], e['sha256'])
            assert p.read_bytes() == q.read_bytes()
        prev = pin(seed / 'PREVIOUS_COMPLETE_MANIFEST.json', sha(source / 'manifest.json'))
        assert prev.read_bytes() == (source / 'manifest.json').read_bytes()
        for group in ('sources', 'accepted_geometric_sources'):
            for path, digest in b[group].items():
                pin(path, digest)
        r = read(report_path, report_sha)
        assert r['status'] == 'PASS_PARTIAL_PHYSICAL_TREE' and not r['complete'] and not r['whole_original_proved']
        assert r['certificate_sha256'] == sha(source / 'manifest.json')
        assert tuple(r[k] for k in ('nodes', 'excluded_leaves', 'open_leaves',
            'local_rounds', 'local_deductions', 'local_printed_rows')) == counts
        assert r['entire_registered_original_domain_retained'] is (label == 'B462')
        for path, digest in r['source_sha256'].items():
            pin(path, digest)
        output = ROOT / 'repo/research/nine/.runs' / output_name
        log = output.with_suffix('.log')
        assert not output.exists() and not log.exists()
        command = ['python', '-B', '-u', str(driver), str(seed), str(output),
            '--packet', str(ROOT / 'b_work/b16a_I32_complete_H_checkpoint'),
            '--rounds', '2', '--existing-rounds', '1', '--proxy-rounds', '0',
            '--max-depth', '24', '--max-new-nodes', '64']
        cases.append(dict(label=label, status=hold, original_id=r['initial_original_id'],
            original_path=r['initial_path'], whole_original_domain_retained=(label == 'B462'),
            source_manifest=str(source / 'manifest.json'), source_manifest_sha256=sha(source / 'manifest.json'),
            prepared_manifest=str(seed / 'manifest.json'), prepared_manifest_sha256=sha(seed / 'manifest.json'),
            nodes=counts[0], excluded_leaves=counts[1], open_leaves=counts[2],
            complete_unions=r['complete_unions'], all_retained_payload_and_cover_bytes_unchanged=True,
            exact_report=str(report_path), exact_report_sha256=report_sha,
            exact_session=exact_session, exact_observed_exit_code=0,
            prepare_only_session=prepare_session, prepare_only_observed_exit_code=0,
            command=command, output=str(output), log=str(log), output_and_log_absent=True,
            numerical_search_started=False, new_original_cells=0, new_masks=0))
    for path, digest in pins.items():
        assert sha(path) == digest, path
    common = dict(schema='B_center_exact_moment_bounded_readiness_v1',
        status='SOURCE_AND_EXACT_CALLER_GATES_PASS_NUMERICAL_START_HELD',
        driver_sha256=DRIVER_SHA, runtime_sha256=RUNTIME_SHA,
        exact_one_import_driver_delta=True, explicit_runtime_engine_identity_checked=True,
        moment_literal_parity_report_sha256=PARITY_SHA, moment_parity_session=77745,
        moment_parity_observed_exit_code=0, moment_rows_compared=3072,
        no_new_mathematical_row_family=True, independent_checker_unchanged=True,
        old_source_files_unchanged=True, cases=cases, files=pins,
        environment=dict(OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1'),
        actual_f_bfree_bytes=os.statvfs(ROOT).f_bfree * os.statvfs(ROOT).f_frsize,
        lost105_or107_suffix_claimed_available=False, numerical_search_started=False,
        new_original_cells=0, new_masks=0, ledger_mutated=False)
    path = HERE / 'B_CENTER_EXACT_MOMENT_BOUNDED_READINESS_FREEZE_V1.json'
    with path.open('x') as f:
        json.dump(common, f, indent=2); f.write('\n')
    for case in cases:
        launch = dict(case, common_source_freeze=dict(path=str(path), sha256=sha(path)),
                      environment=common['environment'])
        target = HERE / f"{case['label']}_CENTER_EXACT_MOMENT_HELD_LAUNCH_V1.json"
        with target.open('x') as f:
            json.dump(launch, f, indent=2); f.write('\n')
    print(json.dumps(dict(status=common['status'], source_freeze_sha256=sha(path),
        source_pins=len(pins), prepared_cases=[c['label'] for c in cases])), flush=True)


if __name__ == '__main__':
    main()
