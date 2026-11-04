#!/usr/bin/env python3
"""Portable exact recovery, full-nine boundary and rational emitter replay."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile, time

HERE = Path(__file__).resolve().parent
SOURCE_SHA = '922b2aec0df9433ed080baf551d4847690c98d0311facd7d585e6e75dbe91ffe'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    binding_path = HERE / 'PUBLICATION_BINDINGS.json'
    binding_bytes = binding_path.read_bytes()
    binding = json.loads(binding_bytes)
    assert binding['schema'] == 'full_mask_continuation_entrypoints_publication_v1'
    assert binding['source_binding_sha256'] == SOURCE_SHA
    assert sha(HERE / 'SOURCE_BINDINGS.json') == SOURCE_SHA
    frozen = {}
    for relative, digest in binding['immutable_inputs'].items():
        path = (HERE / relative).resolve()
        assert path.is_relative_to(HERE) and sha(path) == digest
        frozen[path] = digest
    def run(script, *arguments):
        result = subprocess.run([sys.executable, '-B', '-S', str(HERE / script),
                                 *map(str, arguments)], cwd=HERE,
                                capture_output=True, text=True, check=True)
        return result.stdout
    with tempfile.TemporaryDirectory(prefix='full_mask_exact_') as directory:
        work = Path(directory)
        integrity = json.loads(run('verify_recovery_index.py'))
        four = work / 'four.json'
        single = work / 'single.json'
        run('four_full_nine_mask_closed_q_boundary_witnesses/four_mask_closed_q_boundary/verify_closed_q_boundary_witnesses.py',
            '--negative-controls', '--output', four)
        run('mask_11100_full_nine_closed_q_boundary/mask_11100_closed_q_boundary/verify_11100_boundary.py',
            '--negative-controls', '--output', single)
        four_report, single_report = json.loads(four.read_text()), json.loads(single.read_text())
        assert four_report['status'] == single_report['status'] == 'PASS'
        assert len(four_report['negative_controls_rejected']) == len(single_report['negative_controls_rejected']) == 5
        assert single_report['all_marked_cones_and_bits_strict'] is True
        seven = json.loads(run('verify_seven_original_table.py'))
        assert seven['passed'] is True and seven['covered_masks'] == 24
        assert seven['explicit_rational_predicate_checks'] == 882
        emitter = run('test_emit_fixed_mask.py')
        assert 'PASS:' in emitter and 'No nine-square UNSAT proof.' in emitter
    assert binding_path.read_bytes() == binding_bytes
    assert all(sha(path) == digest for path, digest in frozen.items())
    report = dict(status='PASS_PORTABLE_FULL_MASK_ENTRYPOINTS_AND_BOUNDARIES',
                  immutable_inputs_checked=len(frozen),
                  source_binding_sha256=SOURCE_SHA,
                  publication_binding_sha256=sha(binding_path),
                  recovered_source_files=integrity['source_files'],
                  extracted_boundary_members=integrity['extracted_boundary_members'],
                  closed_Q_boundary_masks=['101/11','111/01','111/10','111/11','111/00'],
                  damaged_boundary_controls_rejected=10,
                  selected_seven_masks=24, selected_seven_rational_assertions=882,
                  rational_emitter_controls_passed=True,
                  full_mask_solver_called=False, new_original_cells=0, new_masks=0,
                  lean_lake_ci_run=False, seconds=time.monotonic()-started)
    if args.output:
        assert not args.output.exists()
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
