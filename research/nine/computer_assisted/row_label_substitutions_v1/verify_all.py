#!/usr/bin/env python3
"""Hash-bound relocated controls for the two literal row applications."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('Exact verification requires Python assertions')

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    binding = json.loads((ROOT / 'PREMISE_BINDINGS.json').read_text())
    for name, digest in binding['immutable_inputs'].items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert sha(ROOT / relative) == digest, name
    with tempfile.TemporaryDirectory(prefix='literal_row_guard_replay_') as temporary:
        work = Path(temporary)
        for name in ('opposite_abid', 'actual_ab_either_extra'):
            shutil.copytree(ROOT / name, work / name)
        jobs = (
            ('opposite_abid', work / 'opposite_abid/tree',
             'check_opposite_abid_substitution.py',
             'OPPOSITE_ABID_SUBSTITUTION_EXACT_CONTROLS.json',
             dict(guard_states=1458, positive_guards=273,
                  wrong_physical_row_controls_rejected=273)),
            ('actual_ab_either_extra', work / 'actual_ab_either_extra',
             'check_actual_ab_any_extra_guard.py', 'EXACT_GUARD_CONTROLS.json',
             dict(guard_states=12150, positive_guards=1512,
                  correlated_translation_controls=54, damaged_literals_rejected=3024)),
        )
        receipts = {}
        for label, folder, script, report_file, expected in jobs:
            subprocess.run([sys.executable, '-B', '-S', script], cwd=folder,
                           check=True, capture_output=True, text=True)
            report = json.loads((folder / report_file).read_text())
            assert report['status'].startswith('PASS_LITERAL_')
            for key, value in expected.items():
                assert report[key] == value
            assert report['new_original_cells'] == report['new_masks'] == 0
            for path, digest in report['source_sha256'].items():
                relative = str(Path(path).relative_to(work))
                assert binding['immutable_inputs'][relative] == digest
            receipts[label] = {key: value for key, value in report.items()
                               if key != 'source_sha256'}
    result = dict(status='PASS_PORTABLE_LITERAL_ROW_SUBSTITUTIONS',
                  premise_bindings_sha256=sha(ROOT / 'PREMISE_BINDINGS.json'),
                  immutable_inputs_checked=len(binding['immutable_inputs']),
                  replays=receipts, scalar_tables_replayed=False,
                  accepted_scalar_dependencies_required=True,
                  new_original_cells=0, new_masks=0, lean_lake_ci_run=False)
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
