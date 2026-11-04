#!/usr/bin/env python3
"""Source-bound relocated exact controls, with no numerical dependencies."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('Exact verification requires assertions')

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    binding = json.loads((ROOT / 'PREMISE_BINDINGS.json').read_text())
    for name, digest in binding['immutable_inputs'].items():
        assert Path(name).name == name
        assert sha(ROOT / name) == digest, name
    with tempfile.TemporaryDirectory(prefix='original_corner_exact_') as temporary:
        folder = Path(temporary)
        for name in ('physical_corner_disk_rows.py',
                     'independent_physical_corner_disk_rows.py',
                     'check_physical_corner_disk_rows.py',
                     'ADAPTIVE_ORIGINAL_CORNER_DISK_HAND_PROOF.md'):
            shutil.copy2(ROOT / name, folder / name)
        subprocess.run([sys.executable, '-B', '-S', 'check_physical_corner_disk_rows.py'],
                       cwd=folder, check=True, capture_output=True, text=True)
        report = json.loads((folder / 'EXACT_CONTROLS.json').read_text())
        assert report['status'] == 'PASS_EXACT_ORIGINAL_CORNER_DISK_ROWS'
        for key, expected in dict(independently_rebuilt_rows=504,
                                  exact_corner_expansions=31752,
                                  contained_corner_evaluations=30240,
                                  exact_disk_boundary_controls=4032,
                                  damaged_literals_rejected=1008).items():
            assert report[key] == expected
        for path, digest in report.pop('source_sha256').items():
            assert binding['immutable_inputs'][Path(path).name] == digest
    report.update(status='PASS_PORTABLE_ORIGINAL_CORNER_DISK_ROWS',
                  immutable_inputs_checked=len(binding['immutable_inputs']),
                  premise_bindings_sha256=sha(ROOT / 'PREMISE_BINDINGS.json'),
                  numerical_producer_imported=False, lean_lake_ci_run=False)
    rendered = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
