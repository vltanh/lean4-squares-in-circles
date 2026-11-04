#!/usr/bin/env python3
"""Portable source-bound exact four-product corner controls."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('Exact replay requires assertions')
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
        assert sha(ROOT / name) == digest, name
    with tempfile.TemporaryDirectory(prefix='four_corner_exact_') as temporary:
        work = Path(temporary)
        folder = work / 'global_work/unit_corner_four_rectangles'
        folder.mkdir(parents=True)
        for name in ('physical_unit_four_corner_rows.py',
                     'independent_physical_unit_four_corner_rows.py',
                     'physical_unit_four_corner_separation.py',
                     'check_four_rectangle_corner_rows.py',
                     'FOUR_RECTANGLE_UNIT_CORNER_HAND_PROOF.md'):
            shutil.copy2(ROOT / name, folder / name)
        old = work / 'd_work/unit_frame_corner/physical_unit_corner_rows.py'
        old.parent.mkdir(parents=True)
        shutil.copy2(ROOT / 'accepted_grouped/physical_unit_corner_rows.py', old)
        output = folder / 'replay.json'
        subprocess.run([sys.executable, '-B', '-S', 'check_four_rectangle_corner_rows.py', str(output)],
                       cwd=folder, check=True, capture_output=True, text=True)
        report = json.loads(output.read_text())
        assert report['status'] == 'PASS_EXACT_FOUR_RECTANGLE_UNIT_CORNER_CONTROLS'
        for key, value in dict(literal_rows=3456, exact_physical_residual_identities=3456,
                                accepted_two_rectangle_rows_reproduced=864,
                                original_signed_corners=36, rectangle_choice_patterns=16,
                                damaged_controls_rejected=5).items():
            assert report[key] == value
        for path, digest in report.pop('source_sha256').items():
            assert binding['immutable_inputs'][Path(path).name] == digest
        assert report['accepted_parent_producer_sha256'] == sha(old)
    report.update(status='PASS_PORTABLE_FOUR_PRODUCT_CORNER_ROWS',
                  immutable_inputs_checked=len(binding['immutable_inputs']),
                  premise_bindings_sha256=sha(ROOT / 'PREMISE_BINDINGS.json'),
                  numerical_optimizer_imported=False, lean_lake_ci_run=False)
    rendered = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
