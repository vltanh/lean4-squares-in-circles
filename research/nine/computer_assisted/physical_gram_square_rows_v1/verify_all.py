#!/usr/bin/env python3
"""Source-bound, relocated, standard-library checks of both norm identities."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    binding = json.loads((HERE / 'PREMISE_BINDINGS.json').read_text())
    assert binding['new_original_cells'] == binding['new_masks'] == 0
    for name, digest in binding['source_sha256'].items():
        assert sha(HERE / name) == digest, name
    families = (
        ('pair_frame', 'physical_pair_frame_squares',
         'PHYSICAL_PAIR_FRAME_SQUARES_EXACT_REPLAY.json', 376, 18424),
        ('projection', 'physical_projection_squares',
         'PHYSICAL_PROJECTION_SQUARES_EXACT_REPLAY.json', 184, 13800),
    )
    receipts = {}
    with tempfile.TemporaryDirectory(prefix='physical_gram_exact_') as temporary:
        directory = Path(temporary)
        for family, module, output, rows, evaluations in families:
            names = (module + '.py', 'independent_' + module + '.py',
                     'check_' + module + '.py')
            for name in names:
                shutil.copy2(HERE / name, directory / name)
            subprocess.run([sys.executable, '-B', '-S', names[2]],
                           cwd=directory, check=True, capture_output=True, text=True)
            report = json.loads((directory / output).read_text())
            assert report['status'].startswith('PASS_EXACT_PHYSICAL_')
            assert report['independently_rebuilt_rows'] == rows
            assert report['exact_physical_evaluations'] == evaluations
            assert report['damaged_rows_rejected'] == 8
            assert report['new_original_cells'] == report['new_masks'] == 0
            for path, digest in report['source_sha256'].items():
                assert binding['source_sha256'][Path(path).name] == digest
            receipts[family] = {key: value for key, value in report.items()
                                if key != 'source_sha256'}
    result = dict(status='PASS_SOURCE_BOUND_RELOCATED_PHYSICAL_GRAM_ROWS',
                  source_files_checked=len(binding['source_sha256']),
                  premise_bindings_sha256=sha(HERE / 'PREMISE_BINDINGS.json'),
                  replays=receipts, new_original_cells=0, new_masks=0,
                  lean_lake_ci_invoked=False)
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
