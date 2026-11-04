#!/usr/bin/env python3
"""One unsplit C887 standard bound fixture; no optimization or live-tree edit."""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import json
import os
import time

for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'

import ac_c887_shared_height_bounds_runtime as MODEL
import direct_shared_bound_round as DIRECT

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'c887_shared_height_bounds_each_round_tree'
SOURCE_SHA = '4ef09829b906836ce9c9c837fccf76870633998e64e43d9ca6d7c88da5ce2b9d'
UNION = HERE / 'c887_whole_DG_shave'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    assert not output.exists()
    raw = (SOURCE / 'manifest.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA
    manifest = json.loads(raw)
    root = deepcopy(manifest['nodes'][0])
    assert root['parent'] is None and root['restriction'] is None and root['index'] == 0
    assert sha(SOURCE / root['file']) == root['sha256']
    old = json.loads((SOURCE / root['file']).read_text())
    assert old['status'] == 'OPEN'
    assert old['initial']['path'] == old['final']['path'] == manifest['original_path']
    original_choices = (((1, 7), 'alternate_four_escape', (1,)),)
    assert MODEL.state_from_view(old['initial'])['choices'] == original_choices
    assert MODEL.state_from_view(old['final'])['choices'] == original_choices
    assert len(old['rounds']) == 3
    context = MODEL.Context(UNION)
    state = MODEL.state_from_view(old['final'])
    started = time.monotonic()
    after, bound, terminal = DIRECT.bound_round(MODEL.E, context, state, (MODEL.ROWS.PREFIX,))
    assert bound is not None and bound['proposals']
    assert terminal is None and after is not None
    result = dict(old)
    result.update(rounds=deepcopy(old['rounds']) + [bound], final=MODEL.stateview(after),
        direct_shared_bound_deductions=len(bound['proposals']), numerical_solves=0,
        fixture_scope='One unsplit original-root bound record; all live covers preserved separately')
    for name in ('point', 'phase', 'best_pairs'):
        result.pop(name, None)
    root['children'] = []
    root.pop('split', None)
    root.pop('complete_children', None)
    root['status'] = 'OPEN'
    output.mkdir(parents=True)
    (output / root['file']).write_text(json.dumps(result, indent=2) + '\n')
    (output / 'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes(raw)
    root['sha256'] = sha(output / root['file'])
    manifest['nodes'] = [root]
    manifest['status'] = 'OPEN'
    manifest['whole_original_height_bound_state'] = context.whole_height_bound_reference
    manifest['source_sha256'].update(MODEL.sources(UNION))
    for path in (__file__, DIRECT.__file__, output / 'PREVIOUS_COMPLETE_MANIFEST.json'):
        manifest['source_sha256'][str(Path(path).resolve())] = sha(path)
    manifest['direct_shared_bound_fixture'] = dict(
        source_manifest_sha256=SOURCE_SHA, source_root_sha256=sha(SOURCE / root['file']),
        source_row_prefix=MODEL.ROWS.PREFIX, numerical_solves=0,
        unchanged_generic_diagonal_round_schema=True,
        original_root_domain_unchanged=True, source_and_live_covers_unchanged=True)
    manifest.pop('snapshot', None)
    manifest.pop('continuation', None)
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    assert sha(SOURCE / 'manifest.json') == SOURCE_SHA
    assert sha(SOURCE / root['file']) == manifest['direct_shared_bound_fixture']['source_root_sha256']
    print(json.dumps(dict(status='PREPARED_REAL_C887_UNSPLIT_DIRECT_SHARED_BOUND_ROUND',
        deductions=len(bound['proposals']), printed_rows=len(bound['printed_rows']),
        numerical_solves=0, seconds=time.monotonic()-started,
        manifest_sha256=sha(output / 'manifest.json'), new_original_cells=0, new_masks=0), indent=2))


if __name__ == '__main__':
    main()
