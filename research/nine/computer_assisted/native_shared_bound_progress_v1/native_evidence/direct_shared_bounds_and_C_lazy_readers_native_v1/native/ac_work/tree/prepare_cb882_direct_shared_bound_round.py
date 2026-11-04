#!/usr/bin/env python3
"""Produce one solver-free standard bound round on the real Cb component1 seed."""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, os, sys, time
for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[key] = '1'
HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parent.parent
SUPPORT = WORKSPACE / 'd_work/cb882_shared_height_bounds'
sys.path.insert(0, str(SUPPORT))
import cb882_shared_height_bounds_runtime as MODEL
import direct_shared_bound_round as DIRECT


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = SUPPORT / 'prepared_seed_trees/component_1'
    raw = (source / 'manifest.json').read_bytes()
    manifest = json.loads(raw)
    assert manifest['component'] == 1 and len(manifest['nodes']) == 1
    node = manifest['nodes'][0]
    assert node['parent'] is None and not node['children']
    old = json.loads((source / node['file']).read_text())
    assert sha(source / node['file']) == node['sha256']
    assert old['status'] == 'OPEN'
    seed_path = Path(manifest['parent']['path'])
    assert sha(seed_path) == manifest['parent']['sha256']
    seed = MODEL.read_seed(seed_path)
    context = MODEL.Context(seed)
    state = MODEL.state_from_view(old['final'])
    started = time.monotonic()
    after, bound, terminal = DIRECT.bound_round(MODEL.E, context, state,
        ('certified_cb882_root_bound_',))
    assert bound is not None and bound['proposals']
    assert terminal is None and after is not None
    result = dict(old)
    result.update(rounds=deepcopy(old['rounds']) + [bound], final=MODEL.stateview(after),
        direct_shared_bound_deductions=len(bound['proposals']), numerical_solves=0)
    for name in ('point', 'phase', 'best_pairs'):
        result.pop(name, None)
    (output / node['file']).write_text(json.dumps(result, indent=2) + '\n')
    (output / 'PREVIOUS_COMPLETE_MANIFEST.json').write_bytes(raw)
    node['sha256'] = sha(output / node['file'])
    manifest['source_sha256'][str(output / 'PREVIOUS_COMPLETE_MANIFEST.json')] = sha(output / 'PREVIOUS_COMPLETE_MANIFEST.json')
    for path in (__file__, DIRECT.__file__):
        manifest['source_sha256'][str(Path(path).resolve())] = sha(path)
    manifest['direct_shared_bound_round'] = dict(numerical_solves=0,
        source_row_prefix='certified_cb882_root_bound_',
        unchanged_generic_diagonal_round_schema=True)
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(dict(status='PREPARED_REAL_CB882_DIRECT_SHARED_BOUND_ROUND',
        deductions=len(bound['proposals']), printed_rows=len(bound['printed_rows']),
        numerical_solves=0, seconds=time.monotonic()-started,
        manifest_sha256=sha(output / 'manifest.json'), new_original_cells=0, new_masks=0), indent=2))


if __name__ == '__main__':
    main()
