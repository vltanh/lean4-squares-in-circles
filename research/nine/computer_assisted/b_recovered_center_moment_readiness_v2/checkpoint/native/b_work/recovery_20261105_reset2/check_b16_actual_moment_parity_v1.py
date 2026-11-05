#!/usr/bin/env python3
"""Complete literal parity on one freshly replayed physical B16 state; no LP."""
from pathlib import Path
from fractions import Fraction as F
from copy import deepcopy
import hashlib
import json
import sys
import time

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'b_work'))
import b_center_exact_moment_runtime_v1 as RT
from run_coupled_sat_cover import restore


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    proof = HERE / 'RESTORED_B16A_45_ACCEPTED_CENTER_FRESH_EXACT_REPLAY.json'
    assert sha(proof) == '6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa'
    exact = json.loads(proof.read_text())
    tree = ROOT / 'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1'
    manifest = json.loads((tree / 'manifest.json').read_text())
    assert sha(tree / 'manifest.json') == exact['certificate_sha256']
    entry = manifest['nodes'][0]; node_path = tree / entry['file']
    assert sha(node_path) == entry['sha256']
    node = json.loads(node_path.read_text())
    assert node['index'] == node['depth'] == 0 and node['parent'] is None
    assert node['record']['status'] == 'OPEN'
    for path, expected in RT.source_bindings().items():
        assert sha(path) == expected
    ctx = RT.Context(ROOT / 'b_work/b16a_I32_complete_H_checkpoint')
    assert RT.E is RT.BASE.E
    state = restore(ctx, node['record'])
    base, bounds, positions, scalar, differences, guards = ctx.K.rebuild(state['path'], state['angles'],
        state['positions'], state['choices'], state['scalar'], state['differences'])
    assert len(differences) == 36
    before = time.monotonic()
    expected = ctx.original_area_moment_generator(differences, matrices=ctx.default_matrices)
    old_seconds = time.monotonic() - before
    before = time.monotonic()
    actual = ctx.AR.generate_linear(differences, matrices=ctx.default_matrices)
    new_seconds = time.monotonic() - before
    assert actual == expected and len(actual) == 3072
    cached = ctx.AR.generate_linear(differences, matrices=ctx.default_matrices)
    assert cached == expected and cached is not actual
    actual.pop()
    assert ctx.AR.generate_linear(differences, matrices=ctx.default_matrices) == expected
    rejected = []
    def deny(name, function):
        try:
            function()
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(('Invalid optimization caller accepted', name))
    missing = dict(differences); missing.pop((0, 1))
    deny('missing_original_pair', lambda: ctx.AR.generate_linear(missing, matrices=ctx.default_matrices))
    deny('nonstable_matrix_iterator', lambda: ctx.AR.generate_linear(differences, matrices=iter(ctx.default_matrices)))
    deny('different_subset_size_sequence', lambda: ctx.AR.generate_linear(differences, counts=(4, 5), matrices=ctx.default_matrices))
    old_helper = ctx.AR.lower_bound
    ctx.AR.lower_bound = lambda *args: F(0)
    try:
        deny('mutated_lower_bound_helper', lambda: ctx.AR.generate_linear(differences, matrices=ctx.default_matrices))
    finally:
        ctx.AR.lower_bound = old_helper
    assert ctx.AR.generate_linear(differences, matrices=ctx.default_matrices) == expected
    encoded = json.dumps(expected, default=str, separators=(',', ':')).encode()
    sources = RT.source_bindings()
    for path in (__file__, restore.__code__.co_filename, ctx.AR.__file__, tree / 'manifest.json', node_path, proof):
        sources[str(Path(path).resolve())] = sha(path)
    for path, digest in sources.items():
        assert sha(path) == digest
    result = dict(status='PASS_COMPLETE_EXACT_MOMENT_LITERAL_PARITY_ON_FRESH_B16_CALLER',
        original_id=state['id'], path=state['path'], source_node_index=0,
        source_node_sha256=sha(node_path), fresh_complete_tree_report_sha256=sha(proof),
        pair_intervals=36, matrices=len(ctx.default_matrices), counts=list(RT.COUNTS),
        rows_compared=3072, complete_coefficients_rhs_names_and_order_equal=True,
        literal_sequence_sha256=hashlib.sha256(encoded).hexdigest(),
        immutable_cache_rows_and_independent_outer_lists=True, malformed_callers_rejected=rejected,
        reference_generator_sha256=RT.REFERENCE_SHA, optimizer_sha256=RT.OPTIMIZER_SHA,
        reference_generation_seconds=old_seconds, optimized_generation_seconds=new_seconds,
        timings_are_generator_only=True, mathematical_row_families_changed=0,
        independent_checker_unchanged=True, numerical_LP_solves=0,
        source_sha256=sources, numerical_search_started=False, new_original_cells=0, new_masks=0)
    out = HERE / 'B16_ACTUAL_EXACT_MOMENT_LITERAL_PARITY.json'
    with out.open('x') as f:
        json.dump(result, f, indent=2); f.write('\n')
    print(json.dumps(dict(status=result['status'], rows=3072, controls=len(rejected),
        reference_seconds=old_seconds, optimized_seconds=new_seconds, report_sha256=sha(out))), flush=True)


if __name__ == '__main__':
    main()
