#!/usr/bin/env python3
"""Restore committed B462 launch/first-use inputs, without launching them."""
from pathlib import Path
import hashlib
import importlib.util
import json

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
PACKET = HERE / 'published_35ac6d675d'

def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    helper = HERE / 'restore_declared_b_ancestry_reset2_v1.py'
    spec = importlib.util.spec_from_file_location('exact_B_outer_restore_IO', helper)
    M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)
    exported = PACKET / 'GIT_EXPORT_RECEIPT.json'
    assert M.sha(exported) == '776aeea8b3387e7bd0093a9707792e03395d5ba8b7a60624ddd7535b7576cff8'
    files = {e['path']: e for e in json.loads(exported.read_text())['files']}
    publication = PACKET / 'PUBLICATION_MANIFEST.json'
    assert M.sha(publication) == files['PUBLICATION_MANIFEST.json']['sha256']
    declared = json.loads(publication.read_text())['files']
    assert set(declared) == set(files) - {'PUBLICATION_MANIFEST.json'}
    for name, e in declared.items():
        assert M.sha(PACKET / name) == e['sha256'] and (PACKET / name).stat().st_size == e['bytes']
    plan = {}
    for name, e in declared.items():
        if name.startswith(('first_actual_B462_use/', 'launch_and_root_review/')):
            relative = name.split('/', 1)[1]
            assert relative.startswith(('b_work/', 'd_work/'))
            plan[str(ROOT / relative)] = dict(source=name, **e)
    name = 'transport/B_ACCEPTED_CENTER_RUNTIME_ROOT_REVIEW.json'
    plan[str(ROOT / 'd_work/B_ACCEPTED_CENTER_RUNTIME_ROOT_REVIEW.json')] = dict(source=name, **declared[name])
    for target, e in plan.items():
        p = Path(target)
        if p.exists():
            assert not p.is_symlink() and p.is_file() and M.sha(p) == e['sha256'], target
    installed = 0
    for target, e in plan.items():
        with (PACKET / e['source']).open('rb') as stream:
            installed += M.install(stream, Path(target), e['bytes'], e['sha256'])
    for target, e in plan.items():
        assert M.sha(target) == e['sha256']
    receipt = dict(status='PASS_EXACT_COMMITTED_B462_OUTER_INPUT_RESTORATION',
        commit='35ac6d675d74f013a59804ef5506b74b005b59d6', publication_manifest_sha256=M.sha(publication),
        files=plan, installed=installed, retained_identical=len(plan)-installed,
        source_sha256=M.sha(__file__), io_helper_sha256=M.sha(helper),
        arithmetic_repeated=False, numerical_search_started=False, old_lost_search_suffix_recovered=False,
        existing_different_files_overwritten=False, new_original_cells=0, new_masks=0)
    path = HERE / 'FRESH_B462_OUTER_INPUT_RESTORATION.json'
    with path.open('x') as out:
        json.dump(receipt, out, indent=2); out.write('\n')
    print(json.dumps(dict(status=receipt['status'], files=len(plan), installed=installed,
                         receipt_sha256=M.sha(path))), flush=True)

if __name__ == '__main__':
    main()
