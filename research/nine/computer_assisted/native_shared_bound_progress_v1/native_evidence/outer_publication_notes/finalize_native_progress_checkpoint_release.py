#!/usr/bin/env python3
"""Finalize outer metadata only for two small, already frozen native checkpoints."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

WORK = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
RELEASE = HERE / 'native_progress_checkpoints_v1'
CB_COMMIT = '8ac1db9d311ab0319105cd35ce46d2b002216330'
CB_PATH = 'research/nine/computer_assisted/a2_00100_cb882_whole_eight_manifest.json'
CB_SHA = '837d41cbbc29b8dd969ff132356883aa80fec545260c2ccb67825cd7c6e59e57'
CB_ARCHIVE = 'a40a03d8f4900a8e403ad2258e9e7660a3c4afe9fb9a8a26bce26149aedf6925'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def dump(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def main():
    if not __debug__:
        raise RuntimeError('Optimized Python is not supported.')
    assert RELEASE.is_dir()
    assert not (RELEASE / 'READY.json').exists()
    prepared = json.loads((RELEASE / 'PREPARED_CHECKPOINTS.json').read_text())
    assert prepared['status'] == 'PREPARED_NATIVE_ONLY_SOURCE_EVIDENCE_CHECKPOINTS'
    assert prepared['full_proof_replayed'] is False
    assert prepared['new_original_cells'] == prepared['new_masks'] == 0
    packages = []
    for name, audit_name in (
        ('direct_shared_bounds_and_C_lazy_readers_native_v1', 'DIRECT_C_NATIVE_HEADER_AUDIT.json'),
        ('A_c744_component3_POST_A1_bounds_native_v1', 'A3_POST_A1_NATIVE_HEADER_AUDIT.json'),
    ):
        folder = RELEASE / name
        audit_path = RELEASE / audit_name
        audit = json.loads(audit_path.read_text())
        assert audit['status'] == 'PASS_NATIVE_CHECKPOINT_BYTES_AND_HEADER_CONSISTENCY_ONLY'
        assert audit['weighted_arithmetic_repeated'] is False
        inventory = json.loads((folder / 'INPUT_MANIFEST.json').read_text())
        assert sha(folder / 'INPUT_MANIFEST.json') == audit['input_manifest_sha256']
        expected = set(inventory['files']) | {'INPUT_MANIFEST.json'}
        assert {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()} == expected
        for member, entry in inventory['files'].items():
            p = folder / member
            assert not p.is_symlink() and p.resolve().is_relative_to(folder.resolve())
            assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256']
        source = json.loads((folder / 'SOURCE_PROVENANCE.json').read_text())
        for path, entry in source.items():
            assert sha(path) == sha(folder / entry['member']) == entry['sha256']
        dependencies = json.loads((folder / 'DEPENDENCIES.json').read_text())
        packages.append(dict(folder=name, input_manifest_sha256=audit['input_manifest_sha256'],
            bytes=audit['bytes'], inventoried_files=audit['files'],
            audit=audit_name, audit_sha256=sha(audit_path),
            dependency_counts=dependencies['availability_counts'],
            native_source_bytes_rehashed_before_release=True))
    raw = subprocess.check_output(['git', '-C', str(WORK / 'repo'), 'show', CB_COMMIT + ':' + CB_PATH])
    assert hashlib.sha256(raw).hexdigest() == CB_SHA
    cb = json.loads(raw)
    assert cb['archive_sha256'] == CB_ARCHIVE
    c_manifest = RELEASE / 'direct_shared_bounds_and_C_lazy_readers_native_v1/published_references/C_height_delta_ARCHIVE_MANIFEST.json'
    assert json.loads(c_manifest.read_text())['base_Cb882_archive_sha256'] == CB_ARCHIVE
    outer = RELEASE / 'outer_publication_notes'
    outer.mkdir()
    (outer / 'PUBLISHED_CB882_WHOLE_EIGHT_MANIFEST.json').write_bytes(raw)
    dump(outer / 'TRANSITIVE_CB882_PUBLICATION_REFERENCE.json', dict(
        schema='explicit_transitive_published_prerequisite_reference_v1',
        applies_to_checkpoint='direct_shared_bounds_and_C_lazy_readers_native_v1',
        commit=CB_COMMIT, repository_path=CB_PATH,
        manifest_sha256=CB_SHA, archive_sha256=CB_ARCHIVE,
        manifest_file='PUBLISHED_CB882_WHOLE_EIGHT_MANIFEST.json',
        archive_bytes_bundled=False, archive_downloaded_or_replayed_now=False,
        relation='Exact Cb882 base already named by the included C height delta publication manifest.',
        original='negative-b882d8ade0cf9ea0', new_original_cells=0, new_masks=0))
    sources = {}
    for p in (HERE / 'build_native_progress_checkpoints.py', HERE / 'verify_native_checkpoint_inventory.py', Path(__file__).resolve()):
        member = 'outer_publication_notes/' + p.name
        shutil.copy2(p, RELEASE / member)
        assert sha(p) == sha(RELEASE / member)
        sources[str(p)] = dict(member=member, sha256=sha(p))
    dump(outer / 'RELEASE_SOURCE_BINDINGS.json', sources)
    (RELEASE / 'README.md').write_text('''# Native progress checkpoints for exact shared bounds\n\nThis release preserves two separately scoped pieces of verified progress. It gives no additional original-cell or mask credit and contains no live search frontier.\n\n| Checkpoint | Included actual native gate | Scope |\n|---|---|---|\n| Direct shared bounds and C readers | Cb882: 158 exact copied bounds; C887: 181 copied bounds within a four-round record | Both saved domains remain OPEN; the Cb fixture is conditional on height component 1 |\n| A c744 POST-A1 bounds | 39 weighted uses of the new 414-row family within a five-round record | Only the exact component 3 domain; the original and component remain OPEN |\n\nThe large proofs already published for the original A base, C height consequences and complete A1 exclusion are referenced by exact commit, archive digest and input inventory. The original Cb882 eight-domain archive is also pinned in the outer publication notes as the transitive C height prerequisite. Every other referenced native prerequisite is explicitly marked as not bundled. Native absolute path strings and all mathematical/source bytes are retained.\n\nThese are source and native-evidence checkpoints, **not self-contained cold proof packets**. The two included audit receipts rehash the bundled files and compare their original, domain and counting headers against the frozen records. They do not repeat weighted arithmetic or reconstruct omitted ancestry. The saved native exact receipts are the evidence for the earlier arithmetic runs.\n\n`READY.json` identifies the two frozen inner inventories and their outer audit receipts. `RELEASE_INVENTORY.json` pins all files in this release except itself. The exact replay inputs are read-only; locally hardlinked records must not be edited. The outer source bindings record the preparation and byte/header-checking scripts. No numerical solver, Lean, Lake, CI, full proof rerun, register update or Git mutation is performed by this release preparation.\n''')
    dump(RELEASE / 'READY.json', dict(status='READY_FOR_ROOT_REVIEW_NATIVE_CHECKPOINTS_ONLY',
        packages=packages, transitive_cb882_archive_sha256=CB_ARCHIVE,
        sources='outer_publication_notes/RELEASE_SOURCE_BINDINGS.json',
        native_exact_evidence_only=True, self_contained_cold_proof=False,
        omitted_ancestry_is_explicit=True, full_arithmetic_rerun=False,
        live_frontiers_changed=False, git_or_register_mutation=False,
        new_original_cells=0, new_masks=0))
    all_files = {p.relative_to(RELEASE).as_posix(): dict(sha256=sha(p), bytes=p.stat().st_size)
                 for p in sorted(RELEASE.rglob('*')) if p.is_file()}
    dump(RELEASE / 'RELEASE_INVENTORY.json', dict(schema='native_checkpoint_release_inventory_v1',
        files=all_files, new_original_cells=0, new_masks=0, self_contained_cold_proof=False))
    print(json.dumps(dict(status='READY', files=len(all_files),
        bytes=sum(e['bytes'] for e in all_files.values()),
        ready_sha256=sha(RELEASE / 'READY.json'),
        release_inventory_sha256=sha(RELEASE / 'RELEASE_INVENTORY.json')), indent=2))


if __name__ == '__main__':
    main()
