#!/usr/bin/env python3
"""Collect compact source/readiness evidence; omit already published payloads."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path('/workspace/scratch/f9f48fcfb253')
HERE = Path(__file__).resolve().parent
OUT = HERE / 'publication_source_checkpoint_v1'
PUB = HERE / 'published_35ac6d675d'
PUBLISHED_COMMIT = '35ac6d675d74f013a59804ef5506b74b005b59d6'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    assert not OUT.exists()
    freeze_path = HERE / 'B_CENTER_EXACT_MOMENT_BOUNDED_READINESS_FREEZE_V1.json'
    assert sha(freeze_path) == 'b744219d6505282f5071d84f29c323c459cf94604a68066c552660b9a2b11138'
    freeze = json.loads(freeze_path.read_text())
    for path, expected in freeze['files'].items():
        assert sha(path) == expected, path
    assert len(freeze['files']) == 396
    for case in freeze['cases']:
        assert not Path(case['output']).exists() and not Path(case['log']).exists()
    member_path = PUB / 'transport/MEMBER_MANIFEST.json'
    assert sha(member_path) == 'b378e221ee25b1aa129a80284b38496f6d9a7eef97768bb65e8696e50b8b7935'
    publication_path = PUB / 'PUBLICATION_MANIFEST.json'
    members = json.loads(member_path.read_text())['members']
    publication = json.loads(publication_path.read_text())['files']
    inputs = {}

    def select(source, relative=None):
        source = Path(source).resolve()
        assert source.is_file() and not source.is_symlink()
        if relative is None:
            relative = 'native/' + str(source.relative_to(ROOT))
        assert relative not in inputs
        inputs[relative] = dict(source=str(source), sha256=sha(source), bytes=source.stat().st_size)

    # Explicit small newly-created source/recovery outputs; no nested proof trees.
    for source in sorted(HERE.iterdir()):
        if source.is_file() and source.suffix in ('.py', '.json', '.md', '.diff'):
            select(source)
    for source in sorted((HERE / 'transcript_source').iterdir()):
        if source.is_file():
            select(source)
    for source in sorted((ROOT / 'b_work/accepted_exact_area_moments_v1').iterdir()):
        if source.is_file():
            select(source)
    for name in ('b_center_exact_moment_runtime_v1.py',
                 'resume_b_center_exact_moment_atomic_tree_v1.py'):
        select(ROOT / 'b_work' / name)
    for folder, names in (
        ('B16A_center_exact_moment_prepared_seed_v1', ('manifest.json', 'PREVIOUS_COMPLETE_MANIFEST.json')),
        ('B462_center_exact_moment_prepared_seed_v1', ('manifest.json', 'PREVIOUS_COMPLETE_MANIFEST.json')),
        ('B462_preserved_two_round_whole_attachment_v1', ('manifest.json', 'ATTACHMENT_BINDING.json'))):
        for name in names:
            select(HERE / folder / name)
    select(ROOT / 'b_work/recovery_20261105/registered_B_initial_states/negative-462e78d2e2d8be05.json')
    select(HERE / 'B_RESET2_SOURCE_CHECKPOINT_README.md', 'README.md')
    select(HERE / 'verify_b_reset2_source_checkpoint_v1.py', 'verify_checkpoint.py')
    select(member_path, 'dependencies/PUBLISHED_185_MEMBER_MANIFEST.json')
    select(publication_path, 'dependencies/PUBLISHED_35AC_PUBLICATION_MANIFEST.json')
    select(PUB / 'GIT_EXPORT_RECEIPT.json', 'dependencies/PUBLISHED_35AC_GIT_EXPORT_RECEIPT.json')
    select(ROOT / 'b_work/recovery_20261105/publication_selection_v1/REQUIRED_PUBLISHED_ANCESTRY.json',
           'dependencies/REQUIRED_PUBLISHED_ANCESTRY.json')
    select(ROOT / 'b_work/resume_b_five_proxy_round_atomic_center_tree_v1.py',
           'dependencies/accepted_center_atomic_driver.py')
    aliases = []
    old_b16 = ROOT / 'b_work/recovery_20261105/reassembled_B16a_published_prefix_v1'
    b16 = json.loads((old_b16 / 'manifest.json').read_text())
    for node in b16['nodes']:
        member = 'native/b_work/recovery_20261105/reassembled_B16a_published_prefix_v1/' + node['file']
        meta = members[member]
        assert meta['sha256'] == node['sha256']
        for folder in (old_b16, HERE / 'B16A_center_exact_moment_prepared_seed_v1'):
            p = folder / node['file']
            assert sha(p) == meta['sha256'] and p.stat().st_size == meta['bytes']
            aliases.append(dict(target=str(p.relative_to(ROOT)), kind='archive_member',
                published_path=member, **meta))
    member = 'first_actual_B462_use/b_work/recovery_20261105/B462_first_center_weighted_prefix_v1/node_0000.json'
    meta = publication[member]
    for folder in (ROOT / 'b_work/recovery_20261105/B462_first_center_weighted_prefix_v1',
                   HERE / 'B462_preserved_two_round_whole_attachment_v1',
                   HERE / 'B462_center_exact_moment_prepared_seed_v1'):
        p = folder / 'node_0000.json'
        assert sha(p) == meta['sha256'] and p.stat().st_size == meta['bytes']
        aliases.append(dict(target=str(p.relative_to(ROOT)), kind='publication_file',
            published_path=member, **meta))
    assert len(aliases) == len({e['target'] for e in aliases}) == 93
    OUT.mkdir()
    files = {}
    for relative, meta in sorted(inputs.items()):
        target = OUT / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(meta['source'], target)
        assert target.stat().st_size == meta['bytes'] and sha(target) == meta['sha256']
        files[relative] = dict(bytes=meta['bytes'], sha256=meta['sha256'], native_source=meta['source'])

    def write(relative, value):
        target = OUT / relative
        with target.open('x') as out:
            json.dump(value, out, indent=2); out.write('\n')
        files[relative] = dict(bytes=target.stat().st_size, sha256=sha(target), native_source=None)

    write('PUBLISHED_PAYLOAD_ALIASES.json', dict(
        schema='B_reset2_published_node_payload_aliases_v1', published_commit=PUBLISHED_COMMIT,
        published_package='research/nine/computer_assisted/b_recovery_center_continuations_v1',
        archive_sha256='ddba86d2dda6c261e1a3b2868459ddbb7eced058fc0c91c8b72d56254d6f6e93',
        aliases=aliases, role='Exact byte reuse only; transitive proof masters remain required',
        arithmetic_replayed=False))
    write('CHECKPOINT.json', dict(schema='B_reset2_source_and_bounded_readiness_checkpoint_v1',
        status='RESTORED_EXACT_CALLERS_AND_SOURCE_READINESS_NUMERICAL_LAUNCH_HELD',
        source_freeze_sha256=sha(freeze_path), source_pins=396,
        accepted_counts=dict(closed_originals=222, total_originals=231, closed_masks=8, total_masks=32),
        fresh_arithmetic_reports=dict(B16A='6957aef8e8867eb8c36ff8df268f448896f27e203e59e76547000a926b31fbfa',
                                      B462='6bbedffa6c286313e4f904cd9a8c134969cb7b22284585a3fd61b627dc2d53ba'),
        moment_parity_sha256='e24f62174bf0f1da13dc1157e8f92341b7a9f0fbd76d14f93a4092a1f97d66d6',
        missing_old_B462_capture_script_sha256='c2f205204abb4a6ba375749195a2b03db08f26b289ff0cbd34ba365c85ca8571',
        missing_old_B462_capture_script_recreated=False,
        lost_B16_105_or_107_suffix_used=False, live_run_trees_or_logs_included=False,
        numerical_search_started=False, no_new_mathematical_row_family=True,
        independent_arithmetic_checker_unchanged=True, standalone_portable_proof=False,
        new_original_cells=0, new_masks=0, lean_lake_ci_run=False))
    for relative, meta in inputs.items():
        assert sha(meta['source']) == meta['sha256'], relative
    for path, expected in freeze['files'].items():
        assert sha(path) == expected, path
    manifest = dict(schema='B_reset2_source_readiness_checkpoint_inventory_v1',
        files=files, total_file_bytes=sum(v['bytes'] for v in files.values()),
        all_sources_rehashed_before_and_after=True, raw_node_payloads_included=False,
        all_required_published_payload_aliases=93, standalone_portable_proof=False,
        arithmetic_replayed_during_packaging=False, numerical_search_started=False,
        new_original_cells=0, new_masks=0)
    with (OUT / 'INPUT_MANIFEST.json').open('x') as output:
        json.dump(manifest, output, indent=2); output.write('\n')
    print(json.dumps(dict(status='COMPACT_SOURCE_CHECKPOINT_PREPARED', output=str(OUT),
        inventory_sha256=sha(OUT / 'INPUT_MANIFEST.json'), included_files=len(files),
        raw_file_bytes=manifest['total_file_bytes'], published_payload_aliases=93,
        numerical_search_started=False)), flush=True)


if __name__ == '__main__':
    main()
