"""Finite hash/structure backup of explicitly selected C covers and reports.

This is a transport producer, not a proof checker. It imports no numerical or
proof-production modules and never upgrades a candidate or partial cover.
"""
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import json
import sys


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def stable(path):
    path = Path(path)
    before = path.stat()
    raw = path.read_bytes()
    after = path.stat()
    assert (before.st_ino, before.st_size, before.st_mtime_ns) == (
        after.st_ino, after.st_size, after.st_mtime_ns)
    assert len(raw) == after.st_size
    return raw


def structure(value):
    nodes = {n['index']: n for n in value['nodes']}
    pending = {n['index']: n for n in value['pending']}
    stopped = {n['index']: n for n in value['stopped']}
    assert len(nodes) == len(value['nodes'])
    assert len(pending) == len(value['pending'])
    assert len(stopped) == len(value['stopped'])
    assert 0 in nodes and not (set(nodes) & set(pending))
    assert set(stopped) <= set(nodes)
    visited, frontier = set(), set()

    def walk(index, parent):
        if index in pending:
            assert index not in frontier and pending[index]['parent'] == parent
            frontier.add(index)
            return False
        assert index in nodes and index not in visited
        visited.add(index)
        node = nodes[index]
        assert node['parent'] == parent and node['status'] != 'RUNNING'
        split = node.get('split')
        if split:
            assert index not in stopped
            children = split['children']
            assert len(children) == len(set(children)) == {
                'proxy': 4, 'sat': 8, 'angle': 2, 'difference': 2}[split['kind']]
            closed = all([walk(child, index) for child in children])
            assert node['status'] == ('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
            return closed
        assert node['status'] in ('OPEN', 'CANDIDATE_CLOSED')
        assert (index in stopped) == (node['status'] == 'OPEN')
        return node['status'] == 'CANDIDATE_CLOSED'

    complete = walk(0, None)
    assert visited == set(nodes) and frontier == set(pending)
    excluded = sum(n['status'] == 'CANDIDATE_CLOSED' for n in nodes.values())
    assert excluded == value['closed_leaves']
    assert complete == value.get('whole_candidate_closed', False)
    return dict(processed_nodes=len(nodes), candidate_excluded_leaves=excluded,
                pending=len(pending), stopped=len(stopped),
                open_leaves=len(pending) + len(stopped),
                whole_candidate_closed=complete)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('config', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    config_raw = stable(args.config)
    config = json.loads(config_raw)
    assert 1 <= len(config['covers']) <= 6
    out = args.output.resolve()
    assert not out.exists()
    out.mkdir(parents=True)
    inventory, paths, sources, external = {}, {}, {}, {}

    def put(relative, raw, source=None, category='payload'):
        relative = Path(relative)
        assert not relative.is_absolute() and '..' not in relative.parts
        digest = sha(raw)
        target = out / relative
        if str(relative) in inventory:
            assert inventory[str(relative)]['sha256'] == digest
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
            assert sha(target.read_bytes()) == digest
            inventory[str(relative)] = dict(sha256=digest, bytes=len(raw), category=category)
        if source is not None:
            for old in {str(Path(source).absolute()), str(Path(source).resolve())}:
                if old in paths:
                    assert paths[old]['sha256'] == digest
                else:
                    paths[old] = dict(payload_path=str(relative), sha256=digest, bytes=len(raw))
        return digest

    def add(path, relative, category, expected=None):
        raw = stable(path)
        assert expected is None or sha(raw) == expected
        return put(relative, raw, path, category)

    def jsonput(relative, value, category='metadata'):
        return put(relative, (json.dumps(value, indent=2) + '\n').encode(), category=category)

    def source_file(path, expected):
        path = Path(path).resolve()
        key = str(path)
        assert key not in sources or sources[key] == expected
        sources[key] = expected
        add(path, Path('sources') / (expected + '_' + path.name), 'bound_source', expected)

    covers = []
    names = set()
    for selected in config['covers']:
        name = selected['name']
        assert name.replace('_', '').isalnum() and name not in names
        names.add(name)
        folder = Path(selected['folder']).resolve()
        manifest_path = folder / 'MANIFEST.json'
        raw = stable(manifest_path)
        original = json.loads(raw)
        assert original['schema'] == 'whole_c_selective_dfs_continuation_v1'
        counts = structure(original)
        assert not counts['whole_candidate_closed']
        prefix = Path('covers') / name
        original_sha = put(prefix / 'ORIGINAL_MANIFEST.json', raw, manifest_path,
                           'verbatim_complete_cover_manifest')
        native = deepcopy(original)
        for node in native['nodes']:
            assert node['file'] == f"node_{node['index']:05}.json"
            path = Path(node.get('source_file', folder / node['file']))
            assert path.is_absolute()
            payload = stable(path)
            record = json.loads(payload)
            assert record['status'] != 'RUNNING'
            expected = 'OPEN' if node['status'] == 'CANDIDATE_COVER_CLOSED' else node['status']
            assert record['status'] == expected
            put(prefix / node['file'], payload, path, 'unchanged_processed_record')
            node.pop('source_file', None)
        jsonput(prefix / 'MANIFEST.json', native, 'location_metadata_transport_only')
        anchor = original['source_manifest']
        add(anchor['path'], Path('anchors') / (name + '_source_manifest.json'),
            'source_manifest_anchor', anchor['sha256'])
        for path, expected in original.get('discovery_source_sha256', {}).items():
            source_file(path, expected)
        report_info = None
        assert selected.get('report'), 'Publication selection requires a fresh whole-original partial replay.'
        if selected.get('report'):
            report_path = Path(selected['report']).resolve()
            report_raw = stable(report_path)
            report = json.loads(report_raw)
            assert report['status'].startswith('PASS_PARTIAL_WHOLE_ORIGINAL_')
            assert report['manifest_snapshot_sha256'] == original_sha
            assert report['nodes'] == counts['processed_nodes']
            assert report['excluded_leaves'] == counts['candidate_excluded_leaves']
            assert report['open_leaves'] == counts['open_leaves']
            assert not report['whole_original_excluded']
            assert report['new_original_cells'] == report['new_masks'] == 0
            report_sha = put(Path('evidence') / report_path.name, report_raw,
                             report_path, 'previous_fresh_exact_partial_replay')
            for key in ('checker_dependency_sha256',
                        'relative_support_chord_source_sha256',
                        'relative_support_chord_and_deep_boundary_source_sha256',
                        'opposite_boundary_and_relative_support_source_sha256'):
                for path, expected in report.get(key, {}).items():
                    source_file(path, expected)
            for path, expected in report.get('input_sha256', {}).items():
                assert path not in external or external[path] == expected
                external[path] = expected
            report_info = dict(path=str(Path('evidence') / report_path.name),
                               sha256=report_sha, status=report['status'],
                               seconds=report['seconds'], new_arithmetic_run_by_freezer=False)
        covers.append(dict(name=name, scope=selected['scope'],
                           original_id=original['original']['id'], counts=counts,
                           source_manifest_path=str(manifest_path),
                           verbatim_manifest=str(prefix / 'ORIGINAL_MANIFEST.json'),
                           native_manifest=str(prefix / 'MANIFEST.json'),
                           original_manifest_sha256=original_sha,
                           exact_replay=report_info,
                           arithmetic_status='FRESH_EXACT_PARTIAL_REPLAY_INCLUDED' if report_info
                           else 'DISCOVERY_ONLY_NO_NEW_REPLAY_CLAIM'))
        assert stable(manifest_path) == raw
        print('FROZEN', name, json.dumps(counts), flush=True)
    for path in config.get('evidence', []):
        p = Path(path).resolve()
        add(p, Path('evidence') / p.name, 'scope_or_source_review')
    for path in config.get('rederived_inputs', []):
        p = Path(path).resolve()
        raw = stable(p)
        put(Path('rederived_inputs') / (sha(raw) + '_' + p.name), raw, p,
            'fresh_rederived_output_or_exact_location_transport')
    for path in config.get('extra_sources', []):
        p = Path(path).resolve()
        source_file(p, sha(stable(p)))
    source_file(Path(__file__).resolve(), sha(stable(__file__)))
    put('FREEZE_CONFIG.json', config_raw, args.config, 'explicit_finite_selection')
    jsonput('SOURCE_BINDINGS.json', sources)
    # The manifest does not hash its processed C records. Bind every copied
    # replay input explicitly to the report's digest before treating it as
    # locally included; otherwise a stale PASS report could accompany changed
    # record bytes under an unchanged manifest. Preserve literal path aliases.
    remaining_external = {}
    for path, expected in external.items():
        copied = paths.get(path) or paths.get(str(Path(path).resolve()))
        if copied is not None:
            assert copied['sha256'] == expected, ('replay input mismatch', path)
            assert path not in paths or paths[path] == copied
            paths[path] = dict(copied)
        else:
            assert sha(stable(path)) == expected, ('external replay input mismatch', path)
            remaining_external[path] = expected
    external = remaining_external
    # Every still-external byte must have an exact member in an explicitly
    # identified published archive. Fresh derived outputs are copied above;
    # they must never masquerade as recoverable accepted external ancestry.
    catalog_path = Path(config['published_dependency_catalog']).resolve()
    catalog_raw = stable(catalog_path)
    catalog = json.loads(catalog_raw)
    assert catalog['status'] == 'PASS_PUBLISHED_GIT_BYTES_AND_STREAMED_ARCHIVE_MEMBERS'
    add(catalog_path, 'PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json',
        'published_archive_byte_and_member_audit')
    published_by_hash = {}
    for member in catalog['members']:
        published_by_hash.setdefault(member['sha256'], []).append(member)
    recovery = {}
    for path, expected in external.items():
        candidates = published_by_hash.get(expected, [])
        assert candidates, ('unpublished external byte must be copied', path, expected)
        preferred = ('cb882_whole_eight_checkpoint' if '/cb882_whole_eight_checkpoint_package/' in path
                     else 'c887_fresh_whole_state' if '/restored/c887_fresh_whole_state_v1/' in path
                     else 'cd402_original_checkpoint_delta' if '/cd402_checkpoint_delta/' in path
                     else 'a_c744_portable_open_checkpoint')
        selected = next((entry for entry in candidates if entry['archive_id'] == preferred), candidates[0])
        assert selected['bytes'] == Path(path).stat().st_size
        recovery[path] = dict(selected)
    jsonput('PUBLISHED_DEPENDENCY_RECOVERY.json', dict(
        schema='complete_C_external_input_archive_member_mapping_v1',
        input_sha256=external, entries=recovery, archives=catalog['archives'],
        catalog_sha256=sha(catalog_raw),
        exact_byte_transport_only=True, mathematical_strings_unchanged=True,
        fresh_rederived_outputs_included_separately=True,
        new_original_cells=0, new_masks=0))
    jsonput('EXTERNAL_PROOF_INPUTS.json', dict(
        scope='Pinned previously used inputs not duplicated by this transport checkpoint. '
              'Restore accepted external ancestry before any fresh proof replay.',
        input_sha256=external, standalone_arithmetic_packet=False))
    jsonput('ORIGINAL_PATH_MAP.json', paths)
    jsonput('MANIFEST.json', dict(
        schema='frozen_c_relative_chord_partial_frontiers_v2', covers=covers,
        arithmetic_replayed_by_freezer=False, new_original_cells=0, new_masks=0,
        included_rederived_outputs=len(config.get('rederived_inputs', [])),
        every_open_alternative_retained=True, processed_record_bytes_unchanged=True,
        native_manifest_change='Only source_file location fields are removed.',
        standalone_arithmetic_packet=False))
    verifier = Path(config['hash_verifier']).resolve()
    add(verifier, 'verify_payload.py', 'independent_hash_and_coverage_verifier')
    readme = Path(config['readme']).resolve()
    add(readme, 'README.md', 'scope_readme')
    (out / 'INVENTORY.json').write_text(json.dumps(inventory, indent=2) + '\n')
    print(json.dumps(dict(status='FROZEN_COMPLETE_PARTIAL_FRONTIERS_HASH_CHECK_PENDING',
                          files=len(inventory), payload_bytes=sum(x['bytes'] for x in inventory.values()),
                          new_original_cells=0, new_masks=0)), flush=True)


if __name__ == '__main__':
    assert __debug__
    assert not any(n in sys.modules for n in ('numpy', 'scipy', 'highspy'))
    main()
