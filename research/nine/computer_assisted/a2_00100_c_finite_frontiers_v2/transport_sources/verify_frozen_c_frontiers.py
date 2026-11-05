"""Hash and complete-graph audit only; performs no proof arithmetic."""
from pathlib import Path
from collections import Counter
import hashlib
import json
import sys

assert __debug__
assert not any(n in sys.modules for n in ('numpy', 'scipy', 'highspy'))
ROOT = Path(__file__).resolve().parent


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


inventory = json.loads((ROOT / 'INVENTORY.json').read_text())
manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
assert manifest['new_original_cells'] == manifest['new_masks'] == 0
assert not manifest['arithmetic_replayed_by_freezer']
assert not manifest['standalone_arithmetic_packet']
for relative, expected in inventory.items():
    path = Path(relative)
    assert not path.is_absolute() and '..' not in path.parts
    data = (ROOT / path).read_bytes()
    assert len(data) == expected['bytes'] and digest(data) == expected['sha256'], relative
path_map = json.loads((ROOT / 'ORIGINAL_PATH_MAP.json').read_text())
for original, expected in path_map.items():
    saved = inventory[expected['payload_path']]
    assert saved['sha256'] == expected['sha256'] and saved['bytes'] == expected['bytes']
sources = json.loads((ROOT / 'SOURCE_BINDINGS.json').read_text())
external = json.loads((ROOT / 'EXTERNAL_PROOF_INPUTS.json').read_text())['input_sha256']
for original, expected in sources.items():
    assert path_map[original]['sha256'] == expected

summaries = []
for selected in manifest['covers']:
    verbatim = ROOT / selected['verbatim_manifest']
    original_raw = verbatim.read_bytes()
    assert digest(original_raw) == selected['original_manifest_sha256']
    original = json.loads(original_raw)
    native_file = ROOT / selected['native_manifest']
    native = json.loads(native_file.read_text())
    expected = json.loads(original_raw)
    for node in expected['nodes']:
        node.pop('source_file', None)
    assert expected == native
    assert native['original']['id'] == selected['original_id']
    assert native['schema'] == 'whole_c_selective_dfs_continuation_v1'
    ns = {x['index']: x for x in native['nodes']}
    originals = {x['index']: x for x in original['nodes']}
    ps = {x['index']: x for x in native['pending']}
    ss = {x['index']: x for x in native['stopped']}
    assert len(ns) == len(native['nodes']) and len(ps) == len(native['pending'])
    assert len(ss) == len(native['stopped']) and not (set(ns) & set(ps))
    assert set(ss) <= set(ns)
    seen, queued = set(), set()
    cases = Counter()

    def visit(index, parent):
        if index in ps:
            assert index not in queued and ps[index]['parent'] == parent
            queued.add(index)
            return False
        assert index not in seen and index in ns
        seen.add(index)
        node = ns[index]
        assert node['parent'] == parent
        assert node['file'] == f'node_{index:05}.json'
        record_raw = (native_file.parent / node['file']).read_bytes()
        record = json.loads(record_raw)
        old = originals[index]
        original_path = Path(old.get('source_file',
            Path(selected['source_manifest_path']).parent / old['file']))
        assert original_path.is_absolute()
        assert path_map[str(original_path)]['sha256'] == digest(record_raw)
        assert record['status'] != 'RUNNING'
        record_status = 'OPEN' if node['status'] == 'CANDIDATE_COVER_CLOSED' else node['status']
        assert record['status'] == record_status
        assert record['initial']['id'] == native['original']['id']
        if 'split' not in node:
            assert node['status'] in ('OPEN', 'CANDIDATE_CLOSED')
            assert (index in ss) == (node['status'] == 'OPEN')
            return node['status'] == 'CANDIDATE_CLOSED'
        assert index not in ss
        split = node['split']
        children = split['children']
        assert len(children) == len(set(children)) == {'proxy': 4, 'sat': 8, 'angle': 2}[split['kind']]
        cases[split['kind']] += 1
        values = [visit(child, index) for child in children]
        closed = all(values)
        assert node['status'] == ('CANDIDATE_COVER_CLOSED' if closed else 'OPEN')
        return closed

    closed = visit(0, None)
    assert seen == set(ns) and queued == set(ps)
    excluded = sum(x['status'] == 'CANDIDATE_CLOSED' for x in ns.values())
    counts = dict(processed_nodes=len(ns), candidate_excluded_leaves=excluded,
                  pending=len(ps), stopped=len(ss), open_leaves=len(ps) + len(ss),
                  whole_candidate_closed=closed)
    assert counts == selected['counts']
    assert excluded == native['closed_leaves']
    assert not closed and not native['whole_candidate_closed']
    exact = selected['exact_replay']
    if exact is not None:
        report_raw = (ROOT / exact['path']).read_bytes()
        assert digest(report_raw) == exact['sha256']
        report = json.loads(report_raw)
        assert report['status'] == exact['status']
        assert report['status'].startswith('PASS_PARTIAL_WHOLE_ORIGINAL_')
        assert report['manifest_snapshot_sha256'] == digest(original_raw)
        assert report['nodes'] == len(ns) and report['excluded_leaves'] == excluded
        assert report['open_leaves'] == counts['open_leaves']
        assert not report['whole_original_excluded']
        assert report['new_original_cells'] == report['new_masks'] == 0
        for original_path, expected_digest in report['input_sha256'].items():
            if original_path in path_map:
                assert path_map[original_path]['sha256'] == expected_digest
            else:
                assert external.get(original_path) == expected_digest
        # Every processed record in this literal manifest must itself be a
        # freshly checked input; merely matching counts and a manifest digest
        # is insufficient because the manifest carries no record hashes.
        for node in original['nodes']:
            original_path = str(Path(node.get('source_file',
                Path(selected['source_manifest_path']).parent / node['file'])))
            assert report['input_sha256'][original_path] == path_map[original_path]['sha256']
    summaries.append(dict(name=selected['name'], counts=counts,
                          complete_declared_unions=dict(cases),
                          exact_partial_report_included=exact is not None))
print(json.dumps(dict(status='PASS_HASH_AND_COMPLETE_FRONTIER_TRANSPORT_ONLY',
                     files_rehashed=len(inventory), covers=summaries,
                     arithmetic_replayed_now=False, new_original_cells=0, new_masks=0)), flush=True)
