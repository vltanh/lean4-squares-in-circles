"""Review the concrete generic B transport output without trusting its receipt."""
from pathlib import Path
from hashlib import sha256
import json

W = Path('/workspace/scratch/6b34cccf3741/repo/research/nine/.runs/closure_20261104')
P = W / 'accepted/b580_complete_original_package_v2'
V1 = W / 'accepted/b580_complete_original_package_v1'
PRIOR = W / 'accepted/b16a_I32_complete_H_checkpoint'
OUT = Path('/workspace/scratch/6b34cccf3741/a_work')
checked = {}

def digest(p, expected=None):
    p = Path(p)
    h = sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    value = h.hexdigest()
    if expected is not None:
        assert value == expected, (p, value, expected)
    checked[str(p)] = value
    return value

def read(p, expected=None):
    digest(p, expected)
    return json.loads(Path(p).read_text())

r = read(P / 'TRANSPORT_PREPARATION.json')
manifest = read(P / 'INPUT_MANIFEST.json')
old = read(P / 'INPUT_MANIFEST_BEFORE_TRANSPORT.json', r['source_input_manifest_sha256'])
before = read(P / 'BINDINGS_BEFORE_TRANSPORT.json', r['original_bindings_sha256'])
after = read(P / 'BINDINGS.json', r['extended_bindings_sha256'])
info = read(P / 'ORIGINAL_PROOF.json')
assert info['original_id'] == r['original_id'] == 'negative-580db3624cf4c2e2'
assert info['complete'] is r['complete'] is True
assert info['open_prototype'] is False
assert info['new_original_ledger_credit'] == info['new_mask_ledger_credit'] == r['original_credit'] == r['mask_credit'] == 0
assert info['counts']['open_leaves'] == 0 and info['counts']['nodes'] == 755
assert info['counts']['terminal_leaves'] == info['counts']['excluded_leaves'] == 537
assert digest(P / 'INPUT_MANIFEST.json') == '2eb464d3586e073604738d30e777d32f584294c55de82ad02730ddab64576409'
assert len(manifest['files']) == 1156
assert len(r['attachments']) == 17
assert read(V1 / 'INPUT_MANIFEST.json', r['source_input_manifest_sha256']) == old
assert read(V1 / 'BINDINGS.json', r['original_bindings_sha256']) == before
assert all(after[k] == v for k, v in before.items())
added = set(after) - set(before)
assert added == set(r['added_aliases']) and len(added) == r['added_alias_count'] == 769
historical = Path(r['historical_prefix'])
canonical = Path(r['canonical_prefix'])
assert historical.resolve() == canonical.resolve() and historical != canonical
for alias in sorted(added):
    detail = r['added_aliases'][alias]
    old_name = detail['canonical']
    entry = after[alias]
    assert old_name in before and entry == before[old_name] == detail['binding']
    assert Path(alias) == historical / Path(old_name).relative_to(canonical)
    assert Path(alias).resolve() == Path(old_name)
    digest(alias, entry['sha256'])
    assert entry['root'] in ('packet', 'prior')
    base = P if entry['root'] == 'packet' else PRIOR
    target = (base / entry['path']).resolve()
    assert target.is_relative_to(base.resolve())
    digest(target, entry['sha256'])
for name, value in old['files'].items():
    digest(V1 / name, value)
    if name != 'BINDINGS.json':
        digest(P / name, value)
for name, value in manifest['files'].items():
    digest(P / name, value)
for name, details in r['attachments'].items():
    digest(P / name, details['sha256'])
    digest(details['source'], details['sha256'])
tree_entry = info['tree']
assert tree_entry['root'] == 'packet'
tree = read(P / tree_entry['path'], tree_entry['sha256'])
parent = tree['parent']
assert parent['path'] == str(historical / 'whole_B_roots' / (info['original_id'] + '.json'))
assert after[parent['path']]['sha256'] == parent['sha256']
parent_entry = after[parent['path']]
parent_base = P if parent_entry['root'] == 'packet' else PRIOR
physical_parent = read(parent_base / parent_entry['path'], parent['sha256'])
assert physical_parent['id'] == info['original_id']
assert physical_parent['path'] == info['original_path']
tool = W / 'acceptance/prepare_registered_b_portable_transport.py'
tool_hash = digest(tool)
digest(P / 'acceptance_tools/prepare_registered_b_portable_transport.py', tool_hash)
baseline = read(W / 'accepted/bf14_complete_original_package_v2/TRANSPORT_ALIAS_REPAIR.json')
assert baseline['historical_prefix'] == r['historical_prefix']
assert baseline['canonical_prefix'] == r['canonical_prefix']
digest(__file__)
answer = dict(status='PASS_GENERIC_B_TRANSPORT_SOURCE_AND_CONCRETE_PACKET_REVIEW',
              tool_sha256=tool_hash, packet_input_manifest_sha256=checked[str(P / 'INPUT_MANIFEST.json')],
              original_id=info['original_id'], complete=True, open_leaves=0,
              nodes=755, excluded_leaves=537, original_v1_packet_bytes_unchanged=True,
              verified_added_aliases=len(added), inputs_checked=len(manifest['files']),
              all_previous_binding_entries_identical=True,
              all_prior_proof_and_checker_bytes_unchanged=True,
              original_parent_id_path_and_hash_derived_and_checked=True,
              attachments_match_reviewed_sources=True,
              arithmetic_replayed_in_this_review=False,
              fresh_portable_arithmetic_replay_required=True,
              original_credit=0, mask_credit=0, blocking_findings=[],
              source_sha256=checked)
(OUT / 'B580_PORTABLE_TRANSPORT_REVIEW.json').write_text(json.dumps(answer, indent=2) + '\n')
print(json.dumps({k: v for k, v in answer.items() if k != 'source_sha256'}, indent=2))
