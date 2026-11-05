"""Read-only staged C checkpoint review; no arithmetic or archive member rescan."""
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from pathlib import Path, PurePosixPath
import json
import subprocess

ROOT = Path('/workspace/scratch/6b34cccf3741')
REPO = ROOT / 'repo'
W = REPO / 'research/nine/.runs/closure_20261104'
C = W / 'c_runtime'
PACKET = C / 'frozen_c_finite_frontiers_v2'
REL = 'research/nine/computer_assisted/a2_00100_c_finite_frontiers_v2'
PUB = REPO / REL
HEAD = '195d1ffb3dfeef021e254744672a5c425352e987'
OUT = ROOT / 'a_work/C_FINITE_FRONTIERS_V2_STAGED_PUBLICATION_REVIEW.json'
bindings = {}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path, expected=None):
    path = Path(path)
    actual = digest(path)
    if expected is not None:
        assert actual == expected, (path, actual, expected)
    bindings[str(path)] = actual
    return json.loads(path.read_text())


assert git('rev-parse', 'HEAD').decode().strip() == HEAD
# This checkout marks HEAD shallow, so revision walking intentionally hides its
# parent. The immutable raw commit header supplies the stronger direct-parent
# evidence without modifying repository history or fetching any objects.
head_commit_bytes = git('cat-file', 'commit', HEAD)
head_headers = head_commit_bytes.split(b'\n\n', 1)[0].splitlines()
dependency_commit = '4ce6c4567ddb810da03f64b2b139e5d3867661a6'
assert [line for line in head_headers if line.startswith(b'parent ')] == [
    ('parent ' + dependency_commit).encode()]
names = git('diff', '--cached', '--name-only', '-z').decode().split('\0')[:-1]
assert len(names) == 56 and len(set(names)) == 56
assert not git('diff', '--name-only')
publication = read(PUB / 'ZERO_CREDIT_PUBLICATION_AUDIT.json')
assert publication['expected_parent'] == HEAD
assert publication['new_original_cells'] == publication['new_masks'] == 0
assert publication['original_ledger_unchanged'] and not publication['complete_original']
assert not publication['standalone_arithmetic_packet'] and not publication['arithmetic_rerun_by_publisher']
parts = read(PUB / 'ARCHIVE_PARTS.json')
assert len(parts['parts']) == 15
expected_names = {REL + '/' + p for p in publication['copied_files']}
expected_names.update(REL + '/' + p['file'] for p in parts['parts'])
expected_names.update(REL + '/' + name for name in ('ARCHIVE_PARTS.json', 'ZERO_CREDIT_PUBLICATION_AUDIT.json', 'README.md'))
expected_names.update(('research/nine/A2_00100_C_FINITE_FRONTIERS_CHECKPOINT.md',
                       'research/nine/HANDOFF_A2_FIXED_CLOSURE.md', 'research/nine/PROGRESS.md'))
assert set(names) == expected_names

staged = {}
for name in names:
    data = git('show', ':' + name)
    assert data == (REPO / name).read_bytes(), name
    staged[name] = dict(sha256=sha256(data).hexdigest(), bytes=len(data),
                        git_blob=git('rev-parse', ':' + name).decode().strip())
    del data
ledger_rel = 'research/nine/gates/A2_00100_FIXED_FRONTIER.json'
ledger_data = git('show', HEAD + ':' + ledger_rel)
assert ledger_data == git('show', ':' + ledger_rel) == (REPO / ledger_rel).read_bytes()
assert sha256(ledger_data).hexdigest() == publication['fixed_register_sha256'] == 'f4b0dcdba20214f819bc6d15cd37704be4986729562932218162f47d1d0dc569'
ledger = json.loads(ledger_data)
assert len(ledger['cells']) == 231 and ledger['closed_cells'] == 224 and ledger['open_cells'] == 7
registered = {v['id']: v for v in ledger['cells']}

historical_doc_hashes = {}
for relative, heading in (
    ('research/nine/PROGRESS.md', b'## Exact C-family checkpoint: no new original credit\n'),
    ('research/nine/HANDOFF_A2_FIXED_CLOSURE.md', b'## Frozen C-family native checkpoint: all three originals remain OPEN\n')):
    before, after = git('show', HEAD + ':' + relative), git('show', ':' + relative)
    start = after.index(heading)
    stop = after.index(b'## Complete B580 original: 224 CLOSED / 7 OPEN\n', start)
    assert after[:start] + after[stop:] == before
    historical_doc_hashes[relative] = sha256(before).hexdigest()

for relative, expected in publication['copied_files'].items():
    target = PUB / relative
    assert target.stat().st_size == expected['bytes'] and digest(target) == expected['sha256']
    if relative == 'FROZEN_PACKET_README.md':
        source = PACKET / 'README.md'
    elif relative.startswith('transport_sources/'):
        source = C / 'code' / Path(relative).name
    elif relative == 'publish_c_finite_frontiers_v2.py':
        source = W / 'acceptance/publish_c_finite_frontiers_v2.py'
    elif (PACKET / relative).is_file():
        source = PACKET / relative
    else:
        source = C / relative
    assert digest(source) == digest(target), (source, target)
    bindings[str(source)] = digest(source)

combined = sha256()
total_bytes = 0
for index, part in enumerate(parts['parts'], 1):
    assert part['file'] == f'frozen_c_finite_frontiers_v2.tar.xz.part{index:03d}'
    data = (PUB / part['file']).read_bytes()
    assert len(data) == part['bytes'] and sha256(data).hexdigest() == part['sha256']
    combined.update(data)
    total_bytes += len(data)
assert total_bytes == parts['archive_bytes'] == 123751936
assert combined.hexdigest() == parts['archive_sha256'] == '60c5fef27b403c0312665b4d1e361f671d4fff0cc30aeda92a12de8c76f9ec2f'
assert digest(C / 'frozen_c_finite_frontiers_v2.tar.xz') == combined.hexdigest()
ready = read(PUB / 'C_FINITE_FRONTIERS_V2_ARCHIVE_AUDIT.json')
assert ready['archive_sha256'] == combined.hexdigest() and ready['archive_bytes'] == total_bytes
assert ready['status'] == 'PASS_FROZEN_C_ARCHIVE_AND_EVERY_MEMBER_BYTE_AUDIT'
assert ready['all_regular_members_rehashed'] and ready['inventory_and_member_names_exhaustive']
assert ready['no_links_or_path_traversal']
assert not ready['independent_arithmetic_replayed_now'] and not ready['standalone_arithmetic_packet']
assert digest(PUB / 'transport_sources/archive_frozen_c_frontiers.py') == ready['archive_auditor_source_sha256']

manifest = read(PUB / 'MANIFEST.json', ready['manifest_sha256'])
inventory = read(PUB / 'INVENTORY.json', ready['inventory_sha256'])
graph = read(PUB / 'C_FINITE_FRONTIERS_V2_HASH_GRAPH_REPLAY.json', ready['hash_graph_report_sha256'])
external = read(PUB / 'EXTERNAL_PROOF_INPUTS.json', ready['external_inputs_sha256'])
recovery = read(PUB / 'PUBLISHED_DEPENDENCY_RECOVERY.json', ready['published_recovery_sha256'])
catalog = read(PUB / 'PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json', ready['published_catalog_sha256'])
path_map = read(PUB / 'ORIGINAL_PATH_MAP.json')
config = read(PUB / 'FREEZE_CONFIG.json')
source_map = read(PUB / 'SOURCE_BINDINGS.json')
assert len(inventory) == graph['files_rehashed'] == 1393
assert len(inventory) + 1 == ready['regular_members'] == 1394
assert sum(v['bytes'] for v in inventory.values()) + (PUB / 'INVENTORY.json').stat().st_size == ready['uncompressed_member_bytes'] == 1493985907
assert graph['status'] == 'PASS_HASH_AND_COMPLETE_FRONTIER_TRANSPORT_ONLY'
assert not graph['arithmetic_replayed_now'] and not manifest['standalone_arithmetic_packet']
assert manifest['new_original_cells'] == manifest['new_masks'] == 0
for original, mapped in path_map.items():
    inv = inventory[mapped['payload_path']]
    assert (inv['sha256'], inv['bytes']) == (mapped['sha256'], mapped['bytes'])
for original, expected in source_map.items():
    assert path_map[original]['sha256'] == expected
assert len(config['rederived_inputs']) == manifest['included_rederived_outputs'] == 6
for original in config['rederived_inputs']:
    assert original not in external['input_sha256']
    assert inventory[path_map[original]['payload_path']]['category'] == 'fresh_rederived_output_or_exact_location_transport'

ext = external['input_sha256']
assert len(ext) == 994 and recovery['input_sha256'] == ext and set(recovery['entries']) == set(ext)
assert recovery['archives'] == catalog['archives']
assert recovery['catalog_sha256'] == digest(PUB / 'PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json')
members = {(m['archive_id'], m['member']): m for m in catalog['members']}
assert len(members) == len(catalog['members']) == 1954
assert len(catalog['archives']) == 4
for old, h in ext.items():
    entry = recovery['entries'][old]
    assert entry['sha256'] == h and entry == members[entry['archive_id'], entry['member']]
mapped_counts = dict(Counter(v['archive_id'] for v in recovery['entries'].values()))
assert mapped_counts == dict(a_c744_portable_open_checkpoint=527, cb882_whole_eight_checkpoint=450,
                             c887_fresh_whole_state=11, cd402_original_checkpoint_delta=6)
published_git_objects = 0
for archive in catalog['archives']:
    assert archive['published_commit'] == '4ce6c4567ddb810da03f64b2b139e5d3867661a6'
    blobs = archive.get('published_parts')
    if blobs is None:
        blobs = [dict(path=archive['published_archive'], git_blob=archive['published_git_blob'])]
    for blob in blobs:
        assert git('rev-parse', archive['published_commit'] + ':' + blob['path']).decode().strip() == blob['git_blob']
        published_git_objects += 1
prior_rehash = read(PUB / 'C_PUBLISHED_DEPENDENCY_B16_REHASH.json')
assert prior_rehash['members_rehashed'] == 1954 and prior_rehash['archive_count'] == 4
assert prior_rehash['catalog_sha256'] == digest(PUB / 'PUBLISHED_DEPENDENCY_ARCHIVE_CATALOG.json')
prefix = read(PUB / 'C_FINITE_FRONTIERS_V2_RECOVERY_PREFIX_MAP.json')
assert prefix['recovery_map_sha256'] == digest(PUB / 'PUBLISHED_DEPENDENCY_RECOVERY.json')
covered_paths = []
for rule in prefix['rules']:
    assert len(rule['input_paths']) == rule['exact_inputs']
    for old in rule['input_paths']:
        entry = recovery['entries'][old]
        assert entry['archive_id'] == rule['archive_id']
        relative = PurePosixPath(old).relative_to(PurePosixPath(rule['old_prefix']))
        assert str(PurePosixPath(rule['archive_member_prefix']) / relative) == entry['member']
        covered_paths.append(old)
assert len(covered_paths) == len(set(covered_paths)) == 994 and set(covered_paths) == set(ext)

checked_covers = []
reports = {}
for selected in manifest['covers']:
    name = selected['name']
    verbatim = read(PUB / selected['verbatim_manifest'], selected['original_manifest_sha256'])
    native = read(PUB / selected['native_manifest'])
    expected = deepcopy(verbatim)
    for n in expected['nodes']:
        n.pop('source_file', None)
    assert native == expected
    report = read(PUB / selected['exact_replay']['path'], selected['exact_replay']['sha256'])
    reports[name] = report
    counts = selected['counts']
    original = registered[selected['original_id']]
    assert original['status'] == 'OPEN'
    assert report['original_id'] == original['id'] and report['original_path'] == original['path']
    assert report['status'].startswith('PASS_PARTIAL_WHOLE_ORIGINAL_')
    assert report['manifest_snapshot_sha256'] == selected['original_manifest_sha256']
    assert report['nodes'] == counts['processed_nodes'] == len(native['nodes'])
    assert report['excluded_leaves'] == counts['candidate_excluded_leaves']
    assert report['unprocessed_leaves'] == counts['pending'] == len(native['pending'])
    assert report['stopped_leaves'] == counts['stopped'] == len(native['stopped'])
    assert report['open_leaves'] == counts['open_leaves'] == counts['pending'] + counts['stopped']
    assert not report['whole_original_excluded'] and not native['whole_candidate_closed']
    assert report['new_original_cells'] == report['new_masks'] == 0
    for key in ('all_nine_originals_retained', 'all_36_corners_and_pairs_retained',
                'all_five_cones_and_mask_bits_retained', 'no_other_original_consequence_imported', 'closed_shared_faces_retained'):
        assert report[key]
    assert not report['numerical_producer_imported'] and not report['lean_lake_ci_run']
    for old, h in report['input_sha256'].items():
        assert (path_map[old]['sha256'] if old in path_map else ext[old]) == h
    for n in verbatim['nodes']:
        old = str(Path(n.get('source_file', str(Path(selected['source_manifest_path']).parent / n['file']))))
        assert report['input_sha256'][old] == path_map[old]['sha256']
    g = next(v for v in graph['covers'] if v['name'] == name)
    assert g['counts'] == counts and g['exact_partial_report_included']
    unions = g['complete_declared_unions']
    total_nodes = counts['processed_nodes'] + counts['pending']
    assert total_nodes - 1 == sum({'proxy': 4, 'sat': 8, 'angle': 2, 'difference': 2}[k]*v for k, v in unions.items())
    assert total_nodes - sum(unions.values()) == counts['candidate_excluded_leaves'] + counts['open_leaves']
    checked_covers.append(dict(name=name, original_id=original['id'], counts=counts,
                               total_graph_domains=total_nodes, exact_report_sha256=selected['exact_replay']['sha256'],
                               original_manifest_sha256=selected['original_manifest_sha256']))

def terminal(report, index):
    row = next(v for v in report['leaf_table'] if v['index'] == index)
    assert row['excluded']
    return row['terminal']

assert terminal(reports['c887_main_259'], 201) == 'accepted_shared_sharp_boundary_terminal'
assert reports['c887_main_259']['deep_boundary_terminal_counts'] == {'original_all_nine_deep_boundary_cylinder': 0}
assert terminal(reports['cd402_opposite_507'], 505) == 'accepted_original_opposite_endpoint_AHID_23_100'
assert terminal(reports['cd402_opposite_507'], 503) == 'positive_exact_reserve'
assert reports['cd402_opposite_507']['independent_opposite_boundary_terminal_counts'] == {'original_opposite_endpoint_AHID_23_100': 1}
for i in (179, 193):
    assert terminal(reports['cb882_abid_138'], i) == 'accepted_original_opposite_endpoint_ABID_23_100'
assert reports['cb882_abid_138']['independent_ABID_boundary_terminal_counts'] == {'original_opposite_endpoint_ABID_23_100': 2}

for name in ('README.md', 'C_FINITE_FRONTIERS_V2_PUBLICATION_HANDOFF.md', 'FROZEN_PACKET_README.md'):
    text = (PUB / name).read_text()
    assert 'standalone' in text and 'OPEN' in text
assert 'not claimed' in (REPO / 'research/nine/A2_00100_C_FINITE_FRONTIERS_CHECKPOINT.md').read_text()
assert git('rev-parse', 'HEAD').decode().strip() == HEAD
assert git('diff', '--cached', '--name-only', '-z').decode().split('\0')[:-1] == names
bindings[str(Path(__file__).resolve())] = digest(__file__)
receipt = dict(
    status='PASS_C_V2_STAGED_NATIVE_PARTIAL_PUBLICATION_SCOPE_AND_BYTE_REVIEW',
    parent_commit=HEAD, staged_files=56, publication_directory_files=53,
    every_staged_blob_equals_reviewed_working_file=True,
    fixed_register_head_index_and_working_bytes_identical=True,
    fixed_register_sha256=publication['fixed_register_sha256'], immutable_original_definitions=231,
    closed_originals=224, open_originals=7, whole_masks_closed=8, whole_masks_total=32,
    only_handoff_and_progress_checkpoint_paragraphs_added=True,
    historical_document_bytes_preserved=historical_doc_hashes,
    copied_source_and_evidence_files=len(publication['copied_files']),
    all_copied_files_match_frozen_source_bytes=True,
    all_15_parts_and_concatenated_bytes_independently_rehashed=True,
    archive_bytes=total_bytes, archive_sha256=combined.hexdigest(),
    archive_regular_members=1394, inventoried_files=1393,
    expanded_archive_member_scan_not_repeated=True,
    pinned_archive_member_auditor_and_receipt_binding_checked=True,
    native_cover_report_and_manifest_bindings_checked=checked_covers,
    all_pending_and_stopped_counts_preserved=True,
    C887_alternative_counts_not_additive=True,
    selected_Cb882_scope_is_138_processed_13_pending_25_OPEN=True,
    later_Cb882_and_C887_continuation_not_imported=True,
    actual_guarded_terminal_counts_checked=dict(C887_sharp=1, Cd402_AHID=1, Cb882_ABID=2, deep_cylinder=0),
    exact_external_inputs=994, external_archive_member_mapping_counts=mapped_counts,
    recovery_rules=336, all_rules_limited_to_exact_input_lists=True,
    published_dependency_archive_count=4, catalog_regular_members=1954,
    published_git_objects_checked=published_git_objects,
    published_dependency_commit_is_immediate_parent_of_current_HEAD=True,
    ancestry_evidence='Immutable git cat-file commit header; shallow revision walking does not expose this parent',
    current_commit_object_payload_sha256=sha256(head_commit_bytes).hexdigest(),
    derived_outputs_included_and_not_external=6,
    native_arithmetic_reports_included=True, cold_standalone_arithmetic_replay_claimed=False,
    arithmetic_or_optimization_run_by_review=False, new_original_cells=0, new_masks=0,
    no_Lean_Lake_compilation_or_CI=True, blocking_findings=[],
    publisher_source_sha256=digest(PUB / 'publish_c_finite_frontiers_v2.py'),
    staged_blobs=staged, source_sha256=bindings)
assert not OUT.exists()
OUT.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: receipt[k] for k in ('status', 'staged_files', 'closed_originals', 'open_originals',
                                        'archive_bytes', 'archive_sha256', 'exact_external_inputs', 'new_original_cells')}, indent=2))
print('REPORT_SHA256', digest(OUT))
