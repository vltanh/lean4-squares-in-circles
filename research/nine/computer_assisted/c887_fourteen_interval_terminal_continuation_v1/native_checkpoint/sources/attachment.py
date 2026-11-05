"""Pinned reuse of the complete C88791 proof and its accepted three-terminal continuation."""
from copy import deepcopy
from pathlib import Path
import historical_leaf_source as H

LEAVES = (1, 3, 5, 11, 12, 17, 19, 22, 71, 73, 75, 84, 85, 87)
OLD_CLOSED = (29, 30, 64)
TERMINAL = dict(kind='accepted_center_interval_terminal', label='empty propagated original center interval')
OLD_TERMINAL = dict(kind='accepted_effective_angle_terminal', label='accepted D/G separator has positive vertical component')
PREDECESSOR_MANIFEST_SHA = '276bae5827e64c8e9cabd1c5907d5047b26cde6cabc68fee9440a44f067f7e09'
PREDECESSOR_REPORT_SHA = 'ab1f2aac0ad99539365df036ce3c884b6af2f7ebecc5c890fdd8b35df5f3a51a'


def source_freeze(here):
    if not __debug__:
        raise RuntimeError('Exact assertions required')
    freeze = H.read(Path(here)/'SOURCE_BINDING.json')
    assert freeze['schema'] == 'C887_fourteen_existing_interval_terminal_sources_v1'
    for name, digest in freeze['files'].items():
        assert H.sha(Path(here)/name) == digest
    return freeze


def closed_record(record, terminal):
    assert record['status'] == 'OPEN' and record['rounds'] == []
    assert record['initial'] == record['final'] and 'terminal' not in record
    result = deepcopy(record)
    result['status'] = 'CANDIDATE_CLOSED'
    result['terminal'] = deepcopy(terminal)
    del result['final']
    return result


def predecessor(packet, tree, report_path):
    packet, tree, report_path = map(Path, (packet, tree, report_path))
    old_report, old_manifest, old_entries, old_records, inputs = H.validate_historical_proof(packet)
    assert H.sha(tree/'manifest.json') == PREDECESSOR_MANIFEST_SHA
    assert H.sha(report_path) == PREDECESSOR_REPORT_SHA
    report = H.read(report_path); manifest = H.read(tree/'manifest.json')
    assert report['status'] == 'PASS_COMPLETE_C887_COVER_WITH_THREE_FRESH_EXISTING_TERMINALS'
    assert report['new_manifest_sha256'] == PREDECESSOR_MANIFEST_SHA
    assert report['accepted_old_complete_consumer_report_sha256'] == H.REPORT_SHA
    assert report['accepted_old_complete_manifest_sha256'] == H.TREE_SHA
    assert report['fresh_terminal_leaf_indices'] == list(OLD_CLOSED)
    assert report['historical_input_identities_rehashed'] == inputs
    assert (report['all_nodes'], report['retained_leaf_domains'], report['excluded_leaf_domains'], report['open_leaf_domains']) == (91,73,3,70)
    assert report['new_original_cells'] == report['new_masks'] == 0
    entries = {e['index']: e for e in manifest['nodes']}
    assert len(entries) == len(manifest['nodes']) == 91 and set(entries) == set(old_entries)
    records = {}; pins = {str(tree/'manifest.json'): PREDECESSOR_MANIFEST_SHA, str(report_path): PREDECESSOR_REPORT_SHA}
    for index, entry in entries.items():
        expected_entry = deepcopy(old_entries[index])
        p = tree/entry['file']; digest = H.sha(p); assert digest == entry['sha256']; pins[str(p)] = digest
        record = H.read(p)
        if index in OLD_CLOSED:
            assert record == closed_record(old_records[index], OLD_TERMINAL)
            expected_entry['status'] = 'CANDIDATE_CLOSED'; expected_entry['sha256'] = digest
        else:
            assert record == old_records[index] and digest == old_entries[index]['sha256']
        assert entry == expected_entry
        records[index] = record
    for index in LEAVES:
        assert entries[index]['children'] == [] and entries[index]['status'] == 'OPEN'
        assert records[index]['rounds'] == [] and records[index]['initial'] == records[index]['final']
    return old_report, old_manifest, old_entries, old_records, inputs, report, manifest, entries, records, pins


def composed_statuses(entries):
    visited = set(); closed_parents = []; leaves = []
    def visit(index):
        assert index not in visited; visited.add(index)
        entry = entries[index]
        if not entry['children']:
            excluded = index in LEAVES or index in OLD_CLOSED
            assert entry['status'] == ('CANDIDATE_CLOSED' if excluded else 'OPEN')
            leaves.append(dict(index=index, excluded=excluded))
            return excluded
        outcomes = [visit(child) for child in entry['children']]
        closed = all(outcomes)
        entry['status'] = 'CANDIDATE_COVER_CLOSED' if closed else 'OPEN'
        if closed: closed_parents.append(index)
        return closed
    closed = visit(0)
    assert visited == set(entries) and len(leaves) == 73
    assert not closed and sum(row['excluded'] for row in leaves) == 17
    return leaves, closed_parents


def expected_manifest(prior, replacements, freeze_sha):
    result = deepcopy(prior); entries = {e['index']: e for e in result['nodes']}
    assert [r['index'] for r in replacements] == list(LEAVES)
    for row in replacements:
        index = row['index']; entry = entries[index]
        assert entry['sha256'] == row['old_sha256'] and entry['children'] == []
        entry['status'] = 'CANDIDATE_CLOSED'; entry['sha256'] = row['new_sha256']
    leaves, parents = composed_statuses(entries)
    result['additional_interval_terminal_continuation'] = dict(
        schema='C887_published91_fourteen_existing_interval_terminals_v1',
        predecessor_manifest_sha256=PREDECESSOR_MANIFEST_SHA,
        predecessor_exact_report_sha256=PREDECESSOR_REPORT_SHA,
        original_complete_consumer_report_sha256=H.REPORT_SHA,
        fresh_terminal_leaf_indices=list(LEAVES), retained_previously_excluded_leaves=list(OLD_CLOSED),
        replacements=replacements, source_binding_sha256=freeze_sha,
        unchanged_payloads=77, recomputed_closed_parent_indices=parents,
        leaf_domains=73, excluded_leaf_domains=17, open_leaf_domains=56,
        historical_bound_arithmetic_reused=True, new_hull_or_endpoint_family_used=False,
        whole_original_exclusion_claimed=False, numerical_search_started=False)
    assert result['status'] == 'OPEN'
    return result
