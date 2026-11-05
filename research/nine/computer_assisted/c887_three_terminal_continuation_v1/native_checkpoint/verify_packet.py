#!/usr/bin/env python3
"""Byte/header checks for the thin C887 terminal continuation; no arithmetic."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def main():
    if not __debug__:
        raise RuntimeError('Packaging assertions must be enabled')
    parser = argparse.ArgumentParser()
    parser.add_argument('--historical-packet', type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    inventory = read(root / 'INPUT_MANIFEST.json')
    assert inventory['schema'] == 'C887_three_terminal_publication_inventory_v1'
    actual = {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
    assert actual == set(inventory['files']) | {'INPUT_MANIFEST.json'}
    for name, entry in inventory['files'].items():
        path = root / name
        assert path.resolve().is_relative_to(root)
        assert path.stat().st_size == entry['bytes'] and digest(path) == entry['sha256']
    report = read(root / 'EXACT_REPLAY.json')
    manifest = read(root / 'continuation/manifest.json')
    dependencies = read(root / 'PUBLISHED_DEPENDENCIES.json')
    observed = read(root / 'OBSERVED_EXECUTION.json')
    freeze = read(root / 'code/SOURCE_BINDING.json')
    assert report['status'] == 'PASS_COMPLETE_C887_COVER_WITH_THREE_FRESH_EXISTING_TERMINALS'
    assert report['new_manifest_sha256'] == digest(root / 'continuation/manifest.json')
    assert report['source_binding_sha256'] == digest(root / 'code/SOURCE_BINDING.json')
    assert report['new_original_cells'] == report['new_masks'] == 0
    assert (report['all_nodes'], report['retained_leaf_domains'],
            report['excluded_leaf_domains'], report['open_leaf_domains']) == (91, 73, 3, 70)
    assert report['original_still_open'] is True and manifest['status'] == 'OPEN'
    assert report['historical_57_round_bound_arithmetic_reused_not_repeated'] is True
    assert observed['actual_process_exit_observed'] is True and observed['exit_code'] == 0
    assert observed['exact_report_sha256'] == digest(root / 'EXACT_REPLAY.json')
    for name, pin in freeze['files'].items():
        assert digest(root / 'code' / name) == pin
    nodes = {entry['index']: entry for entry in manifest['nodes']}
    assert len(nodes) == 91
    changed = (29, 30, 64)
    for index in changed:
        node = nodes[index]
        path = root / 'continuation' / node['file']
        assert digest(path) == node['sha256']
        record = read(path)
        assert node['children'] == [] and node['parent'] == 27 and node['depth'] == 12
        assert node['status'] == record['status'] == 'CANDIDATE_CLOSED'
        assert record['rounds'] == [] and 'final' not in record
        assert record['terminal'] == {
            'kind': 'accepted_effective_angle_terminal',
            'label': 'accepted D/G separator has positive vertical component'}
    aliases = dependencies['unchanged_node_payloads']
    assert len(aliases) == 88
    assert {entry['index'] for entry in aliases} == set(nodes) - set(changed)
    for entry in aliases:
        assert entry['file'] == nodes[entry['index']]['file']
        assert entry['sha256'] == nodes[entry['index']]['sha256']
    receipt = read(root / 'published_dependency_metadata/fresh_replay/PORTABLE_RECEIPT.json')
    assert digest(root / 'published_dependency_metadata/fresh_replay/PORTABLE_RECEIPT.json') == dependencies['published_fresh_portable_receipt_sha256']
    assert receipt['packet_manifest_sha256'] == dependencies['assembled_packet_input_manifest_sha256']
    old_tree = receipt['exact_tree_replays']['first_weighted']
    assert (old_tree['nodes'], old_tree['leaf_domains'], old_tree['rounds'],
            old_tree['deductions'], old_tree['printed_rows_checked']) == (91, 73, 57, 8780, 39146)
    historical_checked = False
    if args.historical_packet is not None:
        packet = args.historical_packet.resolve()
        spec = importlib.util.spec_from_file_location('historical_identity_checks', root / 'code/historical_leaf_source.py')
        module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
        old_report, old_manifest, entries, records, pins = module.validate_historical_proof(packet)
        assert len(pins) == 543 and len(entries) == 91
        for entry in aliases:
            assert digest(packet / entry['published_packet_relative_path']) == entry['sha256']
        historical_checked = True
    print(json.dumps(dict(status='PASS_C887_THREE_TERMINAL_PACKET_IDENTITIES',
        files=len(inventory['files']), bytes=inventory['total_bytes'],
        manifest_sha256=digest(root / 'INPUT_MANIFEST.json'),
        unchanged_node_aliases=88, historical_packet_identities_checked=historical_checked,
        new_terminal_arithmetic_repeated=False, old_weighted_arithmetic_repeated=False,
        new_original_cells=0, new_masks=0)), flush=True)


if __name__ == '__main__':
    main()
