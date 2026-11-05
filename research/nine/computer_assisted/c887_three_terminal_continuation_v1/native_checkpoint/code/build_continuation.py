#!/usr/bin/env python3
"""Preserve the published complete91 cover and replace exactly three leaves."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import shutil
import historical_leaf_source as H

LEAVES = (29, 30, 64)
TERMINAL = dict(kind='accepted_effective_angle_terminal',
                label='accepted D/G separator has positive vertical component')


def main():
    if not __debug__:
        raise RuntimeError('Exact source checks require assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--tree', type=Path, required=True)
    args = parser.parse_args(); packet = args.packet.resolve(); tree = args.tree.resolve()
    here = Path(__file__).resolve().parent
    freeze = H.read(here / 'SOURCE_BINDING.json')
    for name, digest in freeze['files'].items():
        assert H.sha(here / name) == digest
    assert not tree.exists()
    _, source, entries, records, _ = H.validate_historical_proof(packet)
    tree.mkdir()
    manifest = deepcopy(source); manifest_nodes = {e['index']: e for e in manifest['nodes']}
    replacements = []
    for index, entry in entries.items():
        target = tree / entry['file']
        if index not in LEAVES:
            shutil.copyfile(packet / H.TREE_REL / entry['file'], target)
            assert H.sha(target) == entry['sha256']
            continue
        assert entry['children'] == [] and entry['parent'] == 27 and entry['depth'] == 12
        original = records[index]
        assert original['rounds'] == [] and original['initial'] == original['final']
        record = deepcopy(original)
        record['status'] = 'CANDIDATE_CLOSED'; record['terminal'] = deepcopy(TERMINAL)
        del record['final']
        target.write_text(json.dumps(record, indent=2) + '\n')
        manifest_nodes[index]['status'] = 'CANDIDATE_CLOSED'
        manifest_nodes[index]['sha256'] = H.sha(target)
        replacements.append(dict(index=index, old_sha256=entry['sha256'], new_sha256=H.sha(target)))
    manifest['terminal_continuation'] = dict(
        schema='C887_published91_three_existing_terminal_continuation_v1',
        source_manifest_sha256=H.TREE_SHA, source_consumer_report_sha256=H.REPORT_SHA,
        fresh_terminal_leaf_indices=list(LEAVES), replacements=replacements,
        source_binding_sha256=H.sha(here / 'SOURCE_BINDING.json'),
        unchanged_parent_and_sibling_payloads=88, historical_weighted_arithmetic_reused=True,
        whole_original_exclusion_claimed=False, numerical_search_started=False)
    (tree / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(dict(status='PREPARED_COMPLETE91_WITH_THREE_NEW_TERMINAL_RECORDS',
        manifest_sha256=H.sha(tree / 'manifest.json'), nodes=91,
        changed_leaf_records=list(LEAVES), unchanged_records=88,
        retained_leaf_domains=73, candidate_excluded_leaves=3, remaining_open_leaves=70)), flush=True)


if __name__ == '__main__':
    main()
