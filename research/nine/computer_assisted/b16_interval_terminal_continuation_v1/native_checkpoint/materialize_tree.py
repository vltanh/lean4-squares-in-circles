#!/usr/bin/env python3
"""Copy exact retained B16 node bytes into a fresh complete tree directory."""
from pathlib import Path
import argparse
import json
import shutil
from verify_packet import check, read, sha, TREE, CHANGED


def main():
    if not __debug__:
        raise RuntimeError('Exact materialization checks require assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--prior-tree', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent; output = args.output.resolve()
    prior = args.prior_tree.resolve(); assert not output.exists()
    check(here, prior)
    manifest = read(here / TREE / 'manifest.json')
    output.mkdir(parents=True)
    for entry in manifest['nodes']:
        source = (here / TREE if entry['index'] in CHANGED else prior) / entry['file']
        target = output / entry['file']
        assert sha(source) == entry['sha256']
        shutil.copyfile(source, target)
        assert sha(target) == entry['sha256']
    for name in ('manifest.json', 'CONTINUATION_ATTACHMENT.json'):
        shutil.copyfile(here / TREE / name, output / name)
        assert sha(output / name) == sha(here / TREE / name)
    check(here, prior)
    print(json.dumps(dict(status='PASS_EXACT_45_NODE_B16_CONTINUATION_MATERIALIZATION',
        nodes=45, new_terminal_payloads=14, unchanged_published_payloads=31,
        tree_manifest_sha256=sha(output / 'manifest.json'),
        every_target_rehashed=True, old_inputs_unchanged=True,
        weighted_arithmetic_repeated=False, new_original_cells=0, new_masks=0)), flush=True)


if __name__ == '__main__':
    main()
