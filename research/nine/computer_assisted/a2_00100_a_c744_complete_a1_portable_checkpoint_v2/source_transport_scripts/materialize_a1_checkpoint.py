#!/usr/bin/env python3
"""Materialize unchanged complete-A1 delta/base bytes into a fresh proof root."""
from pathlib import Path
import argparse, hashlib, json, shutil


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def safe(root, name):
    root = Path(root).resolve()
    relative = Path(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    path = (root / relative).resolve()
    assert path.is_relative_to(root), ('escaping packet member', name)
    return path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--delta', type=Path, required=True)
    parser.add_argument('--a-base', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    delta, base, output = args.delta.resolve(), args.a_base.resolve(), args.output.resolve()
    assert not output.exists()
    assert not output.is_relative_to(delta) and not output.is_relative_to(base)
    release = json.loads((delta / 'DELTA_MANIFEST.json').read_text())
    assert release['schema'] == 'complete_A1_consequence_thin_delta_files_v1'
    assert release['new_original_cells'] == release['new_masks'] == 0
    for name, digest in release['files'].items():
        assert sha(safe(delta, name)) == digest
    plan = json.loads((delta / 'PUBLICATION_PLAN.json').read_text())
    assert sha(delta / 'PUBLICATION_PLAN.json') == release['plan_sha256']
    original_base = plan['base_A_portable_archive']
    assert sha(base / 'INPUT_MANIFEST.json') == original_base['input_manifest_sha256']
    base_inventory = json.loads((base / 'INPUT_MANIFEST.json').read_text())['files']
    inventory = json.loads((delta / 'INPUT_MANIFEST.json').read_text())['files']
    bindings = json.loads((delta / 'BINDINGS.json').read_text())['files']
    output.mkdir(parents=True)
    for name, digest in release['files'].items():
        source, target = safe(delta, name), safe(output, name)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert sha(target) == digest
    # The thin release manifest is transport metadata, not a proof input.
    shutil.copyfile(delta / 'DELTA_MANIFEST.json', output / 'DELTA_MANIFEST.json')
    for original, entry in original_base['reused_files'].items():
        member, digest = entry['member'], entry['sha256']
        assert base_inventory[member] == digest
        source = safe(base, member)
        assert sha(source) == digest
        destination = bindings[original]['path']
        assert bindings[original]['sha256'] == digest and inventory[destination] == digest
        target = safe(output, destination)
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert sha(target) == digest
        else:
            shutil.copyfile(source, target)
        assert sha(target) == digest
    for name, digest in inventory.items():
        assert sha(safe(output, name)) == digest
    assert sha(output / 'INPUT_MANIFEST.json') == release['assembled_input_manifest_sha256']
    assert sha(base / 'INPUT_MANIFEST.json') == original_base['input_manifest_sha256']
    report = dict(status='PASS_MATERIALIZED_COMPLETE_A1_CONSEQUENCE_THIN_PACKET',
        delta_manifest_sha256=sha(delta / 'DELTA_MANIFEST.json'),
        assembled_input_manifest_sha256=sha(output / 'INPUT_MANIFEST.json'),
        new_delta_files=len(release['files']), reused_A_aliases=len(original_base['reused_files']),
        assembled_input_files=len(inventory),
        assembled_input_bytes=sum(safe(output, name).stat().st_size for name in inventory),
        all_source_bytes_unchanged=True, no_source_packet_modified=True,
        new_original_cells=0, new_masks=0)
    destination = output.parent / (output.name + '_MATERIALIZATION.json')
    assert not destination.exists()
    destination.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
