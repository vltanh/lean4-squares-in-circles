#!/usr/bin/env python3
"""Add one exact archived diagnostic route; retain every mathematical byte.

Unchanged frozen files are hard-linked into fresh roots to avoid duplicate
gigabytes. Changed transport metadata always receives a new file. The old
delta and materialized packet are read-only inputs and remain unchanged.
The ordinary materializer can reproduce this revised delta with byte copies.
"""
from pathlib import Path
import argparse, hashlib, json, os

HERE = Path(__file__).resolve().parent
RUNNER = HERE / 'replay_portable_a1_checkpoint_v2.py'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def safe(root, name):
    relative = Path(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    path = (root / relative).resolve()
    assert path.is_relative_to(root)
    return path


def dump(path, value):
    assert not path.exists()
    path.write_text(json.dumps(value, indent=2) + '\n')


def link(source, target, expected):
    assert sha(source) == expected and not target.exists()
    target.parent.mkdir(parents=True, exist_ok=True)
    os.link(source, target)
    assert sha(target) == expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-delta', type=Path, required=True)
    parser.add_argument('--source-packet', type=Path, required=True)
    parser.add_argument('--output-delta', type=Path, required=True)
    parser.add_argument('--output-packet', type=Path, required=True)
    args = parser.parse_args()
    old_delta, old_packet = args.source_delta.resolve(), args.source_packet.resolve()
    delta, packet = args.output_delta.resolve(), args.output_packet.resolve()
    assert not delta.exists() and not packet.exists()
    assert not delta.is_relative_to(old_delta) and not packet.is_relative_to(old_packet)
    old_release = json.loads((old_delta / 'DELTA_MANIFEST.json').read_text())
    assert old_release['schema'] == 'complete_A1_consequence_thin_delta_files_v1'
    old_inventory = json.loads((old_delta / 'INPUT_MANIFEST.json').read_text())['files']
    assert sha(old_packet / 'INPUT_MANIFEST.json') == sha(old_delta / 'INPUT_MANIFEST.json')
    for name, digest in old_release['files'].items():
        assert sha(safe(old_delta, name)) == digest
    for name, digest in old_inventory.items():
        assert sha(safe(old_packet, name)) == digest
    delta.mkdir(parents=True)
    for name, digest in old_release['files'].items():
        if name in ('README.md', 'INPUT_MANIFEST.json'):
            continue
        link(safe(old_delta, name), safe(delta, name), digest)
    (delta / 'README.md').write_text((old_delta / 'README.md').read_text().replace(
        'replay_portable_a1_checkpoint_v1.py', 'replay_portable_a1_checkpoint_v2.py') +
        '\nTransport revision2 adds the archived `cover_reviews` diagnostic directory.\n'
        'Its full subtree is disjoint from all inputs; the packet mutation guard is unchanged.\n')
    for source in (RUNNER, Path(__file__).resolve()):
        target = delta / source.name
        assert not target.exists()
        target.write_bytes(source.read_bytes())
    revision = dict(schema='A1_exact_diagnostic_output_transport_revision_v2',
        preceding_delta_manifest_sha256=sha(old_delta / 'DELTA_MANIFEST.json'),
        preceding_assembled_input_manifest_sha256=sha(old_delta / 'INPUT_MANIFEST.json'),
        previous_runner_sha256=sha(old_delta / 'replay_portable_a1_checkpoint_v1.py'),
        new_runner_sha256=sha(RUNNER),
        added_exact_output_route=dict(source_basename='verify_central_cover_bounds.py', directory='cover_reviews'),
        full_output_subtree_disjoint_from_all_inputs_required=True,
        all_mathematical_source_and_literal_bytes_unchanged=True,
        old_roots_unchanged=True, unchanged_files_hard_linked=True,
        original_failure='The strict packet guard correctly rejected an archived diagnostic mkdir in cover_reviews.',
        new_original_cells=0, new_masks=0)
    dump(delta / 'TRANSPORT_REVISION.json', revision)
    inventory = dict(old_inventory)
    for path in delta.rglob('*'):
        if path.is_file():
            inventory[str(path.relative_to(delta))] = sha(path)
    assert {k:v for k,v in inventory.items() if k.startswith('payload/')} == {
        k:v for k,v in old_inventory.items() if k.startswith('payload/')}
    dump(delta / 'INPUT_MANIFEST.json', dict(schema='complete_A1_thin_assembled_input_inventory_v1',
        files=dict(sorted(inventory.items())), external_workspace_reads_forbidden=True,
        numerical_imports_forbidden=True))
    release = dict(old_release)
    release.update(files={str(p.relative_to(delta)):sha(p) for p in sorted(delta.rglob('*')) if p.is_file()},
        assembled_input_manifest_sha256=sha(delta / 'INPUT_MANIFEST.json'),
        transport_revision_sha256=sha(delta / 'TRANSPORT_REVISION.json'))
    dump(delta / 'DELTA_MANIFEST.json', release)
    packet.mkdir(parents=True)
    for name, digest in release['files'].items():
        link(safe(delta, name), safe(packet, name), digest)
    link(delta / 'DELTA_MANIFEST.json', packet / 'DELTA_MANIFEST.json', sha(delta / 'DELTA_MANIFEST.json'))
    for name, digest in inventory.items():
        target = safe(packet, name)
        if not target.exists():
            link(safe(old_packet, name), target, digest)
        assert sha(target) == digest
    for name, digest in old_release['files'].items():
        assert sha(safe(old_delta, name)) == digest
    for name, digest in old_inventory.items():
        assert sha(safe(old_packet, name)) == digest
    result = dict(status='PASS_IMMUTABLE_A1_DIAGNOSTIC_TRANSPORT_REVISION',
        delta=str(delta), packet=str(packet), input_files=len(inventory),
        input_manifest_sha256=sha(delta / 'INPUT_MANIFEST.json'),
        delta_manifest_sha256=sha(delta / 'DELTA_MANIFEST.json'),
        unchanged_mathematical_payload_files=sum(k.startswith('payload/') for k in inventory),
        old_inputs_rehashed_and_unchanged=True, new_original_cells=0, new_masks=0)
    dump(delta.parent / (delta.name + '_MATERIALIZATION.json'), result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
