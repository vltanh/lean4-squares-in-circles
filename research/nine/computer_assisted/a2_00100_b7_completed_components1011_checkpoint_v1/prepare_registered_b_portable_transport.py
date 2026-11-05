"""Add verified historical aliases and documentation without changing proof bytes.

This transport preparation supplies no arithmetic or original-cell credit.
The original builder packet is preserved, and the new packet requires a fresh
portable replay with the unchanged independent exact decoder.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import shutil


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('source', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--prior', type=Path, required=True)
    ap.add_argument('--historical-prefix', type=Path, required=True)
    ap.add_argument('--attachment', action='append', default=[],
                    help='packet-relative-name=source-file')
    a = ap.parse_args()
    source, out, prior = a.source.resolve(), a.output.resolve(), a.prior.resolve()
    assert not out.exists()
    old_raw = (source / 'INPUT_MANIFEST.json').read_bytes()
    old = json.loads(old_raw)
    info = json.loads((source / 'ORIGINAL_PROOF.json').read_text())
    assert info['original_id'].startswith('negative-')
    for name, expected in old['files'].items():
        assert digest(source / name) == expected, name
    raw = (source / 'BINDINGS.json').read_bytes()
    bindings = json.loads(raw)
    historical = a.historical_prefix.absolute()
    canonical = historical.resolve()
    assert historical != canonical and historical.is_dir()
    additions = {}
    for name, entry in list(bindings.items()):
        path = Path(name)
        if not path.is_relative_to(canonical):
            continue
        alias = str(historical / path.relative_to(canonical))
        assert Path(alias).resolve() == path
        assert digest(alias) == entry['sha256']
        assert entry['root'] in ('packet', 'prior')
        base = source if entry['root'] == 'packet' else prior
        target = (base / entry['path']).resolve()
        assert target.is_relative_to(base) and digest(target) == entry['sha256']
        if alias in bindings:
            assert bindings[alias] == entry
        else:
            bindings[alias] = entry
            additions[alias] = dict(canonical=name, binding=entry)
    assert additions
    tree_entry = info['tree']
    assert tree_entry['root'] == 'packet'
    tree = source / tree_entry['path']
    assert digest(tree) == tree_entry['sha256']
    parent = json.loads(tree.read_text())['parent']
    assert parent['path'] == str(historical / 'whole_B_roots' / (info['original_id'] + '.json'))
    assert bindings[parent['path']]['sha256'] == parent['sha256']
    shutil.copytree(source, out)
    (out / 'INPUT_MANIFEST_BEFORE_TRANSPORT.json').write_bytes(old_raw)
    (out / 'BINDINGS_BEFORE_TRANSPORT.json').write_bytes(raw)
    (out / 'BINDINGS.json').write_text(json.dumps(bindings, indent=2) + '\n')
    attached = {}
    for argument in a.attachment:
        name, source_file = argument.split('=', 1)
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        target = out / relative
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_file, target)
        assert digest(source_file) == digest(target)
        attached[name] = dict(source=str(Path(source_file).resolve()), sha256=digest(target))
    tool = out / 'acceptance_tools' / Path(__file__).name
    assert not tool.exists()
    tool.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(__file__, tool)
    for name, expected in old['files'].items():
        if name != 'BINDINGS.json':
            assert digest(out / name) == expected, name
    receipt = dict(
        schema='registered_B_verified_portable_transport_preparation_v1',
        original_id=info['original_id'], complete=info['complete'],
        source_input_manifest_sha256=sha256(old_raw).hexdigest(),
        original_bindings_sha256=sha256(raw).hexdigest(),
        extended_bindings_sha256=digest(out / 'BINDINGS.json'),
        historical_prefix=str(historical), canonical_prefix=str(canonical),
        added_aliases=additions, added_alias_count=len(additions), attachments=attached,
        every_alias_matches_already_frozen_input=True,
        all_original_inputs_except_bindings_unchanged=True,
        all_literal_proof_and_checker_bytes_unchanged=True,
        original_builder_packet_preserved=True,
        no_arithmetic_acceptance_inferred=True, fresh_portable_replay_required=True,
        original_credit=0, mask_credit=0)
    (out / 'TRANSPORT_PREPARATION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    old['files'] = {str(p.relative_to(out)): digest(p) for p in sorted(out.rglob('*'))
                    if p.is_file() and p != out / 'INPUT_MANIFEST.json'}
    (out / 'INPUT_MANIFEST.json').write_text(json.dumps(old, indent=2) + '\n')
    print(json.dumps(dict(status='VERIFIED_TRANSPORT_PREPARED_FRESH_REPLAY_REQUIRED',
                         original_id=info['original_id'], complete=info['complete'],
                         aliases=len(additions), attachments=len(attached),
                         inputs=len(old['files']),
                         input_manifest_sha256=digest(out / 'INPUT_MANIFEST.json')), indent=2))


if __name__ == '__main__':
    main()
