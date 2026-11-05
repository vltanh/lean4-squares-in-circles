"""Bind reviewed hand/table attachments before the fresh portable replay.

All native node records, decoder files, original definitions and builder
inputs must remain byte-identical. This adds acceptance documentation only.
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
    ap.add_argument('packet', type=Path)
    ap.add_argument('review_directory', type=Path)
    ap.add_argument('archiver', type=Path)
    a = ap.parse_args()
    packet = a.packet.resolve()
    reviews = a.review_directory.resolve()
    here = Path(__file__).resolve().parent
    info = json.loads((packet / 'ORIGINAL_PROOF.json').read_text())
    assert info['original_id'] == 'negative-f14f5bc4eafdf50d'
    assert info['complete'] and not info['open_prototype']
    manifest_path = packet / 'INPUT_MANIFEST.json'
    old_raw = manifest_path.read_bytes()
    old = json.loads(old_raw)
    for name, expected in old['files'].items():
        assert digest(packet / name) == expected, name
    attachment = here / 'BF14_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md'
    final_review = json.loads((reviews / 'BF14_FINAL_PHYSICAL_SOURCE_REVIEW.json').read_text())
    assert final_review['status'] == 'PASS_FINAL_PHYSICAL_SOURCE_ATTACHMENT_AND_COMPLETE_COVER_REVIEW'
    assert digest(attachment) in final_review['source_sha256'].values()
    table = json.loads((here / 'BF14_COMPLETE_LITERAL_TABLE_AUDIT.json').read_text())
    assert table['status'] == 'PASS_BF14_COMPLETE_LITERAL_TABLE_AND_ROW_ACCOUNTING'
    assert table['terminal_leaves'] == 461
    additions = {}

    def add(source, relative):
        target = packet / relative
        assert not target.exists(), target
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert digest(source) == digest(target)
        additions[relative] = dict(source=str(Path(source).resolve()), sha256=digest(target))

    add(attachment, attachment.name)
    for name in ('BF14_FINAL_PHYSICAL_SOURCE_REVIEW.json',
                 'BF14_FINAL_PHYSICAL_SOURCE_REVIEW.md',
                 'BF14_FINAL_STRUCTURAL_REVIEW.json',
                 'BF14_FINAL_COMPLETE_TERMINAL_TABLE.json',
                 'BF14_FINAL_COMPLETE_COVER_TABLE.json',
                 'PHYSICAL_PRE_REVIEW.json', 'PHYSICAL_PRE_REVIEW.md',
                 'review_final_structure.py'):
        add(reviews / name, 'independent_review/' + name)
    for name in ('audit_bf14_literal_table.py', 'audit_bf14_complete_archive.py',
                 'freeze_bf14_acceptance_inputs.py'):
        add(here / name, 'acceptance_tools/' + name)
    add(here / 'BF14_COMPLETE_LITERAL_TABLE_AUDIT.json',
        'original_audits/BF14_COMPLETE_LITERAL_TABLE_AUDIT.json')
    add(a.archiver, 'acceptance_tools/' + a.archiver.name)
    previous = packet / 'INPUT_MANIFEST_BEFORE_ATTACHMENTS.json'
    assert not previous.exists()
    previous.write_bytes(old_raw)
    proof = dict(schema='bf14_nonmutating_acceptance_attachment_freeze_v1',
                 original_id=info['original_id'],
                 previous_input_manifest_sha256=sha256(old_raw).hexdigest(),
                 unchanged_original_inputs=len(old['files']),
                 every_original_input_unchanged=True,
                 literal_node_and_checker_bytes_unchanged=True,
                 additions=additions, fresh_portable_replay_still_required=True,
                 original_credit=0, mask_credit=0)
    proof_path = packet / 'PACKAGING_ATTACHMENTS.json'
    assert not proof_path.exists()
    proof_path.write_text(json.dumps(proof, indent=2) + '\n')
    for name, expected in old['files'].items():
        assert digest(packet / name) == expected, name
    old['files'] = {str(p.relative_to(packet)): digest(p)
                    for p in sorted(packet.rglob('*'))
                    if p.is_file() and p != manifest_path}
    manifest_path.write_text(json.dumps(old, indent=2) + '\n')
    print(json.dumps(dict(status='FROZEN_BF14_REVIEW_ATTACHMENTS_REPLAY_REQUIRED',
                          original_inputs=proof['unchanged_original_inputs'],
                          final_inputs=len(old['files']),
                          input_manifest_sha256=digest(manifest_path)), indent=2))


if __name__ == '__main__':
    main()
