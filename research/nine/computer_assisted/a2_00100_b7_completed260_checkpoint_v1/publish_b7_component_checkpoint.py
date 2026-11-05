"""Publish a replayed OPEN B7 checkpoint and frozen boundary source helpers.

The immutable original ledger is read and rehashed, never modified. No
whole-original or mask credit is granted by this checkpoint publication.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import shutil
import tarfile


def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser()
    for name in ('repo', 'work', 'packet', 'fresh', 'archive', 'reviews'):
        ap.add_argument(name, type=Path)
    a = ap.parse_args()
    repo, work, packet, fresh, archive, reviews = [getattr(a, name).resolve()
        for name in ('repo', 'work', 'packet', 'fresh', 'archive', 'reviews')]
    nine = repo / 'research/nine'
    ledger = nine / 'gates/A2_00100_FIXED_FRONTIER.json'
    ledger_hash = digest(ledger)
    register = read(ledger)
    cell = next(c for c in register['cells'] if c['id'] == 'negative-7c60be8b07a358e9')
    assert cell['status'] == 'OPEN' and len(register['cells']) == 231
    info = read(packet / 'ORIGINAL_PROOF.json')
    portable = read(fresh / 'PORTABLE_RECEIPT.json')
    native = read(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    report = read(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    ready = read(archive / 'ARCHIVE_READY.json')
    assert info['original_id'] == portable['original_id'] == ready['original_id'] == cell['id']
    assert info['original_path'] == cell['path']
    assert not info['complete'] and info['open_prototype']
    assert portable['status'] == 'PASS_PORTABLE_OPEN_PROTOTYPE'
    assert not portable['complete'] and not portable['whole_original_proved']
    assert portable['every_new_bound_and_cover_replayed']
    assert portable['all_inputs_rehashed_at_completion']
    assert portable['external_workspace_reads_forbidden']
    assert not portable['numerical_modules_imported'] and not portable['lean_lake_ci_run']
    assert portable['new_original_ledger_credit'] == portable['new_mask_ledger_credit'] == 0
    assert portable['packet_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert portable['report_sha256'] == digest(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    for item in (native, report):
        assert item['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
        assert item['entire_registered_original_domain_retained']
        assert item['nodes'] == 813 and item['excluded_leaves'] == 442 and item['open_leaves'] == 6
        assert not item['complete'] and not item['whole_original_proved']
    for key, value in info['counts'].items():
        assert native[key] == report[key] == value
    assert ready['all_member_hashes_match'] and ready['xz_integrity_pass']
    assert not ready['complete_original']
    assert ready['new_original_ledger_credit'] == ready['new_mask_ledger_credit'] == 0
    assert ready['portable_receipt_sha256'] == digest(fresh / 'PORTABLE_RECEIPT.json')
    whole_archive = archive / ready['archive']
    assert whole_archive.stat().st_size == ready['archive_bytes']
    assert digest(whole_archive) == ready['archive_sha256']
    out = nine / 'computer_assisted/a2_00100_b7_completed260_checkpoint_v1'
    helper_out = nine / 'computer_assisted/a2_00100_original_boundary_guard_helpers_v1'
    assert not out.exists() and not helper_out.exists()
    out.mkdir()

    def copy(source, target):
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        assert digest(source) == digest(target)

    parts = []
    combined = sha256()
    with whole_archive.open('rb') as stream:
        for index, block in enumerate(iter(lambda: stream.read(8 * 1024 * 1024), b''), 1):
            name = whole_archive.name + f'.part{index:03d}'
            target = out / name
            target.write_bytes(block)
            expected = sha256(block).hexdigest()
            assert digest(target) == expected
            parts.append(dict(file=name, bytes=len(block), sha256=expected))
            combined.update(block)
    assert combined.hexdigest() == ready['archive_sha256']
    dump(out / 'ARCHIVE_PARTS.json', dict(archive=whole_archive.name,
        archive_bytes=ready['archive_bytes'], archive_sha256=ready['archive_sha256'], parts=parts))
    for name in ('ORIGINAL_PROOF.json', 'INPUT_MANIFEST.json', 'PUBLISHED_PRIOR.json',
                 'TRANSPORT_PREPARATION.json', 'COMPLETE_TERMINAL_TABLE.md',
                 'B7_COMPLETED260_PHYSICAL_HAND_ATTACHMENT.md', 'PARTIAL_RELEASE_MANIFEST.json'):
        copy(packet / name, out / name)
    copy(archive / 'ARCHIVE_READY.json', out / 'ARCHIVE_READY.json')
    copy(packet / 'original_audits/EXACT_TREE_REPLAY.json', out / 'NATIVE_ORIGINAL_REPLAY.json')
    for name in ('PORTABLE_RECEIPT.json', 'COMPLETE_ORIGINAL_REPLAY.json'):
        copy(fresh / name, out / name)
    for name in ('B7_COMPLETED260_ATTACHMENT_REVIEW.md', 'B7_COMPLETED260_ATTACHMENT_REVIEW.json',
                 'B_REGISTERED_PORTABLE_TRANSPORT_REVIEW.json', 'review_b_portable_transport.py'):
        copy(reviews / name, out / name)
    for name in ('prepare_registered_b_portable_transport.py', 'publish_b7_component_checkpoint.py'):
        copy(Path(__file__).parent / name, out / name)
    copy(packet / 'acceptance_tools/archive_partial_b_checkpoint.py', out / 'archive_partial_b_checkpoint.py')

    helper_receipt = read(work / 'c_runtime/BOUNDARY_GUARD_HELPER_PORTABLE_ARCHIVE_RECEIPT.json')
    helper_archive = work / 'c_runtime/reusable_boundary_guard_helpers_v1.tar.xz'
    assert helper_receipt['status'] == 'PASS_BOUNDARY_HELPER_ARCHIVE_MEMBER_HASH_REPLAY'
    assert digest(helper_archive) == helper_receipt['archive_sha256']
    assert helper_archive.stat().st_size == helper_receipt['archive_bytes']
    assert helper_receipt['actual_original_terminal_uses'] == helper_receipt['new_original_cells'] == helper_receipt['new_masks'] == 0
    helper_out.mkdir()
    found = set()
    with tarfile.open(helper_archive, 'r:xz') as stream:
        for member in stream:
            if member.isdir():
                continue
            assert member.isfile() and member.name in helper_receipt['files']
            assert member.name not in found
            relative = Path(member.name).relative_to('reusable_boundary_guard_helpers_v1')
            assert not relative.is_absolute() and '..' not in relative.parts
            data = stream.extractfile(member).read()
            assert sha256(data).hexdigest() == helper_receipt['files'][member.name]
            target = helper_out / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            found.add(member.name)
    assert found == set(helper_receipt['files']) and len(found) == 17
    copy(helper_archive, helper_out / helper_archive.name)
    copy(work / 'c_runtime/BOUNDARY_GUARD_HELPER_PORTABLE_ARCHIVE_RECEIPT.json',
         helper_out / 'BOUNDARY_GUARD_HELPER_PORTABLE_ARCHIVE_RECEIPT.json')

    text = f'''# B7: portable checkpoint of completed domain 260

**The original remains OPEN. This checkpoint grants zero original-cell and
zero whole-mask credit.** The live fixed register at publication has
{register['closed_cells']}/231 CLOSED and {register['open_cells']} OPEN.

The unchanged original is `negative-7c60be8b07a358e9`. Native and fresh portable
exact replay both check its entire 813-node physical cover: 442 excluded
terminal cases and six OPEN cases. Inside it, saved domain 260 is fully
excluded by a 425-node cover with 213 excluded leaves. All nine physical
unit squares, original corners and pairs, marked conditions, strict CD,
original frames and shared closed faces are retained.

The completed component contains both closed sides of `y_I-y_H=0` and the
full positive-half continuation. Its physical attachment and independent
source/coverage review are included. The six outside obligations are
original-tree nodes 3, 4, 142, 154, 156 and 264. Later continuations are not
implicitly part of this frozen snapshot.

## Recovery and exact replay

Concatenate the parts in the order listed in `ARCHIVE_PARTS.json`. Check
every part hash and then the complete archive SHA256
`{ready['archive_sha256']}` before extraction. The archive has
{ready['archive_bytes']:,} bytes and {ready['archive_members_verified']:,}
verified regular members. Its top directory is `{packet.name}`.

Place it beside the published `b16a_I32_complete_H_checkpoint` prior named
in `PUBLISHED_PRIOR.json` (prior archive SHA256
`{info['prior_archive_sha256']}`). From their common directory run:

```sh
python3 -B -S {packet.name}/code/replay_registered_b_relative_support_packet.py \\
  --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is `PASS_PORTABLE_OPEN_PROTOTYPE`, with
`complete=false`, `whole_original_proved=false` and six OPEN leaves.
The portable checker forbids old-workspace proof reads, independently
reconstructs exact arithmetic and complete covers, and rehashes all inputs.
The transport adds only 751 verified aliases to already frozen bytes; the
original proof and checker files are unchanged.

## Reusable boundary sources

The sibling `a2_00100_original_boundary_guard_helpers_v1` folder preserves
the sharp and deep boundary guards with their frozen theorem sources.
Its fresh local-only source replay checks three sharp criteria and 144
deep identities. This source package itself has zero original-terminal
uses and zero credit. Concrete C27 central subdomains use the existing
sharp AHID terminal; no deep-cylinder use is inferred from preparing it.

The claim remains strict `q < 1105/256`. No closed-Q global theorem,
equality classification, original or whole-mask closure is asserted.
No Lean, Lake, compilation or CI was run.
'''
    (out / 'README.md').write_text(text)
    assert digest(ledger) == ledger_hash
    dump(out / 'ZERO_CREDIT_PUBLICATION_AUDIT.json', dict(
        status='PASS_REPLAYED_OPEN_COMPONENT_CHECKPOINT_PUBLICATION',
        original_id=cell['id'], current_register_sha256=ledger_hash,
        original_ledger_unchanged=True, fixed_original_count=231,
        closed_originals=register['closed_cells'], open_originals=register['open_cells'],
        new_original_cells=0, new_masks=0, complete_original=False,
        complete_component_nodes=425, complete_component_leaves=213,
        full_original_cover_nodes=813, open_leaves=6,
        archive_sha256=ready['archive_sha256'], archive_parts=len(parts),
        every_part_rehashed=True, helper_archive_sha256=helper_receipt['archive_sha256'],
        helper_members_rehashed=17, no_lean_lake_compilation_or_ci=True))
    print(json.dumps(dict(status='PUBLISHED_CHECKPOINT_FILES_ZERO_CREDIT',
                         directory=str(out), helper_directory=str(helper_out),
                         archive_parts=len(parts), ledger_unchanged=True), indent=2))


if __name__ == '__main__':
    main()
