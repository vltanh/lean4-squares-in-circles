"""Prepare a hash-bound, zero-credit B7 component4 publication.

This script never writes the immutable original register. Native arithmetic,
cold portable arithmetic, physical review and archive member audit are gates.
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


def read(path):
    return json.loads(Path(path).read_text())


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def main():
    ap = argparse.ArgumentParser()
    for name in ('repo', 'work', 'packet', 'fresh', 'archive'):
        ap.add_argument(name, type=Path)
    a = ap.parse_args()
    repo, work, packet, fresh, archive = [getattr(a, name).resolve()
        for name in ('repo', 'work', 'packet', 'fresh', 'archive')]
    nine = repo / 'research/nine'
    ledger = nine / 'gates/A2_00100_FIXED_FRONTIER.json'
    ledger_hash, register = digest(ledger), read(ledger)
    assert (register['closed_cells'], register['open_cells'], len(register['cells'])) == (224, 7, 231)
    cell = next(c for c in register['cells'] if c['id'] == 'negative-7c60be8b07a358e9')
    assert cell['status'] == 'OPEN'
    info = read(packet / 'ORIGINAL_PROOF.json')
    portable = read(fresh / 'PORTABLE_RECEIPT.json')
    native = read(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    report = read(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    ready = read(archive / 'ARCHIVE_READY.json')
    assert info['original_id'] == portable['original_id'] == ready['original_id'] == cell['id']
    assert info['original_path'] == cell['path']
    assert not info['complete'] and info['open_prototype']
    assert portable['status'] == 'PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER'
    assert not portable['complete'] and not portable['whole_original_proved']
    for key in ('every_new_bound_and_cover_replayed', 'all_inputs_rehashed_at_completion',
                'external_workspace_reads_forbidden'):
        assert portable[key] is True
    assert portable['numerical_modules_imported'] is False and portable['lean_lake_ci_run'] is False
    assert portable['new_original_ledger_credit'] == portable['new_mask_ledger_credit'] == 0
    assert portable['packet_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert portable['report_sha256'] == digest(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    packet_manifest = read(packet / 'INPUT_MANIFEST.json')
    assert len(packet_manifest['files']) == 1411
    for name, expected in packet_manifest['files'].items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert digest(packet / relative) == expected, ('changed frozen packet member', name)
    assert info['exact_tree_report_sha256'] == digest(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    assert packet_manifest['files']['ORIGINAL_PROOF.json'] == digest(packet / 'ORIGINAL_PROOF.json')
    assert packet_manifest['files']['original_audits/EXACT_TREE_REPLAY.json'] == info['exact_tree_report_sha256']
    for item in (native, report):
        assert item['status'] == 'PASS_PARTIAL_PHYSICAL_TREE'
        assert item['entire_registered_original_domain_retained']
        assert [item[k] for k in ('nodes', 'excluded_leaves', 'open_leaves')] == [949, 505, 41]
        assert item['central_F_box_occurrences'] == 6 and item['central_nine_rows_checked'] == 22
        assert not item['complete'] and not item['whole_original_proved']
    for key, value in info['counts'].items():
        assert native[key] == report[key] == value
    component = read(packet / 'B7_COMPLETE_COMPONENT4_FINAL_PHYSICAL_REVIEW.json')
    physical = read(packet / 'B7_COMPLETE_COMPONENT4_C_AGENT_PHYSICAL_REVIEW.json')
    source = read(packet / 'B7_CENTRAL_PORTABLE_SOURCE_TRANSPORT_REVIEW.json')
    transport_path = work / 'c_runtime/B7_CENTRAL_POSITION_CONCRETE_TRANSPORT_C_REVIEW.json'
    transport = read(transport_path)
    assert component['status'] == 'PASS_COMPLETE_B7_COMPONENT4_WITH_OPEN_ORIGINAL_RETAINED'
    assert component['component_nodes'] == 33 and component['component_excluded_terminals'] == 20
    assert physical['status'] == 'PASS_B7_COMPONENT4_C_AGENT_PHYSICAL_LITERAL_TABLE_REVIEW'
    assert physical['source_review_no_blocker'] and not physical['blocking_findings']
    assert physical['component_domains'] == 33 and physical['excluded_terminals'] == 20
    assert source['status'] == 'PASS_B7_CENTRAL_PORTABLE_SOURCE_TRANSPORT_REVIEW'
    assert not source['blocking_findings']
    assert transport['status'] == 'PASS_B7_CENTRAL_POSITION_CONCRETE_TRANSPORT_C_REVIEW'
    assert not transport['blocking_findings']
    assert transport['packet_input_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert transport['verified_added_aliases'] == 751 and transport['inputs_checked'] == 1411
    assert transport['prior_inputs'] == 507 and transport['attachments'] == 10
    assert transport['every_binding_resolves_inside_packet_or_published_prior']
    assert ready['all_member_hashes_match'] and ready['xz_integrity_pass']
    assert not ready['complete_original']
    assert ready['new_original_ledger_credit'] == ready['new_mask_ledger_credit'] == 0
    assert ready['portable_receipt_sha256'] == digest(fresh / 'PORTABLE_RECEIPT.json')
    release_path = packet / 'PARTIAL_RELEASE_MANIFEST.json'
    assert digest(release_path) == ready['release_manifest_sha256']
    release = read(release_path)
    assert release['original_id'] == cell['id'] and release['counts'] == info['counts']
    assert not release['complete_original']
    assert release['new_original_ledger_credit'] == release['new_mask_ledger_credit'] == 0
    for name, expected in release['files'].items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert digest(packet / relative) == expected, ('changed archived member', name)
    for name, expected in packet_manifest['files'].items():
        assert release['files'][name] == expected
    assert release['files']['INPUT_MANIFEST.json'] == portable['packet_manifest_sha256']
    assert release['files']['original_audits/FRESH_PORTABLE_RECEIPT.json'] == digest(fresh / 'PORTABLE_RECEIPT.json')
    assert release['files']['original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json'] == portable['report_sha256']
    whole_archive = archive / ready['archive']
    assert whole_archive.stat().st_size == ready['archive_bytes']
    assert digest(whole_archive) == ready['archive_sha256']
    by_index = {item['index']: item for item in native['node_audits']}
    remaining = {3: [], 142: [], 154: [], 156: [], 264: []}
    for item in native['leaf_table']:
        if item['excluded']:
            continue
        cursor = item['index']
        while cursor not in remaining:
            cursor = by_index[cursor]['parent']
            assert cursor is not None
        remaining[cursor].append(item['index'])
    assert {k: len(v) for k, v in remaining.items()} == {3: 8, 142: 6, 154: 18, 156: 4, 264: 5}
    out = nine / 'computer_assisted/a2_00100_b7_completed4_central_checkpoint_v1'
    assert not out.exists()
    out.mkdir()

    def copy(source_path, target):
        assert not target.exists()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source_path, target)
        assert digest(source_path) == digest(target)

    parts, combined = [], sha256()
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
    names = ('ORIGINAL_PROOF.json', 'INPUT_MANIFEST.json', 'PUBLISHED_PRIOR.json',
        'TRANSPORT_PREPARATION.json', 'COMPLETE_TERMINAL_TABLE.md', 'PARTIAL_RELEASE_MANIFEST.json',
        'B7_COMPLETE_COMPONENT4_PHYSICAL_HAND_ATTACHMENT.md',
        'B7_COMPLETE_COMPONENT4_FINAL_PHYSICAL_REVIEW.json',
        'B7_COMPLETE_COMPONENT4_C_AGENT_PHYSICAL_REVIEW.json',
        'B7_CENTRAL_PORTABLE_SOURCE_TRANSPORT_REVIEW.json',
        'B7_CENTRAL_PORTABLE_SOURCE_DERIVATION.json',
        'B7_COMPONENT4_FOUR_F_BOXES_ROOT_PHYSICAL_REVIEW.json',
        'B7_COMPONENT4_FOUR_F_BOXES_B16_SOURCE_PHYSICAL_REVIEW.json',
        'B7_COMPONENT4_TWELVE_OUTER_B16_WRAPPER_REVIEW.json',
        'B7_COMPONENT4_THREE_SURVIVORS_B16_WRAPPER_REVIEW.json')
    for name in names:
        copy(packet / name, out / name)
    copy(archive / 'ARCHIVE_READY.json', out / 'ARCHIVE_READY.json')
    copy(packet / 'original_audits/EXACT_TREE_REPLAY.json', out / 'NATIVE_ORIGINAL_REPLAY.json')
    for name in ('PORTABLE_RECEIPT.json', 'COMPLETE_ORIGINAL_REPLAY.json'):
        copy(fresh / name, out / name)
    copy(transport_path, out / transport_path.name)
    for name in ('build_b7_central_position_packet.py', 'replay_b7_central_position_packet.py',
                 'archive_partial_b7_central_checkpoint.py', 'publish_b7_central_component_checkpoint_v2.py'):
        copy(Path(__file__).parent / name, out / name)
    for name in ('review_b7_complete_component4.py', 'prepare_registered_b_portable_transport.py'):
        copy(packet / 'acceptance_tools' / name, out / name)
    dump(out / 'REMAINING_OPEN_FRONTIER.json', dict(original_id=cell['id'],
        exact_manifest_sha256=native['certificate_sha256'], original_still_open=True,
        remaining_by_prior_coarse_branch={str(k): v for k, v in remaining.items()},
        total_open_terminal_domains=41, original_cell_credit=0, mask_credit=0))
    text = f'''# B7: complete component 4 and retained complete component 260

**B7 remains OPEN. This checkpoint grants zero original-cell and zero whole-mask credit.**
The unchanged register has **224 CLOSED / 7 OPEN**; whole masks remain **8 CLOSED / 24 OPEN**.

Native and fresh portable exact replay check the entire retained original
`negative-7c60be8b07a358e9`: **949 domains, 505 excluded terminal domains and
41 OPEN terminal domains**. The new completed component 4 has 33 domains and
20 excluded terminals. Previously completed component 260 remains intact
with 425 domains and 213 excluded terminals.

## Physical argument

Component 4 uses all eight actual E/H separating-axis alternatives. Four
previously unresolved children each receive the three closed cuts
`x_F=1/5`, `y_F=-9/50`, `y_F=9/50`. The four inner boxes have
`|c_F|² <= 181/2500 = (27/100)² - 1/2000` and are excluded by the published
all-nine central-capacity theorem. The twelve outer complements and the
four previously excluded E/H children complete the cover. All shared faces
remain present. See the [physical hand proof and terminal table](B7_COMPLETE_COMPONENT4_PHYSICAL_HAND_ATTACHMENT.md).

The exact decoder retains all nine original frames, all 36 corners and
physical pairs, the five original cones, actual AB/BC/EF/FG, strictly weak
CD, and original H/I labels. Across the full tree it checks 342 bound rounds,
57,118 rational deductions, 220,172 printed row occurrences, 1,657 relative
support chord rows, 22 central rows and six original-F central-box terminals.
No numerical point or producer status supplies a proof premise.

## Remaining original obligations

The older checkpoint had six unresolved coarse branches. Component 4 is now
complete; the other five have the following finer terminal frontier:

| Prior coarse branch | OPEN terminal domains |
|---:|---:|
| 3 | 8 |
| 142 | 6 |
| 154 | 18 |
| 156 | 4 |
| 264 | 5 |

The exact leaf IDs are in `REMAINING_OPEN_FRONTIER.json`. The count of 41
refers to this refined cover, not to 41 original register cells. Later
alternative angle covers are outside this immutable checkpoint.

## Recovery and exact replay

Concatenate the archive parts in `ARCHIVE_PARTS.json` order, checking each
part and the full SHA-256 `{ready['archive_sha256']}` before extraction.
The archive has {ready['archive_bytes']:,} bytes and
{ready['archive_members_verified']:,} independently rehashed regular members.
Its top directory is `{packet.name}`.

Place the extracted directory beside the published prior
`b16a_I32_complete_H_checkpoint`, identified in `PUBLISHED_PRIOR.json` by
archive SHA-256 `{info['prior_archive_sha256']}`. From their common directory:

```sh
python3 -B -S {packet.name}/code/replay_b7_central_position_packet.py \\
  --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is `PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER`,
with `complete=false`, `whole_original_proved=false`, and 41 OPEN leaves.
The checker forbids proof reads outside that dedicated replay directory,
reconstructs rational rows and complete physical covers, and rehashes all
inputs after completion. There are {portable['packet_inputs']:,} frozen
packet inputs, {portable['prior_inputs']} prior inputs and 751 verified
historical aliases to already frozen bytes. The unchanged mathematical
decoder and position-cover reader are bound by the source reviews.

The claim remains strict `q < 1105/256`. Neither a closed-Q global theorem
nor an equality classification is asserted. No Lean, Lake, compilation or
CI was run. Continue the remaining seven whole originals under the current
bounded-work directive.
'''
    (out / 'README.md').write_text(text)
    assert digest(ledger) == ledger_hash
    dump(out / 'ZERO_CREDIT_PUBLICATION_AUDIT.json', dict(
        status='PASS_REPLAYED_B7_CENTRAL_COMPONENT_CHECKPOINT_PUBLICATION',
        original_id=cell['id'], current_register_sha256=ledger_hash,
        original_ledger_unchanged=True, fixed_original_count=231,
        closed_originals=224, open_originals=7, new_original_cells=0, new_masks=0,
        complete_original=False, completed_components={'4': [33, 20], '260': [425, 213]},
        full_original_cover_nodes=949, excluded_terminal_domains=505, open_terminal_domains=41,
        archive_sha256=ready['archive_sha256'], archive_parts=len(parts),
        every_part_rehashed=True, all_archive_members_rehashed=ready['archive_members_verified'],
        fresh_portable_receipt_sha256=digest(fresh / 'PORTABLE_RECEIPT.json'),
        physical_peer_sha256=digest(packet / 'B7_COMPLETE_COMPONENT4_C_AGENT_PHYSICAL_REVIEW.json'),
        concrete_transport_peer_sha256=digest(transport_path), no_lean_lake_compilation_or_ci=True))
    print(json.dumps(dict(status='PUBLISHED_CHECKPOINT_FILES_ZERO_CREDIT',
                         directory=str(out), archive_parts=len(parts), ledger_unchanged=True), indent=2))


if __name__ == '__main__':
    main()
