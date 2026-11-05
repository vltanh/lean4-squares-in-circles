"""Prepare the hash-bound, zero-credit B7 selected1011 component publication.

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
    assert len(packet_manifest['files']) == 1523
    assert digest(packet / 'INPUT_MANIFEST.json') == '02a31bff354a13b6ee84e3cd8ef36c7972d85abe3bd610aee82c94611f00d1e7'
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
        assert [item[k] for k in ('nodes', 'excluded_leaves', 'open_leaves')] == [1011, 543, 43]
        assert item['central_F_box_occurrences'] == 13 and item['central_nine_rows_checked'] == 131
        assert not item['complete'] and not item['whole_original_proved']
    for key, value in info['counts'].items():
        assert native[key] == report[key] == value
    component = read(packet / 'B7_SELECTED1011_COMPLETE_COMPONENTS_FINAL_PHYSICAL_REVIEW.json')
    physical_path = packet / 'B7_SELECTED1011_COMPLETE_COMPONENTS_C_AGENT_PHYSICAL_TABLE_REVIEW.json'
    physical = read(physical_path)
    source = read(packet / 'B7_CENTRAL_PORTABLE_SOURCE_TRANSPORT_REVIEW.json')
    transport_path = work / 'c_runtime/B7_SELECTED1011_CONCRETE_PORTABLE_TRANSPORT_C_REVIEW.json'
    transport = read(transport_path)
    assert digest(packet / 'original_audits/EXACT_TREE_REPLAY.json') == '0f7007a02876f18701a532cf1bf82c038557c5eabfb5566a35080b7c48b862ba'
    assert digest(packet / 'B7_SELECTED1011_COMPLETE_COMPONENTS_FINAL_PHYSICAL_REVIEW.json') == 'd9c151d858827e66964de21cc782eff81fad793eb3047bfd8072325a03ecff8a'
    assert digest(physical_path) == '8f23ec1fbb784fd01fc720fb2fa0267dd5eae823be17c8a87101e59cd2dda98a'
    assert digest(packet / 'B7_SELECTED1011_COMPLETE_COMPONENTS_LITERAL_TERMINAL_TABLE.json') == '500eff3ba2fe5ce420f0c57ae4295986ca28d3168e1f13e85f987ff71787ee8f'
    assert digest(packet / 'B7_SELECTED1011_COMPLETE_COMPONENTS_PHYSICAL_HAND.md') == '1a07937cb73a6c7392ba9b7655343d8d29284c378a2e62762b9f8480cd454a6a'
    assert component['status'] == 'PASS_B7_SELECTED1011_TWO_COMPLETE_COMPONENTS_WITH_OPEN_ORIGINAL'
    assert component['counts'] == [1011, 543, 43] and component['literal_terminal_count'] == 18
    assert physical['status'] == 'PASS_B7_SELECTED1011_C_AGENT_PHYSICAL_COMPLETE_COMPONENT_TABLE_REVIEW'
    assert physical['blocking_findings'] == []
    assert physical['whole814_domains'] == 13 and physical['whole814_terminals'] == 10
    assert physical['negative_F993_domains'] == 9 and physical['negative_F993_terminals'] == 8
    assert physical['all_five_closed_unions_reconstructed'] and physical['all18_raw_terminal_attributions_checked']
    expected_components = {'4': [33, 20], '260': [425, 213], '814': [13, 10],
                           '816': [7, 4], '818': [9, 8], '820': [7, 4], '993': [9, 8]}
    for index, counts in expected_components.items():
        for reviewed in (component['completed_components'], physical['complete_components']):
            assert [reviewed[index]['domains'], reviewed[index]['excluded_terminals']] == counts
    assert source['status'] == 'PASS_B7_CENTRAL_PORTABLE_SOURCE_TRANSPORT_REVIEW'
    assert not source['blocking_findings']
    assert transport['status'] == 'PASS_B7_SELECTED1011_CONCRETE_PORTABLE_TRANSPORT_C_REVIEW'
    assert not transport['blocking_findings']
    assert transport['packet_input_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert transport['verified_added_aliases'] == 752 and transport['inputs_checked'] == 1523
    assert transport['prior_inputs'] == 507 and transport['attachments'] == 12
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
    assert {k: len(v) for k, v in remaining.items()} == {3: 10, 142: 6, 154: 18, 156: 4, 264: 5}
    out = nine / 'computer_assisted/a2_00100_b7_completed_components1011_checkpoint_v1'
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
        'TRANSPORT_PREPARATION.json', 'COMPLETE_TERMINAL_TABLE.md', 'PARTIAL_RELEASE_MANIFEST.json')
    for name in names:
        copy(packet / name, out / name)
    attachments = read(packet / 'TRANSPORT_PREPARATION.json')['attachments']
    assert len(attachments) == 12
    for name, entry in attachments.items():
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert digest(packet / relative) == entry['sha256']
        copy(packet / relative, out / relative)
    copy(archive / 'ARCHIVE_READY.json', out / 'ARCHIVE_READY.json')
    copy(packet / 'original_audits/EXACT_TREE_REPLAY.json', out / 'NATIVE_ORIGINAL_REPLAY.json')
    for name in ('PORTABLE_RECEIPT.json', 'COMPLETE_ORIGINAL_REPLAY.json'):
        copy(fresh / name, out / name)
    copy(transport_path, out / transport_path.name)
    for name in ('build_b7_central_position_packet.py', 'replay_b7_central_position_packet.py',
                 'archive_partial_b7_central_checkpoint.py', 'publish_b7_selected1011_component_checkpoint.py'):
        copy(Path(__file__).parent / name, out / name)
    for name in ('prepare_registered_b_portable_transport.py',):
        copy(packet / 'acceptance_tools' / name, out / name)
    dump(out / 'REMAINING_OPEN_FRONTIER.json', dict(original_id=cell['id'],
        exact_manifest_sha256=native['certificate_sha256'], original_still_open=True,
        remaining_by_prior_coarse_branch={str(k): v for k, v in remaining.items()},
        total_open_terminal_domains=43, original_cell_credit=0, mask_credit=0))
    text = f'''# B7: seven complete components in the retained 1,011-domain cover

**B7 remains OPEN. This checkpoint grants zero original-cell and zero whole-mask credit.**
The unchanged register has **224 CLOSED / 7 OPEN**; whole masks remain **8 CLOSED / 24 OPEN**.

Native and fresh isolated portable exact replay check the entire retained original
`negative-7c60be8b07a358e9`: **1,011 domains, 543 excluded terminal domains and
43 OPEN terminal domains**. The two newest complete components are the G-axis
positive G/I branch814 and the negative-F half993 under949.

## Complete components

| Component | Domains | Excluded terminal domains |
|---:|---:|---:|
| 4 | 33 | 20 |
| 260 | 425 | 213 |
| 814 | 13 | 10 |
| 816 | 7 | 4 |
| 818 | 9 | 8 |
| 820 | 7 | 4 |
| 993 | 9 | 8 |

These internal components are not additional original register cells. Every
listed component has zero OPEN terminal domains. All four positive-sign G/I
alternatives under component3 are now complete; its four negative-sign
alternatives still retain unresolved regions.

## Physical argument for the newest components

Component814 retains both closed F-position cuts `y_F=-3/64` and `y_F=3/64`.
Its lower complement is excluded by its literal exact terminal. Its central
box has `|c_F|² <=149/2048`, below `(27/100)²` by exactly`187/1280000`, so the
accepted all-nine central-capacity theorem excludes the whole closed box.
The upper complement956 has all eight actual C/I separating-axis alternatives,
and every child1003–1010 is excluded. This completes814 with13 domains/10terminals.

Under the negative G/I branch,949 is covered by the two closed halves at
`x_F=0`. Its negative half993 has all eight actual F/I separating-axis
alternatives, and every child994–1001 is excluded. The positive half1002 and
old complementary domain952 remain OPEN. Whole813 remains OPEN.

The [physical hand attachment](B7_SELECTED1011_COMPLETE_COMPONENTS_PHYSICAL_HAND.md)
and [literal terminal table](B7_SELECTED1011_COMPLETE_COMPONENTS_LITERAL_TERMINAL_TABLE.json)
retain the original labels, both closed faces of every cut, all row coefficients,
rational weights, residual bounds, exact reserves and terminal recipes. The
independent physical peer reconstructed all22 child states in five complete
unions,238 printed terminal rows and13 exact positive reserves, together with
the frame/interval and central-box terminals.

All993 previous bound records and initial states remain identical.989 old
payloads are byte-identical; the other four change only graph metadata or
propagated candidate status. All previously completed components are retained.
The full exact replay checks416 bound rounds,67,065 deductions,246,778 printed
rows,2,118 relative-support chord rows,131 all-nine central rows and13 original-F
central-box terminals. Numerical points and producer flags are not premises.

The decoder retains all nine distinct original unit squares,36 original corners,
36 physical pairs,five cones,actual AB/BC/EF/FG,strictly weak CD,and originalH/I.
The radius scope is strict`q < Q =1105/256`. No global closed-Q theorem or
equality classification is asserted.

## Remaining obligations

| Prior coarse branch | OPEN terminal domains |
|---:|---:|
| 3 | 10 |
| 142 | 6 |
| 154 | 18 |
| 156 | 4 |
| 264 | 5 |

`REMAINING_OPEN_FRONTIER.json` lists the exact43 unresolved terminal IDs.
Later numerical alternatives are outside this immutable checkpoint. The seven
original cells remain the accounting target.

## Recovery and isolated exact replay

Concatenate the parts in `ARCHIVE_PARTS.json` order, checking each part and the
full SHA-256`{ready['archive_sha256']}` before extraction. The archive has
{ready['archive_bytes']:,} bytes and{ready['archive_members_verified']:,}
independently rehashed regular members. Its top directory is`{packet.name}`.

Place it beside the published prior`b16a_I32_complete_H_checkpoint`, identified
by `PUBLISHED_PRIOR.json` and archive SHA-256`{info['prior_archive_sha256']}`.
Use a dedicated directory containing only these copied input packages and the
new output directory. From their common parent:

```sh
python3 -B -S {packet.name}/code/replay_b7_central_position_packet.py \
  --prior b16a_I32_complete_H_checkpoint --output fresh_b7_open_replay
```

The expected receipt is`PASS_PORTABLE_B7_CENTRAL_POSITION_OPEN_COVER`, with
`complete=false`,`whole_original_proved=false`,and43 OPEN leaves. The checker
forbids proof reads outside that dedicated directory and rehashes all copied
inputs at completion. It checks{portable['packet_inputs']:,} packet inputs,
{portable['prior_inputs']} prior inputs and752 verified historical aliases to
already frozen bytes. The12 attachments and unchanged decoder/transport sources
are independently reviewed. No old disk PASS initializes the fresh replay.

No Lean,Lake,compilation or CI was run. Continue the seven original obligations
under the fixed bounded-work directive; this checkpoint changes no ledger entry.
'''
    (out / 'README.md').write_text(text)
    assert digest(ledger) == ledger_hash
    dump(out / 'ZERO_CREDIT_PUBLICATION_AUDIT.json', dict(
        status='PASS_REPLAYED_B7_CENTRAL_COMPONENT_CHECKPOINT_PUBLICATION',
        original_id=cell['id'], current_register_sha256=ledger_hash,
        original_ledger_unchanged=True, fixed_original_count=231,
        closed_originals=224, open_originals=7, new_original_cells=0, new_masks=0,
        complete_original=False, completed_components=expected_components,
        full_original_cover_nodes=1011, excluded_terminal_domains=543, open_terminal_domains=43,
        archive_sha256=ready['archive_sha256'], archive_parts=len(parts),
        every_part_rehashed=True, all_archive_members_rehashed=ready['archive_members_verified'],
        fresh_portable_receipt_sha256=digest(fresh / 'PORTABLE_RECEIPT.json'),
        physical_peer_sha256=digest(physical_path),
        concrete_transport_peer_sha256=digest(transport_path), no_lean_lake_compilation_or_ci=True))
    print(json.dumps(dict(status='PUBLISHED_CHECKPOINT_FILES_ZERO_CREDIT',
                         directory=str(out), archive_parts=len(parts), ledger_unchanged=True), indent=2))


if __name__ == '__main__':
    main()
