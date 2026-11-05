"""Publish exactly one fully accepted Bf14 original; no arithmetic or Git calls."""
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import argparse
import json
import shutil

ID = 'negative-f14f5bc4eafdf50d'
NAME = 'a2_00100_bf14_complete_original'


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


def one(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new, 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repo', type=Path)
    ap.add_argument('packet', type=Path)
    ap.add_argument('portable_replay', type=Path)
    ap.add_argument('archive', type=Path)
    ap.add_argument('review_directory', type=Path)
    a = ap.parse_args()
    nine = a.repo.resolve() / 'research/nine'
    packet, fresh, archive = a.packet.resolve(), a.portable_replay.resolve(), a.archive.resolve()
    reviews = a.review_directory.resolve()
    here = Path(__file__).resolve().parent
    out = nine / 'computer_assisted' / NAME
    assert not out.exists()
    info = read(packet / 'ORIGINAL_PROOF.json')
    native = read(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    replay = read(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    receipt = read(fresh / 'PORTABLE_RECEIPT.json')
    ready = read(archive / 'ARCHIVE_READY.json')
    table = read(here / 'BF14_COMPLETE_LITERAL_TABLE_AUDIT.json')
    byte_audit = read(here / 'BF14_COMPLETE_ARCHIVE_AUDIT.json')
    alias_audit = read(here / 'BF14_PORTABLE_ALIAS_AUDIT.json')
    physical = read(reviews / 'BF14_FINAL_PHYSICAL_SOURCE_REVIEW.json')
    structure = read(reviews / 'BF14_FINAL_STRUCTURAL_REVIEW.json')
    assert info['original_id'] == receipt['original_id'] == ready['original_id'] == ID
    assert info['complete'] and not info['open_prototype']
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'
    assert receipt['complete'] and receipt['whole_original_proved']
    assert receipt['every_new_bound_and_cover_replayed'] and receipt['all_inputs_rehashed_at_completion']
    assert receipt['external_workspace_reads_forbidden'] and not receipt['numerical_modules_imported']
    assert receipt['report_sha256'] == digest(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    assert receipt['packet_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert table['status'] == 'PASS_BF14_COMPLETE_LITERAL_TABLE_AND_ROW_ACCOUNTING'
    assert byte_audit['status'] == 'PASS_ROOT_BF14_COMPLETE_ARCHIVE_AND_PART_AUDIT'
    assert byte_audit['archive_sha256'] == ready['archive_sha256']
    assert byte_audit['fresh_complete_report_sha256'] == receipt['report_sha256']
    assert alias_audit['status'] == 'PASS_LITERAL_PORTABLE_ALIAS_EXTENSION_ONLY'
    assert alias_audit['all_literal_proof_and_checker_bytes_unchanged']
    assert alias_audit['added_aliases'] == 754
    assert physical['status'] == 'PASS_FINAL_PHYSICAL_SOURCE_ATTACHMENT_AND_COMPLETE_COVER_REVIEW'
    assert physical['all_231_original_definitions_compared_equal']
    assert structure['final_manifest_sha256'] == native['certificate_sha256']
    assert structure['all_child_domains_independently_reconstructed']
    for report in (native, replay):
        assert report['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
        assert report['initial_original_id'] == ID
        assert report['complete'] and report['whole_original_proved']
        assert report['entire_registered_original_domain_retained'] is True
        assert report['nodes'] == 679 and report['terminal_leaves'] == report['excluded_leaves'] == 461
        assert report['open_leaves'] == 0
        assert report['complete_unions'] == {'proxy': 64, 'angle': 135, 'sat': 19}
    for key in info['counts']:
        assert native[key] == replay[key] == info['counts'][key], key
    assert table['totals']['rounds'] == replay['local_rounds']
    assert table['totals']['deductions'] == replay['local_deductions']
    assert table['totals']['premise_rows'] + table['totals']['terminal_rows'] == replay['local_printed_rows']
    assert table['all_printed_terminal_reserve_lower_bounds_valid']
    assert table['terminal_kinds'] == structure['terminal_kinds'] == {
        'accepted_center_interval_terminal': 111, 'positive_exact_reserve': 312,
        'proved_empty_analytic_frame': 10, 'accepted_effective_angle_terminal': 20,
        'proved_frame_contradiction': 8}

    ledger = nine / 'gates/A2_00100_FIXED_FRONTIER.json'
    before = read(ledger)
    before_hash = digest(ledger)
    assert (before['closed_cells'], before['open_cells'], len(before['cells'])) == (222, 9, 231)
    assert before_hash == info['current_definition_attachment']['current_register']['sha256']
    cell = next(c for c in before['cells'] if c['id'] == ID)
    assert cell['status'] == 'OPEN' and cell['path'] == info['original_path'] == replay['initial_path']
    assert info['current_definition_attachment']['all_231_original_definitions_unchanged']
    out.mkdir()

    def copy(source, name=None):
        source = Path(source)
        target = out / (name or source.name)
        assert not target.exists()
        shutil.copyfile(source, target)
        assert digest(source) == digest(target)

    for part in ready['parts']:
        source = archive / part['file']
        assert source.stat().st_size == part['bytes'] and digest(source) == part['sha256']
        copy(source)
    copy(archive / 'ARCHIVE_READY.json')
    for name in ('RELEASE_MANIFEST.json', 'INPUT_MANIFEST.json', 'PUBLISHED_PRIOR.json',
                 'ORIGINAL_PROOF.json', 'PACKAGING_ATTACHMENTS.json', 'TRANSPORT_ALIAS_REPAIR.json',
                 'COMPLETE_TERMINAL_TABLE.md', 'BF14_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md'):
        copy(packet / name)
    copy(packet / 'records/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md')
    for name in ('RELATIVE_SUPPORT_CHORD_HAND_PROOF.md', 'OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md'):
        copy(packet / 'code/relative_support_chords' / name)
    copy(packet / 'original_audits/EXACT_TREE_REPLAY.json', 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json')
    copy(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    copy(fresh / 'PORTABLE_RECEIPT.json')
    for name in ('BF14_FINAL_PHYSICAL_SOURCE_REVIEW.json', 'BF14_FINAL_PHYSICAL_SOURCE_REVIEW.md',
                 'BF14_FINAL_STRUCTURAL_REVIEW.json', 'BF14_FINAL_COMPLETE_TERMINAL_TABLE.json',
                 'BF14_FINAL_COMPLETE_COVER_TABLE.json', 'review_final_structure.py'):
        copy(reviews / name)
    for name in ('BF14_COMPLETE_LITERAL_TABLE_AUDIT.json', 'BF14_COMPLETE_ARCHIVE_AUDIT.json',
                 'BF14_PORTABLE_ALIAS_AUDIT.json', 'audit_bf14_portable_aliases.py',
                 'audit_bf14_literal_table.py', 'audit_bf14_complete_archive.py',
                 'freeze_bf14_acceptance_inputs.py', 'repair_bf14_portable_aliases.py',
                 'publish_bf14_complete_original.py'):
        copy(here / name)
    copy(packet / 'acceptance_tools/archive_registered_b_packet_streaming.py')

    counts = table['totals']
    summary = f'''The complete physical tree excludes `{ID}` in the strict-radius caller
`q < Q = 1105/256`. Its 679 nodes have **461 excluded terminal domains and
zero OPEN leaves**, with 64 four-way inset covers, 19 eight-way physical
separating-axis covers and 135 two-way closed slope covers.

Native and fresh portable exact replay both pass. The independent
physical/source and full-cover reviews, complete literal terminal-table
audit and archive/part audit also pass. The arithmetic contains
{counts['rounds']:,} bound rounds, {counts['deductions']:,} rational deductions,
{counts['premise_rows']:,} premise-row occurrences and {counts['terminal_rows']:,}
terminal-row occurrences. These are internal proof counts, not additional
originals or masks.

This accepts exactly one unchanged original, advancing **222 CLOSED / 9 OPEN
to 223 CLOSED / 8 OPEN** in the same 231-cell register. Remaining original
families are **A1, B4, C3, D0**. Whole masks remain **8 CLOSED / 24 OPEN**;
`001/00` and reversal `100/00` remain OPEN. No Lean, Lake, compilation or CI.
'''
    root_review = f'''# Final acceptance of the complete Bf14 original

{summary}
## Physical and coverage review

The exact negative baseline-59 path is retained in `ORIGINAL_PROOF.json`.
Its independently reconstructed original parent is
`{replay['parent_certificate_sha256']}`. The final tree manifest is
`{replay['certificate_sha256']}`.

`BF14_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md` derives all three literal
F/H escape inequalities, including the closed predecessor complement.
All nine physical unit squares, 36 original corners, 36 physical pairs,
five cones, actual AB/BC/EF/FG and strict weak CD remain in the caller.
The relative-support derivation and every sign, endpoint and product guard
are checked against the independent decoder and source-bound hand proofs.

The independent structural review reconstructs every child domain and
round-state link. At the final graft, 534 base sibling files are byte-identical,
two ancestors change only candidate status, and every one of the 142 added
conditional descendants matches the exact index remap. The original root
and its initial state are unchanged. All complete alternative sets and
shared closed faces remain present.

The terminal table has 312 positive-reserve terminals, 111 center-interval
terminals, 20 effective-angle terminals, 10 empty analytic-frame terminals
and eight frame contradictions. Every displayed positive reserve lower
bound is checked against its exact literal record. The native and portable
replays reconstruct all weighted rows and pay every coefficient residual.
Neither an assembler status nor numerical infeasibility is an accepted proof.

## Portable identity and archive

The fresh portable replay verifies {receipt['packet_inputs']:,} packet inputs
and {receipt['prior_inputs']:,} pinned prior inputs, forbids old-workspace reads,
uses standard-library exact arithmetic and imports no numerical optimizer.
Every input is rehashed at completion. Its original-domain flag is explicit:
`entire_registered_original_domain_retained=true`.

The first portable attempt stopped before tree arithmetic because the
restored workspace's historical B-family path lacked an explicit alias.
The version-2 packet adds 754 hash-checked aliases to already frozen inputs.
Every proof and checker byte is unchanged. The original package and failure
log are retained, and the accepted version-2 replay starts from the beginning.

The {ready['archive_bytes']:,}-byte archive has SHA256
`{ready['archive_sha256']}`. The independent audit checks every one of
{len(ready['parts'])} ordered parts, their concatenated digest and all
{ready['all_archive_members_verified']:,} regular members. It also compares
native and portable mathematical reports and rehashes the source packet.
These byte/table audits are separate from the two complete arithmetic replays.

The pinned prior is the published `b16a_I32_complete_H_checkpoint`, archive
SHA256 `{ready['prior_archive_sha256']}`. Its shared code and immutable
original definitions are reused; its B16 domain is not borrowed as a Bf14 proof.
The source-bound register snapshot deliberately precedes acceptance and
therefore records Bf14 as OPEN. The live ledger carries the subsequent closure.

## Scope

The conclusion is this one original's strict-radius exclusion. No closed-Q
global theorem, equality classification, whole mask, positional root or
roadmap gate is inferred. No human or proof-kernel verification is claimed.
Only the named original changes status after these acceptance checks.
'''
    (out / 'ROOT_FINAL_ACCEPTANCE.md').write_text(root_review)
    (out / 'README.md').write_text('# Complete Bf14 original\n\n' + summary +
        '\n[Final acceptance](ROOT_FINAL_ACCEPTANCE.md) · '
        '[Physical attachment](BF14_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md) · '
        '[Complete terminal table](COMPLETE_TERMINAL_TABLE.md) · '
        '[Archive parts](ARCHIVE_READY.json).\n\n'
        'The complete literal tree, independent checker sources, hand proofs, '
        'frozen bindings and fresh reports are in the ordered archive parts. '
        'Reproduction is documented in the '
        '[whole-original assembly](../../A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md).\n')
    closure = f'''# Complete Bf14 original: 223 CLOSED / 8 OPEN

{summary}
## Exact caller and finite argument

The frozen original is negative baseline frontier index 59, with path

```json
{json.dumps(cell['path'], separators=(',', ':'))}
```

It retains `t_D,t_A in [-1,0]`, `y_F <= 1/2`, and the literal inequalities
`x_H-x_F <= 0`, `-y_A+2y_H-y_F <= -3/5`, `y_A-y_F <= 3/5`.
The [physical attachment](computer_assisted/{NAME}/BF14_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md)
gives the original-nine caller, relative-support argument, complete cover
rules, strict-radius scope and exact whole-original attachment.

Every leaf is excluded by a positive rational weighted-row reserve or a
separately checked interval/frame contradiction. Every internal node retains
all members of its finite physical cover, including all closed faces.
Induction over the complete tree excludes its root. The independent
whole-domain checker reconstructs that root as the entire frozen original.

| Proof item | Count |
| --- | ---: |
| Node records | 679 |
| Four-way inset covers | 64 |
| Eight-way physical separators | 19 |
| Two-way closed slope covers | 135 |
| Excluded terminal domains | 461 |
| OPEN terminal domains | 0 |
| Exact bound rounds | {counts['rounds']:,} |
| Rational deductions | {counts['deductions']:,} |
| Premise-row occurrences | {counts['premise_rows']:,} |
| Terminal-row occurrences | {counts['terminal_rows']:,} |

The [complete terminal table](computer_assisted/{NAME}/COMPLETE_TERMINAL_TABLE.md)
lists all 461 leaves. The [final acceptance review](computer_assisted/{NAME}/ROOT_FINAL_ACCEPTANCE.md)
explains physical transport, exact replay, literal table accounting and the
archive audit. The [publication manifest](computer_assisted/{NAME}_manifest.json)
binds all published files and the exact one-original ledger delta.

## Reproduction

Concatenate the new archive parts in `ARCHIVE_READY.json` order, checking
each part and the combined SHA256 `{ready['archive_sha256']}`.
Restore the pinned prior in `PUBLISHED_PRIOR.json` and extract both inside
one dedicated directory. From that directory run:

```sh
python3 -B -S {packet.name}/code/replay_registered_b_relative_support_packet.py \\
  --prior b16a_I32_complete_H_checkpoint --output fresh_bf14_replay
```

The required receipt is `PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`,
with `complete=true`, `whole_original_proved=true` and no OPEN leaf.
The archived pre-acceptance register intentionally records this original
as OPEN; all 231 definition tuples agree with the live register.

Only Bf14 changes status. The other 230 original entries and all fixed
denominators (231 originals, 32 masks, 7,915 positional roots, 15 roadmap
gates) are unchanged. The remaining eight originals still require complete
proofs. The accepted radius scope remains `q < 1105/256`.
'''
    closure_path = nine / 'A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md'
    closure_path.write_text(closure)

    after = deepcopy(before)
    after.update(assembly='../' + closure_path.name, cell_review='../' + closure_path.name,
                 manifest='../computer_assisted/' + NAME + '_manifest.json',
                 closed_cells=223, open_cells=8, latest_new_closed_cells=1,
                 cumulative_new_closed_since_53=170,
                 preceding_assembly=before['assembly'], preceding_manifest=before['manifest'])
    selected = next(c for c in after['cells'] if c['id'] == ID)
    selected.update(status='CLOSED', method='complete_registered_original_physical_tree_with_relative_support_chords', terminal_leaves=461)
    selected['evidence'] = dict(method=selected['method'], record_id=ID,
        whole_cell_exclusion=True, complete_closed_face_cover=True,
        all_original_physical_conditions_retained=True,
        original_initial_state_sha256=replay['parent_certificate_sha256'],
        tree_manifest_sha256=replay['certificate_sha256'],
        archive_parts_manifest=NAME + '/ARCHIVE_READY.json',
        archive_sha256=ready['archive_sha256'], archive_bytes=ready['archive_bytes'],
        prior_archive_sha256=ready['prior_archive_sha256'],
        certificate=NAME + '/COMPLETE_ORIGINAL_REPLAY.json',
        certificate_sha256=digest(out / 'COMPLETE_ORIGINAL_REPLAY.json'),
        native_report_sha256=digest(out / 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json'),
        independent_checker='replay_registered_b_relative_support_packet.py',
        independent_checker_sha256=digest(packet / 'code/replay_registered_b_relative_support_packet.py'),
        independent_report=NAME + '/PORTABLE_RECEIPT.json',
        independent_report_sha256=digest(out / 'PORTABLE_RECEIPT.json'),
        root_hand_table_review=NAME + '/ROOT_FINAL_ACCEPTANCE.md',
        root_hand_table_review_sha256=digest(out / 'ROOT_FINAL_ACCEPTANCE.md'),
        terminal_table_sha256=digest(out / 'COMPLETE_TERMINAL_TABLE.md'),
        nodes=679, terminal_leaves=461, open_leaves=0,
        all_new_bound_and_cover_arithmetic_repeated=True,
        radius_scope='q < 1105/256', whole_mask_closed=False)
    fields = ('id', 'sign', 'baseline_frontier_index', 'path')
    assert [[c[k] for k in fields] for c in before['cells']] == [[c[k] for k in fields] for c in after['cells']]
    changed = [x['id'] for x, y in zip(before['cells'], after['cells']) if x != y]
    assert changed == [ID]
    assert sum(c['status'] == 'CLOSED' for c in after['cells']) == 223
    assert sum(c['status'] == 'OPEN' for c in after['cells']) == 8
    assert before['global_mask_ledger'] == after['global_mask_ledger']
    dump(ledger, after)
    dump(out / 'FIXED_LEDGER_DELTA_AUDIT.json', dict(
        status='PASS_EXACT_ONE_REGISTERED_ORIGINAL_LEDGER_DELTA',
        before_sha256=before_hash, after_sha256=digest(ledger), changed_original_ids=changed,
        all_231_original_definitions_unchanged=True, other_230_entries_unchanged=True,
        before=dict(closed=222, open=9, total=231), after=dict(closed=223, open=8, total=231),
        mask_ledger=dict(closed=8, open=24, total=32), new_original_cells=1, new_masks=0,
        new_positional_roots=0, new_roadmap_gates=0,
        fixed_denominators=dict(original_cells=231, masks=32, positional_roots=7915, roadmap_gates=15),
        remaining_open_original_ids=[c['id'] for c in after['cells'] if c['status'] == 'OPEN'],
        lean_lake_ci_run=False))

    heading = '> **ACTIVE EXECUTION DIRECTIVE — 2026-11-05:** [Current mask, priorities, bounded whole-cell attempts and exact acceptance](CURRENT_MASK_DIRECTIVE.md). **223/231 original cells CLOSED, 8 OPEN (A1, B4, C3); 8/32 masks CLOSED.** Bf14 is accepted; continue B16, A and the remaining B/C originals. The next milestone is **224/231**. Historical paragraphs below retain their original scope. No Lean/Lake/CI.'
    section = '## Complete Bf14 original: 223 CLOSED / 8 OPEN\n\n' + summary + '\n[Complete proof and reproduction](A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md).\n\n'
    for name in ('PROGRESS.md', 'HANDOFF_A2_FIXED_CLOSURE.md'):
        path = nine / name
        text = path.read_text()
        first, rest = text.split('\n', 1)
        assert first.startswith('> **ACTIVE EXECUTION DIRECTIVE')
        text = heading + '\n' + rest
        if name == 'PROGRESS.md':
            text = one(text, '**222/231 cells CLOSED, 9 OPEN; 8/32 masks CLOSED, 24 OPEN.**', '**223/231 cells CLOSED, 8 OPEN; 8/32 masks CLOSED, 24 OPEN.**')
            marker = '## Completed bounded A and B16 attempts'
            text = one(text, marker, section + '## Earlier continuation records\n\n' + marker)
            text = one(text, '# n=9: 222/231 current-mask cells closed; 9 remain OPEN', '# n=9: 223/231 current-mask cells closed; 8 remain OPEN')
            text = one(text, '**Latest accepted closure: the complete D821 original-cell exclusion.**\nThe same register now has **222 CLOSED / 9 OPEN**, with\n**169 additions beyond the first 53**. Remaining families: **A1, B5, C3, D0**.',
                '**Latest accepted closure: the complete Bf14 original-cell exclusion.**\nThe same register now has **223 CLOSED / 8 OPEN**, with\n**170 additions beyond the first 53**. Remaining families: **A1, B4, C3, D0**.')
            text = one(text, '[Latest complete assembly](A2_00100_D821_COMPLETE_ORIGINAL_CLOSURE.md)', '[Latest complete assembly](A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md)')
            text = one(text, '[Source-bound packet and fresh portable replay](computer_assisted/a2_00100_d821_complete_original_manifest.json)', '[Source-bound packet and fresh portable replay](computer_assisted/a2_00100_bf14_complete_original_manifest.json)')
            text = text.replace('register is 222/9, with A1/B5/C3/D0 remaining.', 'register is 223/8, with A1/B4/C3/D0 remaining.')
        else:
            old = '# Current A.2 handoff: 222/231 current-mask cells closed; 9 OPEN'
            text = one(text, old, '# Current A.2 handoff: 223/231 current-mask cells closed; 8 OPEN\n\n' + section + '## Earlier continuation records')
            text = text.replace('- Current mask: **222 CLOSED / 9 OPEN**, same 231 IDs and certified full cover.', '- Current mask: **223 CLOSED / 8 OPEN**, same 231 IDs and certified full cover.')
            text = text.replace('The register is **222 CLOSED / 9 OPEN**; the mask ledger is **8 CLOSED /', 'The register is **223 CLOSED / 8 OPEN**; the mask ledger is **8 CLOSED /')
        path.write_text(text)

    directive = nine / 'CURRENT_MASK_DIRECTIVE.md'
    text = directive.read_text()
    text = one(text, '**222 of 231 original cells CLOSED, 9 OPEN (A1, B5, C3; D0)**', '**223 of 231 original cells CLOSED, 8 OPEN (A1, B4, C3; D0)**')
    text = one(text, '**223/231 fully closed originals**', '**224/231 fully closed originals**')
    begin = text.index('2. **First: Bf14.**')
    end = text.index('3. **Next: B16a.**', begin)
    text = text[:begin] + '2. **Bf14 completed.** The [complete original proof](A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md) has passed native and portable exact replay, full physical/hand/table review and archive verification. Its 679-node cover excludes all 461 leaves. The immutable original `negative-f14f5bc4eafdf50d` is CLOSED; do not resume its former OPEN checkpoint.\n' + text[end:]
    text = one(text, '## Exact resume inputs and latest execution limitation', '## Fresh complete-original acceptance — 5 November 2026 UTC\n\n' + summary + '\nThe present environment restored and hash-checked the published archives, then verified the later 537-node source before continuing. Git transport and exact execution are available. The older transfer failure below is historical.\n\n## Historical resume inputs and earlier execution limitation')
    directive.write_text(text)

    publication = dict(schema='complete_registered_BF14_original_source_bound_publication_v1',
        status='ACCEPTED_COMPLETE_ORIGINAL_PHYSICAL_EXCLUSION', original_id=ID,
        original_path=cell['path'], target_mask='001/00', target_Q='1105/256',
        radius_scope='q < 1105/256', new_original_cells=1, new_masks=0,
        new_positional_roots=0, new_roadmap_gates=0,
        original_before=dict(closed=222, open=9, total=231),
        original_after=dict(closed=223, open=8, total=231),
        mask_ledger=dict(closed=8, open=24, total=32),
        remaining_original_families=dict(A=1, B=4, C=3, D=0),
        fixed_denominators=dict(original_cells=231, masks=32, positional_roots=7915, roadmap_gates=15),
        all_nine_original_frames_retained=True, original_corners=36, original_pairs=36,
        original_cone_comparisons=5, original_actual_links=['AB', 'BC', 'EF', 'FG'],
        original_strict_weak_link='CD', counts=info['counts'],
        literal_row_accounting=counts, terminal_kinds=table['terminal_kinds'],
        fresh_portable_receipt=receipt, proof_archive=ready,
        closure_hand=closure_path.name, closure_hand_sha256=digest(closure_path),
        fixed_register_sha256=digest(ledger), all_231_original_definitions_unchanged=True,
        other_230_original_entries_unchanged=True,
        published_files={p.name: dict(bytes=p.stat().st_size, sha256=digest(p))
                         for p in sorted(out.iterdir()) if p.is_file()},
        lean_lake_ci_run=False)
    output = nine / 'computer_assisted' / (NAME + '_manifest.json')
    dump(output, publication)
    print(json.dumps(dict(status='BF14_COMPLETE_PUBLICATION_PREPARED',
                          manifest=str(output), manifest_sha256=digest(output),
                          closed=223, open=8, changed_original_ids=changed), indent=2))


if __name__ == '__main__':
    main()
