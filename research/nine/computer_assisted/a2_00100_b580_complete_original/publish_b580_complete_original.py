"""Publish exactly the completely replayed B580 original; no Git or arithmetic."""
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import argparse
import json
import shutil

ID = 'negative-580db3624cf4c2e2'
NAME = 'a2_00100_b580_complete_original'
TREE_SHA = '2f8125fc8107684ef2d31bb64cd82ea8c71a621dd671786355f4906daa28ea1a'
UNIONS = {'proxy': 96, 'angle': 101, 'sat': 21}
KINDS = {'accepted_center_interval_terminal': 167, 'positive_exact_reserve': 347,
         'proved_empty_analytic_frame': 11, 'proved_frame_contradiction': 11,
         'empty_difference': 1}

def digest(path):
    h = sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_text())

def dump(path, obj):
    Path(path).write_text(json.dumps(obj, indent=2) + '\n')

def one(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new, 1)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('repo', type=Path)
    ap.add_argument('packet', type=Path)
    ap.add_argument('portable_replay', type=Path)
    ap.add_argument('archive', type=Path)
    ap.add_argument('reviews', type=Path)
    args = ap.parse_args()
    nine = args.repo.resolve() / 'research/nine'
    packet, fresh, archive, reviews = (p.resolve() for p in
        (args.packet, args.portable_replay, args.archive, args.reviews))
    here = Path(__file__).resolve().parent
    out = nine / 'computer_assisted' / NAME
    assert not out.exists()
    info = read(packet / 'ORIGINAL_PROOF.json')
    native = read(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    replay = read(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    receipt = read(fresh / 'PORTABLE_RECEIPT.json')
    ready = read(archive / 'ARCHIVE_READY.json')
    table = read(here / 'B580_COMPLETE_LITERAL_TABLE_AUDIT.json')
    byte_audit = read(here / 'B580_COMPLETE_ARCHIVE_AUDIT.json')
    structure = read(reviews / 'B580_FINAL_STRUCTURAL_REVIEW.json')
    physical = read(reviews / 'B580_FINAL_PHYSICAL_SOURCE_REVIEW.json')
    hand_table = read(reviews / 'B580_FINAL_HAND_TABLE_ACCEPTANCE_REVIEW.json')
    transport = read(reviews / 'B580_PORTABLE_TRANSPORT_REVIEW.json')
    publishing = read(reviews / 'B580_PUBLICATION_SOURCE_REVIEW.json')
    assert publishing['status'] == 'PASS_B580_PUBLICATION_SOURCE_SCOPE_REVIEW'
    assert publishing['publisher_sha256'] == digest(__file__)
    assert publishing['blocking_findings'] == []
    assert info['original_id'] == receipt['original_id'] == ready['original_id'] == ID
    assert info['complete'] and not info['open_prototype']
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'
    for key in ('complete', 'whole_original_proved', 'every_new_bound_and_cover_replayed',
                'all_inputs_rehashed_at_completion', 'external_workspace_reads_forbidden'):
        assert receipt[key] is True
    assert receipt['numerical_modules_imported'] is False
    assert receipt['packet_manifest_sha256'] == digest(packet / 'INPUT_MANIFEST.json')
    assert receipt['report_sha256'] == digest(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    assert table['status'] == 'PASS_REGISTERED_B_COMPLETE_LITERAL_TABLE_AND_ROW_ACCOUNTING'
    assert byte_audit['status'] == 'PASS_REGISTERED_B_COMPLETE_ARCHIVE_AND_PART_AUDIT'
    assert byte_audit['archive_sha256'] == ready['archive_sha256']
    assert byte_audit['fresh_complete_report_sha256'] == receipt['report_sha256']
    assert physical['status'] == 'PASS_B580_PHYSICAL_HAND_ATTACHMENT_AND_COMPLETE_STRUCTURAL_TABLE'
    assert structure['status'] == 'PASS_B580_COMPLETE_STRUCTURE_AND_PHYSICAL_ATTACHMENT_ARITHMETIC_PENDING'
    assert structure['final_manifest_sha256'] == physical['manifest_sha256'] == TREE_SHA
    assert physical['physical_attachment_sha256'] == digest(packet / 'B580_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md')
    for review in (structure, physical, hand_table, transport):
        assert review['status'].startswith('PASS_')
        assert review['original_id'] == ID and review['blocking_findings'] == []
    for key in ('all_child_states_independently_reconstructed', 'all_round_state_links_checked',
                'all_shared_closed_faces_retained', 'original_parent_id_path_and_initial_state_identical',
                'all_231_original_definition_tuples_unchanged',
                'all_nine_original_labels_and_corners_and_pair_domains_retained', 'fixed_H_I_order_preserved'):
        assert structure[key] is True
    assert structure['H_I_permutation_transport_assumed'] is False
    assert transport['complete'] is True and transport['open_leaves'] == 0
    assert transport['packet_input_manifest_sha256'] == receipt['packet_manifest_sha256']
    assert transport['verified_added_aliases'] == 769
    assert transport['all_previous_binding_entries_identical']
    assert transport['all_prior_proof_and_checker_bytes_unchanged']
    assert transport['original_parent_id_path_and_hash_derived_and_checked']
    for report in (native, replay):
        assert report['status'] == 'PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
        assert report['initial_original_id'] == ID and report['certificate_sha256'] == TREE_SHA
        assert report['complete'] and report['whole_original_proved']
        assert report['entire_registered_original_domain_retained'] is True
        assert report['nodes'] == 755 and report['terminal_leaves'] == report['excluded_leaves'] == 537
        assert report['open_leaves'] == 0 and report['complete_unions'] == UNIONS
        assert report['relative_support_chord_rows_checked'] == 1177
    for key in info['counts']:
        assert native[key] == replay[key] == info['counts'][key]
    for key in ('initial_path', 'parent_certificate_sha256', 'leaf_table'):
        assert native[key] == replay[key]
    assert table['terminal_kinds'] == structure['terminal_kinds'] == physical['actual_terminal_kinds'] == KINDS
    assert table['totals'] == structure['totals'] == {
        'rounds': 350, 'deductions': 66464, 'premise_rows': 209185, 'terminal_rows': 7089}
    assert table['tree_manifest_sha256'] == TREE_SHA
    assert table['terminal_table_sha256'] == digest(packet / 'COMPLETE_TERMINAL_TABLE.md')
    assert table['exact_report_sha256'] == digest(packet / 'original_audits/EXACT_TREE_REPLAY.json')
    for report in (structure, physical, hand_table, transport):
        for source, expected in report['source_sha256'].items():
            assert digest(source) == expected, source

    ledger = nine / 'gates/A2_00100_FIXED_FRONTIER.json'
    before = read(ledger)
    before_sha = digest(ledger)
    assert publishing['expected_before_register_sha256'] == before_sha
    assert (before['closed_cells'], before['open_cells'], len(before['cells'])) == (223, 8, 231)
    assert before_sha == info['current_definition_attachment']['current_register']['sha256']
    cell = next(c for c in before['cells'] if c['id'] == ID)
    assert cell['status'] == 'OPEN' and cell['path'] == info['original_path'] == replay['initial_path']
    assert info['current_definition_attachment']['all_231_original_definitions_unchanged']
    assert before['global_mask_ledger'] == {'closed': 8, 'open': 24, 'new_mask_closures': 0}
    out.mkdir()

    def copy(source, name=None):
        source = Path(source)
        target = out / (name or source.name)
        assert source.is_file() and not target.exists()
        shutil.copyfile(source, target)
        assert digest(source) == digest(target)

    for part in ready['parts']:
        p = archive / part['file']
        assert p.stat().st_size == part['bytes'] and digest(p) == part['sha256']
        copy(p)
    copy(archive / 'ARCHIVE_READY.json')
    for name in ('RELEASE_MANIFEST.json', 'INPUT_MANIFEST.json', 'PUBLISHED_PRIOR.json',
                 'ORIGINAL_PROOF.json', 'TRANSPORT_PREPARATION.json',
                 'COMPLETE_TERMINAL_TABLE.md', 'B580_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md'):
        copy(packet / name)
    copy(packet / 'records/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md')
    for name in ('RELATIVE_SUPPORT_CHORD_HAND_PROOF.md', 'OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md'):
        copy(packet / 'code/relative_support_chords' / name)
    for p in sorted((packet / 'review_inputs').iterdir()):
        copy(p)
    for name in ('B580_PORTABLE_TRANSPORT_REVIEW.json', 'B580_PUBLICATION_SOURCE_REVIEW.json', 'review_b580_final_structure.py',
                 'review_b580_physical_parent.py', 'review_b580_portable_transport.py'):
        copy(reviews / name)
    copy(packet / 'original_audits/EXACT_TREE_REPLAY.json', 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json')
    copy(fresh / 'COMPLETE_ORIGINAL_REPLAY.json')
    copy(fresh / 'PORTABLE_RECEIPT.json')
    for name in ('B580_COMPLETE_ARCHIVE_AUDIT.json', 'audit_registered_b_literal_table.py',
                 'audit_registered_b_complete_archive.py', 'prepare_registered_b_portable_transport.py',
                 'publish_b580_complete_original.py'):
        copy(here / name)
    archiver = nine / 'computer_assisted/a2_00100_b340_complete_original/archive_registered_b_packet_streaming.py'
    assert digest(archiver) == ready['outer_archiver_sha256']
    copy(archiver)

    summary = '''The complete physical tree excludes `negative-580db3624cf4c2e2`
in the strict-radius caller `q < Q = 1105/256`. Its **755 nodes exclude all
537 terminal domains, with zero OPEN leaves**. The complete unions are
96 four-way inset covers, 101 two-way closed slope covers and 21 eight-way
physical separating-axis covers.

Fresh native and portable exact replay, independent physical and complete
coverage review, the full literal terminal-table audit and archive/member
verification all pass. The arithmetic checks 350 bound rounds, 66,464
rational deductions and 216,274 printed row occurrences, including
1,177 independently decoded relative-support chord rows.

This accepts exactly one unchanged original: **223 CLOSED / 8 OPEN becomes
224 CLOSED / 7 OPEN**, with remaining families **A1, B3, C3, D0**. The
231-cell register and all original definitions remain fixed. Whole masks
remain **8 CLOSED / 24 OPEN**; `001/00` and reversal `100/00` remain OPEN.
No Lean, Lake, compilation or CI was run.
'''
    acceptance = f'''# Final acceptance of the complete B580 original

{summary}
## Physical and complete-cover attachment

The frozen negative baseline-68 path retains `t_A,t_D<=0`, `y_F>=1/2`,
`x_F-x_H<=0` and `y_D-y_F<=-3/5`. The inherited ordering `x_H<=x_I`
and strict transverse normalization remain. The physical attachment
derives the literal branch and preserves all nine original unit frames,
36 original corners, 36 physical pairs, five cones, actual AB/BC/EF/FG
and strictly weak CD.

The independent structural review reconstructs every child and all 350
bound-round links. It verifies the two literal-prefix assembly stages,
671 unchanged original-base sibling payloads and eight candidate-status-
only changes. All owner, axis, sign and shared closed faces are covered.
The root initial record is `{replay['parent_certificate_sha256']}`;
the final manifest is `{TREE_SHA}`.

The complete table contains 347 positive-reserve terminals, 167 center-
interval contradictions, 11 empty analytic frames, 11 frame contradictions
and one empty difference. All displayed positive reserve lower bounds
are checked against the exact records. The two arithmetic replays
reconstruct every weighted row and pay every coefficient residual.

## Portable replay and archive

The fresh portable replay checks {receipt['packet_inputs']} packet inputs
and {receipt['prior_inputs']} published-prior inputs. Historical proof reads
are forbidden, numerical modules are absent, and every input is rehashed
at completion. Transport adds 769 aliases to identical frozen bytes and
17 reviewed attachments; every prior proof and checker byte is unchanged.
Its receipt is `PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`.

The archive is {ready['archive_bytes']:,} bytes in {len(ready['parts'])} ordered
parts, with SHA256 `{ready['archive_sha256']}`. Every part, the concatenated
digest and all {ready['all_archive_members_verified']} regular members are
independently checked. Native and portable mathematical reports agree.
The required prior archive is `{ready['prior_archive_sha256']}`.

The archived status register precedes acceptance and intentionally leaves
B580 OPEN; the live fixed register records the subsequent one-cell change.
The accepted conclusion is strict-radius exclusion of this exact original.
It grants no whole-mask, positional-root, roadmap-gate or global closed-Q
classification. No human or proof-kernel verification is claimed.
'''
    (out / 'ROOT_FINAL_ACCEPTANCE.md').write_text(acceptance)
    (out / 'README.md').write_text('# Complete B580 original\n\n' + summary +
        '\n[Final acceptance](ROOT_FINAL_ACCEPTANCE.md) · '
        '[Physical attachment](B580_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md) · '
        '[Complete terminal table](COMPLETE_TERMINAL_TABLE.md) · '
        '[Archive parts](ARCHIVE_READY.json).\n\n'
        'The complete literal tree, independent checker sources, frozen bindings '
        'and fresh replay reports are in the ordered archive parts.\n')
    closure_path = nine / 'A2_00100_B580_COMPLETE_ORIGINAL_CLOSURE.md'
    closure_path.write_text(f'''# Complete B580 original: 224 CLOSED / 7 OPEN

{summary}
## Original caller and finite proof

The frozen negative baseline frontier index is 68, with path

```json
{json.dumps(cell['path'], separators=(',', ':'))}
```

The [physical attachment](computer_assisted/{NAME}/B580_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md)
derives the literal original-nine predicates, strict-radius scope, exact
support rules and complete finite-cover argument. Every leaf is excluded
by a positive rational reserve or a separately checked interval/frame
contradiction. Complete induction over every internal union excludes the
unchanged registered root.

| Proof item | Count |
| --- | ---: |
| Node records | 755 |
| Four-way inset covers | 96 |
| Eight-way physical separators | 21 |
| Two-way closed slope covers | 101 |
| Excluded terminal domains | 537 |
| OPEN terminal domains | 0 |
| Exact bound rounds | 350 |
| Rational deductions | 66,464 |
| Premise-row occurrences | 209,185 |
| Terminal-row occurrences | 7,089 |
| Relative-support chord row occurrences | 1,177 |

The [complete table](computer_assisted/{NAME}/COMPLETE_TERMINAL_TABLE.md)
lists every leaf. The [final acceptance](computer_assisted/{NAME}/ROOT_FINAL_ACCEPTANCE.md)
and [publication manifest](computer_assisted/{NAME}_manifest.json) bind the
physical reviews, complete exact reports, archive and one-original ledger delta.

## Reproduction

Concatenate the parts in `ARCHIVE_READY.json` order, checking each part and
the combined SHA256 `{ready['archive_sha256']}`. Restore the pinned prior
in `PUBLISHED_PRIOR.json`, then extract both inside one directory. Run:

```sh
python3 -B -S {packet.name}/code/replay_registered_b_relative_support_packet.py \\
  --prior b16a_I32_complete_H_checkpoint --output fresh_b580_replay
```

Require `PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`,
`complete=true`, `whole_original_proved=true` and zero OPEN leaves.
Only B580 changes status; the other 230 entries and all fixed denominators
(231 originals, 32 masks, 7,915 positional roots, 15 roadmap gates) are unchanged.
Seven originals still require complete proofs. The accepted scope is
`q < 1105/256`.
''')

    after = deepcopy(before)
    after.update(assembly='../' + closure_path.name, cell_review='../' + closure_path.name,
        manifest='../computer_assisted/' + NAME + '_manifest.json', closed_cells=224,
        open_cells=7, latest_new_closed_cells=1, cumulative_new_closed_since_53=171,
        preceding_assembly=before['assembly'], preceding_manifest=before['manifest'])
    selected = next(c for c in after['cells'] if c['id'] == ID)
    method = 'complete_registered_original_physical_tree_with_relative_support_chords'
    selected.update(status='CLOSED', method=method, terminal_leaves=537)
    selected['evidence'] = dict(method=method, record_id=ID, whole_cell_exclusion=True,
        complete_closed_face_cover=True, all_original_physical_conditions_retained=True,
        original_initial_state_sha256=replay['parent_certificate_sha256'], tree_manifest_sha256=TREE_SHA,
        archive_parts_manifest=NAME + '/ARCHIVE_READY.json', archive_sha256=ready['archive_sha256'],
        archive_bytes=ready['archive_bytes'], prior_archive_sha256=ready['prior_archive_sha256'],
        certificate=NAME + '/COMPLETE_ORIGINAL_REPLAY.json', certificate_sha256=receipt['report_sha256'],
        native_report_sha256=digest(out / 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json'),
        independent_checker='replay_registered_b_relative_support_packet.py',
        independent_checker_sha256=digest(packet / 'code/replay_registered_b_relative_support_packet.py'),
        independent_report=NAME + '/PORTABLE_RECEIPT.json', independent_report_sha256=digest(out / 'PORTABLE_RECEIPT.json'),
        root_hand_table_review=NAME + '/ROOT_FINAL_ACCEPTANCE.md', root_hand_table_review_sha256=digest(out / 'ROOT_FINAL_ACCEPTANCE.md'),
        terminal_table_sha256=digest(out / 'COMPLETE_TERMINAL_TABLE.md'), nodes=755,
        terminal_leaves=537, open_leaves=0, all_new_bound_and_cover_arithmetic_repeated=True,
        radius_scope='q < 1105/256', whole_mask_closed=False)
    fields = ('id', 'sign', 'baseline_frontier_index', 'path')
    assert [[c[k] for k in fields] for c in before['cells']] == [[c[k] for k in fields] for c in after['cells']]
    changed = [a['id'] for a, b in zip(before['cells'], after['cells']) if a != b]
    assert changed == [ID]
    assert sum(c['status'] == 'CLOSED' for c in after['cells']) == 224
    assert sum(c['status'] == 'OPEN' for c in after['cells']) == 7
    assert after['global_mask_ledger'] == before['global_mask_ledger']
    dump(ledger, after)
    dump(out / 'FIXED_LEDGER_DELTA_AUDIT.json', dict(
        status='PASS_EXACT_ONE_REGISTERED_ORIGINAL_LEDGER_DELTA', before_sha256=before_sha,
        after_sha256=digest(ledger), changed_original_ids=changed,
        all_231_original_definitions_unchanged=True, other_230_entries_unchanged=True,
        before=dict(closed=223, open=8, total=231), after=dict(closed=224, open=7, total=231),
        mask_ledger=dict(closed=8, open=24, total=32), new_original_cells=1, new_masks=0,
        new_positional_roots=0, new_roadmap_gates=0,
        fixed_denominators=dict(original_cells=231, masks=32, positional_roots=7915, roadmap_gates=15),
        remaining_open_original_ids=[c['id'] for c in after['cells'] if c['status'] == 'OPEN'],
        lean_lake_ci_run=False))
    heading = '> **ACTIVE EXECUTION DIRECTIVE — 2026-11-05:** [Current mask, priorities, bounded whole-cell attempts and exact acceptance](CURRENT_MASK_DIRECTIVE.md). **224/231 original cells CLOSED, 7 OPEN (A1, B3, C3); 8/32 masks CLOSED.** Bf14 and B580 are accepted; continue B16, A and the remaining B/C originals. The next milestone is **225/231**. Historical paragraphs below retain their original scope. No Lean/Lake/CI.'
    section = '## Complete B580 original: 224 CLOSED / 7 OPEN\n\n' + summary + '\n[Complete proof and reproduction](A2_00100_B580_COMPLETE_ORIGINAL_CLOSURE.md).\n\n'
    for name in ('PROGRESS.md', 'HANDOFF_A2_FIXED_CLOSURE.md'):
        p = nine / name
        first, rest = p.read_text().split('\n', 1)
        assert first.startswith('> **ACTIVE EXECUTION DIRECTIVE')
        text = heading + '\n' + rest
        text = one(text, '## Complete Bf14 original: 223 CLOSED / 8 OPEN', section + '## Complete Bf14 original: 223 CLOSED / 8 OPEN')
        if name == 'PROGRESS.md':
            replacements = [
                ('**223/231 cells CLOSED, 8 OPEN; 8/32 masks CLOSED, 24 OPEN.**', '**224/231 cells CLOSED, 7 OPEN; 8/32 masks CLOSED, 24 OPEN.**'),
                ('# n=9: 223/231 current-mask cells closed; 8 remain OPEN', '# n=9: 224/231 current-mask cells closed; 7 remain OPEN'),
                ('**Latest accepted closure: the complete Bf14 original-cell exclusion.**\nThe same register now has **223 CLOSED / 8 OPEN**, with\n**170 additions beyond the first 53**. Remaining families: **A1, B4, C3, D0**.', '**Latest accepted closure: the complete B580 original-cell exclusion.**\nThe same register now has **224 CLOSED / 7 OPEN**, with\n**171 additions beyond the first 53**. Remaining families: **A1, B3, C3, D0**.'),
                ('[Latest complete assembly](A2_00100_BF14_COMPLETE_ORIGINAL_CLOSURE.md)', '[Latest complete assembly](A2_00100_B580_COMPLETE_ORIGINAL_CLOSURE.md)'),
                ('[Source-bound packet and fresh portable replay](computer_assisted/a2_00100_bf14_complete_original_manifest.json)', '[Source-bound packet and fresh portable replay](computer_assisted/a2_00100_b580_complete_original_manifest.json)')]
            for old, new in replacements:
                text = one(text, old, new)
            text = text.replace('register is 223/8, with A1/B4/C3/D0 remaining.', 'register is 224/7, with A1/B3/C3/D0 remaining.')
        else:
            text = one(text, '# Current A.2 handoff: 223/231 current-mask cells closed; 8 OPEN', '# Current A.2 handoff: 224/231 current-mask cells closed; 7 OPEN')
            text = text.replace('- Current mask: **223 CLOSED / 8 OPEN**, same 231 IDs and certified full cover.', '- Current mask: **224 CLOSED / 7 OPEN**, same 231 IDs and certified full cover.')
            text = text.replace('The register is **223 CLOSED / 8 OPEN**; the mask ledger is **8 CLOSED /', 'The register is **224 CLOSED / 7 OPEN**; the mask ledger is **8 CLOSED /')
        p.write_text(text)
    p = nine / 'CURRENT_MASK_DIRECTIVE.md'
    text = p.read_text()
    text = one(text, '**223 of 231 original cells CLOSED, 8 OPEN (A1, B4, C3; D0)**', '**224 of 231 original cells CLOSED, 7 OPEN (A1, B3, C3; D0)**')
    text = one(text, '**224/231 fully closed originals**', '**225/231 fully closed originals**')
    text = one(text, '## Fresh complete-original acceptance — 5 November 2026 UTC',
        '## Complete B580 original accepted — 5 November 2026 UTC\n\n' + summary +
        '\n[Complete proof and reproduction](A2_00100_B580_COMPLETE_ORIGINAL_CLOSURE.md).\n\n## Earlier Bf14 acceptance — 5 November 2026 UTC')
    p.write_text(text)
    publication = dict(schema='complete_registered_B580_original_source_bound_publication_v1',
        status='ACCEPTED_COMPLETE_ORIGINAL_PHYSICAL_EXCLUSION', original_id=ID,
        original_path=cell['path'], target_mask='001/00', target_Q='1105/256', radius_scope='q < 1105/256',
        new_original_cells=1, new_masks=0, new_positional_roots=0, new_roadmap_gates=0,
        original_before=dict(closed=223, open=8, total=231), original_after=dict(closed=224, open=7, total=231),
        mask_ledger=dict(closed=8, open=24, total=32), remaining_original_families=dict(A=1, B=3, C=3, D=0),
        fixed_denominators=dict(original_cells=231, masks=32, positional_roots=7915, roadmap_gates=15),
        all_nine_original_frames_retained=True, original_corners=36, original_pairs=36,
        original_cone_comparisons=5, original_actual_links=['AB', 'BC', 'EF', 'FG'], original_strict_weak_link='CD',
        counts=info['counts'], literal_row_accounting=table['totals'], terminal_kinds=KINDS,
        fresh_portable_receipt=receipt, proof_archive=ready, closure_hand=closure_path.name,
        closure_hand_sha256=digest(closure_path), fixed_register_sha256=digest(ledger),
        all_231_original_definitions_unchanged=True, other_230_original_entries_unchanged=True,
        published_files={p.name: dict(bytes=p.stat().st_size, sha256=digest(p)) for p in sorted(out.iterdir()) if p.is_file()},
        lean_lake_ci_run=False)
    pub = nine / 'computer_assisted' / (NAME + '_manifest.json')
    dump(pub, publication)
    print(json.dumps(dict(status='B580_COMPLETE_PUBLICATION_PREPARED', manifest=str(pub),
        manifest_sha256=digest(pub), closed=224, open=7, changed_original_ids=changed), indent=2))

if __name__ == '__main__':
    main()
