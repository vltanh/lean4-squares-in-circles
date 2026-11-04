#!/usr/bin/env python3
"""Prepare one reviewed whole-original D821 closure, never a partial credit.

Requires completed native, cold, literal-table and full archive gates.
Preserves every other fixed-original entry and the external native-checkpoint
supplements. Git publication itself is a separate compare-and-swap operation.
"""
from pathlib import Path
from copy import deepcopy
import hashlib
import json
import os
import shutil
import subprocess

WORK = Path('/workspace/scratch/f9f48fcfb253')
REPO = WORK / 'repo'
NINE = REPO / 'research/nine'
CA = NINE / 'computer_assisted'
PACKET = Path('/tmp/d821_complete_portable_v1_20261104/d821_complete_original_package')
FRESH = PACKET.parent / 'fresh_replay'
ARCH = WORK / 'global_work/d821_complete_archive_v1'
D = WORK / 'global_work/d821_work'
NAME = 'a2_00100_d821_complete_original'
OUT = CA / NAME
NATIVE_NAME = 'a2_00100_d821_complete_native_checkpoint_v1'
NATIVE = CA / NATIVE_NAME
ID = 'positive-821c9a2debeed0aa'
ORIGINAL_PATH = [['angle', 3, 1], ['angle_cut', [0, '0'], 1],
                 ['alternate_four_escape', [1, 7], [3]]]
PRE_REGISTER_SHA = 'b805df8706151a4eb43bd8c0912205ffbfd67d8dfb582daf441717e04fd023dc'
NATIVE_COMMIT = 'b6ad19e31b1fa72235bba8307332fd3dbfaee67a'


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def git_bytes(path, commit='HEAD'):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def copy(source, name=None):
    source = Path(source)
    target = OUT / (name or source.name)
    assert source.is_file() and not source.is_symlink() and not target.exists()
    shutil.copyfile(source, target)
    assert sha(source) == sha(target)
    return target


def once(text, old, new):
    assert text.count(old) == 1, (old, text.count(old))
    return text.replace(old, new, 1)


def main():
    if not __debug__:
        raise RuntimeError('Publication gates require assertions enabled.')
    assert not OUT.exists()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()
    ready = read(ARCH / 'ARCHIVE_READY.json')
    archive_audit = read(WORK / 'd_work/D821_COMPLETE_ROOT_ARCHIVE_AUDIT.json')
    table_audit_path = WORK / 'd_work/D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json'
    path_audit_path = WORK / 'd_work/D821_REGISTERED_PATH_LITERAL_ROOT_REVIEW.json'
    assert sha(table_audit_path) == '7f5c37538f6836f377c270fb346f5dbbfaa45174f1a69d3d3c49e55558326f1c'
    assert sha(path_audit_path) == 'ff0d33fdbdedfe18dd5034b421e21adc21dd094f2830bcc99599e5549d4ea150'
    table_audit = read(table_audit_path)
    path_audit = read(path_audit_path)
    receipt = read(FRESH / 'PORTABLE_RECEIPT.json')
    fresh = read(FRESH / 'COMPLETE_ORIGINAL_REPLAY.json')
    native = read(D / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json')
    assert archive_audit['status'] == 'PASS_ROOT_D821_COMPLETE_ARCHIVE_AND_PART_AUDIT'
    assert archive_audit['archive_ready_sha256'] == sha(ARCH / 'ARCHIVE_READY.json')
    assert archive_audit['archive_sha256'] == ready['archive_sha256']
    assert archive_audit['all_regular_members_verified'] == 2436
    assert archive_audit['all_2432_frozen_inputs_unchanged']
    assert archive_audit['native_and_cold_all_mathematical_fields_identical']
    assert table_audit['status'] == 'PASS_D821_COMPLETE_LITERAL_TABLE_AND_INDEPENDENT_AFFINE_TERMINAL_AUDIT'
    assert [table_audit[k] for k in ('trees','nodes','grafts','rounds','deductions','premise_rows','terminal_rows')] == [46,650,42,789,109838,281916,6355]
    assert sum(table_audit['exclusions_by_kind'].values()) == 415
    assert table_audit['closed_unions'] == {'proxy':79,'angle':104,'sat':10}
    assert sha(D/'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json') == table_audit['report_sha256']
    assert sha(PACKET/'COMPLETE_TERMINAL_TABLE.json') == table_audit['table_sha256']
    assert sha(PACKET/'COMPLETE_TERMINAL_TABLE.md') == table_audit['markdown_sha256']
    assert path_audit['status'] == 'PASS_D821_LITERAL_REGISTERED_PATH_AND_PHYSICAL_ATTACHMENT'
    assert path_audit['all_231_original_definitions_unchanged']
    assert path_audit['original_id'] == ID and path_audit['original_path'] == ORIGINAL_PATH
    assert receipt['status'] == 'PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D821'
    assert receipt['input_files'] == 2432 and receipt['input_bytes'] == 2422735486
    assert receipt['packet_manifest_sha256'] == sha(PACKET / 'INPUT_MANIFEST.json')
    assert receipt['exact_report_sha256'] == sha(FRESH / 'COMPLETE_ORIGINAL_REPLAY.json')
    assert sha(FRESH / 'PORTABLE_RECEIPT.json') == archive_audit['fresh_portable_receipt_sha256']
    assert receipt['all_inputs_rehashed_at_completion'] and receipt['external_workspace_reads_forbidden']
    assert receipt['numerical_imports_forbidden'] and not receipt['lean_lake_ci_run']
    for proof in (native, fresh):
        assert proof['status'] == 'PASS_COMPLETE_ORIGINAL_CELL' and proof['whole_original_proved']
        assert proof['original_id'] == ID and proof['original_path'] == ORIGINAL_PATH
        assert proof['complete_closed_complement_domains'] == 5
        assert proof['proposed_original_cell_credit'] == 1 and proof['whole_mask_credit'] == 0
    ledger = NINE / 'gates/A2_00100_FIXED_FRONTIER.json'
    before_bytes = ledger.read_bytes()
    assert digest(before_bytes) == PRE_REGISTER_SHA
    before = json.loads(before_bytes)
    assert (before['closed_cells'], before['open_cells'], len(before['cells'])) == (221, 10, 231)
    original = next(c for c in before['cells'] if c['id'] == ID)
    assert original['status'] == 'OPEN' and original['path'] == ORIGINAL_PATH
    assert before['original_predicate'].startswith('D_001/00^lt')

    # Resolve and validate concurrent native-checkpoint history before writing.
    native_manifest_rel = 'research/nine/computer_assisted/' + NATIVE_NAME + '_manifest.json'
    native_prefix = 'research/nine/computer_assisted/' + NATIVE_NAME + '/'
    historical_manifest_bytes = git_bytes(native_manifest_rel, NATIVE_COMMIT)
    historical_manifest = json.loads(historical_manifest_bytes)
    historical_readme = git_bytes(native_prefix + 'README.md', NATIVE_COMMIT)
    external_readme = git_bytes(native_prefix + 'README.md', head)
    assert digest(historical_readme) == historical_manifest['files']['README.md']['sha256']
    assert git_bytes(native_manifest_rel, head) == historical_manifest_bytes
    preserved_core = {}
    for name, entry in historical_manifest['files'].items():
        if name != 'README.md':
            data = git_bytes(native_prefix + name, head)
            assert len(data) == entry['bytes'] and digest(data) == entry['sha256']
            preserved_core[name] = entry
    extras = {}
    for name in ('stage_d821_portable_sources.py','test_stage_d821_portable_sources.py'):
        data = git_bytes(native_prefix + name, head)
        extras[name] = {'bytes':len(data),'sha256':digest(data)}
    prepared_hand = D / 'D821_COMPLETE_ORIGINAL_CLOSURE_HAND_PAGE.md'
    assert sha(prepared_hand) == 'fb640e35fdeeb38e164e576301634052e2954fcc6c1161e9222b7448c750ca93'
    assert prepared_hand.read_text().count('## 8. Publication gate — prepared only') == 1
    assert native['component_audits'][2]['pilot']['reserve'] == '514143/10485760'
    handoff_before = (NINE/'HANDOFF_A2_FIXED_CLOSURE.md').read_bytes()
    assert handoff_before == git_bytes('research/nine/HANDOFF_A2_FIXED_CLOSURE.md', head)

    OUT.mkdir()
    (OUT/'HANDOFF_BEFORE_D821_ACCEPTANCE.md').write_bytes(handoff_before)
    for part in ready['parts']:
        source = ARCH / part['file']
        assert source.stat().st_size == part['bytes'] and sha(source) == part['sha256']
        target = OUT / source.name
        os.link(source, target)
        assert sha(target) == part['sha256']
    for name in ('ARCHIVE_READY.json',):
        copy(ARCH / name)
    for name in ('INPUT_MANIFEST.json','RELEASE_MANIFEST.json','ORIGINAL_PROOF.json',
                 'COMPLETE_TERMINAL_TABLE.json','COMPLETE_TERMINAL_TABLE.md',
                 'D821_COMPLETE_ASSEMBLY_HAND_PROOF.md','replay_portable_d821_packet.py'):
        copy(PACKET / name)
    copy(FRESH / 'PORTABLE_RECEIPT.json')
    copy(FRESH / 'COMPLETE_ORIGINAL_REPLAY.json')
    copy(D / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json', 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json')
    copy(D / 'complete_original_final_plan/D821_COMPLETE_ORIGINAL_GRAFT_PLAN.json')
    for name in ('PRESERVED_CHECKPOINT_INDEX.json','PRESERVED_CHECKPOINT_INDEX.md'):
        copy(D / 'complete_checkpoint_provenance' / name)
    for name in ('D821_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md',
                 'D821_REGISTERED_PATH_LITERAL_ROOT_REVIEW.json',
                 'D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json',
                 'D821_COMPLETE_ROOT_ARCHIVE_AUDIT.json',
                 'audit_d821_complete_table_root.py','audit_d821_complete_archive_root.py',
                 'D821_ARCHIVE_RESUME_V3_ROOT_REVIEW.json'):
        copy(WORK / 'd_work' / name)
    for name in ('archive_complete_d821_packet_streaming_fast_v2.py',
                 'archive_complete_d821_packet_streaming_resume_v3.py',
                 'D821_ARCHIVER_V2_TO_V3.diff','D821_ARCHIVER_RESUME_V3_REVIEW_REQUEST.json'):
        copy(D / name)
    for name in ('D821_ROOT_ARCHIVE_AUDITOR_INDEPENDENT_REVIEW.md',
                 'D821_ROOT_ARCHIVE_AUDITOR_INDEPENDENT_REVIEW.json'):
        copy(WORK / 'ac_work/tree' / name)
    copy(Path(__file__))

    root_review = f'''# Final root acceptance: complete D821 original

The unchanged original `{ID}`, positive baseline index 26, is excluded
in full. Native exact replay, fresh portable exact replay, the literal
terminal-table audit, physical hand assembly and complete archive audit
pass. This accepts exactly one original, advancing **221 CLOSED / 10 OPEN
to 222 CLOSED / 9 OPEN**. All whole-mask obligations retain their status.

The literal caller and all four alternate-chain halfspaces are recorded in
`D821_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md`; its separate audit checks
all 231 immutable definitions. All nine originals, 36 corners, 36 pairs,
five cones, actual AB/BC/EF/FG and strictly weak CD are retained.

## Complete physical assembly

The root's four exact bound rounds prove the D/G corridor, D slope sign
and I-left-of-D guard. The accepted actual-AB theorem and its strict-CD
equality blocker exclude the guarded row. The five closed complementary
domains cover every remaining caller, retaining all threshold faces.
Components 0, 1, 3 and 4 close through complete grafted trees; component 2
is a separate direct exact exclusion. The original-wide weak consequences
of completed components 0 and 1 enter only components 3 and 4, after fresh
source replay, in an explicitly acyclic dependency order.

The scalar theorem is recalculated over 28 domains, 103 leaves and 12,875
rational coefficients. The complete tree proof has 46 trees, 650 nodes,
42 grafts and 415 excluded tree terminals. Its complete unions comprise
79 four-way inset covers, ten eight-way physical separating covers and
104 two-way closed slope covers. The direct component-2 pilot, original
root and repeated dependency arithmetic are separate from these tree totals.

The 789 tree bound rounds contain 109,838 deductions and 288,271 row
occurrences: 281,916 premise rows plus 6,355 terminal rows. Root's separate
table audit rehashes every node, checks every complete child and graft, and
independently sums all 242 affine terminal contradictions, including
coefficient residual payments and printed reserve bounds. The remaining
terminals are 107 accepted interval, 13 empty analytic frame, 11 frame
contradiction, 38 early center-interval and four early difference-interval
exclusions. The two preserved migration snapshots add historical storage
references, not proof nodes or credit: 48 referenced manifests and 714
stored node records remain distinct from 46 proof trees and 650 proof nodes.

## Portable replay and transport

The cold replay rehashes all 2,432 frozen inputs, 2,422,735,486 bytes, with
old-workspace reads and numerical imports forbidden. Its receipt is
`8b873cf6dd8cc7ad608383e326303464e709e86151ad0bf66e55cffd6ade51e3`;
its exact report is
`29babcc1c812d09b07a84d7381414f6f0053e1d435b782ac673af3b024abb35f`.
Root compares the entire native and cold reports: every mathematical field
is identical after only elapsed-time removal and explicit hash-bound
filename normalization. This also matches all 889 original input hashes
and six checker hashes. The cold report includes 35 additional filename
aliases for the same inputs, not extra mathematical premises.

The final archive is {ready['archive_bytes']:,} bytes in {len(ready['parts'])}
ordered parts, SHA256 `{ready['archive_sha256']}`. Root independently checks
xz integrity, every part, the concatenated digest and all 2,436 regular
members, then rehashes the complete source packet. These byte/table audits
do not claim another repetition of all weighted geometric reconstruction;
that work is supplied by the native and cold exact proof runs.

Compression resumed from exact preserved outer release files. The release
creator is the included fast v2 archiver; actual read-only compression uses
the included reviewed v3 at SHA256
`d0c078e1bc991bb1b3ff078da0ac0e9cba71f6c06482bcf968d26ef8e16697d6`.
V3 writes no packet file and creates no raw tar. The earlier initiator of
the already present outer release files was not observed; no execution
history is inferred from them. Their entire byte stream and source map
are pinned and independently reverified before compression.

## Scope and history

Only D821 changes status. All other 230 original entries, including B340's
additional review evidence, remain byte-for-byte structurally identical.
The 32 masks, 7,915 positional roots and 15 roadmap IDs stay fixed. The
eventual whole-mask 001/00 and 100/00 conclusions remain **strict-radius**
because inherited cover terminals have that scope; this individual cell's
stronger closed-Q argument does not alter the whole-mask target.

The earlier native checkpoint and externally added byte-staging tool/tests
are preserved. Its original manifest and README are retained as historical
copies. The updated outer metadata distinguishes that OPEN/221 checkpoint
from this completed portable acceptance. Frozen proof inputs are unchanged.
No Lean compilation, Lake or CI ran. No Lean-kernel verification is claimed.
'''
    (OUT / 'ROOT_FINAL_ACCEPTANCE.md').write_text(root_review)

    closure_path = NINE / 'A2_00100_D821_COMPLETE_ORIGINAL_CLOSURE.md'
    copy(prepared_hand, 'PREPARED_CLOSURE_HAND_PAGE.md')
    hand = prepared_hand.read_text()
    hand = once(hand,
        'does not close the whole `001/00` mask. The final section separately records\nthe publication gate, which is not asserted complete by this prepared page.',
        'does not close the whole `001/00` mask. The final section records the\ncompleted archive audit and accepted one-original ledger update.')
    hand = once(hand,
        'has exact positive reserve\n3/5 - 526317/1048576 = 514143/5242880. No remaining component is marked',
        'has a positive whole-bound gap\n3/5 - 526317/1048576 = 514143/5242880. The separately scaled pilot\ncertificate records the exact reserve 514143/10485760. No remaining component is marked')
    marker = '## 8. Publication gate — prepared only'
    assert hand.count(marker) == 1
    hand = hand.split(marker)[0].rstrip() + f'''

## 8. Accepted release and fixed accounting

The complete native and cold exact proofs, root hand/table review and full
archive audit pass. The unchanged original `{ID}` is CLOSED. Exactly this
entry advances the fixed register from **221 CLOSED / 10 OPEN** to
**222 CLOSED / 9 OPEN**, leaving **A1, B5, C3, D0**. The mask ledger remains
**8 CLOSED / 24 OPEN**. All 231 original definitions and the other 230
entries are unchanged.

The [final source-bound manifest](computer_assisted/{NAME}_manifest.json)
binds the full proof, [literal table](computer_assisted/{NAME}/COMPLETE_TERMINAL_TABLE.md),
[root acceptance](computer_assisted/{NAME}/ROOT_FINAL_ACCEPTANCE.md), cold
reports, exact ledger delta and every archive part. The self-contained
archive contains {ready['archive_bytes']:,} bytes in {len(ready['parts'])}
ordered parts, SHA256 `{ready['archive_sha256']}`. All 2,436 regular members
and all 2,432 frozen inputs have been verified. Concatenate the parts in
`ARCHIVE_READY.json` order, verify the archive hash, extract into a clean
directory and follow the [replay entry](computer_assisted/{NAME}/README.md).

This is one original-cell closure. The whole-mask target remains
strict-radius; no mask, positional root or roadmap gate closes here.
No Lean, Lake or CI ran.
'''
    assert not closure_path.exists()
    closure_path.write_text(hand)
    (OUT / 'README.md').write_text(f'''# Complete D821 original: accepted portable proof

The whole registered original `{ID}` is excluded. Native and isolated
portable exact replay, complete physical/table review and full archive
audit pass. This closes one original: **222/231 CLOSED, 9 OPEN**. The
whole-mask ledger remains **8/32 CLOSED, 24 OPEN**.

Read `ROOT_FINAL_ACCEPTANCE.md`, `D821_COMPLETE_ASSEMBLY_HAND_PROOF.md`,
the registered physical attachment and `COMPLETE_TERMINAL_TABLE.md` for
the full argument. The source-bound manifest one directory above binds
all outer files and the exact one-cell ledger delta.

## Reproduce the complete proof

Concatenate all {len(ready['parts'])} parts in `ARCHIVE_READY.json` order.
Check each part hash and the reconstructed {ready['archive_bytes']:,}-byte
archive hash `{ready['archive_sha256']}`, then extract in a dedicated
directory. No earlier proof archive or original workspace is required.
Run from that directory, with a fresh output path:

```sh
python3 -B -S -u d821_complete_original_package/replay_portable_d821_packet.py \\
  --packet d821_complete_original_package --output fresh_replay
```

Success requires `PASS_COMPLETE_ORIGINAL_CELL` and
`PASS_FRESH_PORTABLE_COMPLETE_ORIGINAL_D821`. Python optimization must
remain disabled. The launcher permits only explicit hash-bound filename
aliases, rejects old-workspace reads and numerical imports, and rehashes
all 2,432 inputs at completion. Frozen inputs have SHA256 inventory
`5aa6efecb64df25da202b895d609598e8d66d8f13a77f172af3d0ccf25184a63`.

The proof retains all nine original squares, 36 corners, 36 physical pairs,
five cones, actual AB/BC/EF/FG and strictly weak CD. All five complementary
domains close. The 46-tree/650-node proof contains 415 tree exclusions;
component 2 has an additional separate direct exclusion. Historical
storage references are not added to proof counts. Eventual 001/00 and
100/00 whole-mask assembly remains strict-radius. No Lean, Lake or CI ran.
''')

    after = deepcopy(before)
    after.update(assembly='../' + closure_path.name, cell_review='../' + closure_path.name,
                 manifest='../computer_assisted/' + NAME + '_manifest.json',
                 closed_cells=222, open_cells=9, cumulative_new_closed_since_53=169,
                 latest_new_closed_cells=1, preceding_assembly=before['assembly'],
                 preceding_manifest=before['manifest'])
    cell = next(c for c in after['cells'] if c['id'] == ID)
    cell.update(status='CLOSED', method='complete_registered_original_five_domain_grafted_physical_proof',
                terminal_leaves=416)
    cell['evidence'] = dict(
        method=cell['method'], record_id=ID, whole_cell_exclusion=True,
        complete_closed_face_cover=True, all_original_physical_conditions_retained=True,
        original_initial_state_sha256=fresh['original_ancestor']['certificate_sha256'],
        complete_graft_plan_sha256=fresh['plan_sha256'],
        certificate=NAME + '/COMPLETE_ORIGINAL_REPLAY.json',
        certificate_sha256=sha(OUT / 'COMPLETE_ORIGINAL_REPLAY.json'),
        native_report_sha256=sha(OUT / 'NATIVE_COMPLETE_ORIGINAL_REPLAY.json'),
        independent_report=NAME + '/PORTABLE_RECEIPT.json',
        independent_report_sha256=sha(OUT / 'PORTABLE_RECEIPT.json'),
        independent_checker='replay_portable_d821_packet.py',
        independent_checker_sha256=sha(OUT / 'replay_portable_d821_packet.py'),
        root_hand_table_review=NAME + '/ROOT_FINAL_ACCEPTANCE.md',
        root_hand_table_review_sha256=sha(OUT / 'ROOT_FINAL_ACCEPTANCE.md'),
        terminal_table_sha256=sha(OUT / 'COMPLETE_TERMINAL_TABLE.md'),
        archive_parts_manifest=NAME + '/ARCHIVE_READY.json',
        archive_sha256=ready['archive_sha256'], archive_bytes=ready['archive_bytes'],
        complete_complement_domains=5, proof_trees=46, proof_nodes=650,
        tree_terminal_leaves=415, additional_direct_component_terminal=1, open_leaves=0,
        all_new_bound_and_cover_arithmetic_repeated=True, whole_mask_closed=False)
    definitions = lambda r: [{k:c[k] for k in ('id','sign','baseline_frontier_index','path')} for c in r['cells']]
    assert definitions(before) == definitions(after)
    changed = [a['id'] for a,b in zip(before['cells'],after['cells']) if a != b]
    assert changed == [ID]
    assert sum(c['status'] == 'CLOSED' for c in after['cells']) == 222
    assert sum(c['status'] == 'OPEN' for c in after['cells']) == 9
    assert before['global_mask_ledger'] == after['global_mask_ledger']
    assert before['original_predicate'] == after['original_predicate']
    dump(ledger, after)
    dump(OUT / 'FIXED_LEDGER_DELTA_AUDIT.json', dict(
        status='PASS_EXACT_ONE_REGISTERED_ORIGINAL_LEDGER_DELTA',
        before_sha256=PRE_REGISTER_SHA, after_sha256=sha(ledger),
        changed_original_ids=changed, all_231_original_definitions_unchanged=True,
        other_230_entries_unchanged=True, before={'closed':221,'open':10,'total':231},
        after={'closed':222,'open':9,'total':231}, mask_ledger={'closed':8,'open':24,'total':32},
        fixed_denominators={'original_cells':231,'masks':32,'positional_roots':7915,'roadmap_gates':15},
        new_original_cells=1, new_masks=0, new_positional_roots=0, new_roadmap_gates=0,
        remaining_open_original_ids=[c['id'] for c in after['cells'] if c['status']=='OPEN'],
        whole_00100_and_reversal_target_remains_strict_radius=True, lean_lake_ci_run=False))

    # Preserve original publication bytes and externally added README/tools.
    history = NATIVE / 'publication_history'
    assert not history.exists()
    history.mkdir(parents=True)
    for name, data in (
        ('ORIGINAL_PUBLICATION_MANIFEST_b6ad19e.json',historical_manifest_bytes),
        ('README_b6ad19e.md',historical_readme),
        ('README_before_portable_acceptance.md',external_readme),
        ('REGISTER_BEFORE_D821.json',before_bytes)):
        (history / name).write_bytes(data)
    current_notice = f'''# Historical native D821 checkpoint; complete portable proof now accepted

The [complete portable release](../{NAME}/README.md) has passed all final
gates and closes D821, advancing the current register to **222 CLOSED /
9 OPEN**. The body below is preserved native-checkpoint history from before
portable acceptance. Its OPEN/221 and pending statements describe that
earlier checkpoint, not the current register.

The original manifest and README, the externally supplemented README and
the pre-acceptance register are retained in `publication_history`. The
updated outer manifest now binds the present README and the externally
added staging tool/tests while preserving every original mathematical file.
The staging tool intentionally requires an OPEN register; historical use
must pass `--ledger publication_history/REGISTER_BEFORE_D821.json` together
with the correctly recovered source root/report/plan/audit arguments.
For reproduction of the accepted proof, use the final portable release.

---

'''
    NATIVE.mkdir(exist_ok=True)
    (NATIVE / 'README.md').write_bytes(current_notice.encode() + external_readme)
    current_files = dict(preserved_core)
    current_files.update(extras)
    current_files['README.md'] = {'bytes':(NATIVE/'README.md').stat().st_size,
                                'sha256':sha(NATIVE/'README.md')}
    for p in sorted(history.iterdir()):
        current_files[str(p.relative_to(NATIVE))] = {'bytes':p.stat().st_size,'sha256':sha(p)}
    repaired = deepcopy(historical_manifest)
    repaired.update(schema='D821_native_checkpoint_with_preserved_history_and_portable_acceptance_v2',
                    status='HISTORICAL_NATIVE_CHECKPOINT_FINAL_PORTABLE_RELEASE_ACCEPTED',
                    all_preexisting_checkpoint_ledger_fields_are_historical=True,
                    original_publication_commit=NATIVE_COMMIT,
                    original_publication_manifest_sha256=digest(historical_manifest_bytes),
                    external_supplement_source_commit=head,
                    final_portable_publication=NAME+'_manifest.json',
                    current_original_status='CLOSED',
                    current_register_sha256=sha(ledger),
                    current_original_ledger={'closed':222,'open':9,'total':231},
                    historical_readme_and_manifest_preserved=True,
                    all_15_original_non_readme_files_unchanged=True,
                    files=current_files)
    dump(CA / (NATIVE_NAME + '_manifest.json'), repaired)
    dump(OUT / 'NATIVE_CHECKPOINT_HISTORY_RECONCILIATION.json', dict(
        status='PASS_PRESERVED_NATIVE_AND_EXTERNAL_SUPPLEMENTS_WITH_CURRENT_OUTER_HASHES',
        original_publication_commit=NATIVE_COMMIT, external_supplement_source_commit=head,
        original_manifest_sha256=digest(historical_manifest_bytes),
        original_readme_sha256=digest(historical_readme),
        external_readme_sha256=digest(external_readme),
        preacceptance_handoff_sha256=digest(handoff_before),
        full_external_handoff_preserved='HANDOFF_BEFORE_D821_ACCEPTANCE.md',
        unchanged_original_mathematical_files=preserved_core, unchanged_external_tools=extras,
        current_outer_manifest_sha256=sha(CA/(NATIVE_NAME+'_manifest.json')),
        historical_open_register_sha256=PRE_REGISTER_SHA,
        current_register_sha256=sha(ledger), frozen_portable_input_manifest_unchanged=True))

    section = '''## Complete D821 original: 222 CLOSED / 9 OPEN

`positive-821c9a2debeed0aa` is completely excluded. Its five closed
complementary domains retain all threshold faces; four close through
46 grafted trees with 650 nodes and 415 excluded terminals, and the fifth
has a direct exact exclusion. All nine original squares, 36 corners,
36 physical pairs, five cones and exact marked conditions remain active.

Native and isolated portable replay check the full assembly and freshly
replay the actual-AB scalar theorem. The tree arithmetic contains 789
rounds, 109,838 deductions and 288,271 row occurrences. Root independently
checks the complete table, all 242 affine terminal sums, every compressed
part and all 2,436 archive members. All 2,432 frozen inputs are unchanged.
The whole-mask ledger remains **8 CLOSED / 24 OPEN**. Eventual 001/00 and
100/00 assembly remains strict-radius.

'''
    p = NINE / 'PROGRESS.md'; text = p.read_text()
    text = once(text,'**221/231 cells CLOSED, 10 OPEN; 8/32 masks CLOSED, 24 OPEN.**',
                '**222/231 cells CLOSED, 9 OPEN; 8/32 masks CLOSED, 24 OPEN.**')
    text = once(text,'close D6c5 and B340.','close D6c5, B340 and D821.')
    text = once(text,'# n=9: 221/231 current-mask cells closed; 10 remain OPEN',
                '# n=9: 222/231 current-mask cells closed; 9 remain OPEN')
    start = text.index('**Latest accepted closure:')
    end = text.index('## A-c744 complete component 1:')
    text = text[:start] + f'''**Latest accepted closure: the complete D821 original-cell exclusion.**
The same register now has **222 CLOSED / 9 OPEN**, with
**169 additions beyond the first 53**. Remaining families: **A1, B5, C3, D0**.
`001/00`, its reversal, the unrestricted bound and equality remain OPEN.
The whole-mask target remains strict-radius. No Lean, Lake or CI.

[Latest complete assembly]({closure_path.name}) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Source-bound packet and fresh portable replay](computer_assisted/{NAME}_manifest.json) ·
[Operative handoff](HANDOFF_A2_FIXED_CLOSURE.md)

'''+section+text[end:]
    text = once(text,'original or mask is newly closed. Counts remain **221 CLOSED / 10 OPEN**',
                'original or mask was newly closed at this checkpoint. Counts then remained **221 CLOSED / 10 OPEN**')
    start = text.index('## D821 complete native proof; portable acceptance pending')
    end = text.index('## Complete B340 original:', start)
    text = text[:start] + '''## Earlier D821 native checkpoint

The [native checkpoint](computer_assisted/a2_00100_d821_complete_native_checkpoint_v1/README.md)
preserves the first complete native proof, full literal table and subsequent
external byte-staging tools. Its original 221/10 OPEN-state metadata is
explicitly historical. The final portable release above now passes the
remaining gates and accepts the same whole original once.

''' + text[end:]
    text = once(text,'## Complete B340 original:','## Earlier complete B340 original:')
    text = once(text,'| Current `001/00` fixed cells | 197 | 34 |',
                '| Current `001/00` fixed cells | 222 | 9 |')
    text = once(text,'handles `|y_D-y_C|<=2/3`. All 34 remaining original cells belong to the',
                'handles `|y_D-y_C|<=2/3`. All 9 remaining original cells belong to the')
    text = once(text,'| Fixed family | Original OPEN baseline | Closed since baseline | Current OPEN |',
                'The following table preserves the historical 197/34 checkpoint. The current\nregister is 222/9, with A1/B5/C3/D0 remaining.\n\n| Fixed family | Original OPEN baseline | Closed since baseline | OPEN at that checkpoint |')
    p.write_text(text)
    p = NINE / 'HANDOFF_A2_FIXED_CLOSURE.md'; text = p.read_text()
    text = once(text,'# Current A.2 handoff: 221/231 current-mask cells closed; 10 OPEN',
                '# Current A.2 handoff: 222/231 current-mask cells closed; 9 OPEN')
    text = once(text,'November 4, 2026. The [complete B340 proof](A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md) advances\nthe unchanged original register from **220 CLOSED / 11 OPEN to 221 CLOSED / 10 OPEN**.',
                'November 4, 2026. The [complete D821 proof](A2_00100_D821_COMPLETE_ORIGINAL_CLOSURE.md) advances\nthe unchanged original register from **221 CLOSED / 10 OPEN to 222 CLOSED / 9 OPEN**.')
    text = once(text,'## Read first\n\n','## Read first\n\n'+section)
    external_title = '## 4 November continuation: D821 portable-source staging (no new closure)'
    if external_title in text:
        start = text.index(external_title)
        end = text.index('November 4, 2026. The [complete D821 proof]', start)
        text = text[:start] + f'''## D821 source restoration and portable acceptance completed

The earlier external continuation correctly required real source bytes,
an isolated exact replay and complete archive verification before closure.
Those gates now pass. All 2,432 portable inputs are present and rehashed;
the entire native/cold mathematical reports agree after explicit filename
normalization. The externally added staging tool and its tests remain
unchanged at the [native checkpoint](computer_assisted/{NATIVE_NAME}/README.md).
The full pre-acceptance handoff, including that continuation's scope and
source-availability statements, is preserved byte-for-byte in
[its historical snapshot](computer_assisted/{NAME}/HANDOFF_BEFORE_D821_ACCEPTANCE.md).
The live fixed register uses its existing `CLOSED` status and counts exactly
this one whole original. No mask or broader target scope changes.

''' + text[end:]
    text = once(text,'zero additional closure credit. Current counts remain **221/231 cells** and',
                'zero additional closure credit. At that review, counts remained **221/231 cells** and')
    text = text.replace('## Latest complete original: B340','## Earlier complete original: B340')
    text = text.replace('complete original-cell proofs now give **221/10 cells and 8/24 masks**.',
                        'complete original-cell proofs now give **222/9 cells and 8/24 masks**.')
    text = once(text,'- Current mask: **221 CLOSED / 10 OPEN**, same 231 IDs and certified full cover.',
                '- Current mask: **222 CLOSED / 9 OPEN**, same 231 IDs and certified full cover.')
    text = text.replace('10 original predicates or a theorem subsuming them, followed by the other',
                        '9 original predicates or a theorem subsuming them, followed by the other')
    start = text.index('## Remaining original cells')
    end = text.index('\n## ', start + 1)
    remaining = '''## Remaining original cells

| Existing family | Original OPEN baseline after first 53 proofs | Subsequently CLOSED | Still OPEN |
|---|---:|---:|---:|
| A: positive D, nonpositive A, inward-row escapes | 77 | 76 | 1 |
| B: negative D, nonpositive A, F-height branches | 39 | 34 | 5 |
| C: negative D, nonnegative A, alternate-chain escapes | 33 | 30 | 3 |
| D: positive D, nonnegative A, alternate-chain escapes | 29 | 29 | 0 |
| **Total** | **178** | **169** | **9** |

The precise unresolved predicates are the unchanged paths of these IDs:

- **A:** `positive-c744bc031d40ee64`.
- **B:** `negative-f14f5bc4eafdf50d`, `negative-7c60be8b07a358e9`, `negative-462e78d2e2d8be05`, `negative-16a2fc93c8d133f0`, `negative-580db3624cf4c2e2`.
- **C:** `negative-887236b78100baf3`, `negative-d4021ade840b985c`, `negative-b882d8ade0cf9ea0`.
- **D:** none; the last whole original D821 is now accepted.
'''
    assert all(c['id'] in remaining for c in after['cells'] if c['status']=='OPEN')
    assert 'negative-34029ea8b047982f' not in remaining and ID not in remaining
    text = text[:start] + remaining + text[end:]
    start = text.index('## D821 complete native proof; portable acceptance pending')
    end = text.find('\n## ', start + 1)
    if end < 0:
        end = len(text)
    text = text[:start] + f'''## Earlier D821 native checkpoint and final acceptance

The [native proof checkpoint](computer_assisted/{NATIVE_NAME}/README.md)
and externally added staging tools are preserved with explicit historical
metadata. The [complete portable release](computer_assisted/{NAME}/README.md)
now passes native/cold proof replay, full hand/table review and every
archive gate. D821 is CLOSED in the unchanged fixed-original definition.
The register is **222 CLOSED / 9 OPEN**; the mask ledger is **8 CLOSED /
24 OPEN**. The eventual full-mask conclusion remains strict-radius.
''' + text[end:]
    p.write_text(text)

    manifest = dict(
        schema='complete_registered_D821_original_source_bound_publication_v1',
        status='ACCEPTED_COMPLETE_ORIGINAL_PHYSICAL_EXCLUSION', original_id=ID,
        original_path=ORIGINAL_PATH, target_mask='001/00', target_Q='1105/256',
        new_original_cells=1, new_masks=0, new_positional_roots=0, new_roadmap_gates=0,
        original_before={'closed':221,'open':10,'total':231},
        original_after={'closed':222,'open':9,'total':231},
        mask_ledger={'closed':8,'open':24,'total':32},
        remaining_original_families={'A':1,'B':5,'C':3,'D':0},
        fixed_denominators={'original_cells':231,'masks':32,'positional_roots':7915,'roadmap_gates':15},
        all_nine_original_frames_retained=True, original_corners=36, original_pairs=36,
        original_cone_comparisons=5, original_actual_links=['AB','BC','EF','FG'],
        original_strict_weak_link='CD', complete_complement_domains=5,
        tree_counts={k:table_audit[k] for k in ('trees','nodes','grafts','rounds','deductions','premise_rows','terminal_rows','checked_row_occurrences')},
        tree_terminal_kinds=table_audit['exclusions_by_kind'], complete_unions=table_audit['closed_unions'],
        additional_direct_component_exclusions=1, historical_references_not_added_to_proof_counts=True,
        fresh_portable_receipt=receipt, proof_archive=ready,
        closure_hand=closure_path.name, closure_hand_sha256=sha(closure_path),
        fixed_register_sha256=sha(ledger), all_231_original_definitions_unchanged=True,
        other_230_original_entries_unchanged=True,
        whole_00100_and_reversal_target_remains_strict_radius=True,
        preparation_source_commit=head,
        published_files={p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(OUT.iterdir()) if p.is_file()},
        lean_lake_ci_run=False)
    final_manifest = CA / (NAME + '_manifest.json')
    assert not final_manifest.exists()
    dump(final_manifest, manifest)
    assert sha(PACKET/'INPUT_MANIFEST.json') == receipt['packet_manifest_sha256']
    print(json.dumps(dict(status='D821_COMPLETE_PUBLICATION_PREPARED',
        manifest=str(final_manifest), manifest_sha256=sha(final_manifest),
        outer_files=len(manifest['published_files']), closed=222, open=9,
        changed_ids=changed, current_register_sha256=sha(ledger),
        original_preparation_head=head)), flush=True)


if __name__ == '__main__':
    main()
