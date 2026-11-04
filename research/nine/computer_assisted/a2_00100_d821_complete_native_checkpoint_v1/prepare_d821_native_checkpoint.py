"""Preserve native D821 arithmetic and table review without ledger promotion."""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parent.parent
NINE = ROOT / 'repo/research/nine'
BASE = ROOT / 'global_work/d821_work'
OUT = NINE / 'computer_assisted/a2_00100_d821_complete_native_checkpoint_v1'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def copy(path):
    target = OUT / path.name
    assert not target.exists()
    shutil.copyfile(path, target)
    assert sha(path) == sha(target)


def main():
    register = NINE / 'gates/A2_00100_FIXED_FRONTIER.json'
    before = sha(register)
    assert before == 'b805df8706151a4eb43bd8c0912205ffbfd67d8dfb582daf441717e04fd023dc'
    fixed = json.loads(register.read_text())
    assert fixed['closed_cells'] == 221 and fixed['open_cells'] == 10
    cell = next(c for c in fixed['cells'] if c['id'] == 'positive-821c9a2debeed0aa')
    assert cell['status'] == 'OPEN'
    report = json.loads((BASE / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json').read_text())
    audit = json.loads((ROOT / 'd_work/D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json').read_text())
    assert report['status'] == 'PASS_COMPLETE_ORIGINAL_CELL' and report['whole_original_proved'] is True
    assert audit['report_sha256'] == sha(BASE / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json')
    assert audit['trees'] == 46 and audit['nodes'] == 650
    assert len(audit['independent_affine_terminal_sums']) == 242
    assert not OUT.exists()
    OUT.mkdir()
    sources = [
        BASE / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json',
        BASE / 'complete_original_final_plan/D821_COMPLETE_ORIGINAL_GRAFT_PLAN.json',
        BASE / 'complete_literal_terminal_table/COMPLETE_TERMINAL_TABLE.json',
        BASE / 'complete_literal_terminal_table/COMPLETE_TERMINAL_TABLE.md',
        BASE / 'complete_checkpoint_provenance/PRESERVED_CHECKPOINT_INDEX.json',
        BASE / 'complete_checkpoint_provenance/PRESERVED_CHECKPOINT_INDEX.md',
        BASE / 'D821_COMPLETE_ASSEMBLY_HAND_PROOF.md',
        BASE / 'verify_D821_grafted_original.py',
        BASE / 'render_d821_complete_terminal_table.py',
        ROOT / 'd_work/D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json',
        ROOT / 'd_work/audit_d821_complete_table_root.py',
        ROOT / 'd_work/D821_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md',
        ROOT / 'd_work/D821_REGISTERED_PATH_LITERAL_ROOT_REVIEW.json',
        ROOT / 'd_work/review_d821_registered_path_attachment.py',
        Path(__file__).resolve(),
    ]
    for source in sources:
        copy(source)
    (OUT / 'README.md').write_text('''# D821 complete native proof and literal-table checkpoint

The native independent checker has excluded all five closed complementary
domains of registered original `positive-821c9a2debeed0aa` in mask `001/00`.
Its result is `PASS_COMPLETE_ORIGINAL_CELL`. This checkpoint preserves that
exact report, complete graft plan, mathematical assembly argument, original
physical attachment, literal table, and independent root table audit.

**The accepted fixed register is unchanged: 221 CLOSED / 10 OPEN originals,
8 CLOSED / 24 OPEN masks.** D821 remains OPEN there until the final portable
arithmetic replay and complete archive-member audit pass. This checkpoint
does not include the full compressed proof-input payload; the final portable
publication will provide it. Paths and hashes in the native report identify
the frozen source records, rather than claiming those records are all shipped
in this small intermediate checkpoint.

## Complete original-domain argument

The proof starts with the unchanged registered path and reconstructs all nine
original squares, 36 original corners, 36 physical pairs, five center cones,
actual AB/BC/EF/FG and strictly weak CD. Four exact root rounds prove the
physical premises needed by the accepted actual-AB two-link theorem. Its
28-domain scalar proof, 103 rational leaves and 12,875 coefficient checks are
freshly repeated by the complete-original checker. The caller's strict-CD
equality blocker excludes the closed-Q equality face.

The five complementary domains are all closed and retain every threshold
face. One pilot directly excludes component 2. The other four components
close through 46 complete grafted trees with 650 literal nodes and 42 grafts.
All 79 proxy unions, ten physical owned-axis unions and 104 slope unions retain
their complete four, eight and two alternatives respectively. Every originally
OPEN leaf is either excluded or continued exactly once by the complete graph.

Across these 46 tree reports the fresh exact replay checks 789 rounds,
109,838 deductions and 288,271 row occurrences: 281,916 bound-premise rows plus
6,355 affine-terminal rows. These totals describe the tree reports only;
the original root, five pilots, scalar theorem and repeated dependency proofs
remain separately present in the native report and are not silently folded
into those counts.

## Independent literal-table review

Root compared every table entry with its hash-bound raw node, every native
node audit, every complete child-choice set and every child initial state.
The five-component graft graph reaches every one of the 650 nodes exactly
once and has no omitted terminal or dangling continuation. Root independently
recomputed all 242 affine terminal sums and their positive exact reserves
with Fraction arithmetic, including every residual correction and displayed
dyadic reserve lower bound. Geometric reconstruction of every premise remains
the responsibility of the separate fresh native and portable exact checkers.

The 415 terminal exclusions comprise 242 positive exact reserves, 107 accepted
interval terminals, 13 empty analytic frames, 11 frame contradictions,
38 early center-interval contradictions and four early difference-interval
contradictions. They are conditional terminal domains, not extra originals.

Two retained pre-migration snapshots add 64 historical records to the storage
reference graph. The separate preservation index checks all 216 recorded
round prefixes and 46 unchanged old closed payloads inside their final
continuations. These snapshots are provenance, not additional arithmetic
trees or additional closure credit.

## Remaining acceptance work

The final packet must freeze the full required source graph, rerun the strict
complete-original checker with old-workspace reads and numerical imports
forbidden, preserve all hashes, and pass a full archive-member audit. Only
then may one original status change. This checkpoint changes none of the
fixed denominators: 231 originals, 32 masks, 7,915 positional roots and
15 roadmap IDs. No Lean, Lake or CI was run.
''')
    section = '''## D821 complete native proof; portable acceptance pending

The [native proof and complete literal-table checkpoint](computer_assisted/a2_00100_d821_complete_native_checkpoint_v1/README.md)
excludes all five complementary domains of `positive-821c9a2debeed0aa` in
fresh independent exact replay. Its 46 grafted trees have 650 nodes and
415 excluded terminal domains. The tree reports check 109,838 deductions
and 288,271 row occurrences. Root independently checks every table entry,
every closed child choice and all 242 affine terminal sums. The original
nine-square attachment and two preserved migration snapshots are explicit.

The final isolated portable replay and complete compressed-payload audit
remain acceptance gates. D821 stays OPEN in the unchanged fixed register;
this intermediate commit adds **zero original-cell or mask credit**.
Accepted counts remain **221 CLOSED / 10 OPEN** and **8 CLOSED / 24 OPEN**.

'''
    handoff = NINE / 'HANDOFF_A2_FIXED_CLOSURE.md'
    text = handoff.read_text()
    marker = '## Fixed ledgers and next handoff\n'
    assert text.count(marker) == 1
    handoff.write_text(text.replace(marker, section + marker))
    progress = NINE / 'PROGRESS.md'
    text = progress.read_text()
    text = text.replace('**Latest verified continuation: the complete B340 original-cell exclusion.**',
                        '**Latest accepted closure: the complete B340 original-cell exclusion.**')
    marker = '## Complete B340 original: 221 CLOSED / 10 OPEN\n'
    assert text.count(marker) == 1
    progress.write_text(text.replace(marker, section + marker))
    assert sha(register) == before
    manifest = dict(schema='D821_complete_native_proof_checkpoint_v1',
        status='NATIVE_COMPLETE_ORIGINAL_EXACT_REPLAY_AND_LITERAL_TABLE_VERIFIED',
        original_id=cell['id'], original_path=cell['path'], mask='001/00',
        native_complete_original_proved=True, portable_final_replay_pending=True,
        complete_input_archive_not_in_this_intermediate_checkpoint=True,
        fixed_original_status_retained='OPEN', new_original_cells=0, new_masks=0,
        original_ledger=dict(closed=221, open=10, total=231),
        mask_ledger=dict(closed=8, open=24, total=32),
        fixed_register_sha256=before, fixed_register_source_commit='f060c3811465e35592cc5f191e45924178287f48',
        native_report_sha256=sha(OUT / 'D821_COMPLETE_ORIGINAL_EXACT_REPLAY.json'),
        root_table_audit_sha256=sha(OUT / 'D821_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json'),
        files={p.name:dict(bytes=p.stat().st_size, sha256=sha(p)) for p in sorted(OUT.iterdir())},
        lean_lake_ci_run=False)
    target = OUT.with_name(OUT.name + '_manifest.json')
    assert not target.exists()
    target.write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(dict(status='PREPARED_D821_NATIVE_ZERO_CREDIT_CHECKPOINT',
        files=len(manifest['files']), bytes=sum(x['bytes'] for x in manifest['files'].values()),
        publication_manifest_sha256=sha(target), fixed_register_unchanged=True)), flush=True)


if __name__ == '__main__':
    main()
