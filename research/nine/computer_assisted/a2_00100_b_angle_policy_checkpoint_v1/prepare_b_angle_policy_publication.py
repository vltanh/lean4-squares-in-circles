#!/usr/bin/env python3
"""Publish two exact conditional unions, keeping all original/mask ledgers fixed."""
from pathlib import Path
import hashlib,json,shutil
R=Path('/workspace/scratch/f9f48fcfb253');N=R/'repo/research/nine'
P=R/'b_work/b_angle_policy_checkpoint';A=R/'b_work/b_angle_policy_checkpoint_archive_v1'
O=N/'computer_assisted/a2_00100_b_angle_policy_checkpoint_v1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def cp(p,name=None):
    p=Path(p);d=O/(name or p.name);shutil.copyfile(p,d);assert sha(p)==sha(d)
assert not O.exists()
fixed=N/'gates/A2_00100_FIXED_FRONTIER.json';fixed_sha=sha(fixed);reg=read(fixed)
assert fixed_sha=='b805df8706151a4eb43bd8c0912205ffbfd67d8dfb582daf441717e04fd023dc'
assert reg['closed_cells']==221 and reg['open_cells']==10
ready=read(A/'ARCHIVE_READY.json');audit=read(R/'d_work/B_ANGLE_POLICY_CHECKPOINT_ROOT_AUDIT.json')
assert audit['status']=='PASS_ROOT_TWO_CONDITIONAL_B_UNIONS_SOURCE_TABLE_AND_ARCHIVE_AUDIT'
assert audit['archive_sha256']==ready['archive_sha256']
header=read(R/'b_work/B_ANGLE_POLICY_HEADER_CONSISTENCY.json')
assert header['status']=='PASS_TWO_UNION_NATIVE_REPORT_HEADER_CONSISTENCY'
O.mkdir()
for x in ready['parts']:cp(A/x['file'])
cp(A/'ARCHIVE_READY.json')
for name in ['README.md','CHECKPOINT.json','INPUT_MANIFEST.json','RELEASE_MANIFEST.json','PHYSICAL_COMPLETE_COVER_ATTACHMENT.md','TRANSPORT_RECEIPT.json']:
    cp(P/name)
for name in ['B7C_FIRST_FIVE_PROXY_ROUND_ANGLE_EXACT_REPLAY.json','B16A_FIRST_AFTER_ROUND_TWO_ANGLE_EXACT_REPLAY.json']:
    cp(P/'reports'/name)
cp(R/'b_work/B_ANGLE_POLICY_HEADER_CONSISTENCY.json')
cp(R/'b_work/B340_FINAL_PUBLICATION_INDEPENDENT_REVIEW.json')
for name in ['B_TWO_ANGLE_POLICY_CHECKPOINT_INDEPENDENT_REVIEW.md','B_TWO_ANGLE_POLICY_CHECKPOINT_INDEPENDENT_REVIEW.json']:
    cp(R/'ac_work/tree'/name)
cp(R/'d_work/B_ANGLE_POLICY_CHECKPOINT_ROOT_AUDIT.json')
cp(R/'d_work/audit_b_angle_policy_checkpoint.py')
cp(R/'d_work/b_policy_concurrent_review_merge/RECONCILIATION.json','CONCURRENT_REVIEW_RECONCILIATION.json')
cp(__file__)
(O/'ROOT_REVIEW.md').write_text('''# Root acceptance of the two conditional B angle unions

This checkpoint preserves two complete conditional exclusions with native
independent exact replay. Neither proof closes its whole registered original.
The fixed ledgers remain 221 CLOSED / 10 OPEN originals and 8 CLOSED / 24 OPEN
masks. The original 231 definitions and every live status entry are unchanged.

Root read the physical attachment, explicit-engine completed-round helper,
five-proxy split selector, driver call sites and portable transport source.
The new policy changes when discovery chooses an angle split. It adds no
mathematical row or acceptance rule and preserves every completed bound round.
All three helper calls pass the actual runtime engine explicitly.

The B7c case retains 10 selected-branch records. Its complete G-slope cut at 0
has two excluded closed children, with positive exact reserve bounds 1 and
1/1000. The B16a case retains 15 prefix records, including both parent rounds
before the callback. Its complete C-slope cut at 0 has two excluded closed
children with reserve bounds 1/40 each. Every inequality remains attached to
the same original nine-square caller; no unselected alternative is credited.

Root independently checked the native-report hashes and all local count
fields against CHECKPOINT.json, all literal angle endpoints and printed
reserve lower bounds, every archive part, and all 82 regular members against
their unchanged source bytes. The frozen input inventory contains 79 files.
The native reports check 459 and 424 local deductions respectively,
with complete retained ancestry. No weighted arithmetic was repeated for
this packaging audit.

The independent AC source review agrees on conditional scope and closed
coverage. Its suggested report-header consistency checks pass in the outer
header audit; the frozen packet remains unchanged. The default transport
receipt checks hashes and literal covers. The optional --replay mode is
provided for readers and was not exercised for this publication, so no new
cold arithmetic replay is claimed. Its common-directory guard is not
described as a strict inventoried cold-replay sandbox.

Shared code is reused by hash from the published B340 and I32 archives.
Earlier B340 or I32 exclusions are not substituted for these conditional
proofs. The B340 final publication review is also preserved. No Lean, Lake
or CI was run and no fixed ledger is changed by this checkpoint.

Before publication, concurrent commit03fa63eb added a separate independent
B340 review. Its13 inventoried review files were hash-checked, all231
definitions and statuses were compared, and its evidence addition was
preserved. The handoff additions merge cleanly. This checkpoint is based
on that newer commit and retains its full tree without extra closure credit.
''')
handoff=N/'HANDOFF_A2_FIXED_CLOSURE.md';text=handoff.read_text()
marker='## Fixed ledgers and next handoff\n';assert text.count(marker)==1
section='''## Exact conditional B angle unions and revised discovery policy

The [source-bound checkpoint](computer_assisted/a2_00100_b_angle_policy_checkpoint_v1/README.md)
preserves two complete conditional angle unions. In B7c, both closed
G-slope halves are excluded after the five-proxy policy selected the cut.
In B16a, both closed C-slope halves are excluded after the second completed
bound round triggered the callback. The native independent replays retain
all 10 and 15 selected-branch ancestry records and check 459 and 424 local
deductions respectively. Both shared zero faces remain in the covers.

The explicit-engine helper and split policy change discovery timing only.
The full physical attachment, literal reserve bounds, exact reports, peer
review and root 82-member archive audit are preserved. Shared bytes reuse
the published B340 and I32 packets by exact hash. Packaging checks source
transport and literal covers; it does not repeat the already completed
weighted arithmetic. The optional replay entry point is provided without
claiming an additional cold run. This checkpoint adds **zero original-cell
and mask closures**; accepted counts remain **221 CLOSED / 10 OPEN** and
**8 CLOSED / 24 OPEN**.

'''
handoff.write_text(text.replace(marker,section+marker))
assert sha(fixed)==fixed_sha
manifest=dict(schema='two_conditional_B_angle_unions_source_bound_publication_v1',
    status='ACCEPTED_NATIVE_EXACT_CONDITIONAL_PROOFS_AND_SOURCE_TRANSPORT',
    original_ids=['negative-7c60be8b07a358e9','negative-16a2fc93c8d133f0'],
    target_mask='001/00',target_Q='1105/256',new_original_cells=0,new_masks=0,
    whole_original_proved=False,original_ledger=dict(closed=221,open=10,total=231),
    mask_ledger=dict(closed=8,open=24,total=32),fixed_register_sha256=fixed_sha,
    fixed_register_source_commit='03fa63eb45e43913f0b38c5c8a0469bdaeb9e4c7',
    all_register_entries_unchanged=True,mathematical_rule_changes=0,
    native_weighted_arithmetic_replayed=True,weighted_arithmetic_repeated_for_packaging=False,
    cold_optional_arithmetic_mode_exercised=False,archive=ready,
    root_audit_sha256=sha(O/'B_ANGLE_POLICY_CHECKPOINT_ROOT_AUDIT.json'),
    files={p.name:dict(bytes=p.stat().st_size,sha256=sha(p))for p in sorted(O.iterdir())if p.is_file()},
    lean_lake_ci_run=False)
mp=N/'computer_assisted/a2_00100_b_angle_policy_checkpoint_v1_manifest.json';dump(mp,manifest)
print(json.dumps(dict(status='PREPARED_ZERO_CREDIT_B_POLICY_PUBLICATION',files=len(manifest['files']),manifest_sha256=sha(mp),fixed_register_unchanged=True)))
