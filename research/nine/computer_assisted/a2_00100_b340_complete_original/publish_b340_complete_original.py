#!/usr/bin/env python3
"""Prepare the reviewed complete B340 publication; no arithmetic or Git mutation."""
from pathlib import Path
from copy import deepcopy
import hashlib,json,shutil,subprocess

ROOT=Path('/workspace/scratch/f9f48fcfb253')
REPO=ROOT/'repo'
NINE=REPO/'research/nine'
PACKET=ROOT/'b_work/portable_b340_complete_v1/b340_complete_original_package'
FRESH=ROOT/'b_work/portable_b340_complete_v1/fresh_replay'
ARCH=ROOT/'b_work/b340_complete_original_archive_v1'
OUT=NINE/'computer_assisted/a2_00100_b340_complete_original'
ID='negative-34029ea8b047982f'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text())
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def copy(src,name=None):
    src=Path(src);dst=OUT/(name or src.name)
    shutil.copyfile(src,dst);assert sha(src)==sha(dst)
    return dst
def replace_once(text,old,new):
    assert text.count(old)==1,(old,text.count(old))
    return text.replace(old,new,1)

assert not OUT.exists()
ready=read(ARCH/'ARCHIVE_READY.json')
archive_audit=read(ROOT/'d_work/B340_COMPLETE_ROOT_ARCHIVE_AUDIT.json')
table_audit=read(ROOT/'d_work/B340_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json')
native=read(ROOT/'b_work/B340_COMPLETE_ORIGINAL_FOUR_CORNER_EXACT_REPLAY.json')
fresh=read(FRESH/'COMPLETE_ORIGINAL_REPLAY.json')
receipt=read(FRESH/'PORTABLE_RECEIPT.json')
proof=read(PACKET/'ORIGINAL_PROOF.json')
assert archive_audit['status']=='PASS_ROOT_B340_COMPLETE_ARCHIVE_AND_PART_AUDIT'
assert table_audit['status']=='PASS_B340_COMPLETE_LITERAL_TABLE_AND_ROW_ACCOUNTING'
assert receipt['status']=='PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL'
assert receipt['original_id']==ID and receipt['complete'] and receipt['whole_original_proved']
assert receipt['every_new_bound_and_cover_replayed'] and receipt['all_inputs_rehashed_at_completion']
assert receipt['external_workspace_reads_forbidden'] and not receipt['numerical_modules_imported']
assert ready['archive_sha256']==archive_audit['archive_sha256']
assert sha(FRESH/'COMPLETE_ORIGINAL_REPLAY.json')==receipt['report_sha256']==archive_audit['fresh_complete_report_sha256']
assert sha(FRESH/'PORTABLE_RECEIPT.json')==archive_audit['fresh_portable_receipt_sha256']
assert sha(PACKET/'INPUT_MANIFEST.json')==receipt['packet_manifest_sha256']==archive_audit['input_manifest_sha256']
for report in (native,fresh):
    assert report['status']=='PASS_COMPLETE_ORIGINAL_PHYSICAL_TREE'
    assert report['initial_original_id']==ID and report['complete'] and report['whole_original_proved']
    assert report['nodes']==403 and report['terminal_leaves']==report['excluded_leaves']==279 and report['open_leaves']==0
    assert report['local_rounds']==400 and report['local_deductions']==67336 and report['local_printed_rows']==203189
    assert report['complete_unions']=={'proxy':47,'angle':67,'sat':10}
assert table_audit['totals']=={'rounds':400,'deductions':67336,'premise_rows':199016,'terminal_rows':4173}
assert table_audit['all_printed_terminal_reserve_lower_bounds_valid']
prior_git_bytes=subprocess.check_output(['git','show','HEAD:research/nine/computer_assisted/a2_00100_b16a_I32_complete_H_manifest.json'],cwd=REPO)
assert hashlib.sha256(prior_git_bytes).hexdigest()==sha(PACKET/'PUBLISHED_PRIOR.json')

ledger=NINE/'gates/A2_00100_FIXED_FRONTIER.json'
before=read(ledger);before_sha=sha(ledger)
assert before_sha=='37bcd835ed57cb5c9656234a9ca0d4678da655d43e556e58ecc196d187d5a256'
assert (before['closed_cells'],before['open_cells'],len(before['cells']))==(220,11,231)
cell=next(c for c in before['cells'] if c['id']==ID)
assert cell['status']=='OPEN' and cell['path']==proof['original_path']==fresh['initial_path']
assert proof['current_definition_attachment']['all_231_original_definitions_unchanged']

OUT.mkdir()
for entry in ready['parts']:
    p=ARCH/entry['file'];assert p.stat().st_size==entry['bytes'] and sha(p)==entry['sha256'];copy(p)
copy(ARCH/'ARCHIVE_READY.json')
for name in ('RELEASE_MANIFEST.json','INPUT_MANIFEST.json','PUBLISHED_PRIOR.json','ORIGINAL_PROOF.json','PACKAGING_ATTACHMENTS.json','COMPLETE_TERMINAL_TABLE.md','B340_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md'):
    copy(PACKET/name)
copy(ROOT/'b_work/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md')
copy(ROOT/'b_work/B340_COMPLETE_ORIGINAL_FOUR_CORNER_EXACT_REPLAY.json','NATIVE_COMPLETE_ORIGINAL_REPLAY.json')
copy(FRESH/'COMPLETE_ORIGINAL_REPLAY.json')
copy(FRESH/'PORTABLE_RECEIPT.json')
for name in ('B340_NATIVE_PHYSICAL_AND_SOURCE_ROOT_REVIEW.md','B340_COMPLETE_LITERAL_TABLE_ROOT_AUDIT.json','B340_COMPLETE_ROOT_ARCHIVE_AUDIT.json','audit_b340_literal_table.py','audit_b340_complete_archive.py'):
    copy(ROOT/'d_work'/name)
copy(ROOT/'b_work/archive_registered_b_packet_streaming.py')
copy(Path(__file__))

root_review='''# Final root acceptance of the complete B340 original

The complete proof excludes `negative-34029ea8b047982f`, baseline negative
index 66, with the exact four-entry path retained in `ORIGINAL_PROOF.json`.
The native replay, fresh portable replay, literal terminal-table audit and
full compressed-archive audit all pass. This accepts one entire original
cell, advancing the fixed register from 220 CLOSED / 11 OPEN to 221 CLOSED /
10 OPEN. The whole-mask ledger remains 8 CLOSED / 24 OPEN.

## Mathematical attachment

The root is the independently reconstructed registered original, at SHA256
`d7663ff3b35a6a08062695af46494ad85e1632d94d1cc1bb25d59198c89c1019`.
The root review checked the original path against the frozen definition and
read the literal F/H side-escape implementation. All nine original unit
squares, their 36 corners and 36 physical pairs, all five cones, actual
AB/BC/EF/FG and strict weak CD are retained. The four center inequalities
in the physical attachment include both earlier closed complements.

The complete finite tree has 403 nodes and 279 excluded terminal domains.
Its 47 four-member inset covers, 10 eight-member physical separating covers
and 67 two-member closed slope covers retain every alternative. Exact bound
induction reconstructs the weighted physical premises and pays every
coefficient residual. No numerical infeasibility claim is an accepted leaf.
There are no sharp, full-angle, actual-AB-extra or opposite-row terminals in
this instance. The generic hand proof explains available theorem families;
it does not assert they are all used here.

## Literal table and counts

The independent table audit matches every one of the 279 entries to its
frozen node record and independently checks every displayed positive reserve
lower bound against the exact recorded reserve. There are 181 positive-reserve
terminals, 71 accepted center-interval terminals, 14 effective-angle terminals,
10 empty analytic-frame terminals and three frame contradictions.

The 400 bound rounds contain 67,336 deductions. The total 203,189 printed-row
occurrences comprises **199,016 premise rows and 4,173 terminal rows**.
The earlier native review's phrase "203,189 printed premise rows" refers to
this combined total; this final accounting supplies the precise split.
All literal coefficients and rational multipliers remain in the archive,
and the table audit retains per-node counts. Row-name prefix counts in that
audit are literal identifier counts, not newly asserted geometric categories.

## Independent portable replay and archive

The cold replay freshly reconstructs all new bound and cover arithmetic,
checks the registered whole-original attachment, compares all 231 ID/sign/
index/path definitions and rehashes 726 new inputs plus 507 pinned prior
inputs. Old-workspace reads are forbidden and no numerical module is imported.
The archived status-register snapshot deliberately records B340 as OPEN
before acceptance; it is not a replacement for the updated live ledger.

The final 53,274,488-byte archive has SHA256
`b4b3db56da2b3ac7a006d8c8e1060d07e4ab0103070fdce88c7611c74744569f`.
Root independently checked all seven ordered parts, their concatenated
digest, all 730 regular members and the unchanged source packet bytes.
The packaging attachment names the original archiver entry point. Actual
compression used the included immutable streaming version at SHA256
`d47b36d2084628d2b784e6e19d0337e8368a70676c4d7bf6cb06ce3a3918649d`,
which streams tar into xz and creates no raw tar intermediate. It changes
packaging only; frozen proof inputs and their manifest are unchanged.

The two root audits check literal accounting and transport; they do not
claim another independent repetition of all weighted arithmetic. That
arithmetic is supplied by the native exact replay and the cold exact replay.
No Lean compilation, Lake or CI ran. No proof-kernel or human verification
is claimed. Only the named complete original receives ledger credit.
'''
(OUT/'ROOT_FINAL_ACCEPTANCE.md').write_text(root_review)

closure='''# Complete B340 original: 221 CLOSED / 10 OPEN

The unchanged original `negative-34029ea8b047982f` is completely excluded.
Its independently reconstructed initial domain is covered by a finite
403-node tree with **279 excluded leaves and zero OPEN leaves**. Native exact
replay, fresh portable exact replay, the complete hand/table review and the
full archive audit pass. The fixed 231-original register advances from
**220 CLOSED / 11 OPEN to 221 CLOSED / 10 OPEN**. Remaining families are
**A1, B5, C3, D1**. The mask ledger stays **8 CLOSED / 24 OPEN**.

## Exact physical caller

This is negative baseline frontier index 66. Its path is

```json
[["angle",3,0],["angle_cut",[0,"0"],0],
 ["position_cut",[11,"1/2"],1],["f_side_escape",[5,7],[2]]]
```

For the original frame slopes this retains `t_D,t_A in [-1,0]` and
`y_F >= 1/2`. The selected F/H escape and its earlier closed complements are

\[
x_H-x_F\le0,\qquad y_A-2y_H+y_F\le-3/5,\qquad
y_A-y_F\le3/5,\qquad y_A-2y_H+y_F\le3/5.
\]

The last inequality is redundant and remains present in the literal caller.
All nine physical unit squares A through I, their 36 original corners and
36 pair-disjointness conditions, five center cones, actual AB/BC/EF/FG and
strict weak CD remain unchanged. Every original corner lies in the closed
disk of squared radius `Q=1105/256`.

The [physical attachment](computer_assisted/a2_00100_b340_complete_original/B340_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md)
defines the exact original, and the [generic hand proof](computer_assisted/a2_00100_b340_complete_original/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md)
derives the weighted-row and finite-cover rules. Insets and product variables
express necessary consequences of the same original squares.

## Complete proof

The independent checker reconstructs every weighted row from certified
original intervals, verifies nonnegative rational multipliers and pays every
coefficient residual. A positive exact contradiction reserve, or a separately
checked interval/frame contradiction, excludes its domain. Every internal
node retains its entire physical cover, including shared faces.

| Exact proof item | Count |
| --- | ---: |
| Node records | 403 |
| Complete four-way inset covers | 47 |
| Complete eight-way physical separating covers | 10 |
| Complete two-way closed slope covers | 67 |
| Excluded terminal domains | 279 |
| OPEN terminal domains | 0 |
| Bound rounds | 400 |
| Rational bound deductions | 67,336 |
| Premise-row occurrences | 199,016 |
| Terminal-row occurrences | 4,173 |

The [complete terminal table](computer_assisted/a2_00100_b340_complete_original/COMPLETE_TERMINAL_TABLE.md)
lists all 279 leaves: 181 positive exact reserves, 71 center-interval
terminals, 14 effective-angle terminals, 10 empty analytic-frame terminals
and three frame contradictions. Every coefficient and multiplier appears
in its archived literal record. No sharp or full-angle terminal is needed
in this instance. Induction over all complete covers excludes the root,
which is the entire registered original rather than a restricted descendant.

## Replay, source identity and reproducibility

The [publication manifest](computer_assisted/a2_00100_b340_complete_original_manifest.json)
binds the original definition, complete tree, hand proof, reports, terminal
table, archive parts, and exact one-cell ledger delta. The
[final root review](computer_assisted/a2_00100_b340_complete_original/ROOT_FINAL_ACCEPTANCE.md)
explains the physical attachment, arithmetic/table distinction and archive
checks. The native and cold replays both reconstruct every new bound and
cover. The cold run reads only the portable packet and its pinned published
prior, uses standard-library exact arithmetic, and imports no optimizer.
All 726 new and 507 prior input files are rehashed at completion.

The new archive is 53,274,488 bytes in seven ordered parts, SHA256
`b4b3db56da2b3ac7a006d8c8e1060d07e4ab0103070fdce88c7611c74744569f`.
Root independently verifies every part and all 730 regular archive members.
The prior is the already published
[I32 dependency manifest](computer_assisted/a2_00100_b16a_I32_complete_H_manifest.json),
archive SHA256 `c6e8dfc170a3d88366a6cd6f0955302ca5f664c626790ca91387f84c42502cb6`.
Its mathematical B16a scope is not borrowed as a B340 exclusion; its frozen
shared code and original-definition inputs are reused by the new full replay.

To reproduce, concatenate the seven new parts in `ARCHIVE_READY.json` order
and the seven prior parts in `PUBLISHED_PRIOR.json` order. Check both archive
hashes, then extract both inside one dedicated directory. Run the extracted
new packet's entry point, using a fresh output directory:

```sh
python3 -B b340_complete_original_package/code/replay_registered_b_four_lazy_packet.py \\
  --prior b16a_I32_complete_H_checkpoint --output fresh_b340_replay
```

The required receipt status is
`PASS_FRESH_PORTABLE_COMPLETE_REGISTERED_B_ORIGINAL`, with `complete=true`
and `whole_original_proved=true`. The source-bound register snapshot records
the pre-acceptance OPEN status intentionally; the live fixed register carries
the subsequently accepted closure.

## Fixed accounting

Exactly B340 changes from OPEN to CLOSED. All 231 ID/sign/index/path tuples
and the other 230 entries are unchanged. The same 32 mask IDs, 7,915
positional-root IDs and 15 roadmap IDs remain fixed. No whole mask,
positional root or roadmap gate closes here. `001/00`, its reversal and the
unrestricted bound/equality obligations remain OPEN. No Lean, Lake or CI ran.
'''
closure_path=NINE/'A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md'
closure_path.write_text(closure)

after=deepcopy(before)
after.update(assembly='../A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md',cell_review='../A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md',manifest='../computer_assisted/a2_00100_b340_complete_original_manifest.json',closed_cells=221,open_cells=10,cumulative_new_closed_since_53=168,latest_new_closed_cells=1,preceding_assembly=before['assembly'],preceding_manifest=before['manifest'])
c=next(c for c in after['cells'] if c['id']==ID)
c.update(status='CLOSED',method='complete_registered_original_physical_tree_with_exact_four_product_corner_rows',terminal_leaves=279)
c['evidence']={
    'method':c['method'],'record_id':ID,'whole_cell_exclusion':True,
    'complete_closed_face_cover':True,'all_original_physical_conditions_retained':True,
    'original_initial_state_sha256':fresh['parent_certificate_sha256'],
    'tree_manifest_sha256':fresh['certificate_sha256'],
    'archive_parts_manifest':'a2_00100_b340_complete_original/ARCHIVE_READY.json',
    'archive_sha256':ready['archive_sha256'],'archive_bytes':ready['archive_bytes'],
    'prior_archive_sha256':ready['prior_archive_sha256'],
    'certificate':'a2_00100_b340_complete_original/COMPLETE_ORIGINAL_REPLAY.json',
    'certificate_sha256':sha(OUT/'COMPLETE_ORIGINAL_REPLAY.json'),
    'native_report_sha256':sha(OUT/'NATIVE_COMPLETE_ORIGINAL_REPLAY.json'),
    'independent_checker':'replay_registered_b_four_lazy_packet.py',
    'independent_checker_sha256':sha(ROOT/'b_work/replay_registered_b_four_lazy_packet.py'),
    'independent_report':'a2_00100_b340_complete_original/PORTABLE_RECEIPT.json',
    'independent_report_sha256':sha(OUT/'PORTABLE_RECEIPT.json'),
    'root_hand_table_review':'a2_00100_b340_complete_original/ROOT_FINAL_ACCEPTANCE.md',
    'root_hand_table_review_sha256':sha(OUT/'ROOT_FINAL_ACCEPTANCE.md'),
    'terminal_table_sha256':sha(OUT/'COMPLETE_TERMINAL_TABLE.md'),
    'nodes':403,'terminal_leaves':279,'open_leaves':0,
    'all_new_bound_and_cover_arithmetic_repeated':True,
    'whole_mask_closed':False}
defs=lambda d:[{k:c[k] for k in ('id','sign','baseline_frontier_index','path')}for c in d['cells']]
assert defs(before)==defs(after)
changed=[x['id'] for x,y in zip(before['cells'],after['cells']) if x!=y]
assert changed==[ID]
assert sum(c['status']=='CLOSED' for c in after['cells'])==221
assert sum(c['status']=='OPEN' for c in after['cells'])==10
assert before['global_mask_ledger']==after['global_mask_ledger']
dump(ledger,after)
dump(OUT/'FIXED_LEDGER_DELTA_AUDIT.json',{
    'status':'PASS_EXACT_ONE_REGISTERED_ORIGINAL_LEDGER_DELTA',
    'before_sha256':before_sha,'after_sha256':sha(ledger),'changed_original_ids':changed,
    'all_231_original_definitions_unchanged':True,'other_230_entries_unchanged':True,
    'before':{'closed':220,'open':11,'total':231},'after':{'closed':221,'open':10,'total':231},
    'mask_ledger':{'closed':8,'open':24,'total':32},
    'new_original_cells':1,'new_masks':0,'new_positional_roots':0,'new_roadmap_gates':0,
    'fixed_denominators':{'original_cells':231,'masks':32,'positional_roots':7915,'roadmap_gates':15},
    'remaining_open_original_ids':[c['id']for c in after['cells']if c['status']=='OPEN'],
    'lean_lake_ci_run':False})

section='''## Complete B340 original: 221 CLOSED / 10 OPEN

`negative-34029ea8b047982f` is completely excluded. Its direct registered
root has a complete 403-node tree with 279 excluded terminal domains and
zero OPEN leaves. All 47 four-way inset covers, ten eight-way physical
separating covers and 67 two-way closed slope covers retain every face.
The proof preserves the same nine originals, 36 corners, 36 physical pairs,
five cones and exact marked conditions.

Native and fresh portable exact replay check 400 rounds, 67,336 rational
deductions and 203,189 printed rows (199,016 premise plus 4,173 terminal
rows). The full hand proof and all 279 literal table entries are reviewed.
The cold replay rehashes 726 new inputs and 507 pinned prior inputs with
old-workspace reads forbidden. Root independently checks every ordered
archive part and all 730 regular members. This closes one entire original;
the whole-mask ledger remains **8 CLOSED / 24 OPEN**.

'''
p=NINE/'PROGRESS.md';t=p.read_text()
t=replace_once(t,'**220/231 cells CLOSED, 11 OPEN; 8/32 masks CLOSED, 24 OPEN.**','**221/231 cells CLOSED, 10 OPEN; 8/32 masks CLOSED, 24 OPEN.**')
t=replace_once(t,'New computer-assisted discovery, exact replays and complete physical assembly now close D6c5. All other open originals remain explicit.','Subsequent computer-assisted discovery, exact replays and complete physical assembly close D6c5 and B340. All other open originals remain explicit.')
t=replace_once(t,'# n=9: 220/231 current-mask cells closed; 11 remain OPEN','# n=9: 221/231 current-mask cells closed; 10 remain OPEN')
start=t.index('**Latest verified continuation:');end=t.index('## Complete D6c5 original:')
t=t[:start]+'''**Latest verified continuation: the complete B340 original-cell exclusion.**
The same register now has **221 CLOSED / 10 OPEN**, with
**168 additions beyond the first 53**. Remaining families:
**A1, B5, C3, D1**. `001/00`, its reversal, the unrestricted bound and
equality remain OPEN. No Lean, Lake or CI.

[Latest complete assembly](A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md) ·
[Current fixed register](gates/A2_00100_FIXED_FRONTIER.json) ·
[Source-bound packet and fresh portable replay](computer_assisted/a2_00100_b340_complete_original_manifest.json) ·
[Operative handoff](HANDOFF_A2_FIXED_CLOSURE.md)

'''+section+t[end:]
t=replace_once(t,'## Complete D6c5 original:','## Earlier complete D6c5 original:')
p.write_text(t)

p=NINE/'HANDOFF_A2_FIXED_CLOSURE.md';t=p.read_text()
t=replace_once(t,'# Current A.2 handoff: 220/231 current-mask cells closed; 11 OPEN','# Current A.2 handoff: 221/231 current-mask cells closed; 10 OPEN')
t=replace_once(t,'November 4, 2026. The [complete D6c5 proof](A2_00100_D6C5_COMPLETE_ORIGINAL_CLOSURE.md) advances\nthe unchanged original register from **219 CLOSED / 12 OPEN to 220 CLOSED / 11 OPEN**.','November 4, 2026. The [complete B340 proof](A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md) advances\nthe unchanged original register from **220 CLOSED / 11 OPEN to 221 CLOSED / 10 OPEN**.')
t=replace_once(t,'with a fresh whole-original portable replay. Accepted counts are\n**220/231 original cells and 8/32 masks closed**.','with a fresh whole-original portable replay. At that recovery checkpoint,\naccepted counts were **220/231 original cells and 8/32 masks closed**.')
t=replace_once(t,'update. Remaining original families are **A1, B6, C3, D1**.','update. At that checkpoint the remaining families were **A1, B6, C3, D1**;\nthe subsequent complete B340 proof leaves **A1, B5, C3, D1**.')
t=replace_once(t,'## Latest complete original\n','## Latest complete original: B340\n\n'+section.split('\n\n',1)[1]+'[Complete B340 physical assembly and reproduction](A2_00100_B340_COMPLETE_ORIGINAL_CLOSURE.md).\n\n## Earlier complete original: D6c5\n')
t=replace_once(t,'in the caller. The unchanged register now has **220 CLOSED / 11 OPEN**, with','in the caller. At this earlier checkpoint the register had **220 CLOSED / 11 OPEN**, with')
t=replace_once(t,'complete original-cell proofs now give **220/11 cells and 8/24 masks**.','complete original-cell proofs now give **221/10 cells and 8/24 masks**.')
t=replace_once(t,'- Current mask: **220 CLOSED / 11 OPEN**, same 231 IDs and certified full cover.','- Current mask: **221 CLOSED / 10 OPEN**, same 231 IDs and certified full cover.')
t=replace_once(t,'11 original predicates or a theorem subsuming them, followed by the other','10 original predicates or a theorem subsuming them, followed by the other')
p.write_text(t)

manifest={
    'schema':'complete_registered_B340_original_source_bound_publication_v1',
    'status':'ACCEPTED_COMPLETE_ORIGINAL_PHYSICAL_EXCLUSION',
    'original_id':ID,'original_path':cell['path'],'target_mask':'001/00','target_Q':'1105/256',
    'new_original_cells':1,'new_masks':0,'new_positional_roots':0,'new_roadmap_gates':0,
    'original_before':{'closed':220,'open':11,'total':231},
    'original_after':{'closed':221,'open':10,'total':231},
    'mask_ledger':{'closed':8,'open':24,'total':32},
    'remaining_original_families':{'A':1,'B':5,'C':3,'D':1},
    'fixed_denominators':{'original_cells':231,'masks':32,'positional_roots':7915,'roadmap_gates':15},
    'all_nine_original_frames_retained':True,'original_corners':36,'original_pairs':36,
    'original_cone_comparisons':5,'original_actual_links':['AB','BC','EF','FG'],
    'original_strict_weak_link':'CD','counts':proof['counts'],
    'literal_row_accounting':table_audit['totals'],'terminal_kinds':table_audit['terminal_kinds'],
    'fresh_portable_receipt':receipt,'proof_archive':ready,
    'published_prior_manifest':'a2_00100_b16a_I32_complete_H_manifest.json',
    'published_prior_manifest_sha256':sha(PACKET/'PUBLISHED_PRIOR.json'),
    'closure_hand':closure_path.name,'closure_hand_sha256':sha(closure_path),
    'fixed_register_sha256':sha(ledger),'all_231_original_definitions_unchanged':True,
    'other_230_original_entries_unchanged':True,
    'published_files':{p.name:{'bytes':p.stat().st_size,'sha256':sha(p)}for p in sorted(OUT.iterdir())if p.is_file()},
    'lean_lake_ci_run':False}
mp=NINE/'computer_assisted/a2_00100_b340_complete_original_manifest.json';dump(mp,manifest)
print(json.dumps({'status':'B340_COMPLETE_PUBLICATION_PREPARED','manifest':str(mp),'manifest_sha256':sha(mp),'outer_files':len(manifest['published_files']),'closed':221,'open':10,'changed_ids':changed}))
