"""Commit the reviewed conditional mask transfer, without changing any ledger."""
from pathlib import Path
import hashlib,json,shutil,subprocess
R=Path(__file__).resolve().parent;repo=R/'pr11';nine=repo/'research/nine'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo,text=True).strip()
assert git('rev-parse','HEAD')=='87705ef3bd4291921cac321042b2cac7cc5fa605'
root_review=R/'ORIGINAL_ROW_MASK_TRANSFER_ROOT_REVIEW.json'
assert sha(root_review)=='b636312a30cff84d2255a4ab620f1771d4f802c0a9f0b24265a358bdc5741715'
independent=R/'a_family/other_masks/ORIGINAL_ABCD_OPPOSITE_TILT_SPECIALIZATION_INDEPENDENT_REVIEW.json'
assert sha(independent)=='246c147cd9e70adf71a61ce8fce5252f40c660e28a37c36f1ea4331bee39a404'
package=nine/'computer_assisted/original_row_mask_transfer';assert not package.exists();(package/'inputs').mkdir(parents=True)
source_theorem=R/'c887_whole_eight_checkpoint_package/opposite_tilt_theorem'
committed_theorem=nine/'computer_assisted/opposite_tilt_ahid_row'
bound=json.loads(independent.read_text())['source_sha256'];bound.update(json.loads(root_review.read_text())['source_sha256'])
for p in [independent,root_review,R/'a_family/other_masks/ORIGINAL_ABCD_OPPOSITE_TILT_SPECIALIZATION_INDEPENDENT_REVIEW.md',R/'a_family/other_masks/review_original_ABCD_opposite_tilt_specialization.py',Path(__file__).resolve()]:bound[str(p)]=sha(p)
paths=[];bindings=[]
for source,expected in sorted(bound.items()):
 p=Path(source);assert sha(p)==expected
 if p.is_relative_to(source_theorem):
  candidate=committed_theorem/p.relative_to(source_theorem)
 else:candidate=None
 if candidate is not None and candidate.is_file()and sha(candidate)==expected:destination=candidate;reused=True
 else:
  destination=package/'inputs'/(expected[:20]+'_'+p.name);reused=False
  if destination.exists():assert sha(destination)==expected
  else:shutil.copy2(p,destination);paths.append(destination)
 bindings.append(dict(original_source=source,repository_file=str(destination.relative_to(repo)),sha256=expected,reused_accepted_theorem_input=reused))
manifest=dict(schema='portable_original_ABCD_row_mask_transfer_sources_v1',normative_hand_sha256='6d95730bd97d4a69e6f3028b06b8c5bdb1605334f6f86f92e5c599f9bc09ec50',normative_specification_sha256='e9090ecd6aeac9de625e6bc44f7cdef049cc9720a05b108c3783a468937cddf3',sources=bindings,new_original_cells=0,new_masks=0,new_positional_roots=0,new_roadmap_gates=0,original_cell_denominator=231,mask_denominator=32,positional_root_denominator=7915,roadmap_gate_denominator=15)
p=package/'SOURCE_BINDINGS.json';p.write_text(json.dumps(manifest,indent=2)+'\n');paths.append(p)
p=package/'verify_source_bindings.py';p.write_text('''"""Verify immutable publication inputs; this is not a new polynomial replay."""
from pathlib import Path
import hashlib,json
here=Path(__file__).resolve().parent
repo=here.parents[3]
m=json.loads((here/'SOURCE_BINDINGS.json').read_text())
for row in m['sources']:
 p=(repo/row['repository_file']).resolve()
 assert p.is_relative_to(repo)
 assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],row['repository_file']
assert m['new_original_cells']==m['new_masks']==m['new_positional_roots']==m['new_roadmap_gates']==0
print('PASS_PORTABLE_SOURCE_BINDINGS',len(m['sources']),'conditional cover only; no new closure credit')
''');paths.append(p)
hand=nine/'ORIGINAL_FOUR_ROW_MASK_TRANSFER_AND_CLOSED_ESCAPE_COVER.md'
assert not hand.exists();hand.write_text((R/'global_theorem/FULL_MASK_TRANSFER_AND_ORIGINAL_ROW_REDUCTION_v2.md').read_text()+'''

## Committed source attachment and review

The normative v2 note and specification are preserved byte for byte in
[`computer_assisted/original_row_mask_transfer`](computer_assisted/original_row_mask_transfer).
Its [source map](computer_assisted/original_row_mask_transfer/SOURCE_BINDINGS.json)
locates every immutable input and both independent/root reviews in this
repository. The map explicitly selects the v2 specification; the earlier
JSON name in the historical prose above does not supersede that selection.
The previously accepted opposite-tilt polynomial table is reused unchanged.
Run `python -B -S computer_assisted/original_row_mask_transfer/verify_source_bindings.py`
from this directory to recheck every attachment.

The root read the full normative note and the geometric proof through its
separate original-001 section. The specialization uses Sections 1–6 only.
Only EF and FG require actual projection; each original main link supplies
row order and physical separation. At closed Q, all three main gaps become
one, contradicting any retained strictly weak main bit. Two closed same-sign
conjunctions and all eight signed-height escapes preserve every overlap.

This is a conditional theorem and a complete necessary cover. No escape
member is closed by the cover itself. The fixed ledger remains 218 CLOSED /
13 OPEN original cells, 8 CLOSED / 24 OPEN masks and 5,838 CLOSED / 2,077 OPEN
positional roots. No roadmap gate is added. No Lean, Lake or CI was run.
''');paths.append(hand)
p=package/'README.md';p.write_text('''# Original-row specialization and mask transfers

The [complete hand note](../../ORIGINAL_FOUR_ROW_MASK_TRANSFER_AND_CLOSED_ESCAPE_COVER.md)
specializes the accepted opposite-endpoint theorem to the original ABCD row.
The exact closed necessary cover has two endpoint-angle conjunctions and
eight signed-height halfspaces. All 24 open masks form 14 simultaneous
chain-reversal classes. This packet adds no original-cell or mask credit.

`SOURCE_BINDINGS.json` identifies the normative v2 note/specification and
preserves every reviewed source. `inputs/` contains small immutable copies;
the accepted scalar table stays at its existing repository location.
`verify_source_bindings.py` verifies those exact attachments. It does not
repeat the inherited polynomial arithmetic or prove any remaining domain.
''');paths.append(p)
registers=[nine/'gates/A2_00100_FIXED_FRONTIER.json',nine/'gates/A2_MASK_FRONTIER.json'];before={str(p):sha(p)for p in registers}
for filename,marker in [('PROGRESS.md','## D6c5: complete I21 H and frame cover\n'),('HANDOFF_A2_FIXED_CLOSURE.md','## Fixed ledgers and next handoff\n')]:
 p=nine/filename;s=p.read_text();assert s.count(marker)==1
 s=s.replace(marker,'''## Original ABCD row: complete necessary cover for short-00 masks

The [reviewed mask-transfer note](ORIGINAL_FOUR_ROW_MASK_TRANSFER_AND_CLOSED_ESCAPE_COVER.md)
applies the accepted opposite-endpoint theorem to the unchanged original
ABCD row. It requires actual EF/FG and no actual main link. Opposite endpoint
signs and total main-row height variation at most23/100 exclude strict
radius; any strict weak main bit also excludes the closed-Q equality case.
The complete necessary remainder consists of two closed same-sign domains
and eight signed-height escapes, or the eight height escapes when opposite
signs are already proved. Both angle constraints in each same-sign domain,
all shared threshold faces and all nine original squares are retained.

All24 open masks form14 explicit reversal classes. This is a conditional
reduction with a portable source map and two reviews; every remaining
domain still needs its own complete proof. No fixed ledger is changed.

'''+marker);p.write_text(s);paths.append(p)
subprocess.run(['python','-B','-S',str(package/'verify_source_bindings.py')],check=True)
assert all(sha(p)==h for p,h in before.items())
names=[str(p.relative_to(repo))for p in paths];assert len(names)==len(set(names))
subprocess.run(['git','diff','--check','--',*names],cwd=repo,check=True)
subprocess.run(['git','add','--',*names],cwd=repo,check=True)
assert set(git('diff','--cached','--name-only').splitlines())==set(names)
message='[skip ci] Specialize the original four-row theorem across short-00 masks'
subprocess.run(['git','commit','-m',message],cwd=repo,check=True)
bundle=dict(parent=git('rev-parse','HEAD^'),local_commit=git('rev-parse','HEAD'),base_tree=git('rev-parse','HEAD^^{tree}'),tree=git('rev-parse','HEAD^{tree}'),message=message,files=[])
for name in names:
 p=repo/name;assert 4*((p.stat().st_size+2)//3)+2048<16*1024*1024
 bundle['files'].append(dict(path=name,absolute=str(p),bytes=p.stat().st_size,sha=git('hash-object',str(p))))
(R/'ORIGINAL_ROW_MASK_TRANSFER_PUBLICATION_BUNDLE.json').write_text(json.dumps(bundle,indent=2)+'\n')
print(json.dumps(dict(local_commit=bundle['local_commit'],parent=bundle['parent'],files=len(names),bound_sources=len(bindings),reused_theorem_inputs=sum(x['reused_accepted_theorem_input']for x in bindings))))
