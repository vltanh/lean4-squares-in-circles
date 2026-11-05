from pathlib import Path
import json,hashlib,shutil,tarfile,io
B=Path(__file__).resolve().parent;P=B/'restored/b7_selected1011_open_packet_v1';PRIOR=B/'restored/b16a_I32_complete_H_checkpoint';O=B/'b7_verified_prefix_handoff_v1';O.mkdir(exist_ok=False)
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
known={}
for kind,root,m in [('packet',P,read(P/'INPUT_MANIFEST.json')),('prior',PRIOR,read(PRIOR/'SHA256_MANIFEST.json'))]:
 for name,h in m['files'].items():known.setdefault(h,dict(root=kind,path=name))
entries={};blobs={}
def add(p,h=None):
 p=Path(p);native=str(p.resolve());h=h or sha(p)
 if native in entries:assert entries[native]['sha256']==h;return
 if h in known:storage=known[h]
 else:
  assert p.is_file() and sha(p)==h,('unrecoverable new source',str(p),h)
  blobs[h]=p;storage=dict(root='delta',path='sources/'+h)
 target=str(p.resolve().relative_to(B)) if p.resolve().is_relative_to(B) else None
 entries[native]=dict(native_path=native,sha256=h,storage=storage,target=target)
variants={}
for name,accepted in [('component156_one',True),('component156_sat256',False),('component813_ci16',False),('component156_angles96',False)]:
 d=B/'restored'/name;m=read(d/'manifest.json');add(d/'manifest.json')
 for e in m['nodes']:add(d/e['file'],e['sha256'])
 for p,h in m['sources'].items():add(p,h)
 for p in d.glob('*RECEIPT.json'):add(p)
 for p in d.glob('*COUNT.json'):add(p)
 variants[name]=dict(manifest=str((d/'manifest.json').relative_to(B)),manifest_sha256=sha(d/'manifest.json'),accepted_full_exact_replay=accepted,nodes=len(m['nodes']),new_original_credit=0)
for rel in ['bounded_continue.py','sat_cover_v1.py','fixed_ci_813_v1.py','angle_cover156_v1.py','replay_continuation_v1.py','audit_bounded_results.py','BOUNDED_RESULTS_STRUCTURAL_AUDIT.json','B7_ANGLE96_DIAGNOSTIC_AND_NEXT_PLAN.json','component156_one.log','component156_sat256.log','component813_ci16.log','component156_angles96.log','restored/component156_one_replay/COMPLETE_ORIGINAL_REPLAY.json','restored/component156_one_replay/PORTABLE_RECEIPT.json','restored/baseline_replay/COMPLETE_ORIGINAL_REPLAY.json','restored/baseline_replay/PORTABLE_RECEIPT.json']:
 add(B/rel)
for native,h in read(B/'restored/component156_one_replay/COMPLETE_ORIGINAL_REPLAY.json')['source_sha256'].items():add(native,h)
pub=B.parents[1]/'computer_assisted/a2_00100_b7_completed_components1011_checkpoint_v1'
for name in ['ARCHIVE_PARTS.json','PUBLISHED_PRIOR.json']:
 shutil.copyfile(pub/name,O/name)
write(O/'INPUTS.json',dict(schema='B7_thin_delta_exact_native_source_map_v1',files=list(entries.values())))
with tarfile.open(O/'inputs.tar.xz','w:xz',preset=6)as tar:
 for h,p in sorted(blobs.items()):
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==h
  info=tarfile.TarInfo('sources/'+h);info.size=len(data);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(data))
write(O/'MANIFEST.json',dict(schema='B7_verified_prefix_and_negative_bounded_handoff_v1',original_id='negative-7c60be8b07a358e9',published_checkpoint_commit='38b47f293ba6dec51f2abf7d6c2738d427742059',published_checkpoint='research/nine/computer_assisted/a2_00100_b7_completed_components1011_checkpoint_v1',published_prior='research/nine/computer_assisted/a2_00100_b16a_I32_complete_H_checkpoint',packet_manifest_sha256=sha(P/'INPUT_MANIFEST.json'),prior_manifest_sha256=sha(PRIOR/'SHA256_MANIFEST.json'),verified_tree='component156_one',verified_counts=dict(nodes=1011,excluded=543,open=43),new_verified_bound_deductions=160,changed_verified_node=871,preserved_completed_components=[4,260,814,816,818,820,993],variants=variants,next_plan=dict(parent=1013,children=[1051,1055],source='component156_sat256',status='NOT_STARTED_USER_REQUESTED_HANDOFF',complete_angle_children_cap=32,actual_persisted_native_LP_call_cap=600),candidate_trees_are_diagnostics_only=True,inputs_sha256=sha(O/'INPUTS.json'),archive_sha256=sha(O/'inputs.tar.xz'),archive_bytes=(O/'inputs.tar.xz').stat().st_size,new_input_blobs=len(blobs),new_uncompressed_bytes=sum(p.stat().st_size for p in blobs.values()),native_input_paths=len(entries),no_published_input_blob_duplicated=True,whole_original_credit=0,new_masks=0))
shutil.copyfile(__file__,O/Path(__file__).name)
print(json.dumps({k:v for k,v in read(O/'MANIFEST.json').items()if k in ['archive_bytes','archive_sha256','new_input_blobs','native_input_paths','new_uncompressed_bytes']},indent=2))
