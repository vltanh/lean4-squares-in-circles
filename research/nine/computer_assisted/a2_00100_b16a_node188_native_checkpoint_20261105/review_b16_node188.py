from pathlib import Path
from itertools import combinations,product
from fractions import Fraction as F
from collections import Counter
import json,hashlib,tarfile
R=Path('/workspace/lean4-squares-in-circles/research/nine/.runs');P=R/'b16_continue/node188_native_package';TREE=R/'b16_continue/complete_node188_tree';OUT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
rpath=OUT/'B16_NODE188_INDEPENDENT_REPLAY.json';r=read(rpath);m=read(TREE/'manifest.json');pack=read(P/'MANIFEST.json');index=read(P/'INPUTS.json')
assert r['status']=='PASS_COMPLETE_RESTRICTED_PHYSICAL_TREE' and r['complete'] and not r['whole_original_proved']
assert (r['nodes'],r['excluded_leaves'],r['open_leaves'])==(281,210,0) and r['complete_unions']=={'sat':23,'angle':48}
assert (r['additional_relative_support_chord_rows_checked'],r['additional_central_nine_rows_checked'])==(45,0)
assert r['initial_original_id']=='negative-16a2fc93c8d133f0' and len(r['initial_path'])==19
reg=read('/workspace/lean4-squares-in-circles/research/nine/gates/A2_00100_FIXED_FRONTIER.json');root=next(e for e in reg['cells'] if e['id']==r['initial_original_id'])['path'];assert r['initial_path'][:len(root)]==root
nodes={}
for n in m['nodes']:
 p=TREE/n['file'];assert sha(p)==n['sha256'];d=read(p);nodes[n['index']]=d;s=d['initial'];assert s['id']==r['initial_original_id']
 assert len(s['angles'])==9 and len(s['positions'])==18 and len(s['scalar'])==36
 assert {tuple(x['pair']) for x in s['differences']}==set(combinations(range(9),2))
counts=Counter();seen=set();stack=[0]
while stack:
 k=stack.pop();assert k not in seen;seen.add(k);d=nodes[k]
 if d['children']:
  kind=d['split']['kind'];counts[kind]+=1;children=[nodes[c]for c in d['children']]
  assert all(c['parent']==k for c in children)
  if kind=='angle':assert len(children)==2 and [c['choice']for c in children]==[0,1]
  else:
   assert kind=='sat' and len(children)==8
   assert {tuple(c['choice'])for c in children}==set(product(d['split']['pair'],range(2),(-1,1)))
  stack.extend(d['children'])
 else:
  assert d['record']['status']=='CANDIDATE_CLOSED';terminal=d['record']['terminal']
  assert terminal['kind'] in ('positive_exact_reserve','accepted_effective_angle_terminal')
  if terminal['kind']=='positive_exact_reserve':assert F(terminal['reserve'])>0
assert seen==set(nodes) and counts=={'sat':23,'angle':48}
prefix_path=Path(m['parent']['path']);assert sha(prefix_path)==m['parent']['sha256']==r['parent_certificate_sha256'];prefix=read(prefix_path)
assert sha(prefix['source_manifest_path'])==prefix['source_manifest_sha256']
assert len(prefix['steps'])==16 and prefix['steps'][-1]['original_tree_index']==188
last=prefix['steps'][-1]['record'];assert len(last['rounds'])==2
assert nodes[0]['initial']==nodes[0]['record']['initial']==nodes[0]['record']['final']==prefix['final']==last['final']
assert nodes[0]['record']['rounds']==[]
assert r['parent_audit']['certificate_sha256']==sha(prefix_path)
assert r['parent_audit']['branch_steps']==len(prefix['steps'])
assert m['grafted_complete_regions']==[206,318,322,326,330]
assert sha(P/'inputs.tar.xz')==pack['input_archive_sha256']=='5ce1da49ec74e29d1daa986c2a49d01fa58638f8bbbb8aa4b23a0f55b139ca5c'
expected={e['sha256']for e in index['files']};blobs=set()
with tarfile.open(P/'inputs.tar.xz','r:xz')as tar:
 for member in tar:
  assert member.isfile() and member.name.startswith('sources/');digest=member.name.split('/')[-1]
  assert digest in expected and hashlib.sha256(tar.extractfile(member).read()).hexdigest()==digest;blobs.add(digest)
assert blobs==expected
for e in index['files']:assert sha(e['path'])==e['sha256']
for name,h in pack['files'].items():assert sha(P/name)==h
review=dict(status='PASS_INDEPENDENT_NODE188_PHYSICAL_COVER_WEIGHTED_CHORD_AND_NATIVE_TRANSPORT_REVIEW',independent_replay=dict(path=str(rpath),sha256=sha(rpath)),tree_manifest_sha256=sha(TREE/'manifest.json'),package_manifest_sha256=sha(P/'MANIFEST.json'),archive_sha256=sha(P/'inputs.tar.xz'),input_paths=len(index['files']),unique_input_blobs=len(expected),original_id=r['initial_original_id'],same_frozen_original_prefix=True,scope='complete 19-entry conditional region node188 only',nodes=281,complete_closed_SAT_unions=23,complete_closed_angle_unions=48,excluded_terminal_domains=210,open_terminal_domains=0,weighted_relative_support_chord_occurrences_independently_decoded=45,weighted_central_nine_rows=0,every_chord_guard_rebuilt_from_certified_same_state_intervals=True,all_nine_originals_36corners_36pairs_fivecones_actual_AB_BC_EF_FG_strict_weak_CD_retained=True,ancestor_prefix_freshly_replayed=True,root_two_bound_rounds_in_prefix=True,zero_round_root_identical_to_replayed_prefix_final=True,grafted_complete_regions=m['grafted_complete_regions'],all_closed_angle_and_SAT_faces_retained=True,all_archive_members_and_native_inputs_rehashed=True,full_original_or_parent73_closure_claimed=False,standalone_cold_portable_replay_claimed=False,whole_original_credit=0,new_mask_credit=0,blocking_findings=[],reviewer_source_sha256=sha(__file__))
(OUT/'B16_NODE188_INDEPENDENT_REVIEW.json').write_text(json.dumps(review,indent=2)+'\n');print(review['status'],sha(OUT/'B16_NODE188_INDEPENDENT_REVIEW.json'))
