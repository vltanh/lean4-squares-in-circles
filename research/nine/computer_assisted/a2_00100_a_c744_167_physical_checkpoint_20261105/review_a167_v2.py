#!/usr/bin/env python3
"""Independent physical suffix, complete-union and unchanged ancestry review for A167."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
import hashlib,json,sys,time
BASE=Path('/workspace/lean4-squares-in-circles/research/nine/.runs/a_continue')
OUT=Path(__file__).resolve().parent
T=Path('/workspace/scratch/f9f48fcfb253/ac_work/tree');sys.path.insert(0,str(T))
import verify_c887_unit_four_corner_tree as V
import independent_physical_sat_diagonal_replay as S

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def state(v,adapter):
 s=dict(id=v['id'],path=v['path'],choices=adapter.choices(v['path']))
 for k in ('angles','positions','scalar'):s[k]=tuple(tuple(map(F,z))for z in v[k])
 for k in ('differences','diagonal'):
  assert {tuple(e['pair'])for e in v[k]}==set(combinations(range(9),2))
  s[k]={tuple(e['pair']):tuple(tuple(map(F,z))for z in e['intervals'])for e in v[k]}
 assert len(s['angles'])==9 and len(s['positions'])==18 and len(s['scalar'])==36
 return s
started=time.monotonic();mp=BASE/'checkpoint167/manifest.json';oldmp=BASE/'retained165/manifest.json'
assert sha(oldmp)=='5c06610c0f8e4e317707b4f352277a2530d39e7f3cb63dfc5b03089571ccd98c'
m=read(mp);old=read(oldmp)
for k in ('id','original_path','parent','conditional_parent','component','closed_domain','scope'):assert m[k]==old[k]
register=read('/workspace/lean4-squares-in-circles/research/nine/gates/A2_00100_FIXED_FRONTIER.json')
cell=next(c for c in register['cells']if c['id']==m['id']);assert cell['path']==m['original_path']and cell['status']=='OPEN'
assert m['component']==3 and m['scope']=='ONE_CLOSED_MEMBER_OF_THE_COMPLETE_ACTUAL_AB_FIVE_COVER'
assert m['new_original_cells']==m['new_masks']==0
for p,h in m['source_sha256'].items():assert sha(p)==h,p
for ref in(m['parent'],m['conditional_parent']):assert sha(ref['path'])==ref['sha256']
ns=m['nodes'];assert len(ns)==167 and [e['index']for e in ns]==list(range(167))
for e in ns:assert sha(mp.parent/e['file'])==e['sha256']
changed={145,149,152,163,144,148,151,154,156,157,159,161,164}
for i,e in enumerate(old['nodes']):
 assert sha(oldmp.parent/e['file'])==e['sha256']
 if i not in changed:assert ns[i]['sha256']==e['sha256']
visited=set();unions=[]
def visit(i,parent=None,depth=0):
 assert i not in visited;visited.add(i);n=ns[i];assert n['parent']==parent and n['depth']==depth
 if not n['children']:return n['status']=='CANDIDATE_CLOSED'
 assert n['complete_children']is True and len(n['children'])==len(set(n['children']))
 split=n['split'];kind=split['kind'];restrictions=[ns[k]['restriction']for k in n['children']]
 if kind in('complete_physical_sat','complete_physical_proxy'):
  pair=tuple(split['pair']);assert 0<=pair[0]<pair[1]<9
  expected=set(product(pair,(0,1),(-1,1)))if kind=='complete_physical_sat'else set(product((0,1),(-1,1)))
  assert {tuple(z['choice'])for z in restrictions}==expected and len(restrictions)==len(expected)
  assert all(z['pair']==list(pair)for z in restrictions)
 else:
  assert kind=='closed_angle_bisection'and len(restrictions)==2 and {z['side']for z in restrictions}=={0,1}
  assert all(z['owner']==split['owner']and F(z['cut'])==F(split['cut'])for z in restrictions)
 outcomes=[visit(k,i,depth+1)for k in n['children']];closed=all(outcomes)
 assert n['status']==('CANDIDATE_COVER_CLOSED'if closed else'OPEN');unions.append(dict(index=i,kind=kind,complete=True));return closed
assert visit(0)is False and visited==set(range(167))
assert ns[146]['children']==[165,166]and ns[146]['split']==dict(kind='closed_angle_bisection',owner=8,cut='1/2')
parent146=read(oldmp.parent/old['nodes'][146]['file'])['final'];assert F(parent146['angles'][8][0])<F(1,2)<F(parent146['angles'][8][1])
for i,side in((165,0),(166,1)):
 r=read(mp.parent/ns[i]['file']);expected=json.loads(json.dumps(parent146));expected['angles'][8][1 if side==0 else 0]='1/2';expected['path']+= [['angle_cut',[8,'1/2'],side]]
 assert r['initial']==expected
checker=V.Checker();adapter=V.Adapter(checker);assert checker.K.V.Q==F(1105,256)
assert checker.K.V.EDGES==((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
reports=[];row_names=set()
for i in sorted(changed|{165,166}):
 r=read(mp.parent/ns[i]['file'])
 if i<165:
  before=read(oldmp.parent/old['nodes'][i]['file']);assert r['initial']==before['initial']and r['rounds'][:len(before['rounds'])]==before['rounds']
  initial=before['final'];rounds=r['rounds'][len(before['rounds']):]
 else:initial=r['initial'];rounds=r['rounds']
 suffix=dict(status=r['status'],initial=initial,rounds=rounds)
 if 'terminal'in r:suffix.update(terminal=r['terminal'],terminal_state=r['terminal_state'])
 else:suffix['final']=r['final']
 printed=[x for rr in rounds for x in rr['printed_rows']]+r.get('terminal',{}).get('rows',[])
 names={x['name']for x in printed};row_names|=names
 assert not any(n.startswith(('selected_extra','certified_a_','two_link_actual_AB_escape','stronger_actual_ab'))for n in names)
 audit,after=S.check_record(suffix,state(initial,adapter),adapter)
 assert (after is None)==(i in{145,149,152,163,165,166})
 reports.append(dict(index=i,payload_sha256=ns[i]['sha256'],**audit));print('REVIEW_SUFFIX',i,audit['status'],audit['deductions'],flush=True)
V.verify_all_bindings();assert not any(n in sys.modules for n in('numpy','scipy','highspy'))
for p,h in m['source_sha256'].items():assert sha(p)==h
leaves=[n for n in ns if not n['children']]
result=dict(status='PASS_INDEPENDENT_A167_NEW_PHYSICAL_SUFFIXES_AND_FULL_COVER_STRUCTURE',manifest_sha256=sha(mp),source_manifest_sha256=sha(oldmp),
 original_id=m['id'],original_path=m['original_path'],same_frozen_231_cell_definition=True,component=3,scope=m['scope'],
 nodes=167,excluded_leaves=sum(n['status']=='CANDIDATE_CLOSED'for n in leaves),open_leaves=sum(n['status']=='OPEN'for n in leaves),
 every_graph_node_reached_once=True,every_closed_union_complete=True,new_angle146_both_closed_faces_retained=True,
 all_nine_original_frames_36_corners_36_pairs_five_cones_actual_AB_BC_EF_FG_strict_weak_CD_preserved=True,
 all_152_unmodified_payloads_byte_identical=True,original_prefix_rounds_preserved=True,
 new_physical_suffixes_independently_replayed=reports,unproved_guarded_height_rows_used=False,
 new_rows_replay_under_standard_physical_adapter_without_original_i64_or_height_extensions=True,
 existing_original_wide_I64_transport_reviewed_separately=True,historical_accepted_source_arithmetic_reused_not_repeated=True,
 complete167_prefix_replay_status='PENDING_SEPARATE_FULL_REPLAY',new_original_ledger_credit=0,new_mask_ledger_credit=0,
 strict_radius_scope='q < 1105/256; no global equality classification',blocking_findings=[],
 checker_source_sha256={str(Path(p).resolve()):sha(p)for p in(__file__,V.__file__,S.__file__)},seconds=time.monotonic()-started)
full_path=BASE/'CHECKPOINT167_FULL_REPLAY.json';full=read(full_path)
assert full['status']=='PASS_PARTIAL_TWO_LINK_COMPLEMENT_TREE'
assert (full['nodes'],full['excluded_leaves'],full['open_leaves'])==(167,124,9)
assert full['original_id']==m['id'] and full['original_path']==m['original_path'] and full['component']==3
assert full['all_current_records_and_prefixes_freshly_replayed'] is True
assert full['historical_source_proofs_reused_not_repeated']['source_arithmetic_repeated'] is False
assert full['all_nine_originals_retained'] and full['closed_shared_faces_retained']
assert full['new_original_cells']==full['new_masks']==0
assert full['input_sha256'][str(mp.resolve())]==sha(mp)
for i,e in enumerate(ns):assert full['input_sha256'][str((mp.parent/e['file']).resolve())]==e['sha256']
for p,h in full['checker_dependency_sha256'].items():assert sha(p)==h
source_bindings=BASE/'CHECKPOINT167_SOURCE_BINDINGS.json';sb=read(source_bindings)
for rel,h in sb['files'].items():assert sha(BASE/rel)==h
result.update(status='PASS_INDEPENDENT_A167_PHYSICAL_ANCESTRY_COVER_AND_NEW_SUFFIX_REVIEW',
 complete167_prefix_replay_status=full['status'],complete167_prefix_replay=dict(path=str(full_path.resolve()),sha256=sha(full_path)),
 complete_current_prefixes_freshly_replayed=True,historical_source_proofs_reused_not_cold_replayed=True,
 full_replay_counts={k:full[k]for k in ('nodes','leaf_domains','excluded_leaves','open_leaves','rounds','deductions','printed_rows_checked')},
 source_bindings_sha256=sha(source_bindings),reviewed_I64_source_binding_sha256='63458318a3681d677745baf4a00d8a738a5705c6276659174e59f440fa9a06e3',
 zero_whole_original_credit_because_nine_component3_domains_remain_open=True)
(OUT/'A167_INDEPENDENT_PHYSICAL_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in('status','nodes','excluded_leaves','open_leaves','seconds')}),flush=True)
