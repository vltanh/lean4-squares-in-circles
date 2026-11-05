"""Independent exact replay of the current unchanged-original C887 cover.

The numerical search may leave a frontier. Every processed record and every
4/8/2 closed cover edge is checked, and every unprocessed frontier domain is
accounted for. The archived original initializer and its original bound source, plus the
accepted same-original height exclusions, are replayed afresh. Only standard-library and independent modules are imported.
No original or mask credit is emitted while even one frontier domain remains.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
from collections import Counter
import sys,json,argparse,hashlib,time,subprocess
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/ac_work/tree'))
sys.path.insert(0,str(HERE.parent/'b_family/source/universal_center_disk'))
import verify_c887_unit_four_corner_tree as BASE
import independent_physical_sat_diagonal_replay as CORE
import independent_physical_proxy_cover as PROXY
import independent_physical_center_disk_rows as CENTER
import independent_c_height_exclusion_consequences as HEIGHT
TARGET='negative-887236b78100baf3'
ROOT_PATH=[['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

class Adapter(BASE.Adapter):
 def rebuild(self,state,printed):
  assert state['id']==TARGET and state['path'][:3]==ROOT_PATH
  ordinary=[r for r in printed if not r['name'].startswith((CENTER.PREFIX,HEIGHT.PREFIX))]
  answer,bounds,physical=super().rebuild(state,ordinary)
  for r in printed:
   if not r['name'].startswith((CENTER.PREFIX,HEIGHT.PREFIX)):continue
   literal=(tuple((k,F(v))for k,v in r['coefficients']),F(r['rhs']),r['name'])
   if r['name'].startswith(CENTER.PREFIX):CENTER.verify_literal(literal)
   else:HEIGHT.verify_literal(literal,state)
   assert r['index']not in answer;answer[r['index']]=literal
  return answer,bounds,physical


def original_state(adapter,bindings,output):
 prefix_script=HERE/'replay_c887_original_prefix.py';script_hash=sha(prefix_script)
 prefix_report=output.with_suffix('.original.json');prefix_log=output.with_suffix('.original.log')
 with prefix_log.open('w')as log:
  subprocess.run([sys.executable,'-B','-S',str(prefix_script),str(prefix_report)],check=True,stdout=log,stderr=subprocess.STDOUT)
 result=json.loads(prefix_report.read_text());assert result['status']=='PASS_FRESH_C887_ORIGINAL_PREFIX'
 assert result['original_id']==TARGET and result['original_path']==ROOT_PATH and result['checker_sha256']==script_hash
 assert sha(prefix_script)==script_hash;bindings[str(prefix_script)]=script_hash
 for path,digest in result['input_sha256'].items():assert sha(path)==digest;bindings[path]=digest
 height=HEIGHT.replay_source_exclusions('c887',output.parent/(output.stem+'_fresh_height_exclusions'))
 assert height['status']=='PASS_FRESH_C_ORIGINAL_HEIGHT_EXCLUSION_CONSEQUENCES'
 bindings[height['source_report']['path']]=height['source_report']['sha256']
 bindings[str(HEIGHT.BINDING)]=HEIGHT.BINDING_SHA;bindings[str(HEIGHT.LOADER)]=HEIGHT.LOADER_SHA
 v=result['certified_original_state'];box=lambda entries:tuple(tuple(map(F,ab))for ab in entries)
 state=dict(id=TARGET,path=ROOT_PATH,choices=adapter.choices(ROOT_PATH),angles=box(v['angles']),positions=box(v['positions']),scalar=box(v['scalar']),differences={tuple(d['pair']):box(d['intervals'])for d in v['differences']},diagonal={tuple(d['pair']):box(d['intervals'])for d in v['diagonal']})
 CORE.valid_state(state);assert CORE.state_view(state)==v
 # Re-establish the complete starting box from a fresh exact root record.
 bound_path=HERE/'C887_FRESH_WHOLE_BOUND_REDERIVATION.json';bound_raw=bound_path.read_bytes();bindings[str(bound_path)]=sha(bound_path)
 bound_record=json.loads(bound_raw)
 assert bound_record['initial']==CORE.state_view(state)
 assert not any('certified_original_root_bound_'in row['name']for rr in bound_record['rounds']for row in rr['printed_rows'])
 bound_audit,stronger=CORE.check_record(bound_record,state,adapter);assert stronger is not None
 statement_path=HERE.parents[1]/'computer_assisted/native_shared_bound_progress_v1/native_evidence/direct_shared_bounds_and_C_lazy_readers_native_v1/native/ac_work/tree/C887_WHOLE_HEIGHT_BOUND_STATE_BINDING.json'
 bindings[str(statement_path)]=sha(statement_path);assert bindings[str(statement_path)]=='b24a9fa7675eb4d2330518da7481e5bca75700928035d202eeb9bf964a4adf2d'
 v=json.loads(statement_path.read_text())['state'];assert v['id']==TARGET and v['path']==ROOT_PATH
 actual=CORE.state_view(stronger);compared=0
 for key in ('angles','positions','scalar'):
  assert len(v[key])==len(actual[key])
  for i,((lo,hi),(tlo,thi))in enumerate(zip(actual[key],v[key])):
   assert F(tlo)<=F(lo)<=F(hi)<=F(thi),('starting state not reestablished',key,i,[lo,hi],[tlo,thi]);compared+=1
 for key in ('differences','diagonal'):
  targets={tuple(r['pair']):r['intervals']for r in v[key]}
  assert set(targets)==set(tuple(r['pair'])for r in actual[key])
  for row in actual[key]:
   for axis,((lo,hi),(tlo,thi))in enumerate(zip(row['intervals'],targets[tuple(row['pair'])])):
    assert F(tlo)<=F(lo)<=F(hi)<=F(thi),('starting state not reestablished',key,row['pair'],axis,[lo,hi],[tlo,thi]);compared+=1
 assert compared==207
 state=dict(id=TARGET,path=ROOT_PATH,choices=adapter.choices(ROOT_PATH),angles=box(v['angles']),positions=box(v['positions']),scalar=box(v['scalar']),differences={tuple(d['pair']):box(d['intervals'])for d in v['differences']},diagonal={tuple(d['pair']):box(d['intervals'])for d in v['diagonal']})
 CORE.valid_state(state);assert CORE.state_view(state)==v
 return dict(original_prefix=result,necessary_same_original_height_exclusions=height,fresh_whole_root_bound_record=dict(path=str(bound_path),sha256=bindings[str(bound_path)],audit=bound_audit),starting_state_rederived_without_missing_archive=True,componentwise_interval_weakenings_checked=compared),state,{}



def angle_child(parent,owner,cut,side,adapter):
 assert type(owner)is int and 0<=owner<9 and type(side)is int and side in(0,1)
 cut=F(cut);lo,hi=parent['angles'][owner];assert lo<cut<hi
 child=deepcopy(parent);angles=list(child['angles']);angles[owner]=(lo,cut)if side==0 else(cut,hi)
 child['angles']=tuple(angles);child['path']=deepcopy(parent['path'])+[['angle_cut',[owner,str(cut)],side]]
 child['choices']=adapter.choices(child['path']);CORE.valid_state(child);return child


def replay(manifest_path,output):
 assert __debug__;started=time.monotonic();manifest_path=Path(manifest_path).resolve();output=Path(output).resolve()
 manifest_bytes=manifest_path.read_bytes();manifest=json.loads(manifest_bytes)
 snapshot_path=output.with_suffix('.manifest.json');snapshot_path.parent.mkdir(parents=True,exist_ok=True);snapshot_path.write_bytes(manifest_bytes)
 assert manifest['schema']=='whole_c_selective_dfs_continuation_v1'
 assert manifest['original']['id']==TARGET and manifest['original']['path']==ROOT_PATH
 bindings={};checker=BASE.Checker();adapter=Adapter(checker);BASE.verify_all_bindings()
 parent_audit,state,source_map=original_state(adapter,bindings,output)
 assert CORE.state_view(state)==manifest['original']
 source=Path(manifest['source_manifest']['path']);assert sha(source)==manifest['source_manifest']['sha256'];bindings[str(source)]=sha(source)
 entries=manifest['nodes'];nodes={n['index']:n for n in entries}
 assert len(nodes)==len(entries)and 0 in nodes
 pending={n['index']:n for n in manifest['pending']};assert len(pending)==len(manifest['pending'])and not(set(nodes)&set(pending))
 stopped={n['index']:n for n in manifest['stopped']};assert len(stopped)==len(manifest['stopped'])and set(stopped)<=set(nodes)
 records={}
 for idx,n in nodes.items():
  assert type(idx)is int and idx>=0 and n['file']==f'node_{idx:05}.json'
  path=Path(n['source_file'])if 'source_file'in n else manifest_path.parent/n['file']
  assert path.is_file();digest=sha(path);bindings[str(path)]=digest;records[idx]=(path,digest)
 visited=set();frontier=set();audits=[];covers=[];leaves=[];recomputed_closed=[]
 def edge_key(e):
  if e is None:return None
  if e['kind']in('proxy','sat'):
   assert len(e['pair'])==2 and all(type(x)is int for x in e['pair'])and 0<=e['pair'][0]<e['pair'][1]<9
   assert all(type(x)is int for x in e['choice'])
   return e['kind'],tuple(e['pair']),tuple(e['choice'])
  assert e['kind']=='angle'and type(e['owner'])is int and type(e['choice'])is int
  return 'angle',e['owner'],F(e['cut']),e['choice']
 def visit(idx,initial,parent=None,edge=None):
  assert type(idx)is int and idx>=0 and idx not in visited and idx not in frontier
  if idx in pending:
   n=pending[idx];assert n['parent']==parent and edge_key(n['edge'])==edge_key(edge)
   assert n['state']==CORE.state_view(initial);frontier.add(idx);leaves.append(dict(index=idx,excluded=False,unprocessed=True));return False
  assert idx in nodes;visited.add(idx);n=nodes[idx]
  assert n['parent']==parent and edge_key(n['edge'])==edge_key(edge)
  assert n['depth']==len(initial['path'])-3
  path,digest=records[idx];assert sha(path)==digest;record=json.loads(path.read_text())
  audit,after=CORE.check_record(record,initial,adapter);audit.update(index=idx,depth=n['depth'],sha256=digest)
  audits.append(audit);split=n.get('split');children=split['children']if split else[]
  assert isinstance(children,list)and len(children)==len(set(children))
  if after is None:
   assert not children and split is None and n['status']=='CANDIDATE_CLOSED'and idx not in stopped
   leaves.append(dict(index=idx,excluded=True,terminal=record['terminal']['kind']));return True
  assert n['status']in('OPEN','CANDIDATE_COVER_CLOSED')
  if not children:
   assert split is None and idx in stopped
   assert stopped[idx]['state']==CORE.state_view(initial)
   leaves.append(dict(index=idx,excluded=False,stopped=True));return False
  assert idx not in stopped
  child_entries=[nodes.get(i,pending.get(i))for i in children];assert all(x is not None for x in child_entries)
  restrictions=[x['edge']for x in child_entries];outcomes=[]
  kind=split['kind']
  if kind in('proxy','sat'):
   pair=tuple(split['pair']);expected=set(product((0,1),(-1,1)))if kind=='proxy'else set(product(pair,(0,1),(-1,1)))
   actual=[tuple(e['choice'])for e in restrictions]
   assert len(actual)==len(set(actual))==len(expected)and set(actual)==expected
   assert all(e['kind']==kind and e['pair']==list(pair)for e in restrictions)
   if kind=='proxy':PROXY.check_choices(actual)
   for child_idx,e in zip(children,restrictions):
    child=PROXY.proxy_child(after,pair,e['choice'],adapter)if kind=='proxy'else CORE.sat_child(after,pair,e['choice'],adapter)
    outcomes.append(visit(child_idx,child,idx,e))
  else:
   assert kind=='angle'and len(children)==2
   assert sorted(e['choice']for e in restrictions)==[0,1]
   owner=split['owner'];cut=F(split['cut'])
   assert all(e['kind']=='angle'and e['owner']==owner and F(e['cut'])==cut for e in restrictions)
   for child_idx,e in zip(children,restrictions):outcomes.append(visit(child_idx,angle_child(after,owner,cut,e['choice'],adapter),idx,e))
  closed=all(outcomes)
  if n['status']=='CANDIDATE_COVER_CLOSED':assert closed
  if closed:recomputed_closed.append(idx)
  covers.append(dict(index=idx,kind=kind,children=children,all_alternatives_present=True,shared_closed_faces_retained=True,excluded=closed))
  if len(audits)%20==0:print('CHECKED',len(audits),'NODES',len(leaves),'LEAVES',round(time.monotonic()-started,2),flush=True)
  return closed
 excluded=visit(0,state)
 assert visited==set(nodes)and frontier==set(pending)
 assert not manifest['whole_candidate_closed']or excluded
 for path,digest in bindings.items():assert sha(path)==digest
 BASE.verify_all_bindings();HEIGHT.verify_binding()
 for name,digest in checker.frozen_inventory.items():assert sha(BASE.OLD.PKG/name)==digest
 forbidden=('numpy','scipy','highspy','c_center_runtime','physical_center_disk_rows','ac_objective_unit_four_corner_runtime','physical_sat_engine_snapshot','physical_sat_diagonal_engine','c_height_exclusion_consequence_rows')
 assert not any(name in sys.modules for name in forbidden)
 dependencies={str(Path(m.__file__).resolve()):sha(m.__file__)for m in tuple(sys.modules.values())if getattr(m,'__file__',None)and Path(m.__file__).is_file()and '/research/nine/.runs/'in str(Path(m.__file__).resolve())}
 report=dict(status='PASS_COMPLETE_WHOLE_ORIGINAL_C887'if excluded else'PASS_PARTIAL_WHOLE_ORIGINAL_C887_COVER',original_id=TARGET,original_path=ROOT_PATH,original_mask='001/00',squared_radius='1105/256',whole_original_excluded=excluded,nodes=len(nodes),leaves=len(leaves),excluded_leaves=sum(v['excluded']for v in leaves),open_leaves=sum(not v['excluded']for v in leaves),unprocessed_leaves=len(frontier),stopped_leaves=len(stopped),complete_covers=dict(Counter(c['kind']for c in covers)),complete_excluded_subtrees=recomputed_closed,rounds=sum(v['rounds']for v in audits),deductions=sum(v['deductions']for v in audits),printed_rows_checked=sum(v['printed_rows_checked']for v in audits),fresh_original_ancestor=parent_audit,node_audits=audits,leaf_table=leaves,cover_audits=covers,input_sha256=bindings,checker_dependency_sha256=dependencies,original_source_relocation=source_map,manifest_snapshot_path=str(snapshot_path),manifest_snapshot_sha256=hashlib.sha256(manifest_bytes).hexdigest(),all_nine_originals_retained=True,all_36_corners_and_pairs_retained=True,all_five_cones_and_mask_bits_retained=True,no_other_original_consequence_imported=True,closed_shared_faces_retained=True,numerical_producer_imported=False,hand_review_and_publication_acceptance_separate=True,new_original_cells=0,new_masks=0,lean_lake_ci_run=False,seconds=time.monotonic()-started)
 output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in('status','nodes','excluded_leaves','open_leaves','deductions','printed_rows_checked','seconds')}),flush=True)
 return report

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('manifest',type=Path);ap.add_argument('output',type=Path);a=ap.parse_args();replay(a.manifest,a.output)
