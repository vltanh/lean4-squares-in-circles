#!/usr/bin/env python3
"""Bounded-memory C887 replay with unchanged exact physical cover semantics.

Only independently rebuilt physical rows and exact rational arithmetic decide
exclusion. Complete SAT unions and closed angle bisections are verified before
any whole-original conclusion. No producer, numerical optimizer, or floating
point operation is imported or used by this checker.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from copy import deepcopy
from collections import Counter
import argparse,hashlib,importlib,json,sys,time
HERE=Path(__file__).resolve().parent
PKG=HERE.parent/'c887/c887_whole_eight_checkpoint_package'
sys.path.insert(0,str(PKG))
import verify_cd_triple_energy_recursive_bounds as BASE
sys.path.insert(0,str(HERE))
import independent_physical_sat_diagonal_replay as SAT
import independent_coupled_three_square_energy as CT
import independent_tightened_sat_products as TP
import independent_shared_frame_triangle_products as TRI
import independent_relative_frame_arc_rows as ARC
import independent_physical_proxy_cover as PROXY
import independent_owner_free_relative_support as OF

TARGET='negative-887236b78100baf3'
TARGET_PATH=[['angle',3,0],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
ANCESTOR_SHA='9a5c4af1e23964ee661e4e1ae427265a29303b2a6f6bd5a65c5ece14177040a3'
SAT_CORE_SHA='a96a5ea5890553a7db6a0d22fb6245ec5b9b98851d5afc039d154989aab21301'
PKG_MANIFEST_SHA='d95bb23022ab5ba457c88139490e5147045069ce58bf3fef83c5ad1a3602c9c0'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

class Checker(BASE.Checker):
 def __init__(self):
  super().__init__(PKG,PKG/'ancestry')
  self.coupled_occurrences=0
  self.tightened_sat_occurrences=0
  self.triangle_sat_occurrences=0
  self.relative_arc_occurrences=0
  self.opposite_theorem_report=None
  self.active_choices=None
  self.active_positions=None
  self.owner_free_occurrences=0
  assert sha(PKG/'SHA256_MANIFEST.json')==PKG_MANIFEST_SHA
  self.frozen_inventory=json.loads((PKG/'SHA256_MANIFEST.json').read_text())['files']
  for name,h in self.frozen_inventory.items():assert sha(PKG/name)==h
  assert self.K.V.Q==F(1105,256)
  assert self.K.V.EDGES==((0,1,0),(1,2,0),(2,3,1),(4,5,0),(5,6,0))
  assert sha(SAT.__file__)==SAT_CORE_SHA
 def printed_rows(self,saved,total,base,bounds,scalar,diff,diagonal,angles):
  prefixes=('coupled_three_','tight_sat_','sat_triangle_product_','sat_relative_','owner_free_signed_','owner_free_folded_')
  regular=[r for r in saved if not r['name'].startswith(prefixes)]
  rows,names=super().printed_rows(regular,total,base,bounds,scalar,diff,diagonal,angles)
  rows.extend([((),F(0),'UNUSED_UNVERIFIED')]*max(0,max((r['index']for r in saved),default=-1)+1-len(rows)))
  for r in saved:
   if not r['name'].startswith(prefixes):continue
   k=r['index'];assert type(k)is int and len(base)<=k<total
   row=(tuple((i,F(v))for i,v in r['coefficients']),F(r['rhs']),r['name'])
   if r['name'].startswith('coupled_three_'):
    CT.verify_literal(row,diff,diagonal);self.coupled_occurrences+=1
   elif r['name'].startswith(('owner_free_signed_','owner_free_folded_')):
    assert self.active_positions is not None
    OF.verify_literal(row,self.active_positions,scalar,diff);self.owner_free_occurrences+=1
   else:
    assert self.active_choices is not None
    if r['name'].startswith('tight_sat_'):
     TP.verify_literal(row,self.active_choices,scalar,diff,diagonal);self.tightened_sat_occurrences+=1
    elif r['name'].startswith('sat_triangle_product_'):
     TRI.verify_literal(row,self.active_choices,scalar,diff,diagonal);self.triangle_sat_occurrences+=1
    else:
     ARC.verify_literal(row,self.active_choices,angles);self.relative_arc_occurrences+=1
   rows[k]=row;names.append(r['name'])

  return rows,names

class Adapter:
 def __init__(self,checker):
  self.checker=checker;self.K=checker.K
  self.R=importlib.import_module('review_guarded_frame_bounds_independent')
 def choices(self,path):return self.K.V.reconstruct(path)[2]
 def analytic(self,angles):return self.K.analytic(angles)
 def infer_angles(self,angles,scalar):return self.R.infer_angles(angles,scalar)
 def rebuild(self,state,printed):
  base,bounds,pos,scalar,diff,guards=self.K.rebuild(state['path'],state['angles'],state['positions'],
   state['choices'],state['scalar'],state['differences'])
  diagonal=self.checker.ID.intervals(diff,state['diagonal'])
  assert all(a<=b for ds in diagonal.values()for a,b in ds)
  total=max(len(base),max((r['index']+1 for r in printed),default=0))
  self.checker.active_choices=state['choices']
  self.checker.active_positions=pos
  rows,names=self.checker.printed_rows(printed,total,base,bounds,scalar,diff,diagonal,state['angles'])
  return {r['index']:rows[r['index']]for r in printed},bounds,dict(state,positions=pos,scalar=scalar,differences=diff,diagonal=diagonal)
 def verify_early_terminal(self,state,terminal):
  if terminal['kind']=='accepted_interval_terminal':
   _,_,label=self.R.collect_guarded(state['path'],state['angles'],state['positions'],state['choices'],state['scalar'])
   assert label is not None and terminal['label']==label
   return True
  if terminal['kind']=='empty_correlated_diagonal':
   _,_,pos,scalar,diff,_=self.K.rebuild(state['path'],state['angles'],state['positions'],state['choices'],state['scalar'],state['differences'])
   diagonal=self.checker.ID.intervals(diff,state['diagonal'])
   assert any(a>b for ds in diagonal.values()for a,b in ds)
   return True
  if terminal['kind']in('accepted_effective_angle_terminal','accepted_center_interval_terminal','empty_propagated_scalar','empty_propagated_difference'):
   V=self.K.V
   effective,label=V.effective_boxes(state['angles'],state['choices'],self.K.LEGACY)
   if terminal['kind']=='accepted_effective_angle_terminal':
    assert label is not None and terminal['label']==label
    return True
   assert label is None
   positions,hs,gs,label=V.center_bounds(effective,state['positions'],state['choices'],self.K.LEGACY)
   if terminal['kind']=='accepted_center_interval_terminal':
    assert label is not None and terminal['label']==label
    return True
   assert label is None
   if terminal['kind']=='empty_propagated_scalar':
    k=terminal['index'];assert type(k)is int and 0<=k<36
    a,b=state['scalar'][k];c,d=self.K.analytic(effective)[k]
    lo,hi=max(a,c),min(b,d)
   else:
    pair=tuple(terminal['pair']);axis=terminal['axis']
    assert len(pair)==2 and all(type(k)is int for k in pair)and 0<=pair[0]<pair[1]<9
    assert type(axis)is int and axis in(0,1)
    lo,hi=V.difference_bounds(pair,positions,gs,self.K.LEGACY)[axis]
    if pair in state['differences']:
     a,b=state['differences'][pair][axis];lo,hi=max(lo,a),min(hi,b)
   assert lo>hi and terminal['lower']==str(lo)and terminal['upper']==str(hi)
   return True
  if terminal['kind']=='accepted_opposite_tilt_AHID_terminal':
   _,_,positions,scalar,differences,_=self.K.rebuild(state['path'],state['angles'],state['positions'],state['choices'],state['scalar'],state['differences'])
   root=PKG/'opposite_tilt_theorem';sys.path.insert(0,str(root))
   guard=importlib.import_module('opposite_tilt_four_row_guard')
   assert Path(guard.__file__).resolve()==root/'opposite_tilt_four_row_guard.py'
   actual=guard.evaluate(dict(state,positions=positions,scalar=scalar,differences=differences))
   assert actual['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL'and terminal['guard']==actual
   if self.checker.opposite_theorem_report is None:
    table=importlib.import_module('verify_chiral_cover')
    assert Path(table.__file__).resolve()==root/'verify_chiral_cover.py'
    theorem=table.run(root/'cover')
    assert theorem['complete_domains']==80 and theorem['leaves']==1405 and theorem['coefficient_checks']==878125 and theorem['frontier']==0
    self.checker.opposite_theorem_report=theorem
   return True
  raise AssertionError(('unsupported exact terminal',terminal))

def angle_child(parent,owner,cut,side,adapter):
 assert type(owner)is int and 0<=owner<9 and type(side)is int and side in(0,1)
 cut=F(cut);lo,hi=parent['angles'][owner];assert lo<cut<hi
 result=deepcopy(parent);angles=list(result['angles'])
 angles[owner]=(lo,cut)if side==0 else(cut,hi)
 result['angles']=tuple(angles)
 result['path']=deepcopy(parent['path'])+[['angle_cut',[owner,str(cut)],side]]
 result['choices']=adapter.choices(result['path'])
 SAT.valid_state(result)
 return result

def replay(parent,tree,output):
 start=time.monotonic();parent=Path(parent).resolve();tree=Path(tree).resolve()
 mp=tree/'manifest.json';manifest=json.loads(mp.read_text())
 assert manifest['schema']=='same_original_physical_SAT_proxy_angle_tree_discovery_v1'
 assert manifest['id']==TARGET and manifest['original_path']==TARGET_PATH
 assert manifest['parent']['sha256']==sha(parent)==ANCESTOR_SHA
 assert manifest['new_original_cells']==manifest['new_masks']==0
 frozen=PKG/'ancestry/cd_family/diagonal_results'/f'{TARGET}.json'
 assert sha(frozen)==ANCESTOR_SHA
 checker=Checker();ancestor,state,diagonal=checker.D.replay(frozen)
 assert ancestor['status']=='PASS_CERTIFIED_PARENT_STATE_OPEN'
 assert state['id']==TARGET and state['path']==TARGET_PATH
 state=dict(state,diagonal=diagonal);adapter=Adapter(checker)
 bindings={str(parent):ANCESTOR_SHA,str(mp):sha(mp)}
 for name,h in manifest['source_sha256'].items():
  assert sha(name)==h;bindings[str(Path(name).resolve())]=h
 nodes={}
 for entry in manifest['nodes']:
  i=entry['index'];assert type(i)is int and i>=0 and i not in nodes
  assert entry['file']==f'node_{i:05d}.json'
  p=tree/entry['file'];assert sha(p)==entry['sha256']
  nodes[i]=entry;bindings[str(p)]=entry['sha256']
 visited=set();audits=[];covers=[]
 def visit(i,initial,parent_index=None,depth=0,restriction=None):
  assert i not in visited;visited.add(i);node=nodes[i]
  node_path=tree/node['file'];assert sha(node_path)==node['sha256']
  record=json.loads(node_path.read_text())
  assert node['parent']==parent_index and node['depth']==depth and node['restriction']==restriction
  assert record['id']==TARGET and record['original_path']==TARGET_PATH
  audit,after=SAT.check_record(record,initial,adapter)
  audit.update(index=i,parent=parent_index,depth=depth,restriction=restriction,
   terminal_kind=record.get('terminal',{}).get('kind'),terminal_label=record.get('terminal',{}).get('label'))
  audits.append(audit);children=node['children']
  assert isinstance(children,list)and len(children)==len(set(children))
  if after is None:
   assert children==[] and 'split'not in node and node['status']=='CANDIDATE_CLOSED'
   return True
  if not children:
   assert node['status']in('OPEN','OPEN_NO_SPLIT_SELECTED')and'split'not in node
   return False
  # Release the consumed node payload before recursive children.
  del record
  split=node['split'];assert node['complete_children']is True
  outcomes=[]
  if split['kind']=='complete_physical_proxy':
   pair=tuple(split['pair']);assert len(pair)==2 and all(type(x)is int for x in pair)and 0<=pair[0]<pair[1]<9
   actual=[]
   for k in children:
    r=nodes[k]['restriction'];assert set(r)=={'kind','pair','choice'}and r['kind']=='physical_proxy'and r['pair']==list(pair)
    actual.append(r['choice'])
   PROXY.check_choices(actual)
   for k in children:
    restriction=nodes[k]['restriction'];child=PROXY.proxy_child(after,pair,restriction['choice'],adapter)
    SAT.valid_state(child)
    outcomes.append(visit(k,child,i,depth+1,restriction))
   cover=dict(index=i,kind='complete_physical_proxy',pair=list(pair),all_four_original_inset_alternatives=True)
  elif split['kind']=='complete_physical_sat':
   pair=tuple(split['pair']);assert len(pair)==2 and all(type(x)is int for x in pair)and 0<=pair[0]<pair[1]<9
   expected=set(product(pair,(0,1),(-1,1)))
   actual=[]
   for k in children:
    r=nodes[k]['restriction'];assert set(r)=={'kind','pair','choice'}and r['kind']=='physical_sat'and r['pair']==list(pair)
    actual.append(tuple(r['choice']))
   assert len(children)==8 and len(set(actual))==8 and set(actual)==expected
   for k in children:
    restriction=nodes[k]['restriction'];child=SAT.sat_child(after,pair,restriction['choice'],adapter)
    outcomes.append(visit(k,child,i,depth+1,restriction))
   cover=dict(index=i,kind='complete_physical_sat',pair=list(pair),all_eight_alternatives=True)
  else:
   assert split['kind']=='closed_angle_bisection'
   owner=split['owner'];cut=F(split['cut']);assert type(owner)is int and 0<=owner<9
   lo,hi=after['angles'][owner];assert lo<cut<hi
   actual=[]
   for k in children:
    r=nodes[k]['restriction'];assert set(r)=={'kind','owner','cut','side'}
    assert r['kind']=='closed_angle'and r['owner']==owner and F(r['cut'])==cut
    assert type(r['side'])is int;actual.append(r['side'])
   assert len(children)==2 and sorted(actual)==[0,1]
   for k in children:
    restriction=nodes[k]['restriction'];child=angle_child(after,owner,cut,restriction['side'],adapter)
    outcomes.append(visit(k,child,i,depth+1,restriction))
   cover=dict(index=i,kind='closed_angle_bisection',owner=owner,parent_interval=[str(lo),str(hi)],cut=str(cut),shared_closed_face_retained=True)
  excluded=all(outcomes)
  assert node['status']==('CANDIDATE_COVER_CLOSED'if excluded else'OPEN')
  cover.update(children=children,closed_faces_retained=True,all_children_excluded=excluded);covers.append(cover)
  return excluded
 excluded=visit(0,state)
 assert visited==set(nodes)
 assert manifest['status']==('CANDIDATE_COVER_CLOSED'if excluded else'OPEN')
 forbidden=('numpy','scipy','highspy','v3_whole_parent_pass','ac_physical_context','physical_sat_engine_snapshot','physical_sat_diagonal_engine','ac_physical_context_diag','ac_physical_context_tight','coupled_three_square_energy','tightened_sat_products','shared_frame_triangle_products','relative_frame_arc_rows','ac_physical_context_complete','ac_physical_context_proxy','physical_proxy_branch','owner_free_relative_support_snapshot','ac_physical_context_ownerfree')
 assert not any(name in sys.modules for name in forbidden)
 for path,h in bindings.items():assert sha(path)==h
 frozen_manifest=json.loads((PKG/'ancestry/MANIFEST.json').read_text())
 for name,h in frozen_manifest['frozen_file_sha256'].items():assert sha(PKG/'ancestry'/name)==h
 assert sha(PKG/'SHA256_MANIFEST.json')==PKG_MANIFEST_SHA
 for name,h in checker.frozen_inventory.items():assert sha(PKG/name)==h
 dependencies={str(Path(m.__file__).resolve()):sha(m.__file__)for m in(BASE,SAT,CT,TP,TRI,ARC,PROXY,OF)}
 for name,module in tuple(sys.modules.items()):
  path=getattr(module,'__file__',None)
  if path and Path(path).resolve().is_relative_to(PKG):dependencies[str(Path(path).resolve())]=sha(path)
 dependencies[str(Path(__file__).resolve())]=sha(__file__)
 report=dict(schema='independent_C887_whole_original_SAT_closed_angle_tree_replay_v1',
  status='PASS_COMPLETE_WHOLE_ORIGINAL_C887'if excluded else'PASS_PARTIAL_WHOLE_ORIGINAL_C887_COVER',
  original_id=TARGET,original_path=TARGET_PATH,ancestor_replay=ancestor,nodes=len(nodes),
  leaf_domains=sum(not n['children']for n in nodes.values()),excluded_leaf_domains=sum(a['status']=='PASS_EXCLUDED_PHYSICAL_DOMAIN'for a in audits),
  complete_proxy_covers=sum(c['kind']=='complete_physical_proxy'for c in covers),
  complete_sat_covers=sum(c['kind']=='complete_physical_sat'for c in covers),closed_angle_covers=sum(c['kind']=='closed_angle_bisection'for c in covers),
  rounds=sum(a['rounds']for a in audits),deductions=sum(a['deductions']for a in audits),printed_rows_checked=sum(a['printed_rows_checked']for a in audits),
  coupled_row_occurrences_checked=checker.coupled_occurrences,
  owner_free_relative_support_occurrences_checked=checker.owner_free_occurrences,
  tightened_sat_row_occurrences_checked=checker.tightened_sat_occurrences,
  triangle_sat_row_occurrences_checked=checker.triangle_sat_occurrences,
  relative_frame_arc_row_occurrences_checked=checker.relative_arc_occurrences,opposite_tilt_theorem_replay=checker.opposite_theorem_report,all_nine_original_squares_retained=True,
  original_corner_predicates=36,original_pair_predicates=36,original_mask='001/00',closed_shared_faces_retained=True,
  input_sha256=bindings,checker_dependency_sha256=dependencies,audits=audits,covers=covers,
  node_payloads_replayed_lazily=True,
  numerical_discovery_fields_used=False,numerical_producer_imported=False,lean_lake_ci_run=False,
  new_original_cells=int(excluded),new_masks=0,seconds=time.monotonic()-start)
 Path(output).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k]for k in('status','nodes','leaf_domains','excluded_leaf_domains','complete_proxy_covers','complete_sat_covers','closed_angle_covers','rounds','deductions','printed_rows_checked','seconds')}),flush=True)
 return report

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('parent',type=Path);p.add_argument('tree',type=Path);p.add_argument('output',type=Path)
 a=p.parse_args();replay(a.parent,a.tree,a.output)
