#!/usr/bin/env python3
"""Actual sharp-leaf routing tests with explicitly non-arithmetic fixture states."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from types import SimpleNamespace
from copy import deepcopy
import argparse,importlib.util,json,shutil,sys,tempfile
HERE=Path(__file__).resolve().parent
sha=lambda p:sha256(Path(p).read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('dc71_v3_gate',HERE/'verify_dc71_original_cover_v3.py')
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
def main(source_context):
 source_context=Path(source_context).resolve()
 checks=[]
 def reject(name,call):
  try:call()
  except AssertionError:checks.append(dict(case=name,outcome='REJECTED'))
  else:raise AssertionError(('invalid sharp fixture accepted',name))
 with tempfile.TemporaryDirectory(prefix='dc71_sharp_gate_',dir=HERE)as temp:
  folder=Path(temp)
  for name,h in G.SHARP_PINS.items():
   source=source_context/name;assert sha(source)==h
   target=folder/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(source,target)
  obj=G.Assembly.__new__(G.Assembly);obj.packet=folder;obj.files=dict(G.SHARP_PINS);obj.touched={}
  sp=importlib.util.spec_from_file_location('shared_strict_row_terminal',folder/'shared_strict_row_terminal.py')
  M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M);sys.modules['shared_strict_row_terminal']=M
  centers=[(0,0),(1,2),(2,2),(3,0),(0,1),(1,1),(2,1),(1,0),(2,0)]
  state=dict(id=G.ID,path=deepcopy(G.PATH),positions=tuple((F(v),F(v))for p in centers for v in p),
   angles=tuple((F(0),F(0))for _ in range(9)),scalar=tuple((v,v)for v in [F(1)]*9+[F(0)]*18+[F(1,2)]*9),differences={})
  raw=dict(id=G.ID,path=deepcopy(G.PATH),status='OPEN',rounds=[],final_test=dict(round=0,proposals=[]))
  report=dict(status='PASS_CERTIFIED_RESTRICTED_TILE_STATE_OPEN',certificate_sha256='a'*64,original_prefix_replay=dict(certificate_sha256=G.PREFIX))
  count=[]
  def reconstruct(rr,st,diagonal):
   count.append(deepcopy(rr));return None,None,st['positions'],st['scalar'],st['differences'],None
  obj.slope=SimpleNamespace(reconstruct=reconstruct)
  original=deepcopy(raw)
  result=obj.accepted_sharp_guard(raw,report,state,{})
  assert result['guard']['row']==[0,7,8,3]and result['guard']['certified_variation_upper']=='0'
  assert raw==original and raw['status']=='OPEN'and len(count)==1
  checks.append(dict(case='same_OPEN_state_gets_separate_exact_AHID_terminal',outcome='PASS'))
  def wrong_record(field,value):
   r=deepcopy(raw);r[field]=value;return lambda:obj.accepted_sharp_guard(r,report,state,{})
  reject('raw_OPEN_status_cannot_be_rewritten',wrong_record('status','CANDIDATE_CLOSED'))
  r=deepcopy(report);r['status']='PASS_COMPLETE_RESTRICTED_PHYSICAL_TILE'
  reject('terminal_requires_replayed_OPEN_state',lambda:obj.accepted_sharp_guard(raw,r,state,{}))
  r=deepcopy(report);r['original_prefix_replay']['certificate_sha256']='b'*64
  reject('changed_original_prefix',lambda:obj.accepted_sharp_guard(raw,r,state,{}))
  s=deepcopy(state);s['path']=[]
  reject('changed_original_path',lambda:obj.accepted_sharp_guard(raw,report,s,{}))
  reject('unfinished_final_test',wrong_record('final_test',dict(round=0,proposals=[{}])))
  reject('wrong_final_test_round',wrong_record('final_test',dict(round=1,proposals=[])))
  s=deepcopy(state);s['positions']=list(s['positions']);s['positions'][15]=(F(2),F(2))
  reject('no_complete_accepted_height_guard',lambda:obj.accepted_sharp_guard(raw,report,s,{}))
  s=deepcopy(state);s['positions']=list(s['positions']);s['positions'][9]=(F(0),F(0))
  reject('shoulder_equality_not_silently_upgraded',lambda:obj.accepted_sharp_guard(raw,report,s,{}))
  s=deepcopy(state);s['positions']=list(s['positions']);s['positions'][14]=(F(-1),F(-1))
  reject('missing_main_order_guard',lambda:obj.accepted_sharp_guard(raw,report,s,{}))
  for name in G.SHARP_PINS:
   p=folder/name;saved=p.read_bytes();p.write_bytes(saved+b'\n')
   reject('changed_required_'+name,lambda:obj.accepted_sharp_guard(raw,report,state,{}));p.write_bytes(saved)
  old=M.__file__;M.__file__=str(folder/'different.py')
  reject('helper_import_outside_required_packet_path',lambda:obj.accepted_sharp_guard(raw,report,state,{}));M.__file__=old
  for name,h in G.SHARP_PINS.items():assert sha(folder/name)==h
 report=dict(schema='Dc71_accepted_sharp_leaf_focused_tests_v1',status='PASS_FOCUSED_SHARP_ATTACHMENT_TESTS',
  outer_source_sha256=sha(HERE/'verify_dc71_original_cover_v3.py'),test_source_sha256=sha(__file__),
  actual_pinned_guard_helper_sha256=G.SHARP_PINS['shared_strict_row_terminal.py'],cases=len(checks),checks=checks,
  scope='Assembly-only fixture states and reconstruction stub exercise the actual outer method and pinned exact guard evaluator; no physical parent or terminal arithmetic is claimed.',
  new_original_cells=0,new_masks=0,lean_lake_ci_run=False)
 out=HERE/'SHARP_LEAF_FOCUSED_TEST_RESULTS_V2.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(dict(status=report['status'],cases=len(checks),report_sha256=sha(out))))
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source-context',type=Path,required=True)
 main(parser.parse_args().source_context)
