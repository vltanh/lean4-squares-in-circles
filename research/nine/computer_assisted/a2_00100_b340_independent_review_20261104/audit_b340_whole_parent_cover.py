#!/usr/bin/env python3
"""Independent structural/physical-source audit; does not redo weighted arithmetic."""
from pathlib import Path
from fractions import Fraction
from itertools import product
from collections import Counter
from copy import deepcopy
import argparse,hashlib,json,time
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--packet',required=True,type=Path,help='Extracted b340_complete_original_package directory')
ap.add_argument('--prior',required=True,type=Path,help='Extracted immutable prior directory')
ap.add_argument('--register',type=Path,help='Current register; defaults to the packet pre-acceptance snapshot')
ap.add_argument('--arithmetic-report',type=Path,help='Frozen independent report; defaults to the packet audit copy')
ap.add_argument('--output',required=True,type=Path)
args=ap.parse_args()
ROOT=args.packet.resolve()
PRIOR=args.prior.resolve()
LIVE=(args.register or ROOT/'accepted_repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json').resolve()
ARITHMETIC=(args.arithmetic_report or ROOT/'original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json').resolve()
OUT=args.output.resolve()
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
start=time.monotonic()
info=read(ROOT/'ORIGINAL_PROOF.json');im=read(ROOT/'INPUT_MANIFEST.json');pm=read(PRIOR/'SHA256_MANIFEST.json')
assert sha(ROOT/'INPUT_MANIFEST.json')=='0120b24b3764033ae6e8ae80f7395ace02f1e18a6466c2f39274639e65722667'
assert sha(PRIOR/'SHA256_MANIFEST.json')==info['prior_manifest_sha256']=='33272ed096ceb3f2dab6a16570ebe080a84677a033be5690ee63bfbdbf7bfc72'
for root,manifest in ((ROOT,im),(PRIOR,pm)):
 for name,h in manifest['files'].items():
  p=(root/name).resolve();assert p.is_relative_to(root.resolve());assert sha(p)==h,(name,h)
fields=('id','sign','baseline_frontier_index','path')
fd=info['current_definition_attachment']['frozen_definition'];old=read(PRIOR/fd['path']);live=read(LIVE)
assert sha(PRIOR/fd['path'])==fd['sha256']=='ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604'
assert len(old['cells'])==len(live['cells'])==231
assert [[c[k]for k in fields]for c in old['cells']]==[[c[k]for k in fields]for c in live['cells']]
original=[c for c in live['cells']if c['id']==info['original_id']];assert len(original)==1
original=original[0];assert original['status']in('OPEN','CLOSED') and original['path']==info['original_path']
frozen_original=[c for c in old['cells']if c['id']==info['original_id']]
assert len(frozen_original)==1 and frozen_original[0]['status']=='OPEN'
assert info['current_definition_attachment']['selected_original_status_before_acceptance']=='OPEN'
assert info['original_id']=='negative-'+hashlib.sha256(json.dumps(info['original_path'],separators=(',',':')).encode()).hexdigest()[:16]
entry=info['tree'];tpath=ROOT/entry['path'];assert sha(tpath)==entry['sha256'];tree=read(tpath)
alias=read(ROOT/'BINDINGS.json')
def resolve(ref):
 a=alias[ref['path']];p=(PRIOR if a['root']=='prior' else ROOT)/a['path'];assert sha(p)==ref['sha256'];return p
parent=read(resolve(tree['parent']));assert parent['schema']=='B_registered_original_initial_state_v1'
assert parent['id']==info['original_id'] and parent['path']==info['original_path']
assert parent['scope']=='WHOLE_UNCHANGED_ORIGINAL_PARENT'
entries=tree['nodes'];assert [e['index']for e in entries]==list(range(len(entries)))
visited=set();counts=Counter();terminals=Counter();totals=Counter();maximum_depth=0

def visit(index,expected,parent_index=None,depth=0,choice=None):
 global maximum_depth
 assert index not in visited;visited.add(index);maximum_depth=max(maximum_depth,depth)
 e=entries[index];p=tpath.parent/e['file'];assert sha(p)==e['sha256'];n=read(p)
 assert n['index']==index and n['depth']==depth and n['parent']==parent_index and n['choice']==choice
 assert n['initial']==expected==n['record']['initial']
 assert n['status']==e['status']
 r=n['record'];totals['rounds']+=len(r['rounds'])
 totals['deductions']+=sum(len(rr['proposals'])for rr in r['rounds'])
 if n['children']:
  assert n['status']=='CANDIDATE_COVER_CLOSED' and r['status']=='OPEN'
  assert n['complete_closed_children']is True and len(n['children'])==len(set(n['children']))
  final=r['final'];kind=n['split']['kind'];counts[kind]+=1
  if kind=='proxy':
   pair=n['split']['pair'];assert 0<=pair[0]<pair[1]<9
   cases=[list(c)for c in product((0,1),(-1,1))]
  elif kind=='sat':
   pair=n['split']['pair'];assert 0<=pair[0]<pair[1]<9
   cases=[list(c)for c in product(pair,(0,1),(-1,1))]
  else:
   assert kind=='angle';cases=[0,1];owner=n['split']['owner'];cut=Fraction(n['split']['cut']);lo,hi=map(Fraction,final['angles'][owner]);assert 0<=owner<9 and lo<cut<hi
  assert len(cases)==len(n['children'])
  for child,case in zip(n['children'],cases):
   exp=deepcopy(final)
   if kind in ('proxy','sat'):exp['path']=exp['path']+[[kind,pair,case]]
   else:
    exp['path']=exp['path']+[['angle_cut',[owner,str(cut)],case]]
    exp['angles'][owner]=[str(lo),str(cut)]if case==0 else[str(cut),str(hi)]
   visit(child,exp,index,depth+1,case)
 else:
  assert n['status']=='CANDIDATE_CLOSED' and r['status']=='CANDIDATE_CLOSED'
  terminals[r['terminal']['kind']]+=1
  if r['terminal']['kind']=='positive_exact_reserve':assert Fraction(r['terminal']['reserve'])>0
visit(0,parent['final'])
assert visited==set(range(len(entries)))
assert tree['completed']is True and tree['status']=='CANDIDATE_COVER_CLOSED'
assert len(visited)==403 and sum(terminals.values())==279
assert counts==dict(proxy=47,angle=67,sat=10)
assert totals==dict(rounds=400,deductions=67336)
report=read(ARITHMETIC)
assert report['complete']is True and report['whole_original_proved']is True and report['open_leaves']==0
assert report['initial_original_id']==info['original_id'] and report['initial_path']==info['original_path']
assert report['nodes']==len(visited) and report['complete_unions']==dict(counts)
assert sha(ARITHMETIC)=='5a1fd96d47b0472404a353c64452cfb1a2c2ae6a501987a8b1b12136da6a624f'
out=dict(status='PASS_INDEPENDENT_B340_WHOLE_PARENT_AND_CLOSED_COVER_REVIEW',original_id=info['original_id'],original_path=info['original_path'],live_register_sha256=sha(LIVE),selected_original_live_status=original['status'],frozen_231_definitions_equal_to_live=True,direct_registered_original_root=True,all_packet_inputs_rehashed=len(im['files']),all_prior_inputs_rehashed=len(pm['files']),node_hashes_checked=len(visited),visited_exactly_once=True,complete_closed_unions=dict(counts),terminal_leaves=sum(terminals.values()),open_leaves=0,terminal_kinds=dict(terminals),retained_bound_rounds=totals['rounds'],retained_bound_deductions=totals['deductions'],maximum_depth=maximum_depth,all_shared_angle_faces_retained=True,all_parent_intervals_retained_in_proxy_and_sat_children=True,all_paths_extend_exact_parent=True,independent_arithmetic_report_sha256=sha(ARITHMETIC),weighted_arithmetic_repeated_here=False,source_review='Registered initializer, whole-domain guard, lazy walker, exact bound core, three branch constructors, physical caller EDGES and f_side_escape_rows read independently. No narrowing of original caller or missing sibling found.',audit_code_sha256=sha(__file__),no_hardcoded_workspace_paths=True,no_lean_lake_ci=True,seconds=time.monotonic()-start)
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
