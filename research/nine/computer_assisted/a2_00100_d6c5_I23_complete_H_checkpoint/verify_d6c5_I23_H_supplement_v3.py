#!/usr/bin/env python3
"""Compose the complete I23 H/I/D cover with the accepted fourteen-I checkpoint.

This rechecks pinned completed exact reports and every source, caller, closed
union and literal accounting attachment. It does not repeat weighted arithmetic.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from itertools import product
from collections import Counter
import argparse,json,subprocess,sys,time

HERE=Path(__file__).resolve().parent
ID='positive-6c5f13d07e5538df'
PATH=[['angle',3,1],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
PREFIX='d247d7e09ee9366a29164a26c3a776a36fd6dc1fbaa6c88e30190dfd8d9fa1df'
BASE_MANIFEST='99b9b662e0eb92767f85f220f42b3e07b765da3f8ae3449ec3963bbd60a64007'
BASE_MASTER='6663367a835f52efa0af4c529905b731c636205547db4a05024c546528e4e34a'
CORE_MANIFEST='4d30e61283571ca74986957f047ae848127ea7e65fba0fadebe364d6af708b7d'
I_COMPONENT='e73773f57e99797edcf5ee9726000c57ce212936b853c75247ff63ce9f16e0f4'
H_COMPONENT='4503752584c2df381a26253a3554dbb752bec917f1d644f177d5a86cddff1524'
SLOPE_COMPONENT='68cb272be836cd94ab1201ade1a13b6a1e4db2220c71097bb91240e10a41ebf1'
CONT_COMPONENT='85f801c1cd7dd5b8c5c2d75dc1218b476a62e47367356755ab8067feba901c21'
REPORT_PINS={
 'core/D6C5_ALL_H_I13_SLOPE_COMPONENT_EXACT_REPLAY.json':'a9a851e67e27caa69ba62aacd90c531828a57d1f9f9c9192de31f308c472da43',
 'core/D6C5_COMPLETED_I_GROUPS_EXACT_REPLAY.json':'94637ce3d9fee31f17199d056c1454db52c837668c01cd049f4a19df7afc2def',
 'core/D6C5_REMAINING_I_AND_NINE_EXACT_REPLAY.json':'45b2d4ecaf3898bc3a500f1112ba5e8f7a4f92d803ad9669f9609ce747a3c90f',
 'core/D6C5_I23_SIX_EXACT_REPLAY.json':'b821e79674e3a45f561de229eed539ba2bc46bd3320d1903cbd593e0f2985e68',
 'core/D6C5_I23_NINE_EXACT_REPLAY.json':'a819dc09f7a6b16e40e1af589e5cc556af16f103ff4377ec875ad4869324f1c0',
 'accepted_reports/D6C5_I23_D24_EXACT_REPLAY.json':'f364a3b8c6036c133391352e7d89f34566ecfa531572c4beac9d90bba153e38d'}
PHYSICAL_PROOFS={'physical_proofs/FOUR_ORIGINAL_PLANAR_MATCHING_AND_ENERGY_HAND_PROOF.md': 'c8e665a2abd2c67df541e612c874bc30b469f817cb6151cd77e21179533b0c18', 'physical_proofs/FOUR_ORIGINAL_PLANAR_ENERGY_INDEPENDENT_REVIEW.md': '5808a7fa00f490f508ae2c2612ed6aeb6ec352eff96960ff7be357676260cd28', 'physical_proofs/PHYSICAL_SQUARE_AREA_MOMENT_HAND_PROOF.md': '86f402efbf135228d2dd0d034fa55f56206c9176f4afe8354c4cf880b3fab293', 'physical_proofs/four_original_planar_rows_replay.json': '8fd1fb67b9675ab9daa8f9c4b368e398496c86755ef920ac5aa1e01cb65ade03', 'physical_proofs/square_area_moment_rows_replay.json': 'cbe05ea3e83c692e0d9d4666a198ed79e425d3d96380661cfcf9615f0212240d'}
digest=lambda p:sha256(Path(p).read_bytes()).hexdigest()
canonical=lambda v:json.dumps(v,sort_keys=True,separators=(',',':'))

def part(interval,index,parts):
 lo,hi=map(F,interval)
 assert lo<hi and type(index)is int and 0<=index<parts
 return list(map(str,(lo+(hi-lo)*F(index,parts),lo+(hi-lo)*F(index+1,parts))))

def counts(record):
 rounds=record['rounds'];assert [r['round']for r in rounds]==list(range(len(rounds)))
 premise=sum(len(r['printed_rows'])for r in rounds)
 terminal=len(record.get('terminal',{}).get('printed_rows',[]))
 return dict(rounds=len(rounds),deductions=sum(len(r['proposals'])for r in rounds),
  premise_rows=premise,terminal_rows=terminal,all_printed_rows=premise+terminal)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--report',type=Path,default=HERE/'I23_SUPPLEMENT_COMPOSITION_REPLAY.json')
 args=ap.parse_args();assert __debug__;started=time.monotonic()
 mp=HERE/'I23_SUPPLEMENT_MANIFEST.json';manifest_bytes=mp.read_bytes();mf=json.loads(manifest_bytes)
 assert mf['schema']=='D6c5_I23_H_I_D_supplement_frozen_inputs_v1';files=mf['files']
 def recheck():
  assert mp.read_bytes()==manifest_bytes
  for n,h in files.items():
   rel=Path(n);assert not rel.is_absolute()and'..'not in rel.parts
   p=(HERE/rel).resolve();assert p.is_relative_to(HERE)and digest(p)==h,n
 def read(n,expected=None):
  assert n in files
  raw=(HERE/n).read_bytes();assert sha256(raw).hexdigest()==files[n]
  if expected is not None:assert files[n]==expected
  return json.loads(raw)
 def bound(ref):
  assert set(ref)=={'packet_path','sha256'}
  return read(ref['packet_path'],ref['sha256'])
 recheck();assert files[Path(__file__).name]==digest(__file__)
 proof_binding=read('PHYSICAL_THEOREM_DEPENDENCIES.json')
 assert proof_binding['files']==PHYSICAL_PROOFS
 for name,expected in PHYSICAL_PROOFS.items():assert files[name]==expected

 bm=read('base/I21_SUPPLEMENT_MANIFEST.json',BASE_MANIFEST)
 assert len(bm['files'])==1456 and files['base/verify_d6c5_I21_H_supplement.py']==BASE_MASTER
 for n,h in bm['files'].items():assert files['base/'+n]==h
 cm=read('core/SHA256_MANIFEST.json',CORE_MANIFEST);assert len(cm['files'])==779
 for n,h in cm['files'].items():assert files['core/'+n]==h
 known_hashes=set(cm['files'].values())
 for h in(I_COMPONENT,H_COMPONENT,SLOPE_COMPONENT,CONT_COMPONENT):assert h in known_hashes
 for h in('a4b923589a52be57fb84e484c92f4438c275dbc13e5b01a8e9add9d4dd40edcb',
          '0d233bddea414938482cb312519da061a546d26c4ee5a5bb83a14b48c178ed02',
          'fd2e595cdd4d7bdc164defbcbec347ab5fd588a916ec64347b3165bcf6a9295a',
          'bb95fb217e91f19d85b69de9bf7db35efeade3a768488c23c5cf5940cdc557cf'):
  assert h in known_hashes
 reports={n:read(n,h)for n,h in REPORT_PINS.items()}
 for n,r in reports.items():
  assert r['status']=='PASS_ALL_LISTED_COMPONENTS_WITH_OPEN_STATES_RETAINED'
  assert r['original_id']==ID and r['all_input_hashes_unchanged']is True
  assert r['whole_original_closed']is False and r['new_original_cells']==r['new_masks']==0
  assert r['numerical_producer_or_optimizer_imported']is False
 final=reports['accepted_reports/D6C5_I23_D24_EXACT_REPLAY.json']
 assert final['manifest_sha256']==CORE_MANIFEST and final['frozen_inputs']==779
 assert final['listed_components']==final['exact_closed']==24 and final['exact_open']==0
 def exact(ref):
  assert set(ref)=={'packet_path','sha256','json_path'}
  name=ref['packet_path'];assert name in REPORT_PINS and REPORT_PINS[name]==ref['sha256']
  obj=reports[name]
  for key in ref['json_path']:
   assert type(key)in(str,int);obj=obj[key]
  assert isinstance(obj,dict)
  return obj
 by_hash={}
 for n,h in cm['files'].items():by_hash.setdefault(h,'core/'+n)
 def raw_hash(h):return read(by_hash[h],h)

 # Recompose the immutable fourteen-I assembly without repeating arithmetic.
 base_output=HERE/'base/I23_BASE_COMPOSITION_REPLAY.json'
 log=HERE/'BASE_FOURTEEN_COMPOSITION.log';assert not base_output.exists()and not log.exists()
 with log.open('x')as stream:
  subprocess.run([sys.executable,'-B','-S',str(HERE/'base/verify_d6c5_I21_H_supplement.py'),
   '--report',str(base_output)],cwd=HERE/'base',stdout=stream,stderr=subprocess.STDOUT,check=True)
 base=json.loads(base_output.read_text())
 # Correct only the older published I21 energy appendix, preserving its raw
 # reports and arithmetic. Recount every selected original row directly.
 previous=read('accepted_reports/PRIOR_FOURTEEN_I_NATIVE_COMPOSITION.json','0d743226fc0ed4a511cae42e0c6c5e41dd0330b299d5cd2ec1514870c7059ffc')
 correction=read('prior_I21_documentation_addendum/I21_ENERGY_TABLE_CORRECTION.json','d3ce2da22f85abc889bcea359c189cabbb186ec8413327f7f2f1a07ff8c23cbe')
 assert correction['manifest_sha256']==BASE_MANIFEST and correction['report_sha256']==files['accepted_reports/PRIOR_FOURTEEN_I_NATIVE_COMPOSITION.json']
 old_paths={}
 for n,h in bm['files'].items():old_paths.setdefault(h,'base/'+n)
 old_energy=Counter();old_labels=set();old_definitions=set();old_four=[]
 for selected in previous['selected_new_bound_records']:
  h=selected['certificate_sha256'];q=read(old_paths[h],h)
  for location,rows in [(f'round[{k}]',v['printed_rows'])for k,v in enumerate(q['rounds'])]+[('terminal',q.get('terminal',{}).get('printed_rows',[]))]:
   for row in rows:
    name=row['name'];family=next((p for p in('three_square_center_energy_','planar_four_center_sum_','four_center_energy_','square_area_moment_secant_')if name.startswith(p)),None)
    if family:
     old_energy[family]+=1;old_labels.add(name);old_definitions.add(canonical({k:row[k]for k in('name','coefficients','rhs')}))
     if family=='four_center_energy_':old_four.append(dict(record=h,location=location,row=row))
    else:assert 'energy'not in name,('unclassified_energy_row',name)
 assert len(previous['selected_new_bound_records'])==correction['all_new_selected_records']==32
 assert dict(old_energy)==correction['occurrences']=={'three_square_center_energy_':497,'four_center_energy_':9}
 assert len(old_labels)==correction['labels']==37 and len(old_definitions)==correction['distinct_definitions']==413
 assert old_four==correction['omitted_four_center_rows']

 assert base['status']=='PASS_FOURTEEN_EXCLUDED_I_RECTANGLES_WITH_TWO_OPEN_REMAINDERS'
 assert base['proof_mode']=='COMPOSITION_OF_PINNED_COMPLETED_EXACT_REPORTS'
 assert base['id']==ID and base['original_path']==PATH and base['original_prefix_sha256']==PREFIX
 assert base['exact_excluded_original_I_rectangles']==14 and base['remaining_original_I_tiles']==[[2,2],[2,3]]
 assert base['all_frozen_inputs_unchanged']and base['all_closed_faces_retained']
 assert base['physical_arithmetic_repeated']is False and base['whole_original_closed']is False
 recheck()
 index=read('I23_SUPPLEMENT_INDEX.json');table=read('COVER_TABLE.json')
 for d in(index,table):
  assert d['id']==ID and d['original_path']==PATH and d['original_prefix_sha256']==PREFIX
  assert d['new_original_cells']==d['new_masks']==0 and d['I_tile']==[2,3]
 assert index['schema']=='D6c5_I23_complete_H_I_D_cover_index_v1'
 parent_ref=index['parent_bound_record'];parent=bound(parent_ref)
 six=read('base/base/base/accepted_reports/D6C5_FRESH_SIX_ROUND_EXACT_REPLAY.json')['component_reports']
 parent_report=next(r for r in six if r['tile']==[2,3])
 assert parent_ref['sha256']==parent_report['certificate_sha256']
 assert parent_report['checker_sha256']==I_COMPONENT and parent_report['status']=='PASS_CERTIFIED_TILE_STATE_OPEN'
 assert parent_report['bound_rounds']==6 and parent['status']=='OPEN'and parent['id']==ID and parent['path']==PATH
 assert parent['prior']['sha256']==PREFIX and parent['prior']['tile']==[2,3]
 assert parent['final_test']['round']==len(parent['rounds'])==6
 irect=parent['prior']['rectangle'];hbox=parent['final']['positions'][14:16]
 assert index['I_rectangle']==table['I_rectangle']==irect
 assert index['H_parent_rectangle']==table['H_parent_rectangle']==hbox
 assert index['H_parts']==[2,4]and index['closed_faces_retained']is True
 assert [x['H_tile']for x in index['members']]==[list(t)for t in product(range(2),range(4))]
 assert [x['H_tile']for x in table['members']]==[x['H_tile']for x in index['members']]
 unique={};retained_prefixes=set();terminal_hashes=[];energy=Counter();energy_definitions={}
 def identity(r,q,tile,hrect):
  assert r['id']==q['id']==ID and r['original_parent_path']==q['path']==PATH
  assert r['tile']==list(tile)and r['rectangle']==irect and r['h_rectangle']==hrect
  assert q['prior']['sha256']==PREFIX and q['prior']['tile']==[2,3]
  assert q['prior']['rectangle']==irect and q['prior']['h_rectangle']is None
  assert r['original_prefix_replay']['certificate_sha256']==PREFIX
  assert r['new_original_cells']==r['new_masks']==0
  assert r['unfinished_rounds_admitted']is False and r['unsupported_rules_accepted']is False
  assert r['numerical_producer_or_optimizer_imported']is False
 def continuation(q):
  if 'derived_H_continuation'in q:
   ref=q['derived_H_continuation'];old=raw_hash(ref['sha256']);n=ref['inherited_local_rounds']
   assert old['rounds']==q['rounds'][:n]and len(old['rounds'])==n and old['status']=='OPEN'
   assert old['prior']==q['prior']and old['derived_H_cover']==q['derived_H_cover']
   assert old['final']==q['rounds'][n]['before']
   assert len(q['rounds'])<=n+ref['additional_local_round_budget']
   retained_prefixes.add(ref['sha256']);continuation(old)
  if 'continuation'in q:
   ref=q['continuation'];old=raw_hash(ref['sha256']);n=ref['inherited_rounds']
   assert old['status']=='OPEN'and old['schema']==ref['schema']
   assert old['rounds']==q['rounds'][:n]and len(old['rounds'])==n
   for k in('id','path','prior','slope_restriction'):assert old[k]==q[k]
   assert old['final']==q['rounds'][n]['before']
   assert 0<len(q['rounds'])-n<=ref['additional_round_budget']==3
   retained_prefixes.add(ref['sha256']);continuation(old)
 def account(q,r,role):
  h=r['certificate_sha256'];assert q==raw_hash(h)
  c=counts(q)
  assert c['rounds']==r['bound_rounds']and c['deductions']==r['bound_deductions']
  assert c['all_printed_rows']==r['printed_rows_checked']and c['terminal_rows']==r['terminal_rows']
  value=dict(certificate_sha256=h,**c)
  if h in unique:
   assert {k:v for k,v in unique[h].items()if k!='roles'}==value
   unique[h]['roles']=sorted(set(unique[h]['roles']+[role]))
  else:
   unique[h]=dict(value,roles=[role])
   for rows in [x['printed_rows']for x in q['rounds']]+[q.get('terminal',{}).get('printed_rows',[])]:
    for row in rows:
     name=row['name'];family=next((p for p in('three_square_center_energy_','planar_four_center_sum_','four_center_energy_','square_area_moment_secant_')if name.startswith(p)),None)
     if family:
      energy[family]+=1;energy_definitions.setdefault(name,{})[canonical(row)]=row
     else:assert 'energy'not in name,('unclassified_energy_row',name)
  continuation(q)
  return c
 def printed_terminal(p,q,r,role):
  c=account(q,r,role)
  assert p['certificate_sha256']==r['certificate_sha256']and p['local_counts']==c
  assert p['terminal_kind']==r['terminal_kind']and p['reserve']==r['reserve']
  if r['reserve']is not None:assert 0<F(p['positive_reserve_floor'])<=F(r['reserve'])
  else:assert p['positive_reserve_floor']is None
  terminal_hashes.append(r['certificate_sha256'])
 def check_restriction(q,r,parent_ref,parent_literal,original,index,interval):
  d=q['slope_restriction'];assert d==r['slope_restriction']
  assert d['kind']=='original_slope_closed_equal_partition'
  assert d['parent']['sha256']==parent_ref['sha256']and d['parent']['schema']==parent_literal['schema']
  assert d['original']==original and type(d['original'])is int and d['parts']==4
  assert d['index']==index and type(d['index'])is int
  assert d['parent_interval']==parent_literal['final']['angles'][original]
  assert d['interval']==interval==part(d['parent_interval'],index,4)
  assert d['all_other_inherited_bounds_retained']is True
  assert r['inherited_bound_parent_replay']['certificate_sha256']==parent_ref['sha256']
  assert r['all_inherited_bounds_retained_before_local_propagation']is True
 def check_H_state(q,r,href,tile,hrect):
  identity(r,q,tile,hrect)
  assert r['certificate_sha256']==href['sha256']and r['checker_sha256']==H_COMPONENT
  d=q['derived_H_cover']
  assert d['parent_bound_record']['sha256']==parent_ref['sha256']
  assert d['parent_h_rectangle']==hbox and d['h_rectangle']==hrect
  assert d['parts']==[2,4]and d['tile']==list(tile[2:])
  assert r['derived_parent_replay']['certificate_sha256']==parent_ref['sha256']
  assert r['all_inherited_bounds_retained_before_local_propagation']is True
 def walk_cover(node,printed,tile,hrect,depth):
  assert depth in(0,1)
  original=8 if depth==0 else 3
  assert node['kind']=='complete_slope_cover'and printed['kind']==node['kind']
  assert node['original']==printed['original']==original and node['parts']==printed['parts']==4
  pref=node['parent_bound_record'];q=bound(pref);r=exact(node['parent_exact_report'])
  identity(r,q,tile,hrect)
  assert r['certificate_sha256']==pref['sha256']and q['status']=='OPEN'
  assert q['final_test']['round']==len(q['rounds'])and q['final_test']['proposals']==[]
  assert q['final_test']['before']==q['final']==q['rounds'][-1]['after']
  if depth==0:
   check_H_state(q,r,pref,tile,hrect)
   assert r['status']=='PASS_CERTIFIED_TILE_STATE_OPEN'and len(q['rounds'])==6
  else:
   assert r['status']=='PASS_CERTIFIED_RESTRICTED_TILE_STATE_OPEN'and len(q['rounds'])==9
   assert r['checker_sha256']==CONT_COMPONENT
  assert printed['parent_counts']==account(q,r,'common_H6'if depth==0 else'common_I9')
  interval=q['final']['angles'][original]
  assert node['parent_interval']==printed['parent_interval']==interval
  assert [c['index']for c in node['children']]==list(range(4))
  assert [c['index']for c in printed['children']]==list(range(4))
  for child,pchild in zip(node['children'],printed['children']):
   i=child['index'];assert type(i)is int
   small=part(interval,i,4);assert child['interval']==pchild['interval']==small
   kind=child['kind'];assert pchild['kind']==kind
   if kind=='complete_slope_cover':
    assert depth==0
    cr=exact(child['parent_exact_report']);cq=bound(child['parent_bound_record'])
    check_restriction(cq,cr,pref,q,original,i,small)
    walk_cover(child,pchild,tile,hrect,1)
    continue
   cq=bound(child['certificate']);cr=exact(child['accepted_exact_report'])
   assert cr['certificate_sha256']==child['certificate']['sha256']
   assert kind=='accepted_bound_terminal'
   identity(cr,cq,tile,hrect);check_restriction(cq,cr,pref,q,original,i,small)
   assert cq['status']=='CANDIDATE_CLOSED'and cr['status']=='PASS_COMPLETE_RESTRICTED_PHYSICAL_TILE'
   assert cr['checker_sha256']in(SLOPE_COMPONENT,CONT_COMPONENT)
   if depth==1:assert cr['checker_sha256']==CONT_COMPONENT
   printed_terminal(pchild,cq,cr,'restricted_I_terminal'if depth==0 else'restricted_D_terminal')
 coverage=[]
 for member,printed in zip(index['members'],table['members']):
  hx,hy=member['H_tile'];tile=(2,3,hx,hy)
  hrect=[part(hbox[0],hx,2),part(hbox[1],hy,4)]
  assert member['H_rectangle']==printed['H_rectangle']==hrect
  assert member['kind']==printed['kind']
  if member['kind']=='accepted_bound_terminal':
   q=bound(member['certificate']);r=exact(member['accepted_exact_report'])
   check_H_state(q,r,member['certificate'],tile,hrect)
   assert q['status']=='CANDIDATE_CLOSED'and r['status']=='PASS_COMPLETE_PHYSICAL_TILE'
   printed_terminal(printed,q,r,'ordinary_H_terminal')
  else:walk_cover(member,printed,tile,hrect,0)
  coverage.append(dict(tile=list(tile),H_rectangle=hrect,kind=member['kind']))
 assert len(coverage)==8 and len(terminal_hashes)==len(set(terminal_hashes))==41
 assert len(unique)==52 and not(retained_prefixes&set(unique))
 assert parent_ref['sha256']not in unique
 total=Counter()
 for d in unique.values():total.update({k:d[k]for k in('rounds','deductions','premise_rows','terminal_rows','all_printed_rows')})
 assert dict(total)==table['new_selected_local_counts']and table['new_selected_bound_records']==52
 assert dict(energy)==table['selected_energy_row_occurrences']
 used=read('USED_ENERGY_ROWS.json')
 assert used['occurrences']==dict(energy)and used['labels']==len(energy_definitions)
 assert {n:set(map(canonical,rows))for n,rows in used['definitions'].items()}=={n:set(rows)for n,rows in energy_definitions.items()}
 combined={k:base['base_and_supplement_counts'][k]+total[k]for k in total}
 assert combined==table['base_and_supplement_counts']
 assert table['remaining_original_I_tiles']==[[2,2]]
 recheck();output=args.report.resolve();assert output.is_relative_to(HERE)and not output.exists()
 result=dict(schema='D6c5_I23_complete_H_I_D_supplement_assembly_v1',
  status='PASS_FIFTEEN_EXCLUDED_I_RECTANGLES_WITH_ONE_OPEN_REMAINDER',
  proof_mode='COMPOSITION_OF_PINNED_COMPLETED_EXACT_REPORTS',id=ID,original_path=PATH,original_prefix_sha256=PREFIX,
  base_composition_sha256=digest(base_output),base_manifest_sha256=BASE_MANIFEST,
  core_manifest_sha256=CORE_MANIFEST,component_report_sha256=REPORT_PINS,
  exact_supplemented_I_rectangles=1,complete_H_rectangles=8,ordinary_H_terminals=3,
  complete_I_angle_H_covers=5,complete_D_angle_I_subcovers=6,selected_terminal_domains=41,
  ordinary_restricted_or_normal_bound_terminals=41,accepted_sharp_terminals=0,
  coverage=coverage,selected_new_bound_records=[unique[h]for h in sorted(unique)],
  new_selected_local_counts=dict(total),base_and_supplement_counts=combined,
  selected_energy_occurrences=dict(energy),corrected_prior_I21_energy_occurrences=dict(old_energy),
  physical_theorem_dependencies=PHYSICAL_PROOFS,prior_I21_mathematical_sources_unchanged=True,exact_excluded_original_I_rectangles=15,
  remaining_original_I_tiles=[[2,2]],all_original_I_rectangles_accounted_for=16,
  all_closed_faces_retained=True,common_I6_antecedent_already_counted_in_base=True,
  shorter_same_domain_continuations_counted_again=False,retained_prefix_hashes=sorted(retained_prefixes),
  frozen_inputs=len(files),frozen_manifest_sha256=sha256(manifest_bytes).hexdigest(),
  all_frozen_inputs_unchanged=True,checker_sha256=digest(__file__),physical_arithmetic_repeated=False,
  whole_original_closed=False,whole_mask_closed=False,new_original_cells=0,new_masks=0,lean_lake_ci_run=False,
  seconds=time.monotonic()-started)
 output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k not in('coverage','selected_new_bound_records','retained_prefix_hashes')},indent=2))

if __name__=='__main__':main()
