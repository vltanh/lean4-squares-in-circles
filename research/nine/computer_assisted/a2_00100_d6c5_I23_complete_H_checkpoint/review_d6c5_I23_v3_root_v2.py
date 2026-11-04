"""Independent literal union/accounting/hand and portable archive review."""
from pathlib import Path, PurePosixPath
from fractions import Fraction as F
from collections import Counter,defaultdict
from hashlib import sha256
from datetime import datetime,timezone
import json,lzma,tarfile,time

ROOT=Path(__file__).resolve().parent
B=ROOT/'a_family/other_masks/d6c5_I23_H_supplement_v3'
META=ROOT/'a_family/other_masks/d6c5_I23_v3_archive_metadata'
ID='positive-6c5f13d07e5538df'
PATH=[['angle',3,1],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[1]]]
PREFIX='d247d7e09ee9366a29164a26c3a776a36fd6dc1fbaa6c88e30190dfd8d9fa1df'

def digest(p):
 h=sha256()
 with Path(p).open('rb')as s:
  while block:=s.read(1<<20):h.update(block)
 return h.hexdigest()

def part(interval,i,n):
 a,b=map(F,interval);assert a<b and 0<=i<n
 return list(map(str,(a+(b-a)*F(i,n),a+(b-a)*F(i+1,n))))

def counts(q):
 rs=q['rounds'];assert [r['round']for r in rs]==list(range(len(rs)))
 p=sum(len(r['printed_rows'])for r in rs);t=len(q.get('terminal',{}).get('printed_rows',[]))
 return dict(rounds=len(rs),deductions=sum(len(r['proposals'])for r in rs),premise_rows=p,terminal_rows=t,all_printed_rows=p+t)

def main():
 started=time.monotonic();mp=B/'I23_SUPPLEMENT_MANIFEST.json';mb=mp.read_bytes()
 assert sha256(mb).hexdigest()=='6abcc61af5923520746d14b378fee6b4f347b5ea44f77c74c16139a6443d8e57'
 files=json.loads(mb)['files'];assert len(files)==2255
 def recheck():
  assert mp.read_bytes()==mb;seen={}
  for n,h in files.items():
   p=B/n;assert p.resolve().is_relative_to(B)and p.is_file()
   st=p.stat();k=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns)
   if k not in seen:seen[k]=digest(p)
   assert seen[k]==h,n
 recheck();cache={}
 def read(n):
  if n not in cache:cache[n]=json.loads((B/n).read_text())
  return cache[n]
 def ref(d):
  assert files[d['packet_path']]==d['sha256'];return read(d['packet_path'])
 def exact(d):
  assert files[d['packet_path']]==d['sha256'];v=read(d['packet_path'])
  for key in d['json_path']:v=v[key]
  return v
 pins={'verify_d6c5_I23_H_supplement_v3.py':'8742d413d0df5f7785db7bacc22d810b12fa8990a1f36ab6d341287ac0d06ae2',
 'HAND_PROOF.md':'5d844d1b67e61baa94555a44716cc1220127fb64210035a1f9b15de92f525e7a',
 'COVER_TABLE.json':'ed7ca309d9adf672dcf493f089d1c6732a3a57a7eea1a6b8729d7aae6f32c18c'}
 for n,h in pins.items():assert files[n]==h
 report_path=B/'I23_SUPPLEMENT_COMPOSITION_REPLAY.json'
 assert digest(report_path)=='934d715f57fbe734ac6431793ea0cab61b782167a64285f89e67de458465eb5a'
 report=json.loads(report_path.read_text());idx=read('I23_SUPPLEMENT_INDEX.json');table=read('COVER_TABLE.json')
 assert report['status']=='PASS_FIFTEEN_EXCLUDED_I_RECTANGLES_WITH_ONE_OPEN_REMAINDER'
 assert report['remaining_original_I_tiles']==table['remaining_original_I_tiles']==[[2,2]]
 assert report['physical_arithmetic_repeated']is False and report['whole_original_closed']is False
 for v in [report,idx,table]:assert v['id']==ID and v['original_path']==PATH and v['original_prefix_sha256']==PREFIX
 parent=ref(idx['parent_bound_record']);assert parent['prior']['tile']==[2,3]
 assert idx['I_rectangle']==table['I_rectangle']==parent['prior']['rectangle']
 hbox=parent['final']['positions'][14:16];assert idx['H_parent_rectangle']==table['H_parent_rectangle']==hbox
 assert idx['H_parts']==[2,4]and idx['closed_faces_retained']
 selected={};terminals=[];unions=Counter();hand_lines=[]
 def account(q,r):
  assert r['id']==q['id']==ID and q['path']==r['original_parent_path']==PATH
  assert q['prior']['sha256']==PREFIX and q['prior']['tile']==[2,3]
  assert not r['unfinished_rounds_admitted']and not r['unsupported_rules_accepted']
  c=counts(q);h=r['certificate_sha256']
  assert (c['rounds'],c['deductions'],c['all_printed_rows'],c['terminal_rows'])==(r['bound_rounds'],r['bound_deductions'],r['printed_rows_checked'],r['terminal_rows'])
  if h in selected:assert selected[h][0]==q
  selected[h]=(q,c);return c
 def walk(node,printed,label,depth,hrect):
  assert node['kind']==printed['kind']
  if node['kind']=='accepted_bound_terminal':
   q=ref(node['certificate']);r=exact(node['accepted_exact_report']);h=node['certificate']['sha256']
   assert h==r['certificate_sha256']==printed['certificate_sha256']
   assert q['status']=='CANDIDATE_CLOSED'and r['status']in('PASS_COMPLETE_PHYSICAL_TILE','PASS_COMPLETE_RESTRICTED_PHYSICAL_TILE')
   assert r['h_rectangle']==hrect and r['rectangle']==idx['I_rectangle']
   c=account(q,r);assert c==printed['local_counts'];assert r['reserve']==printed['reserve']
   if r['reserve']is not None:assert 0<F(printed['positive_reserve_floor'])<=F(r['reserve'])
   else:assert printed['positive_reserve_floor']is None
   end=printed['positive_reserve_floor']if r['reserve']is not None else printed['terminal_label']
   hand_lines.append('| '+label+' | '+' | '.join(str(c[k])for k in ['rounds','deductions','premise_rows','terminal_rows'])+' | '+end+' |')
   terminals.append(h);return
  assert node['kind']=='complete_slope_cover'and depth in(0,1)
  orig=8 if depth==0 else 3;unions[orig]+=1
  assert node['original']==printed['original']==orig and node['parts']==printed['parts']==4
  pref=node['parent_bound_record'];q=ref(pref);r=exact(node['parent_exact_report'])
  assert q['status']=='OPEN'and r['certificate_sha256']==pref['sha256']
  assert q['final']==q['final_test']['before']==q['rounds'][-1]['after']
  assert q['final_test']['round']==len(q['rounds'])==(6 if depth==0 else 9)
  assert printed['parent_counts']==account(q,r)
  interval=q['final']['angles'][orig];assert node['parent_interval']==printed['parent_interval']==interval
  assert [c['index']for c in node['children']]==[c['index']for c in printed['children']]==list(range(4))
  for c,p in zip(node['children'],printed['children']):
   small=part(interval,c['index'],4);assert c['interval']==p['interval']==small
   cref=c['parent_bound_record']if c['kind']=='complete_slope_cover'else c['certificate'];cq=ref(cref);d=cq['slope_restriction']
   assert d['parent']['sha256']==pref['sha256']and d['parent']['schema']==q['schema']
   assert d['original']==orig and d['parts']==4 and d['index']==c['index']
   assert d['parent_interval']==interval and d['interval']==small and d['all_other_inherited_bounds_retained']
   walk(c,p,label+('/I4:'if orig==8 else'/D4:')+str(c['index']),depth+1,hrect)
 expected_tiles=[[x,y]for x in range(2)for y in range(4)]
 assert [m['H_tile']for m in idx['members']]==[m['H_tile']for m in table['members']]==expected_tiles
 for node,printed,(x,y)in zip(idx['members'],table['members'],expected_tiles):
  rectangle=[part(hbox[0],x,2),part(hbox[1],y,4)]
  assert node['H_rectangle']==printed['H_rectangle']==rectangle
  walk(node,printed,'I23H'+str(x)+str(y),0,rectangle)
 assert len(terminals)==len(set(terminals))==41 and len(selected)==52 and unions=={8:5,3:6}
 hand=(B/'HAND_PROOF.md').read_text()
 assert [s for s in hand.splitlines()if s.startswith('| I23H')]==hand_lines
 total=Counter();energy=Counter();definitions=defaultdict(set);normalized=set();canon=lambda v:json.dumps(v,sort_keys=True,separators=(',',':'))
 for q,c in selected.values():
  total.update(c)
  for rows in [r['printed_rows']for r in q['rounds']]+[q.get('terminal',{}).get('printed_rows',[])]:
   for row in rows:
    name=row['name'];family=next((s for s in ['three_square_center_energy_','four_center_energy_','planar_four_center_sum_','square_area_moment_secant_']if name.startswith(s)),None)
    if family:
     energy[family]+=1;definitions[name].add(canon(row));normalized.add(canon({k:row[k]for k in ['name','coefficients','rhs']}))
    else:assert 'energy'not in name
 assert dict(total)==report['new_selected_local_counts']==table['new_selected_local_counts']
 assert dict(total)==dict(rounds=194,deductions=29470,premise_rows=43124,terminal_rows=734,all_printed_rows=43858)
 assert not(set(report['retained_prefix_hashes'])&set(selected))
 assert {r['certificate_sha256']for r in report['selected_new_bound_records']}==set(selected)
 used=read('USED_ENERGY_ROWS.json');assert dict(energy)==used['occurrences']==report['selected_energy_occurrences']==table['selected_energy_row_occurrences']
 assert energy=={'three_square_center_energy_':347,'four_center_energy_':10,'square_area_moment_secant_':3}
 assert len(definitions)==used['labels']==36 and len(normalized)==255
 assert {k:set(map(canon,v))for k,v in used['definitions'].items()}==definitions
 bm=read('base/I21_SUPPLEMENT_MANIFEST.json');oldmap={}
 for n,h in bm['files'].items():oldmap.setdefault(h,'base/'+n)
 old=read('accepted_reports/PRIOR_FOURTEEN_I_NATIVE_COMPOSITION.json');correction=read('prior_I21_documentation_addendum/I21_ENERGY_TABLE_CORRECTION.json')
 oldcount=Counter();oldlabels=set();olddefs=set();four=[]
 assert len(old['selected_new_bound_records'])==32
 for item in old['selected_new_bound_records']:
  h=item['certificate_sha256'];q=read(oldmap[h])
  for location,rows in [(f'round[{i}]',r['printed_rows'])for i,r in enumerate(q['rounds'])]+[('terminal',q.get('terminal',{}).get('printed_rows',[]))]:
   for row in rows:
    name=row['name'];family=next((s for s in ['three_square_center_energy_','four_center_energy_','planar_four_center_sum_','square_area_moment_secant_']if name.startswith(s)),None)
    if family:
     oldcount[family]+=1;oldlabels.add(name);olddefs.add(canon({k:row[k]for k in ['name','coefficients','rhs']}))
     if family=='four_center_energy_':four.append(dict(record=h,location=location,row=row))
    else:assert 'energy'not in name
 assert oldcount=={'three_square_center_energy_':497,'four_center_energy_':9}
 assert dict(oldcount)==correction['occurrences']and four==correction['omitted_four_center_rows']
 assert len(oldlabels)==37 and len(olddefs)==413
 proofs=read('PHYSICAL_THEOREM_DEPENDENCIES.json')['files'];assert len(proofs)==5
 assert proofs==report['physical_theorem_dependencies']
 for n,h in proofs.items():assert files[n]==h
 review=ROOT/'b_family/D6C5_I23_V3_SOURCE_HAND_TABLE_ENERGY_REVIEW.json'
 assert digest(review)=='ccc716f83ce19fc9bfb2d281ca1f9f49f4b4911f6a33d39237e19e421b255214'
 recheck()
 receipt_path=META/'PORTABLE_ARCHIVE_BUILD_RECEIPT.json'
 assert digest(receipt_path)=='1298f8975725a40631a31928eed85eb55b332975b7c1c2cc016e2c600604b1e6'
 receipt=json.loads(receipt_path.read_text());archive=Path(receipt['archive'])
 assert digest(archive)=='c58aedd5dd0d5efc3dbc0422703ced905f31667e77de303387ce4b377c34993d'
 expected={n:v['sha256']for n,v in receipt['member_source_map'].items()}
 assert len(expected)==2272;prefix='d6c5_I23_H_supplement_v3/';checked={};regular=links=bytes_read=0
 with lzma.open(archive,'rb')as stream:
  with tarfile.open(fileobj=stream,mode='r|')as tar:
   for item in tar:
    assert item.name.startswith(prefix)and '..'not in PurePosixPath(item.name).parts
    name=item.name[len(prefix):];assert name in expected and name not in checked
    assert item.uid==item.gid==item.mtime==0 and item.mode in (0o444,0o555)
    if item.isfile():
     h=sha256();payload=tar.extractfile(item);count=0
     while block:=payload.read(1<<20):h.update(block);count+=len(block)
     assert count==item.size;actual=h.hexdigest();regular+=1;bytes_read+=count
    else:
     assert item.islnk()and item.linkname.startswith(prefix)
     target=item.linkname[len(prefix):];assert target in checked
     actual=checked[target];links+=1
    assert actual==expected[name],name;checked[name]=actual
  while stream.read(1<<20):pass
 assert checked==expected and (regular,links,bytes_read)==(575,1697,852190109)
 assert expected['ARCHIVE_MANIFEST.json']==receipt['archive_manifest_sha256']
 assert expected['accepted_reviews/'+review.name]==digest(review)
 result=dict(schema='D6c5_I23_v3_root_literal_physical_hand_and_archive_review_v1',status='PASS_COMPLETE_I23_WITH_I22_EXPLICITLY_OPEN',
  checked_at=datetime.now(timezone.utc).isoformat(),input_manifest_sha256=sha256(mb).hexdigest(),frozen_inputs=2255,
  master_sha256=pins['verify_d6c5_I23_H_supplement_v3.py'],native_composition_sha256=digest(report_path),
  full_changed_source_and_physical_hand_read=True,all_eight_H_products_and_eleven_frame_unions_recomputed=True,
  all_41_hand_terminal_rows_match_raw_records=True,selected_records=52,selected_counts=dict(total),
  energy_occurrences=dict(energy),energy_labels=36,energy_definitions=255,
  prior_I21_energy_occurrences=dict(oldcount),prior_I21_omitted_four_rows_exactly_reproduced=9,
  physical_premise_files=proofs,all_input_hashes_unchanged=True,archive_sha256=digest(archive),archive_members=2272,
  every_archive_payload_and_safe_prior_hardlink_checked=True,complete_XZ_footer_consumed=True,
  prior_I21_arithmetic_and_source_bytes_unchanged=True,weighted_arithmetic_repeated_by_root=False,
  exact_excluded_original_I_rectangles=15,remaining_original_I_tiles=[[2,2]],whole_original_closed=False,
  new_original_cells=0,new_masks=0,seconds=time.monotonic()-started)
 out=ROOT/'D6C5_I23_V3_ROOT_COMPLETE_REVIEW_V2.json';assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result),flush=True);print('REVIEW_SHA256',digest(out),flush=True)

if __name__=='__main__':main()
