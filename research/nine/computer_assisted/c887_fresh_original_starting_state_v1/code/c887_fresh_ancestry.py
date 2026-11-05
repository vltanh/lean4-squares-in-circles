"""Fresh independent C887 ancestry and necessary root-bound replay.
The missing archived strong state is never an assumption. All numerical
weights are checked as rational linear implications from original geometry.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,hashlib,subprocess,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import check_c887_complete_cover as CHECK
import independent_c_general_rows_adapter as EXT
import local_c_height_transport as TRANSPORT
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def from_view(v,adapter):
 box=lambda xs:tuple(tuple(map(F,x))for x in xs)
 s=dict(id=v['id'],path=v['path'],choices=adapter.choices(v['path']),angles=box(v['angles']),positions=box(v['positions']),scalar=box(v['scalar']),differences={tuple(x['pair']):box(x['intervals'])for x in v['differences']},diagonal={tuple(x['pair']):box(x['intervals'])for x in v['diagonal']})
 CHECK.CORE.valid_state(s);assert CHECK.CORE.state_view(s)==v;return s

def deficits(actual,target):
 bad=[];total=0
 for key in ('angles','positions','scalar'):
  assert len(actual[key])==len(target[key])
  for index,(a,t)in enumerate(zip(actual[key],target[key])):
   total+=1
   if not F(t[0])<=F(a[0])<=F(a[1])<=F(t[1]):bad.append(dict(kind=key,index=index,actual=a,target=t))
 for key in ('differences','diagonal'):
  targets={tuple(x['pair']):x['intervals']for x in target[key]}
  assert len(targets)==len(target[key])and set(targets)==set(tuple(x['pair'])for x in actual[key])
  for row in actual[key]:
   for axis,(a,t)in enumerate(zip(row['intervals'],targets[tuple(row['pair'])])):
    total+=1
    if not F(t[0])<=F(a[0])<=F(a[1])<=F(t[1]):bad.append(dict(kind=key,pair=row['pair'],axis=axis,actual=a,target=t))
 assert total==207;return bad

def replay_bounds(record_path,output_prefix):
 started=time.monotonic();transport=TRANSPORT.install(CHECK.HEIGHT);CHECK.BASE.verify_all_bindings();CHECK.HEIGHT.verify_binding()
 checker=CHECK.BASE.Checker();adapter=EXT.extend_adapter(CHECK.Adapter,allow_rotating=True)(checker)
 output_prefix=Path(output_prefix).resolve();script=HERE/'replay_c887_original_prefix.py';script_hash=sha(script)
 prefix_path=output_prefix.with_suffix('.original.json');prefix_log=output_prefix.with_suffix('.original.log')
 with prefix_log.open('w')as log:subprocess.run([sys.executable,'-B','-S',str(script),str(prefix_path)],check=True,stdout=log,stderr=subprocess.STDOUT)
 prefix=json.loads(prefix_path.read_text());assert prefix['status']=='PASS_FRESH_C887_ORIGINAL_PREFIX'and prefix['checker_sha256']==script_hash
 assert prefix['original_id']==CHECK.TARGET and prefix['original_path']==CHECK.ROOT_PATH
 inputs=dict(prefix['input_sha256']);inputs[str(script)]=script_hash
 height=CHECK.HEIGHT.replay_source_exclusions('c887',output_prefix.with_name(output_prefix.name+'_height'))
 assert height['status']=='PASS_FRESH_C_ORIGINAL_HEIGHT_EXCLUSION_CONSEQUENCES'
 inputs[height['source_report']['path']]=height['source_report']['sha256']
 inputs[str(CHECK.HEIGHT.BINDING)]=CHECK.HEIGHT.BINDING_SHA;inputs[str(CHECK.HEIGHT.LOADER)]=CHECK.HEIGHT.LOADER_SHA
 state=from_view(prefix['certified_original_state'],adapter)
 record_path=Path(record_path).resolve();raw=record_path.read_bytes();inputs[str(record_path)]=hashlib.sha256(raw).hexdigest();record=json.loads(raw)
 assert record['initial']==CHECK.CORE.state_view(state)
 assert not any('certified_original_root_bound_'in row['name']for rd in record['rounds']for row in rd['printed_rows'])
 audit,after=CHECK.CORE.check_record(record,state,adapter)
 for p,h in inputs.items():assert sha(p)==h
 for p,h in transport['input_sha256'].items():assert sha(p)==h
 assert sha(TRANSPORT.__file__)==transport['transport_source_sha256'];CHECK.BASE.verify_all_bindings();CHECK.HEIGHT.verify_binding();EXT.no_producers()
 report=dict(status='PASS_FRESH_C887_WHOLE_BOUND_EXCLUSION'if after is None else'PASS_FRESH_C887_WHOLE_NECESSARY_BOUNDS',original_id=state['id'],original_path=state['path'],certified_state=None if after is None else CHECK.CORE.state_view(after),fresh_original_ancestor=prefix,accepted_height_source=height,round_audit=audit,input_sha256=inputs,local_transport=transport,new_row_counts=dict(EXT.COUNTS),missing_archived_bound_state_assumed=False,all_nine_originals_retained=True,all_36_original_pairs_retained=True,no_selected_child_assumed=True,new_original_cells=0,new_masks=0,numerical_producer_imported=False,seconds=time.monotonic()-started)
 return report,after,adapter,checker
