#!/usr/bin/env python3
from pathlib import Path
import copy,hashlib,json
import verify_low_endpoint_central_position as verifier
HERE=Path(__file__).resolve().parent
p=HERE/'low_endpoint_central_position_cover.json';raw=p.read_bytes();data=json.loads(raw);checks=[]
def attempt(label,edit):
 d=copy.deepcopy(data);edit(d)
 try:verifier.verify(d)
 except(AssertionError,KeyError,IndexError,ValueError,TypeError,ZeroDivisionError)as exc:
  checks.append({'control':label,'rejected':True,'exception':type(exc).__name__});return
 raise RuntimeError('False certificate accepted: '+label)
for key,value in [('type','unrelated_cover'),('Q','17/4'),('gx','1/2'),('gy','1/3'),('proof_status','incomplete_checkpoint'),('remaining',1),('pending',[{'node':0,'depth':0}]),('root_indices',list(range(7)))]:
 attempt('changed_'+key,lambda d,k=key,v=value:d.__setitem__(k,v))
attempt('uncovered_central_boundary',lambda d:d['nodes'][7]['box'].__setitem__(2,'11/100'))
attempt('changed_physical_frame_sign',lambda d:d['nodes'][7].__setitem__('signs',[-1,-1]))
attempt('changed_small_angle_chart',lambda d:d['nodes'][7].__setitem__('chart',0))
attempt('invalid_split_dimension',lambda d:d['nodes'][7].__setitem__('split',4))
attempt('duplicated_child',lambda d:d['nodes'][7]['children'].__setitem__(1,d['nodes'][7]['children'][0]))
attempt('missing_child',lambda d:d['nodes'][7].__setitem__('children',d['nodes'][7]['children'][:1]))
def false_leaf(d):
 n=d['nodes'][7];replacement={'box':n['box'],'signs':n['signs'],'chart':n['chart'],'terminal':'strict_scalar','upper':'-1'};d['nodes'][7]=replacement
attempt('asserted_negative_whole_chart_is_recomputed',false_leaf)
report={'proof_status':'all_damaged_and_false_controls_rejected','certificate_sha256':hashlib.sha256(raw).hexdigest(),'control_count':len(checks),'controls':checks}
(HERE/'low_endpoint_central_position_controls.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
