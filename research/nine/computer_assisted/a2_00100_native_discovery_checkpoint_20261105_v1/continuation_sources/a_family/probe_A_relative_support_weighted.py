#!/usr/bin/env python3
"""One small A discovery round to exercise the new weighted literal family.
This is conditional on a saved state and does not replay its original ancestry.
"""
from pathlib import Path
import json,hashlib,sys,time
HERE=Path(__file__).resolve().parent
DRIVER=HERE/'run_conditional_global_corner_relative_v9.py'
source=DRIVER.read_text();assert source.endswith("g['main']()\n")
sys.argv=[str(DRIVER),'--h-component','3','--policy','I-owned']
namespace={'__name__':'frozen_v9_probe','__file__':str(DRIVER)}
exec(compile(source[:-len("g['main']()\n")],str(DRIVER),'exec'),namespace)
S=namespace['S'];E=namespace['STRONG'].E;g=namespace['g'];Context=namespace['FastContext']
source_tree=HERE/'a_c744_native_discovery_checkpoint_20261105T033547Z/trees/H3'
m=json.loads((source_tree/'manifest.json').read_text());n=m['nodes'][206]
raw=(source_tree/n['file']).read_bytes();assert hashlib.sha256(raw).hexdigest()==n['sha256'];old=json.loads(raw)
parent=Path(S.map_path(m['conditional_parent']['path']));praw=parent.read_bytes();assert hashlib.sha256(praw).hexdigest()==m['conditional_parent']['sha256']
whole=json.loads(praw)
context=Context(g['state_from_view'](whole['record']['final']),3)
state=g['state_from_view'](old['final']);started=time.monotonic()
rows,bounds,physical,term=context.collect(state);assert term is None
h,phase,point,term=E.phase_solve(rows,bounds);assert term is None,term
# Center objectives only:36 LPs rather than a full propagation pass.
after,record,terminal=E.bound_round(context,state,rows,bounds,physical,h,objective_limit=36)
new=[r for r in record['printed_rows'] if r['name'].startswith(namespace['RELATIVE'].PREFIX)]
out=HERE/'A_RELATIVE_SUPPORT_LOCAL_WEIGHTED_RECORD.json'
payload={'schema':'A_relative_support_local_weighted_probe_v1','source':{'path':str(source_tree/n['file']),'sha256':n['sha256'],'node':206,'H_component':3},'driver':{'path':str(DRIVER),'sha256':hashlib.sha256(DRIVER.read_bytes()).hexdigest()},'record':record,'terminal':terminal,'phase':phase,'seconds':time.monotonic()-started,'objective_limit':36,'new_rows':len(new),'ancestry_replayed':False,'new_original_cells':0,'new_masks':0}
out.write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'status':'LOCAL_DISCOVERY_ROUND_SAVED','deductions':len(record['proposals']),'new_family_rows':len(new),'seconds':payload['seconds'],'output':str(out)}),flush=True)
assert new,'No weighted new row; do not claim adoption check passed.'
