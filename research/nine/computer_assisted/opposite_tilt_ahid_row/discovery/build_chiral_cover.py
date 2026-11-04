from chiral_row_poly import run,polynomials,S,U
from itertools import product
from pathlib import Path
import json,time
folder=Path('/workspace/scratch/1b414599b857/whole_mask_work/chiral_cover');folder.mkdir(exist_ok=True)
rows=[];t0=time.monotonic()
for a,b in product((-1,1),repeat=2):
 signs=[1,a,b,-1]
 for choices in product((0,1),repeat=3):
  owners=[j+v for j,v in enumerate(choices)]
  for k in sorted(set(owners)):
   name='s'+''.join('p'if s>0 else'm'for s in signs)+'_o'+''.join(str(v)for v in owners)+'_k'+str(k)+'.json';p=folder/name
   if p.exists():r=json.loads(p.read_text())
   else:
    r=run(signs,owners,k,100000);p.write_text(json.dumps(r,separators=(',',':'))+'\n')
   row={'file':name,'signs':signs,'owners':owners,'k':k,'nodes':r['nodes'],'leaves':len(r['leaves']),'open':len(r['frontier']),'depth':r['maxdepth'],'seconds':r['seconds']};rows.append(row)
   print(json.dumps({'done':len(rows),**row}),flush=True)
manifest={'schema':'chiral_row_complete_cover_discovery_v1','root_upper':str(S),'strict_variation_candidate':str(U),'target_variation':'23/100','domains':rows,'nodes':sum(x['nodes']for x in rows),'leaves':sum(x['leaves']for x in rows),'open':sum(x['open']for x in rows),'seconds':time.monotonic()-t0,'proof_status':'UNVERIFIED_EXACT_REPLAY_REQUIRED'}
(folder/'DISCOVERY_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:v for k,v in manifest.items()if k!='domains'},indent=2))
