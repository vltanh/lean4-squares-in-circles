#!/usr/bin/env python3
"""Refine complete producer leaves until the distinct replay formula is sharp enough."""
from pathlib import Path
from fractions import Fraction as F
import json,time
import certify_low_endpoint_central_position as producer
import verify_low_endpoint_central_position as checker
HERE=Path(__file__).resolve().parent
p=HERE/'low_endpoint_central_position_cover.json';data=json.loads(p.read_text());assert data['proof_status']=='producer_complete_pending_independent_replay'
nodes=data['nodes'];todo=[];walk=[(i,0)for i in data['root_indices']]
while walk:
 i,depth=walk.pop();n=nodes[i]
 if'children'in n:walk.extend((k,depth+1)for k in n['children'])
 else:todo.append((i,depth))
original_nodes=len(nodes);original_leaves=len(todo);new_splits=checked=0;start=last=time.monotonic()
while todo:
 i,depth=todo.pop();n=nodes[i];box=tuple(map(F,n['box']));sg=n['signs'];ch=n['chart'];u=checker.upper(box,sg,ch);checked+=1
 if u<0:
  if'terminal'not in n:
   up,wide=producer.ceiling(box,sg,ch)
   if up<0:n.update(terminal='strict_scalar',upper=str(F(up,producer.ar.S)))
   else:n.update(terminal='strict_scalar',upper=str(u),refinement_arithmetic='independent_64_bit')
 else:
  assert depth<100,(i,depth,str(u));up,wide=producer.ceiling(box,sg,ch);mids=[(box[2*j]+box[2*j+1])/2 for j in range(4)]
  dim=max(range(4),key=lambda j:float(box[2*j+1]-box[2*j])*max(abs(wide.g[j].l),abs(wide.g[j].h))/producer.ar.S)
  left,right=list(box),list(box);left[2*dim+1]=mids[dim];right[2*dim]=mids[dim];li=len(nodes);ri=li+1
  n.pop('terminal',None);n.pop('upper',None);n.update(split=dim,children=[li,ri]);nodes.extend([{'box':list(map(str,left)),'signs':sg,'chart':ch},{'box':list(map(str,right)),'signs':sg,'chart':ch}]);todo.extend([(li,depth+1),(ri,depth+1)]);new_splits+=1
 now=time.monotonic()
 if now-last>=25:print('REFINE',checked,new_splits,len(todo),'seconds',round(now-start,1),flush=True);last=now
leaves=sum('terminal'in n for n in nodes);data.update(closed=leaves,processed=len(nodes),remaining=0,pending=[])
p.write_text(json.dumps(data,separators=(',',':'))+'\n')
report={'status':'complete_leaf_refinement_pending_fresh_replay','original_nodes':original_nodes,'original_leaves':original_leaves,'added_splits':new_splits,'final_nodes':len(nodes),'final_leaves':leaves,'seconds':time.monotonic()-start}
(HERE/'low_endpoint_central_position_refinement.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
