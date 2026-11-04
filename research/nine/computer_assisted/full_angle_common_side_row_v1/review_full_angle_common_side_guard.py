"""Separate rational checks of the full-angle AHID quantitative guards."""
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
import json,hashlib
import full_angle_common_side_four_row_guard as G
if not __debug__:raise RuntimeError('Exact guard review requires assertions')
def run():
 checks=0;rows=G.complement_rows();forms=[]
 expected_orders=(((14,F(1)),(0,F(-1))),((16,F(1)),(14,F(-1))),((6,F(1)),(16,F(-1))))
 for n,p in enumerate(expected_orders):assert rows[n]==(p,F(0),'full_angle_AHID_order_'+str(n));checks+=1
 for n,(a,b,c)in enumerate(product((-1,1),repeat=3)):
  p=tuple(sorted((k,F(v))for k,v in((1,-a),(15,a-b),(17,b-c),(7,c))if v));forms.append(p)
  assert rows[n+3]==(tuple((k,-v)for k,v in p),-F(13,100),'full_angle_AHID_variation_'+str(n));checks+=1
 assert tuple(forms)==G.height_expressions();checks+=1
 chain=(0,7,8,3)
 def state(xs,ys):
  p=[(F(0),F(0))for _ in range(18)]
  for i,x,y in zip(chain,xs,ys):p[2*i]=(x,x);p[2*i+1]=(y,y)
  return dict(positions=p,angles=[(F(-1),F(1))for _ in range(9)],scalar=[(F(-1),F(1))for _ in range(36)],differences=[])
 for ys in product((F(-13,200),F(0),F(13,200)),repeat=4):
  s=state((F(-3,2),F(-1,2),F(1,2),F(3,2)),ys);u=sum(abs(ys[j+1]-ys[j])for j in range(3))
  values=[sum(v*s['positions'][k][0]for k,v in p)for p in forms]
  assert max(values)==u;checks+=1
  r=G.evaluate(s);assert F(r['certified_height_variation_upper'])==u;checks+=1
  assert(r['status']=='PASS_FULL_ANGLE_AHID_TERMINAL')==(u<=F(13,100));checks+=1
 for xs in product((F(-1),F(0),F(1)),repeat=4):
  s=state(xs,(F(0),)*4);ordered=all(xs[j]<=xs[j+1]for j in range(3))
  assert(G.evaluate(s)['status']=='PASS_FULL_ANGLE_AHID_TERMINAL')==ordered;checks+=1
  if not ordered:assert any(sum(v*s['positions'][k][0]for k,v in p)<=b for p,b,_ in rows[:3]);checks+=1
 # All endpoint sign patterns, including broad intervals, are accepted.
 for a,b in product((F(-1),F(0),F(1)),repeat=2):
  s=state((F(-3,2),F(-1,2),F(1,2),F(3,2)),(F(0),)*4)
  s['angles'][0]=(a,a);s['angles'][3]=(b,b)
  assert G.evaluate(s)['status']=='PASS_FULL_ANGLE_AHID_TERMINAL';checks+=1
 s=state((F(-3,2),F(-1,2),F(1,2),F(3,2)),(F(0),)*4)
 for i in chain:s['positions'][2*i+1]=(F(-1),F(1))
 assert G.evaluate(s)['status']=='GUARD_NOT_IMPLIED';checks+=1
 for i,j in combinations(sorted(chain),2):
  dx=s['positions'][2*j][0]-s['positions'][2*i][0]
  s['differences'].append(dict(pair=[i,j],intervals=[(dx,dx),(F(0),F(0))]))
 assert G.evaluate(s)['status']=='PASS_FULL_ANGLE_AHID_TERMINAL';checks+=1
 for bad in(F(0),F(-1),F(131,1000)):
  try:G.complement_rows(bad)
  except AssertionError:checks+=1
  else:raise AssertionError('Unproved threshold accepted')
 assert F(131,1000)-F(13,100)==F(1,1000)>0;checks+=1
 assert F(1)-2*F(13,100)**2>0;checks+=1
 assert 2*46+F(27,2)==2*F(211,4);checks+=1
 assert F(55,64)-F(119,92)*F(5,12)==F(1415,4416)>0;checks+=1
 for x in(F(0),F(1,100),F(143,943),F(1,4),F(5,12)):
  al=(1-x*x)/(1+x*x);be=2*x/(1+x*x);h=(al+be)/2
  tg=F(55,64)*be-F(119,92)*(1-al)
  assert tg-h==(-368+529*x-1536*x*x)/(736*(1+x*x));checks+=1
  e4=(-23-38*x+23*x*x)/(46*(1+x*x));es=(-8-7*x-33*x*x)/(16*(1+x*x))
  assert e4==2*be/23-h and es==(9*be-41*(1-al))/32-h;checks+=2
  assert es-e4==x*(143-943*x)/(368*(1+x*x));checks+=1
  assert al*al+be*be==1 and al>0;checks+=1
 root=Path(__file__).parent
 report=dict(status='PASS_FULL_ANGLE_GUARD_AND_RATIONAL_IDENTITIES',checks=checks,closed_complement_domains=11,
  threshold='13/100',endpoint_angles_unrestricted=True,full_original_ancestry_required=True,
  new_original_cells=0,new_masks=0,sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(root/'full_angle_common_side_four_row_guard.py',Path(__file__))})
 return report
if __name__=='__main__':
 r=run();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
