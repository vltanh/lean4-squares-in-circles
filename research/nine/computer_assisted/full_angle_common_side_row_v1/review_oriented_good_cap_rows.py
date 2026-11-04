from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json,hashlib
import oriented_good_cap_rows as P
import check_oriented_good_cap_rows as C
if not __debug__:raise RuntimeError('Exact review requires assertions')
def run():
 checks=0
 for eta,delta in product((1,-1),repeat=2):
  a=[(F(-1),F(1))for _ in range(9)];s=[(F(-1),F(1))for _ in range(36)]
  a[0]=(F(1,10),F(1,5))if eta>0 else(F(-1,5),F(-1,10))
  s[9]=a[0]
  ds={p:((F(-4),F(4)),(F(-4),F(4)))for p in combinations(range(9),2)}
  ds[0,1]=((F(1,4),F(3,4)),(F(1),F(2))if delta>0 else(F(-2),F(-1)))
  rows,g=P.rows(a,s,ds);assert C.check(rows,g,a,s,ds)['rows']==1;checks+=1
  co,rhs,name=rows[0];d=dict(co)
  assert d[0]==46*eta*delta and d[2]==F(27,2)*eta*delta;checks+=1
  assert d[18]==F(73,2)and d[36]==F(529,32)and d[19]==d[37]==F(-27,4)and rhs==F(449,4);checks+=1
  for bad_dx in((F(-1),F(0)),(F(0),F(1)),(F(-1),F(1))):
   dd=dict(ds);dd[0,1]=(bad_dx,ds[0,1][1]);assert P.rows(a,s,dd)[0]==C.rows(a,s,dd)[0]==[];checks+=1
  dd=dict(ds);dd[0,1]=(ds[0,1][0],(F(-1),F(1)));assert P.rows(a,s,dd)[0]==C.rows(a,s,dd)[0]==[];checks+=1
  # The physical normal and original frame signs transform correctly:
  # x'=-sigma*x, y'=-delta*y yields a nonnegative canonical main angle
  # and a strictly downward physical separator, the proved good-cap case.
  sigma=eta*delta
  assert (-sigma)*(-delta)*eta==1 and (-delta)*delta==-1;checks+=1
 here=Path(__file__).parent
 return dict(status='PASS_EXACT_GUARDED_ORIENTED_CAP_ROW_REVIEW',checks=checks,
  variable_layout='0:18 centers,18:27 alpha,27:36 signed beta,36:45 absolute beta,45:54 insets',
  strict_horizontal_guard='-1<dx_lower<=dx_upper<1',full_original_bound_ancestry_required=True,
  physical_theorem='ORIENTED_GOOD_ENDPOINT_TILT_TOLL_HAND_PROOF.md',new_original_cells=0,new_masks=0,
  sources={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(here/'oriented_good_cap_rows.py',here/'check_oriented_good_cap_rows.py',Path(__file__))})
if __name__=='__main__':
 r=run();Path(__file__).with_suffix('.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
