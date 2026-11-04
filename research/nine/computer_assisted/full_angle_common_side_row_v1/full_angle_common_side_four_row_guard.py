"""Exact quantitative guards for the full-angle AHID row terminal.

Every bound must have ancestry from the unchanged original-nine001/00
caller, including actual EF/FG and their original center cones. This
module checks order and height bounds only; it is not a full caller proof.
"""
from fractions import Fraction as F
from itertools import product,permutations
CHAIN=(0,7,8,3)
THRESHOLD=F(13,100)
THEOREM_VERSION='full_angle_common_side_AHID_row_13_100_v1'
if not __debug__:raise RuntimeError('Exact guard evaluation requires assertions')
def threshold(value=THRESHOLD):
 value=F(value);assert 0<value<=THRESHOLD;return value

def box(raw):
 result=tuple(tuple(F(x)for x in p)for p in raw)
 assert all(len(p)==2 and p[0]<=p[1]for p in result)
 return result

def unpack(state):
 p=box(state['positions']);a=box(state['angles']);s=box(state['scalar'])
 assert len(p)==18 and len(a)==9 and len(s)==36
 raw=state.get('differences',{})
 ds=({tuple(r['pair']):box(r['intervals'])for r in raw}if isinstance(raw,list)
     else{tuple(k):box(v)for k,v in raw.items()})
 assert all(len(k)==2 and 0<=k[0]<k[1]<9 and len(v)==2 for k,v in ds.items())
 return p,ds

def difference(p,ds,i,j,ax):
 if i==j:return F(0),F(0)
 lo=p[2*j+ax][0]-p[2*i+ax][1];hi=p[2*j+ax][1]-p[2*i+ax][0]
 if i<j and(i,j)in ds:a,b=ds[i,j][ax];lo=max(lo,a);hi=min(hi,b)
 if i>j and(j,i)in ds:a,b=ds[j,i][ax];lo=max(lo,-b);hi=min(hi,-a)
 assert lo<=hi
 return lo,hi

def height_expressions():
 forms=[]
 for e0,e1,e2 in product((-1,1),repeat=3):
  forms.append(tuple(sorted((k,F(v))for k,v in((1,-e0),(15,e0-e1),(17,e1-e2),(7,e2))if v)))
 return tuple(forms)

def complement_rows(limit=THRESHOLD):
 limit=threshold(limit);rows=[]
 for k,(i,j)in enumerate(zip(CHAIN,CHAIN[1:])):
  rows.append((((2*j,F(1)),(2*i,F(-1))),F(0),'full_angle_AHID_order_'+str(k)))
 for k,terms in enumerate(height_expressions()):
  rows.append((tuple((i,-v)for i,v in terms),-limit,'full_angle_AHID_variation_'+str(k)))
 assert len(rows)==11
 return tuple(rows)

def expression_upper(terms,p,ds):
 best=sum(v*p[i][1 if v>0 else 0]for i,v in terms)
 positive=[];negative=[]
 for i,v in terms:
  assert i%2==1 and v.denominator==1
  (positive if v>0 else negative).extend([i//2]*abs(int(v)))
 assert len(positive)==len(negative)<=3
 for order in set(permutations(positive)):
  best=min(best,sum(difference(p,ds,i,j,1)[1]for i,j in zip(negative,order)))
 return best

def evaluate(state,limit=THRESHOLD):
 limit=threshold(limit);p,ds=unpack(state)
 orders=[difference(p,ds,i,j,0)for i,j in zip(CHAIN,CHAIN[1:])]
 uppers=[expression_upper(f,p,ds)for f in height_expressions()]
 variation=max(uppers);passed=all(lo>=0 for lo,hi in orders)and variation<=limit
 return dict(status='PASS_FULL_ANGLE_AHID_TERMINAL'if passed else'GUARD_NOT_IMPLIED',
  horizontal_order_intervals=[[str(x)for x in v]for v in orders],
  signed_height_upper_bounds=list(map(str,uppers)),certified_height_variation_upper=str(variation),
  variation_limit=str(limit),maximum_proved_variation=str(THRESHOLD),theorem_version=THEOREM_VERSION,
  endpoint_angles_unrestricted=True,short_row_actual_links_and_center_cones_required=True,
  full_original_ancestry_required=True,whole_original_cover_checked=False,new_original_cells=0,new_masks=0)
