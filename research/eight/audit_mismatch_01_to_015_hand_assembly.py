"""Exact state/angle union and mismatch contraction for the .1 to .015 gate.

This does not import the JavaScript verifier or a discovery routine. Every
angle bound and set union is recomputed with rational arithmetic.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from hashlib import sha256
from collections import Counter,defaultdict
import json

P=Path(__file__).resolve().parent
data=json.loads((P/'MISMATCH_01_TO_015_AFFINE_HAND_DATA.json').read_text())
report=json.loads((P/'MISMATCH_01_TO_015_AFFINE_HAND_COMPACT_REPORT.json').read_text())
assert data['Q']=='3.915534138'
assert data['cuts']=={'0':['0','1'],'1':['-4/5','-1/20'],'2':['0','1'],'3':['-1','0'],'4':['1/20','4/5'],'5':['-1','0'],'6':['-1','0']}
assert 'axis_domains' not in data
I={0,2,3,4,5}
assert data['beta']==['0.005' if i in I else '0' for i in range(7)]
assert data['difference_ranges']=={str(i):(['-1/10','1/10'] if i in I else ['-7/10','7/10']) for i in range(7)}
word=[0,1,0,1,0,1,1];assert data['word']==word
assert data['gamma']==['.8975928']*5+['.89759275','.8975917']
assert report['status']=='PASS' and not report['failures'] and report['cover']['status']=='PASS'
assert len(data['rows'])==report['rows']==report['passed']==107196
arcs={x['id']:x for x in data['arcs']};assert len(arcs)==len(data['arcs'])==335
for arc in arcs.values():
 assert arc['kind'] in ['C','O'] and arc['sign'] in [-1,1] and arc['role'] in range(7)
 lo,hi=map(F,[arc['lo'],arc['hi']]);assert 0<=lo<hi<=1
 if arc['kind']=='C':assert hi<=F(6,7) or lo>=F(6,7)
 for key in ['c','p','q']:F(arc[key])

def covers(pieces,lo,hi):
 if lo>hi:return True
 end=lo
 for a,b in sorted(pieces):
  if b<end:continue
  if a>end:return False
  end=max(end,b)
  if end>=hi:return True
 return False

state_unions=0
for i in range(7):
 l,h=map(F,data['cuts'].get(str(i),['-1','1']))
 assert l<h
 for kind in ['C','O']:
  for sign in [-1,1]:
   lo,hi=(l,h) if sign==1 else(-h,-l);lo,hi=max(F(0),lo),min(F(1),hi)
   if lo>=hi:continue
   pieces=[(F(a['lo']),F(a['hi'])) for a in arcs.values() if (a['role'],a['kind'],a['sign'])==(i,kind,sign)]
   assert covers(pieces,lo,hi),(i,kind,sign)
   state_unions+=1

def atan_series(x,n):return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n+1)),F(0))
pi_lo=16*atan_series(F(1,5),25)-4*atan_series(F(1,239),6)
pi_hi=16*atan_series(F(1,5),24)-4*atan_series(F(1,239),7)
assert 2*pi_hi<F(710,113)
P2=(pi_lo/2,pi_hi/2)
def outward(v,upper=False,den=10**22):
 n=v.numerator*den//v.denominator
 if upper and F(n,den)<v:n+=1
 return F(n,den)
P2=(outward(P2[0]),outward(P2[1],True))
atan_cache={}
def atan_interval(x):
 x=F(x)
 if x not in atan_cache:
  z=1+x*x;den=10**24;n=isqrt(z.numerator*den*den//z.denominator)
  lo,hi=F(n,den),F(n+1,den);assert lo*lo<=z<hi*hi
  yl,yh=x/(1+hi),x/(1+lo)
  al,ah=2*atan_series(yl,25),2*atan_series(yh,24)
  atan_cache[x]=(outward(al),outward(ah,True))
 return atan_cache[x]
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def point(x):return(F(x),F(x))
def alpha(a):
 lo,hi=atan_interval(a['lo']),atan_interval(a['hi'])
 return(lo,hi) if a['sign']==1 else(neg(hi),neg(lo))
domains={}
def needed(s,t,k,r):
 key=s['id'],t['id'],k,r
 if key not in domains:
  sl,sh=alpha(s);tl,th=alpha(t)
  fl=add(sub(point(F(19,25)),sh),tl)
  fh=add(sub(point(F(710,113)-F(114,25)),sl),th)
  base=P2 if k else point(0)
  lo,hi=(sub(fl,base),sub(fh,base)) if r==1 else(sub(base,fh),sub(base,fl))
  dl,dh=map(F,data['difference_ranges'][str(s['role'])])
  if r==-1:dl,dh=-dh,-dl
  domains[key]=(max(F(0),lo[0],dl),min(F(7,10),hi[1],dh))
 return domains[key]

groups=defaultdict(list)
for row in data['rows']:
 s,t=arcs[row['source']],arcs[row['target']];i=row['edge']
 assert s['role']==i and t['role']==(i+1)%7
 assert row['axis'] in [1,2,3,4] and row['k']==word[i] and row['r'] in [-1,1]
 assert F(row['lambda'])>=0
 lo,hi=map(F,[row['lo'],row['hi']]);assert 0<=lo<=hi<=F(7,10)
 assert row['mode'] in ['lower','upper','endpoints','circle']
 if row['mode']=='circle':
  assert F(row['h'])>0
  target=s if row['axis'] in [2,3] else t
  assert target['kind']=='O' or F(target['lo'])>=F(6,7)
 assert F(row.get('gamma',data['gamma'][i]))>=F(data['gamma'][i])
 groups[i,s['id'],t['id'],row['axis'],row['r']].append((lo,hi))

chain_count=0
for i,k in enumerate(word):
 for s in arcs.values():
  if s['role']!=i:continue
  for t in arcs.values():
   if t['role']!=(i+1)%7:continue
   for r in [-1,1]:
    lo,hi=needed(s,t,k,r)
    if lo>hi:continue
    for axis in [1,2,3,4]:
     assert covers(groups[i,s['id'],t['id'],axis,r],lo,hi),(i,s['id'],t['id'],axis,r)
     chain_count+=1
assert chain_count==101280==report['cover']['angle_chains']

assert len(report['row_records'])==len(data['rows'])
polys=[];cost=[]
for premises,costs in report['row_records']:
 assert costs
 polys+=premises+costs;cost+=costs
 for degree,bound in premises:
  assert isinstance(degree,int) and degree>=0 and F(bound)>=0
 for degree,bound in costs:
  assert isinstance(degree,int) and degree>=0 and F(bound)>0
assert len(polys)==report['polynomials']==292119
assert sum(p[0]+1 for p in polys)==report['coefficients']==2468184
for name,digest in report['sha256'].items():
 path=P/name
 # The large full coefficient output is an optional deterministic replay
 # artifact. The rational table and frozen verifier are always required.
 if name=='MISMATCH_01_TO_015_AFFINE_HAND_ARITHMETIC.json' and not path.exists():continue
 assert sha256(path.read_bytes()).hexdigest()==digest,(name,'hash mismatch')
gamma_sum=sum(map(F,data['gamma']),F(0));assert gamma_sum==F(125662969,20000000)
x=F(3,200);h_lower=x/2-x*x/4-x*x*x/12
assert h_lower==F(238191,32000000)
pi_upper=F('6.28318531')
machin_upper=32*atan_series(F(1,5),6)-8*atan_series(F(1,239),3)
assert 2*pi_hi<machin_upper<pi_upper
reserve=gamma_sum+F(1,200)*h_lower-pi_upper
assert reserve==F(2287,6400000000)>0
names=['MISMATCH_01_TO_015_AFFINE_HAND_DATA.json','MISMATCH_01_TO_015_AFFINE_HAND_COMPACT_REPORT.json','verify_mismatch_01_to_015_affine_hand.js']
out={'status':'PASS','scope':'Exact state and conditional angle domain union, rational input binding and mismatch contraction; polynomial arithmetic comes from the separately reviewed kernel',
 'Q':data['Q'],'word':word,'cuts':data['cuts'],'arcs':len(arcs),'state_unions':state_unions,
 'angle_chains':chain_count,'rows':len(data['rows']),'polynomials':len(polys),
 'printed_nonnegative_coefficients':sum(p[0]+1 for p in polys),
 'least_strict_cost_coefficient':str(min(F(p[1]) for p in cost)),
 'gamma_sum':str(gamma_sum),'mismatch_input_bound':'1/10','mismatch_output_strict_bound':'3/200','beta':'1/200','pi_upper':str(pi_upper),'h_lower_at_output':str(h_lower),'strict_contraction_reserve':str(reserve),
 'full_coefficient_replay_sha256':report['sha256']['MISMATCH_01_TO_015_AFFINE_HAND_ARITHMETIC.json'],
 'sha256':{n:sha256((P/n).read_bytes()).hexdigest() for n in names}}
(P/'MISMATCH_01_TO_015_AFFINE_HAND_ASSEMBLY_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
