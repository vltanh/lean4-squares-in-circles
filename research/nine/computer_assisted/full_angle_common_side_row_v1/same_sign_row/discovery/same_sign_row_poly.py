"""Discovery only: polynomial Bernstein certificate for an all-angle chiral row.
Exact checking is separate. All geometry is in a separately required hand proof.
"""
import os
for _key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[_key]='1'
from fractions import Fraction as F
import numpy as np
from math import comb
from itertools import product
from scipy.optimize import linprog
import time,json,sys,warnings
from scipy.optimize import OptimizeWarning
warnings.filterwarnings('ignore',category=OptimizeWarning,message='Unrecognized options detected.*')
S=F(5,12);SCALE=92000;U=F(131,1000);DIM=4;DEG=4;SHAPE=(5,)*4
ZERO=(0,)*4

def const(x):return {ZERO:int(x)}
def var(i,c=1,degree=1):
 e=[0]*4;e[i]=degree;return {tuple(e):int(c)}
def add(*ps):
 out={}
 for p in ps:
  for e,c in p.items():out[e]=out.get(e,0)+c
 return {e:c for e,c in out.items() if c}
def scale(p,c):return {e:c*v for e,v in p.items() if c*v}
def mul(p,q):
 out={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(a+b for a,b in zip(e,f));assert max(g)<=4,g
   out[g]=out.get(g,0)+c*d
 return {e:c for e,c in out.items() if c}
def prod(ps):
 o=const(1)
 for p in ps:o=mul(o,p)
 return o
def dense(p):
 o=np.zeros(SHAPE,dtype=np.int64)
 for e,c in p.items():o[e]=c
 return o

Dfac=[add(const(1),var(i,-1,4)) for i in range(4)]
Dpoly=prod(Dfac)

def polynomials(sg,owners,k):
 base=scale(Dpoly,-2*SCALE);ps=[]
 for j,o in enumerate(owners):
  i=j;n=j+1;q=n if o==i else i
  mixed=mul(var(i,sg[i]),var(n,sg[n]));one=add(const(1),mixed)
  delta=add(var(i,sg[i]),var(n,-sg[n]))
  rem=prod([add(const(1),var(o,1,2)),add(const(1),var(q,-1,2))]+[Dfac[v]for v in range(4) if v not in(i,n)])
  base=add(base,scale(mul(mul(one,one),rem),SCALE))
  ps.append(scale(mul(mul(one,delta),rem),SCALE))
 # Good oriented left endpoint: T_good-h=(-368+529x-1536x^2)/(736(1+x^2)).
 rem=prod([add(const(1),var(0,-1,2))]+[Dfac[v]for v in range(1,4)])
 good=add(const(-368),var(0,529),var(0,-1536,2))
 base=add(base,scale(mul(good,rem),125))
 # Unrestricted right endpoint uses the maximum of the accepted two tolls.
 rem=prod([add(const(1),var(3,-1,2))]+[Dfac[v]for v in range(3)])
 high=add(const(-23),var(3,-38),var(3,23,2))
 base=add(base,scale(mul(high,rem),2000))
 difference=add(var(3,143),var(3,-943,2))
 ps.append(scale(mul(difference,rem),250))
 rem=prod([add(const(1),var(k,1,2))]+[Dfac[v]for v in range(4) if v!=k])
 base=add(base,scale(mul(var(k),rem),-24104))
 return np.stack([dense(base)]+[dense(p)for p in ps])

def T(l,h):
 w=h-l;o=np.zeros((5,5))
 for j in range(5):
  for r in range(5):
   o[j,r]=sum(comb(r,m)*l**(r-m)*w**m*comb(j,m)/comb(4,m)for m in range(min(j,r)+1))
 return o

def transform(polys,box):
 b=polys.astype(float)/SCALE
 for axis,(l,h) in enumerate(box):
  M=T(l,h)
  b=np.moveaxis(np.tensordot(M,b,axes=([1],[axis+1])),0,axis+1)
 return b.reshape((5,-1))

def test(polys,box):
 b=transform(polys,box)
 grid=np.indices(SHAPE).reshape(4,-1)
 w=sum(l+(h-l)*grid[i]/4 for i,(l,h) in enumerate(box))
 A=np.c_[-b[1:].T,w];rhs=b[0]
 res=linprog([0,0,0,0,-1],A_ub=A,b_ub=rhs,bounds=[(-1,1)]*3+[(0,1)]+[(None,None)],method='highs',options={'threads':1})
 if not res.success:return None,0
 eps=res.x[:4];margin=res.x[4]
 if margin>1e-9:
  # Try a short exact dyadic set of combination weights, no true rounding is claimed here.
  for power in (12,16,20,24,30,40):
   W=2**power;nums=np.rint(eps*W).astype(np.int64);combo=b[0]+np.dot(nums/W,b[1:]);minimum=float(np.min(combo))
   weighted=float(np.min(combo[w>0]/w[w>0]))
   if minimum>=-1e-12 and weighted>1e-10:return {'weights':[int(v) for v in nums],'weight_power':power,'float_bernstein_min':minimum,'float_weighted_min':weighted},margin
 return None,margin

def run(sg,owners,k,budget=1000000):
 ps=polynomials(sg,owners,k);count=0;leaves=0;maxdepth=0;t0=time.monotonic();out=[];front=[]
 # Dyadic addresses use the common rational root [0,5/12].
 stack=[([(0,0)]*4,())]
 while stack and count<budget:
  addr,path=stack.pop();box=[(float(S)*n/2**d,float(S)*(n+1)/2**d)for n,d in addr]
  proof,margin=test(ps,box);count+=1;maxdepth=max(maxdepth,len(path))
  if proof is not None:
   leaves+=1;out.append({'path':list(path),**proof})
  else:
   # Use one-generation trial estimates to pick an axis when the box is narrow.
   widths=[h-l for l,h in box];axis=max(range(4),key=lambda i:widths[i])
   n,d=addr[axis]
   for side in (1,0):
    child=list(addr);child[axis]=(2*n+side,d+1);stack.append((child,path+((axis,side),)))
  if count%1000==0:print(json.dumps({'sg':sg,'owners':owners,'k':k,'nodes':count,'leaves':leaves,'stack':len(stack),'depth':maxdepth,'sec':round(time.monotonic()-t0,1)}),flush=True)
 for addr,path in stack:front.append({'path':list(path)})
 result={'schema':'four_row_chiral_polynomial_discovery_v1','root_upper':str(S),'variation_certified_candidate':str(U),'signs':sg,'owners':owners,'owner_for_max':k,'nodes':count,'maxdepth':maxdepth,'seconds':time.monotonic()-t0,'leaves':out,'frontier':front}
 return result

if __name__=='__main__':
 sg=json.loads(sys.argv[1]);owners=json.loads(sys.argv[2]);k=int(sys.argv[3]);budget=int(sys.argv[4])if len(sys.argv)>4 else 1000000
 r=run(sg,owners,k,budget);out=sys.argv[5]if len(sys.argv)>5 else 'same_sign_pilot.json';open(out,'w').write(json.dumps(r,separators=(',',':'))+'\n');print(json.dumps({k:v for k,v in r.items()if k not in('leaves','frontier')},indent=2));print('LEAVES',len(r['leaves']),'OPEN',len(r['frontier']),flush=True)
