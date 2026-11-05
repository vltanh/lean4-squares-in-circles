"""Exact Bernstein discovery for two physical row links and one actual link.
No floating point or optimizer is used. Independent reconstruction is separate.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
from pathlib import Path
import json,time,argparse
DIM=3;DEG=4;N=125;S=F(29,70);LAMBDA=F(641,1000);SCALE=736000
ZERO=(0,0,0);INDICES=list(product(range(5),repeat=3))
def const(x):return {ZERO:int(x)}
def var(i,c=1,power=1):
 e=[0]*3;e[i]=power;return {tuple(e):int(c)}
def add(*ps):
 ans={}
 for p in ps:
  for e,c in p.items():ans[e]=ans.get(e,0)+c
 return {e:c for e,c in ans.items()if c}
def scale(p,c):return {e:int(c)*v for e,v in p.items()if c*v}
def mul(p,q):
 ans={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(a+b for a,b in zip(e,f));assert max(g)<=4
   ans[g]=ans.get(g,0)+c*d
 return {e:c for e,c in ans.items()if c}
def prod(ps):
 ans=const(1)
 for p in ps:ans=mul(ans,p)
 return ans
Dfac=[add(const(1),var(i,-1,4))for i in range(3)]
Dpoly=prod(Dfac)
def polynomials(signs,owners,k):
 base=scale(Dpoly,-2*SCALE);parts=[]
 for j,o in enumerate(owners):
  i=j;n=j+1;q=n if o==i else i
  one=add(const(1),mul(var(i,signs[i]),var(n,signs[n])))
  delta=add(var(i,signs[i]),var(n,-signs[n]))
  rem=prod([add(const(1),var(o,1,2)),add(const(1),var(q,-1,2))]+[Dfac[v]for v in range(3)if v not in(i,n)])
  base=add(base,scale(mul(mul(one,one),rem),SCALE))
  parts.append(scale(mul(mul(one,delta),rem),SCALE))
 rem=prod([add(const(1),var(0,-1,2)),Dfac[1],Dfac[2]])
 base=add(base,scale(mul(add(const(-368),var(0,529),var(0,-1536,2)),rem),1000))
 rem=prod([Dfac[0],Dfac[1],add(const(1),var(2,-1,2))])
 base=add(base,scale(mul(add(const(1),var(2,2),var(2,-1,2)),rem),SCALE//2))
 rem=prod([add(const(1),var(k,1,2))]+[Dfac[v]for v in range(3)if v!=k])
 base=add(base,scale(mul(var(k),rem),-int(2*LAMBDA*SCALE)))
 return [base]+parts

def transform_matrix(address):
 n,d=address;den=70*(1<<d);lo=29*n;width=29
 return [[sum((12//comb(4,m))*comb(r,m)*comb(j,m)*lo**(r-m)*width**m*den**(4-r)
              for m in range(min(j,r)+1))for r in range(5)]for j in range(5)]
def transform(poly,addresses):
 a=[poly.get(e,0)for e in INDICES]
 for axis,addr in enumerate(addresses):
  T=transform_matrix(addr);b=[0]*N;stride=5**(2-axis)
  for index in range(N):
   digit=(index//stride)%5;first=index-digit*stride
   b[index]=sum(T[digit][r]*a[first+r*stride]for r in range(5))
  a=b
 return a
CANDIDATES=list(product(range(-8,9),repeat=2))
def test(ps,addresses):
 base,p,q=[transform(poly,addresses)for poly in ps]
 origin=all(n==0 for n,d in addresses)
 # Try weights whose linear part has a strictly positive coefficient on all three rays first.
 def score(w):
  a,b=w
  vals=[8*base[i]+a*p[i]+b*q[i]for i in (25,5,1)]
  return min(vals)
 for a,b in sorted(CANDIDATES,key=score,reverse=True):
  values=[8*x+a*y+b*z for x,y,z in zip(base,p,q)]
  if origin:
   passed=values[0]==0 and min(values[1:])>0
  else:passed=min(values)>0
  if passed:return dict(weights=[a,b],weight_denominator=8,coefficient_min=str(min(values)),
                        positive_coefficient_min=str(min(values[1:]if origin else values)),origin_leaf=origin)
 return None

def run(signs,owners,k,budget):
 ps=polynomials(signs,owners,k);stack=[([(0,0)]*3,[])];leaves=[];unresolved=[];nodes=0;maximum=0;start=time.monotonic()
 while stack and nodes<budget:
  addresses,path=stack.pop();nodes+=1;maximum=max(maximum,len(path));proof=test(ps,addresses)
  if proof:leaves.append(dict(path=path,**proof));continue
  if len(path)>=24:unresolved.append(path);continue
  axis=max(range(3),key=lambda i:F(1,1<<addresses[i][1]));n,d=addresses[axis]
  for side in (1,0):
   child=list(addresses);child[axis]=(2*n+side,d+1);stack.append((child,path+[[axis,side]]))
  if nodes%500==0:print('PROGRESS',signs,owners,k,nodes,len(leaves),len(stack),maximum,round(time.monotonic()-start,2),flush=True)
 return dict(schema='exact_actual_edge_three_angle_bernstein_cover_v1',signs=signs,owners=owners,selected_owner=k,
             root_upper=str(S),coefficient=str(LAMBDA),target_variation='16/25',scale=SCALE,
             nodes=nodes,maxdepth=maximum,leaves=leaves,frontier=unresolved+[path for addr,path in stack],seconds=time.monotonic()-start)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);ap.add_argument('--budget',type=int,default=10000)
 ap.add_argument('--pilot',action='store_true');args=ap.parse_args();args.output.mkdir(exist_ok=True,parents=True)
 summaries=[]
 for u,v in product((-1,1),repeat=2):
  signs=[1,u,v]
  for a,b in product((0,1),repeat=2):
   owners=[a,1+b]
   for k in sorted(set(owners)):
    name='s'+''.join('p'if x>0 else'm'for x in signs)+'_o'+''.join(map(str,owners))+'_k'+str(k)+'.json'
    dest=args.output/name
    if dest.exists():r=json.loads(dest.read_text())
    else:r=run(signs,owners,k,args.budget);dest.write_text(json.dumps(r,separators=(',',':'))+'\n')
    summary={q:r[q]for q in('signs','owners','selected_owner','nodes','maxdepth','seconds')}
    summary.update(file=name,leaves=len(r['leaves']),open=len(r['frontier']));summaries.append(summary);print(json.dumps(summary),flush=True)
    if args.pilot:return
 manifest=dict(schema='exact_actual_edge_three_angle_complete_cover_v1',root_upper=str(S),coefficient=str(LAMBDA),
               target_variation='16/25',domains=summaries,leaves=sum(s['leaves']for s in summaries),open=sum(s['open']for s in summaries),
               independent_replay_pending=True,no_original_or_mask_credit=True)
 (args.output/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
if __name__=='__main__':main()
