#!/usr/bin/env python3
"""Independent exact arithmetic replay for the G-order LP forest.

No producer import, optimizer, floating point arithmetic, or claimed producer
bounds are used. Each leaf is a positive rational combination of necessary
physical inequalities; the residual center coefficients are bounded explicitly.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import gcd,isqrt
from pathlib import Path
import argparse,gzip,json,hashlib,time
Q=F(1105,256);RHO=F(91,60);A=F(46);B=F(27,2);ROOT_BITS=48
DIRS=tuple((x,y) for x in range(-4,5) for y in range(-4,5) if (x or y) and gcd(x,y)==1)
PAIRS=((1,2),(0,2),(0,1));ROOTS=tuple(product(((F(-1),F(0)),(F(0),F(1))),repeat=3))
@lru_cache(maxsize=None)
def root_bounds(x):
 assert x>=0
 n=isqrt((x.numerator << (2*ROOT_BITS))//x.denominator);d=1<<ROOT_BITS
 lo=F(n,d);hi=lo if lo*lo==x else F(n+1,d)
 return lo,hi

def quotient_bounds(n,d):
 lo,hi=root_bounds(d)
 assert lo>0 and n>=0
 return n/hi,n/lo
@lru_cache(maxsize=None)
def h_bounds(T):
 l,u=T
 vals=[quotient_bounds(1+abs(t),1+t*t) for t in (l,u)]
 return (F(1,2) if l<=0<=u else min(v[0]/2 for v in vals)),max(v[1]/2 for v in vals)
@lru_cache(maxsize=None)
def support_lower(T,w):
 l,u=T;x,y=w;ts=[l,u]
 if y and l<=F(-x,y)<=u:ts.append(F(-x,y))
 if x and l<=F(y,x)<=u:ts.append(F(y,x))
 return min(quotient_bounds(abs(x+y*t)+abs(y-x*t),1+t*t)[0]/2 for t in ts)
@lru_cache(maxsize=None)
def normal_bounds(T,axis,sgn):
 l,u=T;small=F(0) if l<=0<=u else min(abs(l),abs(u));big=max(abs(l),abs(u))
 an=(quotient_bounds(F(1),1+big*big)[0],quotient_bounds(F(1),1+small*small)[1])
 def sine(t):
  low,high=quotient_bounds(abs(t),1+t*t)
  return (low,high) if t>=0 else (-high,-low)
 bn=(sine(l)[0],sine(u)[1])
 if axis:an,bn=(-bn[1],-bn[0]),an
 if sgn<0:an,bn=(-an[1],-an[0]),(-bn[1],-bn[0])
 return an,bn
@lru_cache(maxsize=None)
def pair_support_lower(T,U):
 if max(T[0],U[0])<=min(T[1],U[1]):return F(1)
 vals=[]
 for t,u in ((T[0],U[1]),(T[1],U[0])):
  vals.append(quotient_bounds(1+t*u+abs(t-u),(1+t*t)*(1+u*u))[0])
 return (1+min(vals))/2
@lru_cache(maxsize=2048)
def context(box):
 hs=tuple(h_bounds(t) for t in box);gs=tuple(F(1,4)/h[1] for h in hs)
 xs=((hs[0][0]-F(1,60),RHO-gs[0]-gs[1]),(hs[0][0]-F(1,60)+gs[0]+gs[1],RHO),(hs[2][0]-F(1,60),RHO))
 ys=[]
 for i in range(3):
  hlo,hhi=hs[i];klo=root_bounds(max(F(0),F(1,2)-hhi*hhi))[0];xlo=xs[i][0]
  cap=max(root_bounds(max(F(0),Q-(xlo+hlo)**2))[1]-klo,root_bounds(max(F(0),Q-(xlo+klo)**2))[1]-hlo)
  cap=min(RHO,cap);ys.append((-cap,cap))
 cb=tuple(z for i in range(3) for z in (xs[i],ys[i]))
 return hs,gs,cb

def basis(i,v):
 row=[F(0)]*6;row[i]=v;return row

def rational_row(index,box,choice):
 hs,gs,cb=context(box);row=[F(0)]*6
 if index<12:
  k=index//2
  return (basis(k,F(1)),cb[k][1]) if index%2==0 else (basis(k,F(-1)),-cb[k][0])
 index-=12
 if index<3*len(DIRS):
  i,j=divmod(index,len(DIRS));p,q=DIRS[j];row[2*i]=F(p);row[2*i+1]=F(q)
  return row,root_bounds(Q*(p*p+q*q))[1]-support_lower(box[i],(p,q))
 index-=3*len(DIRS)
 if index==0:row[0]=-A;row[4]=-B;return row,-F(27,4)-A*hs[0][0]-B*hs[2][0]
 if index==1:row[0]=1;row[2]=-1;return row,-gs[0]-gs[1]
 if index==2:row[1]=1;row[3]=-1;return row,-F(7,30)
 if index==3:row[0]=1;row[2]=-1;row[1]=-1;row[3]=1;return row,F(0)
 if index==4:row[0]=-1;row[2]=1;return row,hs[0][1]+hs[1][1]
 if index==5:row[3]=-1;row[5]=1;return row,F(0)
 if index==6:row[2]=1;row[4]=-1;return row,F(1459,1728)
 k=index-7
 assert 0<=k<len(choice)
 i,j=PAIRS[k];owner,axis,sgn=choice[k];nn=normal_bounds(box[owner],axis,sgn)
 nm=[F(round((v[0]+v[1])/2*(1<<30)),1<<30) for v in nn]
 error=F(0)
 for xy in (0,1):
  ee=(nn[xy][0]-nm[xy],nn[xy][1]-nm[xy]);dr=(cb[2*j+xy][0]-cb[2*i+xy][1],cb[2*j+xy][1]-cb[2*i+xy][0])
  if k==0:
   dr=(max(dr[0],-F(1459,1728)),min(dr[1],F(1))) if xy==0 else (dr[0],min(dr[1],F(0)))
  if k==2:
   dr=(max(dr[0],gs[0]+gs[1]),min(dr[1],F(31,30))) if xy==0 else (max(dr[0],F(7,30)),min(dr[1],F(31,30)))
  assert dr[0]<=dr[1],('empty center interval must have been pruned without separator',box,choice,k,xy,dr)
  error+=max(e*d for e in ee for d in dr)
 row[2*i:2*i+2]=nm;row[2*j:2*j+2]=[-v for v in nm]
 return row,-pair_support_lower(box[i],box[j])+error

def omitted_option_impossible(box,k,option):
 owner,axis,sgn=option;nn=normal_bounds(box[owner],axis,sgn)
 if k==0:return nn[1][0]>=0
 if k==2:return nn[0][1]<=0 and nn[1][1]<=0
 return False

def all_options(k):
 i,j=PAIRS[k]
 return tuple((owner,axis,sgn) for owner in (i,j) for axis in (0,1) for sgn in (-1,1))

def pack(discovery,target):
 assert not discovery['frontier'],'A complete forest cannot have an unresolved frontier.'
 roots=[{} for _ in ROOTS]
 for leaf in discovery['leaves']:
  pp=leaf['path'];steps=[]
  while 'parent' in pp:
   if 'axis' in pp:steps.append(('angle',pp['axis'],pp['side']))
   else:steps.append(('sep',tuple(pp['sep'])))
   pp=pp['parent']
  cur=roots[pp['root']]
  for step in reversed(steps):
   assert 'w' not in cur
   kind=step[0]
   if 'kind' in cur:assert cur['kind']==kind
   else:cur['kind']=kind;cur['children']={}
   key=str(step[2]) if kind=='angle' else ','.join(str(x) for x in step[1])
   if kind=='angle':
    if 'axis' in cur:assert cur['axis']==step[1]
    else:cur['axis']=step[1]
   cur=cur['children'].setdefault(key,{})
  assert not cur,'Duplicate or overlapping terminal paths.'
  assert leaf['power']==40
  cur['w']=leaf['weights']
 data={'schema':'weak-outer-G-order-farkas-v1','root_bits':ROOT_BITS,'weight_power':40,'roots':roots}
 raw=(json.dumps(data,separators=(',',':'))+'\n').encode()
 with gzip.open(target,'wb',compresslevel=9) as f:f.write(raw)
 return data

def verify(data):
 assert data['schema']=='weak-outer-G-order-farkas-v1'
 assert data['root_bits']==ROOT_BITS and data['weight_power']==40
 assert len(data['roots'])==8
 stats={'nodes':0,'leaves':0,'angle_splits':0,'separator_splits':0,'max_depth':0};least=None
 def visit(node,box,ch,depth):
  nonlocal least
  stats['nodes']+=1;stats['max_depth']=max(stats['max_depth'],depth)
  if 'w' in node:
   assert set(node)=={'w'}
   rr=[F(0)]*6;bb=F(0);seen=set()
   for index,weight in node['w']:
    assert type(index) is int and type(weight) is int and weight>0 and index not in seen
    assert 0<=index<12+3*len(DIRS)+7+len(ch);seen.add(index)
    row,rhs=rational_row(index,box,ch);bb+=weight*rhs
    for j in range(6):rr[j]+=weight*row[j]
   reserve=(-bb-RHO*sum(abs(z) for z in rr))/(1<<40)
   assert reserve>0,('nonpositive exact leaf',str(reserve),box,ch,node)
   stats['leaves']+=1;least=reserve if least is None else min(least,reserve)
   if stats['leaves']%10000==0:print('exact leaves',stats['leaves'],'nodes',stats['nodes'],flush=True)
  elif node.get('kind')=='angle':
   assert set(node)=={'kind','axis','children'} and set(node['children'])=={'0','1'}
   k=node['axis'];assert type(k)is int and 0<=k<3;stats['angle_splits']+=1;l,u=box[k];m=(l+u)/2
   for side,T in enumerate(((l,m),(m,u))):
    bo=list(box);bo[k]=T;visit(node['children'][str(side)],tuple(bo),ch,depth+1)
  else:
   assert set(node)=={'kind','children'} and node['kind']=='sep'
   k=len(ch);assert k<3;stats['separator_splits']+=1
   children={tuple(map(int,key.split(','))):value for key,value in node['children'].items()}
   assert set(children)<=set(all_options(k))
   for option in all_options(k):
    if option in children:visit(children[option],box,ch+(option,),depth+1)
    else:assert omitted_option_impossible(box,k,option),('uncovered separator owner/sign',k,option,box)
 for node,box in zip(data['roots'],ROOTS):visit(node,box,(),0)
 stats['minimum_reserve']=str(least);stats['minimum_reserve_floor_1e12']=str(F((least*10**12).numerator//(least*10**12).denominator,10**12))
 stats['status']='PASS';stats['frontier']=0
 return stats

def main():
 ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--pack-discovery',type=Path);ap.add_argument('--report',type=Path);args=ap.parse_args();start=time.time()
 if args.pack_discovery:data=pack(json.loads(args.pack_discovery.read_text()),args.certificate)
 else:
  with gzip.open(args.certificate,'rt') as f:data=json.load(f)
 stats=verify(data);stats['seconds']=time.time()-start;stats['certificate_sha256']=hashlib.sha256(args.certificate.read_bytes()).hexdigest()
 if args.report:args.report.write_text(json.dumps(stats,indent=2)+'\n')
 print(json.dumps(stats,indent=2))
if __name__=='__main__':main()
