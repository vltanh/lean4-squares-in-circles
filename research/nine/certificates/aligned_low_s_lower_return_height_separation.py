#!/usr/bin/env python3
"""Exact continuous certificate for the actual lower-C return height.

The scalar domain and every safe contraction are specified in
ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md. All mathematical
operations use Fraction, isqrt, and outward enclosures. No float or
sampled pose decides a branch. Root supplied the first independent
continuous cover; this implementation uses separate interval pairs,
a direct normal enclosure, 64-bit radical endpoints, and a checked
complete prefix partition.
"""
from fractions import Fraction as Q
from math import isqrt
from collections import Counter
from pathlib import Path
import hashlib,json
BITS=64
SCALE=1<<BITS
# Intervals are plain immutable pairs. Every operation encloses all real
# operands; no floating-point operation is used for a mathematical decision.
def C(x):
 q=Q(x);return(q,q)
def add(A,B):return(A[0]+B[0],A[1]+B[1])
def neg(A):return(-A[1],-A[0])
def sub(A,B):return add(A,neg(B))
def mul(A,B):
 v=[a*b for a in A for b in B];return(min(v),max(v))
def sq(A):
 return((Q(0) if A[0]<=0<=A[1] else min(a*a for a in A)),max(a*a for a in A))
def div(A,B):
 assert B[0]>0;return mul(A,(1/B[1],1/B[0]))
def intersect(A,B):
 lo=max(A[0],B[0]);hi=min(A[1],B[1]);return None if lo>hi else(lo,hi)
def root(A):
 assert A[1]>=0
 lo=max(A[0],Q(0));hi=A[1]
 k=isqrt(lo.numerator*SCALE*SCALE//lo.denominator)
 l=isqrt(hi.numerator*SCALE*SCALE//hi.denominator)
 if Q(l*l,SCALE*SCALE)<hi:l+=1
 assert Q(k*k,SCALE*SCALE)<=lo and Q(l*l,SCALE*SCALE)>=hi
 return(Q(k,SCALE),Q(l,SCALE))
ONE=C(1);ZERO=C(0)
initial=((Q(14,15),Q(1)),(Q(29,50),Q(2,3)),(Q(2,25),Q(5,7)))
width=[b-a for a,b in initial]
def prove(box):
 d,h,t=box;a=sub(ONE,d);g=sub(ONE,h)
 b=root(sub(ONE,sq(t)));b=intersect(b,(t[0],Q(1)))
 if b is None:return 'unit tilt',None
 R2=add(sq(add(d,ONE)),C(Q(1,4)));Y=add(add(g,b),t)
 X2=sub(R2,sq(Y))
 if X2[1]<=0:return 'positive X',None
 X=root(X2)
 x=intersect(add(sub(X,b),t),(max(Q(3,10),t[0]),d[1]))
 if x is None:return 'original x',None
 X=intersect(X,sub(add(x,b),t))
 if X is None:return 'original X identity',None
 screen=sub(mul(sub(d,x),t),mul(sub(h,C(Q(1,2))),b))
 if screen[1]<0:return 'leaf screen',None
 w=add(x,a);length=root(add(sq(w),sq(h)))
 if X[0]<=0 or length[0]<=0:return None,None
 c=div(w,length);s=div(h,length)
 N=add(mul(a,c),mul(h,s));K=mul(x,s)
 W2=sub(R2,sq(add(N,ONE)))
 if W2[1]<0:return 'upper radius',None
 W=root(W2)
 rho=intersect(sub(W,K),(Q(7,8),Q(1)))
 if rho is None:return 'upper side mean',None
 delta=sub(ONE,rho)
 tau=mul(b,sub(div(mul(x,Y),X),g))
 tau=intersect(tau,(Q(0),Q(1)))
 if tau is None:return 'lower side mean',None
 target=sub(mul(tau,b),mul(delta,c))
 return ('positive separation',target[0]) if target[0]>0 else(None,None)
todo=[('',initial)];leaves=[];nodes=0
while todo:
 path,box=todo.pop();nodes+=1
 reason,margin=prove(box)
 if reason:
  leaves.append({'path':path,'reason':reason,'margin':None if margin is None else str(margin)})
  continue
 assert len(path)<42 and nodes<200000,(path,box)
 axis=max(range(3),key=lambda j:(box[j][1]-box[j][0])/width[j])
 mid=sum(box[axis],Q(0))/2
 left=list(box);right=list(box)
 left[axis]=(box[axis][0],mid);right[axis]=(mid,box[axis][1])
 todo.extend([(path+'1',tuple(right)),(path+'0',tuple(left))])
# A finite prefix cover of the complete initial closed rectangle.
paths={v['path'] for v in leaves}
assert len(paths)==len(leaves)
while paths!={''}:
 longest=max(map(len,paths));parents={p[:-1] for p in paths if len(p)==longest}
 for p in parents:
  assert p+'0' in paths and p+'1' in paths
  paths.remove(p+'0');paths.remove(p+'1');paths.add(p)
assert nodes==2*len(leaves)-1
payload=json.dumps(leaves,sort_keys=True,separators=(',',':')).encode()
positive=[Q(v['margin']) for v in leaves if v['margin'] is not None]
assert min(positive)>Q(1,25000)
record={'uniform_strict_floor':'1/25000','initial':[[str(x) for x in v] for v in initial],'bits':BITS,'nodes':nodes,'leaf_count':len(leaves),'max_depth':max(len(v['path']) for v in leaves),'counts':dict(Counter(v['reason'] for v in leaves)),'smallest_margin':str(min(positive)),'prefix_cover':True,'leaf_digest':hashlib.sha256(payload).hexdigest(),'leaves':leaves}
p=Path('/tmp/aligned_low_s_lower_return_height_separation_certificate.json');p.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='leaves'},indent=2))
