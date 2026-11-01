#!/usr/bin/env python3
"""Independent exact traversal and arithmetic verification of the stored certificate.

No import of the certificate generator. Run with normal Python (assertions enabled).
Optional first argument: certificate JSON path. The analytic tail's physical transfer
is proved in the manuscript; its exact scalar arithmetic is checked here.
"""
import sys
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import json

SOURCE=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('perpendicular_single_free_triangle_certificate.json')
TARGET=F(625,144)
SCALE=1<<18
ONE=(F(1),F(1))
def N(x):
    return x if isinstance(x,tuple) else (F(x),F(x))
def A(x,y):
    x,y=N(x),N(y);return x[0]+y[0],x[1]+y[1]
def M(x,y):
    x,y=N(x),N(y);p=[a*b for a in x for b in y];return min(p),max(p)
def S(x,y):
    x,y=N(x),N(y);return x[0]-y[1],x[1]-y[0]
def D(x,y):
    x,y=N(x),N(y);assert y[0]>0;return M(x,(1/y[1],1/y[0]))
def SQ(x):
    x=N(x);return (F(0) if x[0]<=0<=x[1] else min(t*t for t in x),max(t*t for t in x))
def CL(x):
    result=max(F(0),x[0]),min(F(1),x[1]);assert result[0]<=result[1];return result
def ROOT(x):
    assert x[0]>=0
    l=isqrt(x[0].numerator*SCALE*SCALE//x[0].denominator)
    h=isqrt(x[1].numerator*SCALE*SCALE//x[1].denominator)
    while F(h*h,SCALE*SCALE)<x[1]:h+=1
    assert F(l*l,SCALE*SCALE)<=x[0]<=x[1]<=F(h*h,SCALE*SCALE)
    return F(l,SCALE),F(h,SCALE)
def sn(t):return 2*t/(1+t*t)
def cs(t):return (1-t*t)/(1+t*t)
def sd(p,q):return 2*(q-p)*(1+p*q)/((1+p*p)*(1+q*q))
def lower(box):
    p,q=box
    ca,sa=(cs(p[1]),cs(p[0])),(sn(p[0]),sn(p[1]))
    cb,sb=(cs(q[1]),cs(q[0])),(sn(q[0]),sn(q[1]))
    delt=(F(0) if q[0]<=p[1] else sd(p[1],q[0]),sd(p[0],q[1]))
    t,s=CL(A(S(1,ca),cb)),CL(S(A(1,sa),sb))
    da,db=A(M(t,ca),M(s,sa)),A(M(t,cb),M(s,sb))
    ua=CL(S(1,D(M(M(t,sb),delt),da)))
    ub=CL(S(1,D(M(M(s,ca),delt),db)))
    n=ROOT(A(SQ(t),SQ(s)))
    a=(A(A(1,M(2,sb)),M(ua,cb)),A(S(s,M(2,cb)),M(ua,sb)))
    b=(A(S(t,M(2,sa)),M(ub,ca)),A(A(1,M(2,ca)),M(ub,sa)))
    c=(D(M(-1,t),n),D(M(-1,s),n))
    return sum(SQ(S(x[k],y[k]))[0] for x,y in ((a,b),(b,c),(c,a)) for k in (0,1))/9
def box_of(x):return tuple(tuple(map(F, row)) for row in x)

cert=json.loads(SOURCE.read_text())
assert F(cert['report']['target_squared'])==TARGET
assert cert['report']['sqrt_scale']==SCALE
counts={'nodes':0,'variance':0,'empty_order':0}
expected_roots=[((F(0),F(1,20)),(F(0),F(10,11))),((F(1,20),F(1)),(F(0),F(1)))]
assert len(cert['trees'])==2
for root_index,tree in enumerate(cert['trees']):
    root=box_of(tree['root']);assert root==expected_roots[root_index]
    records={n['address']:n for n in tree['nodes']}
    assert len(records)==len(tree['nodes'])
    seen=set();stack=[('',root)]
    while stack:
        addr,box=stack.pop();assert addr not in seen;seen.add(addr)
        record=records[addr];counts['nodes']+=1
        if 'split_axis' in record:
            axis=record['split_axis'];assert axis in (0,1)
            midpoint=F(record['split_at']);assert midpoint==sum(box[axis])/2
            assert box[axis][0]<midpoint<box[axis][1]
            left,right=list(box),list(box)
            left[axis]=(box[axis][0],midpoint);right[axis]=(midpoint,box[axis][1])
            stack.extend([(addr+'0',tuple(left)),(addr+'1',tuple(right))])
        else:
            assert box_of(record['box'])==box
            reason=record['reason'];counts[reason]+=1
            if reason=='empty_order':assert box[0][0]>box[1][1]
            elif reason=='variance':
                bound=lower(box)
                assert bound==F(record['lower_bound']) and bound-TARGET>F(1,6000)
            else:raise AssertionError('unexpected rejection type '+reason)
    assert seen==set(records)
assert counts=={'nodes':898,'variance':441,'empty_order':9}
assert cert['report']['total_nodes']==counts['nodes']
assert cert['report']['total_variance_leaves']==counts['variance']
assert cert['report']['total_empty_leaves']==counts['empty_order']
assert box_of(cert['report']['analytic_tail']['root'])==((F(0),F(1,20)),(F(10,11),F(1)))
assert sn(F(1,20))<=F(1,10) and cs(F(10,11))<=F(1,10)
assert F(99,100)**2<F(99,100)
L=F(149,50)-F(25,12)
assert L>0 and 2*L*L+1+2*L-TARGET==F(5497,90000)>0
assert F(cert['report']['analytic_tail']['center_coordinate_lower_bound'])==L
assert F(cert['report']['analytic_tail']['strict_margin'])==F(5497,90000)
print('Independent tree and arithmetic reconstruction passed:',counts)
print('All stored bounds matched exactly; all strict margins positive; every root is completely covered.')
