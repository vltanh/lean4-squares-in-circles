#!/usr/bin/env python3
"""Exact dyadic interval search for the physical-two side-return feature.

The complete generated cover and its hand soundness theorem are in
research/nine/PHYSICAL_TWO_PERPENDICULAR_SINGLETON_WHOLE_SIDE_RETURN_EXCLUSION_2026_10_30.md.
Every arithmetic operation is rounded outwards with integer arithmetic.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path
import time

BITS = 40
D = 1 << BITS
KIND = 'physical_two_side_return'

def require(test, message):
    if not test:raise ValueError(message)

def ceildiv(a,b):
    return -((-a)//b)

@dataclass(frozen=True)
class I:
    lo: int
    hi: int
    @staticmethod
    def q(n,d=1):
        return I(n*D//d,ceildiv(n*D,d))
    def __add__(self,o):
        if not isinstance(o,I):o=I.q(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o if isinstance(o,I) else self+I.q(-o)
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        if not isinstance(o,I):o=I.q(o)
        v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(min(v)//D,ceildiv(max(v),D))
    __rmul__=__mul__
    def sq(self):
        lo=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        hi=max(self.lo*self.lo,self.hi*self.hi)
        return I(lo//D,ceildiv(hi,D))
    def sqrt(self):
        if self.hi<0:raise ValueError('negative radicand')
        a=isqrt(max(0,self.lo)*D);b=isqrt(max(0,self.hi)*D)
        return I(a,b+(b*b<self.hi*D))
    def abs(self):return I(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))

ROOT=((0,ceildiv(2*D,3)),(0,ceildiv(16*D,25)),(D//2,D),(9*D//10,ceildiv(61*D,60)))
NAMES=('s','b','H','d')

def classify(box):
    s,b,H,d=[I(*v) for v in box]
    a=(1-b.sq()).sqrt();c=(1-s.sq()).sqrt()
    if c.hi<=I.q(3,4).lo:return 'c_domain'
    da=1-a+H*s;na=1-H*c+b;t=H-I.q(1,2)
    u=a*c-b*s;y=a*s+b*c
    x=a-H*s;l=H*c-b
    for name,z in [('x',x),('l',l)]:
        if z.hi<=0 or z.lo>=D:return name+'_domain'
    if u.hi<=0 or y.hi<=0:return 'positive_direction'
    if (5*u-18*b).lo>=0:return 'return_ratio'
    if y.hi<=I.q(3,11).lo:return 'low_y'
    eq=b*t*na-(d*s+I.q(1,2)*c)*u*da
    if eq.lo>0 or eq.hi<0:return 'full_torque'
    W=da.sq()+na.sq();rw=W.sqrt()
    Kx=d-c+s*na;Ky=I.q(1,2)+s+c*na
    X=-c*da+s*na;Y=s*da+c*na
    N=Kx*X+Ky*Y
    if (N-d*rw).lo>0:return 'B_support'
    radius=(d+1).sq()+I.q(1,4)
    if ((Kx.sq()+Ky.sq()+1-radius)*rw+2*N).lo>0:return 'B_point'
    # Whole-square vertical gap: no division by c or sqrt(W).
    L=c*(H+s+c*na+u-y-1)-a*u*y
    gap=L*rw-c*X.abs()
    G=1+a-b*da
    if Y.lo>0 and rw.lo>0 and c.lo>0 and gap.lo>0 and G.lo>0 and G.sq().lo>2*D:
        return 'bridge_exclusion'
    return None

def split(box,k):
    lo,hi=box[k];mid=(lo+hi)//2
    if not lo<mid<hi:raise ValueError('precision limit')
    left=list(box);right=list(box)
    left[k]=(lo,mid);right[k]=(mid,hi)
    return tuple(left),tuple(right)

def choose(box):
    # Scale relative widths; the radius parameter has weak geometric influence.
    widths=[Fraction(v[1]-v[0],ROOT[k][1]-ROOT[k][0]) for k,v in enumerate(box)]
    return max(range(4),key=lambda k:widths[k]*(1 if k<3 else Fraction(1,3)))

def generate(limit):
    start=time.monotonic();stack=[(0,ROOT,0)];nodes=[None];counts=Counter();depth=0
    while stack:
        index,box,lev=stack.pop();depth=max(depth,lev)
        rule=classify(box)
        if rule is not None:nodes[index]=[rule];counts[rule]+=1
        else:
            if len(nodes)+2>limit:
                return None,dict(nodes=len(nodes),unresolved=len(stack)+1,max_depth=depth,counts=dict(counts),seconds=round(time.monotonic()-start,2),box=[[str(Fraction(v,D)) for v in p] for p in box])
            k=choose(box);left,right=split(box,k);ii=len(nodes);nodes.extend([None,None]);nodes[index]=['split',k,ii,ii+1]
            stack.append((ii+1,right,lev+1));stack.append((ii,left,lev+1))
        if len(nodes)%20000==1:
            print(json.dumps({'progress_nodes':len(nodes),'pending':len(stack),'depth':depth}),flush=True)
    return {'version':1,'kind':KIND,'precision_bits':BITS,'root_box':ROOT,'nodes':nodes},dict(nodes=len(nodes),max_depth=depth,counts=dict(counts),seconds=round(time.monotonic()-start,2))

def verify(data):
    require(data['version']==1 and data['kind']==KIND,'wrong certificate specification')
    require(data['precision_bits']==BITS and tuple(map(tuple,data['root_box']))==ROOT,'wrong precision or domain')
    nodes=data['nodes'];seen=set();counts=Counter();stack=[(0,ROOT)]
    while stack:
        i,box=stack.pop();require(i not in seen and 0<=i<len(nodes),'duplicate or invalid node');seen.add(i);row=nodes[i]
        if row[0]=='split':
            require(len(row)==4 and row[1] in range(4),'invalid split')
            le,ri=split(box,row[1]);stack.extend([(row[2],le),(row[3],ri)])
        else:
            require(len(row)==1 and classify(box)==row[0],'unproved leaf');counts[row[0]]+=1
    require(len(seen)==len(nodes),'unreachable nodes')
    return {'status':'EXACT INTERVAL COVER REPLAYED','nodes':len(nodes),'leaves':sum(counts.values()),'counts':dict(counts),'original_load_row_closed':False,'Lean_verified':False}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--limit',type=int,default=200000);ap.add_argument('--output',type=Path);ap.add_argument('--verify',type=Path);args=ap.parse_args()
    if args.verify:
        print(json.dumps(verify(json.loads(args.verify.read_text())),indent=2));return
    data,stats=generate(args.limit);print(json.dumps(stats,indent=2),flush=True)
    if data is None:print('UNRESOLVED: no proof certificate produced');return
    print(json.dumps(verify(data),indent=2),flush=True)
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(data,separators=(',',':'))+'\n')

if __name__=='__main__':main()
