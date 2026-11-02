#!/usr/bin/env python3
"""Independent Fraction replay of the complete original lower-side gate.

No producer import, dyadic production kernel, floating arithmetic, Lean,
or CI. Geometry and full root coverage are reconstructed here.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,time

class I:
    def __init__(self,lo,hi=None):
        if isinstance(lo,I):self.lo,self.hi=lo.lo,lo.hi
        else:self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o);v=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o);assert o.lo>0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def sq(self):
        v=(self.lo*self.lo,self.hi*self.hi)
        return I(0 if self.lo<=0<=self.hi else min(v),max(v))
    def ab(self):
        return I(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def rt(self):
        assert self.lo>=0
        d=1<<80
        lo=isqrt(self.lo.numerator*d*d//self.lo.denominator)
        hi=isqrt(self.hi.numerator*d*d//self.hi.denominator)
        if F(hi*hi,d*d)<self.hi:hi+=1
        return I(F(lo,d),F(hi,d))

ROOT=((F(0),F(17,500)),(F(0),F(1)),(F(29,60),F(13,12)))
Q=F(1105,256);Z=F(17,50)
def minimum(*v):return I(min(x.lo for x in v),min(x.hi for x in v))
def maximum(*v):return I(max(x.lo for x in v),max(x.hi for x in v))
def frame(t):
    a=1/(1+I(t).sq()).rt();b=t*a
    return a,b,(a+b)/2,(a-b)/2
def frame_range(r):
    low,high=frame(r[0]),frame(r[1])
    return (I(high[0].lo,low[0].hi),I(low[1].lo,high[1].hi),
            I(low[2].lo,high[2].hi),I(high[3].lo,low[3].hi))

def check(box,tag):
    am,bm,hm,km=frame_range(box[0]);a,b,h,k=frame_range(box[1]);x=I(*box[2])
    if tag=='main_tilt':
        reserve=hm.lo-F(31,60)
        assert reserve>0,('unproved main-tilt leaf',box)
        return reserve
    assert tag=='all_axes',('unknown rule',tag)
    e=hm-F(1,2)
    d=maximum(x-F(29,60)-e,F(31,60)-e-x)
    caps=[]
    for sign in (-1,1):
        offsets=((h,-sign*k),(sign*k,h),(-h,sign*k),(-sign*k,-h))
        caps.append(minimum(I(F(91,60)),*[(Q-(x+dx).sq()).rt()-dy for dx,dy in offsets]))
    v=maximum(*caps)-Z
    mlo,mhi=box[0];slo,shi=box[1]
    if shi<mlo:tm,ts=mlo,shi
    elif mhi<slo:tm,ts=mhi,slo
    else:tm=ts=None
    if tm is None:sigma=I(1)
    else:
        am0,bm0,_,_=frame(tm);a0,b0,_,_=frame(ts)
        # Reconstruct the relative support from dot and determinant.
        sigma=maximum(I(1),(1+am0*a0+bm0*b0+(am0*b0-bm0*a0).ab())/2)
    margins=(a*d+b*v-sigma,b*d+a*v-sigma,
             am*d+bm*v-sigma,bm*d+am*v-sigma)
    reserve=-max(t.hi for t in margins)
    assert reserve>0,('unproved pair-axis leaf',box,str(reserve))
    return reserve

def verify(data,include_rows=False):
    assert data['type']=='original_lower_side_main_height_17_50_v1'
    assert data['main_height']=='17/50'
    assert data['root']==[[str(a),str(b)] for a,b in ROOT]
    # The actual main satisfies h<31/60, so its tangent is below 17/500.
    t=F(17,500)
    tangent_reserve=(1+t)**2/(4*(1+t*t))-F(31,60)**2
    assert tangent_reserve>0
    rho=F(91,60)
    radius_reserve=rho*rho+rho+F(1,2)-Q
    assert radius_reserve>0
    nodes=data['tree'];assert isinstance(nodes,list) and nodes
    seen=set();counts=Counter();reserves=[];rows=[];depthmax=0
    def walk(index,box,depth):
        nonlocal depthmax
        assert type(index)is int and 0<=index<len(nodes) and index not in seen
        seen.add(index);depthmax=max(depthmax,depth);node=nodes[index]
        assert isinstance(node,dict)
        if 'tag' in node:
            assert set(node)=={'tag'}
            reserve=check(box,node['tag']);reserves.append(reserve);counts[node['tag']]+=1
            if include_rows:rows.append({'box':[[str(a),str(b)]for a,b in box],'rule':node['tag'],'reserve':str(reserve)})
            return
        assert set(node)=={'axis','children'}
        axis=node['axis'];children=node['children']
        assert type(axis)is int and 0<=axis<3 and isinstance(children,list) and len(children)==2
        lo,hi=box[axis];mid=(lo+hi)/2;assert lo<mid<hi
        l=list(box);r=list(box);l[axis]=(lo,mid);r[axis]=(mid,hi)
        walk(children[0],tuple(l),depth+1);walk(children[1],tuple(r),depth+1)
    walk(0,ROOT,0)
    assert len(seen)==len(nodes)==2*len(reserves)-1
    assert len(reserves)==data['leaves'] and depthmax==data['maximum_depth']
    result={'result':'PASS','nodes':len(nodes),'leaves':len(reserves),'maximum_depth':depthmax,
       'rules':dict(counts),'least_exact_reserve':str(min(reserves)),
       'main_tangent_cut_squared_reserve':str(tangent_reserve),
       'universal_center_squared_reserve':str(radius_reserve),
       'arithmetic':'Fraction intervals with outward 80-bit radicals; no producer imports or floating arithmetic'}
    if include_rows:result['rows']=rows
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--certificate',type=Path,default=Path(__file__).with_name('lower_side_main_17_50_cover.json'))
    parser.add_argument('--report',type=Path);parser.add_argument('--rows',action='store_true');args=parser.parse_args()
    start=time.monotonic();blob=args.certificate.read_bytes();report=verify(json.loads(blob),args.rows)
    report.update(certificate_sha256=hashlib.sha256(blob).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-start)
    text=json.dumps(report,indent=2)+'\n'
    if args.report:args.report.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
