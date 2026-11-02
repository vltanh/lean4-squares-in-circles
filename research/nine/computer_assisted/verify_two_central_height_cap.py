#!/usr/bin/env python3
"""Independent exact Fraction replay of the two-central height-cap cover.
No producer, producer evaluator, or dyadic interval class is imported.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import gzip,hashlib,json,sys,time

class I:
    def __init__(self,lo,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi
        else: self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o);p=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o); assert o.lo>0 or o.hi<0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def sq(self):
        return I(0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
    def abs(self):
        return I(0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def sqrt(self,bits=44):
        assert self.lo>=0
        d=1<<bits
        lo=isqrt((self.lo.numerator*d*d)//self.lo.denominator)
        hi=isqrt((self.hi.numerator*d*d)//self.hi.denominator)+1
        return I(F(lo,d),F(hi,d))
    def serialize(self):return [str(self.lo),str(self.hi)]
    def floats(self):return [float(self.lo),float(self.hi)]

ROOT=((F(0),F(29,60)),(F(0),F(1)),(F(0),F(1)))

def check(box, sign_a, sign_b, rule):
    x=I(*box[0]); ta=I(*box[1]); tb=I(*box[2])
    da=(I(1)+ta*ta).sqrt(64); db=(I(1)+tb*tb).sqrt(64)
    a=I(1)/da; b=ta/da; c=I(1)/db; d=tb/db
    h=(a+b)/2; k=(a-b)/2; j=(c+d)/2
    caps=[(I(F(1105,256))-(x+sign_a*k).sq()).sqrt(64)-h,
          (I(F(1105,256))-(x+h).sq()).sqrt(64)+sign_a*k,
          I(F(91,60))]
    top=I(min(v.lo for v in caps),min(v.hi for v in caps))
    if rule=='circle':
        reserve=F(273,200)-top.hi
    elif rule=='pair_axes':
        # Compute the exact relative-frame support from dot and determinant.
        ua=(I(1),sign_a*ta); ub=(I(1),sign_b*tb)
        cosine_numerator=ua[0]*ub[0]+ua[1]*ub[1]
        sine_numerator=ua[0]*ub[1]-ua[1]*ub[0]
        assert cosine_numerator.lo>=0
        sigma=(I(1)+(cosine_numerator+sine_numerator.abs())/(da*db))/2
        dx=x+F(29,60); dy=top-j-F(1,10)
        na=(a,b) if sign_a==1 else (b,a)
        nb=(c,d) if sign_b==1 else (d,c)
        projections=[na[0]*dx+na[1]*dy,nb[0]*dx+nb[1]*dy]
        reserve=sigma.lo-max(v.hi for v in projections)
    else:raise AssertionError(('unknown rule',rule))
    assert reserve>0,(box,sign_a,sign_b,rule,reserve)
    return reserve

def main():
    start=time.monotonic()
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('two_central_height_cap_cover.json.gz')
    raw=path.read_bytes();cert=json.loads(gzip.decompress(raw))
    assert cert['root']==[[str(a),str(b)] for a,b in ROOT]
    signs=set(); reports=[];total=0
    for chart in cert['charts']:
        sa,sb=chart['epsA'],chart['epsB']
        assert sa in (-1,1) and sb in (-1,1) and (sa,sb) not in signs
        signs.add((sa,sb));nodes=chart['tree'];seen=set();counts={};reserves=[];maxdepth=0
        def walk(index,box,depth):
            nonlocal maxdepth
            assert isinstance(index,int) and 0<=index<len(nodes) and index not in seen
            seen.add(index);maxdepth=max(maxdepth,depth);node=nodes[index]
            if 'tag' in node:
                assert set(node)=={'tag'}
                tag=node['tag'];reserves.append(check(box,sa,sb,tag));counts[tag]=counts.get(tag,0)+1;return
            assert set(node)=={'axis','children'}
            axis=node['axis'];children=node['children'];assert axis in (0,1,2) and len(children)==2
            lo,hi=box[axis];mid=(lo+hi)/2;left=list(box);right=list(box)
            left[axis]=(lo,mid);right[axis]=(mid,hi)
            walk(children[0],tuple(left),depth+1);walk(children[1],tuple(right),depth+1)
        walk(0,ROOT,0)
        assert len(seen)==len(nodes)==2*len(reserves)-1
        assert counts==chart['counts']
        total+=len(reserves)
        reports.append({'epsA':sa,'epsB':sb,'leaves':len(reserves),'counts':counts,'max_depth':maxdepth,'least_positive_reserve':str(min(reserves))})
        print('chart PASS',sa,sb,len(reserves),flush=True,file=sys.stderr)
    assert signs=={(-1,-1),(-1,1),(1,-1),(1,1)}
    assert total==cert['leaves']
    print(json.dumps({'result':'PASS','certificate':path.name,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'root':cert['root'],'charts':reports,'total_leaves':total,'arithmetic':'exact Fraction arithmetic with outward 64-bit sqrt bounds; no producer imports or floating point acceptance','seconds':time.monotonic()-start},indent=2))

if __name__=='__main__':main()
