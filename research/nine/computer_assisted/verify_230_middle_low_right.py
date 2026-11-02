#!/usr/bin/env python3
"""Independent Fraction replay of the complete central-right endpoint table.

Uses no producer, producer evaluator, dyadic interval kernel, or derivatives.
Only direct interval leaves are accepted.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import gzip,hashlib,json,sys,time

class Interval:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        if isinstance(lo,Interval):self.lo,self.hi=lo.lo,lo.hi
        else:self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,other):
        z=Interval(other);return Interval(self.lo+z.lo,self.hi+z.hi)
    __radd__=__add__
    def __neg__(self):return Interval(-self.hi,-self.lo)
    def __sub__(self,z):return self+-Interval(z)
    def __rsub__(self,z):return Interval(z)+-self
    def __mul__(self,other):
        z=Interval(other);terms=[self.lo*z.lo,self.lo*z.hi,self.hi*z.lo,self.hi*z.hi]
        return Interval(min(terms),max(terms))
    __rmul__=__mul__
    def __truediv__(self,other):
        z=Interval(other);assert z.lo>0
        return self*Interval(1/z.hi,1/z.lo)
    def __rtruediv__(self,z):return Interval(z)/self
    def square(self):
        lower=0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi)
        return Interval(lower,max(self.lo*self.lo,self.hi*self.hi))
    def absolute(self):
        lower=0 if self.lo<=0<=self.hi else min(abs(self.lo),abs(self.hi))
        return Interval(lower,max(abs(self.lo),abs(self.hi)))
    def root(self):
        assert self.lo>=0
        scale=1<<80
        low=isqrt(self.lo.numerator*scale*scale//self.lo.denominator)
        high=isqrt(self.hi.numerator*scale*scale//self.hi.denominator)
        if high*high*self.hi.denominator<self.hi.numerator*scale*scale:high+=1
        return Interval(F(low,scale),F(high,scale))

def minimum(*items):return Interval(min(x.lo for x in items),min(x.hi for x in items))
def maximum(*items):return Interval(max(x.lo for x in items),max(x.hi for x in items))
def intersect(x,lo,hi):return Interval(max(x.lo,F(lo)),min(x.hi,F(hi)))

ROOT=((F(0),F(1)),)*3+((F(11,12),F(13,12)),(F(-23,60),F(0)),(F(19,60),F(29,60)))

def bound(box):
    t0,t1,t2,z,x,w=[Interval(*ends)for ends in box]
    slopes=(t0,t1,t2)
    frames=[]
    for t in slopes:
        d=(1+t.square()).root()
        def endpoint(s):
            n=Interval(1+s*s).root()
            return (1/n,s/n,(1+s)/(2*n),(1-s)/(2*n))
        low,high=endpoint(t.lo),endpoint(t.hi)
        # On [0,1], a,k decrease and b,h increase. The exact endpoint
        # radicals enclose the complete orientation intervals.
        a=Interval(high[0].lo,low[0].hi)
        b=Interval(low[1].lo,high[1].hi)
        h=Interval(low[2].lo,high[2].hi)
        k=Interval(high[3].lo,low[3].hi)
        frames.append((d,a,b,h,k))
    hL,hP,hR=[row[3]for row in frames]
    left_gap=x+z;right_gap=w-x
    necessary=[left_gap-1/(4*hL)-1/(4*hP),right_gap-1/(4*hP)-1/(4*hR)]
    p_low=hP+F(509,4960)
    l_low=maximum(Interval(F(27,40)),F(221,600)+minimum(hL,frames[0][0]/2+t0*(z-F(503,480))))
    r_low=Interval(F(-7,40))
    def circle_ceiling(index,center,sign):
        d,a,b,h,k=frames[index]
        corner_list=((h,-sign*k),(sign*k,h),(-h,sign*k),(-sign*k,-h))
        bounds=[Interval(F(91,60))]
        for horizontal,vertical in corner_list:
            bounds.append((Interval(F(1105,256))-(center+horizontal).square()).root()-vertical)
        return minimum(*bounds)
    ceilingsL={s:circle_ceiling(0,z,-s)for s in (-1,1)}
    ceilingsR={s:minimum(Interval(F(3,5)),circle_ceiling(2,w,s))for s in (-1,1)}
    def pair_ceiling(i,si,j,sj,dx,low_dy,high_dy):
        ti,tj=slopes[i],slopes[j]
        di,ai,bi,hi,ki=frames[i];dj,aj,bj,hj,kj=frames[j]
        cosine=1+si*sj*ti*tj
        assert cosine.lo>=0
        sine=(sj*tj-si*ti).absolute()
        unnormalized_support=(1+(cosine+sine)/(di*dj))/2
        normalized_cosine=(ai*aj+si*sj*bi*bj).absolute()
        normalized_sine=(si*bi*aj-sj*ai*bj).absolute()
        normalized_support=(1+normalized_cosine+normalized_sine)/2
        # Both displayed expressions equal the same physical support at
        # every point. Their independently evaluated lower bounds can be
        # combined; endpoint-monotone component ranges sometimes make the
        # normalized form sharper than dividing an entire numerator box.
        support=maximum(Interval(1),unnormalized_support,normalized_support)
        normals=((ai,si*bi,si),(bi,-si*ai,-si),(aj,sj*bj,sj),(bj,-sj*aj,-sj))
        projections=[nx*dx+ny*(high_dy if sign>0 else low_dy)for nx,ny,sign in normals]
        return minimum(high_dy-low_dy,maximum(*projections)-support)
    possible_P=[]
    for sp in (-1,1):
        p_high=circle_ceiling(1,x,sp)
        possible_L=[];possible_R=[]
        for sl in (-1,1):
            l_high=ceilingsL[sl]
            low=maximum(-left_gap,p_low-l_high)
            high=minimum(left_gap,p_high-l_low)
            possible_L.append(minimum(l_high-l_low,left_gap+p_high-l_low,left_gap+l_high-p_low,pair_ceiling(0,sl,1,sp,left_gap,low,high)))
        for sr in (-1,1):
            r_high=ceilingsR[sr]
            low=maximum(-right_gap,r_low-p_high)
            high=minimum(right_gap,r_high-p_low)
            possible_R.append(minimum(r_high-r_low,right_gap+p_high-r_low,right_gap+r_high-p_low,pair_ceiling(1,sp,2,sr,right_gap,low,high)))
        possible_P.append(minimum(p_high-p_low,maximum(*possible_L),maximum(*possible_R)))
    return minimum(*necessary,maximum(*possible_P)).hi

def verify(path):
    start=time.monotonic();raw=Path(path).read_bytes();cert=json.loads(gzip.decompress(raw))
    assert cert['type']=='central_right_endpoint_low_height_230_v1'
    assert cert['root']==[[str(a),str(b)]for a,b in ROOT]
    assert cert['coordinates']==['tL','tP','tR','minus_xL','xP','xR']
    assert cert['pending']==[]
    nodes=cert['tree'];seen=set();leaves=0;maxdepth=0;largest=None
    stack=[(0,ROOT,0)];last=time.monotonic()
    while stack:
        idx,box,depth=stack.pop()
        assert isinstance(idx,int) and 0<=idx<len(nodes) and idx not in seen
        seen.add(idx);maxdepth=max(maxdepth,depth);node=nodes[idx]
        if 'tag' in node:
            assert set(node) in ({'tag','upper'},{'tag'}) and node['tag']=='direct'
            if 'upper' in node:assert F(node['upper'])<0
            upper=bound(box);assert upper<0,(idx,box,upper)
            leaves+=1;largest=upper if largest is None else max(largest,upper)
        else:
            assert set(node)=={'axis','children'}
            axis=node['axis'];kids=node['children']
            assert isinstance(axis,int) and 0<=axis<6 and len(kids)==2
            lo,hi=box[axis];mid=(lo+hi)/2;left=list(box);right=list(box)
            left[axis]=(lo,mid);right[axis]=(mid,hi)
            stack.extend([(kids[1],tuple(right),depth+1),(kids[0],tuple(left),depth+1)])
        if time.monotonic()-last>25:
            print('REPLAY',leaves,len(seen),len(stack),flush=True,file=sys.stderr);last=time.monotonic()
    assert len(seen)==len(nodes)==2*leaves-1
    assert leaves==cert['closed']
    return {'result':'PASS','certificate':Path(path).name,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'nodes':len(nodes),'leaves':leaves,'max_depth':maxdepth,'largest_upper':str(largest),'arithmetic':'exact Fraction intervals; outward80-bit square roots; no producer imports, derivatives, or floating point acceptance','seconds':time.monotonic()-start}

if __name__=='__main__':
    path=sys.argv[1]if len(sys.argv)>1 else str(Path(__file__).with_name('230_middle_low_right_complete_cover.json.gz'))
    print(json.dumps(verify(path),indent=2))
