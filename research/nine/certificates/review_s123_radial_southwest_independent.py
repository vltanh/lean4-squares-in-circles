"""Independent exact audit of the radial-Southwest two-variable cover.

Ordinary operations use exact rational endpoints. Only radicals are
rounded, on a 2**-48 lattice. No author checker is imported.
"""
from fractions import Fraction as F
from math import isqrt
from collections import Counter

SCALE = 1 << 48
class Interval:
    def __init__(self, lower, upper=None):
        self.lo = F(lower)
        self.hi = F(lower if upper is None else upper)
    def __add__(self, other):
        other = iv(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)
    __radd__ = __add__
    def __neg__(self):
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other):
        return self + -iv(other)
    def __rsub__(self, other):
        return iv(other) + -self
    def __mul__(self, other):
        other = iv(other)
        values = [x*y for x in (self.lo,self.hi) for y in (other.lo,other.hi)]
        return Interval(min(values),max(values))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = iv(other)
        if other.lo <= 0:
            raise ValueError("unresolved positive divisor")
        return self*Interval(1/other.hi,1/other.lo)
    def __rtruediv__(self, other):
        return iv(other)/self
    def square(self):
        lower = 0 if self.lo <= 0 <= self.hi else min(self.lo**2,self.hi**2)
        return Interval(lower,max(self.lo**2,self.hi**2))
    def sqrt(self):
        if self.hi < 0:
            raise ValueError("negative radical interval")
        def endpoints(x):
            x=max(F(0),x)
            numerator=x.numerator*SCALE*SCALE
            denominator=x.denominator
            k=isqrt(numerator//denominator)
            return F(k,SCALE), F(k+(k*k*denominator<numerator),SCALE)
        return Interval(endpoints(self.lo)[0],endpoints(self.hi)[1])
    def absolute(self):
        if self.lo <= 0 <= self.hi:
            return Interval(0,max(-self.lo,self.hi))
        return Interval(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def intersect(self, lower, upper):
        return Interval(max(self.lo,F(lower)),min(self.hi,F(upper)))
    def empty(self):
        return self.lo>self.hi

def iv(x):
    return x if isinstance(x,Interval) else Interval(x)

extrema = dict.fromkeys(("far","D","low_n","high_n","low_f","high_f"))
def record(name,value,upper=False):
    if extrema[name] is None:
        extrema[name]=value
    else:
        extrema[name]=(max if upper else min)(extrema[name],value)

def classify(box):
    a,K=[Interval(*segment) for segment in box]
    b=1-a
    La=(K.square()+a.square()).sqrt()
    Lb=(K.square()+b.square()).sqrt()
    eps=(a.square()/(La+K)).intersect(0,F(1,60))
    if eps.empty(): return "empty"
    radius2=((2+eps).square()+F(1,4)).intersect(F(17,4),F(1105,256))
    if radius2.empty(): return "empty"
    N=((b.square()-eps*K)/Lb).intersect(0,1)
    if N.empty(): return "empty"
    z=b*(K+eps)/Lb
    S=N+1
    radicand=radius2-S.square()
    if radicand.hi<0: return "empty"
    W=radicand.sqrt().intersect(F(1,2),F(11,6))
    if W.empty(): return "empty"
    length=(z*S/W-N).intersect(0,1)
    depth=(z+1-W).intersect(0,1)
    if length.empty() or depth.empty(): return "empty"
    D=(K.square()-a*b)/(La*Lb)
    E=K/(La*Lb)
    center_n=(N+F(1,2))*D-(W-F(1,2))*E
    center_f=(N+F(1,2))*E+(W-F(1,2))*D
    if (center_n-F(9,50)*center_f.absolute()).lo>=0:
        return "empty"
    if D.lo<=F(1,4): return "split"
    try:
        far=(S*(1-length)-(W-1)*depth)/((1-length).square()+depth.square()).sqrt()
    except ValueError:
        return "split"
    if far.lo<=F(61,60): return "split"
    inner=(radius2-1).sqrt()-1
    points=[]
    for near in (True,False):
        if near:
            ww=W.intersect(F(1,2),1)
            qm=N.intersect(inner.lo,1)
            if ww.empty() or qm.empty(): continue
        else:
            ww=W
            qm=z*S/W
        point_n=qm*D-(ww-1)*E
        point_f=qm*E+(ww-1)*D
        if (point_n.square()+point_f.square()).hi<inner.square().lo:
            continue
        if not (point_n.lo>F(1,10) and point_n.hi<F(3,4)
                and point_f.lo>F(1,2) and point_f.hi<F(43,50)):
            return "split"
        points.append((point_n,point_f))
    record("far",far.lo)
    record("D",D.lo)
    for point_n,point_f in points:
        record("low_n",point_n.lo)
        record("high_n",point_n.hi,True)
        record("low_f",point_f.lo)
        record("high_f",point_f.hi,True)
    return "pass"

def main():
    box=((F(0),F(29,100)),(F(1,4),F(7)))
    stack=[(box,0)]
    counts=Counter()
    depths=Counter()
    scales=(12,1)
    while stack:
        box,level=stack.pop()
        state=classify(box)
        counts[state]+=1
        depths[level]+=1
        if state=="split":
            assert level<30,box
            axis=max(range(2),key=lambda index:(box[index][1]-box[index][0])*scales[index])
            lo,hi=box[axis]
            middle=(lo+hi)/2
            for segment in ((lo,middle),(middle,hi)):
                child=list(box)
                child[axis]=segment
                stack.append((tuple(child),level+1))
    assert counts["pass"]+counts["empty"]==counts["split"]+1
    print("counts",dict(sorted(counts.items())))
    print("maximum depth",max(depths))
    print("depth nodes",[depths[k] for k in range(max(depths)+1)])
    margins={
        "far":extrema["far"]-F(61,60),
        "D":extrema["D"]-F(1,4),
        "low_n":extrema["low_n"]-F(1,10),
        "high_n":F(3,4)-extrema["high_n"],
        "low_f":extrema["low_f"]-F(1,2),
        "high_f":F(43,50)-extrema["high_f"]}
    for name,margin in sorted(margins.items()):
        assert margin>0
        scaled=margin*SCALE
        lower=F(scaled.numerator//scaled.denominator,SCALE)
        assert lower>0
        print("strict margin",name,lower)

if __name__=="__main__":
    main()

