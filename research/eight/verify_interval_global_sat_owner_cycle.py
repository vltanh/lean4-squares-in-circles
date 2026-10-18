#!/usr/bin/env python3
"""SOUND Fraction interval true SAT owner CYCLE obstruction.

Checks a FULL independent frame half-tangent angular box
and any prescribed directed simple cycle of genuine square
side SAT normal owners. Exact interval arithmetic supplies
(1) true whole-square separator-support lower bounds, and
(2) rigorous center-normal-coefficient Euclidean upper
bounds. If supports exceed the disk-center projection upper
bound, NO centers can realize these owners for ANY angle
inside the box, at q<=9789/2500.

This is a globally valid pruning step for ONE angle/owner box,
NOT a complete owner cover or global R8>=Rhat proof.
"""
import sys,json
from fractions import Fraction as F

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.lo,self.hi=a.lo,a.hi
        else:
            self.lo=F(str(a))
            self.hi=F(str(a if b is None else b))
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o)
        vals=[a*b for a in (self.lo,self.hi)
                    for b in (o.lo,o.hi)]
        return I(min(vals),max(vals))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o)
        assert o.lo>0 or o.hi<0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def square(self):
        if self.lo>=0:return I(self.lo**2,self.hi**2)
        if self.hi<=0:return I(self.hi**2,self.lo**2)
        return I(0,max(self.lo**2,self.hi**2))
    def __abs__(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return I(0,max(-self.lo,self.hi))
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(x,a):return (x*a[0],x*a[1])

def check(cert):
    r0=F(283,200)
    qplus=F(9789,2500)
    assert r0*r0+r0+F(1,2)-qplus==F(13,8000)>0
    ef=[]
    for lo,hi in cert["angle_half_tangent_boxes"]:
        t=I(lo,hi)
        z=t.square()
        c=(1-z)/(1+z)
        s=2*t/(1+z)
        ef.append(((c,s),(-s,c)))
    cycle=cert["cycle"]
    k=len(cycle)
    assert k>=3 and len(set(row[0] for row in cycle))==k
    assert all(cycle[i][1]==cycle[(i+1)%k][0] for i in range(k))
    normals=[]
    supports=[]
    for a,b,owner,axis,sign in cycle:
        assert a!=b and owner in (a,b)
        assert 0<=a<len(ef) and 0<=b<len(ef)
        assert axis in ("e","f") and sign in (-1,1)
        n=mul(sign,ef[owner][0 if axis=="e" else 1])
        normals.append(n)
        H=lambda i:I(F(1,2))*(
            abs(dot(n,ef[i][0]))+abs(dot(n,ef[i][1])))
        supports.append(H(a)+H(b))
    lower=sum((w.lo for w in supports),F(0))
    assert all(w.lo>0 for w in supports)
    upper=[F(x) for x in cert["coefficient_norm_upper_bounds"]]
    assert len(upper)==k and all(x>=0 for x in upper)
    for i in range(k):
        d=sub(normals[(i-1)%k],normals[i])
        bound=d[0].square()+d[1].square()
        assert upper[i]*upper[i]>=bound.hi,(
            "invalid center coefficient norm upper bound",i)
    rhs=r0*sum(upper)
    assert lower>rhs,("no contradiction for this box",lower,rhs)
    target=F(cert.get("claimed_minimum_margin","0"))
    assert lower-rhs>target
    print("PASS exact continuous angle-box true SAT owner cycle exclusion")
    print("cycle length",k,"support lower",lower,"~",float(lower))
    print("center projection upper",rhs,"~",float(rhs))
    print("strict rational interval reserve",lower-rhs,"~",float(lower-rhs))
    print("SCOPE: this angular box and genuine directed owner cycle only")
if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))
