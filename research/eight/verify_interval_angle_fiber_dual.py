#!/usr/bin/env python3
"""SOUND exact Fraction interval checker for a true SAT-owner ANGLE BOX.

Certifies: for EVERY frame half-tangent in each given rational interval,
and ALL centers satisfying every listed genuine oriented SAT support
inequality, squared containing radius >= target_q.

Positive total vertex weight is required on EVERY square so the center
variables can be eliminated without division by zero.
This checks ONE selected angle/owner box; it neither certifies coverage
of all boxes nor establishes global n=8 optimality.

Usage:
  python verify_interval_angle_fiber_dual.py \
      seven_parallel_positive_angle_box_certificate.json
"""
import json,sys
from fractions import Fraction as F

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I):
            self.lo,self.hi=a.lo,a.hi
        else:
            self.lo=F(str(a))
            self.hi=F(str(b if b is not None else a))
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o)
        vv=[x*y for x in (self.lo,self.hi) for y in (o.lo,o.hi)]
        return I(min(vv),max(vv))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o)
        assert o.lo>0 or o.hi<0
        return self*I(F(1)/o.hi,F(1)/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def __abs__(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return I(0,max(-self.lo,self.hi))
    def square(self):
        if self.lo>=0:return I(self.lo**2,self.hi**2)
        if self.hi<=0:return I(self.hi**2,self.lo**2)
        return I(0,max(self.lo**2,self.hi**2))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(k,a):return (k*a[0],k*a[1])
def dot(a,b):return a[0]*b[0]+a[1]*b[1]

def check(cert):
    n=len(cert["angle_half_tangent_boxes"])
    frame=[]
    for lo,hi in cert["angle_half_tangent_boxes"]:
        z=I(lo,hi)
        z2=z.square()
        c=(1-z2)/(1+z2)
        s=2*z/(1+z2)
        frame.append(((c,s),(-s,c)))
    mu=[F(0)]*n
    av=[(I(0),I(0)) for _ in range(n)]
    cvec=[(I(0),I(0)) for _ in range(n)]
    for i,k,mstr in cert["corner_weights"]:
        m=F(mstr)
        assert m>=0 and 0<=i<n and 0<=k<4
        j1=(-1,1)[k//2];j2=(-1,1)[k%2]
        e,f=frame[i]
        offset=mul(I(F(1,2)),add(mul(j1,e),mul(j2,f)))
        mu[i]+=m
        av[i]=add(av[i],mul(m,offset))
    assert sum(mu)==1
    assert all(u>0 for u in mu),"all anchor masses must be positive"
    support=I(0)
    for i,j,where,sgn,lstr in cert["edges"]:
        assert 0<=i<j<n and sgn in (-1,1)
        lam=F(lstr);assert lam>=0
        idx,key=where.split(".")
        assert idx in ("i","j") and key in ("e","f")
        fidx=i if idx=="i" else j
        normal=frame[fidx][0 if key=="e" else 1]
        normal=mul(sgn,normal)
        halfwidth_sum=I(0)
        for k in (i,j):
            e,f=frame[k]
            halfwidth_sum+=I(F(1,2))*(
                abs(dot(normal,e))+abs(dot(normal,f))
            )
        support+=lam*halfwidth_sum
        cvec[i]=add(cvec[i],mul(lam,normal))
        cvec[j]=add(cvec[j],mul(-lam,normal))
    dual=I(F(1,2))+support
    for i in range(n):
        vv=add(mul(2,av[i]),cvec[i])
        normhi=(vv[0].square()+vv[1].square()).hi
        dual-=I(F(normhi)/(4*mu[i]))
    target=F(cert["target_q"])
    assert dual.lo>=target,(
        "unproved target on this box",float(dual.lo),float(target)
    )
    print("PASS: exact interval dual for",n,
          "independent true square frame half-tangent boxes")
    print("D_lower =",dual.lo,"~",float(dual.lo))
    print("target_q =",target,
          "strict exact margin =",dual.lo-target)
    print("SCOPE: ONLY this angle box and the listed true SAT owners")

if __name__=="__main__":
    with open(sys.argv[1]) as fd:check(json.load(fd))
