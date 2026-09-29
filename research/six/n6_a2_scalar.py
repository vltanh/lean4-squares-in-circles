#!/usr/bin/env python3
"""Exact rational interval/jet utilities for scalar n=6 A2 audits."""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial,isqrt
from functools import lru_cache

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi)
        assert self.lo<=self.hi,(self.lo,self.hi)
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); xs=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(min(xs),max(xs))
    __rmul__=__mul__
    def inv(self):
        assert not(self.lo<=0<=self.hi),(self.lo,self.hi)
        return I(1/self.hi,1/self.lo)
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
    def __abs__(self):
        if self.lo<=0<=self.hi:return I(0,max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))

def iv(x): return x if isinstance(x,I) else I(x)
def hullI(*xs): return I(min(x.lo for x in xs),max(x.hi for x in xs))

def sqrt_bounds(x,bits=120):
    x=F(x); assert x>=0
    sc=1<<(2*bits); k=isqrt((x.numerator*sc)//x.denominator)
    while F(k*k,sc)>x:k-=1
    while F((k+1)*(k+1),sc)<=x:k+=1
    return I(F(k,1<<bits),F(k+1,1<<bits))
def sqrtI(x):
    x=iv(x); assert x.lo>=0
    return I(sqrt_bounds(x.lo).lo,sqrt_bounds(x.hi).hi)

def atan_bounds(x:F,terms=28):
    z=F(0)
    for k in range(terms):
        t=x**(2*k+1)/F(2*k+1); z += t if k%2==0 else -t
    nxt=x**(2*terms+1)/F(2*terms+1)
    return I(z,z+nxt) if terms%2==0 else I(z-nxt,z)
PI=16*atan_bounds(F(1,5),28)-4*atan_bounds(F(1,239),8)

@lru_cache(maxsize=200000)
def sin_point(x:F,m=14):
    s=F(0)
    for k in range(m+1):
        t=x**(2*k+1)/F(factorial(2*k+1)); s += t if k%2==0 else -t
    r=abs(x)**(2*m+2)/F(factorial(2*m+2))
    return I(s-r,s+r)
@lru_cache(maxsize=200000)
def cos_point(x:F,m=14):
    s=F(0)
    for k in range(m+1):
        t=x**(2*k)/F(factorial(2*k)); s += t if k%2==0 else -t
    r=abs(x)**(2*m+1)/F(factorial(2*m+1))
    return I(s-r,s+r)

def scaleI(k:F,x:I): return I(k*x.lo,k*x.hi) if k>=0 else I(k*x.hi,k*x.lo)
def overlap(a:I,b:I): return not(a.hi<b.lo or b.hi<a.lo)

def sinR(x):
    x=iv(x); a=sin_point(x.lo); b=sin_point(x.hi); lo=min(a.lo,b.lo); hi=max(a.hi,b.hi)
    for k in range(-5,6,2):
        c=scaleI(F(k,2),PI)
        if overlap(x,c):
            v=F(1) if k%4==1 else F(-1); lo=min(lo,v);hi=max(hi,v)
    return I(lo,hi)
def cosR(x):
    x=iv(x); a=cos_point(x.lo); b=cos_point(x.hi); lo=min(a.lo,b.lo);hi=max(a.hi,b.hi)
    for k in range(-3,4):
        c=scaleI(F(k),PI)
        if overlap(x,c):
            v=F(1) if k%2==0 else F(-1); lo=min(lo,v);hi=max(hi,v)
    return I(lo,hi)

class J:
    __slots__=('v','d','dd')
    def __init__(self,v,d=0,dd=0): self.v=iv(v);self.d=iv(d);self.dd=iv(dd)
    def __add__(self,o):o=jj(o);return J(self.v+o.v,self.d+o.d,self.dd+o.dd)
    __radd__=__add__
    def __neg__(self):return J(-self.v,-self.d,-self.dd)
    def __sub__(self,o):return self+(-jj(o))
    def __rsub__(self,o):return jj(o)-self
    def __mul__(self,o):
        o=jj(o);return J(self.v*o.v,self.d*o.v+self.v*o.d,
                         self.dd*o.v+2*self.d*o.d+self.v*o.dd)
    __rmul__=__mul__
    def inv(self):
        v2=self.v*self.v;v3=v2*self.v
        return J(self.v.inv(),-self.d/v2,2*self.d*self.d/v3-self.dd/v2)
    def __truediv__(self,o):return self*jj(o).inv()
    def __rtruediv__(self,o):return jj(o)/self

def jj(x):return x if isinstance(x,J) else J(x)
def hullJ(*zs):return J(hullI(*(z.v for z in zs)),hullI(*(z.d for z in zs)),hullI(*(z.dd for z in zs)))
def jsin(x):
    x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(s,c*x.d,-s*x.d*x.d+c*x.dd)
def jcos(x):
    x=jj(x);s=sinR(x.v);c=cosR(x.v);return J(c,-s*x.d,-c*x.d*x.d-s*x.dd)
def jsqrt(x):
    x=jj(x);q=sqrtI(x.v);return J(q,x.d/(2*q),x.dd/(2*q)-x.d*x.d/(4*q*q*q))
def jabs(x):
    x=jj(x)
    if x.v.lo>=0:return x
    if x.v.hi<=0:return -x
    return hullJ(x,-x)

rt2=sqrt_bounds(F(2),150); h=1/rt2
A=(F(1466)+F(1940)*h)/F(267); B=(F(327)+F(432)*h)/F(712)
disc=A*A-4*B; sd=sqrtI(disc); ss=2*B/(A+sd)
qstar=2*ss*ss+4*ss+F(5,2); R=sqrtI(qstar); rho=sqrtI(qstar-F(1,4))-F(1,2); c0=rho-1

def support_ordered(U,V,norm):
    cap=jj(rho)*U; vert=jj(R)*norm-(U+V)/2
    sw=2*R*V.v-norm.v
    if sw.hi<=0:return cap
    if sw.lo>=0:return vert
    return hullJ(cap,vert)
def support_any(x,y):
    x,y=jj(x),jj(y);ax,ay=jabs(x),jabs(y);norm=jsqrt(x*x+y*y)
    if ax.v.lo>=ay.v.hi:return support_ordered(ax,ay,norm)
    if ay.v.lo>=ax.v.hi:return support_ordered(ay,ax,norm)
    return hullJ(support_ordered(ax,ay,norm),support_ordered(ay,ax,norm))

def parts(lo,hi,step):
    x=F(lo);hi=F(hi);step=F(step)
    while x<hi:
        y=min(x+step,hi);yield x,y;x=y

def drange(fun,lo,hi,step=F(1,200)):
    a0=F(100);a1=-F(100)
    for a,b in parts(lo,hi,step):
        z=fun(J(I(a,b),1)).d;a0=min(a0,z.lo);a1=max(a1,z.hi)
    return a0,a1
def maxdd(fun,lo,hi,step=F(1,200)):
    out=-F(100)
    for a,b in parts(lo,hi,step):out=max(out,fun(J(I(a,b),1)).dd.hi)
    return out
def minval(fun,lo,hi,step=F(1,200)):
    out=F(100)
    for a,b in parts(lo,hi,step):out=min(out,fun(J(I(a,b))).v.lo)
    return out

if __name__=='__main__':
    assert PI.lo < F(22,7) and PI.hi > F(333,106)
    print('n6 A2 scalar core: PASS')
