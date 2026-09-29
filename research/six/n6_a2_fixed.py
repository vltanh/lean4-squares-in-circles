#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from math import factorial,isqrt

BITS=52
S=1<<BITS

def floord(a,b):
    assert b>0
    return a//b
def ceild(a,b):
    assert b>0
    return -((-a)//b)

def qfloor(q:F): return floord(q.numerator*S,q.denominator)
def qceil(q:F): return ceild(q.numerator*S,q.denominator)

class I:
    __slots__=("lo","hi")
    def __init__(self,lo,hi=None):
        if hi is None:
            q=F(lo); self.lo=qfloor(q); self.hi=qceil(q)
        elif isinstance(lo,F) or isinstance(hi,F):
            self.lo=qfloor(F(lo)); self.hi=qceil(F(hi))
        else:
            self.lo=int(lo); self.hi=int(hi)
        assert self.lo<=self.hi,(self.lo,self.hi)
    @staticmethod
    def frac(q): return I(F(q))
    @staticmethod
    def bounds(a,b): return I(F(a),F(b))
    def __add__(self,o): o=iv(o); return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,o): return self+(-iv(o))
    def __rsub__(self,o): return iv(o)-self
    def __mul__(self,o):
        o=iv(o); z=(self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi)
        return I(floord(min(z),S),ceild(max(z),S))
    __rmul__=__mul__
    def inv(self):
        assert not(self.lo<=0<=self.hi),(self.lo,self.hi)
        if self.hi<0: return -((-self).inv())
        return I(floord(S*S,self.hi),ceild(S*S,self.lo))
    def __truediv__(self,o): return self*iv(o).inv()
    def __rtruediv__(self,o): return iv(o)/self
    def div_int(self,n):
        if n<0:return (-self).div_int(-n)
        return I(floord(self.lo,n),ceild(self.hi,n))
    def __abs__(self):
        if self.lo<=0<=self.hi:return I(0,max(-self.lo,self.hi))
        return I(min(abs(self.lo),abs(self.hi)),max(abs(self.lo),abs(self.hi)))
    def f(self): return (self.lo/S,self.hi/S)

def iv(x):
    if isinstance(x,I):return x
    return I.frac(F(x))
def hullI(*xs): return I(min(x.lo for x in xs),max(x.hi for x in xs))
ZERO=I(0,0); ONE=I(S,S)

def sqrtI(x):
    x=iv(x); assert x.lo>=0
    lo=isqrt(x.lo*S)
    hi=isqrt(x.hi*S)
    if hi*hi<x.hi*S:hi+=1
    return I(lo,hi)

def atan_bounds(x:F,n=24):
    z=F(0)
    for k in range(n):
        t=x**(2*k+1)/F(2*k+1); z += t if k%2==0 else -t
    nxt=x**(2*n+1)/F(2*n+1)
    return (z,z+nxt) if n%2==0 else (z-nxt,z)
a5=atan_bounds(F(1,5),24);a239=atan_bounds(F(1,239),8)
PI=I.bounds(16*a5[0]-4*a239[1],16*a5[1]-4*a239[0])

def abs_power(x,n):
    y=ONE;a=abs(x)
    for _ in range(n):y=y*a
    return y

def rem_bound(x,n):
    p=abs_power(x,n); return ceild(p.hi,factorial(n))
@lru_cache(maxsize=500000)
def sin_point_int(v):
    x=I(v,v); x2=x*x; term=x; total=term
    for k in range(1,18):
        term=(term*x2).div_int((2*k)*(2*k+1))
        total=total-term if k%2 else total+term
    r=rem_bound(x,37)
    return I(total.lo-r,total.hi+r)
@lru_cache(maxsize=500000)
def cos_point_int(v):
    x=I(v,v); x2=x*x; term=ONE; total=term
    for k in range(1,18):
        term=(term*x2).div_int((2*k-1)*(2*k))
        total=total-term if k%2 else total+term
    r=rem_bound(x,36)
    return I(total.lo-r,total.hi+r)

def overlap(a,b):return not(a.hi<b.lo or b.hi<a.lo)
@lru_cache(maxsize=500000)
def sin_cached(lo,hi):
    x=I(lo,hi);a=sin_point_int(lo);b=sin_point_int(hi);L=min(a.lo,b.lo);H=max(a.hi,b.hi)
    for k in range(-7,8,2):
        c=I.frac(F(k,2))*PI
        if overlap(x,c):
            v=S if k%4==1 else -S;L=min(L,v);H=max(H,v)
    return I(max(-S,L),min(S,H))
@lru_cache(maxsize=500000)
def cos_cached(lo,hi):
    x=I(lo,hi);a=cos_point_int(lo);b=cos_point_int(hi);L=min(a.lo,b.lo);H=max(a.hi,b.hi)
    for k in range(-4,5):
        c=I.frac(F(k))*PI
        if overlap(x,c):
            v=S if k%2==0 else -S;L=min(L,v);H=max(H,v)
    return I(max(-S,L),min(S,H))
def sinR(x):x=iv(x);return sin_cached(x.lo,x.hi)
def cosR(x):x=iv(x);return cos_cached(x.lo,x.hi)

@dataclass(frozen=True)
class J:
    v:I; d:I=ZERO; dd:I=ZERO
    def __init__(self,v,d=0,dd=0):
        object.__setattr__(self,'v',iv(v));object.__setattr__(self,'d',iv(d));object.__setattr__(self,'dd',iv(dd))
    def __add__(self,o):o=jj(o);return J(self.v+o.v,self.d+o.d,self.dd+o.dd)
    __radd__=__add__
    def __neg__(self):return J(-self.v,-self.d,-self.dd)
    def __sub__(self,o):return self+(-jj(o))
    def __rsub__(self,o):return jj(o)-self
    def __mul__(self,o):
        o=jj(o);return J(self.v*o.v,self.d*o.v+self.v*o.d,self.dd*o.v+2*self.d*o.d+self.v*o.dd)
    __rmul__=__mul__
    def inv(self):
        v2=self.v*self.v;v3=v2*self.v
        return J(self.v.inv(),-self.d/v2,2*self.d*self.d/v3-self.dd/v2)
    def __truediv__(self,o):return self*jj(o).inv()
    def __rtruediv__(self,o):return jj(o)/self

def jj(x):return x if isinstance(x,J) else J(x)
def hullJ(*z):return J(hullI(*(a.v for a in z)),hullI(*(a.d for a in z)),hullI(*(a.dd for a in z)))
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

rt2=sqrtI(I.frac(2));h=ONE/rt2
A=(F(1466)+F(1940)*h)/F(267);B=(F(327)+F(432)*h)/F(712)
disc=A*A-4*B;ss=2*B/(A+sqrtI(disc));qstar=2*ss*ss+4*ss+F(5,2)
R=sqrtI(qstar);rho=sqrtI(qstar-F(1,4))-F(1,2);c0=rho-1

def support_ordered(U,V,norm):
    cap=J(rho)*U;vert=J(R)*norm-(U+V)/2;sw=2*R*V.v-norm.v
    if sw.hi<=0:return cap
    if sw.lo>=0:return vert
    return hullJ(cap,vert)
def jsq(x):
    x=jj(x); a=abs(x.v)
    return J(a*a,2*x.v*x.d,2*x.d*x.d+2*x.v*x.dd)
def support_any(x,y):
    x,y=jj(x),jj(y);ax,ay=jabs(x),jabs(y);norm=jsqrt(jsq(x)+jsq(y))
    if ax.v.lo>=ay.v.hi:return support_ordered(ax,ay,norm)
    if ay.v.lo>=ax.v.hi:return support_ordered(ay,ax,norm)
    return hullJ(support_ordered(ax,ay,norm),support_ordered(ay,ax,norm))

def parts(lo,hi,step):
    lo=F(lo);hi=F(hi);step=F(step);x=lo
    while x<hi:
        y=min(x+step,hi);yield x,y;x=y

if __name__=='__main__':
    print('fixed core PASS',R.f(),rho.f(),c0.f())
