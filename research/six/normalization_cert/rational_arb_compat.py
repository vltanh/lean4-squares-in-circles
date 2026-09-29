"""Independent exact-dyadic arithmetic for the normalization predicates.

This is NOT python-flint or Arb. It implements only the operations used by
normalization_cert, with endpoints in units of 2^-96. Rational and float
inputs are enclosed with integer floor/ceiling; floats are exact dyadics.
Products and quotients round outward; roots use isqrt. Sin/cos use Taylor
polynomials with Lagrange remainders and include every possible critical point.
Inverse functions use monotone certified bisection, stopping conservatively
when rounding prevents a decision. This backend is for independent replay,
not a replacement for a Lean correctness theorem about the checker.
"""
from fractions import Fraction
from functools import lru_cache
from math import factorial,isqrt

BITS = 96
SCALE = 1 << BITS
__certificate_backend__ = 'independent exact-dyadic intervals, 96-bit units (NOT Arb)'


def ceildiv(a,b):
    if b<=0: raise ValueError('positive divisor required')
    return -((-a)//b)


class _Context:
    # The input module requests 64 bits; actual endpoint units remain 2^-96.
    prec = 64


ctx = _Context()


def _atan_small(x,terms=30):
    s = sum(((-1)**k*x**(2*k+1)/(2*k+1) for k in range(terms)),Fraction(0))
    r = x**(2*terms+1)/(2*terms+1)
    return (s,s+r) if terms%2==0 else (s-r,s)


_p5 = _atan_small(Fraction(1,5))
_p239 = _atan_small(Fraction(1,239))
_PI_LO = 16*_p5[0]-4*_p239[1]
_PI_HI = 16*_p5[1]-4*_p239[0]


class arb:
    __slots__ = ('l','h')

    def __init__(self,value=0):
        if isinstance(value,arb): self.l,self.h = value.l,value.h
        else:
            q = Fraction(value)
            self.l = q.numerator*SCALE//q.denominator
            self.h = ceildiv(q.numerator*SCALE,q.denominator)

    @classmethod
    def raw(cls,l,h):
        if l>h: raise ValueError('reversed interval')
        obj = object.__new__(cls)
        obj.l,obj.h = l,h
        return obj

    @classmethod
    def pi(cls): return cls.raw(arb(_PI_LO).l,arb(_PI_HI).h)

    def __add__(self,other):
        b = arb(other)
        return arb.raw(self.l+b.l,self.h+b.h)
    __radd__ = __add__
    def __neg__(self): return arb.raw(-self.h,-self.l)
    def __sub__(self,other): return self+(-arb(other))
    def __rsub__(self,other): return arb(other)+(-self)

    def __mul__(self,other):
        b = arb(other)
        p = (self.l*b.l,self.l*b.h,self.h*b.l,self.h*b.h)
        return arb.raw(min(p)//SCALE,ceildiv(max(p),SCALE))
    __rmul__ = __mul__

    def inv(self):
        if self.l<=0<=self.h: raise ValueError('division by interval containing zero')
        if self.h<0: return -(-self).inv()
        return arb.raw(SCALE*SCALE//self.h,ceildiv(SCALE*SCALE,self.l))
    def __truediv__(self,other): return self*arb(other).inv()
    def __rtruediv__(self,other): return arb(other)*self.inv()

    def __abs__(self):
        if self.l>=0: return self
        if self.h<=0: return -self
        return arb.raw(0,max(-self.l,self.h))

    def __pow__(self,n):
        if not isinstance(n,int): raise TypeError('integer powers only')
        if n<0: return (self**(-n)).inv()
        if n==0: return arb(1)
        den = SCALE**(n-1)
        if n%2==0:
            a = abs(self)
            return arb.raw(a.l**n//den,ceildiv(a.h**n,den))
        return arb.raw(self.l**n//den,ceildiv(self.h**n,den))

    def __lt__(self,other): return self.h<arb(other).l
    def __le__(self,other): return self.h<=arb(other).l
    def __gt__(self,other): return self.l>arb(other).h
    def __ge__(self,other): return self.l>=arb(other).h
    def __float__(self): return float(Fraction(self.l+self.h,2*SCALE))
    def __repr__(self): return '[%.17g, %.17g]'%(self.l/SCALE,self.h/SCALE)
    def lower(self): return arb.raw(self.l,self.l)
    def upper(self): return arb.raw(self.h,self.h)
    def mid(self): return arb(Fraction(self.l+self.h,2*SCALE))

    def union(self,other):
        b = arb(other)
        return arb.raw(min(self.l,b.l),max(self.h,b.h))
    def min(self,other):
        b = arb(other)
        return arb.raw(min(self.l,b.l),min(self.h,b.h))
    def max(self,other):
        b = arb(other)
        return arb.raw(max(self.l,b.l),max(self.h,b.h))
    def nonnegative_part(self): return self.max(0)

    def sqrt(self):
        if self.l<0: raise ValueError('sqrt with negative lower bound')
        l,h = isqrt(self.l*SCALE),isqrt(self.h*SCALE)
        if h*h<self.h*SCALE: h+=1
        return arb.raw(l,h)

    def sin_cos(self): return _trig_range(self.l,self.h)
    def sin(self): return self.sin_cos()[0]
    def cos(self): return self.sin_cos()[1]
    def tan(self):
        s,c = self.sin_cos()
        return s/c
    def asin(self):
        if self.l<-SCALE or self.h>SCALE: raise ValueError('asin outside [-1,1]')
        return arb.raw(_inverse_point(self.l,'asin')[0],_inverse_point(self.h,'asin')[1])
    def atan(self):
        return arb.raw(_inverse_point(self.l,'atan')[0],_inverse_point(self.h,'atan')[1])


@lru_cache(maxsize=200000)
def _trig_point(x):
    # sin Taylor degree 73 / Lagrange remainder order 74;
    # cos Taylor degree 72 / Lagrange remainder order 73.
    a = arb.raw(x,x)
    a2 = a*a
    st,ct = a,arb(1)
    sn,cs = st,ct
    for k in range(1,37):
        st = st*a2/((2*k)*(2*k+1))
        ct = ct*a2/((2*k-1)*(2*k))
        if k%2: sn,cs = sn-st,cs-ct
        else: sn,cs = sn+st,cs+ct
    rs = ceildiv(abs(x)**74,SCALE**73*factorial(74))
    rc = ceildiv(abs(x)**73,SCALE**72*factorial(73))
    return arb.raw(sn.l-rs,sn.h+rs),arb.raw(cs.l-rc,cs.h+rc)


@lru_cache(maxsize=200000)
def _trig_range(l,h):
    p = arb.pi()
    if h-l>=2*p.l or l<-16*SCALE or h>16*SCALE:
        return arb.raw(-SCALE,SCALE),arb.raw(-SCALE,SCALE)
    sa,ca = _trig_point(l)
    sb,cb = _trig_point(h)
    sl,sh = min(sa.l,sb.l),max(sa.h,sb.h)
    cl,ch = min(ca.l,cb.l),max(ca.h,cb.h)
    # Includes all critical points in [-16,16].
    for k in range(-12,13):
        z = p*k/2
        if z.h<l or z.l>h: continue
        if k%2:
            v = SCALE if k%4==1 else -SCALE
            sl,sh = min(sl,v),max(sh,v)
        else:
            v = SCALE if k%4==0 else -SCALE
            cl,ch = min(cl,v),max(ch,v)
    return arb.raw(max(-SCALE,sl),min(SCALE,sh)),arb.raw(max(-SCALE,cl),min(SCALE,ch))


@lru_cache(maxsize=1000)
def _inverse_point(x,kind):
    if x==0: return 0,0
    p = arb.pi()
    l,h = (-p/2).l,(p/2).h
    if kind=='asin' and x==SCALE: return (p/2).l,(p/2).h
    if kind=='asin' and x==-SCALE: return (-p/2).l,(-p/2).h
    target = arb.raw(x,x)
    for _ in range(BITS+10):
        if h-l<=1: break
        m = (l+h)//2
        f = arb.raw(m,m)
        y = f.sin() if kind=='asin' else f.tan()
        if y<target: l=m
        elif y>target: h=m
        else: break  # retain the enclosing bracket, never guess a side
    return l,h
