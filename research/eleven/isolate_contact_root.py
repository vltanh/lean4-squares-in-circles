#!/usr/bin/env python3
"""Exact rational interval contraction certificate for the contact family."""
from fractions import Fraction as F
from math import isqrt
from contact_family import family

if not __debug__:
    raise RuntimeError("Run without -O: this certificate uses assertions.")

class I:
    def __init__(self,lo,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi;return
        self.lo=F(lo); self.hi=F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,o):
        o=I(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-I(o)
    def __rsub__(self,o):return I(o)+-self
    def __mul__(self,o):
        o=I(o);a=[x*y for x in (self.lo,self.hi) for y in (o.lo,o.hi)];return I(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=I(o);assert o.lo*o.hi>0
        return self*I(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):return I(o)/self
    def __pow__(self,n):
        assert n==2
        if self.lo>=0:return I(self.lo**2,self.hi**2)
        if self.hi<=0:return I(self.hi**2,self.lo**2)
        return I(0,max(self.lo**2,self.hi**2))
    def sqrt(self):
        assert self.lo>=0
        D=10**35
        a=isqrt(self.lo.numerator*D*D//self.lo.denominator)
        b=isqrt(self.hi.numerator*D*D//self.hi.denominator)+1
        return I(F(a,D),F(b,D))
    def abs_upper(self):return max(abs(self.lo),abs(self.hi))
    def __abs__(self):
        if self.lo>=0:return self
        if self.hi<=0:return -self
        return I(0,self.abs_upper())
    def approx(self):return [float(self.lo),float(self.hi)]

class D:
    def __init__(self,x,grad=None):
        if isinstance(x,D):self.x,self.grad=x.x,x.grad;return
        self.x=I(x);self.grad=[I(z) for z in (grad if grad is not None else [0,0])]
    def __add__(self,o):
        o=D(o);return D(self.x+o.x,[a+b for a,b in zip(self.grad,o.grad)])
    __radd__=__add__
    def __neg__(self):return D(-self.x,[-x for x in self.grad])
    def __sub__(self,o):return self+-D(o)
    def __rsub__(self,o):return D(o)+-self
    def __mul__(self,o):
        o=D(o);return D(self.x*o.x,[a*o.x+self.x*b for a,b in zip(self.grad,o.grad)])
    __rmul__=__mul__
    def __truediv__(self,o):
        o=D(o);return D(self.x/o.x,[(a*o.x-self.x*b)/(o.x**2) for a,b in zip(self.grad,o.grad)])
    def __rtruediv__(self,o):return D(o)/self
    def __pow__(self,n):
        assert n==2;return D(self.x**2,[2*self.x*a for a in self.grad])
    def sqrt(self):
        y=self.x.sqrt();return D(y,[a/(2*y) for a in self.grad])


def certificate():
    x0=[F('4.901206412408144'),F('0.2054740374066444')]
    radii=[F(1,10**9),F(1,10**9)]
    box=[I(x-r,x+r) for x,r in zip(x0,radii)]
    fx=family(D(box[0],[1,0]),D(box[1],[0,1]),lambda x:x.sqrt())[0]
    jac=[row.grad for row in fx]
    # Rational approximate inverse; its provenance is irrelevant to verification.
    C=[[F('0.41567770'),F('0.45546983')],[F('0.82609008'),F('-0.56097775')]]
    assert C[0][0]*C[1][1]-C[0][1]*C[1][0] != 0
    assert max(sum(abs(z) for z in row) for row in C) < 2
    f0=family(I(x0[0]),I(x0[1]),lambda x:x.sqrt())[0]
    digest = [[I('0.9204730', '0.9204731'), I('0.7473516', '0.7473520')],
              [I('1.3554791', '1.3554793'), I('-0.6820595', '-0.6820592')]]
    for i in range(2):
        assert f0[i].abs_upper() < F(1, 10**15)
        for j in range(2):
            assert digest[i][j].lo <= jac[i][j].lo <= jac[i][j].hi <= digest[i][j].hi
    digest_A = [[I(int(i == j)) - sum(C[i][k]*digest[k][j] for k in range(2))
                 for j in range(2)] for i in range(2)]
    assert max(sum(z.abs_upper() for z in row) for row in digest_A) < F(1, 10**6)
    A=[[I(int(i==j))-sum(C[i][k]*jac[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
    residual=[-sum(C[i][k]*f0[k] for k in range(2)) for i in range(2)]
    errors=[residual[i]+sum(A[i][j]*I(-radii[j],radii[j]) for j in range(2)) for i in range(2)]
    for i in range(2):
        assert errors[i].abs_upper() < F(3, 10**15) < radii[i]
    norm=max(sum(A[i][j].abs_upper()*radii[j]/radii[i] for j in range(2)) for i in range(2))
    assert norm < F(1, 10**6)
    print('PASS strict self-map and contraction; root unique in rational box.')
    print('box',[(str(z.lo),str(z.hi)) for z in box])
    print('Krawczyk errors',[z.approx() for z in errors]);print('weighted contraction bound',float(norm))
    return box



def packing_certificate(box):
    import json
    from pathlib import Path
    from itertools import product
    _,p,angles,extra=family(box[0],box[1],lambda x:x.sqrt())
    (ca,sa),(cb,sb)=angles
    r,w,v,z=extra
    cd, sd = (1-v*v)/(1+v*v), 2*v/(1+v*v)
    assert 0 < v.lo <= v.hi < 1 and w.lo > 1
    assert all(value.lo > 0 for value in (ca, sa, cb, sb, cd, sd))
    ka=(1+ca+sa)/2
    a,b=p[0]
    H=(ka+1-r-sa*(b-1))/ca
    assert H.hi < a.lo
    p[1]=(I(H.lo,a.hi),b-1)
    frames=[((I(1),I(0)),(I(0),I(1)))]*7+[((ca,sa),(-sa,ca))]*2+[((cb,sb),(-sb,cb))]*2
    dot=lambda x,y:sum(u*v for u,v in zip(x,y))
    # These ten disk equalities hold identically by the family formulas.
    disk_contacts={(0,1,1),(2,1,1),(3,1,-1),(5,1,-1),(6,-1,-1),(7,-1,-1),(7,-1,1),(9,-1,1),(10,-1,1),(10,1,1)}
    disk_slacks=[]
    for i in range(11):
        u,vv=frames[i]
        for ee,ff in product([-1,1],repeat=2):
            if (i,ee,ff) in disk_contacts:continue
            pt=tuple(p[i][k]+(ee*u[k]+ff*vv[k])/2 for k in range(2))
            slack=box[0]-dot(pt,pt)
            assert slack.lo>F(1,2),(i,ee,ff,slack.approx())
            disk_slacks.append(slack)
    # Fourteen equalities plus the two inequalities defining the slider interval.
    pair_contacts={(0,1),(0,2),(0,10),(1,4),(2,3),(3,4),(4,5),(4,8),(5,6),(6,7),(7,8),(7,9),(8,9),(9,10),(1,2),(1,8)}
    witnesses=json.loads(Path(__file__).with_name('RATIONAL_WITNESS.json').read_text())['separators']
    assert len(witnesses) == 55
    assert {(s['i'], s['j']) for s in witnesses} == {(i,j) for i in range(11) for j in range(i+1,11)}
    pair_slacks=[]
    for entry in witnesses:
        i,j,owner,sign=entry['i'],entry['j'],entry['owner'],entry['sign']
        assert owner in (i,j) and sign in (-1,1) and entry['axis'] in ('u','v')
        if (i,j) in pair_contacts:continue
        ax=frames[owner][0 if entry['axis']=='u' else 1]
        direction=tuple(sign*z for z in ax)
        delta=tuple(p[j][k]-p[i][k] for k in range(2))
        support=sum(abs(dot(direction,w)) for k in [i,j] for w in frames[k])/2
        slack=dot(direction,delta)-support
        assert slack.lo>F(1,100),(i,j,slack.approx())
        pair_slacks.append(slack)
    assert len(disk_slacks) == 34 and len(pair_slacks) == 39
    print('PASS: 34 inactive vertex inequalities with slack > 1/2; 39 inactive pair inequalities with slack > 1/100.')
    print('Ten vertex equalities and fourteen pair equalities follow by algebra; two slider inequalities follow from H <= h <= a.')
    print('Slider endpoints enclosed:',H.approx(),a.approx())

if __name__=='__main__':
    packing_certificate(certificate())
