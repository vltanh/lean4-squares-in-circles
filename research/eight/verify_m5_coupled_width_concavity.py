#!/usr/bin/env python3
"""Exact-dyadic regressions for the M5 coupled-width hand proof.
No floating-point trigonometry, optimizer, or continuum proof oracle.
"""
from fractions import Fraction as F
from math import isqrt
from random import Random
from itertools import combinations

SCALE=1<<100
class I:
    def __init__(self,lo,hi=None):
        self.lo=int(lo);self.hi=int(lo if hi is None else hi)
        assert self.lo<=self.hi
    @classmethod
    def rational(cls,q):
        q=F(q);a=q.numerator*SCALE;b=q.denominator
        return cls(a//b,-((-a)//b))
    def __add__(self,b):
        b=b if isinstance(b,I) else I.rational(b)
        return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-b if isinstance(b,I) else self+-I.rational(b)
    def __rsub__(self,b):return I.rational(b)+-self
    def __mul__(self,b):
        b=b if isinstance(b,I) else I.rational(b)
        ps=[a*c for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        return I(min(ps)//SCALE,-((-max(ps))//SCALE))
    __rmul__=__mul__
    def __truediv__(self,b):
        if not isinstance(b,I):return self*I.rational(1/F(b))
        assert b.lo>0
        vals=[F(a*SCALE,c) for a in (self.lo,self.hi) for c in (b.lo,b.hi)]
        lo=min(vals);hi=max(vals)
        return I(lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator))

def atan_point(z):
    z=F(z);v=F(0)
    for k in range(25):v+=(-1)**k*z**(2*k+1)/(2*k+1)
    upper=v;lower=v-z**51/51
    return I(I.rational(lower).lo,I.rational(upper).hi)

H=4*atan_point(F(1,5))-atan_point(F(1,239))
sq=isqrt(2*SCALE*SCALE);ROOT2=I(sq,sq+1)
KAPPA=(ROOT2-1)/2;KAPPA2=(2*ROOT2-1)/4

def sincos(x):
    assert x.lo>=0 and x.hi<=2*SCALE
    xx=x*x;st=x;ct=I.rational(1);sp=st;cp=ct
    for k in range(1,25):
        st=-(st*xx)/((2*k)*(2*k+1));ct=-(ct*xx)/((2*k-1)*(2*k))
        sp=sp+st;cp=cp+ct
    snext=-(st*xx)/(50*51);cnext=-(ct*xx)/(49*50)
    return I((sp+snext).lo,sp.hi),I((cp+cnext).lo,cp.hi)

WORDS=('LHLHLHLL','LHLLHHLL')
PAIRS=list(combinations(range(8),2))

def cut(word,k):
    labels=[int(c=='H') ^ int(i>=k) for i,c in enumerate(word)]
    return labels,[labels[i]!=labels[j] for i,j in PAIRS]

def check_word(word,rng):
    sizes=[];cuts=[]
    for k in range(1,9):
        labels,mask=cut(word,k);sizes.append(labels.count(0));cuts.append(mask)
        assert sum(mask)==(16 if k%2 else 15)
    expected=(4,3,4,3,4,3,4,5) if word==WORDS[0] else (4,3,4,5,4,3,4,5)
    assert tuple(sizes)==expected
    for trial in range(32):
        x=[F(0)]+[F(v,1000) for v in sorted(rng.sample(range(1,1000),7))]
        theta=[v+int(c=='H') for v,c in zip(x,word)]
        counts=[sum((b-a)%2<=1 for b in theta) for a in theta]
        assert max(counts)==5
        weights=[rng.randrange(1,8) for _ in PAIRS]
        ws=[];ws2=[];energy=I.rational(0);variance=F(0);wvariance=F(0)
        for a,(i,j) in zip(weights,PAIRS):
            dr=x[j]-x[i];si,co=sincos(H*dr)
            wi=(1+si+co)/2 if word[i]==word[j] else (1+ROOT2*co)/2
            ws.append(wi);ws2.append(wi*wi)
            sn,cn=sincos(H*(2*dr));energy+=sn if word[i]==word[j] else cn
            variance+=dr*(1-dr);wvariance+=a*dr*(1-dr)
        W=sum(ws,I.rational(0));W2=sum(ws2,I.rational(0))
        A=sum((x[i]-x[i-1] for i in (1,3,5,7)),F(0))
        rhs=(41+15*ROOT2)/2+KAPPA*A+(H*H)*(variance/4)
        rhs2=(97+30*ROOT2)/4+KAPPA2*A+(H*H)*(variance/4)
        assert W.lo>rhs.hi and W2.lo>rhs2.hi
        assert energy.lo>=15*SCALE
        mincut=min(sum(a for a,yes in zip(weights,mask) if yes) for mask in cuts)
        b=sum(weights);v1=sum((a*w for a,w in zip(weights,ws)),I.rational(0))
        v2=sum((a*w for a,w in zip(weights,ws2)),I.rational(0))
        lower=b+KAPPA*mincut+(H*H)*(wvariance/4)
        lower2=b+KAPPA2*mincut+(H*H)*(wvariance/4)
        assert v1.lo>lower.hi and v2.lo>lower2.hi
    return 32

def main():
    rng=Random(20261013);n=sum(check_word(w,rng) for w in WORDS)
    print('Both eight-cut tables, including all 16 endpoint colorings: PASS')
    print(f'{n} exact maximum-five frame tests: weighted and uniform width/squared-width bounds: PASS')
    print('Quantitative concavity reserves and doubled-angle dispersion: PASS')
    print('All comparisons use outward integer-dyadic enclosures and rational arithmetic.')
    print('The continuum theorem is the concavity proof, not these finite tests.')

if __name__=='__main__':main()
