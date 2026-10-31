"""Exact rational enclosure certificate for the S123 opposite-root owned star.

This file uses only integer/Fraction arithmetic.  The interval lattice is
2**-40; every operation rounds outwards.  The adaptive cover is an exact
binary partition of the displayed closed rational initial box.  No sample,
pose search, floating-point value, or numerical tolerance enters a decision.
"""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt

D = 1 << 40

def floorq(q):
    return q.numerator // q.denominator

def ceilq(q):
    return -((-q.numerator) // q.denominator)

class I:
    __slots__ = ('lo', 'hi')
    def __init__(self, lo, hi):
        self.lo, self.hi = lo, hi
    @staticmethod
    def rational(q):
        q = Q(q)
        return I(floorq(q*D), ceilq(q*D))
    @staticmethod
    def range(lo, hi):
        return I(floorq(Q(lo)*D), ceilq(Q(hi)*D))
    def __add__(a,b):
        b=cv(b); return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-cv(b)
    def __rsub__(a,b):return cv(b)+-a
    def __mul__(a,b):
        b=cv(b)
        v=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
        return I(min(v)//D,-((-max(v))//D))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=cv(b)
        if b.lo<=0:raise ArithmeticError('nonpositive interval divisor')
        return a*I((D*D)//b.hi,-((-(D*D))//b.lo))
    def __rtruediv__(a,b):return cv(b)/a
    def sq(a):
        lo=0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi)
        hi=max(a.lo*a.lo,a.hi*a.hi)
        return I(lo//D,-((-hi)//D))
    def sqrt(a):
        if a.hi<0:raise ArithmeticError('negative square root')
        lo=isqrt(max(0,a.lo)*D)
        v=a.hi*D; hi=isqrt(v)
        if hi*hi<v:hi+=1
        return I(lo,hi)
    def intersect(a,b):
        return I(max(a.lo,b.lo),min(a.hi,b.hi))
    def empty(a):return a.lo>a.hi
    def above(a,q):return Q(a.lo,D)>q
    def below(a,q):return Q(a.hi,D)<q

def cv(x):return x if isinstance(x,I) else I.rational(x)

RHO=(cv(Q(13,4)).sqrt()-1)
RHO2=RHO.sq()
HALF=cv(Q(1,2))
HMAX=cv(Q(33,35))
UNIT=I(0,D)

def check(box):
    A,F,p,R2=(I.range(lo,hi) for lo,hi in box)
    L=(1+p.sq()).sqrt(); r=p/L; s=1/L
    H=A*r+F*s; z=-A*s+F*r
    # The literal geometric guards in the theorem are strict.
    if (A.sq()+F.sq()).lo>=D or H.hi<=HALF.lo or z.hi<=0:
        return 'empty',None
    H=H.intersect(I(HALF.lo,HMAX.hi))
    if H.empty():return 'empty',None
    S=H+1; W=(R2-S.sq()).sqrt()
    try:
        lam=z*S/W-H
        eta=z+1-W
    except ArithmeticError:
        return 'split',None
    if lam.hi<0 or eta.hi<0 or eta.lo>D:
        return 'empty',None
    lam=lam.intersect(UNIT); eta=eta.intersect(UNIT)
    if lam.empty() or eta.empty():return 'empty',None
    b=1-F
    v=b*(1-p)/(p*(1-b-Q(3,5)*b.sq()))
    if v.hi>=p.lo:return 'split',None
    # Complete far-return support, before assigning an M mask.
    try:
        far=(S*(1-lam)-(W-1)*eta)/((1-lam).sq()+eta.sq()).sqrt()
    except ArithmeticError:
        return 'split',None
    if not far.above(Q(61,60)):return 'split',None
    result={'far':far.lo,'v_gap':p.lo-v.hi}
    for kind in ('near','side'):
        if kind=='near':
            # The exact sharp boundary-contact lemma gives W<=1.
            if W.lo>D:continue
            WW=W.intersect(I(0,D))
            HH=H.intersect(I(RHO.lo,HMAX.hi))
            if HH.empty():continue
            qm=HH
        else:
            WW=W; qm=z*S/W
        Qx=qm*r-(WW-1)*s
        Qy=qm*s+(WW-1)*r
        if (Qx.sq()+Qy.sq()).hi<RHO2.lo:continue
        if Qx.lo<=0 or Qy.lo<=0:return 'split',None
        qnl=(Qx-v*Qy)/(1+v.sq()).sqrt()
        qfu=Qy+v*Qx
        qfl=Qy/(1+v.sq()).sqrt()
        if not (qnl.above(Q(1,8)) and Qx.below(Q(3,4))
                and qfu.below(Q(9,10)) and qfl.above(Q(1,10))):
            return 'split',None
        result[kind]=(qnl.lo,Qx.hi,qfl.lo,qfu.hi)
    return 'pass',result

def run():
    initial=((Q(-1,60),Q(1,60)),(Q(37,50),Q(1)),
             (Q(13,40),Q(1)),(Q(17,4),Q(1105,256)))
    scales=(4,3,3,1)
    stack=[(initial,0)]
    count=Counter(); depths=Counter(); rows={}
    extrema={'far':10*D,'v_gap':10*D,'qnl':10*D,'qxu':-10*D,
             'qfl':10*D,'qfu':-10*D}
    while stack:
        box,depth=stack.pop()
        status,result=check(box)
        count[status]+=1; depths[depth]+=1
        if status=='split':
            assert depth<24,('unresolved exact cell',box)
            j=max(range(4),key=lambda j:(box[j][1]-box[j][0])*scales[j])
            lo,hi=box[j];mid=(lo+hi)/2
            for segment in ((lo,mid),(mid,hi)):
                child=list(box);child[j]=segment
                stack.append((tuple(child),depth+1))
        elif status=='pass':
            extrema['far']=min(extrema['far'],result['far'])
            extrema['v_gap']=min(extrema['v_gap'],result['v_gap'])
            for kind in ('near','side'):
                if kind not in result:continue
                a,b,c,d=result[kind]
                extrema['qnl']=min(extrema['qnl'],a)
                extrema['qxu']=max(extrema['qxu'],b)
                extrema['qfl']=min(extrema['qfl'],c)
                extrema['qfu']=max(extrema['qfu'],d)
    assert count['pass']+count['empty']==count['split']+1
    print('lattice denominator',D)
    print('exact cover counts',dict(sorted(count.items())))
    print('maximum depth',max(depths))
    print('visited nodes by depth',dict(sorted(depths.items())))
    print('enclosure endpoint numerators / lattice denominator')
    for k in sorted(extrema):print(k,extrema[k])
    margins={
        'far_minus_61_60':Q(extrema['far'],D)-Q(61,60),
        'p_minus_v':Q(extrema['v_gap'],D),
        'Qn_minus_1_8':Q(extrema['qnl'],D)-Q(1,8),
        '3_4_minus_Qn':Q(3,4)-Q(extrema['qxu'],D),
        'Qf_minus_1_10':Q(extrema['qfl'],D)-Q(1,10),
        '9_10_minus_Qf':Q(9,10)-Q(extrema['qfu'],D),
    }
    print('strict rational margins')
    for k,v in sorted(margins.items()):
        assert v>0,(k,v)
        print(k,str(v))
    return count,depths,extrema,margins

if __name__=='__main__':run()
