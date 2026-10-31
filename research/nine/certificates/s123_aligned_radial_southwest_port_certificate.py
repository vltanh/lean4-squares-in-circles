"""Exact rational enclosure certificate for the aligned S123 radial Southwest star.

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
UNIT=I(0,D)
QMAX=cv(Q(1105,256))

def absi(a):
    return I(0,max(-a.lo,a.hi)) if a.lo<=0<=a.hi else I(min(abs(a.lo),abs(a.hi)),max(abs(a.lo),abs(a.hi)))

def check(box):
    a,K=(I.range(lo,hi) for lo,hi in box)
    b=1-a; LA=(K.sq()+a.sq()).sqrt(); LB=(K.sq()+b.sq()).sqrt()
    eps=a.sq()/(LA+K)
    if eps.above(Q(1,60)):return 'empty',None
    eps=eps.intersect(I.range(0,Q(1,60)))
    R2=(2+eps).sq()+Q(1,4)
    if R2.lo>QMAX.hi:return 'empty',None
    R2=R2.intersect(I.range(Q(17,4),Q(1105,256)))
    N=(b.sq()-eps*K)/LB; z=b*(K+eps)/LB
    N=N.intersect(UNIT)
    if N.empty():return 'empty',None
    S=N+1; rad=R2-S.sq()
    if rad.hi<0:return 'empty',None
    W=rad.sqrt().intersect(I.range(Q(1,2),Q(11,6)))
    if W.empty():return 'empty',None
    lam=z*S/W-N; eta=z+1-W
    if lam.hi<0 or lam.lo>D or eta.hi<0 or eta.lo>D:return 'empty',None
    lam=lam.intersect(UNIT);eta=eta.intersect(UNIT)
    dd=(K.sq()-a*b)/(LA*LB); ee=K/(LA*LB)
    bn=(N+Q(1,2))*dd-(W-Q(1,2))*ee
    bf=(N+Q(1,2))*ee+(W-Q(1,2))*dd
    # Strict genuine endpoint separation >80 degrees implies this weak guard.
    if (bn-Q(9,50)*absi(bf)).lo>=0:return 'empty',None
    if not dd.above(Q(1,4)):return 'split',None
    try:
        far=(S*(1-lam)-(W-1)*eta)/((1-lam).sq()+eta.sq()).sqrt()
    except ArithmeticError:return 'split',None
    if not far.above(Q(61,60)):return 'split',None
    result={'far':far.lo,'dd':dd.lo}
    rho=(R2-1).sqrt()-1
    for kind in ('near','side'):
        if kind=='near':
            if W.lo>D:continue
            WW=W.intersect(I.range(Q(1,2),1))
            NN=N.intersect(I(rho.lo,D))
            if NN.empty():continue
            qm=NN
        else:
            WW=W;qm=z*S/W
        qn=qm*dd-(WW-1)*ee
        qf=qm*ee+(WW-1)*dd
        if (qn.sq()+qf.sq()).hi<rho.sq().lo:continue
        if not (qn.above(Q(1,10)) and qn.below(Q(3,4)) and qf.above(Q(1,2)) and qf.below(Q(43,50))):
            return 'split',None
        result[kind]=(qn.lo,qn.hi,qf.lo,qf.hi)
    return 'pass',result

def run():
    initial=((Q(0),Q(29,100)),(Q(1,4),Q(7)))
    scales=(12,1)
    stack=[(initial,0)];count=Counter();depths=Counter()
    ext={'far':10*D,'dd':10*D,'qnl':10*D,'qnu':-10*D,'qfl':10*D,'qfu':-10*D}
    while stack:
        box,depth=stack.pop();status,result=check(box)
        count[status]+=1;depths[depth]+=1
        if status=='split':
            assert depth<30,('unresolved',box)
            j=max(range(2),key=lambda j:(box[j][1]-box[j][0])*scales[j])
            lo,hi=box[j];mid=(lo+hi)/2
            for seg in ((lo,mid),(mid,hi)):
                child=list(box);child[j]=seg;stack.append((tuple(child),depth+1))
        elif status=='pass':
            ext['far']=min(ext['far'],result['far']);ext['dd']=min(ext['dd'],result['dd'])
            for kind in ('near','side'):
                if kind not in result:continue
                l,u,f,g=result[kind];ext['qnl']=min(ext['qnl'],l);ext['qnu']=max(ext['qnu'],u);ext['qfl']=min(ext['qfl'],f);ext['qfu']=max(ext['qfu'],g)
    assert count['pass']+count['empty']==count['split']+1
    print('D',D);print('counts',dict(sorted(count.items())));print('depth',max(depths));print('nodes',dict(sorted(depths.items())))
    print('endpoints',ext)
    for name,val in [('far',Q(ext['far'],D)-Q(61,60)),('dd',Q(ext['dd'],D)-Q(1,4)),('qnl',Q(ext['qnl'],D)-Q(1,10)),('qnu',Q(3,4)-Q(ext['qnu'],D)),('qfl',Q(ext['qfl'],D)-Q(1,2)),('qfu',Q(43,50)-Q(ext['qfu'],D))]:
        assert val>0;print(name,val)

if __name__=='__main__':run()
