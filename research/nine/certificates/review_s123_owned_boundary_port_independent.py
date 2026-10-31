from fractions import Fraction as F
from math import isqrt
from collections import Counter

# Independent audit: exact Fraction endpoints; only square roots are
# enclosed, on a finer 2^-48 lattice. No author interval class is imported.
SCALE=1<<48
class J:
    def __init__(self,lo,hi=None):
        self.l=F(lo); self.h=F(lo if hi is None else hi)
    def __add__(self,other):
        o=j(other); return J(self.l+o.l,self.h+o.h)
    __radd__=__add__
    def __neg__(self):return J(-self.h,-self.l)
    def __sub__(self,other):return self+-j(other)
    def __rsub__(self,other):return j(other)+-self
    def __mul__(self,other):
        o=j(other); v=[self.l*o.l,self.l*o.h,self.h*o.l,self.h*o.h]
        return J(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,other):
        o=j(other)
        if o.l<=0:raise ValueError('divisor not positive')
        return self*J(1/o.h,1/o.l)
    def __rtruediv__(self,other):return j(other)/self
    def square(self):
        low=F(0) if self.l<=0<=self.h else min(self.l*self.l,self.h*self.h)
        return J(low,max(self.l*self.l,self.h*self.h))
    def root(self):
        if self.h<0:raise ValueError('empty root domain')
        def bounds(q):
            q=max(F(0),q); n=q.numerator*SCALE*SCALE;d=q.denominator
            k=isqrt(n//d)
            return F(k,SCALE),F(k+(k*k*d<n),SCALE)
        return J(bounds(self.l)[0],bounds(self.h)[1])
    def clip(self,low,high):return J(max(self.l,F(low)),min(self.h,F(high)))
    def empty(self):return self.l>self.h

def j(x):return x if isinstance(x,J) else J(x)
rmin=(J(F(13,4)).root()-1)
rmin2=rmin.square()

bounds={'far':None,'vgap':None,'qnlow':None,'qnhigh':None,'qflow':None,'qfhigh':None}
def update(name,value,maximum=False):
    if bounds[name] is None:bounds[name]=value
    else:bounds[name]=(max if maximum else min)(bounds[name],value)

def test(box):
    A,F0,p,V=[J(*q) for q in box]
    ll=(1+p.square()).root(); r=p/ll;s=1/ll
    H=A*r+F0*s;z=-A*s+F0*r
    if (A.square()+F0.square()).l>=1 or H.h<=F(1,2) or z.h<=0:return 'empty'
    H=H.clip(F(1,2),F(33,35))
    if H.empty():return 'empty'
    SS=H+1;W=(V-SS.square()).root()
    try:
        lm=z*SS/W-H;eta=z+1-W
    except ValueError:return 'split'
    lm=lm.clip(0,1);eta=eta.clip(0,1)
    if lm.empty() or eta.empty():return 'empty'
    bb=1-F0
    vb=bb*(1-p)/(p*(1-bb-F(3,5)*bb.square()))
    if vb.h>=p.l:return 'split'
    try:
        far=(SS*(1-lm)-(W-1)*eta)/((1-lm).square()+eta.square()).root()
    except ValueError:return 'split'
    if far.l<=F(61,60):return 'split'
    rows=[]
    for near in [True,False]:
        if near:
            WW=W.clip(0,1);HH=H.clip(rmin.l,F(33,35))
            if WW.empty() or HH.empty():continue
            qm=HH
        else:WW=W;qm=z*SS/W
        q1=qm*r-(WW-1)*s;q2=qm*s+(WW-1)*r
        if (q1.square()+q2.square()).h<rmin2.l:continue
        if q1.l<=0 or q2.l<=0:return 'split'
        den=(1+vb.square()).root()
        qn=(q1-vb*q2)/den;qfl=q2/den;qfu=q2+vb*q1
        if not(qn.l>F(1,8) and q1.h<F(3,4) and qfl.l>F(1,10) and qfu.h<F(9,10)):
            return 'split'
        rows.append((qn.l,q1.h,qfl.l,qfu.h))
    update('far',far.l);update('vgap',p.l-vb.h)
    for qn,qx,qf,qfu in rows:
        update('qnlow',qn);update('qnhigh',qx,True);update('qflow',qf);update('qfhigh',qfu,True)
    return 'pass'

initial=((F(-1,60),F(1,60)),(F(37,50),F(1)),(F(13,40),F(1)),(F(17,4),F(1105,256)))
stack=[(initial,0)];counts=Counter();depths=Counter();scales=(4,3,3,1)
while stack:
    box,dep=stack.pop();status=test(box);counts[status]+=1;depths[dep]+=1
    if status=='split':
        assert dep<24
        i=max(range(4),key=lambda k:(box[k][1]-box[k][0])*scales[k]);lo,hi=box[i];mid=(lo+hi)/2
        for childint in [(lo,mid),(mid,hi)]:
            child=list(box);child[i]=childint;stack.append((tuple(child),dep+1))
assert counts['pass']+counts['empty']==counts['split']+1
print('independent exact Fraction counts',dict(sorted(counts.items())))
print('maximum depth',max(depths))
print('depth counts',[depths[k] for k in range(max(depths)+1)])
# Short exact rational lower bounds for the strict margins. Each is
# independently rounded down on the audit lattice after the proof run.
margins={
    'far':bounds['far']-F(61,60),'vgap':bounds['vgap'],
    'qnlow':bounds['qnlow']-F(1,8),'qnhigh':F(3,4)-bounds['qnhigh'],
    'qflow':bounds['qflow']-F(1,10),'qfhigh':F(9,10)-bounds['qfhigh']}
for name,value in sorted(margins.items()):
    assert value>0
    lower=F((value*SCALE).numerator//(value*SCALE).denominator,SCALE)
    assert lower>0
    print('strict margin lower bound',name,str(lower))

