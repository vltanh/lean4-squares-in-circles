"""Fixed rational arithmetic for the whole edge-3 (+,-) outer quarter row.

Only the displayed point evaluations and universal rational bounds are checked.
There is no optimizer, adaptive cover, discovery-data input, or floating acceptance.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
import json

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I):self.lo,self.hi=a.lo,a.hi
        else:self.lo,self.hi=F(a),F(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(a,b):b=I(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);v=[x*y for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert not b.lo<=0<=b.hi
        return a*I(1/b.hi,1/b.lo)
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,n):
        assert n>=0
        if n==2:return I(0 if a.lo<=0<=a.hi else min(a.lo*a.lo,a.hi*a.hi),max(a.lo*a.lo,a.hi*a.hi))
        v=I(1)
        for _ in range(n):v=v*a
        return v
    def sqrt(a):
        assert a.lo>0
        den=10**14
        lo=F(isqrt(a.lo.numerator*den**2//a.lo.denominator),den)
        hi=F(isqrt(a.hi.numerator*den**2//a.hi.denominator)+1,den)
        assert lo*lo<=a.lo and hi*hi>a.hi
        return I(lo,hi)

checks=[]
def gt(name,a,b=0):
    v=(I(a)-b).lo
    assert v>0,(name,str(v))
    checks.append({'name':name,'strict_reserve':str(v)})
def lt(name,a,b):gt(name,b,a)
def trig(x):
    x=F(x)
    def t(n,o):return sum(((-1)**j*x**k/F(factorial(k)) for j,k in enumerate(range(o,n+1,2))),F(0))
    return I(t(11,1),t(13,1)),I(t(14,0),t(12,0))
Q=I('9789/2500');R=Q.sqrt();d=(Q/2).sqrt()-F(1,2)
a0=(Q-F(1,4)).sqrt()-F(1,2)
CF={
 'P':list(map(F,('.02478','0','.93015','.02363','-.11055'))),
 'J':list(map(F,('0','-.00026','.83194','-.11864','.17627'))),
}
def outer(b):
    b=I(b);u=(Q-(b+F(1,2))**2).sqrt();return u-F(1,2),u
def label(n,b):
    b=I(b);a,u=outer(b);c,p,q,r,s=CF[n]
    return c+p*a+q*b+r*b*b+s*a*b
def der(n,b):
    b=I(b);a,u=outer(b);v=b+F(1,2);rho=v/u;c,p,q,r,s=CF[n]
    D=-p*rho+q+2*r*b+s*(a-b*rho)
    DD=2*r-2*s*rho-(p+s*b)*Q/u**3
    DDD=-3*Q*(s*Q+(p-s/2)*v)/u**5
    return D,DD,DDD
def positive_contact(B,x):
    B=I(B);A,_=outer(B);s,c=trig(x)
    return F('.5')+(F('.5')-B)*c-(A-F('.5'))*s,(A-F('.5'))*c-(B-F('.5'))*s


# All coefficients are those of the declared exact role table.
CF.update({
 'L':list(map(F,('.03965','0','3.85510','-1.49748','-1.89442'))),
 'K':list(map(F,('0','-.02112','.29090','0','.44642'))),
})
s026,c026=trig('.026');s3,c3=trig('.3');s5,c5=trig('.5');s6,c6=trig('.6');s7,c7=trig('.7')
CF['R']=list(map(F,('0','-.01025','.16031','0','.63457')))
def atan_sum(x,n):
    x=F(x)
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
pi2=I(8*atan_sum('1/5',16)-2*atan_sum('1/239',5),
      8*atan_sum('1/5',15)-2*atan_sum('1/239',4))
gt('Machin lower pi/2',pi2,'1.57079632679489')
lt('Machin upper pi/2',pi2,'1.57079632679490')
ell=pi2-F('.7')
gt('outer radius slope lower',F('.5')/(a0+F('.5')),'.261')
for n in ['R','K']:
    p,q,r,t=CF[n][1:]
    lt(n+' global concavity',-2*t*F('.261')+abs(p)*Q/(d+F('.5'))**3,0)
    gt(n+' derivative at diagonal',der(n,d)[0],0)
    gt(n+' derivative at .2',der(n,'.2')[0],'.8')
constant=label('R',0)+label('K',0)
gt('late angle direct cost',F('.943')+constant,'.8986')
gt('large transverse sum direct cost',ell+constant+F('.16'),'.986')
norm=F('.4')**2+(F('.8')*a0-F('.4'))**2
lt('small-sum secondary scalar derivative norm',norm,1)
endpoint=ell+constant+F('.4')+F('.4')*s7-(F('.8')*a0-F('.4'))*c7
gt('small-sum secondary endpoint',endpoint,'.924')
s943,c943=trig('.943')
gt('small-sum primary radial bound',outer('.2')[0],'1.35')
gt('small-sum primary cosine bound',c943,'.587')
lt('small-sum primary projection bound',F('1.415')-F('1.35')*F('.587')+F('.2'),1)
gt('whole row strict target reserve',F('.8986'),'17953/20000')
result={'status':'PASS: whole edge-3 positive-negative outer quarter row',
        'Q':'9789/2500','target':'17953/20000',
        'comparison_count':len(checks),'checks':checks}
out=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('wrong_0011011_positive_negative_outer_quarter_hand_arithmetic.json').write_text(out)
print(out,end='')
