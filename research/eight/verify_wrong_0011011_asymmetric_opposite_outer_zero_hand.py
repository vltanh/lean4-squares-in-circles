"""Fixed rational arithmetic for the asymmetric opposite-sign OO zero pair.

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

gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.900')
gt('axial lower',a0,'1.4145');lt('axial upper',a0,'1.415')
lt('radius upper',R,2)
gt('P third derivative numerator',Q,F('.5')*(d+F('.5')))
gt('P derivative lower',der('P',0)[0],'.773')
lt('P derivative upper',der('P',d)[0],'.973')
gt('P second derivative positive at zero',der('P',0)[1])
gt('J third derivative numerator',CF['J'][4]*Q+(CF['J'][1]-CF['J'][4]/2)*F('1.4'))
lt('J second derivative upper',der('J',0)[1],'-.329')
gt('J derivative lower',der('J',d)[0],'.618')
lt('J derivative upper',der('J',0)[0],'1.082')
lt('aligned derivative at right',der('P',d)[0]-der('J',1-d)[0],0)
gt('aligned left endpoint',label('P',1-d)+label('J',d),'.89778')
gt('aligned right endpoint',label('P',d)+label('J',1-d),'.89778')

s3,c3=trig('.3');s5,c5=trig('.5');s7,c7=trig('.7')
lt('primary negative angle bound',a0-d*c7-1,0)
lt('primary positive angle .5 barrier',a0-F('.5')-(d+F('.5'))*c5+(d-F('.5'))*s5,0)
lt('primary target .6 barrier',a0-outer('.6')[0]*c7+F('.6')*s7-1,0)
gt('primary P-J cost',F('.5')+label('P',0)+label('J','.6'),'.99')
gt('primary J-P cost',F('.5')+label('J',0)+label('P','.6'),'.99')
lt('no simultaneous zero secondary contact',a0*s7,1)
gt('positive contact speed lower',(d-F('.5'))*(c7-s7))
gt('outer radial slope lower',F('.5')/(a0+F('.5')),'.261')
lt('universal positive contact speed',(Q-2*a0).sqrt(),'1.043')
gt('P small-angle speed envelope increases',F('.5')*c3-F('.915')*s3)
gt('P small-angle cost derivative',1-F('.973')*(F('.915')*c3+F('.5')*s3))
lt('P large-angle contact coordinate',positive_contact(0,'.3')[0],'.708')
lt('P derivative at .708',der('P','.708')[0],'.907')
gt('P large-angle cost derivative',1-F('.907')*F('1.043'))

lt('J target .2 speed',(Q-2*(outer('.2')[0]+F('.2'))).sqrt(),'.903')
gt('J first half target-large cost derivative',1-F('1.082')*F('.903'))
gt('J first half target-small coordinate',positive_contact('.2','.5')[0],'.35')
lt('J derivative at .35',der('J','.35')[0],'.947')
gt('J first half target-small cost derivative',1-F('.947')*F('1.043'))
lt('J latter half source coordinate upper',positive_contact(0,'.5')[0],'.501')
gt('J derivative latter half lower',der('J','.501')[0],'.874')
gt('J latter half second derivative lower',der('J','.501')[1],'-.514')
lt('latter-half c-rs upper',c5-F('.261')*s5,'.753')
gt('latter-half rc+s lower',F('.261')*c7+s5,'.679')
gt('J speed product decreases with target',F('.874')*F('.679')-F('.514')*F('1.043')*F('.753'))
b7,k7=positive_contact(0,'.7')
gt('J zero-target last contact lower',b7,'.293')
lt('J zero-target last derivative upper',der('J',b7)[0],'.972')
gt('J zero-target last speed lower',k7,'1.02')
gt('J zero-target speed product increases in angle',F('.329')*F('1.02')**2-F('.972')*F('.207'))
lt('J zero-target final speed product',der('J',b7)[0]*k7,'.993')

def axial_root_test(x):
    s,c=trig(x);return (a0-F('.5'))*s-c/2+d-F('.5')
lt('positive source-diagonal zero-target angle lower',axial_root_test('.10726'),0)
gt('positive source-diagonal zero-target angle upper',axial_root_test('.108'),0)
gt('positive source-diagonal endpoint P-J',F('.10726')+label('P',d)+label('J',0),'.89779')
gt('positive source-diagonal endpoint J-P',F('.10726')+label('J',d)+label('P',0),'.926')
lt('positive boundary target coordinate upper',1-d,'.101')
lt('P boundary second derivative',der('P','.101')[1],'.125')
s108,c108=trig('.108')
gt('positive boundary speed positive',1-1/(Q-F('.601')**2).sqrt())
lt('positive boundary f upper',1-(c108-s108)/R,'.56')
gt('positive boundary f-prime numerator',Q-2-F('.16')+3*F('.399'),8*F('.36'))
gt('positive boundary U lower',outer('.101')[1],'1.8')
gt('P positive boundary strict concavity',F('.773')*F('1.8')*F('.36')-F('.125')*F('1.12')**2)

gt('negative P contact cost derivative square',F('.773')**2*(Q-F('1.8')-F('.16')),1)
lt('negative J contact curvature',-F('.329')*(Q-F('1.8')-F('.16'))+F('1.082')*F('.4'),0)
s56,c56=trig('.56')
lt('negative diagonal endpoint before .56',(d-F('.5'))*(1+c56)-(d+F('.5'))*s56,0)
gt('negative boundary Z positive',c56-F('.4'))
gt('negative boundary speed positive',1-s56/(Q-F('.601')**2).sqrt())
lt('negative boundary f-prime numerator coefficient',1-Q+F('.16'),0)
lt('negative boundary inverse secant slope',F('.56')/(2*F('.899')-1),'.702')
gt('negative boundary P derivative beats secant',F('.773'),'.702')
gt('claimed bound exceeds target',F('.89778'),F(17953,20000))
out={'status':'PASS','strict_comparisons':len(checks),'Q':'9789/2500','gamma':'17953/20000','proved_lower':'0.89778','checks':checks}
dest=Path(__file__).with_name('wrong_0011011_asymmetric_opposite_outer_zero_hand_arithmetic.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'strict_comparisons':len(checks),'output':str(dest)}))

