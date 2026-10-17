"""Fixed rational arithmetic for all same-sign OO zero pairs.

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
gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.9')
gt('axial lower',a0,'1.4145');lt('axial upper',a0,'1.415')
gt('physical negative angle bound',F('.026'),F(355,452)-F('.76'))
lt('negative primary SAT upper',a0-d*c026+d*s026,1)
lt('positive source primary SAT upper',a0-d*c7,1)
lt('target primary angle barrier',a0-F('.5')-(d+F('.5'))*c6+(d-F('.5'))*s6,0)
lt('target primary source .8 barrier',a0-F('.5')-(outer('.8')[0]+F('.5'))*c7+F('.3')*s7,0)
lt('target primary target .3 barrier',outer('.3')[0]-F('.5')-(d+F('.5'))*c7+(d-F('.5'))*s7,0)
s3024,c3024=trig('.3024')
lt('target secondary angle barrier',(d-F('.5'))*(s3024+c3024)-F('.5'),0)
lt('target secondary target coordinate',(d-F('.5'))*(s7+c7)-F('.5'),'.063')
lt('target secondary early source .8 barrier',(outer('.8')[0]-F('.5'))*s5+F('.3')*c5-F('.5'),0)
lt('target secondary late source .624 barrier',(outer('.624')[0]-F('.5'))*s7+F('.124')*c7-F('.5'),0)
for f,g in [('P','J'),('L','K')]:
    gt(f+' target primary direct cost',F('.6')+label(f,'.8')-label(g,'.3'),'.98')
    gt(f+' target secondary early direct cost',F('.3024')+label(f,'.8')-label(g,'.063'),'.93')
    gt(f+' target secondary late direct cost',F('.5')+label(f,'.624')-label(g,'.063'),'.96')

# Scalar label facts.
gt('P derivative lower',der('P',0)[0],'.773')
lt('P derivative upper',der('P',d)[0],'.973')
gt('P second derivative positive',der('P',0)[1])
gt('P third derivative positive numerator',Q,F('.5')*(d+F('.5')))
gt('P fourth derivative positive coarse numerator',2*F('3.9')-2*F('1.4')**2)
lt('J second derivative upper',der('J',0)[1],'-.329')
gt('J third derivative positive brace',CF['J'][4]*Q+(CF['J'][1]-CF['J'][4]/2)*F('1.4'))
gt('J derivative positive at diagonal',der('J',d)[0])
lt('J derivative upper',der('J',0)[0],'1.082')
for n in ['J','K']:
    # A uniform upper bound for F'' at every b, using p<0, s>0.
    p,q,rr,ss=CF[n][1:]
    upper=2*rr-2*ss*F('.5')/(a0+F('.5'))+abs(p)*Q/(d+F('.5'))**3
    lt(n+' globally strictly concave',upper,0)
    gt(n+' globally increasing',der(n,d)[0])
gt('L third derivative lower',3*F('1.8')*F('3.9')/8,2)
gt('L derivative at .5 lower',der('L','.5')[0],'.6248')
gt('L second derivative at .5 lower',der('L','.5')[1],'-.0311')
lt('L second derivative at .5 upper',der('L','.5')[1],0)
gt('L global derivative lower',F('.6248')-F('.0311')**2/4,'.6245')
lt('L derivative at zero upper',der('L',0)[0],'1.176')
lt('L derivative at diagonal upper',der('L',d)[0],'1.176')
gt('L derivative at diagonal lower',der('L',d)[0],'1.16')
lt('K derivative at zero upper',der('K',0)[0],'.928')
lt('K derivative at .2 upper',der('K','.2')[0],'.869')

# Source-secondary contact b=.5+(B+.5)c-(A-.5)s.
def contact(B,x):
    B=I(B);A,U=outer(B);s,c=trig(x)
    b=F('.5')+(B+F('.5'))*c-(A-F('.5'))*s
    v=(A-F('.5'))*c+(B+F('.5'))*s
    k=c+(B+F('.5'))/U*s
    return b,v,k
lt('source-secondary lower angle .107',d+a0*trig('.107')[0]-(1+sum(trig('.107')))/2,0)
gt('source-secondary contact b lower',contact(0,'.7')[0],'.293')
lt('source-secondary B=d impossible at .7',d-contact(d,'.7')[0],0)
lt('source-secondary universal v bound',R-c7,'1.215')
gt('outer U at target .2 lower',outer('.2')[1],'1.85')
lt('outer universal U upper',a0+F('.5'),'1.915')
gt('outer universal U lower',d+F('.5'),'1.399')

# L/K: a two-direction implication forces target B=0.
lt('L derivative at .293 upper',der('L','.293')[0],'.817')
lt('L derivative at .755 upper',der('L','.755')[0],'.817')
gt('L low source positive angle derivative',1-F('.817')*F('1.215'))
qsmall=Q+1-2*F('1.85')
small=(Q-F('1.915'))/(F('1.85')*qsmall)+F('.5')*F('.255')/(F('1.915')*qsmall*qsmall.sqrt())
gt('L target-small k/v lower',small,'.928')
m=F('.84')
gt('universal first k/v term quadratic',Q-(1+m*(Q+1))**2/(8*m))
large=m+F('.7')*F('.255')/(F('1.915')*F('2.118')*F('1.456'))
gt('L target-large k/v lower',large,'.869')
lt('universal q upper',Q+1-2*F('1.399'),'2.118')
lt('universal v upper from q',(Q+1-2*F('1.399')).sqrt(),'1.456')
gt('L source-diagonal angle derivative negative square',F('1.16')**2*(Q-2*a0-F('.16')),1)
gt('L high-source second derivative lower',der('L','.755')[1],'1.67')
gt('L axial boundary high-source curvature',F('1.67')*(Q-2*a0-F('.16'))-F('1.176')*F('.4'),1)
gt('L axial low-source angle derivative',1-F('.817')*(Q-2*a0).sqrt())
bref,vref,_=contact(0,'.15781')
gt('L axial reference source above cut',bref,'.755');lt('L axial reference below diagonal',bref,d)
href=F('.15781')+label('L',bref)-label('K',0)
hp=1-der('L',bref)[0]*vref
gt('L axial reference value',href,'.8977797')
lt('L axial reference derivative upper',hp,'.000003')
gt('L axial reference derivative lower',hp,'-.000003')
gt('L axial square-completion lower',F('.8977797')-F('.000003')**2/2,'.89777')

# P/J: exact stationary-curve Hessian exclusion.
pp6=der('P','.6')[0]
v6=(Q-(F('.1')-s7)**2).sqrt()-c7
lt('P no critical source below .6',pp6*v6,1)
def E(b):
    b=I(b);p,p2,p3=der('P',b);return p2-(b-F('.5'))*p**3
lt('P third derivative first interval upper',der('P','.7')[2],'.45')
gt('P derivative at .6 lower',pp6,'.876')
gt('P stationary curvature first interval decreases',F('.876')**3,F('.45'))
lt('P third derivative second interval upper',der('P',d)[2],'.779')
gt('P derivative at .7 lower',der('P','.7')[0],'.903')
gt('P second derivative at .7 lower',der('P','.7')[1],'.293')
gt('P stationary curvature second interval decreases',F('.903')**3+3*F('.2')*F('.903')**2*F('.293'),'.779')
gt('P stationary curvature positive at diagonal',E(d),'.043')
lt('P stationary curvature at .6 upper',E('.6'),'.187')
lt('P stationary curvature at .75 upper',E('.75'),'.124')
def critical_B(b):
    b=I(b);p=der('P',b)[0];z=b-F('.5');q=z*z+1/p**2
    U=(Q+1-q)/2
    return (Q-U**2).sqrt()-F('.5')
gt('stationary target lower',critical_B(d),'.2')
lt('stationary target upper',critical_B('.6'),'.32')
gt('stationary first-half target lower',critical_B('.75'),'.242')
gt('stationary target radial slope lower',F('.7')/outer('.2')[1],'.378')
gt('stationary first-half radial slope lower',F('.742')/outer('.242')[1],'.404')
gt('stationary target U lower',outer('.32')[1],'1.8')
lt('stationary target U upper',outer('.2')[1],'1.852')
ulo=F('1.8');uhi=F('1.852');qlo=Q+1-2*uhi;qhi=Q+1-2*ulo
fp_lower=(4*Q*ulo-2*ulo*ulo-Q*(Q+1))/(ulo*qhi)**2
gt('stationary f1-prime positive numerator',4*Q*ulo-2*ulo*ulo-Q*(Q+1))
bracket=Q/ulo**3-3*F('.378')**2/qhi
gt('stationary mixed derivative bracket upper positive',bracket)
phiBB=-F('.378')*fp_lower+F('.4')*bracket/(qlo*(qlo-F('.16')).sqrt())
lt('stationary phi_BB upper',phiBB,'-.05')
gt('stationary J second derivative lower',der('J','.32')[1],'-.436')
gt('stationary determinant first interval negative', (F('.404')*F('.876')**3)**2-F('.187')*F('.386'))
gt('P derivative at .75 lower',der('P','.75')[0],'.918')
gt('stationary determinant second interval negative',(F('.378')*F('.918')**3)**2-F('.124')*F('.386'))

# P/J target-zero boundary.
gt('P axial early angle derivative',1-F('.973')*(F('.915')*c3+F('.5')*s3))
lt('P axial later source coordinate',contact(0,'.3')[0],'.708')
lt('P axial later derivative',der('P','.708')[0],'.907')
gt('P axial later angle derivative',1-F('.907')*F('1.043'))
lt('P axial speed norm',(Q-2*a0).sqrt(),'1.043')
s10726,c10726=trig('.10726')
lt('P axial starting angle lower',(a0-F('.5'))*s10726-c10726/2+d-F('.5'),0)
gt('P axial starting cost',F('.10726')+label('P',d)-label('J',0),'.8985')

# P/J source-diagonal boundary. Six fixed angle intervals.
z0=d-F('.5')
def diagonal_curve(l,h=None):
    if h is None:
        s,c=trig(l)
    else:
        sl,cl=trig(l);sh,ch=trig(h)
        s=I(sl.lo,sh.hi);c=I(ch.lo,cl.hi)
    Z=z0-s;Y=(Q-Z**2).sqrt()
    U=Y*c-Z*s;V=Y*s+Z*c
    f=1-c/Y
    fp=(s*(Q-1-z0*z0)+z0*(1+s*s))/Y**3
    return V-F('.5'),U*f,-V*f*f+U*fp
rows=[]
for l,h,bpl,bppu in [
    ('.107','.2','.915','.151'),('.2','.3','.914','.190'),
    ('.3','.4','.919','.217'),('.4','.5','.924','.238'),
    ('.5','.6','.924','.251'),('.6','.7','.924','.248')]:
    B,bp,bpp=diagonal_curve(l,h)
    gt('diagonal B-prime '+l+':'+h,bp,bpl)
    lt('diagonal B-second '+l+':'+h,bpp,bppu)
    gt('diagonal cost curvature '+l+':'+h,F('.329')*F(bpl)**2-F('1.082')*F(bppu),'.009')
    rows.append({'left':l,'right':h,'B_prime_lower':bpl,'B_second_upper':bppu})
gt('diagonal first branch endpoint before .7',diagonal_curve('.7')[0])
lt('diagonal final target in outer arc',diagonal_curve('.7')[0],d)
B,bp,bpp=diagonal_curve('.18909')
gt('diagonal reference target positive',B);lt('diagonal reference target below d',B,d)
value=F('.18909')+label('P',d)-label('J',B)
dvalue=1-der('J',B)[0]*bp
gt('diagonal reference value',value,'.89777605')
lt('diagonal reference derivative upper',dvalue,'.000001')
gt('diagonal reference derivative lower',dvalue,'-.000001')
gt('diagonal completed-square lower',F('.89777605')-F('.000001')**2/F('.018'),'.89777604')

# P/J upper-angle boundary: globally strongly convex in B.
B=I('.34621');b,v,k=contact(B,'.7')
gt('upper-angle reference source positive',b);lt('upper-angle reference below d',b,d)
val=F('.7')+label('P',b)-label('J',B)
D=der('P',b)[0]*k-der('J',B)[0]
gt('upper-angle reference value',val,'.89778868')
lt('upper-angle reference derivative upper',D,'.00001')
gt('upper-angle reference derivative lower',D,'-.00001')
gt('upper-angle completed-square lower',F('.89778868')-F('.00001')**2/F('.658'),'.89778867')
gt('strict final target',F('.89777'),F(17953,20000))
out={'status':'PASS','strict_comparisons':len(checks),'Q':'9789/2500','gamma':'17953/20000',
     'proved_lower':'0.89777','diagonal_curvature_rows':rows,'checks':checks}
dest=Path(__file__).with_name('wrong_0011011_same_outer_zero_hand_arithmetic.json')
dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'strict_comparisons':len(checks),'output':str(dest)}))

