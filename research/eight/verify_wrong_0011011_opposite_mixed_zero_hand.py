"""Fixed exact arithmetic for the full opposite-sign mixed zero-quarter hand proof.
Every interval is declared in the manuscript; there is no search or adaptation.
"""
from fractions import Fraction as F
from math import factorial,isqrt,comb
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
        r=I(1)
        for _ in range(n):r=r*a
        return r
    def sqrt(a):
        assert a.lo>0;d=10**14
        lo=F(isqrt(a.lo.numerator*d*d//a.lo.denominator),d)
        hi=F(isqrt(a.hi.numerator*d*d//a.hi.denominator)+1,d)
        assert lo*lo<=a.lo and hi*hi>a.hi
        return I(lo,hi)
checks=[]
def gt(name,a,b=0):
    r=(I(a)-b).lo;assert r>0,(name,r)
    checks.append({'name':name,'strict_reserve':str(r)})
def lt(name,a,b):gt(name,b,a)
def trig(x):
    x=F(x)
    def T(n,o):return sum(((-1)**j*x**k/F(factorial(k)) for j,k in enumerate(range(o,n+1,2))),F(0))
    return I(T(11,1),T(13,1)),I(T(14,0),T(12,0))
Q=I('9789/2500');d=(Q/2).sqrt()-F(1,2);dc=F(1,2)+I(2).sqrt()/24
ac=F(7,12);a0=(Q-F(1,4)).sqrt()-F(1,2);gamma=F(17953,20000)
coef={'J':list(map(F,('0','-.00026','.83194','-.11864','.17627'))),
      'P':list(map(F,('.02478','0','.93015','.02363','-.11055'))),
      'L':list(map(F,('.03965','0','3.85510','-1.49748','-1.89442')))}
core={'J':(F('.00125'),F('1.03981')),'P':(F('.19555'),F('.63132')),'L':(F('.0497'),F('.94831'))}
def outer(b):b=I(b);u=(Q-(b+F(1,2))**2).sqrt();return u-F(1,2),u
def label(n,b):
    b=I(b);a,u=outer(b);c,p,q,r,s=coef[n]
    return c+p*a+q*b+r*b*b+s*a*b
def D(n,b):
    b=I(b);a,u=outer(b);v=b+F(1,2);rr=v/u;c,p,q,r,s=coef[n]
    return -p*rr+q+2*r*b+s*(a-b*rr)
def D2(n,b):
    b=I(b);a,u=outer(b);v=b+F(1,2);c,p,q,r,s=coef[n]
    return 2*r-2*s*v/u-(p+s*b)*Q/u**3
def D3(n,b):
    b=I(b);a,u=outer(b);v=b+F(1,2);c,p,q,r,s=coef[n]
    return -3*Q*(s*Q+(p-s/2)*v)/u**5
def aligned(n,b):
    c,g=core[n];return c+g*(1-I(b))+label(n,b)
def diag(x):
    ss,cc=trig(x);b=F('.5')+(F('.5')-dc)*cc+(dc+F('.5'))*ss
    w=(dc-F('.5'))*ss+(dc+F('.5'))*cc
    wp=(dc-F('.5'))*cc-(dc+F('.5'))*ss
    return b,w,wp
def Hdiag(n,x):
    c,g=core[n];b,w,wp=diag(x)
    return -F(x)+c+g*dc+label(n,b),-1+D(n,b)*w,D2(n,b)*w*w+D(n,b)*wp

# Geometry and primary cases.
s7,c7=trig('.7');s32,c32=trig('.32');smax,cmax=trig('.44152');s45,c45=trig('.45');s55,c55=trig('.55')
lt('outer axial upper',a0,'1.415');gt('outer diagonal lower',d,'.899');lt('outer diagonal upper',d,'.9')
gt('core diagonal lower',dc,'.5589');lt('core diagonal upper',dc,'.559')
lt('negative primary excludes',F('1.415')-F('.5589')*F('.764'),1)
gt('cos .7 lower',c7,'.764')
lt('primary phi>.45',a0-F('.5')-(dc+F('.5'))*c45+(dc-F('.5'))*s45,0)
lt('side primary phi>.55',a0-F('.5')-F(13,12)*c55,0)
gt('primary B>.34 at0',F(13,12),a0-F('.5'))
gt('primary B>.34 at.7',F(13,12)*c7+F('.16')*s7,a0-F('.5'))
for n,(c,g) in core.items():
    gt(n+' low-angle primary',F('.45')+c+g/2+label(n,0),'.904')
    gt(n+' high-angle primary',F('.55')+c+F('.34')*g+label(n,0),'.904')
lt('source f negative gap x<.32',dc-F('.5')+(d-F('.5'))*c32-(d+F('.5'))*s32,0)
lt('target f negative gap x<.44152',d-F('.5')+(dc-F('.5'))*cmax-(dc+F('.5'))*smax,0)
gt('cos squared for negative target cases',cmax*cmax,'.81')
gt('outer derivative P lower',D('P',0),'.773')
gt('outer derivative L positive floor',F('.6248')-F('.0311')**2/4,'.6245')
lt('J derivative curvature at all b upper',2*coef['J'][3]-2*coef['J'][4]*(F('.5')/(a0+F('.5')))+abs(coef['J'][1])*Q/(d+F('.5'))**3,0)
gt('J derivative positive',D('J',d))
gt('J third derivative negative numerator',coef['J'][4]*Q+(coef['J'][1]-coef['J'][4]/2)*(d+F('.5')))
gt('L strong third lower',3*F('1.8')*F('3.9')/8,2)
gt('L D(.5)',D('L','.5'),'.6248');gt('L D2(.5) lower',D2('L','.5'),'-.0311');lt('L D2(.5) upper',D2('L','.5'),0)
gt('L D2(.6) lower',D2('L','.6'),'.5')

# Global aligned scalar bounds.
for b in (0,d):gt('J aligned endpoint '+str(b.lo if isinstance(b,I) else b),aligned('J',b),'.9005')
gt('J aligned .15 endpoint',aligned('J','.15'),'.9005')
gt('L D(0) above g',D('L',0),core['L'][1]);lt('L D(.6) below g',D('L','.6'),core['L'][1])
gt('L aligned 0',aligned('L',0),'1.03');gt('L aligned .6',aligned('L','.6'),'.94')
gt('L aligned reference',aligned('L','.8216'),'.9010079')
lt('L aligned reference derivative upper',D('L','.8216')-core['L'][1],'.0001')
gt('L aligned reference derivative lower',D('L','.8216')-core['L'][1],'-.0001')
gt('L aligned strong convex remainder',F('.9010079')-F('.0001')**2,'.901')
for b,val in [('.84','.9014'),('.86','.9028')]:gt('L aligned '+b,aligned('L',b),val)
gt('L aligned increasing after .84',D('L','.84'),core['L'][1])
gt('P global aligned derivative',F('.773'),core['P'][1])
gt('P restricted aligned at.435',aligned('P','.435'),'.926')

# Source f, positive phi.
c,g=core['J'];gt('J derivative on [0,.15] above1',D('J','.15'),1)
gt('J small B linear phi coefficient',1,g*(a0-F('.5')))
gt('J small B scalar floor',c+label('J',0)+g-F('.15')*(g-1)-g*F('.7')**2/4,'.907')
a15,_=outer('.15');gt('J large B angle derivative',1,g*g*(Q-2*(a15+F('.15'))))
c,g=core['L'];gt('L all B positive angle derivative',1,g*g*(Q-2*a0))
c,g=core['P'];G=c+coef['P'][0]+F('.773')+(g-F('.773'))*dc
gt('P source scalar baseline',G,'.914')
gt('P positive phi coefficient',1,F('.773')*F('1.09'))
gt('P positive support loss coefficient',F('1.09'),a0-F('.5')+F('.7')/4)
gt('P negative support gain',F('1.399')*(1-F('.32')**2/6)-F('.32')/4,'1.295')
gt('P negative phi coefficient',F('.773')*F('1.295'),1)
for n in ('J','L'):
    c,g=core[n];gt(n+' source negative angle derivative',g*(F('1.399')*c32-s32/2),1)

# Target f, positive phi.
for n in ('J','P','L'):
    c,g=core[n];gt(n+' positive target angle reserve',1,g*F(31,120))
c,g=core['P'];gt('P target phi>=.06',F('.85165')+F('.06')*(1-g*F(31,120)),'.901')
gt('P target small phi outer lower',1-dc-F('.06')/12-F('.06')**2/4,'.435')

# J negative target: side and corner endpoint reductions.
s41,c41=trig('.41')
gt('J side derivative margin',core['J'][1],D('J',1-dc))
gt('J side angle quadratic discriminant',core['J'][1]*F(13,12)-1-core['J'][1]**2*(d-F('.5'))**2/4)
gt('J corner first-feasible low-x',-F('.41')+core['J'][0]+label('J',d)+core['J'][1]/2,'.9056')
blo=F('.5')+(F('.5')+(dc+F('.5'))*s41-d)/c41
gt('J corner first-feasible b for x>=.41',blo,'.5249')
gt('J corner first-feasible high-x',-F('.44152')+core['J'][0]+label('J',d)+core['J'][1]*F('.5249'),'.8999')
lt('J diagonal F second upper',D2('J',1-dc),'-.485')
lt('J diagonal F derivative upper',D('J',1-dc),'.905')
gt('diagonal speed square lower',diag('.44152')[1]**2,'.96')
lt('diagonal acceleration upper',dc-F('.5'),'.059')
lt('J diagonal cost concave',-F('.485')*F('.96')+F('.905')*F('.059'),0)
gt('J diagonal initial cost',Hdiag('J',0)[0],'1.02')
gt('J diagonal final cost bound',-F('.44152')+core['J'][0]+core['J'][1]*dc+label('J',d),'.9353')

# P negative target: core coordinate strictly increases cost in the reverse direction.
gt('P negative target decreasing in core b',D('P',1-dc)*cmax,core['P'][1])
gt('P derivative at first diagonal point',D('P',1-dc),'.84')
gt('P third derivative monotonic numerator',2*Q,2*F('1.4')**2)
for x,bupper in [('.1','.548'),('.3','.757'),('.44152','.9')]:lt('diagonal b upper '+x,diag(x)[0],bupper)
lt('P D3 at .548',D3('P','.548'),'.331')
lt('P D2 at .548',D2('P','.548'),'.236')
lt('P D3 at .757',D3('P','.757'),'.513')
lt('P D3 at .9',D3('P','.9'),'.782')
lt('diagonal speed square upper', (dc-F('.5'))**2+(dc+F('.5'))**2,'1.126')
lt('diagonal acceleration at .1',diag('.1')[2],0)
lt('diagonal speed square at .3',diag('.3')[1]**2,'1.06')
lt('diagonal acceleration at .3',diag('.3')[2],'-.256')
gt('P D2 at diagonal .3',D2('P',diag('.3')[0]),'.32')
gt('P D at diagonal .3',D('P',diag('.3')[0]),'.92')
lt('P Hthird first range',F('.331')*F('1.126')+3*F('.236')*F('.059')-F('.84'),0)
lt('P Hthird middle range',F('.513')*F('1.126')-F('.84'),0)
lt('P Hthird last range',F('.782')*F('1.06')-3*F('.32')*F('.256')-F('.92'),0)
gt('P Hsecond at .44152',Hdiag('P','.44152')[2],'.0079')
lt('P Hprime at .44152',Hdiag('P','.44152')[1],'-.044')
gt('P diagonal endpoint cost',Hdiag('P','.44152')[0],'.89779')

# L negative target, side: three fixed target-coordinate bands.
c,g=core['L']
gt('L side positive angle derivative B<=.84',g*F(13,12)-1-g*g*F('.34')**2/4)
gt('L side derivative middle numerator lower',g*F(13,12)-1-g*g*F('.36')**2/4,'-.00181')
gt('L side derivative last numerator lower',g*F(13,12)-1-g*g*F('.4')**2/4,'-.00864')
gt('L side middle cost',F('.9014')-F('.442')*F('.00181')/F('.81'),'.9004')
gt('L side last cost',F('.9028')-F('.442')*F('.00864')/F('.81'),'.89808')

# L negative target corner: one explicit degree-10 polynomial.
def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return p
def add(*p):
    r=[F(0)]*max(map(len,p))
    for q in p:
        for j,x in enumerate(q):r[j]+=x
    return trim(r)
def scale(p,x):return trim([a*x for a in p])
def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for j,a in enumerate(p):
        for k,b in enumerate(q):r[j+k]+=a*b
    return trim(r)
def bernstein(p,l,h,n):
    return [sum((p[j]*comb(j,t)*l**(j-t)*(h-l)**t*F(comb(k,t),comb(n,t))
                 for t in range(min(k+1,len(p))) for j in range(t,len(p))),F(0))
            for k in range(n+1)]
b=[F(0),F(1)];v=add(b,[F(1,2)]);q=F(9789,2500);u2=add([q],scale(mul(v,v),-1));x=add(b,[F(-1,2)])
k=F('1.89442');zeta=F(144,13);h=F('2.99496');j=F('4.80231')
Ap=add(scale(mul(x,[j,-h]),zeta),[h])
Bp=scale(add(scale(mul(mul(x,add(mul([F(1,2),F(2)],v),[-q])),u2),zeta),scale(mul(v,u2),-2),scale(b,-q)),k)
PP=add(mul(mul(Ap,Ap),mul(mul(u2,u2),u2)),scale(mul(Bp,Bp),-1))
assert len(PP)==11
ba=bernstein(Ap,F('.5'),F('.9'),2)
gt('L corner polynomial A left',ba[0]);gt('L corner polynomial A right',ba[-1])
assert Ap[2]<0
floors=[4,16,34,51,70,96,133,180,233,284,326]
bern=bernstein(PP,F('.5'),F('.9'),10)
for i,(a,lo) in enumerate(zip(bern,floors)):gt('L corner polynomial Bernstein '+str(i),a,lo)

# Corner endpoint B=d: a simple increasing lower function after .377.
s377,c377=trig('.377')
lt('corner first feasible x>.377',F('.5')+F(13,12)*s377,d)
gt('corner first feasible lower derivative numerator',s377*s377-g*(d-F('.5'))*s377+g*(dc+F('.5'))-1)
gt('corner first feasible derivative numerator increasing',2*s377,g*(d-F('.5')))
flow=-F('.377')+c+label('L',d)+g/2+g*(F('.5')-d)/c377+g*(dc+F('.5'))*s377/c377
gt('L corner first feasible lower cost',flow,'.9008')

# The remaining L/core diagonal: arbitrary centers reduced to one strongly convex scalar.
lt('L D left for x<=.3',D('L',diag(0)[0]),'.82')
lt('L D right for x<=.3',D('L',diag('.3')[0]),'.82')
lt('diagonal speed maximum',((dc-F('.5'))**2+(dc+F('.5'))**2).sqrt(),'1.061')
lt('L Hprime below .3',F('.82')*F('1.061'),1)
gt('L H at .3',Hdiag('L','.3')[0],'.9046')
gt('L D2 on upper diagonal',D2('L',diag('.3')[0]),'1.69')
lt('L D on upper diagonal',D('L',diag('.44152')[0]),'1.165')
gt('diagonal acceleration lower',diag('.44152')[2],'-.4')
gt('L Hsecond uniform bound',F('1.69')*F('.96')-F('1.165')*F('.4'),'1.1')
hr,hpr,_=Hdiag('L','.3832')
gt('L H reference value',hr,'.8977797');gt('L Hprime reference lower',hpr,'-.00008');lt('L Hprime reference upper',hpr,'.00008')
gt('L H square completion',F('.8977797')-F('.00008')**2/F('2.2'),'.89777')

for lo in ('.904','.9005','.901','.907','.914','.901','.926','.9056','.8999','1.02','.9353','.89779','.9004','.89808','.9008','.9046','.89777'):
    gt('terminal bound '+lo+' exceeds gamma',F(lo),gamma)
result={'status':'PASS','strict_comparisons':len(checks),
 'scope':'All24 opposite-sign mixed core/outer zero-quarter branches of0011011, with the stated structural signs and four retained SAT axes.',
 'corner_polynomial':{'degree':10,'interval':['1/2','9/10'],'bernstein_strict_integer_floors':floors,'power_coefficients':[str(z) for z in PP]},'checks':checks}
Path(__file__).with_name('wrong_0011011_opposite_mixed_zero_hand_arithmetic.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','strict_comparisons':len(checks)}))
