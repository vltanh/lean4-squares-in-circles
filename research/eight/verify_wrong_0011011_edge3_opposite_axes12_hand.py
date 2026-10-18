"""Fixed hand comparisons for 0011011 edge 3 (-,+), axes 1 and 2.

Every rectangle and test point is fixed in the companion manuscript.
There is no optimizer, adaptive cover, or discovery-data dependency.
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
def atan_sum(x,n):
    x=F(x)
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
def atan_small(x):
    x=I(x);assert 0<x.lo<=x.hi<F('.31')
    return I(atan_sum(x.lo,24),atan_sum(x.hi,25))
pi2=I(8*atan_sum('1/5',16)-2*atan_sum('1/239',5),
      8*atan_sum('1/5',15)-2*atan_sum('1/239',4))
Q=I('9789/2500');d=(Q/2).sqrt()-F('.5')
a0=(Q-F('.25')).sqrt()-F('.5')
b1=(Q-F('2.25')).sqrt()-F('.5')
CF={
 'T':list(map(F,('.01670','0','2.42322','-.91744','-.95769'))),
 'L':list(map(F,('.03965','0','3.85510','-1.49748','-1.89442'))),
}
def outer(b):
    b=I(b);u=(Q-(b+F('.5'))**2).sqrt();return u-F('.5'),u
def label(n,b):
    b=I(b);a,u=outer(b);c,p,q,r,s=CF[n]
    return c+p*a+q*b+r*b*b+s*a*b
def der(n,b):
    b=I(b);a,u=outer(b);v=b+F('.5');rho=v/u;c,p,q,r,s=CF[n]
    D=-p*rho+q+2*r*b+s*(a-b*rho)
    DD=2*r-2*s*rho-(p+s*b)*Q/u**3
    DDD=-3*Q*(s*Q+(p-s/2)*v)/u**5
    return D,DD,DDD
def geometry(b):
    b=I(b);a,u=outer(b);r=(b+F('.5'))/u
    return a,u,r,Q/u**3,3*Q*(b+F('.5'))/u**5

gt('pi/2 lower',pi2,'1.57079632679489')
lt('pi/2 upper',pi2,'1.57079632679490')
gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.9')
gt('axial lower',a0,'1.4145');lt('axial upper',a0,'1.415')
gt('unit-primary transverse lower',b1,'.7905');lt('unit-primary transverse upper',b1,'.791')
gt('T third derivative lower',der('T',0)[2],'1.6')
gt('T derivative positive reference',der('T','.6')[0],'.6101')
gt('T reference second derivative lower',der('T','.6')[1],'-.049')
lt('T reference second derivative upper',der('T','.6')[1],'.049')
gt('T derivative positive by square completion',F('.6101')-F('.049')**2/F('3.2'),'.609')
gt('L third derivative lower',der('L',0)[2],'3.17')
gt('common third derivative increasing numerator',2*Q-F('.5'))
gt('L derivative reference',der('L','.5')[0],'.62481')
gt('L reference second derivative lower',der('L','.5')[1],'-.032')
lt('L reference second derivative upper',der('L','.5')[1],'.032')
gt('L derivative lower by square completion',F('.62481')-F('.032')**2/F('6.34'),'.624')
lt('L derivative upper axial',der('L',0)[0],'1.176')
lt('L derivative upper diagonal',der('L',d)[0],'1.176')
lt('L curvature at .5',der('L','.5')[1],0)
lt('T derivative upper axial',der('T',0)[0],'1.069')
lt('T derivative upper diagonal',der('T',d)[0],'.774')
lt('T derivative at .1',der('T','.1')[0],'.944')
lt('T derivative at .4',der('T','.4')[0],'.774')
lt('T curvature before .415',der('T','.415')[1],0)
gt('f1 uniform quadratic reserve',Q-(1+F('.84')*(Q+1))**2/F('6.72'))

# Aligned contacts.  All upper limits .791 are harmless outward extensions;
# labels whose physical argument is nonnegative are clamped at zero below.
def h12(B):
    B=I(B);a,u,r,rp,rpp=geometry(B);b=a-1
    tp,tpp,tppp=der('T',b);lp,lpp,lppp=der('L',B)
    return pi2-label('T',b)-label('L',B),tp*r-lp,-tpp*r*r+tp*rp-lpp
aligned12_rows=[]
for lo,hi,UB in [('0','.2','-2.2'),('.2','.4','-1.9'),('.4','.6','-1'),('.6','.7','-1.2'),('.7','.791','-.4')]:
    aL,uL,rL,rpL,rppL=geometry(lo);aH,uH,rH,rpH,rppH=geometry(hi)
    bL=I(max(F(0),(aH-1).lo),max(F(0),(aH-1).hi));bH=aL-1
    bound=der('T',bH)[2]*rH**3-3*der('T',bL)[1]*rH*rpH+der('T',bL)[0]*rppH-der('L',lo)[2]
    lt('aligned12 third derivative '+lo+':'+hi,bound,UB)
    aligned12_rows.append({'interval':[lo,hi],'upper':UB,'exact_upper':str(bound.hi)})
gt('aligned12 second derivative at endpoint',h12(b1)[2],'.22')
h,hp,_=h12('.685356885')
gt('aligned12 reference cost',h,'.8980812')
gt('aligned12 reference derivative lower',hp,'-.000001');lt('aligned12 reference derivative upper',hp,'.000001')
gt('aligned12 square completion',F('.8980812')-F('.000001')**2/F('.44'),'.89808')

def h34(b):
    b=I(b);a,u,r,rp,rpp=geometry(b);B=a-1
    tp,tpp,tppp=der('T',b);lp,lpp,lppp=der('L',B)
    return pi2-label('T',b)-label('L',B),-tp+lp*r,-tpp-lpp*r*r+lp*rp
aligned34_rows=[]
for lo,hi,LB in [('0','.4','.97'),('.4','.6','.88'),('.6','.791','.79')]:
    a,u,r,rp,rpp=geometry(lo);B=a-1
    bound=-der('T',hi)[1]-der('L',B)[1]*r*r+der('L',B)[0]*rp
    gt('aligned34 second derivative '+lo+':'+hi,bound,LB)
    aligned34_rows.append({'interval':[lo,hi],'lower':LB,'exact_lower':str(bound.lo)})
h,hp,_=h34('.59709465')
gt('aligned34 reference cost',h,'.8977817')
gt('aligned34 reference derivative lower',hp,'-.000001');lt('aligned34 reference derivative upper',hp,'.000001')
gt('aligned34 square completion',F('.8977817')-F('.000001')**2/F('1.58'),'.89778')

# Inverse lower-contact angle. b is the small source coordinate and B the
# large target coordinate.  The exact Hessian formula is evaluated directly.
def inverse_geometry(b,B):
    b=I(b);B=I(B);A,u,r,rp,rpp=geometry(B);q=Q+1-2*u;z=b+F('.5');v=(q-z*z).sqrt()
    N=4*Q*u-2*u*u-Q*(Q+1)
    f1=(Q-u)/(u*q)
    fb=1/v;fB=f1-r*z/(q*v)
    fbb=z/v**3;fbB=-r/v**3
    fBB=-r*N/(u*u*q*q)-z/(q*v)*(rp-2*r*r/q-r*r/(v*v))
    return fb,fB,fbb,fbB,fBB,v
def inverse_point(b,B):
    b=I(b);B=I(B);A,u=outer(B);q=Q+1-2*u;z=b+F('.5');v=(q-z*z).sqrt()
    w=A-F('.5');y=B+F('.5')
    x=atan_small((w*v-y*z)/(w*z+y*v))
    return pi2-x-label('T',b)-label('L',B)
def inverse_row(lo,hi,zlo,zhi,physical=False):
    lo=F(lo);hi=F(hi);z=I(zlo,zhi)
    u=I(outer(hi)[1].lo,outer(lo)[1].hi);r=I(lo+F('.5'),hi+F('.5'))/u
    q=Q+1-2*u;rp=Q/u**3
    N=I((4*Q*u.lo-2*u.lo*u.lo-Q*(Q+1)).lo,(4*Q*u.hi-2*u.hi*u.hi-Q*(Q+1)).hi)
    if physical:v=I(lo+F('.5'),I(q.hi-F('.25')).sqrt().hi)
    else:v=(q-z*z).sqrt()
    fBB=-r*N/(u*u*q*q)-z/(q*v)*(rp-2*r*r/q-r*r/(v*v))
    return fBB,r/v**3
s571,c571=trig('.571')
lt('lower axis1 angle cap',(a0-F('.5'))*c571-F('.5')*s571,F('.5'))
gt('rectangle entirely in contact domain',Q-F('1.6')**2-F('.9')**2)
gt('source decreases into b<=.1',inverse_geometry('.1','.4')[0]-der('T','.1')[0])
vlo=(Q+1-2*outer('.4')[1]-F('.25')).sqrt()
gt('small rectangle Cbb',-der('T','.1')[1]+F('.5')/vlo**3,'1.5')
hessian_rows=[]
for lo,hi,LB,UB in [('0','.1','1.16','.515'),('.1','.2','.85','.545'),('.2','.3','.51','.561'),('.3','.35','.40','.526'),('.35','.4','.21','.526')]:
    fBB,cross=inverse_row(lo,hi,'.5','.6')
    cross=(F(hi)+F('.5'))/outer(hi)[1]/(Q+1-2*outer(lo)[1]-F('.36')).sqrt()**3
    lower=fBB-der('L',hi)[1]
    gt('small rectangle CBB '+lo+':'+hi,lower,LB)
    lt('small rectangle cross '+lo+':'+hi,cross,UB)
    gt('small rectangle shifted determinant '+lo+':'+hi,(F('1.5')-F('.01'))*(F(LB)-F('.01'))-F(UB)**2)
    hessian_rows.append({'interval':[lo,hi],'CBB_lower':LB,'cross_upper':UB,'exact_CBB_lower':str(lower.lo),'exact_cross_upper':str(cross.hi)})
refb='.05878084';refB='.33400286';fb,fB,*_=inverse_geometry(refb,refB)
gt('lower axis1 reference cost',inverse_point(refb,refB),'.8977764')
gt('lower axis1 reference gradient b lower',fb-der('T',refb)[0],'-.000001')
lt('lower axis1 reference gradient b upper',fb-der('T',refb)[0],'.000001')
gt('lower axis1 reference gradient B lower',fB-der('L',refB)[0],'-.000001')
lt('lower axis1 reference gradient B upper',fB-der('L',refB)[0],'.000001')
gt('lower axis1 square completion',F('.8977764')-2*F('.000001')**2/F('.02'),'.89777')
gt('middle source cutoff',inverse_geometry('.105','.5')[0]-der('T','.105')[0],'.0014')
lt('middle inverse curvature',inverse_row('.4','.5','.605','.605')[0],'-.073')
for lo,hi,LB in [('.4','.42','.0019'),('.42','.45','.0054'),('.45','.5','.0073')]:
    gt('middle target derivative '+lo+':'+hi,inverse_geometry('.105',hi)[1]-der('L',lo)[0],LB)
concavity_rows=[]
for lo,hi,UB in [('.5','.525','-.06'),('.525','.55','-.18'),('.55','.6','-.27'),('.6','.7','-.45'),('.7','.791','-1.1')]:
    # L'' increases, so the upper bound subtracts its left endpoint.
    bound=inverse_row(lo,hi,'.5',outer(lo)[1].hi-1,True)[0]-der('L',lo)[1]
    lt('large target concavity '+lo+':'+hi,bound,UB)
    concavity_rows.append({'interval':[lo,hi],'upper':UB,'exact_upper':str(bound.hi)})
lt('zero-source boundary enters interior',inverse_geometry(0,'.4')[0]-der('T',0)[0],0)

# Upper axis 1 and a reusable zero-exit curve.
q0=Q-2*a0
lt('upper axis1 contact source cap',q0.sqrt()-F('.5'),'.543')
gt('upper axis1 angular derivative',1-F('1.069')*F('.4'))
s31,c31=trig('.31');s7,c7=trig('.7')
for zname,z in [('b1',b1),('d',d)]:
    az,_=outer(z)
    for x,s,c in [('.31',s31,c31),('.7',s7,c7)]:
        gt('upper zero exit excluded corner '+zname+':'+x,(az-F('.5'))*c+(z-F('.5'))*s,F('.5'))
gt('upper zero exit angular speed',(b1-F('.5'))*c31-F('.5')*s31)
gt('upper zero exit numerator',F('.86')*c31-s31,F('.5'))
gt('upper zero exit slope dominates labels',F('.5')/F('.4'),'1.176')

# Lower axis 2.
lt('aligned target ratio upper',(b1+F('.5'))/F('1.5'),'.861')
gt('lower axis2 angular speed product',(F('.624')/F('.861'))**2*(Q-F('.915')**2),1)

# Upper axis 2: target diagonal and then three concavity rows.
z0=d-F('.5')
def upper_diag(b):
    b=I(b);a,u,r,rp,rpp=geometry(b);q=Q+1-2*u;v=(q-z0*z0).sqrt()
    N=4*Q*u-2*u*u-Q*(Q+1);f1=(Q-u)/(u*q)
    jp=f1+r*z0/(q*v)-der('T',b)[0]
    jpp=-r*N/(u*u*q*q)+z0/(q*v)*(rp-2*r*r/q-r*r/(v*v))-der('T',b)[1]
    return jp,jpp
def upper_diag_point(b):
    b=I(b);a,u=outer(b);q=Q+1-2*u;v=(q-z0*z0).sqrt();w=a-F('.5');y=b+F('.5')
    x=atan_small((y*v-w*z0)/(y*z0+w*v))
    return pi2+x-label('T',b)-label('L',d)
def upper_diag_second_row(lo,hi):
    lo=F(lo);hi=F(hi);u=I(outer(hi)[1].lo,outer(lo)[1].hi);r=I(lo+F('.5'),hi+F('.5'))/u
    q=Q+1-2*u;v=(q-z0*z0).sqrt();rp=Q/u**3
    N=I((4*Q*u.lo-2*u.lo*u.lo-Q*(Q+1)).lo,(4*Q*u.hi-2*u.hi*u.hi-Q*(Q+1)).hi)
    return -r*N/(u*u*q*q)+z0/(q*v)*(rp-2*r*r/q-r*r/(v*v))-der('T',hi)[1]
gt('upper diagonal first curvature row',upper_diag_second_row('0','.1'),1)
gt('upper diagonal reference cost',upper_diag_point('.00542853'),'.8977735')
gt('upper diagonal reference derivative lower',upper_diag('.00542853')[0],'-.000001')
lt('upper diagonal reference derivative upper',upper_diag('.00542853')[0],'.000001')
gt('upper diagonal square completion',F('.8977735')-F('.000001')**2/2,'.89777')
u4=outer('.4')[1];q4=Q+1-2*u4;r1=F('.6')/outer('.1')[1]
gt('upper diagonal middle derivative lower',(Q-u4)/(u4*q4)+r1*z0/(q4*q4.sqrt()),'.955')
gt('f1 increases in u on middle interval',4*Q*u4-2*u4*u4-Q*(Q+1))
gt('upper diagonal middle derivative reserve',F('.955')-F('.944'))
gt('upper diagonal late derivative reserve',F('.84')-F('.774'))
gt('inactive upper contact exits before source diagonal',F('.5')+(d+F('.5'))*c7-(d-F('.5'))*s7,d)
lt('small source upper contact angle cap',F('.5')+F('.6')*c7-(outer('.1')[0]-F('.5'))*s7,d)
gt('small source target transverse lower',(Q-F('1.6')**2).sqrt()-F('.5'),'.664')
gt('small source v lower',outer('.1')[0]-F('.5'),'.885')
upper_concavity_rows=[]
for lo,hi,UB in [('.664','.74','-.12'),('.74','.82','-.51'),('.82','.9','-1')]:
    U=I(outer(hi)[1].lo,outer(lo)[1].hi)
    rr=I(F(lo)+F('.5'),F(hi)+F('.5'))/U;zz=U-1
    qhi=Q+1-2*outer('.1')[1]
    v=I('.885',(qhi-zz.lo*zz.lo).sqrt().hi)
    bound=Q/(U**3*v)-zz*rr*rr/v**3-der('L',lo)[1]
    lt('upper axis2 target concavity '+lo+':'+hi,bound,UB)
    upper_concavity_rows.append({'interval':[lo,hi],'upper':UB,'exact_upper':str(bound.hi)})

output={'status':'PASS','scope':'0011011 edge3 (-,+), full-angle axes1/2 and aligned axes3/4',
 'Q':'9789/2500','target':'89777/100000','checks':checks,
 'aligned12_rows':aligned12_rows,'aligned34_rows':aligned34_rows,
 'hessian_rows':hessian_rows,'large_target_concavity_rows':concavity_rows,
 'upper_axis2_concavity_rows':upper_concavity_rows}
Path(__file__).with_name('wrong_0011011_edge3_opposite_axes12_hand_arithmetic.json').write_text(json.dumps(output,indent=2)+'\n')
print('PASS',len(checks),'fixed strict comparisons')
