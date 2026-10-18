"""Independent rational audit of the final two mixed edge-3 theorems.

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

from math import comb
from hashlib import sha256
import re,subprocess
BASE=Path(__file__).resolve().parents[1]
SRC=BASE/'m5_agent/hand_conversion'
bindings={}
replays={}
for stem in ['wrong_0011011_edge3_negative_core_to_positive_outer','wrong_0011011_edge3_outer_to_negative_core']:
    note=SRC/(stem.upper()+'_HAND_PROOF.md')
    checker=SRC/('verify_'+stem+'.js')
    report=SRC/(stem+'_arithmetic.json')
    raw=subprocess.run(['node',str(checker)],capture_output=True,check=True).stdout
    assert raw==report.read_bytes(),stem
    data=json.loads(raw);assert data['status']=='PASS'
    replays[stem]=data.get('comparison_count',data.get('comparisons'))
    for p in [note,checker,report]:bindings[str(p.relative_to(BASE))]=sha256(p.read_bytes()).hexdigest()

def padd(a,b):
    a=list(a)+[F(0)]*max(0,len(b)-len(a));b=list(b)+[F(0)]*max(0,len(a)-len(b))
    return [x+y for x,y in zip(a,b)]
def pscale(a,c):return [v*F(c) for v in a]
def pmul(a,b):
    z=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return z
def ppow(a,k):
    p=[F(1)]
    for _ in range(k):p=pmul(p,a)
    return p
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def bernstein_by_elimination(p,L,H):
    p=trim(list(p));n=len(p)-1;L=F(L);h=F(H)-L
    power=[F(0)]*(n+1)
    for i,c in enumerate(p):
        for k in range(i+1):power[k]+=c*comb(i,k)*L**(i-k)*h**k
    b=[]
    for k in range(n+1):
        b.append(power[k]/comb(n,k)-sum((b[j]*comb(k,j)*(-1)**(k-j) for j in range(k)),F(0)))
    # Independently reconstruct each power coefficient from the solved basis.
    for k in range(n+1):
        assert sum((b[j]*comb(n,j)*comb(n-j,k-j)*(-1)**(k-j) for j in range(k+1)),F(0))==power[k]
    return b
poly_rows=[]
def polycheck(name,p,L,H,printed,den=1):
    b=bernstein_by_elimination(p,L,H)
    assert len(b)==len(printed)
    for j,(actual,floor) in enumerate(zip(b,printed)):
        gt(name+' printed coefficient '+str(j),actual,F(floor)/den)
    poly_rows.append({'name':name,'interval':[str(L),str(H)],'degree':len(b)-1,'bernstein':[str(x) for x in b],
                      'displayed_lower':[str(F(x)/den) for x in printed]})

qq=F('9789/2500');u=[F(0),F(1)];u2=ppow(u,2)
tp=[qq+1,F(-2)];w=padd([qq],pscale(u2,-1))
E0=padd(padd(pscale(u2,2),pscale(u,-4*qq)),[qq*(qq+1)])
E0p=[-4*qq,F(4)]
A0=padd(pmul(pmul(E0,u2),tp),
        pscale(pmul(w,padd(pmul(pmul(E0p,u),tp),pscale(pmul(E0,padd(pscale(tp,3),pscale(u,-4))),-1))),-1))
D0=padd(pmul(ppow(u,5),ppow(tp,3)),pscale(A0,-1))
polycheck('Cminus D0',D0,'1.68','1.915',
 [2787804586,3011298926,3194343971,3343335303,3465605636,3569452117,3664113405,3759672496,3866853865],10**8)
for h,L,H,printed in [
    (F('.98439'),'1.68','1.915',[489607785,323313124,225100758,168621192,129208651,82908158,5312839]),
    (F('.975'),'1.68','1.74',[435018120,395594851,360296092,328700368,300392840,274964286,252010027])]:
    z=padd(pscale(tp,h*h),[F(-1)]);t2=ppow(tp,2);z2=ppow(z,2)
    ch=pscale(pmul(pmul(u,t2),z),3*h*h*qq)
    ch=padd(ch,pscale(pmul(pmul(w,u2),t2),-h**4))
    ch=padd(ch,pscale(pmul(pmul(pmul(w,u2),tp),z),-4*h*h))
    ch=padd(ch,pscale(pmul(t2,z2),3*qq))
    ch=padd(ch,pscale(pmul(pmul(u,tp),z2),-6*qq))
    ch=padd(ch,pscale(pmul(pmul(w,u2),z2),8))
    polycheck('Cminus Ch '+str(h),ch,L,H,printed,10**8)
def trigpoly(n,odd):
    a=[F(0)]*(n+1)
    for j,k in enumerate(range(odd,n+1,2)):a[k]=F((-1)**j,factorial(k))
    return a
g=F('.98439');vv=F('.05334');e=F('.22042')-F('.34492')*F('7/12');gamma=F('.89765')
pilo=F('3.141592653589793238')
K=pilo/2-e-F('.108')+(g+F('.73'))/2-gamma
Ap=padd(padd(pmul(trigpoly(10,0),[K,F(1)]),[g]),pscale(trigpoly(9,1),-g/12))
Pf=padd(ppow(Ap,2),pscale(padd([g*g],pscale(ppow(trigpoly(8,0),2),F('.73')**2)),-qq))
tail=sum((-c*F('.7')**j for j,c in enumerate(Pf) if j>=9 and c<0),F(0))
P8=Pf[:9];P8[0]-=tail
polycheck('Cminus upper primary',P8,'.3','.7',
 [99491629,115049933,128428668,139219167,147047210,151595871,152627541,150000491,143672521],10**8)

# Transcription: every printed coefficient in the four-row table is bound.
cm_note=(SRC/'WRONG_0011011_EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md').read_text()
printed_rows=re.findall(r'\| .*? \| \\?\(\[.*?\]\\?\) \| [68] \| ([0-9, ]+) \|',cm_note)
assert len(printed_rows)==4,printed_rows
assert sum(len(re.findall(r'\d+',r)) for r in printed_rows)==32
for printed,row in zip(printed_rows,poly_rows):
    actual=[F(x)/10**8 for x in re.findall(r'\d+',printed)]
    assert actual==list(map(F,row['displayed_lower']))

def trig_interval(x,odd):
    x=I(x);lo=I(0);hi=I(0)
    for j in range(17):
        k=2*j+odd;term=((-1)**j)*x**k/F(factorial(k))
        hi=hi+term
        if j==15:lo=hi
    return I(lo.lo,hi.hi)
def sinI(x):return trig_interval(x,1)
def cosI(x):return trig_interval(x,0)
def atan_endpoint(x,upper):
    x=F(x)
    if x<0:return -atan_endpoint(-x,not upper)
    assert x<=F('.75')
    return atan_sum(x,41 if upper else 40)
def atanI(x):
    x=I(x);return I(atan_endpoint(x.lo,False),atan_endpoint(x.hi,True))
def Edata(B,h):
    h=F(h);B=I(B);A,U=outer(B);V=B+F('.5');P=U-1;t=Q+1-2*U
    S=(h*h*t-1).sqrt();r=V/U
    beta=pi2/2+atanI((V-P)/(V+P))
    val=beta+atanI(S)-S-e-(g-h)**2/(4*vv)+h/2-label('L',B)
    N=Q-U-V*S;D=U*t;Np=r-S-h*h*V*r/S;Dp=r*(2*U-t)
    return val,N/D-der('L',B)[0],(Np*D-N*Dp)/D**2-der('L',B)[1]
for B,h,LB in [('.3035',g,'.89776733'),('.32',g,'.8978'),('.4',g,'.8985'),('.45',g,'.8985'),('.45','.975','.89807'),('.54','.975','.89807')]:
    gt('Cminus angular envelope value '+str(B)+':'+str(h),Edata(B,h)[0],LB)
gt('Cminus envelope reference slope lower',Edata('.3035',g)[1],'-.000006')
lt('Cminus envelope reference slope upper',Edata('.3035',g)[1],'.000006')
gt('Cminus envelope curvature at .32',Edata('.32',g)[2],'.22')
gt('Cminus envelope derivative at .32',Edata('.32',g)[1])
gt('Cminus envelope derivative at .4',Edata('.4',g)[1])
lt('Cminus envelope curvature at .4',Edata('.4',g)[2],0)
lt('Cminus second envelope curvature at .45',Edata('.45','.975')[2],0)
gt('Cminus strong-convexity reserve',F('.89776733')-F('.000006')**2/F('.44'),gamma)
gt('Cminus imported zero-curve reserve',F('.9025')-(e-F('.01449')),gamma)

# Ominus -> Cminus: rebuild the degree-eight side polynomial independently.
cg=F('.62312');c0=F('.16823');slope=F('.633');intercept=F('.1109')
K=pilo/2+c0-intercept+(cg+slope)/2-gamma
AP=padd(padd(pmul(trigpoly(10,0),[K,F(-1)]),[cg]),pscale(trigpoly(11,1),13*cg/12))
PP=padd(ppow(AP,2),pscale(padd([cg*cg],pscale(ppow(trigpoly(8,0),2),slope*slope)),-qq))
tail2=sum((-c*F('.7')**j for j,c in enumerate(PP) if j>=9 and c<0),F(0))
lt('Ominus polynomial negative omitted tail',tail2,'.000299')
PP8=PP[:9];PP8[0]-=F('.000299')
polycheck('Ominus whole side support',PP8,'.161','.7',
 ['.6117715','.5130297','.4132075','.3172047','.2292187','.1523344','.0883327','.0378233','.0006068'])
oc_note=(SRC/'WRONG_0011011_EDGE3_OUTER_TO_NEGATIVE_CORE_HAND_PROOF.md').read_text()
boxed=oc_note.split(r'\boxed{',1)[1].split('}',1)[0]
assert list(map(F,re.findall(r'\.\d+',boxed)))==list(map(F,poly_rows[-1]['displayed_lower']))

ell=pi2-F('.7');dc=F('.5')+I(2).sqrt()/24;ac=F('7/12')
v=F('.91744');k=F('.95769');V0=F('3.819505');m0=F('1.6636925')+v*Q
def M(u):
    u=I(u);z=(Q-u*u).sqrt()
    return m0-v*u*u-k*u/2-(V0-k*u)*z
def MD(u):
    u=I(u);z=(Q-u*u).sqrt()
    return -2*v*u-k/2+k*z+(V0-k*u)*u/z
def MDD(u):
    u=I(u);z=(Q-u*u).sqrt()
    return -2*v-2*k*u/z+Q*(V0-k*u)/z**3
gt('Ominus M third derivative sign',V0*F('1.4')-k*Q)
gt('Ominus M derivative at1.4',MD('1.4'),'.773')
gt('Ominus M second at1.4',MDD('1.4'),'-.204')
gt('Ominus M second at1.5',MDD('1.5'))
lt('Ominus M second at1.7',MDD('1.7'),'3.212')
gt('Ominus M derivative global lower',F('.773')-F('.204')*F('.1'),'.75')
def contact(phi,A,B):return 1+(I(A)+F('.5'))*cosI(phi)-(I(B)-F('.5'))*sinI(phi)
def speed(phi,A,B):return (I(A)+F('.5'))*sinI(phi)+(I(B)-F('.5'))*cosI(phi)
gt('Ominus contact minimum height',contact('1.098',dc,dc),'1.4')
lt('Ominus contact maximum height',contact(ell,ac,F('.5')),'1.7')
gt('Ominus corner concavity scalar',12*F('.75')*F('.455')-F('3.212'))
for lo,hi in [(ell,F('.95')),(F('.95'),F('1.03')),(F('1.03'),F('1.098'))]:
    for name,A,B in [('join',ac,F('.5')),('diagonal',dc,dc)]:
        for endname,phi in [('left',lo),('right',hi)]:
            lt('Ominus endpoint speed '+name+':'+str(hi)+':'+endname,MD(contact(phi,A,B))*speed(hi,A,B),'.920')
for name,A,B,LB in [('join',ac,F('.5'),'.9196'),('diagonal',dc,dc,'.897784')]:
    gt('Ominus final endpoint '+name,ell+M(contact(ell,A,B))+c0+cg*B,LB)
gt('Ominus late global bound',F('1.409')-F('.67949')+c0,gamma)
gt('Ominus late corner bound',F('1.098')-F('.67949')+c0+cg/2,gamma)

for name in ['WRONG_0011011_ALIGNED_MIXED_QUARTER_HAND_PROOF.md',
             'WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md']:
    p=SRC/name
    bindings[str(p.relative_to(BASE))]=sha256(p.read_bytes()).hexdigest()
output={'status':'PASS','scope':'Independent continuous review and selected exact arithmetic for both final edge3 mixed families',
 'author_replays':replays,'bindings':bindings,'independent_comparison_count':len(checks),
 'independent_checks':checks,'reconstructed_polynomial_rows':poly_rows}
Path(__file__).with_name('wrong_0011011_edge3_final_mixed_independent_audit.json').write_text(json.dumps(output,indent=2)+'\n')
print('PASS',len(checks),'independent strict comparisons; both complete author replays byte-identical')

