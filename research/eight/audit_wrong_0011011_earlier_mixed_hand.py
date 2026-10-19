"""Independent fixed-arithmetic audit of six whole mixed families and their aligned/strip inputs.
No author implementation is imported; Node is used only for byte-bound fresh replays.
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

from math import comb
from hashlib import sha256
import subprocess,re

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

BASE=Path(__file__).resolve().parents[1]
SRC=BASE/'m5_agent/hand_conversion'
stems=[
 'wrong_0011011_edge2_negative_core_side',
 'wrong_0011011_edge2_negative_core_corner',
 'wrong_0011011_edge2_outer_to_positive_core',
 'wrong_0011011_edge2_core_to_positive_outer',
 'wrong_0011011_edge3_four_whole_mixed_families',
 'wrong_0011011_edge3_outer_to_positive_core',
 'wrong_0011011_aligned_mixed_quarter',
 'wrong_0011011_edge2_mixed_quarter_strip',
]
counts=[67,82,55,63,68,127,85,146]
bindings={};replays={};notes={}
from concurrent.futures import ThreadPoolExecutor
def replay(arg):
    stem,count=arg
    note=SRC/(stem.upper()+'_HAND_PROOF.md')
    checker=SRC/('verify_'+stem+'.js')
    report=SRC/(stem+'_arithmetic.json')
    out=subprocess.run(['node',str(checker)],check=True,capture_output=True).stdout
    assert out==report.read_bytes(),stem
    j=json.loads(out)
    assert j['status']=='PASS' and j['comparisons']==count,(stem,j.get('comparisons'))
    return stem,count,[(str(p.relative_to(BASE)),sha256(p.read_bytes()).hexdigest())
                       for p in (note,checker,report)],note.read_text()
with ThreadPoolExecutor(max_workers=4) as pool:
    for stem,count,files,note in pool.map(replay,zip(stems,counts)):
        replays[stem]=count;bindings.update(files);notes[stem]=note

def sinI(x):
    x=I(x);assert 0<=x.lo<=x.hi<=3
    ans=I(0)
    for j in range(17):
        ans=ans+((-1)**j)*x**(2*j+1)/F(factorial(2*j+1))
        if j==15:lo=ans.lo
    return I(lo,ans.hi)
def cosI(x):
    x=I(x);assert 0<=x.lo<=x.hi<=3
    ans=I(0)
    for j in range(17):
        ans=ans+((-1)**j)*x**(2*j)/F(factorial(2*j))
        if j==15:lo=ans.lo
    return I(lo,ans.hi)
pilo=F('3.141592653589793238');pihi=F('3.141592653589793239')
gt('independent Machin lower',16*atan_sum('1/5',26)-4*atan_sum('1/239',7),pilo)
lt('independent Machin upper',16*atan_sum('1/5',25)-4*atan_sum('1/239',8),pihi)
PI=I(pilo,pihi);hp=PI/2;ell=hp-F('.7')
qq=F('9789/2500');Q=I(qq);gamma=F('17953/20000');ac=F('7/12')
d=(Q/2).sqrt()-F('.5');dc=F('.5')+I(2).sqrt()/24
a0=(Q-F('.25')).sqrt()-F('.5');b0=(Q-F('2.25')).sqrt()-F('.5')
CF={
 'L':list(map(F,('.02478','0','.93015','.02363','-.11055'))),
 'T':list(map(F,('.01670','0','2.42322','-.91744','-.95769'))),
 'V':list(map(F,('0','-.01025','.16031','0','.63457'))),
 'N':list(map(F,('0','-.02112','.29090','0','.44642'))),
 'J':list(map(F,('.03965','0','3.85510','-1.49748','-1.89442'))),
}
def outer(b):
    b=I(b);u=(Q-(b+F('.5'))**2).sqrt()
    return u-F('.5'),u
def label(name,b):
    b=I(b);a,u=outer(b);c,p,q,r,s=CF[name]
    return c+p*a+q*b+r*b*b+s*a*b
def derivatives(name,b):
    b=I(b);a,u=outer(b);v=b+F('.5');rho=v/u;c,p,q,r,s=CF[name]
    D=-p*rho+q+2*r*b+s*(a-b*rho)
    DD=2*r-2*s*rho-(p+s*b)*Q/u**3
    DDD=-3*Q*(s*Q+(p-s/2)*v)/u**5
    return D,DD,DDD
def geo(b):
    b=I(b);a,u=outer(b);r=(b+F('.5'))/u
    return a,u,r,Q/u**3,3*Q*(b+F('.5'))/u**5

# Bind every independent role coefficient used by these eight manuscripts.
lp=BASE/'proof_integration/wrong_0011011_labels.json'
labels=json.loads(lp.read_text())
assert labels['Q']=='9789/2500' and labels['gamma']=='17953/20000'
assert labels['features']==['1','a','b','b^2','a*b'] and labels['denominator']==100000
assert labels['independent_roles']['0']['O+']==[int(x*100000) for x in CF['L']]
for role,name,sign in [(3,'T','-'),(3,'V','+'),(4,'N','-'),(4,'J','+')]:
    assert labels['independent_roles'][str(role)]['O'+sign]==[int(x*100000) for x in CF[name]]
for role,sign,expected in [
 (0,'+',[125,0,103981,0,0]),(3,'+',[ -1449,0,104240,0,0]),
 (3,'-',[22042,-34492,98439,-5334,0]),(4,'+',[4970,0,94831,0,0]),
 (4,'-',[16823,0,62312,0,0])]:
    assert labels['independent_roles'][str(role)]['C'+sign]==expected
bindings[str(lp.relative_to(BASE))]=sha256(lp.read_bytes()).hexdigest()

def trigpoly(n,odd):
    p=[F(0)]*(n+1)
    for j,k in enumerate(range(odd,n+1,2)):p[k]=F((-1)**j,factorial(k))
    return p
def displayed(stem,floors):
    # Ignore math delimiters and whitespace, while retaining every digit/sign.
    compact=re.sub(r'\\|[\s()]','',notes[stem])
    target=','.join(floors)
    assert target in compact,(stem,target)
def checked_poly(name,p,L,H,floors,stem):
    displayed(stem,floors)
    polycheck(name,p,L,H,floors)

# Corner contact curvature: reconstruct all three algebraic polynomials.
y=[F(0),F(1)];ym=[F(-1),F(1)]
q2=padd([qq],pscale(ppow(y,2),-1))
j=padd([F('1.12479')],pscale(ppow(ym,2),-1))
k=F('.11055');v=F('.961795');z=F('.02363')
E=pmul([v,-k],padd(pscale(j,qq),pscale(pmul(pmul(y,ym),q2),-1)))
E=padd(E,pscale(pmul(pmul(y,j),q2),-2*k))
E=padd(E,pscale(pmul(ym,ppow(q2,2)),-k))
B0=padd(pscale(j,2*z),pscale(pmul(ym,[-k/2,2*z]),-1))
A0=padd([F('.4')],pscale(B0,-1))
P=padd(ppow(E,2),pscale(pmul(ppow(A0,2),ppow(q2,3)),-1))
stem=stems[1]
for name,p,floors in [
 ('corner E',E,['1.6639','1.3858','1.1359','.9266','.7658','.6529']),
 ('corner A0',A0,['.3544','.3645','.3875']),
 ('corner P',P,['1.5254','1.2197','.9677','.7662','.6102','.4933','.4088','.3495','.3091','.2822','.2642'])]:
    checked_poly(name,p,'1.33','1.7',floors,stem)

# Side discriminant: one entire-interval polynomial, independently expanded.
cm=F('.22042')-F('.34492')*ac
ps=F('.973417553');ks=F('.39');g=F('.98439');zz=F('.05334')
s=trigpoly(10,0);c=trigpoly(9,1)
D=padd(padd([F('-.4')],pscale(c,F('13/12'))),pscale(s,F('.5')))
vv=[pilo/2-F('.790136935')+cm-gamma,F(-1)]
E21=pmul(ppow(s,2),padd(pscale(vv,4*ks),[-ps*ps]))
E21=padd(E21,pscale(s,2*g*ps))
E21=padd(E21,pscale(pmul(D,s),4*g*ks))
E21=padd(E21,pscale(padd(padd(vv,pscale(D,ps)),pscale(ppow(D,2),ks)),-4*zz))
E21=padd(E21,[-g*g])
tail=sum((-t*F('.7')**i for i,t in enumerate(E21) if i>9 and t<0),F(0))
lt('side discriminant negative tail',tail,'1e-7')
E9=E21[:10];E9[0]-=F('2e-7')
checked_poly('side whole discriminant',E9,0,'.7',
 ['.0001770','.0059290','.0067752','.0049065','.0024489','.0010489','.0014710','.0033222','.0050111','.0038894'],stems[0])
lt('side sine degree9 error',F('.7')**11/F(factorial(11)),'5e-10')
lt('side cosine degree10 error',F('.7')**12/F(factorial(12)),'3e-11')
lt('side discriminant derivative in cosine',2*F('1.001')*(4*ks+ps*ps)+2*g*ps+4*g*ks*(1+F('1.001')/2)+2*zz*(ps+2*ks),10)
lt('side discriminant derivative in sine',F('13/12')*(4*g*ks*F('1.001')+4*zz*(ps+2*ks)),3)
lt('side combined trigonometric error',10*F('3e-11')+3*F('5e-10'),'1e-7')

# Six complete squared support polynomials, with their original roundings.
def normpoly(name,gg,q,constant,slope_sign,L,H,allow,floors,stem):
    gg=F(gg);q=F(q);constant=F(constant);allow=F(allow)
    K=pilo/2+constant+(gg+q)/2-gamma
    AP=padd(pmul(trigpoly(10,0),[K,F(slope_sign)]),[gg])
    AP=padd(AP,pscale(trigpoly(11 if slope_sign<0 else 9,1),
                     13*gg/12 if slope_sign<0 else -gg/12))
    PP=padd(ppow(AP,2),pscale(padd([gg*gg],pscale(ppow(trigpoly(8,0),2),q*q)),-qq))
    tail=sum((-t*F(H)**i for i,t in enumerate(PP) if i>8 and t<0),F(0))
    lt(name+' discarded negative tail',tail,allow)
    gt(name+' positive angle coefficient',K-F(H))
    P8=PP[:9];P8[0]-=allow
    checked_poly(name,P8,L,H,floors,stem)
normpoly('edge2 Ominus Cplus lower','1.0424','.8281','-.01029',-1,0,'.7','.00031',
 ['.03216','.09189','.12506','.14048','.14758','.15443','.16617','.18482','.21039'],stems[2])
normpoly('edge2 Ominus Cplus upper','1.0424','.853','-.01029',1,'.02','.7','.000011',
 ['.03108','.44049','.83611','1.19488','1.49153','1.70162','1.80557','1.79252','1.66077'],stems[2])
normpoly('edge2 Cminus Oplus lower','1.03981','.670579666',-F('.00125')-F('.118433769'),-1,0,'.7','.000274',
 ['.000397','.05458','.07950','.08343','.07559','.06439','.05602','.05418','.06095'],stems[3])
normpoly('edge2 Cminus Oplus upper','1.03981','.670579666',-F('.00125')-F('.118433769'),1,0,'.7','.00001',
 ['.000661','.39201','.76842','1.10743','1.38425','1.57465','1.65928','1.62777','1.47923'],stems[3])
normpoly('edge3 Ominus Cplus lower','.94831','.62',-F('.0497')-F('.1109'),-1,0,'.171','1e-9',
 ['.0136520','.0162755','.0174316','.0172488','.0158580','.0133907','.0099778','.0057480','.0008271'],stems[5])
normpoly('edge3 Ominus Cplus upper','.94831','.633',-F('.0497')-F('.1109'),1,'.02','.7','1e-5',
 ['.0617974','.4122007','.7506755','1.0578577','1.3123765','1.4933330','1.5837907','1.5742478','1.4631437'],stems[5])

# Continued negative-L height and its first two derivatives.
def height(y):
    y=I(y);t=(Q-y*y).sqrt()
    M=F('.369499372')+F('.02363')*y*y-F('.055275')*y-(v-k*y)*t
    Mp=F('.04726')*y-F('.055275')+k*t+(v-k*y)*y/t
    Mpp=F('.04726')-2*k*y/t+Q*(v-k*y)/t**3
    return M,Mp,Mpp
gt('continued height third numerator positive at1',v-k*qq)
gt('continued height derivative at1',height(1)[1],'.67')
gt('continued height curvature at1',height(1)[2],'.58')
gt('side quadratic tangent lower endpoint',height(1)[0]-height('1.4')[0]+F('.4')*height('1.4')[1]-F('.39')*F('.4')**2,'.0014')
gt('side rounded tangent constant',height('1.4')[0],'-.790136934')
gt('side rounded tangent slope lower',height('1.4')[1],ps-F('4e-10'))
lt('side rounded tangent slope upper',height('1.4')[1],ps+F('4e-10'))
def U(phi,diag):
    aa=dc+F('.5') if diag else I('13/12')
    bb=dc-F('.5') if diag else I(0)
    return 1+aa*cosI(phi)-bb*sinI(phi)
def Cneg(A,B):
    return F('.22042')-F('.34492')*A+F('.98439')*B-F('.05334')*B*B
def HH(phi,diag):
    AA=dc+F('.5') if diag else I('13/12')
    BB=dc-F('.5') if diag else I(0)
    a=dc if diag else I(ac);b=dc if diag else I('.5')
    u=U(phi,diag);up=-AA*sinI(phi)-BB*cosI(phi)
    return I(phi)+height(u)[0]+Cneg(a,b),1+height(u)[1]*up
gt('corner continued height lower',U('1.191',True),'1.33')
lt('corner continued height upper',U(ell,False),'1.7')
early=[(ell,'.95','2.57','.339'),('.95','1.03','1.90','.209'),
       ('1.03','1.07','1.47','.150'),('1.07','1.085','1.32','.129'),
       ('1.085','1.1','1.27','.109')]
for j,(l,h,m,dd) in enumerate(early):
    lt('corner fixed curvature row '+str(j),height(U(l,False))[2],m)
    gt('corner fixed normal coefficient row '+str(j),height(U(h,True))[1]*cosI(h)-F('.34492'),dd)
    gt('corner fixed concavity reserve '+str(j),12*F(dd)-F(m))
for l,h,m,dd in [('1.1','1.13','1.213','.0697'),('1.13','1.191','1.127','-.0054')]:
    lt('corner later curvature '+l,height(U(l,False))[2],m)
    gt('corner later coefficient '+l,height(U(h,True))[1]*cosI(h)-F('.34492'),dd)
for diag,phi,value,slope in [(True,'1.049','.8977757','.000123'),(False,'1.16','.900224','.00029')]:
    val,der=HH(phi,diag)
    gt('corner reference value '+phi,val,value)
    gt('corner reference slope lower '+phi,der,-F(slope))
    lt('corner reference slope upper '+phi,der,slope)
    gt('corner completed quadratic '+phi,F(value)-F(slope)**2/F('.8'),'.89777' if diag else '.9002')
gt('corner increasing diagonal value1.1',HH('1.1',True)[0],'.89849')
gt('corner increasing diagonal derivative1.1',HH('1.1',True)[1])
gt('corner increasing diagonal value1.13',HH('1.13',True)[0],'.89958')
gt('corner middle interpolation',F('.89849')-F('.059')**2/8,gamma)
gt('corner later interpolation',F('.89958')-3*F('.059')**2/8,gamma)

# Independently bind all eight rounded concave supports for edge3 Ominus Cplus.
tangents=[
 (ell,'.95','.186','.849072101','.036194154'),
 ('.95','1','.208','.827123134','.040516466'),
 ('1','1.05','.226','.809833767','.044267347'),
 ('1.05','1.1','.245','.792248783','.048407521'),
 ('1.1','1.16','.268','.771892909','.053626828'),
 ('1.16','1.23','.297','.747715180','.060452973'),
 ('1.23','1.31','.335','.718627475','.069635209'),
 ('1.31','1.4','.384','.685655525','.081467247')]
def secondary(phi,g,q,constant):
    g=F(g);q=F(q);N=(g*g+q*q-2*g*q*cosI(phi)).sqrt()
    return I(phi)+F(constant)+(g+q)/2+g*sinI(phi)-Q.sqrt()*N
g3=F('.94831')
gt('edge3 uniform secondary concavity',g3*sinI(ell)-Q.sqrt()*I(g3*g3+F('.85')**2).sqrt()/4)
for i,(l,h,b,q,kq) in enumerate(tangents):
    q=F(q);kq=F(kq);td=derivatives('T',b)[0]
    lt('edge3 tangent slope '+str(i),td,q)
    lt('edge3 tangent intercept '+str(i),label('T',b)-F(b)*td,kq)
    for ph in (l,h):
        gt('edge3 scalar endpoint '+str(i)+':'+str(ph),secondary(ph,g3,q,-F('.0497')-kq),'.89790')
    # Compare the whole printed table row, allowing math markup only.
    fields=[str(b),str(q),str(kq)]
    raw=next(s for s in notes[stems[5]].splitlines() if ('| '+str(b)+' |') in s)
    assert [F(x) for x in re.findall(r'(?<![A-Za-z])\.\d+',raw)[-3:]]==[F(x) for x in fields]
gt('edge3 upper bound derivative at .6',derivatives('T','.6')[0],'.610')
lt('edge3 concavity through .6',derivatives('T','.6')[1],'-.048')
bs=F('.53362');val=label('T',bs)-F('.62')*bs;der=derivatives('T',bs)[0]-F('.62')
lt('edge3 small-arc upper completion',val+der**2/F('.096'),'.110895')
for b in ['.6','.7']:
    lt('edge3 small-line boundary '+b,label('T',b)-F('.62')*F(b),'.1109')
lt('edge3 global-line diagonal',label('T',d)-F('.633')*d,'.1109')

def bz(phi):
    m=F('.5')*sinI(phi)+F('13/12')*cosI(phi)
    return (Q-(1+m)**2).sqrt()-F('.5')
def zero_data(phi):
    b=bz(phi);a,u,r,rp,rpp=geo(b)
    vv=F('13/12')*sinI(phi)-F('.5')*cosI(phi)
    cost=I(phi)-F('.0497')-label('T',b)
    slope=1-derivatives('T',b)[0]*vv/r
    return b,cost,slope
gt('edge3 early axial barrier',F('.5')+F('.5')*sinI('1.12')+F('13/12')*cosI('1.12')-a0)
lt('edge3 early zero coordinate endpoint',bz('1.4'),'.551')
lt('edge3 early contact derivative endpoint',g3*geo(bz('1.4'))[2]/sinI('1.4')-derivatives('T',bz('1.4'))[0],'-.013')
gt('edge3 early contact derivative increases',F('.557')*F('.757')/F('.65')-F('.65')*F('.436')/F('.9')**2)
kap=a0-F('.5')
Nm=Q*kap*(2*kap+1)-kap*(kap+1)**3-F('205/144')*Q
lt('edge3 zero-curve curvature numerator',Nm,'-1.8')
gt('edge3 zero-curve acceleration magnitude',F('1.8')/F('1.051')**3,'1.55')
val=zero_data('1.383036')
gt('edge3 zero-curve reference',val[1],'.89777657')
gt('edge3 zero-curve reference slope lower',val[2],'-1e-6')
lt('edge3 zero-curve reference slope upper',val[2],'1e-6')
gt('edge3 zero-curve completion',val[1]-val[2]**2/F('1.88'),'.89777656')
gt('edge3 zero-target strip escape',hp-F('.0497')-label('T','.81'),'.906')

# Key common scalar and alignment interfaces, reconstructed from the labels.
for name in ('V','N'):
    gt('edge3 chord '+name,(label(name,d)-label(name,0))/d,'.704')
gt('edge3 core corner affine bound',F('.05334')/4-F('.34492')*F('.025'))
for e,g,L0 in [(cm,F('.98439'),-F('.02112')*a0),
               (F('.04970'),F('.94831'),-F('.01025')*a0)]:
    q=F('.704');kap=a0-F('.5');s=sinI(ell);c=cosI(ell);W=(1+s+c)/2
    f1=ell-e+L0+g*W-g*a0*s
    f2=ell-e+L0+g/2+g*(c-kap)/s
    c0=-e+L0+q/2-g*dc
    f3=ell+c0-q*s/12+q*(dc+F('.5'))*c
    LL=q*(d+F('.5'));f4=LL*hp+(1-LL)*ell+c0-q/(12*s)
    for n,a,b in [('axis1',f1,'.922'),('axis2',f2,'.945'),('axis3',f3,'1.058'),('axis4',f4,'1.23')]:
        gt('four-family lower '+n+':'+str(g),a,b)
    for x in ('0','.7'):
        ss=sinI(x);cc=cosI(x)
        u2=hp+F(x)-e+L0+g/2-g*kap/cc-g*ss/(12*cc)
        u4=hp+F(x)+c0-q/(12*cc)-q*kap*ss/cc
        gt('four-family upper axis2 '+str(g)+':'+x,u2,'1.11')
        gt('four-family upper axis4 '+str(g)+':'+x,u4,'1.26')

def alignedG(b):
    b=I(b);a,u,r,rp,rpp=geo(b);v=1-a;L1,L2,L3=derivatives('L',b)
    G=hp-label('L',b)+cm+F('.98439')*v-F('.05334')*v*v
    GD=-L1+(F('.98439')-F('.10668')*v)*r
    return G,GD
gg,gd=alignedG('.898')
gt('aligned negative core G reference',gg,'.89778')
gt('aligned negative core G derivative lower',gd,'-.0001')
lt('aligned negative core G derivative upper',gd,'.0001')
gt('aligned negative core G completion',gg-gd**2/F('1.2'),'.89777')
def H2(b):
    b=I(b);A,U,r,rp,rpp=geo(b)
    val=hp+F('1.03856')-F('1.02956')*A-F('.16031')*b-F('.63457')*A*b
    der=r*(F('1.02956')+F('.63457')*b)-(F('.16031')+F('.63457')*A)
    return val,der
hh,hd=H2('.5725')
gt('aligned positive outer H2 reference',hh,'.89778')
gt('aligned positive outer H2 derivative lower',hd,'-.0001')
lt('aligned positive outer H2 derivative upper',hd,'.0001')
gt('aligned positive outer H2 completion',hh-hd*hd,'.89777')
def H3(b):
    b=I(b);A,U,r,rp,rpp=geo(b);j,j2,j3=derivatives('J',b)
    C=hp-cm-F('.98439')*(A-1)+F('.05334')*(A-1)**2-label('J',b)
    D=r*(F('.98439')-F('.10668')*(A-1))-j
    DD=rp*(F('.98439')-F('.10668')*(A-1))+F('.10668')*r*r-j2
    return C,D,DD
hh,hd,hdd=H3('.604')
gt('aligned H3 reference',hh,'.897788')
gt('aligned H3 derivative lower',hd,'-.000013')
lt('aligned H3 derivative upper',hd,'.000013')
gt('aligned H3 completion',hh-hd*hd/F('.4'),'.89777')
gt('aligned H3 curvature at .63',H3('.63')[2],'.2')
gt('aligned H3 slope at .63',H3('.63')[1])
gt('aligned H3 final endpoint',H3(b0)[0],'.8978')
gt('aligned positive core negative source exact boundary',hp-F('.01029')-F('.81960')*b0-F('.02363')*b0*b0,'.89777')
gt('strip positive core small-source reserve',F('.942')-F('.02'),gamma)
gt('strip positive outer small-target reserve',H2('.462')[0]-F('.02')*F('.481'),gamma)
gt('strip zero-source exit',pilo/2-F('.02')-F('.00125')-F('.64805'),gamma)
gt('strip negative-side contact derivative',F('.97')*F('1.25')*F('.9998')-1)
gt('strip positive-side contact derivative',F('1.0424')*F('.99')*F('.9998')-1)
gt('strip zero-core lower derivative',F('.773')*F('1.25')*F('.9998')/F('.92')-1)
gt('strip zero-core upper derivative',1-F('1.073')*F('.33')/(F('.817')*F('.9998')-F('.02')))

result={
 'status':'PASS',
 'scope':'Six whole mixed quarter-one manuscripts, plus the aligned and edge2 closed-strip prerequisites; all declared continuous cases independently reviewed.',
 'author_replays':replays,
 'independent_comparison_count':len(checks),
 'independently_reconstructed_polynomial_count':len(poly_rows),
 'independently_reconstructed_Bernstein_count':sum(len(x['bernstein']) for x in poly_rows),
 'bindings':bindings,
 'independent_checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'checks':checks,'polynomials':poly_rows,
}
out=Path(__file__).with_name('wrong_0011011_earlier_mixed_independent_audit.json')
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ('status','author_replays','independent_comparison_count','independently_reconstructed_polynomial_count','independently_reconstructed_Bernstein_count')},indent=2))

