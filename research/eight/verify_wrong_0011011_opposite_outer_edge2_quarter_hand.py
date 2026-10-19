"""Fixed rational arithmetic for the whole edge-2 (-,+) outer quarter row.

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
    x=F(x);return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
pi2=I(8*atan_sum('1/5',16)-2*atan_sum('1/239',5),
      8*atan_sum('1/5',15)-2*atan_sum('1/239',4))
ell=pi2-F('.7');b1=(Q-F('2.25')).sqrt()-F('.5')
gt('Machin lower',pi2,'1.57079632679489');lt('Machin upper',pi2,'1.57079632679490')
gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.9')
lt('axial upper',a0,'1.415');gt('unit-primary transverse lower',b1,'.7905')
lt('unit-primary transverse upper',b1,'.791')
gt('P derivative lower',der('P',0)[0],'.773')
lt('P derivative upper',der('P',d)[0],'.973')
gt('P second derivative positive',der('P',0)[1])
lt('P second derivative below .415',der('P','.415')[1],'.197')
lt('P second derivative below b1',der('P',b1)[1],'.345')
gt('P fourth derivative numerator',Q*(5*F('.5')-F('.5'))-2*F('1.4')**2)
gt('R negative third derivative numerator',CF['R'][4]*Q+(CF['R'][1]-CF['R'][4]/2)*F('1.4'))
lt('R global concavity',-2*CF['R'][4]*F('.261')+abs(CF['R'][1])*Q/(d+F('.5'))**3,0)
gt('outer slope lower',F('.5')/(a0+F('.5')),'.261')
gt('R derivative positive',der('R',d)[0])
lt('R derivative upper',der('R',0)[0],'1.061')
gt('R derivative through .415',der('R','.415')[0],'.82')
lt('upper transverse contact never reaches diagonal',(Q-2*a0).sqrt()-F('.5'),d)
gt('upper transverse contact low-coordinate primary',outer('.5')[0]-F('.5'),'.7')
gt('upper transverse contact height positive',F('.7')*c7-F('.5')*s7)

def M(a):
    a=I(a);u=a+F('.5');w=(Q-u*u).sqrt();b=w-F('.5')
    D=(F('.93015')+F('.04726')*b-F('.11055')*a)*u/w+F('.11055')*b
    DD=F('.04726')+Q*(F('.961795')-F('.11055')*u)/w**3-F('.2211')*u/w
    return -label('P',b),D,DD
gt('M third derivative positive numerator',F('.961795')*(d+F('.5'))-F('.11055')*Q)
gt('M second derivative lower',M(d)[2],'.979')
gt('M derivative lower',M(d)[1],'.972')
gt('M unit-primary derivative lower',M(1)[1],'1.083')
lt('M unit-primary derivative upper',M(1)[1],'1.084')
gt('aligned source-primary monotonicity',F('1.083')-F('1.061'))
gt('aligned source-primary endpoint',pi2-label('P',b1)-label('R',0),'.8977861')

# The other aligned curve: b=A(B)-1.
def aligned_other(B):
    B=I(B);A,u=outer(B);b=A-1;r=(B+F('.5'))/u
    return pi2-label('P',b)-label('R',B),der('P',b)[0]*r-der('R',B)[0]
gt('other aligned global curvature',-F('.197')+F('.773')*Q/(a0+F('.5'))**3,'.2')
v,hp=aligned_other('.6581')
gt('other aligned reference cost',v,'.9091246')
lt('other aligned reference derivative upper',hp,'.00001')
gt('other aligned reference derivative lower',hp,'-.00001')
gt('other aligned completion',F('.9091246')-F('.00001')**2/F('.4'),'.9091')
gt('other aligned axial endpoint',pi2-label('P',0)-label('R',b1),'.9278')

# Common zero-coordinate contact curve for the negative angle half.
def cap(x):
    s,c=trig(x);Z=F('.5')+c;Y=(Q-Z*Z).sqrt()
    U=Z*c+Y*s;V=Y*c-Z*s;f=1-s/Y
    fp=(F('.5')+(F('1.25')-Q)*c+F('.5')*c*c)/Y**3
    return V-F('.5'),U,V,f,fp
gt('cap f positive through .571',cap('.571')[3])
lt('cap final transverse negative',cap('.571')[0],0)
gt('cap negative fprime numerator monotonicity',Q-F('1.25')-1)
gt('cap negative fprime at endpoint',-cap('.571')[4],'.45')
gt('axis1 negative derivative product decreases',F('.773')*F('1.5')-F('.197')*(Q-F('2.25')))
lt('axis1 negative derivative endpoint product',der('P',0)[0]*(Q-F('2.25')).sqrt(),1)
cap_curvature_rows=[]
for lo,hi,bound in [('0','.1','2.25'),('.1','.2','1.39'),('.2','.3','.66')]:
    B0,U0,V0,f0,fp0=cap(lo);B1,U1,V1,f1,fp1=cap(hi)
    velocity=U0*f1
    second=-V1*f1*f1-U1*fp0
    rr,rr2,_=der('R',B1)
    lower=-rr2*velocity*velocity-rr*second
    gt('axis1 axial curvature '+lo+':'+hi,lower,bound)
    cap_curvature_rows.append([lo,hi,bound])
B,U,V,f,fp=cap('.15017')
H=pi2-F('.15017')-label('P',0)-label('R',B)
Hp=-1+der('R',B)[0]*U*f
gt('axis1 axial reference cost',H,'.8977853')
lt('axis1 axial reference derivative upper',Hp,'.00001')
gt('axis1 axial reference derivative lower',Hp,'-.00001')
gt('axis1 axial completion',F('.8977853')-F('.00001')**2/F('1.32'),'.89778')
lt('cap V after .3',cap('.3')[2],'.851')
gt('cap U after .3',cap('.3')[1],'1.786')
lt('cap f after .3',cap('.3')[3],'.78')
gt('cap late positive second derivative',F('1.786')*F('.45')-F('.851')*F('.78')**2)
gt('cap late speed lower',cap('.571')[1]*cap('.571')[3],'1.203')
gt('R derivative on late cap',der('R',cap('.3')[0])[0],'.875')
gt('axis1 late cap derivative',F('.875')*F('1.203'),1)

# A common upper-angle zero-coordinate exit:
# (a(z)-.5)cos x+(z-.5)sin x=.5, b1<=z<=d.
exit_checks=[]
for zname,z in [('b1',b1),('d',d)]:
    for x in ['.4','.7']:
        s,c=trig(x)
        gt('upper zero exit absent '+zname+':'+x,(outer(z)[0]-F('.5'))*c+(z-F('.5'))*s,F('.5'))
gt('upper zero exit transverse slope',(b1+F('.5'))/F('1.5'),'.86')
gt('upper zero exit cosine',trig('.4')[1],'.921')
lt('upper zero exit sine',trig('.4')[0],'.39')
gt('upper zero exit denominator positive',F('.2905')*F('.921')-F('.5')*F('.39'))
gt('upper zero exit derivative greater than1',F('.86')*F('.921')-F('.39'),'.4')
lt('R derivative on upper zero exit',der('R',b1)[0],'.4')

# Axis 2 lower half: interior critical points, target B=0,
# and the remaining axial source.
gt('axis2 lower stationary angle derivative',F('1.75')*F('.773'),1)
gt('axis2 lower source primary bound',outer('.415')[1],'1.75')
gt('axis2 lower axial early direct',pi2-F('.02')-label('P',0)-label('R',b1),'.9078')
gt('N logarithmic derivative lower',Q/(F('1.915')*F('1.291')**2),'1.22')
gt('axis2 lower axial product increases',F('1.22')*(Q-F('.915')**2)-F('.915'))
def Nprime(A):
    A=I(A);B=(Q-(A+F('.5'))**2).sqrt()-F('.5')
    return der('R',B)[0]*(A+F('.5'))/(B+F('.5'))
s02,c02=trig('.02');A02=F('.5')+(a0+F('.5'))*s02+F('.5')*c02
gt('axis2 lower axial derivative at .02',Nprime(A02)*((a0+F('.5'))*c02-F('.5')*s02),1)

# Uniform P slope-ratio control for all upper axis-2 contacts.
p_ratio_rows=[]
for lo,hi,bound in [('0','.3','.966'),('.3','.5','.973'),('.5','.7','.993'),
                    ('.7','.8','.933'),('.8','.9','.924')]:
    u=outer(lo)[1];rh=(F(hi)+F('.5'))/outer(hi)[1]
    upper=der('P',hi)[0]*(u-c7/(c7+rh*s7))
    lt('axis2 upper P ratio '+lo+':'+hi,upper,bound)
    p_ratio_rows.append([lo,hi,bound])
lt('N derivative at unit primary',Nprime(1),'.44')
lt('axis2 upper axial speed norm',((a0-F('.5'))**2+F('.25')).sqrt(),'1.043')
gt('axis2 upper axial derivative',1-F('.44')*F('1.043'))
gt('upper contact reaches target d',F('.5')+(d+F('.5'))*c7-(d-F('.5'))*s7,d)

# Axis 3 lower half: a small aligned strip and a concave scalar.
gt('P restricted upper chord',F('.83829')*b1,label('P',b1)-label('P',0))
gt('axis3 short-strip global contact curvature',
   -F('.345')+F('.82')*Q/(a0+F('.5'))**3*trig('.01')[1],'.1')
gt('axis3 short-strip endpoint b lower',cap('.01')[0],'.775')
gt('P derivative short-strip endpoint',der('P','.775')[0],'.9269')
lt('source slope through b1',(b1+F('.5'))/F('1.5'),'.861')
gt('axis3 short-strip negative b derivative',F('.9269')-F('1.061')*F('.871'))
gt('axis3 short-strip endpoint speed',F('1.5')*cap('.01')[3],'1.488')
gt('axis3 short-strip endpoint angle derivative',F('.9269')*F('1.488'),1)
g=F('.83829');h=F('1.061')
def support(x):
    s,c=trig(x);n=(g*g+h*h-2*g*h*s).sqrt()
    return pi2-F(x)-label('P',0)-label('R',0)-R*n+h*c+(g+h)/2
support_rows=[]
for lo,hi,bound in [('.01','.1','-.33'),('.1','.2','-.31'),('.2','.3','-.29'),
                    ('.3','.4','-.25'),('.4','.5','-.19'),('.5','.6','-.11'),('.6','.7','-.015')]:
    sl,cl=trig(lo);sh,ch=trig(hi)
    nl=(g*g+h*h-2*g*h*sl).sqrt();nh=(g*g+h*h-2*g*h*sh).sqrt()
    upper=-h*ch-R*g*h*sl/nl+R*g*g*h*h*cl*cl/nh**3
    lt('axis3 support concavity '+lo+':'+hi,upper,bound)
    support_rows.append([lo,hi,bound])
gt('axis3 support initial endpoint',support('.01'),'.8982')
gt('axis3 support final endpoint',support('.7'),'.986')

# Axis 4 lower half.
gt('axis4 lower active angle derivative',F('.972')*(Q-F('.915')**2).sqrt(),1)

# Axis 4 upper half: F(B)>R'(B), with one fixed source diagonal.
z=d-F('.5')
def ratio_F(B):
    B=I(B);A,u=outer(B);v=B+F('.5');q=Q+1-2*u;k=(q-z*z).sqrt()
    return (Q-u)/(u*q)+v*z/(u*q*k)
gt('axis4 upper initial ratio reserve',ratio_F(0)-der('R',0)[0],'.001')
r_ratio_rows=[]
for lo,hi,bound in [('0','.2','.05'),('.2','.4','.21'),('.4','.6','.47'),
                    ('.6','.8','.89'),('.8','.9','1.65')]:
    B=I(lo,hi);A,u=outer(B);r=(B+F('.5'))/u;q=Q+1-2*u;k=(q-z*z).sqrt()
    def nn(t):return 4*Q*t-2*t*t-Q*(Q+1)
    num=I(nn(I(u.lo)).lo,nn(I(u.hi)).hi)
    fp=-r*num/(u*u*q*q)+z/(q*k)*(Q/u**3-2*r*r/q-r*r/(k*k))
    lower=fp-der('R',lo)[1]
    gt('axis4 upper ratio derivative '+lo+':'+hi,lower,bound)
    r_ratio_rows.append([lo,hi,bound])
q0=Q-2*a0
gt('axis4 upper target-zero product increases',F('.67')*(q0-F('.25'))-F('1.084')*F('.5'))
lt('axis4 upper target-zero endpoint product',M(1)[1]*(a0-F('.5')),1)
result={'status':'PASS: whole edge-2 opposite-sign outer quarter row',
        'Q':'9789/2500','target':'17953/20000',
        'comparison_count':len(checks),'checks':checks,
        'axial_curvature_rows':cap_curvature_rows,'P_ratio_rows':p_ratio_rows,
        'support_concavity_rows':support_rows,'R_ratio_derivative_rows':r_ratio_rows}
out=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('wrong_0011011_opposite_outer_edge2_quarter_hand_arithmetic.json').write_text(out)
print(out,end='')
