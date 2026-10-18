"""Fixed rational arithmetic for all same-sign mixed zero-quarter cases.

No search, optimizer, adaptive partition, or floating acceptance is used.
The only variable intervals are the explicit derivative rectangles and
eight predetermined scalar curvature intervals displayed in the paper.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
import json

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.lo,self.hi=a.lo,a.hi
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
    r=(I(a)-b).lo
    assert r>0,(name,r)
    checks.append({'name':name,'strict_reserve':str(r)})
def lt(name,a,b):gt(name,b,a)
def trig(x):
    x=F(x)
    def t(n,odd):return sum(((-1)**j*x**k/F(factorial(k)) for j,k in enumerate(range(odd,n+1,2))),F(0))
    return I(t(11,1),t(13,1)),I(t(14,0),t(12,0))

Q=I('9789/2500');R=Q.sqrt();d=(Q/2).sqrt()-F(1,2)
dc=I(F(1,2))+I(2).sqrt()/24
ac=I(F(7,12));a0=(Q-F(1,4)).sqrt()-F(1,2)
gamma=F(17953,20000)
CF={
 'P':list(map(F,('.02478','0','.93015','.02363','-.11055'))),
 'J':list(map(F,('0','-.00026','.83194','-.11864','.17627'))),
 'L':list(map(F,('.03965','0','3.85510','-1.49748','-1.89442'))),
 'K':list(map(F,('0','-.02112','.29090','0','.44642'))),
}
def outer(b):
    b=I(b);u=(Q-(b+F(1,2))**2).sqrt();return u-F(1,2),u
def label(name,b):
    b=I(b);a,u=outer(b);c,p,q,r,s=CF[name]
    return c+p*a+q*b+r*b*b+s*a*b
def deriv(name,b):
    b=I(b);a,u=outer(b);rho=(b+F(1,2))/u;c,p,q,r,s=CF[name]
    D=-p*rho+q+2*r*b+s*(a-b*rho)
    DD=2*r-2*s*rho-(p+s*b)*Q/u**3
    return D,DD

lt('disk radius below 1.979',R,'1.979')
gt('outer diagonal above .899',d,'.899')
lt('outer diagonal below .900',d,'.900')
gt('core diagonal above .5589',dc,'.5589')
lt('core diagonal below .559',dc,'.559')
lt('outer axial below 1.415',a0,'1.415')
gt('outer coordinate lower positive',d)

s026,c026=trig('.026')
gt('negative same-sign primary impossible',1,F('1.415')-F('.5589')*c026+F('.9')*s026)
gt('negative same-sign angle interval',F('.026'),F(355,452)-F('.76'))
gt('same-sign secondary bound',1,d)

r0=F(1,2)/(a0+F(1,2));rmax=1
for n in ('J','K'):
    cc,p,q,rr,ss=CF[n]
    # Upper bound for F'': the only positive contribution from -(p+s b)
    # is at most |p|Q/(d+1/2)^3.
    top=2*rr-2*ss*r0+abs(p)*Q/(d+F(1,2))**3
    lt(n+' globally concave',top,0)
    gt(n+' derivative positive at diagonal',deriv(n,d)[0])
    lt(n+' derivative at zero below 1.1',deriv(n,0)[0],'1.1')
    lt(n+' label at zero negative',label(n,0),0)
    for lo,hi,k in [('0','.1','.4'),('.1','.381','1.2')]:
        DD,D2=deriv(n,I(lo,hi))
        gt(n+' logarithmic curvature '+lo+':'+hi,D2+F(k)*DD)

gt('P derivative lower at zero',deriv('P',0)[0],'.773')
lt('P derivative upper at diagonal',deriv('P',d)[0],1)
gt('P derivative increases by explicit formula',2*CF['P'][3])
gt('P third derivative positive numerator',Q,F('.5')*(d+F('.5')))
DL,DDL=deriv('L','.5')
gt('L derivative at .5 above .6248',DL,'.6248')
gt('L second derivative at .5 above -.0311',DDL,'-.0311')
lt('L second derivative at .5 below zero',DDL,0)
gt('L third derivative lower',3*F('1.8')*F('3.9')/8,2)
gt('L global derivative above .6245',F('.6248')-F('.0311')**2/4,'.6245')
gt('L second derivative positive on contact curve',deriv('L','.6')[1],'.5')
gt('P derivative dominates core slope',F('.773'),F('.63132'))
gt('L derivative dominates core slope',F('.6245'),F('.62312'))

s44,c44=trig('.44');s49,c49=trig('.49');s7,c7=trig('.7')
gt('positive core-secondary angle barrier',-(dc-F('.5')-c44/2+(a0-F('.5'))*s44))
gt('positive outer-secondary angle barrier',-(d-F('.5')-c49/2+s49/12))
gt('positive core primary exclusion at zero',dc+F('.5'),a0-F('.5'))
gt('positive core primary exclusion at .7',(dc+F('.5'))*c7+s7/2,a0-F('.5'))
lt('sin .7 below .645',s7,'.645');gt('cos .7 above .764',c7,'.764');lt('cos .7 below .765',c7,'.765')
gt('sin .44 above .425',s44,'.425')

tangent_rows=[]
for n,c,g in [('J','.00125','1.03981'),('K','.04970','.94831')]:
    c,g=F(c),F(g);h=F('1.1')
    N7=(g*g+h*h-2*g*h*c7).sqrt()
    lt(n+' tangent norm below .75',N7,'.75')
    gt(n+' tangent envelope concave',g*F('.425'),R*F('.75')/4)
    for x in ('.44','.7'):
        sx,cx=trig(x);N=(g*g+h*h-2*g*h*cx).sqrt()
        val=F(x)+c+g/2+h/2+g*sx-R*N
        gt(n+' positive core secondary endpoint '+x,val,'.96')
        tangent_rows.append({'label':n,'x':x,'lower':'0.96'})

for n,c_core,m in [('P','.19555','.7'),('L','.16823','.6')]:
    cc=CF[n][0]
    val=F('.49')+F('.5')+c49/2-s49/12-F(c_core)+cc-(1-F(m))*d
    lower='.95' if n=='P' else '.903'
    gt(n+' positive outer secondary scalar lower',val,lower)
    gt(n+' positive outer secondary scalar increases',1-F('.5')*s7-F(1,12))
    gt(n+' core target transverse coefficient positive',c7,F('.63132') if n=='P' else F('.62312'))

# Negative core source secondary contact: Z=.5+sin+cos, Y=sqrt(Q-Z^2).
def curve(x):
    ss,cc=trig(x);m=ss+cc;Z=F('.5')+m;Y=(Q-Z**2).sqrt()
    U=Z*ss+Y*cc;V=Z*cc-Y*ss
    f=1-(cc-ss)/Y
    fp=(m*(Q-F('2.25'))-m*m/2-1)/Y**3
    return U,V,f,fp,Y,m
xs=['.3024','.35','.4','.45','.5','.55','.6','.65','.7']
curves={x:curve(x) for x in xs}
gt('negative core-secondary lower angle barrier',-(d-F('.5'))*(trig('.3024')[0]+trig('.3024')[1])+F('.5'))
gt('negative core-secondary contact exists by .7',(d-F('.5'))*(s7+c7)-F('.5'))
gt('curve coordinate lower',curves['.7'][1]-F('.5'),'.624')
lt('curve coordinate upper',curves['.3024'][1]-F('.5'),'.900')
gt('curve rate positive',curves['.3024'][2])
gt('curve rate increasing',curves['.3024'][3])
lt('curve m below Q-2.25',curves['.7'][5],Q-F('2.25'))
gt('curve radicand comparison',Q-F('2.25'),curves['.7'][5])
curvrows=[]
limits={'P':['-.55','-.69','-.89','-1.15','-1.48','-1.90','-2.41','-2.96'],
        'L':['-.11','-.16','-.23','-.31','-.40','-.49','-.62','-.86']}
for n in ('P','L'):
    for idx,(l,h) in enumerate(zip(xs,xs[1:])):
        ul,vl,fl,fpl,_,_=curves[l];uh,vh,fh,fph,_,_=curves[h]
        Dleft,DDleft=deriv(n,vl-F('.5'))
        Dright,DDright=deriv(n,vh-F('.5'))
        upper=DDleft*(uh*fh)**2-Dright*(vh*fl**2+ul*fpl)
        lt(n+' endpoint-contact curvature '+l+':'+h,upper,limits[n][idx])
        curvrows.append({'label':n,'left':l,'right':h,'strict_upper':limits[n][idx]})
for n,c in [('P','.19555'),('L','.16823')]:
    gt(n+' core-axis contact initial endpoint',F('.3024')+label(n,d)-F(c),'.89773')
    gt(n+' core-axis contact final endpoint',F('.7')+label(n,curves['.7'][1]-F('.5'))-F(c),'1.04')

# Outer negative source, negative core target, primary separator.
s45,c45=trig('.45');s56,c56=trig('.56')
gt('primary zero angle barrier .45',-(a0-F('.5')-(dc+F('.5'))*c45+(dc-F('.5'))*s45))
gt('primary core side angle barrier .56',-(a0-F('.5')-F(13,12)*c56))
gt('sin .56 above .531',s56,'.531')
bs=(Q-(1+F(13,12)*c7)**2).sqrt()-F('.5')
bd=(Q-(1+(dc+F('.5'))*c7+(F('.5')-dc)*s7)**2).sqrt()-F('.5')
lt('side contact b below .257',bs,'.257')
lt('diagonal contact b below .381',bd,'.381')
gt('corner curvature ratio t<=.4',12*F('.764'),10*F('.951')**2)
gt('sqrt1.16 above1.07',F('1.16'),F('1.07')**2)
gt('corner curvature ratio .4<=t<=.5',12*F('.764')*F('1.16')*F('1.07'),10*F('1.0275')**2)
gt('sqrt1.25 above1.11',F('1.25'),F('1.11')**2)
gt('corner curvature ratio t>=.5',12*F('.764')*F('1.11'),10)
gt('K increases on v interval',Q,3*F('.881')**2)
for vv,kk in [('.5','.4'),('.6','1.2')]:
    v=I(vv);u=(Q-v*v).sqrt()
    kval=10*v/u-Q/(u*u*v)
    gt('corner normalized curvature K at '+vv,kval,kk)
def scaled_derivative(n,b):
    b=I(b);a,u=outer(b);return deriv(n,b)[0]*u/(b+F('.5'))
def diagonal_speed(b):
    b=I(b);a,u=outer(b)
    return ((dc+F('.5'))**2+(dc-F('.5'))**2-(u-1)**2).sqrt()
gt('diagonal speed at b0',diagonal_speed(0),'.536')
gt('diagonal speed at b.25',diagonal_speed('.25'),'.658')
gt('diagonal speed increases',outer('.381')[1],1)
gt('diagonal first interval derivative product',F('2.07')*F('.536'),1)
gt('diagonal second interval derivative product',F('1.577')*F('.658'),1)
gt('side position derivative dominates largest core slope',2*F('.531'),F('1.03981'))
gt('side angle derivative product',2*F(13,12)*F('.531'),1)
primary_rows=[]
for n,c,g in [('J','.00125','1.03981'),('K','.04970','.94831')]:
    c,g=F(c),F(g)
    gt(n+' scaled derivative at .257',scaled_derivative(n,'.257'),2)
    gt(n+' scaled derivative at .25',scaled_derivative(n,'.25'),'2.07')
    gt(n+' scaled derivative at .381',scaled_derivative(n,'.381'),'1.577')
    gt(n+' axial source corner endpoint',F('.45')+c+g/2-label(n,0),'.97')
    hs=F('.7')+c+g/2-label(n,bs)
    hd=F('.7')+c+g*dc-label(n,bd)
    sl,dl=('.956',' .89778') if n=='J' else ('1.025','.9796')
    dl=dl.strip()
    gt(n+' core side endpoint at .7',hs,sl)
    gt(n+' core diagonal endpoint at .7',hd,dl)
    primary_rows.append({'label':n,'side_lower':sl,'diagonal_lower':dl})

for val in ('.96','.95','.903','.89773','1.04','.97','.956','.89778','1.025','.9796'):
    gt('printed lower bound '+val+' exceeds gamma',F(val),gamma)
out={'status':'PASS','strict_comparisons':len(checks),
     'scope':'All same-sign mixed C/O zero-quarter branches for 0011011; opposite-sign and other quarter classes are separate.',
     'tangent_rows':tangent_rows,'curvature_rows':curvrows,'primary_rows':primary_rows,'checks':checks}
Path(__file__).with_name('wrong_0011011_same_sign_mixed_zero_hand_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','strict_comparisons':len(checks)}))
