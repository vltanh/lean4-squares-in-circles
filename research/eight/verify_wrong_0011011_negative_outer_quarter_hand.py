"""Fixed rational comparisons for the whole 0011011 edge-2 negative OO row.

All intervals below are fixed displayed hand bounds. No optimizer, adaptive
cover, or discovery input is used.
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
CF['T']=list(map(F,('.01670','0','2.42322','-.91744','-.95769')))

def atan_sum(x,n):
    x=F(x)
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
pi2=I(8*atan_sum('1/5',16)-2*atan_sum('1/239',5),
      8*atan_sum('1/5',15)-2*atan_sum('1/239',4))
gt('Machin lower pi/2',pi2,'1.57079632679489')
lt('Machin upper pi/2',pi2,'1.57079632679490')
ell=pi2-F('.7')
b1=(Q-F('2.25')).sqrt()-F('.5')
gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.9')
gt('axial lower',a0,'1.4145');lt('axial upper',a0,'1.415')
gt('unit-primary transverse lower',b1,'.7905')
gt('P derivative lower',der('P',0)[0],'.773')
lt('P derivative upper',der('P',d)[0],'.973')
gt('P derivative at diagonal lower',der('P',d)[0],'.972')
gt('P second derivative positive',der('P',0)[1])
gt('P and T fourth derivative positive numerator',Q*(5*F('.5')-F('.5'))-2*F('1.4')**2)
lt('P third derivative global upper',der('P',d)[2],'.779')
gt('T third derivative coarse lower',3*F('.95')*F('3.9')/8,'1.38')
gt('T derivative at .6',der('T','.6')[0],'.6101')
gt('T second derivative at .6 lower',der('T','.6')[1],'-.049')
lt('T second derivative at .6 upper',der('T','.6')[1],0)
gt('T global derivative lower',F('.6101')-F('.049')**2/F('2.76'),'.609')
lt('T global derivative upper zero',der('T',0)[0],'1.069')
lt('T global derivative upper diagonal',der('T',d)[0],'1.069')
g=F('.853')
gt('P upper chord slope',g*d,label('P',d)-label('P',0))
gt('outer slope lower',F('.5')/(a0+F('.5')),'.261')

# The aligned contact a+B=1.
def primary_M(a):
    a=I(a);u=a+F('.5');w=(Q-u*u).sqrt();b=w-F('.5')
    M=-label('P',b)
    D=(F('.93015')+2*F('.02363')*b-F('.11055')*a)*u/w+F('.11055')*b
    DD=F('.04726')+Q*(F('.961795')-F('.11055')*u)/w**3-F('.2211')*u/w
    return M,D,DD
gt('M third derivative positive numerator',F('.961795')*(d+F('.5'))-F('.11055')*Q)
gt('M second derivative at diagonal',primary_M(d)[2],'.979')
lt('aligned curvature first interval',primary_M('.95')[2]+der('T',1-d)[1],0)
lt('aligned curvature second interval',primary_M(1)[2]+der('T','.05')[1],0)
gt('aligned derivative at unit primary',primary_M(1)[1]-der('T',0)[0],'.0149')
gt('aligned minimum',pi2-label('P',d)+label('T',1-d),'.8977827')

# Axes 1 and 2, both halves.
gt('axis1 target derivative',F('.609')-g*(F('.645')-F('.261')*F('.764')))
lt('axis1 scalar derivative norm',g*g*(F('.25')+(a0-F('.5'))**2),1)
F1ell=ell+label('T',0)-label('P',0)+g/2+g*s7/2-g*(a0-F('.5'))*c7
gt('axis1 lower scalar endpoint',F1ell,'.95')
gt('axis1 upper scalar endpoint',pi2+label('T',0)-label('P',0)+g/2-g*(a0-F('.5')),'.95')
gt('axis2 lower comparison norm',(d+F('.5'))**2,F('.25')+(a0-F('.5'))**2)
gt('axis2 late upper direct',F('1.68')-label('P',d)+label('T',0),'.9')
s11,c11=trig('.11')
lt('axis2 early upper source bound',(a0*(1+s11)-1)/c11,'.6')
gt('axis2 early upper direct',pi2-label('P','.6')+label('T',0),'.95')

# Axis 3 upper half: x-derivative is positive.
gt('axis3 upper derivative',1-F('1.069')*F('.4'))

# Axis 4 upper half, active primary coordinate d<=a<=1.
q0=Q-2*a0
gt('M second derivative coarse .67',primary_M(d)[2],'.67')
lt('M derivative at unit primary',primary_M(1)[1],'1.084')
gt('axis4 upper product increases',F('.67')*(q0-F('.25'))-F('1.084')*F('.5'))
lt('axis4 upper endpoint speed product',primary_M(1)[1]*(a0-F('.5')),1)
gt('axis4 upper primary threshold decreases',F('.399')*F('.764')-F('.4')*F('.645'))

# Axis 4 lower half, active derivative and the diagonal boundary.
gt('axis4 lower active speed square',F('.972')**2*(Q-F('1.8')-F('.915')**2),1)
gt('axis4 lower primary threshold increases',F('1.399')*F('.764')-F('.5')*F('.645'))
gt('axis4 lower diagonal reached by .7',F('.5')+(F('.5')-d)*c7+(d+F('.5'))*s7,d)
k=F('.5')-d
def diag4(x):
    s,c=trig(x);Z=c+k;Y=(Q-Z*Z).sqrt()
    U=Y*c-Z*s;V=Y*s+Z*c
    f=1-s/Y
    fp=((1-Q+k*k)*c+k*(1+c*c))/Y**3
    return V-F('.5'),U*f,-V*f*f+U*fp,U,V,f,fp
gt('double diagonal x endpoint before .556',diag4('.556')[0],d)
lt('axis4 boundary early T curvature',der('T',diag4('.3')[0])[1],0)
lt('axis4 boundary mid target',diag4('.4')[0],'.724')
lt('axis4 boundary mid T curvature',der('T','.724')[1],'.396')
lt('axis4 boundary mid first derivative',diag4('.3')[1],'1.394')
gt('axis4 boundary V lower',diag4('.3')[4],'1.092')
gt('axis4 boundary U lower',diag4('.4')[3],'1.554')
gt('axis4 boundary f lower',diag4('.4')[5],'.795')
gt('axis4 boundary cosine lower',trig('.4')[1],'.92')
gt('axis4 boundary negative fprime bound',
   (Q-1-F('.16'))*F('.92')+F('.399')*(1+F('.92')**2),F('3.2'))
gt('axis4 boundary mid negative curvature',
   F('.609')*(F('1.092')*F('.795')**2+F('1.554')*F('.4'))-F('.396')*F('1.394')**2)
lt('axis4 boundary late first derivative',diag4('.4')[1],'1.238')
lt('axis4 boundary late T derivative left',der('T',diag4('.4')[0])[0],'.774')
lt('axis4 boundary late T derivative right',der('T',d)[0],'.774')
lt('axis4 boundary late derivative product',F('.774')*F('1.238'),1)
gt('axis4 boundary final cost',pi2-F('.556')-label('P',d)+label('T',d),'.903')

# Axis 3 lower half: strict concavity in b for fixed target B.
# q=Q+1-2u and z=B-.5 in[-.5,.4]. The displayed five rows
# bound the second derivative of -x(b,B)-P(b) from above.
curvature_rows=[]
for lo,hi,bound in [('0','.2','-.018'),('.2','.4','-.096'),
                    ('.4','.6','-.126'),('.6','.8','-.045'),('.8','.9','-.081')]:
    b=I(lo,hi);a,u=outer(b);r=(b+F('.5'))/u;q=Q+1-2*u
    def N(v):return 4*Q*v-2*v*v-Q*(Q+1)
    # N increases because u<Q.
    nn=I(N(I(u.lo)).lo,N(I(u.hi)).hi)
    f1prime=nn/(u*u*q*q)
    brace_lo=Q/u**3-2*r*r/q-r*r/(q-F('.25'))
    brace_hi=Q/u**3-3*r*r/q
    M=max(abs(brace_lo.lo),abs(brace_lo.hi),abs(brace_hi.lo),abs(brace_hi.hi))
    upper=-r*f1prime+F('.5')*M/(q*(q-F('.25')).sqrt())-der('P',lo)[1]
    lt('axis3 fixed-target curvature '+lo+':'+hi,upper,bound)
    curvature_rows.append([lo,hi,bound])

# Axis 3 lower contact and its derivatives.
def lower3(b,x):
    b=I(b);a,u=outer(b);s,c=trig(x);r=(b+F('.5'))/u
    B=F('.5')-(a-F('.5'))*c+(b+F('.5'))*s
    vel=(a-F('.5'))*s+(b+F('.5'))*c
    kb=r*c+s;kb1=Q/u**3*c;kb2=3*Q*(b+F('.5'))/u**5*c
    return B,vel,kb,kb1,kb2

# The zero-target part decreases in b and exits to the contact;
# the b=0 contact boundary has two direct bounds.
gt('axis3 axial early direct',pi2-F('.65')-label('P',0)+label('T',0),'.9')
gt('axis3 axial late target',lower3(0,'.65')[0],'.074')
gt('axis3 axial late direct',ell-label('P',0)+label('T',0)+F('.609')*F('.074'),'.9')

# The source-diagonal boundary H(x).
def diag3(x):
    B,v,_,_,_=lower3(d,x)
    z=B-F('.5');t,t2,t3=der('T',B)
    H=pi2-F(x)-label('P',d)+label('T',B)
    Hp=-1+t*v
    Hpp=t2*v*v-t*z
    return H,Hp,Hpp,B
gt('axis3 diagonal third derivative low interval',
   F('1.6')*(Q-2*d-F('.16'))-3*F('1.17')*F('.4')-F('1.069'))
gt('T third derivative at target .1',der('T','.1')[2],'1.6')
gt('T second derivative at target .1',der('T','.1')[1],'-1.17')
gt('T third derivative target .5',der('T','.5')[2],'2.64')
lt('T second derivative diagonal',der('T',d)[1],'1.317')
gt('axis3 diagonal third derivative high interval',
   F('2.64')*(Q-2*d-F('.16'))-3*F('1.317')*F('.4')-F('1.069'))
lt('axis3 diagonal derivative at .4',diag3('.4')[1],0)
gt('axis3 diagonal cost at .4',diag3('.4')[0],'.9095')
gt('axis3 diagonal curvature at .4',diag3('.4')[2],'.3')
gt('axis3 diagonal reference cost',diag3('.5')[0],'.90204')
lt('axis3 diagonal reference is physical',diag3('.5')[3],d)
lt('axis3 diagonal reference derivative upper',diag3('.5')[1],'.022')
gt('axis3 diagonal reference derivative lower',diag3('.5')[1],'-.022')
gt('axis3 diagonal strong-convexity lower',F('.90204')-F('.022')**2/F('.6'),'.9012')

# The endpoint angle x=.7: two early curvature rows and three
# third-derivative rows prove that every minimum is a boundary or
# belongs to the final strongly convex interval.
def end3(b):
    b=I(b);B,v,kb,kb1,kb2=lower3(b,'.7')
    p,p2,p3=der('P',b);t,t2,t3=der('T',B)
    H=ell-label('P',b)+label('T',B)
    Hp=-p+t*kb
    Hpp=-p2+t2*kb*kb+t*kb1
    Hppp=-p3+t3*kb**3+3*t2*kb*kb1+t*kb2
    return H,Hp,Hpp,Hppp,B,kb,kb1,kb2
gt('axis3 endpoint feasible source below .76',end3('.76')[4],d)
end_curvature_rows=[]
for lo,hi,bound in [('0','.1','-.389'),('.1','.2','-.362')]:
    L=end3(lo);H=end3(hi)
    upper=-der('P',lo)[1]+der('T',H[4])[1]*L[5]**2+der('T',L[4])[0]*H[6]
    lt('axis3 endpoint early curvature '+lo+':'+hi,upper,bound)
    end_curvature_rows.append([lo,hi,bound])
third_rows=[]
for lo,hi,bound in [('.2','.3','.410'),('.3','.5','.916'),('.5','.76','3.85')]:
    L=end3(lo);H=end3(hi);t2=der('T',L[4])[1]
    prod=H[5]*H[6] if t2.lo<0 else L[5]*L[6]
    lower=-der('P',hi)[2]+der('T',L[4])[2]*L[5]**3+3*t2*prod+F('.609')*L[7]
    gt('axis3 endpoint third derivative '+lo+':'+hi,lower,bound)
    third_rows.append([lo,hi,bound])
lt('axis3 endpoint derivative at .6',end3('.6')[1],0)
gt('axis3 endpoint value at .6',end3('.6')[0],'.906')
gt('axis3 endpoint curvature at .6',end3('.6')[2],'.65')
gt('axis3 endpoint reference value',end3('.72365')[0],'.89778507')
lt('axis3 endpoint reference is physical',end3('.72365')[4],d)
lt('axis3 endpoint reference derivative upper',end3('.72365')[1],'.000001')
gt('axis3 endpoint reference derivative lower',end3('.72365')[1],'-.000001')
gt('axis3 endpoint strong-convexity lower',F('.89778507')-F('.000001')**2/F('1.3'),'.89778')

result={'status':'PASS: whole edge-2 negative outer/outer quarter row',
        'Q':'9789/2500','target':'17953/20000',
        'comparison_count':len(checks),'checks':checks,
        'fixed_target_curvature_rows':curvature_rows,
        'endpoint_early_curvature_rows':end_curvature_rows,
        'endpoint_third_derivative_rows':third_rows}
out=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('wrong_0011011_negative_outer_quarter_hand_arithmetic.json').write_text(out)
print(out,end='')
