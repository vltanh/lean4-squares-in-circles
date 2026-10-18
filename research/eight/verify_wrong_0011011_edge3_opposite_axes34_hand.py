"""Fixed hand comparisons for 0011011 edge 3 (-,+), axes 3 and 4.

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
lt('unit-primary transverse upper',b1,'.791')
lt('T curvature before .415',der('T','.415')[1],0)
gt('L derivative lower reference',der('L','.5')[0],'.62481')
gt('L reference curvature lower',der('L','.5')[1],'-.032')
lt('L reference curvature upper',der('L','.5')[1],'.032')
gt('L third derivative lower',der('L',0)[2],'3.17')
gt('L derivative positive',F('.62481')-F('.032')**2/F('6.34'),'.624')
lt('L second derivative at .5',der('L','.5')[1],0)
lt('L derivative upper axial',der('L',0)[0],'1.176')
lt('L derivative upper diagonal',der('L',d)[0],'1.176')
gt('T derivative positive reference',der('T','.6')[0],'.6101')
gt('T reference curvature lower',der('T','.6')[1],'-.049')
lt('T reference curvature upper',der('T','.6')[1],'.049')
gt('T third derivative lower',der('T',0)[2],'1.6')
gt('T derivative positive',F('.6101')-F('.049')**2/F('3.2'),'.609')
lt('T derivative upper axial',der('T',0)[0],'1.069')
lt('T derivative upper diagonal',der('T',d)[0],'.774')
gt('common third derivative increases numerator',2*Q-F('.5'))

# The lower axis-3 contact is minimized first in its smaller coordinate B.
# Its implicit critical curve solves S(B)=q(b).
def S(B):
    B=I(B)
    return (B+F('.5'))**2+1/der('L',B)[0]**2
def q_of(b):
    return Q+1-2*outer(b)[1]
def critical_row(lo,hi,Bl,Bh):
    b=I(lo,hi);B=I(Bl,Bh);a,u,r,rp,rpp=geometry(b)
    q=Q+1-2*u;z=B+F('.5');lp,lpp,lppp=der('L',B);v=1/lp
    f1pp=Q/(Q+1)*(rp/u**2+2*r*r/u**3)-2*(Q-1)/(Q+1)*(rp/q**2-4*r*r/q**3)
    E=rpp-6*r*rp/q-3*r*rp/v**2+8*r**3/q**2+4*r**3/(q*v**2)+3*r**3/v**4
    Clll=f1pp-z/(q*v)*E-der('T',lo)[2]
    Clls=-rp/v**3+3*r*r/v**5
    Clss=-3*z*r/v**5
    Css=1/v**3+3*z*z/v**5-lppp
    k=r/(z-lpp*v**3)
    R3=Clll+3*Clls*k+3*Clss*k*k+Css*k**3
    return R3
critical_rows=[]
for lo,hi,Bl,Bh,UB in [
    ('0','.1','.0309','.0458','-.9'),
    ('.1','.2','.0457','.0628','-.78'),
    ('.2','.3','.0627','.0819','-.65'),
    ('.3','.4','.0818','.1028','-.57'),
    ('.4','.5','.1027','.1254','-.54'),
    ('.5','.6','.1253','.1499','-.55')]:
    lt('critical curve lower bracket '+lo,S(Bl),q_of(lo))
    gt('critical curve upper bracket '+hi,S(Bh),q_of(hi))
    bound=critical_row(lo,hi,Bl,Bh)
    lt('reduced third derivative '+lo+':'+hi,bound,UB)
    critical_rows.append({'source_interval':[lo,hi],'critical_target_interval':[Bl,Bh],'upper':UB,'exact_upper':str(bound.hi)})

def lower_inverse(b,B):
    b=I(b);B=I(B);a,u,r,rp,rpp=geometry(b);q=Q+1-2*u
    z=B+F('.5');v=(q-z*z).sqrt();N=4*Q*u-2*u*u-Q*(Q+1)
    fl=(Q-u)/(u*q)-r*z/(q*v)
    fll=-r*N/(u*u*q*q)-z/(q*v)*(rp-2*r*r/q-r*r/(v*v))
    return fl-der('T',b)[0],fll-der('T',b)[1]-r*r/(v**3*(z-der('L',B)[1]*v**3))
def lower_point(b,B):
    b=I(b);B=I(B);a,u=outer(b);q=Q+1-2*u;z=B+F('.5');v=(q-z*z).sqrt()
    w=a-F('.5');y=b+F('.5')
    x=atan_small((w*v-y*z)/(w*z+y*v))
    return pi2-x-label('T',b)-label('L',B)
Bref=I('.12421535815','.12421535816')
Bhalf=I('.12539102082','.12539102083')
lt('reference critical lower bracket',S(Bref.lo),q_of('.495'))
gt('reference critical upper bracket',S(Bref.hi),q_of('.495'))
lt('half critical lower bracket',S(Bhalf.lo),q_of('.5'))
gt('half critical upper bracket',S(Bhalf.hi),q_of('.5'))
gt('reduced curvature at .5',lower_inverse('.5',Bhalf)[1],'.06')
gt('reduced derivative at .5',lower_inverse('.5',Bhalf)[0],'.00025')
gt('reduced reference cost',lower_point('.495',Bref),'.89779')
gt('reduced reference derivative lower',lower_inverse('.495',Bref)[0],'-.0001')
lt('reduced reference derivative upper',lower_inverse('.495',Bref)[0],'.0001')
gt('reduced strong-convexity conclusion',F('.89779')-F('.0001')**2/F('.12'),'.89777')
lt('small target derivative at zero boundary',1/(q_of(0)-F('.25')).sqrt()-der('L',0)[0],0)
def aligned_small_derivative(b):
    b=I(b)
    return 1/(b+F('.5'))-der('L',outer(b)[0]-1)[0]
gt('critical exit later than .5',aligned_small_derivative('.5'))
lt('critical exit earlier than .6',aligned_small_derivative('.6'),0)
lt('L curvature throughout aligned target range',der('L',a0-1)[1],0)
s571,c571=trig('.571')
lt('lower axis3 angle cap',(a0-F('.5'))*c571-F('.5')*s571,F('.5'))

# Axis3 above alignment has the same common zero exit as axes12.
s31,c31=trig('.31');s7,c7=trig('.7')
lt('upper axis3 target cap',(Q-2*a0).sqrt()-F('.5'),'.543')
gt('upper axis3 contact angular derivative',1-F('1.176')*F('.4'))
for name,z in [('b1',b1),('d',d)]:
    az,_=outer(z)
    for x,s,c in [('.31',s31,c31),('.7',s7,c7)]:
        gt('upper zero exit excluded corner '+name+':'+x,(az-F('.5'))*c+(z-F('.5'))*s,F('.5'))
gt('upper zero exit denominator positive',(b1-F('.5'))*c31-F('.5')*s31)
gt('upper zero exit ratio numerator',F('.86')*c31-s31,F('.5'))
gt('upper zero exit dominates T',F('.5')/F('.4'),'1.069')

# A global primary-label lower bound for the lower half of axis4.
def primary(a):
    a=I(a);b=(Q-(a+F('.5'))**2).sqrt()-F('.5')
    return b,der('T',b)[0]*(a+F('.5'))/(b+F('.5'))
gt('primary slope convexity numerator',F('.95769')*F('3.9')-F('1.238845')*F('1.4'),2)
gt('primary slope curvature',3*F('3.9')*2/32,'.7')
r84=F('1.34')/outer('.84')[1]
gt('primary slope reference',der('T','.84')[0]-F('.76')*r84,'.00726')
gp84=der('T','.84')[1]-F('.76')*Q/outer('.84')[1]**3
gt('primary slope reference derivative lower',gp84,'-.016')
lt('primary slope reference derivative upper',gp84,'.016')
gt('primary slope square completion',F('.00726')-F('.016')**2/F('1.4'))
gt('lower axis4 angular derivative',F('.76')**2*(Q-F('.915')**2),1)

# Upper axis4: target-coordinate contact derivative is positive for B>=.2.
def support_F(B):
    B=I(B);a,u,r,rp,rpp=geometry(B);lp,lpp,lppp=der('L',B)
    v=(u-1)*c7+(B+F('.5'))*s7;m=s7-r*c7
    return c7+r*s7-lp*v,rpp*s7-lppp*v-2*lpp*m+lp*rp*c7
support_rows=[]
for lo,hi,UB in [('.2','.5','-1'),('.5','.7','-3.5'),('.7','.9','-3.2')]:
    bound=support_F(I(lo,hi))[1]
    lt('upper axis4 support concavity '+lo+':'+hi,bound,UB)
    support_rows.append({'interval':[lo,hi],'upper':UB,'exact_upper':str(bound.hi)})
gt('upper axis4 support at .2',support_F('.2')[0],'.082')
gt('upper axis4 support at diagonal',support_F(d)[0],'.0068')
gt('upper axis4 inactive exit before target diagonal',
   F('.5')+(d+F('.5'))*c7-(d-F('.5'))*s7,d)

# For B<=.2 the contact instead increases with the upper angle.
# T'-m*r is strictly convex for m=.85 and m=1.051.
gt('primary upper support curvature numerator',
   F('.95769')*F('3.9')-(F('.478845')+F('1.051'))*F('1.4'))
lt('primary slope upper at diagonal',primary(d)[1],'.85')
lt('primary slope upper at 1.1',primary('1.1')[1],'.85')
lt('primary slope upper at 1.2',primary('1.2')[1],'1.051')
qmax=Q-2*outer('.2')[0]
lt('upper axis4 low-primary angular product',F('.85')**2*(qmax-(d-F('.5'))**2),1)
lt('upper axis4 high-primary angular product',F('1.051')**2*(qmax-F('.36')),1)

output={'status':'PASS','scope':'0011011 edge3 (-,+), full-angle axes3/4; aligned input is proved in axes12 companion',
 'Q':'9789/2500','target':'89777/100000','checks':checks,
 'critical_curve_rows':critical_rows,'upper_axis4_support_rows':support_rows}
Path(__file__).with_name('wrong_0011011_edge3_opposite_axes34_hand_arithmetic.json').write_text(json.dumps(output,indent=2)+'\n')
print('PASS',len(checks),'fixed strict comparisons')

