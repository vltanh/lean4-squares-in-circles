"""Fixed rational comparisons for the whole 0011011 edge-3 negative OO row.

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
ell=pi2-F('.7')
b1=(Q-F('2.25')).sqrt()-F('.5')
q0=Q-2*a0
gt('Machin lower pi/2',pi2,'1.57079632679489')
lt('Machin upper pi/2',pi2,'1.57079632679490')
gt('diagonal lower',d,'.899');lt('diagonal upper',d,'.9')
gt('axial lower',a0,'1.4145');lt('axial upper',a0,'1.415')
gt('unit-primary transverse lower',b1,'.7905');lt('unit-primary transverse upper',b1,'.791')
gt('T third derivative increases numerator',2*Q-F('.5'))
gt('T third derivative at zero',der('T',0)[2],'1.6')
gt('T derivative reference',der('T','.6')[0],'.6101')
gt('T second derivative reference lower',der('T','.6')[1],'-.049')
lt('T second derivative reference upper',der('T','.6')[1],'.049')
gt('T derivative global lower',F('.6101')-F('.049')**2/F('3.2'),'.609')
lt('T derivative upper axial',der('T',0)[0],'1.069')
lt('T derivative upper diagonal',der('T',d)[0],'.774')
gt('K third derivative negative numerator',F('.44642')*Q-F('.24433')*F('1.4'))
gt('K fourth derivative negative numerator at zero',
   5*F('.44642')*Q*F('.5')-F('.24433')*(Q+1))
gt('K fourth derivative numerator increases',
   5*F('.44642')*Q-8*F('.24433')*F('1.4'))
lt('K second derivative axial',der('K',0)[1],'-.221')
lt('K third derivative axial',der('K',0)[2],'-.742')
lt('K derivative global upper',der('K',0)[0],'.928')
gt('K derivative global lower',der('K',d)[0],'.31')
lt('T second derivative at .42',der('T','.42')[1],0)
gt('outer primary at .415',outer('.415')[1],'1.75')

# The exact M(a)=-T(b(a)) derivative.
def primary_M(a):
    a=I(a);u=a+F('.5');w=(Q-u*u).sqrt();b=w-F('.5')
    return -label('T',b),der('T',b)[0]*u/w,b
gt('aligned outer slope lower',(b1+F('.5'))/F('1.5'),'.86')
lt('T derivative aligned left',der('T',b1)[0],'.774')
gt('K derivative aligned target',der('K','.101')[0],'.901')
lt('aligned target coordinate',1-d,'.101')
gt('aligned minimum',pi2-label('T',b1)+label('K',0),'.939')

# Axes 1 and 2.
s571,c571=trig('.571')
lt('axis1 lower last feasible x',(a0-F('.5'))*c571-F('.5')*s571,F('.5'))
lt('axis1 lower derivative product',F('1.069')*F('.915'),1)
gt('axis1 lower final bound',pi2-F('.571')-label('T',0)+label('K',0),'.953')
lt('axis1 upper source cap',q0.sqrt()-F('.5'),'.543')
gt('axis1 upper direct bound',pi2-label('T','.543')+label('K',0),'1.09')
s626,c626=trig('.626')
gt('correct lower axis1 target-cost concavity numerator',
   F('.44642')*Q-(F('.24433')+F('1.069')*c7)*F('1.4'),'.261')
gt('correct lower axis1 target-cost derivative axial',
   der('K',0)[0]+F('1.069')*(F('.5')/outer(0)[1]*c7-s7),'.44')
gt('correct lower axis1 target-cost derivative diagonal',
   der('K',d)[0]+F('1.069')*(c7-s7),'.44')
gt('correct lower axis1 early zero-source cost',pi2-F('.626')-label('T',0)+label('K',0),'.8982')
gt('correct lower axis1 late zero-source cost',pi2-F('.7')-label('T',0)+label('K','.1'),'.9157')
gt('correct lower axis1 small target derivative',s626-F('.6')/outer('.1')[1]*c626)
lt('correct lower axis1 small target infeasible',
   (outer('.1')[0]-F('.5'))*c626-F('.4')*s626-F('.5'),'-.0166')
gt('correct upper axis1 direct bound',pi2-label('T','.415')+label('K',0),'1.175')
s25,c25=trig('.25')
gt('axis2 lower angle cap',F('1.75')*s25+F('.5')*c25,'.915')
gt('axis2 lower cap increases',F('1.75')*c7-F('.5')*s7)
gt('axis2 lower direct bound',pi2-F('.25')-label('T','.415')+label('K',0),'.925')
s1,c1=trig('.1')
lt('axis2 upper early source cap',F('.915')*(1+s1)/c1-F('.5'),'.512')
gt('axis2 upper early direct bound',pi2-label('T','.512')+label('K',0),'1.1')
gt('axis2 upper late direct bound',pi2+F('.1')-label('T',d)+label('K',0),'.96')

# Upper secondary/primary axes flow down to alignment.
gt('axis3 upper angle derivative',1-F('.928')*F('.4'))
lt('axis3 upper target cap',F('.5')+F('.5')*s7,d)
lt('axis4 upper angle derivative product',F('.9')*q0.sqrt(),1)

# Whole-primary M'>.76, and its stronger bounds after a=1.1.
gt('M slope convexity numerator',F('.95769')*F('3.9')-F('1.238845')*F('1.4'),2)
gt('M slope convexity bound',3*F('3.9')*2/32,'.7')
u84=outer('.84')[1];r84=F('1.34')/u84
g84=der('T','.84')[0]-F('.76')*r84
g84p=der('T','.84')[1]-F('.76')*Q/u84**3
gt('M slope reference',g84,'.00726')
gt('M slope reference derivative lower',g84p,'-.016')
lt('M slope reference derivative upper',g84p,'.016')
gt('M slope square completion',F('.00726')-F('.016')**2/F('1.4'))
lt('b at primary 1.1',primary_M('1.1')[2],'.665')
lt('T curvature before b=.665',der('T','.665')[1],'.17')
gt('M increasing after primary 1.1',F('.609')*F('3.9')/8-F('.17')*F('.75'))
gt('M derivative at primary 1.1',primary_M('1.1')[1],'.84')
gt('M derivative at primary 1.2',primary_M('1.2')[1],1)
gt('axis4 lower active product first',F('.76')**2*(Q-F('1.8')-F('.6')**2),1)
gt('axis4 lower active product second',F('.84')**2*(Q-F('1.8')-F('.7')**2),1)
gt('axis4 lower active product third',Q-F('1.8')-F('.915')**2,1)
gt('axis4 lower primary increases',F('1.399')*c7-F('.5')*s7)
gt('axis4 lower terminal primary B=0',F('.5')+F('.5')*c7+(a0+F('.5'))*s7,d)
gt('axis4 lower terminal primary B=d',F('.5')+(F('.5')-d)*c7+(d+F('.5'))*s7,d)

# The lower-axis-4 source-diagonal contact curve.
k=F('.5')-d
def diag4(x):
    s,c=trig(x);Z=c+k;Y=(Q-Z*Z).sqrt()
    U=Y*c-Z*s;V=Y*s+Z*c;f=1-s/Y
    fp=((1-Q+k*k)*c+k*(1+c*c))/Y**3
    return V-F('.5'),U,V,f,fp
gt('double diagonal reached before .556',diag4('.556')[0],d)
gt('diagonal lower initial cost',pi2-label('T',d)+label('K',1-d),'.953')
gt('double diagonal lower final cost',pi2-F('.556')-label('T',d)+label('K',d),'.9388')
gt('diagonal curve f positive',diag4('.556')[3],'.7')
gt('diagonal curve U positive',diag4('.556')[1],1)

# Lower axis 3: no interior contact minimum.
# If C_x=0 then v=1/K'(B).
kp1,kpp1,_=der('K','.1')
lt('stationary curvature at target .1',kpp1+F('.4')*kp1**3,0)
lt('small-target u curvature',
   -1-F('.742')/F('.928')**3-3*F('.221')**2/F('.928')**4,'-2.1')
def stationary_u(B):
    B=I(B);kp,kpp,_=der('K',B)
    return (Q+1-(B-F('.5'))**2-1/kp**2)/2,F('.5')-B+kpp/kp**3
gt('small-target u left lower',stationary_u(0)[0],'1.752')
gt('small-target u right lower',stationary_u('.1')[0],'1.752')
lt('small-target u left upper',stationary_u(0)[0],'1.7521')
lt('small-target u left derivative',stationary_u(0)[1],'.224')
gt('small-target u upper completion',F('1.765')-F('1.7521')-F('.224')**2/F('4.2'))
gt('small-target b lower radicand',Q-F('1.765')**2,F('.894')**2)
lt('small-target b upper radicand',Q-F('1.752')**2,F('.92')**2)
gt('small-target v lower',1/F('.928'),'1.077')
ratio=(Q-F('1.765'))/(F('1.765')*(Q+1-F('3.504')))-(F('.92')/F('1.752'))*F('.5')/((Q+1-F('3.53'))*F('1.077'))
gt('small-target stationary b derivative',ratio-der('T','.394')[0],'.007')

def lower3(b,x):
    b=I(b);a,u=outer(b);s,c=trig(x);r=(b+F('.5'))/u
    B=F('.5')-(a-F('.5'))*c+(b+F('.5'))*s
    v=(a-F('.5'))*s+(b+F('.5'))*c
    kb=r*c+s;kb1=Q/u**3*c;kb2=3*Q*(b+F('.5'))/u**5*c
    return B,v,kb,kb1,kb2

# b=0: the cost decreases in x, and the final endpoint is loose.
lt('axis3 zero source speed',F('.928')*q0.sqrt(),1)
gt('axis3 zero source final cost',ell-label('T',0)+label('K',lower3(0,'.7')[0]),'.936')

# B=0: six fixed derivative rows and one midpoint per row.
def axial(x):
    s,c=trig(x);Z=F('.5')+c;Y=(Q-Z*Z).sqrt()
    U=Z*c+Y*s;V=Y*c-Z*s;f=1-s/Y
    fp=(F('.5')+(F('1.25')-Q)*c+F('.5')*c*c)/Y**3
    return V-F('.5'),U,V,f,fp
lt('axial contact ends before .571',axial('.571')[0],0)
gt('axial U positive',axial(0)[1],1)
gt('axial V positive on extension',axial('.571')[2],'.49')
gt('axial f positive on extension',axial('.571')[3],'.62')
axial_rows=[]
for lo,hi,mid,LB,UB,CB in [
    ('0','.1','.05','.843','1.078','.9374'),
    ('.1','.2','.15','.835','.999','.9289'),
    ('.2','.3','.25','.812','1.073','.9210'),
    ('.3','.4','.35','.780','1.181','.9197'),
    ('.4','.5','.45','.744','1.301','.9283'),
    ('.5','.571','.5355','.723','1.356','.9448')]:
    zl,Ul,Vl,fl,_=axial(lo);zh,Uh,Vh,fh,_=axial(hi)
    # T' is convex, hence its maximum on this physical b interval
    # is at an endpoint. The final interval is clipped at b=0.
    low_b=I(max(F(0),zh.lo),max(F(0),zh.hi))
    ds=[der('T',low_b)[0],der('T',zl)[0]]
    tmax=max(v.hi for v in ds)
    lower=F('.609')*Ul*fh;upper=tmax*Uh*fl
    gt('axial speed lower '+lo+':'+hi,lower,LB)
    lt('axial speed upper '+lo+':'+hi,upper,UB)
    cost=pi2-F(mid)-label('T',axial(mid)[0])+label('K',0)
    gt('axial midpoint '+mid,cost,CB)
    axial_rows.append({'x':[lo,hi],'midpoint':mid,
                       'speed_lower':str(lower.lo),'speed_upper':str(upper.hi),
                       'midpoint_cost_lower':str(cost.lo),
                       'displayed_lower':LB,'displayed_upper':UB,
                       'displayed_midpoint_cost':CB})
gt('axial all lower bounds imply Lipschitz',F('.723'),F('5/8'))
lt('axial all upper bounds imply Lipschitz',F('1.356'),F('11/8'))
gt('axial all midpoint costs',F('.9197'),F('.919'))
gt('axial midpoint Lipschitz conclusion',F('.919')-F('3/8')*F('.05'),'.9')

# b=d: every interior stationary point has negative second derivative
# by the same target>=.1 identity above; only its two endpoints remain.
gt('source diagonal initial target',1-d,'.1')
gt('source diagonal last angle before .556',lower3(d,'.556')[0],d)

# B=d: its complete boundary decreases to x=.7.
lt('target diagonal starts after .5',lower3(d,'.5')[0],d)
lt('target diagonal source above .75',lower3('.75','.7')[0],d)
lt('target diagonal primary bound',outer('.75')[1],'1.535')
lt('target diagonal T derivative first endpoint',der('T','.75')[0],'.774')
gt('sine .5 lower',trig('.5')[0],'.479')
gt('sqrt2 upper',F('1.415')**2,2)
lt('target diagonal boundary derivative product',
   F('.774')*(F('1.535')-F('.479')/F('1.415')),1)

# The fixed endpoint x=.7: its cost has strictly decreasing curvature.
Z=c7+F('.5')-d;Y=(Q-Z*Z).sqrt()
bmax=Y*c7-Z*s7-F('.5')
gt('endpoint bmax lower',bmax,'.7518');lt('endpoint bmax upper',bmax,'.752')
gt('endpoint target at b=0 positive',lower3(0,'.7')[0],0)
def end3(b):
    B,v,kb,kb1,kb2=lower3(b,'.7')
    t,t2,t3=der('T',b);h,h2,h3=der('K',B)
    return ell-label('T',b)+label('K',B),-t+h*kb,-t2+h2*kb*kb+h*kb1,-t3+h3*kb**3+3*h2*kb*kb1+h*kb2
lt('endpoint third derivative whole interval',
   -F('1.6')+F('.928')*3*Q*F('1.252')*F('.765')/outer('.752')[1]**5,'-.36')
gt('endpoint derivative at .4',end3('.4')[1],'.06')
gt('endpoint curvature at .4',end3('.4')[2],'.24')
gt('endpoint reference cost',end3('.275034')[0],'.8977814')
gt('endpoint reference derivative lower',end3('.275034')[1],'-0.000001')
lt('endpoint reference derivative upper',end3('.275034')[1],'0.000001')
gt('endpoint square completion',F('.8977814')-F('0.000001')**2/F('.48'),'.89778')
gt('endpoint diagonal-target cost',ell-label('T',bmax)+label('K',d),'.8977831')
gt('final target comparison',F('.89777'),F('17953/20000'))

out={'status':'PASS: whole edge-3 negative outer quarter row',
     'Q':'9789/2500','target':'17953/20000','comparison_count':len(checks),
     'axial_rows':axial_rows,'checks':checks}
data=Path(__file__).with_name('wrong_0011011_edge3_negative_outer_quarter_hand_arithmetic.json')
data.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

