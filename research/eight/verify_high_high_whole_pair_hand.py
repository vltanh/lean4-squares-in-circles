"""Reconstructed fixed arithmetic for the whole high/high hand theorem.

Only rational comparisons, finite Taylor sums, integer square roots and
one fixed Bernstein expansion are used. There is no state search.
"""
from fractions import Fraction as F
from math import comb, factorial, isqrt
import json

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I): self.lo,self.hi=a.lo,a.hi
        else: self.lo,self.hi=F(a),F(a if b is None else b)
        assert self.lo<=self.hi
    def __add__(self,b):
        b=I(b); return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,b): return self+-I(b)
    def __rsub__(self,b): return I(b)+-self
    def __mul__(self,b):
        b=I(b); z=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(z),max(z))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b); assert not b.lo<=0<=b.hi
        return self*I(1/b.hi,1/b.lo)
    def sq(self):
        low=0 if self.lo<=0<=self.hi else min(self.lo**2,self.hi**2)
        return I(low,max(self.lo**2,self.hi**2))

def taylor(x,degree,sine):
    x=F(x)
    return sum((F((-1)**j,factorial(k))*x**k
                for j,k in enumerate(range(int(sine),degree+1,2))),F(0))

PI=I('3.14159','355/113')
def sc(x):
    if x=='quarter': return PI/2,I(1),I(0)
    return I(x),I(taylor(x,11,True),taylor(x,13,True)),I(taylor(x,14,False),taylor(x,12,False))

def sqrt_upper(x):
    x=F(x); assert x>=0
    den=10**10
    ans=F(isqrt(x.numerator*den**2//x.denominator)+1,den)
    assert ans**2>x
    return ans

def trim(p):
    p=list(p)
    while len(p)>1 and not p[-1]: p.pop()
    return p
def add(*args):
    p=[F(0)]*max(map(len,args))
    for q in args:
        for j,x in enumerate(q): p[j]+=x
    return trim(p)
def scale(p,a): return trim([a*x for x in p])
def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for j,a in enumerate(p):
        for k,b in enumerate(q): r[j+k]+=a*b
    return trim(r)
def trigpoly(degree,sine):
    p=[F(0)]*(degree+1)
    for j,k in enumerate(range(int(sine),degree+1,2)):
        p[k]=F((-1)**j,factorial(k))
    return trim(p)
def bernstein(p,l,h):
    n=len(p)-1
    return [sum((p[j]*comb(j,t)*l**(j-t)*(h-l)**t*F(comb(k,t),comb(n,t))
                 for t in range(k+1) for j in range(t,n+1)),F(0))
            for k in range(n+1)]

Q=F('9789/2500'); R=I('2.79842813','2.79842814')
u,v,gamma=map(F,('.089293','.480179','.9099'))
a0=R-1; a1=I('1.71322294','1.71322295'); b1=a1*F('.4')
label_constant=-u*a0; label1=u*(a1-a0)+v*b1
ends={'a':(a0,I(0)),'b':(a1,b1)}
checks=[]; endpoint_rows=[]
def gt(name,lhs,rhs=0):
    gap=(I(lhs)-rhs).lo
    assert gap>0,(name,str(gap))
    checks.append({'name':name,'strict_reserve':str(gap)})

gt('folded radius lower',2*Q,R.lo**2)
gt('folded radius upper',R.hi**2,2*Q)
gt('cut primary lower',2*Q,(a1.lo+1)**2+(F('.4')*a1.lo)**2)
gt('cut primary upper',(a1.hi+1)**2+(F('.4')*a1.hi)**2,2*Q)
gt('folded arc slope below .253',F('.253'),b1/(a1+1))
gt('label increases',v,u*F('.253'))
gt('label cut positive',label1)
gt('label cut upper',F('.321454'),label1)
gt('center radius greater than one',Q-a0.hi-F('.5'),1)
gt('center radius less than four thirds',F(16,9),Q-a1.lo-F('.5'))
gt('cosine comparison for positive folded angle',F(21,29),F(23,32))
gt('positive extra axis source offset',F('.3')*a1.lo,F('.51'))
gt('positive extra axis impossible',1,F(4,3)-F('.51'))
gt('negative extra axis impossible',2,(a1+b1).hi-(a1-b1).lo)

def barrier(name,x,K,A,B):
    _,s,c=sc(x)
    gt(name,-(I(K)+I(A)*s-I(B)*c))
Smax=(a1+b1).hi; diffmin=(a1-b1).lo
barrier('all signs impossible through .35','.35',Smax-1,Smax-1,1+diffmin)
barrier('negative-negative impossible through .6','.6',a0.hi-1,Smax-1,1+diffmin)
barrier('negative-positive impossible through 1','1',a0.hi-1,a0.hi-1,a0.lo+1)

gt('square root two below 1.42',F('1.42')**2,2)
assert F('.18')*F('.21')==F('.0378')
gt('common tail from quarter',PI/2-2*F('.321454'),gamma)
gt('positive-negative direct tail',F('1.05')-F('.0378'),gamma)
gt('negative-negative direct tail',F('1.27')-F('.0378')-F('.321454'),gamma)
gt('negative-positive direct tail',F('1.09')*F('1.5543')-F('.09')*PI/2-2*F('.321454'),gamma)
gt('late tail starts before quarter',PI/2,F('1.5543'))

gt('positive-source axial lower multiplier',F('.34'),u)
gt('positive-source axial upper multiplier',v,F('.43'))
for x in ('.35','1.2'):
    _,s,c=sc(x); gt('positive-positive target C at '+x,s+c,F('1.28'))
gt('positive-positive target V positive',F('.39')*F('1.28'),v)
gt('positive-negative first target U',u)
gt('positive-negative first target V',F('.55'),v)
for x in ('.6','.8','.95'):
    _,s,c=sc(x); gt('target C above1.38 at '+x,s+c,F('1.38'))
_,s08,c08=sc('.8'); gt('target D at .8 below .021',F('.021'),s08-c08)
gt('positive-negative middle target U',u,F('.43')*F('.021'))
gt('positive-negative middle target V',F('.43')*F('1.38'),v)
gt('lambda .34 endpoint support criterion',u*u+v*v,2*F('.34')**2)
_,s095,c095=sc('.95'); gt('varying target D below .232',F('.232'),s095-c095)
gt('varying target derivative auxiliary positive',F('.494')*F('.232'),u)
gt('varying target derivative negative',F('.354')*F('1.38'),
   v+F('.253')*(F('.494')*F('.232')-u))
assert F('.734')-F('.4')*F('.6')==F('.494')
assert F('.734')-F('.4')*F('.95')==F('.354')
_,s1,c1=sc('1'); gt('negative-positive first target D positive',s1,c1)
for x in ('1','1.3'):
    _,s,c=sc(x); gt('negative-positive target C at '+x,s+c,F('1.23'))
gt('negative-positive first target V',F('.4')*F('1.23'),v)
gt('late negative source decreases',v-F('.365'),(u+F('.365'))*F('.253'))

def fixed_target_coefficients(lam,tau,target):
    A,B=ends[target]; lam=F(lam)
    return lam*(1+A+tau*B)-F('.09'),lam*(1-A+tau*B)-F('.09')

for label,lam,tau,target,right in (
    ('++ axial','.39',1,'a','1.2'),
    ('++ cut','.39',1,'b','1.2'),
    ('+- first','.55',-1,'b','.6'),
    ('+- middle','.43',-1,'b','.8'),
    ('-+ first','.4',1,'a','1.3')):
    A,B=fixed_target_coefficients(lam,tau,target)
    _,s,c=sc(right)
    gt(label+' cosine coefficient positive',A)
    gt(label+' sine coefficient negative',-B)
    gt(label+' right derivative negative',A*s-B*c,1)
for target in ('a','b'):
    A,B=fixed_target_coefficients('.34',-1,target)
    gt('lambda .34 scalar increases '+target,1,A.sq()+B.sq())

for label,lam,left,nmax in (('++ circle','.39','1.2','.5'),
                           ('-+ circle','.365','1.3','.47')):
    lam=F(lam); nmax=F(nmax)
    gt(label+' nonzero norm',2*lam*lam,u*u+v*v)
    gt(label+' quarter norm bound',nmax*nmax,(u+lam)**2+(lam-v)**2)
    _,s,c=sc(left)
    gt(label+' norm increases',(u-v)*c+(u+v)*s)
    gt(label+' cost strictly concave',(2*lam-F('.09'))*s,
       F('.09')*c+R*nmax/4)

def endpoint(name,sigma,tau,lam,source,target,x):
    lam=F(lam); xx,s,c=sc(x); C=s+c; D=s-c
    Us,Vs=sigma*u-lam,sigma*(v-lam)
    Ut,Vt=-tau*u-lam*D,tau*(lam*C-v)
    used_roots=[]
    def sup(U,V,kind):
        U,V=I(U),I(V)
        if kind=='o':
            top=(U.sq()+V.sq()).hi
            n=sqrt_upper(top)
            used_roots.append({'squared_norm_upper':str(top),
                               'strict_norm_upper':str(n)})
            return -U-R*n
        a,b=ends[kind]
        return U*a+V*b
    val=xx-F('.09')*(C-1)+lam*(1+C)+(sigma-tau)*label_constant
    val=val+sup(Us,Vs,source)+sup(Ut,Vt,target)
    gt(name+' endpoint '+x,val,gamma)
    den=10**8; num=val.lo.numerator*den//val.lo.denominator
    endpoint_rows.append({'case':name,'sigma':sigma,'tau':tau,
                          'lambda':str(lam),'source':source,'target':target,
                          'angle':x,'strict_cost_lower':str(F(num,den)),
                          'lower_numerator_over_1e8':num,'norm_bounds':used_roots})

for target in ('a','b'):
    for x in ('.35','1.2'): endpoint('++ endpoint '+target,1,1,'.39','a',target,x)
for x in ('1.2','quarter'): endpoint('++ circle',1,1,'.39','a','o',x)
for x in ('.35','.6'): endpoint('+- first',1,-1,'.55','o','b',x)
for x in ('.6','.8'): endpoint('+- middle',1,-1,'.43','a','b',x)
for target in ('a','b'): endpoint('+- last '+target,1,-1,'.34','a',target,'.8')
for target in ('a','b'): endpoint('-- last '+target,-1,-1,'.34','o',target,'.95')
for x in ('1','1.3'): endpoint('-+ first',-1,1,'.4','o','a',x)
for x in ('1.3','1.5543'): endpoint('-+ last',-1,1,'.365','b','o',x)

# The single varying-multiplier polynomial, rebuilt from its hand formula.
lam=[F('.734'),F('-.4')]
A=add(scale(lam,1+a1.lo-b1.hi),[F('-.09')])
B=add(scale(lam,1-a1.hi-b1.hi),[F('-.09')])
T=add([F('.09')+u*(1+a1.lo)+v*b1.lo-gamma,F(1)],
      scale(lam,2),mul(A,trigpoly(6,False)),mul(B,trigpoly(5,True)))
N2=add(mul(add(lam,[u]),add(lam,[u])),
       mul(add(lam,[-v]),add(lam,[-v])))
P=add(mul(T,T),scale(N2,-2*Q))
printed=[6008661,4521736,3269000,2241201,1427808,817238,397075,
         154297,75489,147054,355411,687182,1129359,1669462,2295674]
bb=bernstein(P,F('.6'),F('.95'))
assert len(P)==len(bb)==len(printed)==15
for j,(b,n) in enumerate(zip(bb,printed)):
    gt('varying polynomial Bernstein '+str(j),b,F(n,10**8))
gt('varying polynomial cosine coefficient positive',
   F('.354')*(1+a1.lo-b1.hi)-F('.09'))
gt('varying polynomial sine coefficient negative',a1.lo+b1.lo,1)
gt('cosine lower polynomial positive',1-F('.95')**2/2-F('.95')**6/720)
gt('sine upper polynomial below one',1,F('.95')+F('.95')**5/120)
Tfloor=F('.6')+2*F('.354')+u*(1+a1.lo)+v*b1.lo-gamma+F('.494')*(1-a1.hi-b1.hi)
gt('varying polynomial T positive',Tfloor,F('.278'))

result={'status':'PASS','scope':'Whole physical high/high frame-pair entry >.9099',
        'strict_comparisons':len(checks),'endpoint_rows':endpoint_rows,
        'polynomial':{'interval':['.6','.95'],'degree':14,
                      'lower_numerators_over_1e8':printed,
                      'coefficients':[str(x) for x in P],
                      'exact_bernstein':[str(x) for x in bb],
                      'T_lower_bound':str(Tfloor)},
        'checks':checks}
print(json.dumps(result,indent=2))
