"""Fixed exact comparisons in WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md.

This script has no optimizer, sampled domain, or adaptive subdivision.
Its elementary core endpoint and convexity arguments are in the paper.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

checks=[]
def check(name,x):
    x=F(x)
    assert x>0,(name,x)
    checks.append({'name':name,'positive_reserve':str(x)})

rl,rh=F('1.41421356237'),F('1.41421356238')
check('sqrt2 lower',2-rl*rl)
check('sqrt2 upper',rh*rh-2)
vl,vh=3-2*rh,3-2*rl
check('atan side minimum reserve',vl-vh**3/3-(1+vh)/7-F(1,400))
dl,dh=F('.55892556'),F('.55892557')
check('diagonal lower',F(1,2)+rl/24-dl)
check('diagonal upper',dh-F(1,2)-rh/24)
check('diagonal above .55',dl-F('.55'))
check('corner second derivative numerator',3-F(7,6))
check('nonaffine correction negative',F('.05334')/4-F('.34492')/30)
check('side radius squared below .64',F(16,25)-F(7,12)**2-F(1,4))
check('corner radius squared below .64',F(16,25)-F(1,2)-rh/12-F(1,144))
x=F(27,20)
coslo=sum((-1)**k*x**(2*k)/factorial(2*k) for k in range(6))
check('gap 1.35 cannot separate incircles',1-F(32,25)*(1-coslo))

# pi>3.14 follows, for example, from Machin's formula and these four
# fixed alternating arctangent partial sums. pi<355/113 follows by the
# matching upper bound. No decimal pi value is an input.
def atan_terms(x,n):
    return sum((-1)**k*x**(2*k+1)/(2*k+1) for k in range(n))
pi_lo=16*atan_terms(F(1,5),6)-4*atan_terms(F(1,239),3)
pi_hi=16*atan_terms(F(1,5),7)-4*atan_terms(F(1,239),2)
check('pi above 3.14',pi_lo-F('3.14'))
check('pi below 355/113',F(355,113)-pi_hi)
check('two-zero sign inference',F('.82')-F(355,452))
check('exceptional quarter angle',pi_lo/2-F('.7')-F('.87'))

core={
 (0,1):(F('.00125'),F('1.03981')),
 (0,-1):(F('.19911'),F('.63607')),
 (1,1):(F('.19555'),F('.63132')),
 (1,-1):(F('.19555'),F('.63132')),
 (3,1):(F('-.01449'),F('1.04240')),
 (4,1):(F('.04970'),F('.94831')),
 (4,-1):(F('.16823'),F('.62312')),
}
ranges={}
for (i,sign),(c,g) in core.items():
    check(f'role {i} sign {sign} slope positive',g)
    check(f'role {i} sign {sign} slope at most 8/7',F(8,7)-g)
    lo,hi=-c,F(355,452)-c-g*dl
    if sign==-1:lo,hi=-hi,-lo
    ranges[i,sign]=(lo,hi)
ce=F('.22042')-F('.34492')*F(7,12)
lo,hi=-ce,F(355,452)-ce-F('.98439')*dl+F('.05334')*dh**2
ranges[3,-1]=(-hi,-lo)
check('nonaffine core slope positive',F('.98439'))
check('nonaffine core slope at most 8/7',F(8,7)-F('.98439'))
for i in range(7):
    for sign in (1,-1):
        if (i,sign) not in ranges:
            low,high=ranges[(2-i)%7,-sign]
            ranges[i,sign]=(-high,-low)
rows=[(0,1,1,'.95147'),(0,1,-1,'.91004'),
      (2,-1,1,'1.36323'),(2,-1,-1,'1.11609'),
      (3,-1,-1,'1.06188'),(3,-1,1,'1.28108'),
      (3,1,-1,'1.02374'),(3,1,1,'1.08303'),
      (4,1,1,'.97610'),(4,1,-1,'.93867')]
for e,s,t,bound in rows:
    lower=F('1.35')-ranges[e,s][1]+ranges[(e+1)%7,t][0]
    if (e,s,t)==(3,1,-1):
        lower=pi_lo/2-F('.7')-F('.01449')+F('.16823')
    check(f'edge {e} signs {s},{t} printed bound',lower-F(bound))
    check(f'edge {e} signs {s},{t} above .91',F(bound)-F('.91'))
check('whole core bound exceeds wrong-word gamma',F('.91')-F(17953,20000))
result={'status':'PASS','strict_comparisons':len(checks),
        'scope':'All core/core cases only; no outer or mixed claim.',
        'checks':checks}
Path(__file__).with_name('wrong_0011011_core_core_hand_arithmetic.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','strict_comparisons':len(checks)}))
