"""Fixed rational transcription of the complete L/L hand proof.

The five rows and all domains are fixed in the manuscript.  No optimizer,
sampling, or adaptive subdivision is used.
"""
from fractions import Fraction as F
from math import factorial, comb
from pathlib import Path
import json

def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return p
def add(*pp):
    ans=[F(0)]*max(map(len,pp))
    for p in pp:
        for i,c in enumerate(p):ans[i]+=c
    return trim(ans)
def scale(p,c):return trim([c*v for v in p])
def mul(p,q):
    ans=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):ans[i+j]+=a*b
    return trim(ans)
def bern(p,a,b):
    n=len(p)-1
    power=[sum(p[j]*comb(j,k)*a**(j-k)*(b-a)**k for j in range(k,n+1)) for k in range(n+1)]
    return [sum(power[j]*F(comb(k,j),comb(n,j)) for j in range(k+1)) for k in range(n+1)]

SL=[F(0)]*8;SU=[F(0)]*6;CL=[F(0)]*7;CU=[F(0)]*9
for j in range(4):SL[2*j+1]=F((-1)**j,factorial(2*j+1))
for j in range(3):SU[2*j+1]=F((-1)**j,factorial(2*j+1))
for j in range(4):CL[2*j]=F((-1)**j,factorial(2*j))
for j in range(5):CU[2*j]=F((-1)**j,factorial(2*j))
X=[F(0),F(1)]
Q=F(9789,2500);u=F('.403875');v=F('1.089065');beta=F('.18');goal=F('.91')
a0lo,a0hi=F('1.41457'),F('1.41458')
alo,ahi=F('1.29874'),F('1.29875');blo,bhi=alo/4,ahi/4
Llo,Lhi=F('.30681'),F('.30683')
polys={};domains={};checks=[]
def check(name,left,right=F(0)):
    assert left>right,(name,left,right)
    checks.append({'name':name,'margin':str(left-right)})
def value(p,x):return sum(c*x**i for i,c in enumerate(p))
S3=[F(0),F(1),F(0),-F(1,6)]
C4=[F(1),F(0),-F(1,2),F(0),F(1,24)]
pi=F('3.14159')
check('a0 lower',Q-F(1,4),(a0lo+F('.5'))**2)
check('a0 upper',(a0hi+F('.5'))**2,Q-F(1,4))
def radius_poly(a):return F(17,16)*a*a+F(5,4)*a+F('.5')-Q
check('a1 lower',-radius_poly(alo))
check('a1 upper',radius_poly(ahi))
check('slope ratio upper',F('.46')*(alo+F('.5')),bhi+F('.5'))
check('marker increasing',v-u)
check('marker at most b',1,v-u/(2*a0hi+1))
check('last marker lower',u*(alo-a0hi)+v*blo,Llo)
check('last marker upper',Lhi,u*(ahi-a0lo)+v*bhi)
check('support cusp bound',F('1.42')**2,F(2))
check('large frame cost',pi/2-2*Lhi-beta*F('.21'),goal)
check('positive source with lambda .945',Llo-F('.945')*bhi,-F('.00002'))
check('positive source with lambda .96',Llo-F('.96')*bhi,-F('.013'))
check('negative source with lambda .96',-F('.04')*bhi,-F('.013'))
for name,lam,eps,cut in [('plus',F('.945'),F('.00002'),F('.96')),('minus',F(1),F(0),F('1.1'))]:
    constant=F('.09')+u*a0lo+(u+v+lam)/2-goal-eps
    T=add(X,[constant],scale(S3,lam-F('.09')),scale(C4,-F('.09')))
    N=add([u*u+v*v+lam*lam],scale(SU,2*lam*u),scale(CL,-2*lam*v))
    check(name+' T positive',constant-F('.09'))
    check(name+' target endpoint derivative',v,F('.46')*u+lam*(F('.46')*value(SU,cut)+value(C4,cut)))
    check(name+' target derivative stays decreasing',value(SL,cut),F('.46')*value(CU,cut))
    polys[name+'_circle']=add(mul(T,T),scale(N,-Q));domains[name+'_circle']=[(F(0),cut)]
    d=(lam-beta)/2
    P=add(X,[-eps-Lhi+(lam+beta)/2-goal],scale(CL,d+lam*blo),scale(SU,d-lam*ahi))
    polys[name+'_endpoint']=P;domains[name+'_endpoint']=[(cut,F(11,7))]

lam=F('.96');eps=F('.013');d=(lam-beta)/2
polys['negative_target_axial']=add(X,[-eps+(lam+beta)/2-goal],scale(CL,d),scale(SU,d-lam*a0hi))
polys['negative_target_axial'].append(F(0))  # degree-six polynomial, degree-seven Bernstein basis
domains['negative_target_axial']=[(F(0),F(11,7))]
check('negative-target last endpoint cosine coefficient',d-lam*bhi)
check('negative-target last endpoint increasing',1-(d-lam*blo)-(lam*ahi-d))
check('negative-target last endpoint cost at zero',-eps+Llo+lam-lam*bhi,goal)

cut=F('1.3');s,c=value(SL,cut),value(CL,cut)
check('primary positive-target impossible at zero',1+alo-a0hi)
check('primary positive-target impossible at 1.3',F('.5')+(alo+F('.5'))*c+F('.5')*s-a0hi)
lam=F('.9');d=(lam-beta)/2
check('primary positive-target source endpoint',v,(u+lam)*F('.46'))
check('primary positive-target target endpoint',v,u*F('.46')+lam)
P0=-2*Lhi+(lam+beta)/2-lam*ahi
check('primary positive-target cost at 1.3',cut+P0+(d+lam*alo)*c+(d+lam*blo)*s,goal)
check('primary positive-target cost at pi/2',pi/2+P0+d+lam*blo,goal)
check('primary negative-target large frame',cut-Lhi-beta*F('.21'),goal)
lam=F(5,4);d=(lam-beta)/2
check('primary negative-target source endpoint',v,(u+lam)*F('.46'))
check('primary negative-target last sine coefficient',d-lam*bhi)
for name,C,A,B in [
    ('axial',-Lhi+(lam+beta)/2-lam*ahi,d+lam*a0lo,d),
    ('last',(lam+beta)/2-lam*ahi,d+lam*alo,d-lam*bhi),
]:
    check('primary negative-target '+name+' at zero',C+A,goal)
    check('primary negative-target '+name+' at 1.3',cut+C+A*c+B*s,goal)

expected={
'plus_circle':[548963,881234,1045788,1108067,1109559,1060273,933679,665095,154640],
'plus_endpoint':[87880,36707,21718,62261,175975,377007,673722],
'minus_circle':[1543096,1962322,2150549,2208476,2188950,2081340,1802756,1198887,57531],
'minus_endpoint':[139832,92446,78059,105371,182135,314616,506922],
'negative_target_axial':[370000,441843,284387,76501,25367,329670,1131139,2454431],
}

rows=[]
for name,p in polys.items():
    for a,b in domains[name]:
        coeffs=bern(p,a,b);den=10**7;ints=[(c.numerator*den)//c.denominator for c in coeffs]
        assert ints==expected[name],(name,ints)
        for i,(co,lower) in enumerate(zip(coeffs,ints)):
            assert co>=F(lower,den)>0,(name,i)
        rows.append({'name':name,'interval':[str(a),str(b)],'degree':len(p)-1,'denominator':den,'lower_numerators':ints})
out={'status':'PASS','scope':'all L/L signs, full relative frames, both source axes and reflected target axes','strict_scalar_comparisons':len(checks),'positive_bernstein_coefficients':sum(len(r['lower_numerators']) for r in rows),'rows':rows,'comparisons':checks,'polynomials':{k:[str(x) for x in v] for k,v in polys.items()}}
Path(__file__).with_name('low_low_whole_pair_hand_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ('status','strict_scalar_comparisons','positive_bernstein_coefficients','rows')},indent=2))
