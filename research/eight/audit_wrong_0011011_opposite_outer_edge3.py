"""Independent audit of the whole edge-3 outer/outer opposite-sign row.

The author replays are isolated and compared byte-for-byte.  Additional
arithmetic uses a separately written rational interval implementation with
binary square-root brackets; it does not import either author checker.
The continuous coverage review is in the companion audit manuscript.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
from math import isqrt
import json, subprocess, tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
P = HERE if (HERE/'verify_wrong_0011011_edge3_opposite_axes12_hand.py').exists() else ROOT/'proof_integration'
bindings = {}
replays = []
for axes, count in [('12',108),('34',83)]:
    stem = 'wrong_0011011_edge3_opposite_axes'+axes+'_hand'
    script = P/('verify_'+stem+'.py')
    report = P/(stem+'_arithmetic.json')
    note = P/('WRONG_0011011_EDGE3_OPPOSITE_AXES'+axes+'_HAND_PROOF.md')
    with tempfile.TemporaryDirectory(prefix='opposite_outer_independent_') as temp:
        copied = Path(temp)/script.name
        copied.write_bytes(script.read_bytes())
        run = subprocess.run(['python',str(copied)],capture_output=True,check=True,text=True)
        raw = (Path(temp)/report.name).read_bytes()
    assert raw == report.read_bytes()
    obj = json.loads(raw)
    assert obj['status']=='PASS' and len(obj['checks'])==count
    assert all(F(z['strict_reserve'])>0 for z in obj['checks'])
    replays.append({'axes':axes,'fixed_comparisons':count,'byte_identical':True})
    bindings.update({f.name:sha256(f.read_bytes()).hexdigest() for f in [script,report,note]})

labels_path = HERE/'wrong_0011011_labels.json'
if not labels_path.exists(): labels_path = ROOT/'proof_integration/wrong_0011011_labels.json'
labels = json.loads(labels_path.read_text())
assert labels['independent_roles']['3']['O-']==[1670,0,242322,-91744,-95769]
assert labels['independent_roles']['4']['O+']==[3965,0,385510,-149748,-189442]
assert F(labels['gamma'])==F('17953/20000')
bindings[labels_path.name]=sha256(labels_path.read_bytes()).hexdigest()

class R:
    def __init__(self,lo,hi=None):
        if isinstance(lo,R): self.lo,self.hi=lo.lo,lo.hi
        else: self.lo,self.hi=F(lo),F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(a,b):
        b=R(b);return R(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return R(-a.hi,-a.lo)
    def __sub__(a,b):return a+-R(b)
    def __rsub__(a,b):return R(b)+-a
    def __mul__(a,b):
        b=R(b);v=[i*j for i in [a.lo,a.hi] for j in [b.lo,b.hi]]
        return R(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=R(b);assert b.lo*b.hi>0
        return a*R(1/b.hi,1/b.lo)
    def __rtruediv__(a,b):return R(b)/a
    def __pow__(a,n):
        assert isinstance(n,int) and n>=0
        if not n:return R(1)
        ends=[a.lo**n,a.hi**n]
        return R(0 if n%2==0 and a.lo<=0<=a.hi else min(ends),max(ends))
    def root(a):
        assert a.lo>0
        den=1<<100
        n=isqrt(a.lo.numerator*den*den//a.lo.denominator)
        m=isqrt(a.hi.numerator*den*den//a.hi.denominator)+1
        lo,hi=F(n,den),F(m,den)
        assert lo*lo<=a.lo and hi*hi>a.hi
        return R(lo,hi)

Q=R('9789/2500');checks=[]
def positive(name,value):
    value=R(value);assert value.lo>0,(name,str(value.lo))
    compact=F(value.lo.numerator*10**24//value.lo.denominator,10**24)
    assert 0<compact<=value.lo
    checks.append({'name':name,'strict_reserve':str(compact)})
def ab(y):
    y=R(y);u=(Q-(y+F(1,2))**2).root();return u-F(1,2),u
def derivatives(name,y):
    y=R(y);a,u=ab(y);r=(y+F(1,2))/u
    c,p,s,h=map(F,{'T':('.01670','2.42322','-.91744','-.95769'),
                    'L':('.03965','3.85510','-1.49748','-1.89442')}[name])
    value=c+p*y+s*y**2+h*a*y
    first=p+2*s*y+h*(a-y*r)
    second=2*s-2*h*r-h*y*Q/u**3
    third=-3*h*Q*(Q-(y+F(1,2))/2)/u**5
    return value,first,second,third

# All six implicit critical-curve brackets and third-derivative signs are
# rebuilt from the defining circle equations with independent square bounds.
def S(B):
    return (R(B)+F(1,2))**2+1/derivatives('L',B)[1]**2
def q_of(b):return Q+1-2*ab(b)[1]
for l,h,L,H in [('0','.1','.0309','.0458'),('.1','.2','.0457','.0628'),
                 ('.2','.3','.0627','.0819'),('.3','.4','.0818','.1028'),
                 ('.4','.5','.1027','.1254'),('.5','.6','.1253','.1499')]:
    positive('critical lower bracket '+l,q_of(l)-S(L))
    positive('critical upper bracket '+h,S(H)-q_of(h))
    b,B=R(l,h),R(L,H);a,u=ab(b);r=(b+F(1,2))/u
    rp=Q/u**3;rpp=3*Q*(b+F(1,2))/u**5;q=Q+1-2*u;z=B+F(1,2)
    _,lp,lpp,lppp=derivatives('L',B);v=1/lp
    f1pp=Q/(Q+1)*(rp/u**2+2*r**2/u**3)-2*(Q-1)/(Q+1)*(rp/q**2-4*r**2/q**3)
    e=rpp-6*r*rp/q-3*r*rp/v**2+8*r**3/q**2+4*r**3/(q*v**2)+3*r**3/v**4
    partial0=f1pp-z*e/(q*v)-derivatives('T',l)[3]
    partial1=-rp/v**3+3*r**2/v**5
    partial2=-3*z*r/v**5
    partial3=1/v**3+3*z**2/v**5-lppp
    slope=r/(z-lpp*v**3)
    upper=partial0+3*partial1*slope+3*partial2*slope**2+partial3*slope**3
    positive('reduced third derivative negative '+l+':'+h,-upper)

# The low interior rectangle has a positive definite Hessian after a
# .01 identity shift. These are the exact stated eigenvalue reserves.
for cbb,cross in [('1.16','.515'),('.85','.545'),('.51','.561'),('.40','.526'),('.21','.526')]:
    positive('shifted Hessian determinant '+cbb,
             (F('1.5')-F('.01'))*(F(cbb)-F('.01'))-F(cross)**2)

def atan_sum(x,terms):
    x=F(x)
    return sum((F((-1)**i,2*i+1)*x**(2*i+1) for i in range(terms)),F(0))
halfpi=R(8*atan_sum(F(1,5),30)-2*atan_sum(F(1,239),29),
         8*atan_sum(F(1,5),29)-2*atan_sum(F(1,239),30))
def angle(t):
    t=R(t);assert 0<t.lo<=t.hi<F('.31')
    return R(atan_sum(t.lo,36),atan_sum(t.hi,35))

# Independently evaluate both low nonaligned contact test poses and the
# critical-curve reference, including their actual geometric angles.
b,B=R('.05878084'),R('.33400286');A,u=ab(B);z=b+F(1,2)
q=Q+1-2*u;v=(q-z**2).root();w=A-F(1,2);y=B+F(1,2)
x=angle((w*v-y*z)/(w*z+y*v))
cost=halfpi-x-derivatives('T',b)[0]-derivatives('L',B)[0]
positive('axis1 low reference cost',cost-F('.8977764'))

d=(Q/2).root()-F(1,2);b=R('.00542853');a,u=ab(b)
z=d-F(1,2);q=Q+1-2*u;v=(q-z**2).root();w=a-F(1,2);y=b+F(1,2)
x=angle((y*v-w*z)/(y*z+w*v))
cost=halfpi+x-derivatives('T',b)[0]-derivatives('L',d)[0]
positive('axis2 diagonal reference cost',cost-F('.8977735'))

b=R('.495');B=R('.12421535815','.12421535816');a,u=ab(b)
z=B+F(1,2);q=Q+1-2*u;v=(q-z**2).root();w=a-F(1,2);y=b+F(1,2)
x=angle((w*v-y*z)/(w*z+y*v))
cost=halfpi-x-derivatives('T',b)[0]-derivatives('L',B)[0]
positive('axis3 critical reference cost',cost-F('.89779'))

# Analytic completions and the two primary-label product inequalities.
positive('axis1 rectangle completion',F('.8977764')-2*F('.000001')**2/F('.02')-F('.89777'))
positive('axis2 diagonal completion',F('.8977735')-F('.000001')**2/2-F('.89777'))
positive('axis3 reduced completion',F('.89779')-F('.0001')**2/F('.12')-F('.89777'))
positive('primary slope convexity numerator',F('.95769')*F('3.9')-F('1.238845')*F('1.4')-2)
positive('primary slope square completion',F('.00726')-F('.016')**2/F('1.4'))
positive('axis2 lower angular product',(F('.624')/F('.861'))**2*(Q-F('.915')**2)-1)
positive('axis4 lower angular product',F('.76')**2*(Q-F('.915')**2)-1)
qmax=Q-2*ab('.2')[0]
positive('axis4 upper low-primary product',1-F('.85')**2*(qmax-(d-F(1,2))**2))
positive('axis4 upper high-primary product',1-F('1.051')**2*(qmax-F('.36')))
positive('strict table reserve',F('.89777')-F(labels['gamma']))

out={'status':'PASS','scope':'Whole 0011011 edge3 OO(-,+), all four retained axes and both angle halves; reflected edge5 follows from the stated role symmetry',
     'author_replays':replays,'independent_fixed_comparisons':len(checks),
     'independent_checks':checks,'label_binding':'Exact role3 O- and role4 O+ coefficients match the shared rational table',
     'sha256':bindings}
(HERE/'wrong_0011011_opposite_outer_edge3_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'replayed_comparisons':191,'independent_comparisons':len(checks)},indent=2))
