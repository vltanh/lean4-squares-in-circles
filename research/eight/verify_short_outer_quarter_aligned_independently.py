"""Independent Fraction arithmetic for the six 0010111 aligned OO regimes.

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
Q=I('9789/2500');d=(Q/2).sqrt()-F('.5')
a0=(Q-F('.25')).sqrt()-F('.5');b0=1-d
def a(b):return (Q-(I(b)+F('.5'))**2).sqrt()-F('.5')
def r(b):return (I(b)+F('.5'))/(a(b)+F('.5'))
def atan_sum(x,n):
    x=F(x);return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
pi2=I(8*atan_sum('1/5',16)-2*atan_sum('1/239',5),
      8*atan_sum('1/5',15)-2*atan_sum('1/239',4))
base=Path(__file__).resolve().parent.parent/'global_attack'/'hand_conversion'
labels=json.loads((base/'short_hand_labels.json').read_text())
rows=[list(map(F,x)) for x in [
    ('-.53489','.33147','1.1336','-.09133','.88074'),
    ('-.53062','.20967','.83048','-.19335','.76744'),
    ('-.20704','.21826','.83472','0','.94766')]]
binding=[]
for j,e in enumerate((2,4,6)):
    key='n' if e in (2,4) else 'p'
    cs,ps,qs=[F(v,100000) for v in labels[e]['O'][key]]
    ct,pt,qt=[F(v,100000) for v in labels[(e+1)%7]['O'][key]]
    # Signed affine labels have c+p*a+sigma*q*b.
    row=[cs-ct,-pt,qt,-ps,qs] if e in (2,4) else [cs-ct,ps,qs,pt,qt]
    assert row==rows[j]
    binding.append({'edge':e,'normalized_source_f':[str(v) for v in row]})
gt('inactive e diagonal-zero infeasible',1-F('.9')-F('1.415')*F('.06'))
for j,row in enumerate(rows):
    cc,p,q,P,t=row
    pe,qe,Pe,te=-P,t,-p,q
    assert p>=0 and P<=0 and pe>=0 and Pe<=0
    gt('source f increases '+str(j),q-p)
    gt('target e increases '+str(j),te+Pe)
    assert t-P>=F('.94766') and pe+qe>=F('.94766')
    def H(B):
        B=I(B);aa=1-B;bb=a(aa)
        return pi2+cc+pe*aa-qe*bb-Pe*a(B)+te*B
    def Hp(B):
        B=I(B);aa=1-B;bb=a(aa)
        return te-pe-qe*(aa+F('.5'))/(bb+F('.5'))+Pe*r(B)
    if j==0:
        gt('aligned curvature independently',qe*Q/F('1.4')**3+Pe*Q/F('1.885')**3,1)
        v=Hp('.0517');mag=max(abs(v.lo),abs(v.hi))
        gt('aligned quadratic completion independently',H('.0517')-mag*mag/2,'.8981')
    else:
        gt('aligned monotonicity independently '+str(j),pe+qe-te)
        gt('aligned endpoint independently '+str(j),H(b0),'.8981')
    lt('aligned derivative small-B '+str(j),Hp('1/80'),0)
    gt('aligned small-B allowance independently '+str(j),H('1/80')-F('.0012'),'17953/20000')
    gt('linear target diagonal versus axial '+str(j),
       t*(a0+F('.5'))-P*F('.5')-(t-P)*(d+F('.5')))
    for lo,hi in [('0','.15'),('.15','.3')]:
        sh,ch=trig(hi)
        b=F('.5')+(F('.5')-d)*ch+(F('.5')+d)*sh
        factor=q-p*r(b)
        for x in (lo,hi):
            s,c=trig(x)
            gt('negative f diagonal speed '+str(j)+':'+lo+':'+hi+':'+x,
               factor*((d-F('.5'))*s+(d+F('.5'))*c),1)
    for B,lower in [('0','-.02'),('1/80','0')]:
        bb=F(B);aa=1-bb
        dx=1-(pe+qe*(F('1.5')-bb)/(a(aa)+F('.5')))*(a(bb)-F('.5'))
        gt('positive e initial derivative '+str(j)+':'+B,dx,lower)
s3,c3=trig('.3');s03,c03=trig('.03');s1,c1=trig('.1')
gt('negative f interior speed independently',
   F('.94766')*F('1.399')*(1-s3/(F('.85')*c3+F('1.399')*s3)),1)
gt('positive f interior speed independently',1-F('1.82')*(1-F('.895')/F('1.4')))
gt('negative e active speed independently',F('.94766')*(F('1.399')*c03-F('.5')*s03),1)
gt('negative e diagonal speed independently',
   (F('.83048')*F('1.86')-F('.33147')*F('.66'))*(1-s03/(F('1.86')*c03)),1)
lt('positive e speed product decreases independently',
   -F('.767')*F('3.9')*F('.88')**2/F('1.4')**3+F('1.3')*F('.5'),0)
import hashlib,subprocess
names=['SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md',
       'verify_short_outer_quarter_aligned_hand.js',
       'short_outer_quarter_aligned_hand_arithmetic.json','short_hand_labels.json']
hashes={n:hashlib.sha256((base/n).read_bytes()).hexdigest() for n in names}
replay=subprocess.run(['node',str(base/names[1])],capture_output=True,check=True).stdout
assert replay==(base/names[2]).read_bytes()
assert len(json.loads(replay)['checks'])==80
result={'status':'PASS','scope':'Six stated near-aligned OO quarter-one regimes only',
        'independent_fraction_comparisons':len(checks),'source_replay_comparisons':80,
        'source_replay_byte_identical':True,'binding':binding,'hashes':hashes,'checks':checks}
out=json.dumps(result,indent=2)+'\n'
Path(__file__).with_name('short_outer_quarter_aligned_independent_arithmetic.json').write_text(out)
print(out,end='')
