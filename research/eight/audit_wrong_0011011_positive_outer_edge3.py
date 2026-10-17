"""Independent replay and rational comparisons for the final OO(++) row."""
from fractions import Fraction as F
from math import isqrt, factorial
from pathlib import Path
from hashlib import sha256
import json,subprocess,tempfile

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
name='verify_wrong_0011011_edge3_positive_outer_pair.js'
P=HERE if (HERE/name).exists() else ROOT/'m5_agent/hand_conversion'
checker=P/name;note=P/'WRONG_0011011_EDGE3_POSITIVE_OUTER_PAIR_HAND_PROOF.md'
report=P/'wrong_0011011_edge3_positive_outer_pair_arithmetic.json'
with tempfile.TemporaryDirectory(prefix='positive_outer_review_') as temp:
    cp=Path(temp)/name;cp.write_bytes(checker.read_bytes())
    raw=subprocess.run(['node',str(cp)],capture_output=True,check=True).stdout
assert raw==report.read_bytes()
obj=json.loads(raw)
assert obj['status']=='PASS' and obj['comparison_count']==147
assert all(z['pass'] and F(z['lower'])>F(z['threshold']) for z in obj['checks'])
labels_path=HERE/'wrong_0011011_labels.json'
if not labels_path.exists():labels_path=ROOT/'proof_integration/wrong_0011011_labels.json'
labels=json.loads(labels_path.read_text())
assert labels['independent_roles']['3']['O+']==[0,-1025,16031,0,63457]
assert labels['independent_roles']['4']['O+']==[3965,0,385510,-149748,-189442]

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
        b=I(b);assert b.lo>0
        return a*I(1/b.hi,1/b.lo)
    def __rtruediv__(a,b):return I(b)/a
    def __pow__(a,n):
        assert n>=0
        z=[a.lo**n,a.hi**n]
        return I(0 if n%2==0 and a.lo<=0<=a.hi else min(z),max(z))
    def sqrt(a):
        assert a.lo>0
        den=1<<110
        n=isqrt(a.lo.numerator*den*den//a.lo.denominator)
        m=isqrt(a.hi.numerator*den*den//a.hi.denominator)+1
        l,h=F(n,den),F(m,den)
        assert l*l<=a.lo and h*h>a.hi
        return I(l,h)

Q=I('9789/2500');checks=[]
def gt(name,x):
    x=I(x);assert x.lo>0,name
    lower=F(x.lo.numerator*10**24//x.lo.denominator,10**24)
    assert 0<lower<=x.lo
    checks.append({'name':name,'strict_reserve':str(lower)})
def atan_sum(x,n):
    x=F(x)
    return sum((F((-1)**j,2*j+1)*x**(2*j+1) for j in range(n)),F(0))
hp=I(8*atan_sum(F(1,5),30)-2*atan_sum(F(1,239),29),
     8*atan_sum(F(1,5),29)-2*atan_sum(F(1,239),30))
def trig_point(x):
    x=F(x)
    def partial(kind,last):
        return sum((F((-1)**j,factorial(2*j+kind))*x**(2*j+kind) for j in range(last+1)),F(0))
    return I(partial(1,15),partial(1,16)),I(partial(0,15),partial(0,16))
def phi_trig(phi):
    if phi=='lo':
        s,c=trig_point('.7');return hp-F('.7'),c,s
    s,c=trig_point(phi);return I(phi),s,c
def outer(b):
    b=I(b);u=(Q-(b+F(1,2))**2).sqrt();return u-F(1,2),u
def R(b):
    b=I(b);a,u=outer(b)
    return F('-.01025')*a+F('.16031')*b+F('.63457')*a*b
def RD(b):
    b=I(b);a,u=outer(b);r=(b+F(1,2))/u
    return F('.01025')*r+F('.16031')+F('.63457')*(a-b*r)
def J(b):
    b=I(b);a,u=outer(b)
    return F('.03965')+F('3.85510')*b-F('1.49748')*b**2-F('1.89442')*a*b
def JD(b):
    b=I(b);a,u=outer(b);r=(b+F(1,2))/u
    return F('3.85510')-F('2.99496')*b-F('1.89442')*(a-b*r)
d=(Q/2).sqrt()-F(1,2);a0=outer(0)[0];R0=R(0)

# Reconstruct the target tangent table, not its stored endpoint values.
for row in obj['tangents']:
    q,k,b=F(row['q']),F(row['k']),F(row['b'])
    gt('target tangent slope '+row['b'],q-JD(b))
    gt('target tangent intercept '+row['b'],k-(J(b)-b*JD(b)))
    for endpoint in [row['l'],row['h']]:
        phi,s,c=phi_trig(endpoint);g=F('.98')
        value=phi+R0-k+(g+q)/2+g*s-Q.sqrt()*(g*g+q*q-2*g*q*c).sqrt()
        gt('short support endpoint '+row['b']+':'+endpoint,value-F('.9013'))

# Each contact-derivative rectangle is justified by separate concavity.
# These fresh sixteen corners therefore check the entire displayed table.
for lo,hi,blo,bhi in obj['cutRows']:
    for endpoint in [lo,hi]:
        phi,s,c=phi_trig(endpoint)
        for B in [blo,bhi]:
            a,u=outer(B);r=(I(B)+F(1,2))/u
            value=RD('.35')*(r*s+c)-JD(B)
            gt('contact corner '+str((lo,hi,endpoint,B)),value)

gt('global source chord',R(d)-R0-F('.736')*d)
gt('short source chord',R('.35')-R0-F('.98')*F('.35'))
gt('source derivative contact concavity',3*F('1.89442')-F('1.061')*F('2.15'))

# Reconstruct the two closest endpoints from the circle equations.
gt('aligned target-diagonal endpoint',hp+R(1-d)-J(d)-F('.8977886'))
phi,s,c=phi_trig('lo');z=F(1,2)-d+s;y=(Q-z*z).sqrt()
B=y*s-z*c-F(1,2)
gt('source-diagonal first endpoint',phi+R(d)-J(B)-F('.8977888'))
gt('double-diagonal endpoint',F('1.014')+R(d)-J(d)-F('.8984'))

gt('source-diagonal concavity',F('1.6')*F('.93')**2-F('1.176')*F('1.4')*F('.73')**2)
s,c=trig_point('1.014')
gt('target-diagonal concavity',F('.434')*(F('1.399')*s)**2-F('1.061')*F('.4'))
gt('upper source-coordinate concavity',F('.399')-F('.585')*F('.11')*F('1.02')**2)
gt('upper zero-source cost concavity',2*F('.908')**2-F('1.176')*F('1.32'))
gt('lower axis3 first source interval',F('.639')+F('1.176')*(F('.261')*F('.764')-F('.645')))
gt('lower axis3 second source interval',F('.170')+F('1.176')*(F('.668')*F('.764')-F('.645')))
gt('lower axis3 strong-convexity completion',F('.9439')-F('.052')**2/F('.88')-F('.9408'))
gt('later angle direct bound',F('1.676')+R0-J(d)-F('.8979'))
gt('strict declared table reserve',F('.89777')-F(labels['gamma']))

deps=[P/'WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md',
      P/'WRONG_0011011_EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md']
out={'status':'PASS','scope':'Whole 0011011 edge3 OO(++), four retained axes and both angle halves; reflected edge5 follows from the stated role symmetry',
     'author_replay_byte_identical':True,'author_fixed_comparisons':147,
     'independent_fixed_comparisons':len(checks),'independent_checks':checks,
     'dependencies_reviewed':'The two imported target-only facts have the same Q, label and full angle scope; neither depends on source radius.',
     'sha256':{p.name:sha256(p.read_bytes()).hexdigest() for p in [note,checker,report,labels_path]+deps}}
(HERE/'wrong_0011011_positive_outer_edge3_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','author_comparisons':147,'independent_comparisons':len(checks)},indent=2))
