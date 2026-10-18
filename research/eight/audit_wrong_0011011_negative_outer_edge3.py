"""Independent replay and rational checks of the repaired whole negative OO row."""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from hashlib import sha256
import json,subprocess,tempfile

HERE=Path(__file__).resolve().parent;ROOT=Path(__file__).resolve().parents[2]
name='verify_wrong_0011011_edge3_negative_outer_quarter_hand.py'
P=HERE if (HERE/name).exists() else ROOT/'proof_integration'
checker=P/name;note=P/'WRONG_0011011_EDGE3_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md'
report=P/'wrong_0011011_edge3_negative_outer_quarter_hand_arithmetic.json'
with tempfile.TemporaryDirectory(prefix='negative_outer_review_') as d:
 cp=Path(d)/name;cp.write_bytes(checker.read_bytes())
 raw=subprocess.run(['python',str(cp)],check=True,capture_output=True).stdout
 assert raw==report.read_bytes()
data=json.loads(raw);assert data['comparison_count']==134
assert all(F(c['strict_reserve'])>0 for c in data['checks'])
labelpath=HERE/'wrong_0011011_labels.json'
if not labelpath.exists():labelpath=ROOT/'proof_integration/wrong_0011011_labels.json'
labels=json.loads(labelpath.read_text())
assert labels['independent_roles']['3']['O-']==[1670,0,242322,-91744,-95769]
assert labels['independent_roles']['4']['O-']==[0,-2112,29090,0,44642]

def root_interval(z):
 z=F(z);D=10**30;n=isqrt(z.numerator*D*D//z.denominator)
 l,h=F(n,D),F(n+1,D);assert l*l<=z<h*h;return l,h
Q=F('9789/2500');checks=[]
def positive(name,v):assert v>0,name;checks.append({'name':name,'reserve':str(v)})

# The scalar used to exclude a small-target interior minimum is
# recomputed without importing the author's interval implementation.
b=F('.394');u,_=root_interval(Q-(b+F('.5'))**2)
Tp_upper=F('2.42322')-F('1.83488')*b-F('.95769')*(u-F('.5')-b*(b+F('.5'))/u)
ratio=(Q-F('1.765'))/(F('1.765')*(Q+1-F('3.504')))-(F('.92')/F('1.752'))*F('.5')/((Q+1-F('3.53'))*F('1.077'))
positive('small-target stationary transverse derivative',ratio-Tp_upper-F('.007'))

# At B=.1 both K' and K'' increase with u; using the independent
# upper root gives an upper bound for K''+.4(K')^3.
B=F('.1');_,u=root_interval(Q-(B+F('.5'))**2)
p=F('-.02112');t=F('.44642');w=B+F('.5');r=w/u
Kp=-p*r+F('.29090')+t*(u-F('.5')-B*r)
Kpp=-2*t*r-(p+t*B)*Q/u**3
positive('large-target stationary angular curvature',-(Kpp+F('.4')*Kp**3))
positive('small-target angular-coordinate upper bound',F('1.765')-F('1.7521')-F('.224')**2/F('4.2'))
positive('primary slope lower square completion',F('.00726')-F('.016')**2/F('1.4'))
for slope,extent in [(F('.76'),F('.6')),(F('.84'),F('.7')),(F(1),F('.915'))]:
 positive('primary angular product '+str(slope),slope*slope*(Q-F('1.8')-extent*extent)-1)
positive('repaired axis1 contact derivative concavity',F('.44642')*Q-(F('.24433')+F('1.069')*F('.765'))*F('1.4')-F('.261'))
positive('strong-convexity endpoint reference',F('.8977814')-F('0.000001')**2/F('.48')-F('.89778'))
positive('zero-target six-row mean-value reserve',F('.919')-F(3,8)*F('.05')-F('.9'))
positive('diagonal-target angular decrease',1-F('.774')*(F('1.535')-F('.479')/F('1.415')))
positive('final strict comparison',F('.89777')-F('17953/20000'))

out={'status':'PASS','scope':'Repaired whole edge3 OO(--), reflected edge5(++), all four axes and both quarter halves',
 'replayed_fixed_comparisons':134,'replay_byte_identical':True,'independent_fixed_comparisons':len(checks),
 'independent_checks':checks,'correction_reviewed':'The lower/upper axis1 signs were corrected before this audit; the actual lower half includes the new zero-source endpoint argument.',
 'sha256':{x.name:sha256(x.read_bytes()).hexdigest() for x in [note,checker,report]}}
(HERE/'wrong_0011011_negative_outer_edge3_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
