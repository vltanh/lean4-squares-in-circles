"""Independent rational reconstruction for the whole C+ -> O+ edge3 proof."""
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
from hashlib import sha256
import json,subprocess

HERE=Path(__file__).resolve().parent
ROOT=Path(__file__).resolve().parents[2]
P=HERE if (HERE/'verify_wrong_0011011_edge3_positive_core_to_positive_outer.js').exists() else ROOT/'m5_agent/hand_conversion'
checker=P/'verify_wrong_0011011_edge3_positive_core_to_positive_outer.js'
note=P/'WRONG_0011011_EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md'
report=P/'wrong_0011011_edge3_positive_core_to_positive_outer_arithmetic.json'
raw=subprocess.run(['node',str(checker)],check=True,capture_output=True).stdout
assert raw==report.read_bytes()
data=json.loads(raw);assert data['status']=='PASS' and data['comparisons']==166
assert all(F(c['lower'])>F(c['threshold']) and c['pass'] for c in data['checks'])
label_path=HERE/'wrong_0011011_labels.json'
if not label_path.exists():label_path=ROOT/'proof_integration/wrong_0011011_labels.json'
labels=json.loads(label_path.read_text())
assert labels['independent_roles']['3']['C+']==[-1449,0,104240,0,0]
assert labels['independent_roles']['4']['O+']==[3965,0,385510,-149748,-189442]

def add(a,b):return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
def scale(a,s):return[x*s for x in a]
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def trig(kind,n):
 p=[F(0)]*(n+1);start=1 if kind=='sin' else 0
 for j in range(start,n+1,2):p[j]=F((-1)**((j-start)//2),factorial(j))
 return p
def triangular(p,l,h):
 n=len(p)-1
 a=[sum((p[i]*comb(i,j)*l**(i-j)*(h-l)**j for i in range(j,n+1)),F(0)) for j in range(n+1)]
 b=[]
 for j in range(n+1):
  b.append((a[j]-sum((b[k]*comb(n,k)*comb(n-k,j-k)*(-1)**(j-k) for k in range(j)),F(0)))/comb(n,j))
 return b
Q=F('3.9156');g=F('1.04240');q=F('.643398450');k=F('.128316398');gamma=F('.89765')
K=F('3.141592653589793238')/2-F('.01449')-k+(g+q)/2-gamma
A=add(add(mul(trig('cos',10),[K,F(-1)]),[g]),scale(trig('sin',11),13*g/12))
poly=add(mul(A,A),scale(add([g*g],scale(mul(trig('cos',8),trig('cos',8)),q*q)),-Q))
tail=sum((-v*F('.7')**i for i,v in enumerate(poly) if i>=9 and v<0),F(0))
assert tail<F('.000267')
p8=poly[:9];p8[0]-=F('.000267');bs=triangular(p8,F('.11'),F('.7'))
table=data['tables'][0]
assert list(map(F,table['power_coefficients']))==p8
assert list(map(F,table['bernstein_coefficients']))==bs
assert all(x>F(y)>0 for x,y in zip(bs,table['printed_lower']))
assert F(table['tail'])==tail

# The source-corner convexity prefactor and upper primary zero's domain
# also follow directly from the displayed coarse rational bounds.
assert F('1.016')**2*F('1.34')>F('1.3')
assert 12*F('.399')*F('1.3')/4>1
assert F('.5')+F('.5')*F('.99')-F('.11')/12>F('.9')
assert F('.161')*F('1.3')**2-F('1.176')*F('.22')>0
assert F('6.8')*F('.684')-F('2.003')**2>0
out={'status':'PASS','replayed_fixed_comparisons':166,'replay_byte_identical':True,
 'independent_polynomial_degree':8,'independent_polynomial_coefficients':9,
 'independent_printed_bounds':9,'independent_coarse_checks':5,
 'label_binding':'Exact role3 C+ and role4 O+ rows match the shared rational table',
 'sha256':{x.name:sha256(x.read_bytes()).hexdigest() for x in [note,checker,report]}}
(Path(__file__).resolve().parent/'wrong_0011011_positive_core_outer_edge3_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
