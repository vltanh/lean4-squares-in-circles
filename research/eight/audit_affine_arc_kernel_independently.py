"""Independent algebra/endpoint checks for the frozen affine-arc kernel.

The Bernstein comparison uses triangular basis solving, not the kernel's
integer binomial conversion formula. Endpoint comparisons use the defining
quadratic equations. This script is additional audit evidence; the continuous
proof is recorded in AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
from hashlib import sha256
import json
import subprocess
import tempfile

P=Path(__file__).resolve().parent
kernel=P/'verify_G_upper_affine_hand.js'
code=kernel.read_text()
assert sha256(kernel.read_bytes()).hexdigest()=='1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee'
data=json.loads((P/'G_UPPER_AFFINE_HAND_DATA.json').read_text())

def mul(a,b):
 out=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return out
def power(a,n):
 out=[F(1)]
 for _ in range(n):out=mul(out,a)
 return out

# Let z=sqrt(V)/h. After multiplication by16/h, the majorant
# identity becomes this polynomial identity with integer coefficients.
rhs=mul(power([F(-1),F(1)],4),[F(5),F(4),F(1)])
assert rhs==list(map(F,[5,-16,15,0,-5,0,1]))

def triangular_bernstein(p,lo,hi):
 n=len(p)-1;w=hi-lo
 # First substitute lo+w*x into the power polynomial.
 a=[sum((p[i]*comb(i,j)*lo**(i-j)*w**j for i in range(j,n+1)),F(0)) for j in range(n+1)]
 # Then solve the lower-triangular coefficient system for
 # sum b_k*C(n,k)*x^k*(1-x)^(n-k), one coefficient at a time.
 b=[]
 for j in range(n+1):
  previous=sum((b[k]*comb(n,k)*comb(n-k,j-k)*(-1)**(j-k) for k in range(j)),F(0))
  b.append((a[j]-previous)/comb(n,j))
 return b

cases=[]
for n in range(31):
 p=[F((-1)**j*(j*j+3*n+1),(j+1)*(n+2)) for j in range(n+1)]
 for lo,hi in [(F(0),F(7,10)),(F(113,1000),F(29,100)),(F(1,7),F(1,7))]:
  cases.append({'p':list(map(str,p)),'lo':str(lo),'hi':str(hi)})
points=sorted({(a['kind'],a[k]) for a in data['arcs'] for k in ['lo','hi']})
prefix=code[:code.index('// Fixed one-angle affine-support verifier.')]
ab=code[code.index('function abAt('):code.index('function makeArc(')]
js=prefix+'\nconst Q=rr('+json.dumps(data['Q'])+'),R=root(Q);\n'+ab+'\n'
js+='const cases='+json.dumps(cases)+';const points='+json.dumps(points)+';\n'
js+='console.log(JSON.stringify({bernstein:cases.map(c=>bernstein(c.p.map(rr),c.lo,c.hi).map(x=>x.toString())),endpoints:points.map(([k,u])=>({kind:k,u,...Object.fromEntries(Object.entries(abAt(u,k)).map(([v,x])=>[v,x.map(z=>z.toString())]))}))}));\n'
with tempfile.TemporaryDirectory(prefix='g_upper_kernel_audit_') as d:
 path=Path(d)/'extract.js';path.write_text(js)
 answer=json.loads(subprocess.run(['node',str(path)],check=True,capture_output=True,text=True).stdout)

count=0
for c,actual in zip(cases,answer['bernstein']):
 expected=triangular_bernstein(list(map(F,c['p'])),F(c['lo']),F(c['hi']))
 assert list(map(F,actual))==expected
 count+=len(expected)
assert len(answer['bernstein'])==len(cases)==93

Q=F(data['Q']);endpoint_checks=0
for row in answer['endpoints']:
 u=F(row['u']);lo,hi=map(F,row['a']);bl,bh=map(F,row['b'])
 assert lo<=hi and bl<=u*lo<=u*hi<=bh and lo>0
 if row['kind']=='C' and u<=F(6,7):
  assert lo<=F(7,12)<=hi
 else:
  q0=(F(1,2)-Q) if row['kind']=='O' else F(71,144)
  q1=1+u if row['kind']=='O' else -(1+u)
  def f(a):return(1+u*u)*a*a+q1*a+q0
  assert f(lo)<=0<=f(hi)
  assert 2*(1+u*u)*lo+q1>0
  shift=F(-1,2) if row['kind']=='O' else F(1,2)
  assert lo>shift
 endpoint_checks+=1

out={'status':'PASS','scope':'Independent triangular Bernstein reconstruction, all fixed arc endpoint quadratics, and the global radical identity; continuous SAT/support review is in the companion note',
 'bernstein_polynomials':len(cases),'independently_reconstructed_coefficients':count,
 'degrees':list(range(31)),'fixed_state_endpoints':endpoint_checks,
 'radical_identity':'(z-1)^4(z^2+4z+5)=z^6-5z^4+15z^2-16z+5',
 'sha256':{kernel.name:sha256(kernel.read_bytes()).hexdigest(),'G_UPPER_AFFINE_HAND_DATA.json':sha256((P/'G_UPPER_AFFINE_HAND_DATA.json').read_bytes()).hexdigest()}}
(P/'AFFINE_ARC_KERNEL_INDEPENDENT_ARITHMETIC.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
