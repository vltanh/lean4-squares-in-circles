"""Independent rational reconstruction of the candidate quarter-owner proof.

The author expands a quartic in the power basis.  Here the actual nominal
linear inequalities are evaluated directly at five rational half-angle
points, then a fixed Bernstein evaluation matrix is inverted.  No author
function, optimizer, floating arithmetic, or state sampler is imported.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json,shutil,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'candidate_quarter_owner_circle_dual_hand_data.json').exists() else HERE.parents[1]/'proof_integration'
NAMES=['HAND_CANDIDATE_QUARTER_OWNER_CAPTURE.md','verify_candidate_quarter_owner_circle_duals.py',
       'candidate_quarter_owner_circle_dual_hand_data.json','candidate_quarter_owner_circle_dual_hand_arithmetic.json']
data=json.loads((BASE/NAMES[2]).read_text())
assert data['Q']=='9789/2500' and data['epsilon']=='1/500'
assert data['denominator']==10**8 and data['bernstein_denominator']==10**12 and data['cells']==30
Q=F(data['Q']);eps=F(data['epsilon'])


def evaluate(row,z):
    den=1+z*z;sn=2*z/den;cs=(1-z*z)/den
    lambdas=[F(n,10**8) for n in row['lambda']]
    mus=[F(n,10**8) for n in row['mu']]
    assert len(lambdas)==len(mus)==7
    assert all(isinstance(n,int) and n>=0 for n in row['lambda'])
    assert all(isinstance(n,int) and n>0 for n in row['mu'])
    C=[F(0)]*14;bound=F(0)
    def combine(entries,mult):
        for k,value in entries.items():C[k]+=mult*value
    for i,axis in enumerate(row['owners']):
        j=(i+1)%7
        if i in [0,2,4]:
            assert axis==1;entries={7+i:F(1),7+j:F(1)}
        elif i==3:
            entries={4:F(1),10:F(-1)} if axis==1 else {3:F(1),11:F(-1)}
            assert axis in [1,3]
        elif i==5:
            entries={6:F(1),12:F(-1)} if axis==1 else {5:F(1),13:F(1)}
            assert axis in [1,3]
        elif i==1:
            entries={1:{8:-1,2:cs,9:-sn},2:{1:-sn,8:-cs,2:1},
                     3:{1:cs,8:-sn,9:-1},4:{1:1,2:-sn,9:-cs}}[axis]
        else:
            assert i==6
            entries={1:{13:-1,0:cs,7:sn},2:{6:sn,13:-cs,0:1},
                     3:{6:cs,13:sn,7:-1},4:{6:1,0:sn,7:-cs}}[axis]
        combine(entries,lambdas[i])
        wt=(1+cs+abs(sn))/2
        rhs=wt if i==1 else wt-2*eps if i==6 else 1-F(3,2)*eps
        bound+=lambdas[i]*rhs
    seen=set();low=[F(1,2),F(1,20),F(0),F(0),F(1,20),F(1,2),F(0)]
    high=[F(1),F(4,5),F(1),F(1),F(4,5),F(1),F(1)]
    for index,n in row['cone']:
        assert isinstance(index,int) and 0<=index<35 and index not in seen
        assert isinstance(n,int) and n>0;seen.add(index)
        i,k=divmod(index,5);mult=F(n,10**8)
        entries,rhs=[({i:F(1)},F(447,800)),({i:F(-1)},-F(283,200)),
                     ({7+i:F(1),i:-low[i]},F(0)),({i:high[i],7+i:F(-1)},F(0)),
                     ({7+i:F(-1)},-F(9,10))][k]
        combine(entries,mult);bound+=mult*rhs
    lhs=bound+sum(C,F(0))/2
    upper=Q*sum(mus,F(0))+sum((C[i]*C[i]+C[7+i]*C[7+i])/(4*mus[i]) for i in range(7))
    return den*den*(lhs-upper)


def basis(v):return [F(comb(4,k))*v**k*(1-v)**(4-k) for k in range(5)]
nodes=[F(j,4) for j in range(5)]
matrix=[basis(v)+[F(int(i==j)) for j in range(5)] for i,v in enumerate(nodes)]
for j in range(5):
    pivot=next(i for i in range(j,5) if matrix[i][j])
    matrix[j],matrix[pivot]=matrix[pivot],matrix[j]
    divisor=matrix[j][j];matrix[j]=[x/divisor for x in matrix[j]]
    for i in range(5):
        if i==j:continue
        weight=matrix[i][j];matrix[i]=[a-weight*b for a,b in zip(matrix[i],matrix[j])]
inverse=[r[5:] for r in matrix]
assert [r[:5] for r in matrix]==[[F(int(i==j)) for j in range(5)] for i in range(5)]

patterns={(1,g,1,b,1,e,h) for g,h in product(range(1,5),repeat=2)
          for b,e in [(1,1),(1,3),(3,1)]}
expected={(p,F(-3,8)+F(j,40),F(-3,8)+F(j+1,40)) for p in patterns for j in range(30)}
seen=set();minimum=None;count=0
for row in data['rows']:
    lo,hi=F(row['lo']),F(row['hi']);key=tuple(row['owners']),lo,hi
    assert key in expected and key not in seen and (hi<=0 or lo>=0);seen.add(key)
    values=[evaluate(row,lo+(hi-lo)*v) for v in nodes]
    coefficients=[sum(c*y for c,y in zip(r,values)) for r in inverse]
    printed=row['bernstein_lower_numerators'];assert len(printed)==5
    for actual,n in zip(coefficients,printed):
        assert isinstance(n,int) and n>0 and actual>=F(n,10**12)
        lower=F(n,10**12);minimum=lower if minimum is None else min(minimum,lower);count+=1
    # An extra rational point checks the separately assembled quartic identity.
    v=F(1,3)
    assert evaluate(row,lo+(hi-lo)*v)==sum(c*b for c,b in zip(coefficients,basis(v)))
assert seen==expected and len(patterns)==48 and len(seen)==1440 and count==7200
assert minimum==F(1970267266,10**12)
assert F(3,8)-F(3,8)**3/3-F(7,20)==F(19,2560)>0

with tempfile.TemporaryDirectory() as tmp:
    tmp=Path(tmp)
    for name in [NAMES[1],NAMES[2]]:shutil.copyfile(BASE/name,tmp/name)
    subprocess.run([sys.executable,str(tmp/NAMES[1])],check=True,cwd=tmp,capture_output=True)
    assert (tmp/NAMES[3]).read_bytes()==(BASE/NAMES[3]).read_bytes()

out={'status':'PASS','scope':'Continuous actual-to-nominal owner reduction plus independently reconstructed rational circle-dual quartics',
     'owner_patterns':48,'closed_cells_per_pattern':30,'quartics':1440,'independently_recomputed_bernstein_coefficients':count,
     'independent_extra_identity_points':1440,'minimum_printed_coefficient':str(minimum),'author_replay_byte_identical':True,
     'independent_method':'Direct rational evaluation of explicit nominal inequalities at five points and inversion of a fixed Bernstein evaluation matrix',
     'sha256':{name:sha256((BASE/name).read_bytes()).hexdigest() for name in NAMES}}
(HERE/'candidate_quarter_owner_capture_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
