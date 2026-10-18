"""Independent direct-evaluation audit of the common-weight tilt disjunction.

No author polynomial function is imported. The nominal forces and each
error alternative are assembled as rational values at five points. A
Bernstein evaluation matrix is inverted, rather than converting the
author's power expansion. A sixth point checks the quartic identity.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json, shutil, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'candidate_tilt_signed_error_hand_data.json').exists() else HERE.parents[1]/'proof_integration'
NAMES=['HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md',
       'verify_candidate_signed_error_tilt_duals.py',
       'candidate_tilt_signed_error_hand_data.json',
       'candidate_tilt_signed_error_hand_arithmetic.json']
data=json.loads((BASE/NAMES[2]).read_text())
Q=F(1957767069,500000000);eps=F(1,1000)
assert data['Q']==str(Q) and data['epsilon']==str(eps)
assert data['denominator']==10**8 and data['bernstein_denominator']==10**12
assert data['unresolved']==[]
aligned={0,2,3,4,5}
derivatives={(0,1):1,(0,3):0,(2,1):3,(2,3):2,(3,3):10,
             (3,4):4,(4,1):5,(4,3):4,(5,3):12,(5,4):6}
expected={(-1,0,0,-1)}|{(i,a,s,j) for (i,a),j in derivatives.items() for s in [-1,1]}
assert len(expected)==21

def value(bundle,row,z):
    d=1+z*z;sn=2*z/d;cs=(1-z*z)/d
    lam=[F(n,10**8) for n in bundle['lambda']]
    assert 'lambda' not in row
    C=[F(0)]*14
    nominal=[{7:1,8:1}, {8:-1,2:cs,9:-sn}, {9:1,10:1},
             {3:1,11:-1}, {11:1,12:1}, {5:1,13:1},
             {0:1,6:sn,13:-cs}]
    for i,p in enumerate(nominal):
        for j,x in p.items():C[j]+=lam[i]*x
    width=(1+cs+abs(sn))/2
    bound=sum(lam[i]*(width if i in [1,6] else 1) for i in range(7))
    loss=eps*eps*(F(1001,1000)*max(lam[i] for i in aligned)+F(9,8)*lam[6])
    bound-=loss
    i,axis,sign,j=tuple(row['vertex'])
    if i>=0:
        assert derivatives[i,axis]==j
        C[j]+=sign*eps*lam[i]
        C[6]-=sign*eps*lam[6]*cs
        C[13]-=sign*eps*lam[6]*sn
        wprime=(cs-sn)/2 if F(bundle['lo'])>=0 else -(cs+sn)/2
        bound+=eps*lam[i]/2-sign*eps*lam[6]*wprime
    low=[F(1,2),F(1,20),F(0),F(0),F(1,20),F(1,2),F(0)]
    high=[F(1),F(4,5),F(1),F(1),F(4,5),F(1),F(1)]
    seen=set()
    for index,n in row['cone']:
        assert isinstance(index,int) and 0<=index<35 and index not in seen
        assert isinstance(n,int) and n>0;seen.add(index)
        role,kind=divmod(index,5);mult=F(n,10**8)
        floor=F(7,12) if role in [1,4] else F(447,800)
        ceiling=F(349,250) if role in [1,4] else F(283,200)
        coeff,rhs=[({role:1},floor),({role:-1},-ceiling),
                   ({7+role:1,role:-low[role]},F(0)),
                   ({role:high[role],7+role:-1},F(0)),
                   ({7+role:-1},-F(9,10))][kind]
        for j,x in coeff.items():C[j]+=mult*x
        bound+=mult*rhs
    assert len(row['mu'])==7 and all(isinstance(n,int) and n>0 for n in row['mu'])
    mu=[F(n,10**8) for n in row['mu']]
    L=bound+sum(C,F(0))/2
    U=Q*sum(mu,F(0))+sum((C[i]**2+C[7+i]**2)/(4*mu[i]) for i in range(7))
    return d*d*(L-U)

def basis(v):return [F(comb(4,j))*v**j*(1-v)**(4-j) for j in range(5)]
nodes=[F(j,4) for j in range(5)]
matrix=[basis(v)+[F(int(i==j)) for j in range(5)] for i,v in enumerate(nodes)]
for j in range(5):
    pivot=next(i for i in range(j,5) if matrix[i][j])
    matrix[j],matrix[pivot]=matrix[pivot],matrix[j]
    a=matrix[j][j];matrix[j]=[x/a for x in matrix[j]]
    for i in range(5):
        if i==j:continue
        a=matrix[i][j];matrix[i]=[x-a*y for x,y in zip(matrix[i],matrix[j])]
assert [r[:5] for r in matrix]==[[F(int(i==j)) for j in range(5)] for i in range(5)]
inverse=[r[5:] for r in matrix]

intervals=[];seen=set();row_count=0;coefficient_count=0;minimum=None
for bundle in data['bundles']:
    lo,hi=F(bundle['lo']),F(bundle['hi'])
    assert lo<hi and (lo>=0 or hi<=0) and (lo,hi) not in seen
    seen.add((lo,hi));intervals.append((lo,hi))
    assert len(bundle['lambda'])==7 and all(isinstance(n,int) and n>=0 for n in bundle['lambda'])
    vertices=set()
    for row in bundle['vertices']:
        v=tuple(row['vertex']);assert v in expected and v not in vertices;vertices.add(v)
        values=[value(bundle,row,lo+(hi-lo)*x) for x in nodes]
        coefficients=[sum(a*b for a,b in zip(r,values)) for r in inverse]
        printed=row['bernstein_lower_numerators'];assert len(printed)==5
        for actual,n in zip(coefficients,printed):
            assert isinstance(n,int) and n>0 and actual>=F(n,10**12)
            bound=F(n,10**12);minimum=bound if minimum is None else min(minimum,bound)
            coefficient_count+=1
        x=F(1,3)
        assert value(bundle,row,lo+(hi-lo)*x)==sum(a*b for a,b in zip(coefficients,basis(x)))
        row_count+=1
    assert vertices==expected

intervals.sort();offset=0
for left,right in [(F(-3,8),F(1001,20000)),(F(2,25),F(3,8))]:
    end=left
    while offset<len(intervals) and intervals[offset][0]<right:
        lo,hi=intervals[offset];assert lo==end and hi<=right
        end=hi;offset+=1
    assert end==right
assert offset==len(intervals)==59 and row_count==1239 and coefficient_count==6195

# Reconstruct the harmless strict constants behind the continuous argument.
assert F(3,4)+F(1,4)+F(1,500)/12<F(1001,1000)
assert F(2)<F(3,2)**2 and F(3,4)+F(3,8)==F(9,8)
assert F(3,8)-F(3,8)**3/3>F(7,20)
assert 2*(F(1001,20000)-F(1001,20000)**3/3)>F(1,10)
assert 2*F(2,25)==F(4,25)
assert F(4,5)*F(7,12)<F(1,2)
assert (F(349,250)+F(1,2))**2+(F(349,5000)+F(1,2))**2>Q

with tempfile.TemporaryDirectory() as tmp:
    tmp=Path(tmp)
    for name in NAMES[1:3]:shutil.copyfile(BASE/name,tmp/name)
    subprocess.run([sys.executable,str(tmp/NAMES[1])],check=True,cwd=tmp,capture_output=True)
    assert (tmp/NAMES[3]).read_bytes()==(BASE/NAMES[3]).read_bytes()

out={'status':'PASS','scope':'Independent signed-error disjunction, direct rational circle-dual evaluation, quartic reconstruction and complete tilt-tail cover',
     'Q':str(Q),'epsilon':str(eps),'common_weight_bundles':59,
     'alternatives_per_bundle':21,'quartics':row_count,
     'independently_recomputed_bernstein_coefficients':coefficient_count,
     'independent_sixth_identity_points':row_count,
     'minimum_printed_coefficient':str(minimum),
     'closed_union':'[-3/8,1001/20000] union [2/25,3/8]',
     'author_replay_byte_identical':True,
     'sha256':{name:sha256((BASE/name).read_bytes()).hexdigest() for name in NAMES}}
(HERE/'candidate_signed_error_tilt_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
