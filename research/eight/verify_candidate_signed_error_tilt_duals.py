"""Standalone fixed rational replay of common-weight signed-error bundles.

Each interval has exactly one common edge-weight vector.  All21 permitted
error/owner vertices are reconstructed from that vector and the actual SAT
derivatives; vertex-specific data may supply only cone and circle weights.
There is no floating point, search, optimization, or imported proof program.
"""
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json

BASE=Path(__file__).resolve().parent
INPUT=BASE/'candidate_tilt_signed_error_hand_data.json'
OUTPUT=BASE/'candidate_tilt_signed_error_hand_arithmetic.json'
Q=R(1957767069,500000000);EPS=R(1,1000)
OWNERS=(1,1,1,3,1,3,2);SIGNS=(1,-1,1,-1,1,-1,-1)
D=[R(1),R(0),R(1)];S=[R(0),R(2)];C=[R(1),R(0),-R(1)];Z=[R(0)]
DERIVATIVES=((0,1,1),(0,3,0),(2,1,3),(2,3,2),(3,3,10),
             (3,4,4),(4,1,5),(4,3,4),(5,3,12),(5,4,6))
EXPECTED={(-1,0,0,-1)}|{(i,a,s,j) for i,a,j in DERIVATIVES for s in (-1,1)}

def add(*ps):
    out=[R(0)]*max(map(len,ps))
    for p in ps:
        for j,c in enumerate(p):out[j]+=c
    return out
def scale(p,c):return [c*x for x in p]
def mul(p,q):
    out=[R(0)]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        for j,d in enumerate(q):out[i+j]+=c*d
    return out

def angle(i):
    return (Z,D) if i in (0,2,4) else (D,Z) if i in (3,5) else (C,S) if i==1 else (C,scale(S,-1))

def projection(i,axis,derivative=False):
    j=(i+1)%7;sn,cs=angle(i);row=[Z[:] for _ in range(14)]
    def put(j,p,c=1):row[j]=add(row[j],scale(p,R(c)))
    if derivative:
        if axis==1:put(j,cs);put(7+j,sn,SIGNS[j])
        elif axis==2:put(i,sn);put(7+i,cs,SIGNS[i])
        elif axis==3:put(i,cs);put(7+i,sn,-SIGNS[i])
        else:
            assert axis==4;put(j,sn);put(7+j,cs,-SIGNS[j])
    else:
        if axis==1:put(7+i,D,SIGNS[i]);put(j,sn);put(7+j,cs,-SIGNS[j])
        elif axis==2:put(i,cs,-1);put(7+i,sn,SIGNS[i]);put(j,D)
        elif axis==3:put(i,sn);put(7+i,cs,SIGNS[i]);put(7+j,D,-SIGNS[j])
        else:
            assert axis==4;put(i,D);put(j,cs,-1);put(7+j,sn,-SIGNS[j])
    return row

def cones():
    low=(R(1,2),R(1,20),0,0,R(1,20),R(1,2),0)
    high=(1,R(4,5),1,1,R(4,5),1,1);rows=[];values=[]
    for i in range(7):
        floor=R(7,12) if i in (1,4) else R(447,800)
        ceiling=R(349,250) if i in (1,4) else R(283,200)
        for entries,v in [({i:R(1)},floor),({i:-R(1)},-ceiling),
          ({i:-R(low[i]),7+i:R(1)},R(0)),
          ({i:R(high[i]),7+i:-R(1)},R(0)),({7+i:-R(1)},-R(9,10))]:
            p=[R(0)]*14
            for j,c in entries.items():p[j]+=c
            rows.append(p);values.append(v)
    return rows,values

def polynomial(bundle,row):
    lo,hi=R(bundle['lo']),R(bundle['hi']);positive=lo>=0
    lam=[R(n,10**8) for n in bundle['lambda']]
    # There is deliberately no vertex-specific edge-weight input.
    assert 'lambda' not in row
    A=[projection(i,a) for i,a in enumerate(OWNERS)]
    f6prime=projection(6,2,True)
    width=scale(add(D,C,scale(S,1 if positive else -1)),R(1,2))
    wprime=scale(add(C,scale(S,-1)),R(1,2)) if positive else scale(add(C,S),-R(1,2))
    raw=[add(*[scale(A[i][j],lam[i]) for i in range(7)]) for j in range(14)]
    rhs=add(*[scale(width if i in (1,6) else D,lam[i]) for i in range(7)])
    remainder=EPS**2*(R(1001,1000)*max(lam[i] for i in (0,2,3,4,5))+R(9,8)*lam[6])
    rhs=add(rhs,scale(D,-remainder))
    edge,owner,sign,coordinate=tuple(row['vertex'])
    if edge>=0:
        derivative=projection(edge,owner,True)
        # This independently reconstructs the claimed one-coordinate table.
        expected=[Z[:] for _ in range(14)];expected[coordinate]=D
        assert all(add(a,scale(b,-1))==[R(0)]*max(len(a),len(b)) for a,b in zip(derivative,expected))
        raw=[add(p,scale(v,sign*EPS*lam[edge]),scale(g,-sign*EPS*lam[6]))
             for p,v,g in zip(raw,derivative,f6prime)]
        rhs=add(rhs,scale(wprime,-sign*EPS*lam[6]),scale(D,EPS*lam[edge]/2))
    K,v=cones();kap=[R(0)]*35;seen=set()
    for j,n in row['cone']:
        assert isinstance(j,int) and 0<=j<35 and j not in seen and isinstance(n,int) and n>0
        seen.add(j);kap[j]=R(n,10**8)
    force=[add(p,scale(D,sum(kap[h]*K[h][j] for h in range(35)))) for j,p in enumerate(raw)]
    L=add(rhs,scale(D,sum(kap[h]*v[h] for h in range(35))),*[scale(p,R(1,2)) for p in force])
    assert len(row['mu'])==7 and all(isinstance(n,int) and n>0 for n in row['mu'])
    mu=[R(n,10**8) for n in row['mu']]
    P=add(mul(D,L),scale(mul(D,D),-Q*sum(mu)),
          *[scale(add(mul(force[i],force[i]),mul(force[7+i],force[7+i])),
                  -1/(4*mu[i])) for i in range(7)])
    assert len(P)<=5;P+=[R(0)]*(5-len(P));h=hi-lo
    powers=[sum(P[n]*comb(n,j)*lo**(n-j)*h**j for n in range(j,5)) for j in range(5)]
    berns=[sum(powers[j]*R(comb(i,j),comb(4,j)) for j in range(i+1)) for i in range(5)]
    assert [sum(berns[i]*comb(4,i)*comb(4-i,j-i)*(-1)**(j-i) for i in range(j+1)) for j in range(5)]==powers
    printed=row['bernstein_lower_numerators'];assert len(printed)==5
    assert all(isinstance(n,int) and n>0 and b>=R(n,10**12) for b,n in zip(berns,printed))
    return min(printed)

def main():
    raw=INPUT.read_bytes();data=json.loads(raw)
    assert data['Q']==str(Q) and data['epsilon']==str(EPS)
    assert data['denominator']==10**8 and data['bernstein_denominator']==10**12
    assert data['unresolved']==[] and len(EXPECTED)==21
    intervals=[];seen=set();least=10**100;summary=[]
    for bundle in data['bundles']:
        lo,hi=R(bundle['lo']),R(bundle['hi']);assert lo<hi and (lo>=0 or hi<=0)
        assert (lo,hi) not in seen;seen.add((lo,hi));intervals.append((lo,hi))
        assert len(bundle['lambda'])==7 and all(isinstance(n,int) and n>=0 for n in bundle['lambda'])
        vertices=set();minimum=10**100
        for row in bundle['vertices']:
            key=tuple(row['vertex']);assert key in EXPECTED and key not in vertices
            vertices.add(key);minimum=min(minimum,polynomial(bundle,row))
        assert vertices==EXPECTED;least=min(least,minimum)
        summary.append({'lo':str(lo),'hi':str(hi),'minimum_numerator':minimum})
    intervals.sort();offset=0
    for left,right in [(-R(3,8),R(1001,20000)),(R(2,25),R(3,8))]:
        end=left
        while offset<len(intervals) and intervals[offset][0]<right:
            lo,hi=intervals[offset];assert lo==end and hi<=right;end=hi;offset+=1
        assert end==right
    assert offset==len(intervals)
    # Exact rational bounds behind the Taylor constants and final chart.
    assert 1+R(1,500)/12<R(1001,1000)
    assert R(2)<R(3,2)**2 # sqrt(2)/4 < 3/8
    assert R(3,4)+R(3,8)==R(9,8)
    assert R(3,8)-R(3,8)**3/3>R(7,20)
    assert 2*(R(1001,20000)-R(1001,20000)**3/3)>R(1,10)
    assert 2*R(2,25)==R(4,25)
    report={'status':'PASS_FIXED_COMMON_WEIGHT_ERROR_VERTEX_HAND_PROOF',
      'Q':str(Q),'epsilon':str(EPS),'input_sha256':sha256(raw).hexdigest(),
      'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
      'closed_cells':len(intervals),'vertices_per_common_weight_bundle':21,
      'quartics':21*len(intervals),'bernstein_coefficients':105*len(intervals),
      'minimum_printed_coefficient':str(R(least,10**12)),'cell_summary':summary}
    OUTPUT.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cell_summary'},indent=2))

if __name__=='__main__':main()
