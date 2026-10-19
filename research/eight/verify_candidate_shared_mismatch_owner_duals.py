"""Standalone fixed rational replay for mixed owners at total S<=1/1000.

No search, floating point, optimization, interval subdivision, or imported
proof program is used.  The single total-error loss is reconstructed from
each row's own nonnegative edge weights.
"""
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json

BASE=Path(__file__).resolve().parent
INPUT=BASE/'candidate_mixed_owner_shared_mismatch_hand_data.json'
OUTPUT=BASE/'candidate_mixed_owner_shared_mismatch_hand_arithmetic.json'
Q=R(9789,2500);EPS=R(1,1000);LOSS=R(1001,1000)

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

def nominal(owners,positive):
    D=[R(1),R(0),R(1)];S=[R(0),R(2)];C=[R(1),R(0),-R(1)];Z=[R(0)]
    signs=(1,-1,1,-1,1,-1,-1);out=[]
    for i,axis in enumerate(owners):
        j=(i+1)%7
        sn,cs=((Z,D) if i in (0,2,4) else (D,Z) if i in (3,5)
               else (C,S) if i==1 else (C,scale(S,-1)))
        row=[Z[:] for _ in range(14)]
        def put(j,p,c=1):row[j]=add(row[j],scale(p,R(c)))
        if axis==1:
            put(7+i,D,signs[i]);put(j,sn);put(7+j,cs,-signs[j])
        elif axis==2:
            put(i,cs,-1);put(7+i,sn,signs[i]);put(j,D)
        elif axis==3:
            put(i,sn);put(7+i,cs,signs[i]);put(7+j,D,-signs[j])
        else:
            assert axis==4
            put(i,D);put(j,cs,-1);put(7+j,sn,-signs[j])
        out.append(row)
    W=scale(add(D,C,scale(S,1 if positive else -1)),R(1,2))
    return D,out,[W if i in (1,6) else D for i in range(7)]

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

def verify(row):
    lo,hi=R(row['lo']),R(row['hi']);assert lo<hi and (hi<=0 or lo>=0)
    D,A,b=nominal(row['owners'],lo>=0);K,v=cones()
    assert len(row['lambda'])==len(row['mu'])==7
    assert all(isinstance(n,int) and n>=0 for n in row['lambda'])
    assert all(isinstance(n,int) and n>0 for n in row['mu'])
    lam=[R(n,10**8) for n in row['lambda']];mu=[R(n,10**8) for n in row['mu']]
    kap=[R(0)]*35;seen=set()
    for j,n in row['cone']:
        assert isinstance(j,int) and 0<=j<35 and j not in seen and isinstance(n,int) and n>0
        seen.add(j);kap[j]=R(n,10**8)
    C=[add(scale(D,sum(kap[h]*K[h][j] for h in range(35))),
           *[scale(A[i][j],lam[i]) for i in range(7)]) for j in range(14)]
    error=EPS*(LOSS*max(lam[i] for i in (0,2,3,4,5))+2*lam[6])
    L=add(scale(D,sum(kap[h]*v[h] for h in range(35))-error),
          *[scale(b[i],lam[i]) for i in range(7)],*[scale(p,R(1,2)) for p in C])
    P=add(mul(D,L),scale(mul(D,D),-Q*sum(mu)),
          *[scale(add(mul(C[i],C[i]),mul(C[7+i],C[7+i])),-1/(4*mu[i])) for i in range(7)])
    assert len(P)<=5;P+=[R(0)]*(5-len(P));h=hi-lo
    pw=[sum(P[n]*comb(n,j)*lo**(n-j)*h**j for n in range(j,5)) for j in range(5)]
    bs=[sum(pw[j]*R(comb(i,j),comb(4,j)) for j in range(i+1)) for i in range(5)]
    assert [sum(bs[i]*comb(4,i)*comb(4-i,j-i)*(-1)**(j-i) for i in range(j+1)) for j in range(5)]==pw
    ns=row['bernstein_lower_numerators'];assert len(ns)==5
    assert all(isinstance(n,int) and n>0 and b>=R(n,10**12) for b,n in zip(bs,ns))
    return min(ns)

def main():
    raw=INPUT.read_bytes();data=json.loads(raw)
    assert data['mode']=='mixed' and data['Q']==str(Q) and data['epsilon']==str(EPS)
    assert data['shared_total_error'] is True and data['aligned_loss']==str(LOSS)
    assert data['denominator']==10**8 and data['bernstein_denominator']==10**12 and data['degree']==4
    assert data['unresolved']==[]
    patterns={(1,g,1,3,1,3,h) for g,h in product(range(1,5),repeat=2) if (g,h)!=(1,2)}
    assert len(patterns)==15
    cover={p:[] for p in patterns};bounds={p:10**100 for p in patterns};seen=set()
    for row in data['rows']:
        p=tuple(row['owners']);lo,hi=R(row['lo']),R(row['hi']);key=(p,lo,hi)
        assert p in patterns and key not in seen;seen.add(key)
        bounds[p]=min(bounds[p],verify(row));cover[p].append((lo,hi))
    for chain in cover.values():
        end=-R(3,8)
        for lo,hi in sorted(chain):assert lo==end;end=hi
        assert end==R(3,8)
    # The true aligned support cusp gives the stated uniform loss.
    assert LOSS>1+R(1,500)/4+R(1,500)**2/12
    assert EPS<=R(1,500)
    assert R(3,8)-R(3,8)**3/3>R(7,20)
    assert R(4,5)*R(7,12)<R(1,2)
    assert (R(349,250)+R(1,2))**2+(R(349,5000)+R(1,2))**2>Q
    report={'status':'PASS_FIXED_SHARED_ERROR_HAND_POLYNOMIALS_AND_COVER',
      'Q':str(Q),'epsilon':str(EPS),'aligned_loss':str(LOSS),
      'input_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
      'owner_patterns':15,'quartics':len(seen),'bernstein_coefficients':5*len(seen),
      'minimum_printed_coefficient':str(R(min(bounds.values()),10**12)),
      'pattern_summary':[{'owners':list(p),'closed_cells':len(cover[p]),'minimum_numerator':bounds[p]}
                         for p in sorted(patterns)]}
    OUTPUT.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='pattern_summary'},indent=2))

if __name__=='__main__':main()
