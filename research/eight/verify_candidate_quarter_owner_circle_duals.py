"""Fixed rational arithmetic for the conditional quarter-owner hand theorem.

Only the supplied finite constants are read.  There is no search, floating
point arithmetic, optimizer, adaptive subdivision, or imported proof program.
"""
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json

BASE=Path(__file__).resolve().parent
INPUT=BASE/'candidate_quarter_owner_circle_dual_hand_data.json'
OUTPUT=BASE/'candidate_quarter_owner_circle_dual_hand_arithmetic.json'

def plus(*polys):
    n=max(map(len,polys));out=[R(0)]*n
    for p in polys:
        for i,c in enumerate(p):out[i]+=c
    return out
def times(p,q):
    out=[R(0)]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        for j,d in enumerate(q):out[i+j]+=c*d
    return out
def multiple(p,c):return [c*x for x in p]

def sat(owners,positive):
    den=[R(1),R(0),R(1)];s=[R(0),R(2)];c=[R(1),R(0),R(-1)];zero=[R(0)]
    signs=[1,-1,1,-1,1,-1,-1]
    out=[]
    for i,axis in enumerate(owners):
        j=(i+1)%7
        si,co=((zero,den) if i in (0,2,4) else
               (den,zero) if i in (3,5) else
               (c,s) if i==1 else (c,multiple(s,-1)))
        row=[zero[:] for _ in range(14)]
        def put(k,p,sg=1):row[k]=plus(row[k],multiple(p,R(sg)))
        if axis==1:
            put(7+i,den,signs[i]);put(j,si);put(7+j,co,-signs[j])
        elif axis==2:
            put(i,co,-1);put(7+i,si,signs[i]);put(j,den)
        elif axis==3:
            put(i,si);put(7+i,co,signs[i]);put(7+j,den,-signs[j])
        else:
            assert axis==4
            put(i,den);put(j,co,-1);put(7+j,si,-signs[j])
        out.append(row)
    halfwidth=multiple(plus(den,c,multiple(s,1 if positive else -1)),R(1,2))
    rhs=[multiple(den,R(997,1000)) for _ in range(7)]
    rhs[1]=halfwidth;rhs[6]=plus(halfwidth,multiple(den,-R(1,250)))
    return den,out,rhs

def cones():
    low=[R(1,2),R(1,20),0,0,R(1,20),R(1,2),0]
    high=[1,R(4,5),1,1,R(4,5),1,1]
    rows=[];bounds=[]
    for i in range(7):
        for entries,bound in [({i:R(1)},R(447,800)),
          ({i:-R(1)},-R(283,200)),
          ({i:-R(low[i]),7+i:R(1)},R(0)),
          ({i:R(high[i]),7+i:-R(1)},R(0)),
          ({7+i:-R(1)},-R(9,10))]:
            row=[R(0)]*14
            for j,c in entries.items():row[j]+=c
            rows.append(row);bounds.append(bound)
    return rows,bounds

def reconstruct(row):
    lo=R(row['lo']);hi=R(row['hi']);assert lo<hi and (hi<=0 or lo>=0)
    den,A,b=sat(row['owners'],lo>=0);B,v=cones()
    lam=[R(x,10**8) for x in row['lambda']];mu=[R(x,10**8) for x in row['mu']]
    assert len(lam)==7 and len(mu)==7 and all(x>=0 for x in lam) and all(x>0 for x in mu)
    kap=[R(0)]*35;seen=set()
    for j,n in row['cone']:
        assert 0<=j<35 and j not in seen and isinstance(n,int) and n>0
        seen.add(j);kap[j]=R(n,10**8)
    coeff=[]
    for j in range(14):
        coeff.append(plus(multiple(den,sum(kap[k]*B[k][j] for k in range(35))),
                          *[multiple(A[i][j],lam[i]) for i in range(7)]))
    L=plus(multiple(den,sum(kap[k]*v[k] for k in range(35))),
           *[multiple(b[i],lam[i]) for i in range(7)],
           *[multiple(p,R(1,2)) for p in coeff])
    P=plus(times(L,den),multiple(times(den,den),-R(9789,2500)*sum(mu)),
      *[multiple(plus(times(coeff[i],coeff[i]),times(coeff[7+i],coeff[7+i])),
                 -1/(4*mu[i])) for i in range(7)])
    assert len(P)<=5;P+=[R(0)]*(5-len(P))
    width=hi-lo
    q=[sum(P[n]*comb(n,j)*lo**(n-j)*width**j for n in range(j,5)) for j in range(5)]
    berns=[sum(q[j]*R(comb(k,j),comb(4,j)) for j in range(k+1)) for k in range(5)]
    # Reconstruct the power coefficients from the purported Bernstein basis.
    back=[sum(berns[k]*comb(4,k)*comb(4-k,j-k)*(-1)**(j-k)
              for k in range(j+1)) for j in range(5)]
    assert back==q
    printed=row['bernstein_lower_numerators'];assert len(printed)==5
    assert all(isinstance(n,int) and n>0 and x>=R(n,10**12) for x,n in zip(berns,printed))
    return min(printed)

def main():
    raw=INPUT.read_bytes();data=json.loads(raw)
    assert data['Q']=='9789/2500' and data['epsilon']=='1/500'
    assert data['denominator']==10**8 and data['bernstein_denominator']==10**12
    assert data['cells']==30
    patterns={(1,ga,1,bt,1,de,eh) for bt,de,ga,eh in
        product((1,3),(1,3),range(1,5),range(1,5)) if not (bt==de==3)}
    assert len(patterns)==48
    expected={(p,str(R(-3,8)+R(j,40)),str(R(-3,8)+R(j+1,40)))
              for p in patterns for j in range(30)}
    seen=set();summary={p:10**100 for p in patterns};smallest=10**100
    for row in data['rows']:
        key=(tuple(row['owners']),row['lo'],row['hi'])
        assert key in expected and key not in seen;seen.add(key)
        bound=reconstruct(row);summary[key[0]]=min(summary[key[0]],bound);smallest=min(smallest,bound)
    assert seen==expected
    # 2 atan(3/8)>7/10 follows from atan x>=x-x^3/3.
    assert R(3,8)-R(3,8)**3/3-R(7,20)==R(19,2560)>0
    report={'status':'PASS_FIXED_HAND_POLYNOMIALS_AND_CLOSED_COVER',
      'input_sha256':sha256(raw).hexdigest(),'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
      'owner_patterns':48,'closed_cells_per_pattern':30,'polynomials':len(seen),
      'bernstein_coefficients':5*len(seen),'minimum_printed_coefficient':str(R(smallest,10**12)),
      'pattern_minimum_numerators':[{'owners':list(p),'minimum':summary[p]} for p in sorted(patterns)],
      'meaning':'Under the explicitly stated S<=1/500 and tangent/sign hypotheses, BT and DE have only canonical axes 3 and 4.'}
    OUTPUT.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='pattern_minimum_numerators'},indent=2))
if __name__=='__main__':main()
