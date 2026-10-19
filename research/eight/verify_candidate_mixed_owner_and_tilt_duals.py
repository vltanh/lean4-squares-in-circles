"""Fixed rational arithmetic for the three conditional capture lemmas.

The input consists only of finite rational constants.  All polynomial
coefficients and every closed interval cover are reconstructed.  No floating
point, optimizer, search, subdivision, or external proof program is used.
"""
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json

BASE=Path(__file__).resolve().parent
SPECS={
 'quarter':('candidate_quarter_owner_large_mismatch_dual_data.json',R(9789,2500),R(3,200)),
 'mixed':('candidate_mixed_owner_dual_data.json',R(9789,2500),R(1,10000)),
 'tilt':('candidate_tilt_dual_data.json',R(1957767069,500000000),R(1,100000)),
}

def add(*polys):
    out=[R(0)]*max(map(len,polys))
    for p in polys:
        for i,c in enumerate(p):out[i]+=c
    return out
def mul(p,q):
    out=[R(0)]*(len(p)+len(q)-1)
    for i,c in enumerate(p):
        for j,d in enumerate(q):out[i+j]+=c*d
    return out
def scale(p,c):return [c*x for x in p]

def sat(owners,positive,epsilon):
    D=[R(1),R(0),R(1)];S=[R(0),R(2)];C=[R(1),R(0),-R(1)];Z=[R(0)]
    signs=(1,-1,1,-1,1,-1,-1);out=[]
    for i,axis in enumerate(owners):
        j=(i+1)%7
        sine,cosine=((Z,D) if i in (0,2,4) else (D,Z) if i in (3,5)
                     else (C,S) if i==1 else (C,scale(S,-1)))
        row=[Z[:] for _ in range(14)]
        def put(j,p,c=1):row[j]=add(row[j],scale(p,R(c)))
        if axis==1:
            put(7+i,D,signs[i]);put(j,sine);put(7+j,cosine,-signs[j])
        elif axis==2:
            put(i,cosine,-1);put(7+i,sine,signs[i]);put(j,D)
        elif axis==3:
            put(i,sine);put(7+i,cosine,signs[i]);put(7+j,D,-signs[j])
        else:
            assert axis==4
            put(i,D);put(j,cosine,-1);put(7+j,sine,-signs[j])
        out.append(row)
    W=scale(add(D,C,scale(S,1 if positive else -1)),R(1,2))
    rhs=[scale(D,1-R(3,2)*epsilon) for _ in range(7)]
    rhs[1]=W;rhs[6]=add(W,scale(D,-2*epsilon))
    return D,out,rhs

def cones():
    low=(R(1,2),R(1,20),0,0,R(1,20),R(1,2),0)
    high=(1,R(4,5),1,1,R(4,5),1,1)
    rows=[];rhs=[]
    for i in range(7):
        floor=R(7,12) if i in (1,4) else R(447,800)
        ceiling=R(349,250) if i in (1,4) else R(283,200)
        for entries,b in [({i:R(1)},floor),({i:-R(1)},-ceiling),
          ({i:-R(low[i]),7+i:R(1)},R(0)),
          ({i:R(high[i]),7+i:-R(1)},R(0)),({7+i:-R(1)},-R(9,10))]:
            row=[R(0)]*14
            for j,c in entries.items():row[j]+=c
            rows.append(row);rhs.append(b)
    return rows,rhs

def reconstruct(row,Q,epsilon):
    lo,hi=R(row['lo']),R(row['hi'])
    assert lo<hi and (hi<=0 or lo>=0)
    D,A,b=sat(row['owners'],lo>=0,epsilon);K,v=cones()
    lam=[R(n,10**8) for n in row['lambda']]
    mu=[R(n,10**8) for n in row['mu']]
    assert len(lam)==len(mu)==7 and all(n>=0 for n in lam) and all(n>0 for n in mu)
    assert all(isinstance(n,int) for n in row['lambda']+row['mu'])
    kap=[R(0)]*35;seen=set()
    for j,n in row['cone']:
        assert isinstance(j,int) and isinstance(n,int) and 0<=j<35 and j not in seen and n>0
        seen.add(j);kap[j]=R(n,10**8)
    force=[add(scale(D,sum(kap[h]*K[h][j] for h in range(35))),
               *[scale(A[i][j],lam[i]) for i in range(7)]) for j in range(14)]
    linear=add(scale(D,sum(kap[h]*v[h] for h in range(35))),
               *[scale(b[i],lam[i]) for i in range(7)],
               *[scale(c,R(1,2)) for c in force])
    P=add(mul(D,linear),scale(mul(D,D),-Q*sum(mu)),
          *[scale(add(mul(force[i],force[i]),mul(force[7+i],force[7+i])),
                  -1/(4*mu[i])) for i in range(7)])
    assert len(P)<=5;P+=[R(0)]*(5-len(P));width=hi-lo
    power=[sum(P[n]*comb(n,j)*lo**(n-j)*width**j for n in range(j,5)) for j in range(5)]
    coeff=[sum(power[j]*R(comb(i,j),comb(4,j)) for j in range(i+1)) for i in range(5)]
    # Independently convert the resulting Bernstein expansion back to powers.
    assert [sum(coeff[i]*comb(4,i)*comb(4-i,j-i)*(-1)**(j-i)
                for i in range(j+1)) for j in range(5)]==power
    printed=row['bernstein_lower_numerators']
    assert len(printed)==5 and all(isinstance(n,int) and n>0 for n in printed)
    assert all(c>=R(n,10**12) for c,n in zip(coeff,printed))
    return min(printed)

def expected_patterns(mode):
    if mode=='quarter':
        return {(1,g,1,b,1,d,h) for b,d,g,h in
                product((1,3),(1,3),range(1,5),range(1,5)) if (b,d)!=(3,3)}
    if mode=='mixed':
        return {(1,g,1,3,1,3,h) for g,h in product(range(1,5),repeat=2) if (g,h)!=(1,2)}
    return {(1,1,1,3,1,3,2)}

def check(mode):
    filename,Q,epsilon=SPECS[mode];raw=(BASE/filename).read_bytes();data=json.loads(raw)
    assert data['mode']==mode and R(data['Q'])==Q and R(data['epsilon'])==epsilon
    assert data['denominator']==10**8 and data['bernstein_denominator']==10**12
    assert data['degree']==4 and data['strengthened_slider_primary_cones'] is True
    assert data['unresolved']==[]
    patterns=expected_patterns(mode);assert len(patterns)=={'quarter':48,'mixed':15,'tilt':1}[mode]
    intervals={p:[] for p in patterns};bounds={p:10**100 for p in patterns};seen=set()
    for row in data['rows']:
        p=tuple(row['owners']);lo,hi=R(row['lo']),R(row['hi']);key=(p,lo,hi)
        assert p in patterns and key not in seen;seen.add(key)
        intervals[p].append((lo,hi));bounds[p]=min(bounds[p],reconstruct(row,Q,epsilon))
    tails=[(-R(3,8),R(3,8))] if mode!='tilt' else [(-R(3,8),R(1001,20000)),(R(2,25),R(3,8))]
    for p,chain in intervals.items():
        chain.sort();offset=0
        for left,right in tails:
            current=left
            while offset<len(chain) and chain[offset][0]<right:
                a,b=chain[offset];assert a==current and b<=right
                current=b;offset+=1
            assert current==right
        assert offset==len(chain)
    # All extra geometric rational comparisons used by the companion note.
    assert R(2)>R(141,100)**2
    assert (R(283,200)+R(1,2))**2+R(1,4)>R(9789,2500)
    assert (R(9,10)+R(1,2))**2+(R(9,10)+R(1,2))**2>R(9789,2500)
    assert R(4,5)*R(7,12)<R(1,2)
    assert (R(349,250)+R(1,2))**2+(R(349,5000)+R(1,2))**2>R(9789,2500)
    assert R(3,8)-R(3,8)**3/3>R(7,20)
    assert 2*(R(1001,20000)-R(1001,20000)**3/3)>R(1,10)
    assert 2*R(2,25)==R(4,25)
    report={'status':'PASS_FIXED_HAND_POLYNOMIALS_AND_CLOSED_COVER','mode':mode,
      'Q':str(Q),'epsilon':str(epsilon),'input_sha256':sha256(raw).hexdigest(),
      'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
      'owner_patterns':len(patterns),'polynomials':len(seen),'bernstein_coefficients':5*len(seen),
      'minimum_printed_coefficient':str(R(min(bounds.values()),10**12)),
      'pattern_minimum_numerators':[{'owners':list(p),'minimum':bounds[p],
                                  'closed_cells':len(intervals[p])} for p in sorted(patterns)]}
    name=filename.replace('_data.json','_arithmetic.json')
    (BASE/name).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='pattern_minimum_numerators'},indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=(*SPECS,'all'),default='all',nargs='?')
    args=ap.parse_args()
    for mode in SPECS if args.mode=='all' else [args.mode]:check(mode)
