"""Independent Fraction reconstruction of the five printed M/H polynomial rows."""
from fractions import Fraction as F
from math import comb, factorial, isqrt
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent
NOTE = BASE / "MID_HIGH_WHOLE_PAIR_HAND_PROOF.md"

def trim(p):
    p = list(p)
    while len(p) > 1 and not p[-1]: p.pop()
    return p

def add(*pp):
    p = [F(0)] * max(map(len, pp))
    for q in pp:
        for j, c in enumerate(q): p[j] += c
    return trim(p)

def scale(p, c): return trim([x * c for x in p])

def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for j, x in enumerate(p):
        for k, y in enumerate(q): r[j+k] += x*y
    return trim(r)

def trig(degree, sine):
    p = [F(0)] * (degree + 1)
    for j, k in enumerate(range(int(sine), degree+1, 2)):
        p[k] = F((-1)**j, factorial(k))
    return trim(p)

def bernstein_direct(p, lo, hi, basis_degree):
    # Direct conversion in the requested degree, including degree 20 for row 2.
    power = [sum((p[j] * comb(j, k) * lo**(j-k) * (hi-lo)**k
                  for j in range(k, len(p))), F(0)) for k in range(len(p))]
    return [sum((power[j] * F(comb(k, j), comb(basis_degree, j))
                 for j in range(min(k+1, len(power)))), F(0))
            for k in range(basis_degree+1)]

printed = {}
for line in NOTE.read_text().splitlines():
    parts = [x.strip() for x in line.split('|')]
    if len(parts) == 6 and parts[1] in {'1','2','3','4','5'} and '/' in parts[3]:
        printed[int(parts[1])] = [int(x.strip()) for x in parts[4].split(',')]
assert len(printed) == 5

Q, u, v, k, q, gamma = map(F, ('9789/2500','.089293','.480179','1.534906','.045313','.8926'))
Rlo, Rhi = F('2.79842813'), F('2.79842814')
a0hi, a2lo, a2hi = Rhi-1, F('1.62343405'), F('1.62343407')
b2lo, b2hi = a2lo*F('.6'), a2hi*F('.6')
cmlo = F('3.14159')/4 + F('2.143075')
LMlo = cmlo-k*a2hi+q*b2lo
X = [F(0),F(1)]
rows = []

for no, lo, hi, sigma, lam0, lam1, degree in (
    (1,'.1','.42',1,'.66','-.4',14),
    (2,'.4','.6',-1,'.64','-.365',20)):
    lam = list(map(F,(lam0,lam1)))
    A = add(scale(lam,1+a2lo-b2hi),[F('-.09')])
    B = add(scale(lam,1-a2hi-b2hi),[F('-.09')])
    constant = F('.09')+LMlo-gamma-sigma*u*(Rhi if sigma>0 else Rlo)
    T = add(X,[constant],scale(lam,2),mul(A,trig(6,False)),mul(B,trig(5,True)))
    V = add(mul(add(lam,[-sigma*u]),add(lam,[-sigma*u])),
            mul(add(lam,[-v]),add(lam,[-v])))
    P = add(mul(T,T),scale(V,-2*Q))
    rows.append((no,F(lo),F(hi),degree,P))

for no, lo, hi, lamtext, circle in ((3,'.42','.61','.43',False),
                                  (4,'.6','.7','.42',True),
                                  (5,'.7','.93','.4',True)):
    lam=F(lamtext)
    if circle:
        z=(u+lam)**2+(v-lam)**2
        ns=F(isqrt(z.numerator*10**20//z.denominator)+1,10**10)
        assert ns*ns>z
        K=F('.09')+cmlo+k+2*lam+u*Rlo-Rhi*ns-gamma
    else:
        K=F('.09')+cmlo+k+lam-lam*a0hi-gamma
    T=add(X,[K],scale(trig(7,True),2*lam-F('.09')),scale(trig(8,False),F('-.09')))
    V=add([k*k+q*q+2*lam*lam],scale(trig(9,True),2*lam*(k-q)),
          scale(trig(10,False),-2*lam*(k+q)))
    rows.append((no,F(lo),F(hi),16,add(mul(T,T),scale(V,-2*Q))))

report=[]
for no, lo, hi, degree, P in rows:
    bb=bernstein_direct(P,lo,hi,degree)
    assert len(bb)==len(printed[no])
    assert all(b>F(n,10**8)>0 for b,n in zip(bb,printed[no]))
    report.append({'row':no,'polynomial_degree':len(P)-1,
                   'basis_degree':degree,'coefficients':len(bb),
                   'least_printed_bound':str(F(min(printed[no]),10**8))})
assert sum(r['coefficients'] for r in report)==87
print(json.dumps({'status':'PASS','rows':report,'strict_printed_bounds':87},indent=2))
