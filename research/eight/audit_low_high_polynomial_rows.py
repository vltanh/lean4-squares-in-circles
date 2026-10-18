"""Independent Fraction reconstruction of the six printed L/H rows.

This reads the displayed coefficients from the manuscript, rebuilds its
polynomials from the displayed formulas, and converts them to Bernstein
form independently of the JavaScript arithmetic replay.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
from subprocess import check_output
import json
import re

BASE = Path(__file__).resolve().parent
NOTE = BASE / "LOW_HIGH_WHOLE_PAIR_HAND_PROOF.md"

def trim(p):
    p = list(p)
    while len(p) > 1 and not p[-1]:
        p.pop()
    return p

def add(*pp):
    p = [F(0)] * max(map(len, pp))
    for q in pp:
        for j, c in enumerate(q):
            p[j] += c
    return trim(p)

def scale(p, c):
    return trim([x * c for x in p])

def mul(p, q):
    r = [F(0)] * (len(p) + len(q) - 1)
    for j, x in enumerate(p):
        for k, y in enumerate(q):
            r[j+k] += x*y
    return trim(r)

def compose(p, x):
    r = [F(0)]
    for c in reversed(p):
        r = add(mul(r, x), [c])
    return r

def trig(degree, sine):
    p = [F(0)] * (degree + 1)
    for j, k in enumerate(range(int(sine), degree+1, 2)):
        p[k] = F((-1)**j, factorial(k))
    return trim(p)

def bernstein(p, lo, hi):
    n = len(p)-1
    # Directly combine the affine substitution and power-to-Bernstein map.
    return [sum((p[j] * comb(j, t) * lo**(j-t) * (hi-lo)**t
                 * F(comb(k, t), comb(n, t))
                 for t in range(k+1) for j in range(t, n+1)), F(0))
            for k in range(n+1)]

note = NOTE.read_text()
printed = []
for line in note.splitlines():
    if not line.startswith('|'):
        continue
    final = line.split('|')[-2].strip()
    if re.fullmatch(r'[0-9, ]+', final) and final.count(',') >= 8:
        printed.append([int(z.strip()) for z in final.split(',')])
block = note.split('### 8.2.', 1)[1].split('### 8.3.', 1)[0]
numbers = re.search(r'\\begin\{gathered\}(.*?)\\end\{gathered\}', block, re.S)
assert numbers is not None
printed.insert(2, [int(z) for z in re.findall(r'\d+', numbers.group(1))])
assert [len(x) for x in printed] == [17,17,15,9,11,11]

Q, mu, q, k, v, goal = map(F, ('9789/2500','.403875','1.089065',
                               '.569472','.390886','.8833'))
X = [F(0), F(1)]
rows = []
for lo, hi, lam in (('.08','.11',[F('.960358')]),
                    ('.11','.46',[F('1.005'),F('-.407')])):
    const = (F('.09') + F('3.14159')/4 + mu*F('1.414575670')
             + (mu+q)/2 - goal)
    T = add(X, [const], scale(lam, F('.5')-F('.899214066')),
            mul(add(lam,[F('-.09')]),trig(7,True)),
            scale(trig(8,False),F('-.09')))
    V = add([mu*mu+q*q],mul(lam,lam),
            scale(mul(lam,add(scale(trig(9,True),mu),
                              scale(trig(10,False),-q))),F(2)))
    rows.append((F(lo),F(hi),10**8,add(mul(T,T),scale(V,-Q))))

cHlo = F('3.14159')/4+(k-v)*F('.899214065')
T = add(X,[F('.09')+F('.5')+cHlo+(k-v)/2-goal],
        scale(add(trig(7,True),trig(6,False)),F('.91')))
V = add([k*k+v*v+1],scale(trig(9,True),2*k),
        scale(trig(6,False),-2*v))
rows.append((F('.3'),F('.8'),10**8,add(mul(T,T),scale(V,-Q))))

lam = [F('.990906'),F('-.28')]
w = [F('-.19'),F(1)]
U1 = add(compose(list(map(F,('.7895001401','-.1939323304','.0258329638',
                             '.0063465589','.0011353387'))),w),[F('.000003')])
U2 = add(compose(list(map(F,('.6048369308','.9594403346','-.2050884018',
                             '-.0610720222','.0449392223'))),w),[F('.000001')])
e = F('.00000003')
S, C = trig(9,True),trig(8,False)
X1 = add([k*k],mul(add(lam,[-v]),add(lam,[-v])))
X2 = add([mu*mu+q*q],mul(lam,lam),
         scale(mul(lam,add(scale(S,mu),scale(C,-q))),F(2)))
Vc = add(X,scale(C,F('-.09')),
         mul(add(lam,[F('-.09')]),add(S,[-e])),lam,
         [F('3.14159')/4+(k-v)*F('.899214')+mu*F('1.414575')
          +(k-v+mu+q+F('.18'))/2-goal],
         scale(add(U1,U2),-F('1.978788')))
for P in (add(mul(U1,U1),scale(X1,-1)),
          add(mul(U2,U2),scale(X2,-1),[-3*e]),Vc):
    rows.append((F('.3'),F('.77'),10**10,P))

report = []
for no, ((lo,hi,den,P), pp) in enumerate(zip(rows,printed),1):
    bb = bernstein(P,lo,hi)
    assert len(bb) == len(pp)
    assert all(b > F(n,den) > 0 for b,n in zip(bb,pp))
    report.append({'row':no,'degree':len(P)-1,'coefficients':len(bb),
                   'least_printed_bound':str(F(min(pp),den))})
assert sum(r['coefficients'] for r in report) == 80

replay = json.loads(check_output(
    ['node', str(BASE / 'verify_low_high_whole_pair_hand.mjs')], text=True))
assert replay['status'] == 'PASS' and replay['comparison_count'] == 232
section9 = note.split('## 9.',1)[1].split('All constants are bracketed',1)[0]
endpoint_bounds = []
for line in section9.splitlines():
    if line.startswith('|'):
        text = line.split('|')[-2].strip()
        if re.fullmatch(r'\d*\.\d+',text):
            endpoint_bounds.append(F(text))
assert len(endpoint_bounds) == len(replay['support']['endpoints']) == 16
assert all(bound*10**8 == int(row['lower_numerator_over_1e8'])
           for bound,row in zip(endpoint_bounds,replay['support']['endpoints']))
print(json.dumps({'status':'PASS','rows':report,
                  'strict_printed_bounds':80,'endpoint_transcriptions':16,
                  'separate_javascript_comparisons':232},indent=2))
