"""Independent reconstruction of the eight printed low/middle support rows."""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
from subprocess import check_output
import json
import re

BASE = Path(__file__).resolve().parent
if not (BASE / 'LOW_MID_WHOLE_PAIR_HAND_PROOF.md').exists():
    BASE = BASE.parent / 'm5_agent' / 'hand_conversion'
NOTE = BASE / 'LOW_MID_WHOLE_PAIR_HAND_PROOF.md'

def trim(p):
    p=list(p)
    while len(p)>1 and not p[-1]: p.pop()
    return p

def add(*args):
    p=[F(0)]*max(map(len,args))
    for q in args:
        for j,x in enumerate(q): p[j]+=x
    return trim(p)

def scale(p,a): return trim([a*x for x in p])

def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for j,a in enumerate(p):
        for k,b in enumerate(q): r[j+k]+=a*b
    return trim(r)

def trig(degree,sine):
    p=[F(0)]*(degree+1)
    for j,k in enumerate(range(int(sine),degree+1,2)):
        p[k]=F((-1)**j,factorial(k))
    return trim(p)

def bernstein(p,l,h,n):
    # Direct conversion in the declared basis degree, including degree
    # elevation from the true degree 16 to degree 18 in the fourth row.
    return [sum((p[j]*comb(j,t)*l**(j-t)*(h-l)**t
                 *F(comb(k,t),comb(n,t))
                 for t in range(min(k+1,len(p)))
                 for j in range(t,len(p))),F(0))
            for k in range(n+1)]

printed={}
tfloors={}
for line in NOTE.read_text().splitlines():
    if not line.startswith('|'): continue
    parts=[p.strip() for p in line.split('|')]
    if len(parts)==5 and parts[1].isdigit() and parts[2].isdigit():
        if re.fullmatch(r'[0-9, ]+',parts[3]) and ',' in parts[3]:
            printed[int(parts[1])]=(int(parts[2]),[int(x) for x in parts[3].split(',')])
    if len(parts)==8 and parts[1].isdigit():
        tfloors[int(parts[1])]=F(parts[6])
assert set(printed)==set(tfloors)==set(range(1,9))

Q=F('9789/2500')
mu,q,p,v=map(F,('.403875','1.089065','1.489593','1.580219'))
labels={'L':(mu,q,-mu*F('1.414575670')),
        'M':(p,v,F('-2.143075'))}
rows=[
    ('M','f',1,'.76','1.4',[F('.945')],[F('-.00001')]),
    ('M','f',1,'1','1.58',[F('.98')],[F('-.00004')]),
    ('M','f',2,'1.57','1.71',[F('.98')],[F('-.00004')]),
    ('L','f',1,'.4','.79',[F('1.146'),F('-.335')],None),
    ('M','e',1,'1.5','1.58',[F('.9')],None),
    ('M','e',2,'1.57','1.71',[F('.9')],None),
    ('L','e',1,'1.3','1.58',[F('.94')],None),
    ('L','e',2,'1.57','1.71',[F('.94')],None)]

report=[]
for no,(kind,axis,quad,lo,hi,lam,source) in enumerate(rows,1):
    pt,qt,ct=labels[kind]
    if no==4: source=add([F('.4555')],scale(lam,-F('.513966884')))
    elif no in (5,6): source=add([F('-.30683')],scale(lam,-F('1.298747249')))
    elif no in (7,8): source=add([F('-.455511')],scale(lam,-F('1.199256062')))
    Bs=add(lam,[F('-.09')]) if axis=='f' else [F('-.09')]
    Bc=[F('-.09')] if quad==1 else add(scale(lam,-1),[F('.09')])
    T=add([F('.09')-ct+(pt+qt)/2-F('.9005'),F(1)],source,
          scale(lam,F('.5')),mul(Bs,trig(7 if axis=='f' else 9,True)),
          mul(Bc,trig(8,False)))
    V=add([pt*pt+qt*qt],mul(lam,lam))
    if axis=='f':
        V=add(V,scale(mul(lam,add(scale(trig(9,True),pt),
                                 scale(trig(10,False),-qt))),F(2)))
    else:
        V=add(V,scale(mul(lam,add(scale(trig(10,False),pt),
                                 scale(trig(7,True),qt))),F(-2)))
    P=add(mul(T,T),scale(V,-Q))
    degree,pp=printed[no]
    bb=bernstein(P,F(lo),F(hi),degree)
    assert len(bb)==len(pp)
    assert all(b>F(n,10**6)>0 for b,n in zip(bb,pp))
    tb=bernstein(T,F(lo),F(hi),degree//2)
    assert all(t>tfloors[no]>0 for t in tb)
    report.append({'row':no,'polynomial_degree':len(P)-1,
                   'bernstein_degree':degree,'P_coefficients':len(bb),
                   'T_coefficients':len(tb),
                   'least_printed_P_bound':str(F(min(pp),10**6))})

replay=json.loads(check_output(['node',str(BASE/'verify_low_mid_whole_pair_hand.js')],text=True))
assert replay['status']=='PASS' and replay['comparison_count']==305
assert all(c['pass'] for c in replay['checks'])
print(json.dumps({'status':'PASS','rows':report,
                  'P_coefficient_bounds':sum(r['P_coefficients'] for r in report),
                  'positive_T_bounds':sum(r['T_coefficients'] for r in report),
                  'separate_javascript_comparisons':305},indent=2))
