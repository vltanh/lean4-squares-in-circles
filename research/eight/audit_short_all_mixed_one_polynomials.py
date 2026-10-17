"""Independent reconstruction of the printed polynomial rows in the 0010111
mixed quarter-one hand proof. Uses Fraction arithmetic and triangular
Bernstein basis elimination, independently of the author's JS conversion.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json, re, hashlib

BASE=Path('/workspace/scratch/6ea6bf046677')
source=BASE/'global_attack/hand_conversion/verify_short_all_mixed_one_hand.js'
note=BASE/'global_attack/hand_conversion/SHORT_WRONG_WORD_ALL_MIXED_ONE_HAND_PROOF.md'
replay=Path('/tmp/short_all_mixed_one_independent_replay.json')
report=json.loads(replay.read_text())
assert report['status']=='PASS' and report['fixed_comparisons']==390
data=json.loads(re.search(r'const input=(.*);\n\nconst checks=',source.read_text()).group(1))
labels=BASE/'global_attack/hand_conversion/short_hand_labels.json'
assert data['labels']==json.loads(labels.read_text()),'embedded labels differ from frozen role table'
def add(a,b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
def scale(a,k): return [x*F(k) for x in a]
def sub(a,b): return add(a,scale(b,-1))
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def power(a,k):
    z=[F(1)]
    for _ in range(k): z=mul(z,a)
    return z
def series(degree,cos=False):
    a=[F(0)]*(degree+1)
    for j in range(0 if cos else 1,degree+1,2):
        a[j]=F((-1)**((j-(0 if cos else 1))//2),factorial(j))
    return a
def bern(a,l,h):
    l,h=F(l),F(h);w=h-l;n=len(a)-1
    # First compose the monomial polynomial with l+(h-l)t.
    c=[F(0)]*(n+1)
    for i,x in enumerate(a):
        for k in range(i+1): c[k]+=x*comb(i,k)*l**(i-k)*w**k
    # Then solve the defining Bernstein basis identity coefficient by coefficient.
    b=[]
    for k in range(n+1):
        previous=sum((b[i]*comb(n,i)*comb(n-i,k-i)*(-1)**(k-i) for i in range(k)),F(0))
        b.append((c[k]-previous)/comb(n,k))
    return b
tables={t['name']:t for t in report['tables'] if 'coefficient_lower' in t}
rows=[]
def check(name,P,l,h):
    bs=bern(P,l,h);printed=tables[name]['coefficient_lower']
    assert len(bs)==len(printed)
    for x,s in zip(bs,printed): assert x>0 and x>=F(s),(name,x,s)
    rows.append({'name':name,'degree':len(P)-1,'coefficients_checked':len(bs),'minimum_exact':str(min(bs))})
Q=F('3.9156');SL=series(7);SU=series(9);CL=series(10,True)
for i in [4,12,19,23]:
    z=data['norm']['Of'][i]
    c,p,q,g=(F(z[k],100000) for k in ['cd','p','q','g'])
    A=c+(-p+q+g)/2-F('.898')
    T=add(add(mul([A,F(1)],SL),[g]),scale(CL,F(13,12)*g))
    V=add(add([g*g],scale(SL if p>=0 else SU,-2*g*p)),scale(power(SU,2),p*p+q*q))
    check(f'Of {i} side positive T',T,'.87','1.571')
    check(f'Of {i} side squared radical majorant',sub(power(T,2),scale(V,Q)),'.87','1.571')
X=[F(0),F(1)];Xm1=[F(-1),F(1)];T2=sub([Q],power(X,2))
E=sub(scale(sub([F('1.12479')],power(Xm1,2)),Q),mul(mul(X,Xm1),T2))
A=[F('.65')/F('.767')-F('.253'),F('.253')]
P=sub(power(E,2),mul(power(A,2),power(T2,3)))
check('endpoint curvature E',E,'1.32','1.7')
check('endpoint curvature A',A,'1.32','1.7')
check('endpoint curvature squared bound',P,'1.32','1.7')
out={
 'status':'PASS',
 'scope':'Independent reconstruction of all printed side and common-curvature polynomial coefficients; original 390-comparison replay also passed.',
 'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'manuscript_sha256':hashlib.sha256(note.read_bytes()).hexdigest(),
 'replay_sha256':hashlib.sha256(replay.read_bytes()).hexdigest(),
 'polynomial_rows':len(rows),
 'coefficients_checked':sum(r['coefficients_checked'] for r in rows),
 'rows':rows
}
outpath=BASE/'m5_agent/hand_conversion/short_all_mixed_one_independent_polynomial_audit.json'
outpath.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','polynomial_rows','coefficients_checked','source_sha256','manuscript_sha256']}))
