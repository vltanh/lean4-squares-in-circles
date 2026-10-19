"""Independent exact reconstruction of the 140 scalar hand inequalities.

The author checker is not imported. Fractions, interval coefficient arithmetic,
and a triangular Bernstein-basis elimination are implemented here. No state
sampling, optimizer, or adaptive domain subdivision is used.
"""
from fractions import Fraction as F
from math import isqrt, comb, factorial
from pathlib import Path
from hashlib import sha256
import json, subprocess, tempfile, shutil, re

ROOT=Path('/workspace/scratch/6ea6bf046677')
SOURCE_DIR=ROOT/'global_attack/hand_conversion'
OUT=ROOT/'m5_agent/hand_conversion'
table=json.loads((SOURCE_DIR/'short_quarter_scalar_hand_table.json').read_text())
record=json.loads((SOURCE_DIR/'short_quarter_scalar_hand_arithmetic.json').read_text())
labels=json.loads((SOURCE_DIR/'short_hand_labels.json').read_text())
def I(a):
    if isinstance(a,tuple): return a
    v=F(a); return (v,v)
def add(a,b):
    a,b=I(a),I(b); return (a[0]+b[0],a[1]+b[1])
def neg(a):
    a=I(a); return (-a[1],-a[0])
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    a,b=I(a),I(b); v=[x*y for x in a for y in b]; return min(v),max(v)
def div(a,b):
    b=I(b); assert not b[0]<=0<=b[1]
    return mul(a,(1/b[1],1/b[0]))
def sqrt(a):
    a=I(a); assert a[0]>=0
    scale=10**14
    n=isqrt(a[0].numerator*scale**2//a[0].denominator)
    m=isqrt(a[1].numerator*scale**2//a[1].denominator)+1
    return F(n,scale),F(m,scale)
def pa(a,b):
    return [add(a[j] if j<len(a) else 0,b[j] if j<len(b) else 0) for j in range(max(len(a),len(b)))]
def ps(a,c): return [mul(x,c) for x in a]
def pn(a): return [neg(x) for x in a]
def pm(a,b):
    out=[I(0) for _ in range(len(a)+len(b)-1)]
    for j,x in enumerate(a):
        for k,y in enumerate(b):out[j+k]=add(out[j+k],mul(x,y))
    return out
def pc(x):return [I(x)]
def pp(a,n):
    out=pc(1)
    for _ in range(n):out=pm(out,a)
    return out
def pd(a,b):return pa(a,pn(b))
def bernstein_by_elimination(coefficients,left,right):
    # Horner substitution of u=left+(right-left)z.
    z=[]
    for q in reversed(coefficients):
        v=[F(0)]*(len(z)+1)
        for j,x in enumerate(z):
            v[j]+=left*x;v[j+1]+=(right-left)*x
        v[0]+=q;z=v
    n=len(coefficients)-1
    assert len(z)==n+1
    # Successively remove the lowest monomial in B_kn(z).
    remaining=z[:]; result=[]
    for k in range(n+1):
        v=remaining[k]/comb(n,k);result.append(v)
        for j in range(n-k+1):
            remaining[k+j]-=v*comb(n,k)*comb(n-k,j)*(-1)**j
    assert all(x==0 for x in remaining)
    return result
def atan(q,n):return sum((F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n+1)),F(0))
pi=(F('3.141592653589793238'),F('3.141592653589793239'))
assert pi[0]<16*atan(5,25)-4*atan(239,6)
assert 16*atan(5,24)-4*atan(239,7)<pi[1]
Q=F(9789,2500);R=sqrt(Q);d=sub(sqrt(Q/2),F(1,2));a0=sub(sqrt(Q-F(1,4)),F(1,2))
r0=div(F(1,2),add(a0,F(1,2)));p2=div(pi,2)
# Expand the radical identity independently as a polynomial in x=sqrt(v),
# after setting h=1 by homogeneity.
def poly_mul(a,b):
    o=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):o[i+j]+=x*y
    return o
identity=poly_mul(poly_mul(poly_mul([-1,1],[-1,1]),poly_mul([-1,1],[-1,1])),[5,4,1])
assert identity==[5,-16,15,0,-5,0,1]
sinp=[I(0)]*10;cosp=[I(0)]*11
for j in range(4):sinp[2*j+1]=I(F((-1)**j,factorial(2*j+1)))
sinp[9]=(F(0),F(1,factorial(9)))
for j in range(5):cosp[2*j]=I(F((-1)**j,factorial(2*j)))
cosp[10]=(F(-1,factorial(10)),F(0))
assert table['Q']=='9789/2500' and len(table['rows'])==140
assert table['gamma_by_edge']=={'2':'.8975','4':'.89765','5':'.89765','6':'.89765'}
polynomial_count=coefficient_count=0;worst_cost=None;printed_bounds=0;rows=[]
for index,row in enumerate(table['rows']):
    edge,ss,st,axis=row['original']
    cs,psrc,qsrc=[F(v,100000) for v in labels[edge]['O']['p' if ss==1 else 'n']]
    ct,ptgt,qtgt=[F(v,100000) for v in labels[(edge+1)%7]['O']['p' if st==1 else 'n']]
    c=cs-ct
    if axis in (2,3):
        p,q,P,t=-ptgt,qtgt,-psrc,qsrc
        ss,st=-st,-ss
    else:p,q,P,t=psrc,qsrc,ptgt,qtgt
    axis=1 if axis in (1,3) else 4
    lam=F(row['lam']);sgn=F(row['r']);left=F(row['lo']);right=F(row['hi'])
    assert lam>=0 and sgn in (-1,1) and 0<=left<right<=F('.7')
    assert row['mode'] in ('axial','diagonal','endpoints','circle')
    Xs=p if axis==1 else p-lam
    Ys=ss*(q-lam) if axis==1 else ss*q
    axial=mul(Xs,a0);diagonal=mul(Xs+Ys,d)
    if Xs>=0:
        source=min(axial[0],diagonal[0]);source_mode='concave endpoint minimum'
    elif sub(Ys,mul(Xs,r0))[0]>=0 and Ys-Xs>=0:
        source=axial[0];source_mode='axial monotone minimum'
    elif sub(mul(Xs,r0),Ys)[0]>=0 and Xs-Ys>=0:
        source=diagonal[0];source_mode='diagonal monotone minimum'
    else:
        source=sub(-(Xs+Ys)/2,mul(R,sqrt(Xs*Xs+Ys*Ys)))[0];source_mode='whole-circle lower bound'
    assert source>=F(row['source_lower'])
    if axis==1:
        X=pd(pc(-P),ps(cosp,lam))
        Y=ps(pd(pc(-t),ps(sinp,sgn*lam)),st)
        v=pa(pc(P*P+t*t+lam*lam),pa(ps(cosp,2*lam*P),ps(sinp,2*lam*sgn*t)))
    else:
        X=pd(pc(-P),ps(sinp,sgn*lam))
        Y=ps(pd(ps(cosp,lam),pc(t)),st)
        v=pa(pc(P*P+t*t+lam*lam),pa(ps(sinp,2*lam*sgn*P),ps(cosp,-2*lam*t)))
    premises=[]
    if row['mode']=='axial':premises=[pd(Y,ps(X,r0)),pd(Y,X)]
    elif row['mode']=='diagonal':premises=[pd(ps(X,r0),Y),pd(X,Y)]
    elif row['mode']=='endpoints':premises=[X]
    base=pa(pc(add(add(p2,c),row['source_lower'])),
            pa([I(0),I(sgn)],ps(pa(pc(1),pa(cosp,sinp)),lam/2)))
    if row['mode']=='axial':targets=[ps(X,a0)]
    elif row['mode']=='diagonal':targets=[ps(pa(X,Y),d)]
    elif row['mode']=='endpoints':targets=[ps(X,a0),ps(pa(X,Y),d)]
    else:
        h=F(row['t']);assert h>0
        major=pa(pc(5*h/16),pa(ps(v,15/(16*h)),pa(ps(pp(v,2),-5/(16*h**3)),ps(pp(v,3),1/(16*h**5)))))
        targets=[pd(ps(pa(X,Y),F(-1,2)),ps(major,R))]
    gamma=F('.8975') if edge==2 else F('.89765')
    costs=[pd(pa(base,z),pc(gamma)) for z in targets]
    report=record['results'][index]
    assert report['index']==index and report['original']==row['original']
    assert report['sign']==int(sgn) and list(map(F,report['interval']))==[left,right]
    assert F(report['lambda'])==lam and report['target_mode']==row['mode']
    assert report['source_mode']==source_mode
    assert F(report['source_lower'])<=source
    values=[]
    for kind,polys,reports in [('premise',premises,report['premises']),('cost',costs,report['cost'])]:
        assert len(polys)==len(reports)
        for poly,claim in zip(polys,reports):
            b=bernstein_by_elimination([v[0] for v in poly],left,right)
            polynomial_count+=1;coefficient_count+=len(b)
            assert claim['degree']==len(b)-1
            assert len(claim['coefficient_lower'])==len(b)
            assert claim['method']=='positive Bernstein coefficients'
            for coefficient,printed in zip(b,claim['coefficient_lower']):
                assert coefficient>=F(printed),(index,kind,'printed coefficient mismatch',coefficient,F(printed))
                printed_bounds+=1
            m=min(b)
            if kind=='cost':
                assert m>0 and m>=F(claim['reserve'])
                worst_cost=m if worst_cost is None else min(m,worst_cost)
            else:assert m>=0
            values.append({'kind':kind,'degree':len(b)-1,'minimum':str(m)})
    rows.append({'index':index,'source_mode':source_mode,'source_bound_verified':True,'polynomials':values})
assert polynomial_count==310 and coefficient_count==printed_bounds==4475
assert worst_cost>F('.000094')
# Exact branch inventory, independent of the author's assembly script.
quarters=[2,4,5,6]
cases=set()
for edge in quarters:
    source_signs=[1] if edge==0 else [-1] if edge==2 else [-1,1]
    target=(edge+1)%7
    target_signs=[1] if target==0 else [-1] if target==2 else [-1,1]
    for s in source_signs:
        for t in target_signs:
            for ax in [1,2,3,4]:cases.add((edge,s,t,ax))
assert len(cases)==48
hard={(2,-1,-1,3),(2,-1,-1,4),(4,-1,-1,3),(4,-1,-1,4),(6,1,1,1),(6,1,1,2)}
assert {tuple(x['original']) for x in table['rows']}==cases
chains=0
for case in cases:
    for side in [-1,1]:
        begin=F(0)
        if case in hard:
            begin=F('.3' if case[3] in (1,3) else '.03') if side<0 else F('.1' if case[3] in (1,3) else '.06')
        selected=sorted((r for r in table['rows'] if tuple(r['original'])==case and r['r']==side),key=lambda r:F(r['lo']))
        assert selected
        for r in selected:
            assert F(r['lo'])==begin;begin=F(r['hi'])
        assert begin==F('.7');chains+=1
assert chains==96
# Literal manuscript/table binding, including every displayed decimal reserve.
lines=(SOURCE_DIR/'SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF.md').read_text().splitlines()
md=[line.split('|')[1:-1] for line in lines if re.match(r'^\| \d+ \|',line)]
assert len(md)==140
for index,(cells,row) in enumerate(zip(md,table['rows'])):
    cells=[x.strip() for x in cells]
    assert int(cells[0])==index+1
    e,s,t,a=row['original'];assert cells[1]==f"{e} {('+' if s==1 else '-')+('+' if t==1 else '-')} {a}"
    assert int(cells[2])==row['r']
    assert list(map(F,cells[3][1:-1].split(',')))==[F(row['lo']),F(row['hi'])]
    assert F(cells[4])==F(row['lam']) and F(cells[5])==F(row['source_lower'])
    assert cells[6]=={'axial':'A','diagonal':'D','endpoints':'E','circle':'N'}[row['mode']]
    if row['mode']=='circle':assert F(cells[7])==F(row['t'])
    minimum=min(F(x['minimum']) for x in rows[index]['polynomials'] if x['kind']=='cost')
    assert minimum>=F(cells[8])>0
# Isolated author replay, and run the separate finite-union assembly unchanged.
replay=Path(tempfile.mkdtemp(prefix='m5_short_scalar_audit_'))
for name in ['verify_short_quarter_scalar_hand.js','short_hand_labels.json','short_quarter_scalar_hand_table.json']:
    shutil.copy2(SOURCE_DIR/name,replay/name)
run=subprocess.run(['node',str(replay/'verify_short_quarter_scalar_hand.js')],capture_output=True,check=True)
assert not run.stderr
assert run.stdout==(SOURCE_DIR/'short_quarter_scalar_hand_arithmetic.json').read_bytes()
(replay/'replayed_arithmetic.json').write_bytes(run.stdout)
assembly=subprocess.run(['python3',str(SOURCE_DIR/'audit_short_whole_word_hand.py')],capture_output=True,check=True)
assert not assembly.stderr
assembly_json=json.loads(assembly.stdout);assert assembly_json['status']=='PASS'
names=['SHORT_WRONG_WORD_OUTER_QUARTER_SCALAR_HAND_PROOF.md','verify_short_quarter_scalar_hand.js',
       'short_quarter_scalar_body.js','short_quarter_scalar_hand_table.json',
       'short_quarter_scalar_hand_arithmetic.json','short_hand_labels.json',
       'SHORT_WRONG_WORD_OUTER_QUARTER_ALIGNED_HAND_PROOF.md',
       'SHORT_WRONG_WORD_COMPLETE_HAND_EXCLUSION.md','audit_short_whole_word_hand.py']
report={'status':'PASS','scope':'Independent continuous scalar-support audit, Fraction coefficient reconstruction by triangular Bernstein elimination, literal table binding, and complete 96 angle-chain union',
'rows':140,'polynomials':polynomial_count,'coefficient_comparisons':coefficient_count,
'printed_coefficient_lower_bounds_verified':printed_bounds,'angle_chains':chains,'whole_outer_quarter_cases':48,
'weakest_exact_cost_coefficient':str(worst_cost),'weakest_cost_exceeds':'.000094',
'author_replay':'byte-identical','replay_directory':str(replay),
'whole_word_assembly':assembly_json,
'sha256':{n:sha256((SOURCE_DIR/n).read_bytes()).hexdigest() for n in names},
'independent_checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
'rows_reconstructed':rows}
(OUT/'short_quarter_scalar_independent_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('rows_reconstructed','sha256','whole_word_assembly')},indent=2))

