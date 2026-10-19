"""Independent fixed rational review of the complete 0011011 core/core row."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
from hashlib import sha256
import json,subprocess,tempfile

HERE=Path(__file__).resolve().parent
BASE=HERE.parent if (HERE.parent/'proof_integration').is_dir() else HERE
SRC=BASE/'proof_integration' if (BASE/'proof_integration').is_dir() else HERE
note=SRC/'WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md'
author=SRC/'verify_wrong_0011011_core_core_hand.py'
report=SRC/'wrong_0011011_core_core_hand_arithmetic.json'
labels_file=SRC/'wrong_0011011_labels.json'
with tempfile.TemporaryDirectory() as tmp:
    p=Path(tmp)/author.name
    p.write_bytes(author.read_bytes())
    replay=subprocess.run(['python',str(p)],check=True,capture_output=True)
    regenerated=Path(tmp)/report.name
    assert regenerated.read_bytes()==report.read_bytes()
    j=json.loads(regenerated.read_text())
    assert j['status']=='PASS' and j['strict_comparisons']==52

checks=[]
def positive(name,x):
    x=F(x);assert x>0,(name,str(x))
    checks.append({'name':name,'strict_reserve':str(x)})
def at(x,n):
    x=F(x);return sum(((-1)**j*x**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
plo=16*at('1/5',6)-4*at('1/239',3)
phi=16*at('1/5',5)-4*at('1/239',2)
positive('Machin lower exceeds3.14',plo-F('3.14'))
positive('Machin upper below355/113',F('355/113')-phi)
sl,sh=F('1.41421356237'),F('1.41421356238')
positive('square root lower',2-sl*sl)
positive('square root upper',sh*sh-2)
dl,dh=F('.5')+sl/24,F('.5')+sh/24
vlow,vhigh=3-2*sh,3-2*sl
positive('whole side atan minimum',vlow-vhigh**3/3-(1+vhigh)/7-F('1/400'))
positive('corner convex numerator',3-F('7/6'))
positive('core side squared radius',F('16/25')-F('7/12')**2-F('.25'))
positive('core corner squared radius',F('16/25')-F('.5')-sh/12-F('1/144'))
cos_lower=sum(((-1)**j*F('27/20')**(2*j)/F(factorial(2*j)) for j in range(6)),F(0))
positive('core pair1.35 angle contradiction',1-F('32/25')*(1-cos_lower))
positive('core nonaffine corner correction',F('.05334')/4-F('.34492')/30)
positive('two-zero strict local sign',F('.82')-phi/4)

data=json.loads(labels_file.read_text())
assert data['denominator']==100000 and data['Q']=='9789/2500'
assert data['gamma']=='17953/20000'
roles={int(i):v for i,v in data['independent_roles'].items()}
for i,row in list(roles.items()):
    new={kind+s:row[kind+('-' if s=='+' else '+')] for kind in 'CO' for s in '+-'}
    j=(2-i)%7
    if j in roles:assert new==roles[j]
    else:roles[j]=new
assert set(roles)==set(range(7))
psi={}
for i in range(7):
    for sign in '+-':
        c,p,g,z,ab=[F(n,100000) for n in roles[i]['C'+sign]]
        assert ab==0 and 0<g<F('8/7')
        if p==0 and z==0:
            low,high=-c,phi/4-c-g*dl
        else:
            assert (p,z)==(F('-.34492'),F('-.05334'))
            c0=c+p*F('7/12')
            low,high=-c0,phi/4-c0-g*dl-z*dh**2
        psi[i,sign]=(low,high) if sign=='+' else (-high,-low)

rows=[
 (0,'++','.95147'),(0,'+-','.91004'),(2,'-+','1.36323'),
 (2,'--','1.11609'),(3,'--','1.06188'),(3,'-+','1.28108'),
 (3,'+-','1.02374'),(3,'++','1.08303'),(4,'++','.97610'),
 (4,'+-','.93867')]
for edge,signs,bound in rows:
    lower=F('27/20')-psi[edge,signs[0]][1]+psi[(edge+1)%7,signs[1]][0]
    if (edge,signs)==(3,'+-'):
        lower=plo/2-F('.7')-F('.01449')+F('.16823')
    positive('independent core row '+str(edge)+signs,lower-F(bound))
    positive('core row strict reserve '+str(edge)+signs,F(bound)-F('.91'))
    # The entire printed row, including signs, must occur unchanged.
    assert '| '+str(edge)+' | '+signs+' | '+chr(96)+bound+chr(96)+' |' in note.read_text()
positive('core table exceeds gamma',F('.91')-F(data['gamma']))
out={
 'status':'PASS','scope':'All ten canonical core/core cases; complete core side/corner lemma and angle proof reviewed.',
 'author_replay_count':52,'independent_comparison_count':len(checks),
 'bindings':{str(p.relative_to(BASE)):sha256(p.read_bytes()).hexdigest()
             for p in (note,author,report,labels_file)},
 'independent_checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
 'checks':checks}
Path(__file__).with_name('wrong_0011011_all_core_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ('status','author_replay_count','independent_comparison_count')}))
