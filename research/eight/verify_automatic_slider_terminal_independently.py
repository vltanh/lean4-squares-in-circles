"""Independent fixed arithmetic and binding for the automatic-slider terminal."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import subprocess

BASE=Path(__file__).resolve().parent
ROOT=BASE.parent
paths=[
    BASE/'HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md',
    BASE/'verify_automatic_slider_terminal.py',
    ROOT/'proof_reference/HAND_EXACT_CENTER_SQUARE_COMPLETION.md',
    ROOT/'proof_reference/HUMAN_BROAD_TERMINAL_ARITHMETIC.md',
    BASE/'CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md',
]
bound={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
       for p in paths}
record=BASE/'automatic_slider_terminal_arithmetic.json'
before=record.read_bytes()
subprocess.run(['python',str(BASE/'verify_automatic_slider_terminal.py')],
               check=True,capture_output=True,text=True)
assert before==record.read_bytes()
bound[str(record.relative_to(ROOT))]=hashlib.sha256(record.read_bytes()).hexdigest()
checks=[]
def positive(name,value):
    value=F(value)
    assert value>0,(name,value)
    checks.append({'name':name,'strict_reserve':str(value)})

Q=F(9789,2500);w=F(4209,5000);S=F(1,1000)
amin=F(1,2)+F(141,100)/24
amax=F(283,200)
positive('sqrt2 lower bound',2-F(141,100)**2)
positive('primary upper bound at zero secondary',(amax+F(1,2))**2+F(1,4)-Q)
positive('T lower endpoint from center rotation',amin-F(3,2)*S-F(557,1000))
positive('T upper endpoint from center rotation',F(1417,1000)-amax-F(3,2)*S)
assert -amax+F(7,5)-F(1,2)==-F(103,200)
positive('G upper endpoint from primary and h2',F(49,125)-(-amin+F(29,20)-F(1,2)))

# Reconstruct the old nine reserves from the original midpoint table.
centers=list(map(F,['.0345','.3633','.3211','.4102','.0760','.0425','.0238','.0371','.0549']))
derivatives=list(map(F,['2.04','2.16','1.27','1.51','1.53','1.52','.26','.33','.35']))
old=[c-F(31,4000)*d for c,d in zip(centers,derivatives)]
# The smooth coefficients are affine in exactly these two projections.
loss=[F(0),F(0),F(0),F(0),
      F(1417,1000)-F(7,5),
      F(29,50)-F(557,1000),
      F(0),
      F(49,125)-F(37,100),
      -F(1,2)+F(103,200)]
new=[v-w*d for v,d in zip(old,loss)]
printed=list(map(F,['.0186900','.3465600','.3112575','.3984975','.0498319','.0113586','.0217850','.0160229','.0395605']))
assert new==printed
for i,value in enumerate(new):
    positive('enlarged owner reserve '+str(i+1),value)
rho=min(new)
assert rho==F(56793,5000000)

# Rebuild both remainders from their constituent force/support/slider terms.
X1=F(17649,10000);X4=F(19049,10000)
Y2=F(221,200);X3=F(6793,5000);H1=F(14263,10000)
z=F(81,1000);smin=F(40,401)
smax=2*z/(1+z*z);cmin=(1-z*z)/(1+z*z);tanmax=2*z/(1-z*z)
c2=w*X4/(2*smin)+w*X1*tanmax/2+w*smax/2+w/2+3*w/4
c3=w*(X1/cmin+Y2+X3+H1)/6+w/6+w/6+w/2
assert c2==F(26453303561590200213,2850910772000000000)
assert c3==F(5176729803,3455440000)
positive('quadratic remainder below 9.28',F(232,25)-c2)
positive('cubic remainder below 1.5',F(3,2)-c3)
positive('remainder at S=.001 below 9.3',F(93,10)-c2-c3*S)
coefficient=rho-F(93,10)*S
assert coefficient==F(10293,5000000)
positive('strict final coefficient',coefficient)

eps=F(19,10**6);beta=F(1,25)
first=4*eps/beta
positive('first mismatch in the Taylor range',F(1,250)-first)
positive('Taylor slope at d=.004 above .49',
         F(1,2)-F(1,1000)-F(1,750000)-F(49,100))
second=eps/(beta*F(49,100))
assert second==F(19,19600)
positive('second mismatch below .001',S-second)

out={'status':'PASS',
     'scope':'independent arithmetic and byte-identical replay; continuous review is in the bound audit note',
     'checks':checks,'comparison_count':len(checks),
     'bindings':bound,'owner_reserves':[str(v) for v in new],
     'C2':str(c2),'C3':str(c3),'terminal_coefficient':str(coefficient)}
(BASE/'automatic_slider_terminal_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','comparisons':len(checks),'terminal_coefficient':str(coefficient)}))
