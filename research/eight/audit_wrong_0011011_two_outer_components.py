"""Independent exact coefficient and coarse-reserve checks for two hand notes.

The continuous identities/coverage are reviewed in the accompanying audit
manuscripts. This deliberately does not reuse either companion's arithmetic
class, derivative functions, or label constants.
"""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json

P=Path(__file__).resolve().parent;SRC=P.parents[1]/'proof_integration'
labels=json.loads((SRC/'wrong_0011011_labels.json').read_text())
rows=labels['independent_roles'];den=labels['denominator'];assert den==100000
expected={('0','O+'):[2478,0,93015,2363,-11055],('1','O+'):[0,-26,83194,-11864,17627],('1','O-'):[0,-26,83194,-11864,17627],('4','O+'):[3965,0,385510,-149748,-189442],('4','O-'):[0,-2112,29090,0,44642],('3','O+'):[0,-1025,16031,0,63457]}
for key,v in expected.items():assert rows[key[0]][key[1]]==v
checks=[]
def pos(name,value):
 value=F(value);assert value>0,(name,value);checks.append({'name':name,'strict_reserve':str(value)})
q=F(9789,2500)
pos('P fourth derivative coarse numerator',2*F('3.9')-2*F('1.4')**2)
pos('L global derivative completion',F('.6248')-F('.0311')**2/4-F('.6245'))
pos('L low-source contact derivative',1-F('.817')*F('1.215'))
qs=q+1-2*F('1.85');h=F('.928')-(q-F('1.915'))/(F('1.85')*qs);k=F('.5')*F('.255')/(F('1.915')*qs)
assert h>0
pos('L target-small contact ratio after squaring',k*k-h*h*qs)
pos('global f1 lower complete square',q-(1+F('.84')*(q+1))**2/(8*F('.84')))
pos('L target-large contact ratio',F('.84')+F('.7')*F('.255')/(F('1.915')*F('2.118')*F('1.456'))-F('.869'))
pos('L source-diagonal contact derivative',F('1.16')**2*(q-2*F('1.415')-F('.16'))-1)
pos('L target-zero high-source curvature',F('1.67')*(q-2*F('1.415')-F('.16'))-F('1.176')*F('.4')-1)
pos('L target-zero value completion',F('.8977797')-F('.000003')**2/2-F('.89777'))
pos('P E decreasing first interval',F('.876')**3-F('.45'))
pos('P E decreasing second interval',F('.903')**3+3*F('.2')*F('.903')**2*F('.293')-F('.779'))
pos('P negative Hessian determinant first interval',(F('.404')*F('.876')**3)**2-F('.187')*F('.386'))
pos('P negative Hessian determinant second interval',(F('.378')*F('.918')**3)**2-F('.124')*F('.386'))
for lo,hi,bp,bpp in [('.107','.2','.915','.151'),('.2','.3','.914','.190'),('.3','.4','.919','.217'),('.4','.5','.924','.238'),('.5','.6','.924','.251'),('.6','.7','.924','.248')]:
 pos('P diagonal cost curvature '+lo+':'+hi,F('.329')*F(bp)**2-F('1.082')*F(bpp)-F('.009'))
pos('P diagonal boundary completion',F('.89777605')-F('.000001')**2/F('.018')-F('.89777604'))
pos('P upper-angle boundary completion',F('.89778868')-F('.00001')**2/F('.658')-F('.89778867'))
for name,p,t in [('R','-.01025','.63457'),('K','-.02112','.44642')]:
 pos(name+' global concavity',2*F(t)*F('.261')-abs(F(p))*q/F('1.399')**3)
constant_lower=-F('.03137')*F('1.415')
pos('quarter late-angle lower',F('.943')+constant_lower-F('.8986'))
pos('quarter large-sum lower',F('3.14159')/2-F('.7')+constant_lower+F('.16')-F('.986'))
pos('quarter scalar derivative norm',1-F('.4')**2-(F('.8')*F('1.415')-F('.4'))**2)
pos('quarter small-sum primary impossibility',1-(F('1.415')-F('1.35')*F('.587')+F('.2')))
pos('quarter conclusion target',F('.8986')-F(17953,20000))

records=[]
for stem,expected_count in [('same_outer_zero',133),('positive_negative_outer_quarter',17)]:
 note='WRONG_0011011_'+stem.upper()+'_HAND_PROOF.md';checker='verify_wrong_0011011_'+stem+'_hand.py';record='wrong_0011011_'+stem+'_hand_arithmetic.json'
 x=json.loads((SRC/record).read_text());assert str(x['status']).startswith('PASS');count=x.get('comparison_count',len(x['checks']));assert count==expected_count
 records.append({'scope':stem,'companion_comparisons':count,'sha256':{n:sha256((SRC/n).read_bytes()).hexdigest() for n in [note,checker,record]}})
out={'status':'PASS','scope':'Independent exact label binding and coarse scalar/Hessian/completion comparisons for both reviewed0011011 outer components','independent_comparisons':len(checks),'checks':checks,'records':records,'label_sha256':sha256((SRC/'wrong_0011011_labels.json').read_bytes()).hexdigest()}
(P/'wrong_0011011_two_outer_components_independent_arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','independent_comparisons':len(checks),'companion_replays':[133,17]},indent=2))
