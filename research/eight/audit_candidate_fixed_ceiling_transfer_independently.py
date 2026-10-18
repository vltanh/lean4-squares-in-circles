"""Independent fixed-scalar and identity audit of the final capture transfer."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
BASE=HERE if (HERE/'HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md').exists() else HERE.parents[1]/'proof_integration'
NAMES=['HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md',
       'HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md',
       'HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md',
       'CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH_HAND_MANIFEST.json']
checks=[]
def positive(name,x):
    x=F(x);assert x>0;checks.append({'comparison':name,'positive_difference':str(x)})
qminus=F(7831,2000);Q1=F(1957767069,500000000);Q0=F(9789,2500)
positive('qminus above5/2',qminus-F(5,2))
positive('Q1 aboveqminus',Q1-qminus)
positive('coarseQ0 aboveQ1',Q0-Q1)
positive('4 abovecoarseQ0',4-Q0)
positive('outer radius4/5 test',F(5,2)-(F(4,5)**2+F(3,2)*F(4,5)+F(1,2)))
positive('outer radius3/2 test',F(3,2)**2+F(3,2)+F(1,2)-4)
positive('B less than3/2 by squared comparison',F(3,2)**2-2)
assert 1+4*F(5,2)-2==9 and 2+4*4-2==16
positive('core bodyradiusbelow4/5',F(43,30)**2-2)
assert F(43,30)/2+F(1,12)==F(4,5)
assert F(1,2)/F(4,5)==F(5,8)
assert F(8,15)/4-F(1,3)==-F(1,5)
assert F(1,6)-F(5,8)/5==F(1,24)
assert F(1,5)/F(3,2)==F(2,15)
assert F(2,15)/4==F(1,30)
positive('mixed-signOOmonotonicity',F(1,24))
positive('coreoutermonotonicity',F(1,30))
eps=F(1,1000)
positive('quarter threshold dominatesfinalmismatch',F(3,200)-eps)
positive('zero-axis threshold dominatesquarter',F(2,5)-F(3,200))
rho=F(56793,5000000)
assert rho-F(93,10)*eps==F(10293,5000000)
positive('automaticterminalremainingangularcoefficient',rho-F(93,10)*eps)
offsets=[-1,-1,0,0,1,1,2]
quarters=[offsets[i+1]-offsets[i] for i in range(6)]+[offsets[0]+4-offsets[6]]
assert quarters==[0,1,0,1,0,1,1]
owners=[[1,3],[1],[1,3],[3,4],[1,3],[3,4],[2]]
count=1
for x in owners:count*=len(x)
assert count==32
assert sum([1545,729,1239])==3513 and 5*3513==17565
manifest_hash=sha256((BASE/NAMES[-1]).read_bytes()).hexdigest()
assert manifest_hash=='dd0146dd4262476704293ad8928921d15e5184212490d7eb8c9406e7b7bf8bf6'
out={'status':'PASS','scope':'Independent continuous interface review with exact scalar and labeling checks; preceding geometric and finite-table theorems are explicit imports',
     'fixed_strict_comparisons':len(checks),'checks':checks,'quarter_word':quarters,
     'allowed_owner_assignments':count,'final_mismatch':'1/1000',
     'fixed_capture_package_sha256':manifest_hash,
     'sha256':{n:sha256((BASE/n).read_bytes()).hexdigest() for n in NAMES}}
(HERE/'candidate_fixed_ceiling_transfer_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
