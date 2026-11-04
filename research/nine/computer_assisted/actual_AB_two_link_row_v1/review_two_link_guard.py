"""Exact face, complement, and damage controls for the two-link guard helpers."""
from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import json
import two_link_actual_ab_guard as G
import check_two_link_actual_ab_guard as C

def state(t=F(0)):
 centers=[(-F(3,2),-F(1,16)),(-F(1,2),-F(1,16)-t),(F(1,2),-F(17,16)),
          (F(3,2),-F(1,16)),(-1,F(15,16)),(0,F(15,16)),(1,F(15,16)),
          (-F(1,2),-F(17,16)),(F(1,2),-F(1,16))]
 positions=[(F(v),F(v))for center in centers for v in center]
 return dict(positions=positions,angles=[(F(0),F(0))]*9,
             scalar=[(F(1),F(1))]*9+[(F(0),F(0))]*18+[(F(1,2),F(1,2))]*9,differences={})
checks=[]
def check(s,want,label):
 a=G.evaluate(s);b=C.evaluate(s);assert a==b
 assert(a['status']=='PASS_ACTUAL_AB_TWO_LINK_TERMINAL_GUARD')==want
 checks.append(dict(label=label,passed=True,guard_status=a['status']))
for t in (F(0),F(1,4),F(13,50),F(3,5)):
 s=state(t);check(s,True,'aligned_guard_t_'+str(t))
 assert G.reduced_complement(s)==C.reduced_complement(s)
check(state(F(3,5)+F(1,10000)),False,'variation_outside_closed_face')
for field,index,value,label in (
 ('positions',12,(F(5,2),F(5,2)),'strict_dx_equality_rejected'),
 ('positions',13,(-F(1),-F(1)),'wrong_vertical_side_rejected'),
 ('positions',16,(-F(3,4),-F(3,4)),'left_order_rejected'),
 ('positions',16,(F(7,4),F(7,4)),'right_order_rejected')):
 s=state();s[field][index]=value;check(s,False,label)
s=state();s['angles'][3]=(-F(1,100),-F(1,100));s['scalar'][12]=(-F(1,100),-F(1,100));check(s,False,'wrong_D_sign_rejected')
# Algebraic closed-cover identity, independent of any physical feasibility claim.
cover_checks=0
for b,i,d in product([F(-1),-F(3,5),F(0),F(3,5),F(1)],repeat=3):
 w=abs(i-b)+abs(d-i);forms=(d-b,b-d,2*i-b-d,b+d-2*i)
 assert w==max(forms)
 for x in (F(-3,4),F(-1,2),F(0),F(1,2)):
  order=x>=-F(1,2);terminal=order and w<=F(3,5)
  escapes=[x<=-F(1,2)]+[v>=F(3,5)for v in forms]
  assert terminal or any(escapes)
  cover_checks+=1
root=Path(__file__).resolve().parent
report=dict(status='PASS_EXACT_TWO_LINK_GUARDS_AND_CLOSED_COMPLEMENT',guard_controls=len(checks),
            closed_complement_identity_checks=cover_checks,checks=checks,physical_feasibility_of_controls_not_asserted=True,
            theorem_source_binding_required=True,new_original_cells=0,new_masks=0,
            source_sha256={str(Path(p).resolve()):sha256(Path(p).read_bytes()).hexdigest()for p in(__file__,G.__file__,C.__file__)})
(root/'GUARD_COMPLEMENT_REVIEW.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in('checks','source_sha256')}),flush=True)
