"""Fixed rational arithmetic for the proved candidate hand interfaces.

No sampled geometry, root search, optimizer, or adaptive subdivision is used.
The continuous geometric and budget arguments are in the companion note.
"""
import json
from fractions import Fraction as F
from pathlib import Path

rows=[]
def positive(name,x):
    x=F(x)
    assert x>0,(name,x)
    rows.append({'name':name,'positive_reserve':str(x)})

Q=F(9789,2500)
a=F(349,250)
positive('outer upper endpoint above Q',(a+F(1,2))**2+(a/F(20)+F(1,2))**2-Q)
positive('outer lower endpoint below 39/10',F(39,10)-(F(13,12)**2+(F(4,5)*F(7,12)+F(1,2))**2))
positive('coarse tangent on core side',F(6,7)-F(4,5))
positive('T projected lower reserve',F(7,12)-F(3,1000)-F(29,50))
positive('T projected upper reserve',F(7,5)-a-F(3,1000))
positive('G projected lower reserve',-a+F(7,5))
positive('G projected upper reserve',F(37,100)+F(7,12)-F(29,20)+F(1,2))
positive('sqrt2 exceeds 7/5 by squared comparison',F(2)-F(7,5)**2)
positive('16/5 exceeds 22/7',F(16,5)-F(22,7))
eps=F(19,10**6)
initial=4*eps/F(1,50)
assert initial==F(19,5000)
positive('initial mismatch below 1/250',F(1,250)-initial)
positive('Taylor mismatch slope exceeds .49',F(1,2)-F(1,1000)-F(1,750000)-F(49,100))
final=eps/(F(1,50)*F(49,100))
assert final==F(19,9800)
positive('final mismatch below 1/500',F(1,500)-final)
k=[0,1,0,1,0,1,1]
permutation=[(5-i)%7 for i in range(7)]
assert permutation==[5,4,3,2,1,0,6]
assert [k[(4-i)%7] for i in range(7)]==k
assert sum(k)==4
owners=[[1,3],[1],[1,3],[3,4],[1,3],[3,4],[2]]
count=1
for x in owners:count*=len(x)
assert count==32
report={'status':'PASS','scope':'fixed arithmetic and exact indexing only; whole-domain candidate pair premises remain open','comparisons':len(rows),'reflection_permutation':permutation,'quarter_word':k,'allowed_owner_assignments':count,'rows':rows}
out=Path(__file__).with_name('candidate_word_hand_interfaces_arithmetic.json')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'comparisons':len(rows),'allowed_owner_assignments':count}))
