"""Fixed rational comparisons for the automatic-slider hand terminal."""
from fractions import Fraction as F
from pathlib import Path
import json

rows=[]
def check(name,x):
    x=F(x)
    assert x>0,(name,x)
    rows.append({'name':name,'positive_reserve':str(x)})

check('sqrt2 exceeds 1.41 by squaring',F(2)-F(141,100)**2)
assert F(1,2)+F(141,100)/24==F(447,800)
check('outer primary below 1.415',F('1.915')**2+F(1,4)-F(9789,2500))
check('T lower projection reserve',F(447,800)-F(3,2000)-F(557,1000))
check('T upper projection reserve',F(1417,1000)-F(283,200)-F(3,2000))
assert -F(283,200)+F(7,5)-F(1,2)==-F(103,200)
check('G upper projection reserve',F(49,125)+F(447,800)-F(29,20)+F(1,2))
w=F(4209,5000)
old=list(map(F,['.01869','.34656','.3112575','.3984975','.0641425','.03072','.021785','.0345425','.0521875']))
loss=[F(0)]*9
for i,x in [(4,'.017'),(5,'.023'),(7,'.022'),(8,'.015')]:loss[i]=F(x)*w
new=[a-b for a,b in zip(old,loss)]
printed=list(map(F,['.01869','.34656','.3112575','.3984975','.0498319','.0113586','.021785','.0160229','.0395605']))
assert new==printed
rho=min(new)
assert rho==F(56793,5000000)
for i,v in enumerate(new):check(f'owner reserve V{i+1}',v)
c2=F(26453303561590200213,2850910772000000000)
c3=F(25398850783,17277200000)+w/F(30)
assert c3==F(5176729803,3455440000)
check('quadratic constant below 9.28',F(232,25)-c2)
check('enlarged cubic constant below 1.5',F(3,2)-c3)
check('remainder below 9.3 S squared',F(93,10)-F(232,25)-F(3,2000))
remainder=rho-F(93,10000)
assert remainder==F(10293,5000000)
check('positive terminal linear coefficient',remainder)
eps=F(19,10**6)
assert 4*eps/F(1,25)==F(19,10000)
check('initial budget mismatch below .004',F(1,250)-4*eps/F(1,25))
final=eps/(F(1,25)*F(49,100))
assert final==F(19,19600)
check('final budget mismatch below .001',F(1,1000)-final)
report={'status':'PASS','scope':'fixed exact arithmetic; continuous derivation in HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md','comparisons':len(rows),'owner_reserves':[str(x) for x in new],'rho':str(rho),'terminal_S_coefficient':str(remainder),'rows':rows}
Path(__file__).with_name('automatic_slider_terminal_arithmetic.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':'PASS','comparisons':len(rows),'rho':str(rho),'terminal_S_coefficient':str(remainder)}))
