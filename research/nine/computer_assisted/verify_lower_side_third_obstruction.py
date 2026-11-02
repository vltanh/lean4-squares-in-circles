#!/usr/bin/env python3
"""Exact six-square obstruction to the unsupported local -1/3 bound.

This is not a nine-square packing or a counterexample to the target theorem.
It prevents use of a false strengthening of the one-sided main-height gate.
"""
from fractions import Fraction as F
import json
from verify_lower_side_main_17_50 import I

Q=F(1105,256);lam=F(1000001,1000000)
root=I(901).rt();a=30/root;b=1/root;h=(a+b)/2
assert 30**2+1==901
aligned=((I(1),I(0)),(I(0),I(1)))
clockwise=((a,-b),(b,a))
data=[
 ('M0',(-1-h,I(0)),aligned),
 ('M1',(I(F(-1,2)),I(F(-67,200))),clockwise),
 ('M2',(h,I(0)),aligned),
 ('M3',(1+h,I(0)),aligned),
 ('L',(I(F(-1,2)),I(F(7,10))),aligned),
 ('B',(I(F(-29,60)),I(F(-2673,2000))),clockwise),
]
units=[(name,tuple(lam*z for z in center),frame)for name,center,frame in data]
def dot(x,y):return x[0]*y[0]+x[1]*y[1]
def support(n,frame):return (dot(n,frame[0]).ab()+dot(n,frame[1]).ab())/2
circle_reserves=[]
for name,center,frame in units:
    for su in (-1,1):
        for sv in (-1,1):
            corner=tuple(center[j]+(su*frame[0][j]+sv*frame[1][j])/2 for j in range(2))
            reserve=Q-(corner[0].sq()+corner[1].sq()).hi
            assert reserve>0,(name,su,sv,str(reserve))
            circle_reserves.append(reserve)
pair_reserves=[]
for i,(name,center,frame) in enumerate(units):
    for other,other_center,other_frame in units[i+1:]:
        gap=tuple(other_center[j]-center[j]for j in range(2))
        reserve=max((dot(n,gap).ab()-support(n,frame)-support(n,other_frame)).lo for n in frame+other_frame)
        assert reserve>0,(name,other,str(reserve))
        pair_reserves.append(reserve)
main_reserves=[];cone_reserves=[]
for i in range(3):
    _,p,frame=units[i];_,q,other_frame=units[i+1]
    gap=tuple(q[j]-p[j]for j in range(2))
    reserve=(gap[0]-support((I(1),I(0)),frame)-support((I(1),I(0)),other_frame)).lo
    assert reserve>0
    cone=(gap[0]-gap[1].ab()).lo;assert cone>0
    main_reserves.append(reserve);cone_reserves.append(cone)
assert units[1][1][1].hi<-F(1,3)
assert units[4][1][0].hi<-F(29,60) and units[5][1][0].hi<-F(29,60)
assert units[4][1][1].lo>units[1][1][1].hi>units[5][1][1].hi
assert min(circle_reserves)>F(1,100000)
assert min(pair_reserves)>F(999,1000000000)
report={'result':'PASS','scope':'Six original squares strictly in Q with an actual/cone main four-chain and both full-side outsiders; middle main below -1/3. This is not a nine-square counterexample.',
    'main_height':str(lam*F(-67,200)),
    'center_expansion':str(lam),
    'corner_count':len(circle_reserves),'pair_count':len(pair_reserves),
    'uniform_corner_squared_reserve':'1/100000',
    'uniform_pair_and_main_gap_reserve':'999/1000000000',
    'arithmetic':'Fraction intervals and outward 80-bit radicals; all 24 original corners and all 15 original pairs checked'}
print(json.dumps(report,indent=2))
