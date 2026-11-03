"""Exact closed-weak boundary control; not a strict-mask counterexample."""
from fractions import Fraction as F
from itertools import combinations, product
import json

Q=F(1105,256)
C=[(F(-3,2),F(-1,16)),(F(-1,2),F(-7,32)),
   (F(1,2),F(-17,16)),(F(3,2),F(-1,16)),
   (F(-1),F(15,16)),(F(0),F(15,16)),(F(1),F(15,16)),
   (F(-9,16),F(-41,32)),(F(1,2),F(-1,16))]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
reports=[]
for sign in (-1,):
    u=[(F(1),F(0)) for _ in C]
    u[7]=(F(255,257),sign*F(32,257))
    v=[(-b,a) for a,b in u]
    assert all(dot(x,x)==1 for x in u)
    assert abs(u[7][1]/u[7][0])==F(32,255)>F(1,8)
    h=[(abs(a)+abs(b))/2 for a,b in u]
    corner_reserves=[]
    for i in range(9):
        for s,t in product((-1,1),repeat=2):
            p=tuple(C[i][k]+(s*u[i][k]+t*v[i][k])/2 for k in (0,1))
            reserve=Q-dot(p,p)
            assert reserve>=0,(i,s,t,reserve)
            corner_reserves.append((i,reserve))
    pair_reserves=[]
    for i,j in combinations(range(9),2):
        d=tuple(C[j][k]-C[i][k] for k in (0,1))
        choices=[]
        for n in (u[i],v[i],u[j],v[j]):
            supp=sum(abs(dot(n,w)) for w in (u[i],v[i],u[j],v[j]))/2
            choices.append(abs(dot(n,d))-supp)
        reserve=max(choices)
        assert reserve>=0,(i,j,reserve)
        pair_reserves.append((i,j,reserve))
    bits=[]
    for i,j in ((0,1),(1,2),(2,3),(4,5),(5,6)):
        dx=C[j][0]-C[i][0];dy=C[j][1]-C[i][1]
        assert dx>=abs(dy) and dx>0
        bits.append(int(dx<h[i]+h[j]))
    assert bits==[0,0,0,0,0]
    assert F(17,16)-F(1,2)-h[7]==F(17,4112)>0
    reports.append({
        'H_tilt_sign':sign,'H_tangent':str(u[7][1]/u[7][0]),
        'verified_corners':len(corner_reserves),'verified_pairs':len(pair_reserves),
        'minimum_H_corner_reserve':str(min(r for i,r in corner_reserves if i==7)),
        'minimum_H_pair_reserve':str(min(r for i,j,r in pair_reserves if 7 in (i,j))),
        'marked_bits':bits,'strict_CD_weak_bit':False})
print(json.dumps({'status':'PASS','scope':'Closed-Q physical boundary control; no strict weak mask counterexample','reports':reports},indent=2))
