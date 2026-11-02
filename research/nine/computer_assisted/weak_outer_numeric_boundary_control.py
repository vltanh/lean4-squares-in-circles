#!/usr/bin/env python3
"""Exact rational actual-boundary nine-square control; no mask closure.

All nine squares are axis-aligned. This is a Q-attaining 000/00 packing,
not a 001/00 example: the final main gap equals the sum of halfwidths.
Its weak-outer-limit transverse gap is 97/240 > 2/5.
"""
from fractions import Fraction as F
from itertools import combinations,product
import json

Q=F(1105,256)
CENTERS=[(-F(3,2),-F(1,16)),(-F(1,2),-F(1,16)),
         (F(1,2),-F(7,15)),(F(3,2),-F(1,16)),
         (-F(1),F(15,16)),(F(0),F(15,16)),(F(1),F(15,16)),
         (F(2,15),-F(22,15)),(-F(13,15),-F(17,16))]

def verify():
    corner_reserves=[]
    for x,y in CENTERS:
        corner_reserves.append(min(Q-(x+F(s,2))**2-(y+F(t,2))**2 for s,t in product((-1,1),repeat=2)))
    assert min(corner_reserves)==0
    pair_reserves=[]
    for i,j in combinations(range(9),2):
        dx=abs(CENTERS[j][0]-CENTERS[i][0]);dy=abs(CENTERS[j][1]-CENTERS[i][1])
        pair_reserves.append(max(dx,dy)-1)
    assert min(pair_reserves)>=0
    for i,j in ((0,1),(1,2),(2,3),(4,5),(5,6)):
        dx=CENTERS[j][0]-CENTERS[i][0];dy=CENTERS[j][1]-CENTERS[i][1]
        assert dx>=abs(dy) and dx>=1
    gap=CENTERS[3][1]-CENTERS[2][1]
    assert gap==F(97,240)>F(2,5)>F(1,3)>F(9,32)>F(7,30)
    return {'claim':'exact all-nine closed-Q actual-boundary control',
            'mask':'000/00','weak_outer_mask':False,'corner_count':36,'pair_count':36,
            'gap':str(gap),'corner_reserves':[str(x) for x in corner_reserves],
            'minimum_pair_reserve':str(min(pair_reserves)),
            'centers':[[str(x),str(y)] for x,y in CENTERS]}

if __name__=='__main__':print(json.dumps(verify(),indent=2))
