#!/usr/bin/env python3
"""Exact diameter check for the all-frame boundary-control hand lemma.

This is a finite arithmetic companion, not an unrestricted packing proof.
Only Fraction arithmetic is used. The hand proof covers every frame and
all labelings without angular sampling or a chosen witness extractor.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json
from weak_outer_numeric_boundary_control import CENTERS as BOUNDARY_CENTERS

Q=F(1105,256)
CANONICAL_CENTERS=[(F(x,2),-F(1,16)) for x in (-3,-1,1,3)]
CANONICAL_CENTERS += [(F(x),F(15,16)) for x in (-1,0,1)]
CANONICAL_CENTERS += [(F(x,2),-F(17,16)) for x in (-1,1)]
OBLIQUE_CENTERS=[(F(x,2),F(1,16)) for x in (-3,-1,1,3)]
OBLIQUE_CENTERS += [(F(x),-F(15,16)) for x in (-1,0,1)]
OBLIQUE_CENTERS += [(F(x,20),F(19,16)) for x in (-11,11)]


def check(name,centers):
    corners=[Q-(x+F(s,2))**2-(y+F(t,2))**2
             for x,y in centers for s,t in product((-1,1),repeat=2)]
    diffs=[(abs(x-X),abs(y-Y)) for (x,y),(X,Y) in combinations(centers,2)]
    assert len(centers)==9 and len(corners)==36 and len(diffs)==36
    assert min(corners)==0
    assert min(max(dx,dy)-1 for dx,dy in diffs)>=0
    dx=max(d[0] for d in diffs);dy=max(d[1] for d in diffs)
    l1=max(sum(d) for d in diffs)
    assert dx<=3 and dy<3 and l1<4
    return {'control':name,'status':'PASS','corner_count':36,'pair_count':36,
            'minimum_corner_reserve':str(min(corners)),
            'diameter_x':str(dx),'diameter_y':str(dy),'diameter_l1':str(l1),
            'quadratic_coefficient_reserves':[str(3-dx),str(4-l1),str(3-dy)],
            'consequence':'No 001 or 100 main witness in any frame or labeling; no v restriction.',
            'centers':[[str(x),str(y)] for x,y in centers]}


def check_oblique():
    centers=OBLIQUE_CENTERS
    axes=[(F(1),F(0))]*7+[(F(99,101),F(20,101))]*2
    squares=[]
    for (x,y),(a,b) in zip(centers,axes):
        assert a*a+b*b==1
        squares.append([(x+(s*a-t*b)/2,y+(s*b+t*a)/2)
                        for s,t in product((-1,1),repeat=2)])
    corner_reserves=[Q-x*x-y*y for sq in squares for x,y in sq]
    assert min(corner_reserves)==0
    for i,j in combinations(range(9),2):
        directions=[]
        for k in (i,j):
            a,b=axes[k];directions += [(a,b),(-b,a)]
        reserves=[]
        for a,b in directions:
            p=[a*x+b*y for x,y in squares[i]]
            q=[a*x+b*y for x,y in squares[j]]
            reserves.append(max(min(q)-max(p),min(p)-max(q)))
        assert max(reserves)>=0
    nonendpoint_squared=max(sum((x-y)**2 for x,y in zip(centers[i],centers[j]))
                            for i,j in combinations(range(9),2) if (i,j)!=(0,3))
    assert nonendpoint_squared==F(29,4)
    # (2+1/sqrt(2))^2=9/2+2sqrt(2)>29/4 follows from sqrt(2)>11/8.
    assert F(2)-F(11,8)**2>0
    inner=[1,2,4,5,6,7,8];table=[];survivors=[]
    for b in inner:
        row=[]
        for c in inner:
            if b==c:
                row.append(None);continue
            edges=[tuple(centers[j][k]-centers[i][k] for k in range(2))
                   for i,j in ((0,b),(b,c),(c,3))]
            least=min(sum(x*y for x,y in zip(v,w)) for v,w in combinations(edges,2))
            row.append(str(least))
            if least>=0:survivors.append([0,b,c,3])
        table.append(row)
    assert survivors==[[0,1,2,3]]
    return {'control':'oblique Q-attaining construction','status':'PASS',
            'corner_count':36,'pair_count':36,
            'maximum_non_AD_squared_distance':str(nonendpoint_squared),
            'radical_comparison_squared_reserve':str(F(2)-F(11,8)**2),
            'inner_table_labels':['B','C','E','F','G','H','I'],
            'minimum_edge_pair_dot_product':table,
            'surviving_A_D_cone_chains':survivors,
            'consequence':'No one-weak/two-actual main witness in any frame or labeling.'}

if __name__=='__main__':
    print(json.dumps({'scope':'Exact boundary-control arithmetic only; no fixed-mask closure.',
                      'controls':[check('numeric boundary control',BOUNDARY_CENTERS),
                                  check('three-row 4+3+2 construction',CANONICAL_CENTERS),
                                  check_oblique()]},indent=2))
