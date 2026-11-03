"""Exact guarded affine rows from the three-original strip theorem.

The physical theorem is subject to its separate hand proof and review.
This module derives only its parent guard and secant consequences.
"""
from fractions import Fraction as F
from itertools import combinations,permutations

def three_square_rows(differences):
    def interval(i,j,axis):
        if i<j:return tuple(map(F,differences[(i,j)][axis]))
        lo,hi=map(F,differences[(j,i)][axis]);return -hi,-lo
    result=[];guards=[]
    for triple in combinations(range(9),3):
        for transverse in (0,1):
            longitudinal=1-transverse
            w=max(max(abs(x) for x in interval(i,j,transverse)) for i,j in combinations(triple,2))
            if w>F(7,10):continue
            order=next((p for p in permutations(triple) if interval(p[0],p[1],longitudinal)[0]>=0 and interval(p[1],p[2],longitudinal)[0]>=0),None)
            if order is None:continue
            lo,mid,hi=order;a,b=interval(lo,hi,transverse)
            floor=min(F(2),F(208,75)-F(29,15)*w);coef=F(5,14)*(a+b)
            co={2*lo+longitudinal:F(1),2*hi+longitudinal:F(-1),2*lo+transverse:coef,2*hi+transverse:-coef}
            name=f'three_square_strip_{lo}_{mid}_{hi}_{transverse}'
            result.append((tuple((k,v) for k,v in sorted(co.items()) if v),-floor-F(5,14)*a*b,name))
            guards.append({'triple':list(order),'transverse_axis':transverse,'width_upper':str(w),'endpoint_transverse_interval':[str(a),str(b)],'floor':str(floor)})
    return result,guards
