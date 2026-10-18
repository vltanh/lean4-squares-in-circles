#!/usr/bin/env python3
"""Independent exact rational positive 4+4 packing above the excluded bound.

This is a negative regression against any overstrong claim that the necessary
model makes every real 4+4 packing infeasible for all radii. No floats.
"""
from fractions import Fraction as F
from itertools import combinations
from m5_fourfour_exact_model import (SQ_LOWER, SQ_UPPER, REPS, RationalModel,
                                     transform_point, RADIUS)
import m5_fourfour_exact_model as mdl

RAW_CENTERS = ((-11080,1021), (-54722,120732),(-102841,-99979),
               (107983,-86740),(-124715,20732),(9191,-129368),
               (126239,36426),(45278,126176))
FRAME_TYPES = (0,0,1,1,0,1,1,0)
LAM = F(1001,1000)
DISK_Q = F(81,20)
DISK_R = F(2013,1000)


def farthest_norm_squared(p,kind):
    x,y=p
    base=x*x+y*y+F(1,2)
    if kind==0:
        return base+abs(x)+abs(y)
    return base+SQ_UPPER*max(abs(x),abs(y))


def pair_gap(p,q,fi,fj):
    x,y=q[0]-p[0],q[1]-p[1]
    if fi==fj==0:
        return max(abs(x),abs(y))-1
    if fi==fj==1:
        return abs(x)+abs(y)-SQ_UPPER
    return max(max(abs(x),abs(y))-(1+SQ_UPPER)/2,
               abs(x)+abs(y)-(1+SQ_UPPER/2))


def rank_pattern(std,dia):
    std=sorted(std,key=lambda p:p[0]+p[1])
    dia=sorted(dia,key=lambda p:p[0])
    ts=sorted(range(4),key=lambda i:std[i][0]-std[i][1])
    ys=sorted(range(4),key=lambda i:dia[i][1])
    pi=tuple(ts.index(i) for i in range(4))
    sig=tuple(ys.index(i) for i in range(4))
    return std+dia,pi,sig


def main():
    ps=[(F(a,100000)*LAM,F(b,100000)*LAM) for a,b in RAW_CENTERS]
    assert 4==FRAME_TYPES.count(0)==FRAME_TYPES.count(1)
    norms=[farthest_norm_squared(p,k) for p,k in zip(ps,FRAME_TYPES)]
    assert max(norms)<DISK_Q and DISK_R*DISK_R>DISK_Q
    gaps=[pair_gap(ps[i],ps[j],FRAME_TYPES[i],FRAME_TYPES[j])
          for i,j in combinations(range(8),2)]
    assert len(gaps)==28 and min(gaps)>=F(1,1000)
    assert RADIUS*RADIUS<min(F(4),max(norms))
    print('Positive 4+4 true packing: all 32 vertices and 28 pair SAT gaps PASS')
    print('Squared farthest vertex norm is below 81/20; min SAT gap >= 1/1000')
    mdl.RADIUS=DISK_R
    for rot in range(4):
        for reflect in (False,True):
            std=[transform_point(p,rot,reflect) for p,k in zip(ps,FRAME_TYPES) if k==0]
            dia=[transform_point(p,rot,reflect) for p,k in zip(ps,FRAME_TYPES) if k==1]
            ordered,pi,sigma=rank_pattern(std,dia)
            if (pi,sigma) not in REPS: continue
            model=RationalModel(pi,sigma)
            P=[v for p in ordered for v in p]
            for idx in range(model.base):
                row=model.rows[idx]
                assert sum((P[j]*a for j,a in row.items()),F(0))<=model.right[idx]
            for choices in model.bundles:
                assert any(all(sum((P[j]*a for j,a in model.rows[r].items()),F(0))<=model.right[r]
                               for r in opt) for opt in choices)
            print('Legitimate D4 transform/labeling gives a certified 66-root class:',REPS.index((pi,sigma)))
            print('All 1024 disk-support rows, 12 forced true separations, and all 16 full mixed canonical choices hold at radius 2013/1000.')
            return
    raise AssertionError('No actual D4/label normalization to the 66-root class')

if __name__=='__main__':main()
