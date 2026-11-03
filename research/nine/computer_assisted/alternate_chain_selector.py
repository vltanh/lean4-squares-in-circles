#!/usr/bin/env python3
"""Exact selector enumeration. This is a terminal detector, not a proof of global existence."""
from fractions import Fraction as F
from itertools import permutations
LABELS=(0,1,2,3,7,8)
SELECTORS=tuple(p for p in permutations(LABELS,4) if tuple(i for i in p if i<4)==tuple(sorted(i for i in p if i<4)))
def rows(points, widths, chain):
    """Eight exact slacks; all nonnegative invoke the accepted 000/** or 010/** terminal."""
    out=[]
    for a,b in zip(chain,chain[1:]):
        dx=points[b][0]-points[a][0];dy=points[b][1]-points[a][1]
        out.extend((dx-dy,dx+dy))
    for a,b in ((chain[0],chain[1]),(chain[2],chain[3])):
        out.append(points[b][0]-points[a][0]-widths[a]-widths[b])
    return tuple(out)
def detect(points, widths):
    # Required unchanged E,F,G center cones and two actual links.
    for a,b in ((4,5),(5,6)):
        dx=points[b][0]-points[a][0];dy=points[b][1]-points[a][1]
        if dx<abs(dy) or dx<widths[a]+widths[b]:
            raise ValueError('fixed E,F,G caller does not hold')
    return tuple((p,rows(points,widths,p)) for p in SELECTORS if min(rows(points,widths,p))>=0)
def self_check():
    assert len(SELECTORS)==105 and len(set(SELECTORS))==105
    assert all(len(set(p))==4 for p in SELECTORS)
    counts=[sum(sum(i>=7 for i in p)==k for p in SELECTORS) for k in range(3)]
    assert counts==[1,32,72]
    p=[(F(x,2),F(-1,16)) for x in (-3,-1,1,3)]+[(F(x),F(15,16)) for x in (-1,0,1)]+[(F(x,2),F(-17,16)) for x in (-1,1)]
    witnesses=detect(p,[F(1,2)]*9)
    assert any(c==(0,1,2,3) for c,s in witnesses)
    assert rows(p,[F(1,2)]*9,(0,1,2,3))==(F(1),F(1),F(1),F(1),F(1),F(1),F(0),F(0))
    # A mislabeled chain with decreasing original x-order cannot have six nonnegative cone rows.
    for chain in permutations(LABELS,4):
        if chain not in SELECTORS:assert min(rows(p,[F(1,2)]*9,chain)[:6])<0
    return {'status':'PASS','selector_count':105,'by_extra_count':counts,'scope':'strict-radius terminal; no global existence assertion','equality_control_witness_count':len(witnesses)}
if __name__=='__main__':
    import json
    print(json.dumps(self_check(),indent=2))
