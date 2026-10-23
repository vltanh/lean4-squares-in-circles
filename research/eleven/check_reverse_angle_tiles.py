#!/usr/bin/env python3
"""Exact exclusion of the full closed reverse-order angle triangle."""
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
from angle_tile_dual import tile_lower_bound
from check_angle_tiles import cover_check
from isolate_contact_root import certificate

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')

def main():
    data=json.loads(Path(__file__).with_name('REVERSE_ANGLE_TILES.json').read_text())
    assert data['schema']=='n11-reverse-group-angle-tiles-v1'
    Q=F(data['lower_q']);box=certificate();assert Q>box[0].hi
    leaves=data['leaves'];cover_check(leaves)
    counts=defaultdict(int);minmargin=None
    for index,leaf in enumerate(leaves):
        x0,x1,y0,y1=map(F,leaf['bounds']);kind=leaf['kind'];counts[kind]+=1
        if kind=='outside_reverse_triangle':
            assert y0>x1 # strict: the equal-angle locus remains checked
        elif kind=='dual':
            assert leaf['certificate']['delta_sign']==-1
            lower=tile_lower_bound(leaf['bounds'],leaf['certificate'])
            assert lower>Q,(index,'dual bound did not clear target')
            margin=lower-Q
            minmargin=margin if minmargin is None else min(minmargin,margin)
        else:raise AssertionError(('unknown kind',kind))
        if (index+1)%100==0:print('checked',index+1,'of',len(leaves),'closed rectangles',flush=True)
    assert counts['dual']>=1
    print('PASS: the closed reverse triangle 0 <= tb <= ta <= 1 is strictly excluded below Q.')
    print('Counts:',dict(counts))
    print('Q:',str(Q))
    print('Strict lower-margin floor:',str(F((minmargin*10**12).__floor__(),10**12)))
    print('Together with the ordered-angle theorem: q >= qc for every 0 <= ta,tb <= 1.')
    print('Equality requires the exact ordered candidate angles and the slider family.')

if __name__=='__main__':main()
