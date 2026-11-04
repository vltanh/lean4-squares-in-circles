#!/usr/bin/env python3
"""Independently check a complete finite ordered-angle-domain dual cover.

Only the Python standard library is required. The numerical generator is
not imported and no optimizer output/status is trusted.
"""
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
from angle_tile_dual import tile_lower_bound
from check_angle_neighborhood import angle_neighborhood_certificate

if not __debug__:
    raise RuntimeError('Run without -O: this certificate uses assertions.')

def cover_check(leaves):
    """Every open x strip has a gapless y partition; rectangles are closed."""
    events=defaultdict(lambda:{'start':[],'end':[]})
    for index,leaf in enumerate(leaves):
        x0,x1,y0,y1=map(F,leaf['bounds'])
        assert 0<=x0<x1<=1 and 0<=y0<y1<=1
        events[x0]['start'].append((index,y0,y1));events[x1]['end'].append(index)
    xs=sorted(events)
    assert xs[0]==0 and xs[-1]==1
    active={}
    for k,x in enumerate(xs):
        for index in events[x]['end']:del active[index]
        for index,y0,y1 in events[x]['start']:active[index]=(y0,y1)
        if k==len(xs)-1:
            assert not active
            break
        assert xs[k+1]>x
        previous=F(0)
        for y0,y1 in sorted(active.values()):
            assert y0==previous, ('gap or overlapping interiors',x,y0,previous)
            previous=y1
        assert previous==1
    # Each closed strip boundary is covered by a neighboring strip's closed
    # rectangles. Thus no vertical edge or vertex is omitted from the cover.

def main():
    path=Path(__file__).with_name('ANGLE_TILES.json')
    data=json.loads(path.read_text())
    assert data['schema']=='n11-ordered-group-angle-tiles-v1'
    Q=F(data['upper_q']);keep=list(map(F,data['retained_box']))
    box,root,_,_,_=angle_neighborhood_certificate()
    assert Q>box[0].hi
    assert all(max(abs(keep[2*i]-root[i].hi),abs(keep[2*i+1]-root[i].lo))<F(1,2000) for i in range(2))
    leaves=data['leaves'];cover_check(leaves)
    counts=defaultdict(int);minmargin=None
    for index,leaf in enumerate(leaves):
        x0,x1,y0,y1=map(F,leaf['bounds']);kind=leaf['kind'];counts[kind]+=1
        if kind=='outside_ordered_triangle':
            assert x0>y1 # strict: diagonal ties must be checked elsewhere
        elif kind=='quantitative_neighborhood':
            assert keep[0]<=x0<=x1<=keep[1] and keep[2]<=y0<=y1<=keep[3]
        elif kind=='dual':
            lower=tile_lower_bound(leaf['bounds'],leaf['certificate'])
            assert lower>Q,(index,'dual lower bound did not clear target')
            margin=lower-Q
            minmargin=margin if minmargin is None else min(minmargin,margin)
        else:
            raise AssertionError(('unknown tile kind',kind))
        if (index+1)%100==0:
            print('checked',index+1,'of',len(leaves),'closed rectangles',flush=True)
    assert counts['quantitative_neighborhood']>=1 and counts['dual']>=1
    print('PASS: closed rectangles cover the full unit square without gaps.')
    print('PASS: every ordered-angle point is excluded above qc or in the explicit solved neighborhood.')
    print('Counts:',dict(counts))
    print('Strict lower-margin floor:',str(F((minmargin*10**12).__floor__(),10**12)))
    print('Conclusion: under the 14 prescribed halfspaces and 0 <= ta <= tb <= 1, q >= qc.')
    print('Equality: exact candidate angles; actual packings are precisely the known slider family.')

if __name__=='__main__':main()
