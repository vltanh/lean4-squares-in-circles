#!/usr/bin/env python3
"""Generate full fixed-seven 58-leaf rational dyadic certificate."""
from fractions import Fraction as F
from pathlib import Path
from collections import Counter
R=F(91,60)
C=[(-F(3,2),F(0)),(-F(1,2),-F(1)),(F(1,2),F(-1)),
   (F(3,2),F(0)),(-F(11,12),F(1)),(F(1,12),F(25,112)),
   (F(79,84),F(121,112))]
def classify(box):
    x0,x1,y0,y1=box
    if x0>=-F(1,12) and x1<=F(1,12) and y0>=F(4,3):return 'cap'
    dx=max(x0,-x1,F(0));dy=max(y0,-y1,F(0))
    if dx*dx+dy*dy>=R*R:return 'outer'
    for i,(a,b) in enumerate(C):
        dx=max(abs(x0-a),abs(x1-a));dy=max(abs(y0-b),abs(y1-b))
        if dx*dx+dy*dy<1:return 'center_'+str(i)
    return None
def children(box):
    x0,x1,y0,y1=box
    if x1-x0>=y1-y0:
        m=(x0+x1)/2
        return ((x0,m,y0,y1),(m,x1,y0,y1))
    m=(y0+y1)/2
    return ((x0,x1,y0,m),(x0,x1,m,y1))
def generate():
    rows=[]
    def visit(box,path):
        reason=classify(box)
        if reason:
            rows.append((path,reason))
            return
        if len(path)>24:raise ValueError('unresolved box')
        for bit,child in enumerate(children(box)):
            visit(child,path+str(bit))
    visit((-R,R,-R,R),'')
    return rows
def main():
    rows=generate()
    print('LEAVES',len(rows),'REASONS',dict(Counter(r for p,r in rows)))
    assert len(rows)==58 and max(len(p) for p,r in rows)==13
    md=Path(__file__).with_name('NO_EIGHTH_FIXED_SEVEN_HAND_TABLE.md').read_text()
    seen=[]
    for line in md.splitlines():
        if line.startswith('| '+chr(96)):
            fields=[x.strip().strip(chr(96)) for x in line.strip('|').split('|')]
            seen.append(tuple(fields))
    assert seen==rows,'committed hand table differs from independent generation'
    print('PASS regenerated table matches committed rows')
if __name__=='__main__':main()
