#!/usr/bin/env python3
"""Exact shared-face audit for the full canonical middle-B family.

Let b=y_I-y_B, with I,D at their canonical common height. The physical
family has0<=b<17/64; we check the larger closed interval[0,17/64].
No sampling is used. Each possible closed-escape conjunction is solved
exactly as an interval of one rational variable.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse,json

BOUND=F(17,64)

def intersection(rows):
    lo,hi=F(0),BOUND
    for coefficient,rhs in rows:
        if coefficient==0:
            if rhs<0:return None
        elif coefficient>0:hi=min(hi,rhs/coefficient)
        else:lo=max(lo,rhs/coefficient)
    return None if lo>hi else (lo,hi)

def verify():
    # Each entry is the scalar inequality coefficient*b<=rhs for I.
    # Horizontal escape rows fail by the exact unit horizontal margins.
    old=((F(0),F(-1)),(F(0),F(-1)),(F(1),-F(1,8)),
         (F(-1),-F(1,8)),(F(0),-F(1,8)),(F(0),-F(1,8)))
    asymmetric=((F(0),F(-1)),(F(0),F(-1)),(F(1),F(0)),
                (F(-1),-F(1,3)),(F(0),-F(1,16)),(F(0),-F(1,16)))
    positive=((F(0),F(-1)),(F(0),F(-1)),(F(-1),-F(1,2)),
              (F(1),-F(1,2)),(F(-1),-F(1,2)),(F(1),-F(1,2)))
    for i,j in product(range(6),repeat=2):
        assert intersection((old[i],asymmetric[j])) is None,(i,j)
    for i in range(6):assert intersection((positive[i],)) is None,i
    assert F(117,4)**2-849==F(105,16)>0
    assert F(1,3)-BOUND==F(13,192)>0
    assert F(1,2)-BOUND==F(15,64)>0
    # At b=0, the asymmetric lower face is retained, but the old row gate
    # has no escape. At b=1/8, the old face is retained, but no new escape.
    for b in (F(0),F(1,8),F(1,4),BOUND):
        old_ok=[i for i,(a,r) in enumerate(old) if a*b<=r]
        new_ok=[i for i,(a,r) in enumerate(asymmetric) if a*b<=r]
        assert not(old_ok and new_ok)
    return {'status':'PASS','family_parameter':'b=y_I-y_B',
            'checked_closed_interval':['0','17/64'],
            'negative_D_closed_escape_conjunctions_rejected':36,
            'positive_D_closed_escape_children_rejected':6,
            'actual_family_radical_squared_reserve':'105/16',
            'asymmetric_upper_margin':'13/192','positive_total_variation_margin':'15/64',
            'shared_faces_included':True,'whole_mask_closed':False}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);args=ap.parse_args();out=verify()
    if args.report:args.report.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
