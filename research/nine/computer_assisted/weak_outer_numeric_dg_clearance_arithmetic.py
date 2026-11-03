#!/usr/bin/env python3
"""Exact scalar constants in the affine original-D/G clearance theorem."""
from fractions import Fraction as F
import json

def verify():
    assert F(133,64)-2==F(5,64)
    assert 46+F(27,2)-F(211,4)==F(27,4)
    assert (F(27,4)-46*F(5,64))/F(27,2)==F(101,432)
    assert F(1,8)-F(7,20)**2==F(1,400)>0
    assert F(59,60)+F(7,20)==F(4,3)
    K=F(133,64)-F(101,432)
    assert K==F(3187,1728)
    assert K-1==F(1459,1728)
    assert K-F(10,7)==F(5029,12096)
    reverse=K-F(10,7)-F(11,60)
    assert reverse==F(14057,60480)>0
    assert F(10,7)**2>2
    assert -1-F(7,8)**2==-F(113,64)
    reserves=[]
    for s in (F(1),F(10,7)):
        L=F(8,15)+F(7,8)*(s-1)
        assert L==F(7,8)*s-F(41,120)>0
        p=1-(K-s)**2-L*L
        assert p>0
        reserves.append(p)
    assert reserves==[F(198911,74649600),F(7595279,3657830400)]
    return {'claim':'affine D/G clearance scalar arithmetic','all_checks':'PASS',
            'reverse_gap_reserve':str(reverse),'endpoint_reserves':[str(x) for x in reserves],
            'whole_mask_closed':False}

if __name__=='__main__':print(json.dumps(verify(),indent=2))
