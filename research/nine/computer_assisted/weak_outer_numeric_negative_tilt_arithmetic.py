#!/usr/bin/env python3
"""Exact constants for the complete negative-tilt low-gap hand argument."""
from fractions import Fraction as F
import json

def verify():
    horizontal=F(133,64)+F(91,60)-F(3,2)
    assert horizontal==F(2011,960)
    assert 133**2-16*1105==9
    # 1/sqrt(2)>5/8; all factors squared here are positive.
    mean_reserve=F(1,2)-F(25,64)
    assert mean_reserve==F(7,64)>0
    # J(arctan(1/3)) > horizontal.
    shifted=horizontal+F(5,24)
    assert shifted==F(737,320)
    slope_reserve=7040**2-10*2211**2
    assert slope_reserve==676390>0
    chord_reserve=220**2-10*69**2
    assert chord_reserve==790>0
    assert (F(23,20)-1)*3==F(9,20)
    assert F(5,8)-F(9,20)==F(7,40)
    assert F(1,2)-F(5,8)+F(9,20)==F(13,40)
    folded_reserve=240**2-2*161**2
    assert folded_reserve==5758>0
    assert F(1,2)-F(11,46)==F(6,23)
    assert F(46)*2+F(27,2)==2*F(211,4)
    return {'claim':'scalar arithmetic for a continuous hand proof',
            'whole_mask_closed':False,'horizontal_bound':str(horizontal),
            'mean_square_reserve':str(mean_reserve),
            'separator_square_reserve':slope_reserve,
            'chord_square_reserve':chord_reserve,
            'folded_toll_square_reserve':folded_reserve,
            'all_checks':'PASS'}

if __name__=='__main__':print(json.dumps(verify(),indent=2))
