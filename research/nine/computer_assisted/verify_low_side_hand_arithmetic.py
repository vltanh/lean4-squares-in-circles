#!/usr/bin/env python3
"""Exact rational reserves used in the complete low-side hand reduction."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json

def main():
    l=F(29,60);u=F(13,12);g0=F(5,13)
    values={
        'initial_side_main_horizontal_gap':u-g0+F(1,60),
        'initial_disk_clearance_reserve':F(4,5)**2-(u-g0+F(1,60))**2,
        'endpoint_horizontal_rectangle_halfwidth':F(15,32)-F(1,60),
        'stronger_endpoint_vertical_reserve':F(4421,12000)-F(221,600),
        'side_horizontal_narrowing_squared_reserve':F(1,4)-(F(3,5)-F(221,600))**2-(F(503,480)-F(49,80))**2,
        'central_below_side_disk_reserve':1-F(49,80)**2-(F(3,5)+F(7,40))**2,
        'own_side_main_gap_upper':F(49,80)-g0+F(1,60),
        'one_quarter_gap_reserve':F(1,4)-(F(49,80)-g0+F(1,60)),
        'reverse_horizontal_gap':F(61,60)-F(1,2)-l,
    }
    expected={
        'initial_side_main_horizontal_gap':F(93,130),
        'initial_disk_clearance_reserve':F(2167,16900),
        'endpoint_horizontal_rectangle_halfwidth':F(217,480),
        'stronger_endpoint_vertical_reserve':F(1,12000),
        'side_horizontal_narrowing_squared_reserve':F(38839,5760000),
        'central_below_side_disk_reserve':F(31,1280),
        'own_side_main_gap_upper':F(763,3120),
        'one_quarter_gap_reserve':F(17,3120),
        'reverse_horizontal_gap':F(1,30),
    }
    assert values==expected and all(v>0 for v in values.values())
    report={'status':'ALL_EXACT_RATIONAL_RESERVES_PASSED','reserves':{k:str(v)for k,v in values.items()},'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('low_side_hand_arithmetic_replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
