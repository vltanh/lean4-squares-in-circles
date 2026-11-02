#!/usr/bin/env python3
"""Exact scalar checks for the stated many-central physical callers."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json

ell=F(29,60);g0=F(15,31);delta=F(331,20000)
checks={
 'low_side_x_bound':F(49,80)-F(2211,4000),
 'low_side_main_horizontal_inset_reserve':g0-F(31,240),
 'global_central_horizontal_overlap':F(1,2)-ell-delta,
 'two_lower_whole_floor_reserve':F(269,310)-F(17,24)-F(1,10),
 'same_half_lower_height_squared_reserve':F(1,4)-delta**2-(F(273,200)-2*g0+F(1,10))**2,
 'same_half_three_center_squared_reserve':1-ell**2-F(203,240)**2,
 'middle_main_upper_center_reserve':-F(7,20)+F(59,60)-F(3,5),
 'selected_central_endpoint_floor_coordinate_reserve':F(23,150)-(ell-F(7,20)),
 'replacement_floor_reserve':F(2807,24000)-F(1,10),
 'central_five_cone_span_squared_reserve':2-(2*ell)**2,
}
assert all(v>0 for v in checks.values())
assert checks['two_lower_whole_floor_reserve']==F(221,3720)
assert checks['same_half_lower_height_squared_reserve']==F(945821879,384400000000)
assert checks['same_half_three_center_squared_reserve']==F(587,11520)
assert F(273,200)-2*g0+F(1,10)>0
assert -F(139,120)+F(59,60)==-F(7,40)
assert F(91,60)+F(7,40)==F(203,120)
assert -F(7,20)+F(59,60)==F(19,30)
assert ell<F(1,2)
report={'proof_status':'many_central_caller_exact_arithmetic_passed',
        'checks':{k:str(v)for k,v in checks.items()},
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('many_central_caller_arithmetic_replay.json').write_text(
    json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
