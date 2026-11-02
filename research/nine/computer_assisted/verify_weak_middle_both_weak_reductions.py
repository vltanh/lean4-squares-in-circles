#!/usr/bin/env python3
"""Exact arithmetic for the hand reductions; not a full-mask checker."""
from fractions import Fraction as F
from pathlib import Path
import json

def main():
 r={
  'main_amgm_squared_reserve':F(32**2*82-289**2),
  'central_nearest_clearance_squared_reserve':F(1,4)-(F(31,60)-F(5,13))**2-F(12,25)**2,
  'central_between_height_reserve':F(10,13)+F(12,25)-F(31,30),
  'central_outside_nearest_gap_reserve':F(31,60)-(F(1,2)-F(5,13)),
  'wide_main_routing_width_reserve':F(3,10)-(F(13,20)-F(5,13)),
  'opposite_routing_cone_reserve':F(3,2)-F(22,15),
  'far_endpoint_disk_squared_reserve':1-F(3,5)**2-F(4,5)**2,
  'far_endpoint_bad_order_reserve':-F(9,20)+F(27,40),
  'selected_gap_squared_reserve':F(1,2)-F(7,10)**2,
  'selected_span_squared_reserve':F(2)-F(7,5)**2,
  'all_central_span_squared_reserve':F(2)-F(29,30)**2,
 }
 for name,value in r.items():
  assert value>=0 if name=='far_endpoint_disk_squared_reserve' else value>0
 C=(F(211,4)-46*F(59,60))/F(27,2)
 assert C==F(451,810)
 assert 46/F(27,2)==F(92,27)
 assert (F(211,2)-92)/F(27,2)==1
 assert 2-F(211,184)==F(157,184)
 assert F(27,2)/46==F(27,92)
 r.update(individual_resource_constant=C,middle_surplus_coefficient=F(92,27),opposite_load_constant=F(157,184))
 out={'status':'EXACT_ARITHMETIC_PASS','scope':'common deductions only; complete 010/11 remains open','rational_values':{k:str(v) for k,v in r.items()}}
 p=Path(__file__).with_name('weak_middle_both_weak_reductions_replay.json')
 p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
