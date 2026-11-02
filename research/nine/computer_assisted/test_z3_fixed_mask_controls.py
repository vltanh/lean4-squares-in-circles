#!/usr/bin/env python3
"""Pinned rational SAT/UNSAT controls for the shared-library solver bridge.

These controls test the emitter/solver connection, not global UNSAT.
"""
from fractions import Fraction as F
from pathlib import Path
import ctypes as C
import ctypes.util
import json
from emit_fixed_mask import emit
from z3_ctypes import run

ONE=F(1); ZERO=F(0)
SEVEN=[
 ((-F(3,2),ZERO),(ONE,ZERO)),((-F(1,2),-ONE),(ONE,ZERO)),
 ((F(1,2),-ONE),(ONE,ZERO)),((F(3,2),ZERO),(ONE,ZERO)),
 ((-F(11,12),ONE),(ONE,ZERO)),((F(1,12),F(25,112)),(ONE,ZERO)),
 ((F(79,84),F(121,112)),(F(4,5),F(3,5)))]
NINE=[((F(k,2),F(1,16)),(ONE,ZERO)) for k in (-3,-1,1,3)]+[
 ((F(k),-F(15,16)),(ONE,ZERO)) for k in (-1,0,1)]+[
 ((F(k,20),F(19,16)),(F(99,101),F(20,101))) for k in (-11,11)]

def rational(v):
    v=F(v)
    n=str(v.numerator) if v>=0 else f'(- {-v.numerator})'
    return n if v.denominator==1 else f'(/ {n} {v.denominator})'

def pin(poses):
    rows=[]
    for i,((x,y),(a,b)) in enumerate(poses):
        assert a*a+b*b==1
        for k,v in zip('xyabh',(x,y,a,b,(abs(a)+abs(b))/2)):
            rows.append(f'(assert (= {k}_{i} {rational(v)}))')
    return '\n'.join(rows)

def main():
    cases=[
      ('seven_strict_00001',SEVEN,'000/01','strict','sat'),
      ('seven_wrong_actual_edge',SEVEN,'000/00','strict','unsat'),
      ('nine_equality_closed',NINE,'000/00','closed','sat'),
      ('nine_equality_strict',NINE,'000/00','strict','unsat'),
      ('nine_equality_wrong_weak_edge',NINE,'000/01','closed','unsat'),
    ]
    rows=[]
    for name,poses,mask,radius,expected in cases:
        text='(set-option :timeout 10000)\n'+emit(mask,radius,len(poses)).replace('(check-sat)','')+'\n'+pin(poses)+'\n(check-sat)\n'
        answer=run(text).strip()
        assert answer==expected,(name,answer,expected)
        rows.append({'name':name,'expected':expected,'observed':answer})
    lib=C.CDLL(C.util.find_library('z3'));lib.Z3_get_full_version.restype=C.c_char_p
    report={'status':'PASS','z3_version':lib.Z3_get_full_version().decode(),'pinned_controls':rows,'global_unsat_certificate':False,'full_masks_closed':0}
    Path(__file__).with_name('z3_fixed_mask_control_report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
