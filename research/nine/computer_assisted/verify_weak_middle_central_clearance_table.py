#!/usr/bin/env python3
"""Twelve-row exact disk-versus-square clearance table.

The hand proof defines the rows and interval formulas independently of this
script. All arithmetic is rational; roots are certified by squared bounds.
"""
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib,json

SCALE=10**6

def root_bounds(x):
    m=isqrt(x.numerator*SCALE*SCALE//x.denominator)
    lo=F(m,SCALE);hi=lo if lo*lo==x else F(m+1,SCALE)
    assert lo*lo<=x<=hi*hi
    return lo,hi

def ceil_grid(x):
    return F(-((-x.numerator*SCALE)//x.denominator),SCALE)

def main():
    rows=[]
    for j in range(12):
        lo=F(1,2)+F(j,80);hi=lo+F(1,80)
        kl=root_bounds(F(1,2)-hi*hi)[0]
        ku=root_bounds(F(1,2)-lo*lo)[1]
        # a=h+k decreases; b=h-k increases.
        au=lo+ku;bl=max(F(0),lo-ku);bu=hi-kl
        dl=F(61,60)-hi;du=F(61,60)-lo;y=F(9,10)
        al=hi+kl
        assert al*dl-bu*y>0
        assert al*y-bu*du>0
        u1=au*du+bu*y;v1=au*y-bl*dl
        u2=au*du-bl*y;v2=bu*du+au*y
        ds1=max(u1-F(1,2),0)**2+max(v1-F(1,2),0)**2
        ds2=max(u2-F(1,2),0)**2+max(v2-F(1,2),0)**2
        cap=ceil_grid(max(ds1,ds2));assert cap<F(1,4)
        rows.append({'h_low':str(lo),'h_high':str(hi),'k_low':str(kl),'k_high':str(ku),
                     'chirality_plus_distance2_upper':str(ds1),
                     'chirality_minus_distance2_upper':str(ds2),
                     'distance2_upper_rounded':str(cap)})
    assert rows[0]['h_low']=='1/2' and rows[-1]['h_high']=='13/20'
    worst=max(F(r['distance2_upper_rounded']) for r in rows)
    result={'status':'EXACT_TABLE_PASSED','rows':rows,'maximum_distance2_upper':str(worst),
            'minimum_reserve':str(F(1,4)-worst),
            'theorem':'For a physical unit square B with1/2<=hB<=13/20 and another disjoint unit S, |xS-xB|<=61/60-hB implies |yS-yB|>9/10.',
            'full_masks_closed':0,'human_or_kernel_verification':False}
    Path(__file__).with_name('weak_middle_central_clearance_table.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
    print('| h interval | k lower | k upper | squared-distance upper |')
    print('|---|---:|---:|---:|')
    for r in rows:print('| ['+r['h_low']+','+r['h_high']+'] | '+r['k_low']+' | '+r['k_high']+' | '+r['distance2_upper_rounded']+' |')

if __name__=='__main__':main()
