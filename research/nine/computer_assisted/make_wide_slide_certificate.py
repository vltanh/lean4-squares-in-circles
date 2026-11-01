#!/usr/bin/env python3
"""Generate exact layer data for the widened sharp terminal (not global A.2)."""
from fractions import Fraction as F
from pathlib import Path
import json

def generate():
    w,v,k=F(23,64),F(9,64),F(207,512)
    WM,WB=4*w,3*v; b=F(1,64); c=(1-4*b)/2; lam=F(1,256)
    LM,UM,LB,UB=-F(1,8),F(11,16),-F(19,32),F(1,8)
    mM,hM=(LM+UM)/2,(UM-LM)/2;mB,hB=(LB+UB)/2,(UB-LB)/2
    P=w*(1+b)+k;H=v*(1+b)+k
    losses=[(2*P*P+w*w*(3+b)**2)/(2*w)+k*k/v+25*w/16,
            k*k/(2*w)+(H*H+v*v*(2+b)**2)/(2*v)+31*v/16,
            k*k/w+(2*H*H+v*v*(2+b)**2)/(2*v)+31*v/16]
    A=F(851,2048)-WM*mM;B=F(225,2048)+WB*mB
    rows=[]
    for sign in (1,-1):
        for mask in range(1,8):
            X,Y,Z=[sign*int(mask>>j&1) for j in range(3)]
            val=(WM*(c-hM)-lam)*abs(X)-A*X+(WB*(c-hB)-lam)*abs(Z-Y)+B*(Z-Y)+(k*(c-F(1,4))-lam)*(abs(Y)+abs(X-Z))-b*sum(C*abs(z) for C,z in zip(losses,(X,Y,Z)))
            rows.append({'pattern':[X,Y,Z],'reserve':str(val)})
    return {'schema':'n9_wide_slide_sharp_v1','target_q':'1105/256',
            'horizontal_tolerance':'1/8','anchor_vertical_tolerance':'1/8',
            'middle_row_inner_vertical':['-1/8','11/16'],
            'bottom_row_inner_vertical':['-19/32','1/8'],
            'tilt_bound':'1/64','variation_coefficient':'1/256',
            'anchor_square_fraction':'1/2','row_midpoints':list(map(str,(mM,mB))),
            'row_half_ranges':list(map(str,(hM,hB))),
            'adjusted_linear_coefficients':list(map(str,(A,B))),
            'quadratic_losses':list(map(str,losses)),'layer_table':rows,
            'minimum_layer_reserve':str(min(F(r['reserve']) for r in rows)),
            'global_A2_closed':False}

if __name__=='__main__':
    path=Path(__file__).with_name('wide_slide_certificate.json')
    path.write_text(json.dumps(generate(),sort_keys=True,indent=2)+'\n')
    print(path)
