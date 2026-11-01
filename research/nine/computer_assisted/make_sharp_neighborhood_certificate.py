#!/usr/bin/env python3
"""Produce the rational fourteen-layer certificate for a sharp local terminal.

The terminal is conditional on the explicit geometric neighborhood. It is
not an extraction theorem and does not by itself close a global root or A.2.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def generate():
    w,v,k=F(23,64),F(9,64),F(207,512)
    b,h=F(1,64),F(1,8); c=(1-4*b)/2; lam=F(1,256)
    p=w*(1+b)+k; H=v*(1+b)+k
    C3=(2*p*p+w*w*(3+b)**2)/(2*w)+k*k/v+w*F(25,16)
    C4=k*k/(2*w)+(H*H+v*v*(2+b)**2)/(2*v)+v*F(31,16)
    C6=k*k/w+(2*H*H+v*v*(2+b)**2)/(2*v)+v*F(31,16)
    rows=[]
    for sign in (1,-1):
        for mask in range(1,8):
            X,Y,Z=[sign*int(mask>>i&1) for i in range(3)]
            f=(4*w*(c-h)-lam)*abs(X)-F(851,2048)*X+(3*v*(c-h)-lam)*abs(Z-Y)+F(225,2048)*(Z-Y)+(k*(c-F(1,4))-lam)*(abs(Y)+abs(X-Z))-b*(C3*abs(X)+C4*abs(Y)+C6*abs(Z))
            rows.append({'pattern':[X,Y,Z],'reserve':str(f)})
    return dict(schema='n9_sharp_neighborhood_v3',target_q='1105/256',
        position_tolerance='1/8',tilt_bound='1/64',
        anchor_weights={'0':'23/64','3':'23/64','4':'9/64','6':'9/64'},
        horizontal_weights=['23/16','27/64'],vertical_weight='207/512',
        pair_variation_coefficient=str(c),quadratic_loss_coefficients=list(map(str,(C3,C4,C6))),
        claimed_variation_coefficient='1/256',retained_anchor_square_fraction='1/2',
        layer_table=rows,minimum_layer_reserve=str(min(F(x['reserve']) for x in rows)),
        global_A2_closed=False)

if __name__=='__main__':
    p=Path(__file__).resolve().parent/'sharp_neighborhood_certificate.json'
    p.write_text(json.dumps(generate(),sort_keys=True,indent=2)+'\n');print(p)
