#!/usr/bin/env python3
"""Standalone exact arithmetic verification of the printed seven-original controls.

No floating point, optimizer, imported geometric kernel or producer code.
This proves feasibility of seven-original relaxations, not nine-original masks.
"""
import json
from pathlib import Path
from fractions import Fraction
from itertools import combinations,product
F=Fraction
D=json.loads(Path(__file__).with_name('seven_original_all_open_masks_table.json').read_text())
Q=F(1105,256);q=F(D['radius_squared']);assert q<Q
sx=F(D['x_scale']);sy=F(D['y_scale']);st=F(D['half_angle_scale'])
rows=D['rows']; allbits=set(); checks=0; minima={}
for bits,triples in rows.items():
    assert len(triples)==7 and len(bits)==5
    poses=[];widths=[];reserve=[];cone_reserves=[];bit_reserves=[]
    for X,Y,T in triples:
        t=st*T;a=(1-t*t)/(1+t*t);b=2*t/(1+t*t)
        assert a*a+b*b==1
        poses.append(((sx*X,sy*Y),(a,b),(-b,a)))
        widths.append((a+abs(b))/2)
        assert a>=abs(b)
    for c,u,v in poses:
        for s,t in product((-1,1),repeat=2):
            p=(c[0]+(s*u[0]+t*v[0])/2,c[1]+(s*u[1]+t*v[1])/2)
            r=q-p[0]*p[0]-p[1]*p[1];assert r>0;reserve.append(r);checks+=1
    pair_reserves=[]
    axis_code=D['pair_axis_codes'][bits];assert len(axis_code)==21
    for pair_index,(i,j) in enumerate(combinations(range(7),2)):
        d=(poses[j][0][0]-poses[i][0][0],poses[j][0][1]-poses[i][0][1])
        vals=[]
        for nx,ny in (*poses[i][1:],*poses[j][1:]):
            total=F(0)
            for p in (poses[i],poses[j]):
                for ax,ay in p[1:]:total+=abs(nx*ax+ny*ay)/2
            vals.append(abs(nx*d[0]+ny*d[1])-total)
        designated=vals[int(axis_code[pair_index])]
        assert designated>0;pair_reserves.append(designated);checks+=1
    for bit,(i,j) in zip(bits,((0,1),(1,2),(2,3),(4,5),(5,6))):
        dx=poses[j][0][0]-poses[i][0][0];dy=poses[j][0][1]-poses[i][0][1]
        assert dx>abs(dy);cone_reserves.append(dx-abs(dy));checks+=1
        bit_reserve=(dx-widths[i]-widths[j])*(1 if bit=='0' else -1)
        assert bit_reserve>0;bit_reserves.append(bit_reserve)
        checks+=1
    B=D['rational_summary_bounds'][bits]
    assert q-min(reserve)<=F(B['corner_norm_upper_thousandths'],1000)<q
    assert min(pair_reserves)>=F(B['pair_reserve_lower_millionths'],1000000)>0
    assert min(cone_reserves)>=F(B['cone_reserve_lower_millionths'],1000000)>0
    assert min(bit_reserves)>=F(B['bit_reserve_lower_millionths'],1000000)>0
    checks+=4
    allbits.add(bits);allbits.add(bits[:3][::-1]+bits[3:][::-1])
    minima[bits]={'corner_to_17_over4':str(min(reserve)),'physical_pair':str(min(pair_reserves))}
expected={''.join(a)+''.join(b) for a in product('01',repeat=3) for b in product('01',repeat=2) if a[0]=='1' or a[2]=='1'}
assert allbits==expected
print(json.dumps({'passed':True,'representative_rows':len(rows),'covered_masks':len(allbits),
 'explicit_rational_predicate_checks':checks,'radius_squared':str(q),'Q_reserve':str(Q-q),
 'scope':'seven-original relaxation feasibility only','new_whole_mask_closures':0,'minimum_reserves':minima},indent=2))
