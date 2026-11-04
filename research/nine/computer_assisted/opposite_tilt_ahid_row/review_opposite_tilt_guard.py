#!/usr/bin/env python3
"""Separate exact algebra and guard review; this imports no numerical code."""
from fractions import Fraction as F
from itertools import product,combinations
from pathlib import Path
import json,hashlib
import opposite_tilt_four_row_guard as candidate

if not __debug__:
    raise RuntimeError('Exact guard review requires assertions')


def run():
    checks=0
    rows=candidate.complement_rows()
    expected_orders=(((14,F(1)),(0,F(-1))),((16,F(1)),(14,F(-1))),((6,F(1)),(16,F(-1))))
    for i,terms in enumerate(expected_orders):
        assert rows[i]==(terms,F(0),'opposite_tilt_AHID_order_'+str(i));checks+=1
    forms=[]
    for number,(e1,e2,e3)in enumerate(product((-1,1),repeat=3)):
        terms=tuple(sorted((i,F(v))for i,v in((1,-e1),(15,e1-e2),(17,e2-e3),(7,e3))if v))
        forms.append(terms)
        expected=(tuple((i,-v)for i,v in terms),F(-23,100),'opposite_tilt_AHID_variation_'+str(number))
        assert rows[number+3]==expected;checks+=1
    assert tuple(forms)==candidate.height_expressions();checks+=1
    chain=(0,7,8,3)
    def state(ys,signA=F(0),signD=F(0),xs=None):
        if xs is None:xs=(F(-3,2),F(-1,2),F(1,2),F(3,2))
        p=[(F(0),F(0))for _ in range(18)]
        for i,x,y in zip(chain,xs,ys):p[2*i]=(x,x);p[2*i+1]=(y,y)
        angles=[(F(-1),F(1))for _ in range(9)]
        angles[0]=(signA,signA);angles[3]=(signD,signD)
        scalar=[(F(-1),F(1))for _ in range(36)]
        return {'positions':p,'angles':angles,'scalar':scalar,'differences':[]}
    height_values=(F(-23,200),F(0),F(23,200))
    for ys in product(height_values,repeat=4):
        s=state(ys);actual=sum(abs(ys[j+1]-ys[j])for j in range(3))
        signed=[sum(v*s['positions'][i][0]for i,v in form)for form in forms]
        assert max(signed)==actual;checks+=1
        result=candidate.evaluate(s)
        assert F(result['certified_height_variation_upper'])==actual;checks+=1
        assert (result['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL')==(actual<=F(23,100));checks+=1
        if actual>F(23,100):
            assert any(sum(v*s['positions'][i][0]for i,v in terms)<=rhs for terms,rhs,_ in rows[3:]);checks+=1
    for xs in product((F(-1),F(0),F(1)),repeat=4):
        s=state((F(0),)*4,xs=xs);ordered=all(xs[j]<=xs[j+1]for j in range(3))
        result=candidate.evaluate(s)
        assert (result['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL')==ordered;checks+=1
        if not ordered:
            assert any(sum(v*s['positions'][i][0]for i,v in terms)<=rhs for terms,rhs,_ in rows[:3]);checks+=1
    for a,d in product((F(-1),F(0),F(1)),repeat=2):
        s=state((F(0),)*4,a,d);result=candidate.evaluate(s)
        assert result['opposite_endpoint_signs_proved']==(a*d<=0);checks+=1
        assert (result['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL')==(a*d<=0);checks+=1
    # Scalar component signs are separately sufficient even if slope boxes are broad.
    s=state((F(0),)*4);s['angles'][0]=s['angles'][3]=(F(-1),F(1))
    s['scalar'][9]=(F(0),F(1));s['scalar'][12]=(F(-1),F(0))
    assert candidate.evaluate(s)['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL';checks+=1
    s['scalar'][12]=(F(1,2),F(1))
    assert candidate.evaluate(s)['status']=='GUARD_NOT_IMPLIED';checks+=1
    # Large absolute heights with exact coherent pair differences: every signed
    # form is still zero, including original pair indices that must be reversed.
    s=state((F(0),)*4)
    for i in chain:s['positions'][2*i+1]=(F(-1),F(1))
    assert candidate.evaluate(s)['status']=='GUARD_NOT_IMPLIED';checks+=1
    for i,j in combinations(sorted(chain),2):
        dx=s['positions'][2*j][0]-s['positions'][2*i][0]
        s['differences'].append({'pair':[i,j],'intervals':[(dx,dx),(F(0),F(0))]})
    r=candidate.evaluate(s)
    assert r['status']=='PASS_OPPOSITE_TILT_AHID_TERMINAL'and F(r['certified_height_variation_upper'])==0;checks+=1
    for bad in(F(0),F(-1),F(231,1000)):
        try:candidate.complement_rows(bad)
        except AssertionError:checks+=1
        else:raise AssertionError('Unproved threshold accepted')
    # Continuous proof constants, all with their denominator signs explicit.
    assert F(17,12)**2-2==F(1,144)>0;checks+=1
    assert F(1)-F(5,12)**2>0;checks+=1
    assert F(1)-2*F(23,100)**2>0;checks+=1
    assert F(231,1000)-F(23,100)==F(1,1000)>0;checks+=1
    assert 2*46+F(27,2)==2*F(211,4);checks+=1
    for x in(F(0),F(1,100),F(143,943),F(1,4),F(5,12)):
        al=(1-x*x)/(1+x*x);be=2*x/(1+x*x);h=(al+be)/2
        four=2*be/23;sharp=(9*be-41*(1-al))/32
        E4=(-23-38*x+23*x*x)/(46*(1+x*x))
        Estar=(-8-7*x-33*x*x)/(16*(1+x*x))
        assert E4==four-h and Estar==sharp-h;checks+=2
        assert Estar-E4==x*(143-943*x)/(368*(1+x*x));checks+=1
        assert al*al+be*be==1 and al>0;checks+=1
    for z,w in product((F(-1,3),F(0),F(1,7),F(1,3)),repeat=2):
        ai=(1-z*z)/(1+z*z);bi=2*z/(1+z*z)
        aj=(1-w*w)/(1+w*w);bj=2*w/(1+w*w)
        assert ai*aj+bi*bj>=0
        R=(1+ai*aj+bi*bj+abs(bi*aj-ai*bj))/2
        for owner in(0,1):
            own,other=(z,w)if owner==0 else(w,z)
            direct=(1+z*w)*(1+z*w+abs(z-w))/((1-own*own)*(1+other*other))
            assert direct==R/(ai if owner==0 else aj);checks+=1
    for h in(F(1,2),F(3,5),F(2,3)):
        assert h+F(1)/(4*h)-1==(2*h-1)**2/(4*h);checks+=1
    root=Path(__file__).parent
    return {'status':'PASS_INDEPENDENT_PHYSICAL_ALGEBRA_AND_GUARD_REVIEW',
            'checks':checks,'complete_complement_domains':11,
            'threshold':'23/100','theorem_version':candidate.THEOREM_VERSION,
            'scope':'Exact guard/formula arithmetic only; original bound ancestry and full-domain assembly are not supplied',
            'new_original_cells_closed':0,'new_masks_closed':0,
            'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in(root/'opposite_tilt_four_row_guard.py',Path(__file__))}}

if __name__=='__main__':
    report=run();Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
