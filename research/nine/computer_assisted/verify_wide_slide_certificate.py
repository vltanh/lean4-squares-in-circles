#!/usr/bin/env python3
"""Independent exact check of the wide-slide extension.

Rechecks the earlier two physical polynomial identities, then checks the new
owner-independent telescoping bounds, full signed layers, boundary controls
and corruptions. Imports no new producer. This is not a global coverage proof.
"""
from fractions import Fraction as R
from itertools import combinations,product
from pathlib import Path
import argparse,copy,hashlib,json
from verify_sharp_neighborhood_certificate import check as check_base, BASE, need
HERE=Path(__file__).resolve().parent

def check(cert):
    need(cert['schema']=='n9_wide_slide_sharp_v1' and cert['global_A2_closed'] is False,'scope')
    fixed={'target_q':'1105/256','horizontal_tolerance':'1/8','anchor_vertical_tolerance':'1/8',
           'middle_row_inner_vertical':['-1/8','11/16'],'bottom_row_inner_vertical':['-19/32','1/8'],
           'tilt_bound':'1/64','variation_coefficient':'1/256','anchor_square_fraction':'1/2'}
    need(all(cert[k]==v for k,v in fixed.items()),'physical constants')
    base=json.loads((HERE/'sharp_neighborhood_certificate.json').read_text())
    dependency=check_base(base)
    loss=list(map(R,dependency['quadratic_loss_coefficients']))
    need(loss==list(map(R,cert['quadratic_losses'])),'quadratic cost changed')
    M=[R(-1,8),R(11,16)];B=[R(-19,32),R(1,8)]
    row_mid=[sum(M)/2,sum(B)/2];row_half=[(M[1]-M[0])/2,(B[1]-B[0])/2]
    need(row_mid==list(map(R,cert['row_midpoints'])),'midpoints')
    need(row_half==list(map(R,cert['row_half_ranges'])),'half-ranges')
    b=R(1,64);ex=R(1,8);c=R(15,32);lam=R(1,256)
    WM,WB,k=R(23,16),R(27,64),R(207,512)
    A=R(851,2048)-WM*row_mid[0];Blin=R(225,2048)+WB*row_mid[1]
    need([A,Blin]==list(map(R,cert['adjusted_linear_coefficients'])),'endpoint terms')
    # The old displacement-identity is algebraic and independent of inner heights.
    # Recenter z at each row midpoint to prove the new telescoping remainder.
    # Check both possible endpoint owners as polynomial coefficient equalities.
    telescoping_cases=0
    for midpoint,half in zip(row_mid,row_half):
        for owner in (0,1):
            # Coefficients ordered as ti*zi, ti*zj, tj*zi, tj*zj, ti, tj.
            lhs=[1,-1,0,0,0,0] if owner==0 else [0,0,1,-1,0,0]
            # ti*zi-tj*zj + midpoint*(tj-ti) + (z_r-midpoint)*(tj-ti)
            zr=1 if owner==0 else 0
            rhs=[R(1),R(0),R(0),R(-1),-midpoint,midpoint]
            rhs[zr]-=1;rhs[2+zr]+=1;rhs[4]+=midpoint;rhs[5]-=midpoint
            need(lhs==rhs,'row telescope identity')
            telescoping_cases+=1
    wrong_horizontal=[];positive_horizontal=[]
    for low,high in (M,B):
        length=high-low
        wrong_horizontal.append(b*(1+2*ex)+length)
        positive_horizontal.append((1-b)*(1-2*ex)-b*length)
    need(max(wrong_horizontal)<1 and min(positive_horizontal)>0,'new horizontal separator cover')
    need(R(1,2)+2*ex+b*(1+2*ex)<1 and (1-b)*(1-2*ex)-b*(R(1,2)+2*ex)>0,'anchor vertical cover')
    alpha=WM*(c-row_half[0])-lam;beta=WB*(c-row_half[1])-lam;gamma=k*(c-R(1,4))-lam
    need(alpha>0 and beta>0,'variation reduction signs')
    def endpoint_value(X,Y,Z):
        return alpha*abs(X)-A*X+beta*abs(Z-Y)+Blin*(Z-Y)+gamma*(abs(Y)+abs(X-Z))-b*sum(C*abs(z) for C,z in zip(loss,(X,Y,Z)))
    rows=[]
    for sign in (1,-1):
        for mask in range(1,8):
            p=[sign*int(mask>>j&1) for j in range(3)];val=endpoint_value(*p)
            need(val>0,'nonpositive endpoint layer')
            rows.append({'pattern':p,'reserve':str(val)})
    need(cert['layer_table']==rows,'layer coverage or reserve')
    minimum=min(R(r['reserve']) for r in rows)
    need(minimum==R(cert['minimum_layer_reserve']),'minimum reserve')
    # Independent expansion on every signed level layer of ALL six free tilts.
    full=[]
    for sign in (1,-1):
        for mask in range(1,64):
            t=[R(0)]+[R(sign*int(mask>>j&1)) for j in range(6)]
            vm=sum(abs(t[j+1]-t[j]) for j in range(3))
            vb=abs(t[5]-t[4])+abs(t[6]-t[5]);vc=abs(t[4])+abs(t[3]-t[6])
            val=alpha*vm+beta*vb+gamma*vc-A*t[3]+Blin*(t[6]-t[4])-b*sum(C*abs(z) for C,z in zip(loss,(t[3],t[4],t[6])))
            need(val>0 and val>=endpoint_value(t[3],t[4],t[6]),'full variation layer')
            full.append(val)
    # The entire physically possible downward slide is included at q<=Q.
    need(R(91,60)**2+R(91,60)+R(1,2)>R(1105,256),'center radius bound')
    margin=R(15,16)-R(91,60)+R(19,32);need(margin==R(7,480)>0,'downward slide caller')
    # Equality M squares are contained for every allowed nonnegative slide.
    need(1+(R(1,16)+R(11,16)+R(1,2))**2==R(41,16)<R(1105,256),'upper slide containment')
    # r_min=(23-sqrt(1041))/16 is strictly inside the new lower tolerance.
    need(4*1041<65**2 and 1041>23**2,'algebraic lower equality endpoint')
    # At r_min the bottom middle farthest corner has squared norm Q:
    need(R(1041,256)+R(1,4)==R(1105,256),'bottom circle equality')
    return {'base_polynomial_residual_monomials':dependency['polynomial_residual_monomials'],
            'telescoping_owner_cases':telescoping_cases,'endpoint_layers_checked':14,
            'full_tilt_layers_checked':126,'minimum_layer_reserve':str(minimum),
            'full_layer_minimum':str(min(full)),
            'wrong_horizontal_axis_upper_bounds':list(map(str,wrong_horizontal)),
            'correct_horizontal_axis_lower_bounds':list(map(str,positive_horizontal)),
            'unconditional_downward_margin':str(margin)}

def controls():
    q=R(1105,256);count=0;outside_old=0
    for s1,s2 in product((R(0),R(1,8),R(1,2),R(11,16)),repeat=2):
        for r in (R(-9,16),R(-1,8),R(0),min(R(1,8),s1,s2)):
            poses=BASE[:]
            for i,z in ((1,s1),(2,s2),(5,r)):poses[i]=(poses[i][0],poses[i][1]+z)
            norms=[(x+R(s,2))**2+(y+R(t,2))**2 for x,y in poses for s,t in product((-1,1),repeat=2)]
            need(max(norms)==q,'equality disk control')
            need(all(abs(x-X)>=1 or abs(y-Y)>=1 for (x,y),(X,Y) in combinations(poses,2)),'equality overlap control')
            count+=1;outside_old+=int(max(abs(s1),abs(s2),abs(r))>R(1,8))
    return {'rational_equality_controls':count,'controls_outside_old_neighborhood':outside_old}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--negative-controls',action='store_true');args=ap.parse_args()
    raw=(HERE/'wide_slide_certificate.json').read_bytes();cert=json.loads(raw)
    result=check(cert);result.update(controls());negative=[]
    if args.negative_controls:
        changes=[('unsupported global closure',lambda z:z.update(global_A2_closed=True)),
                 ('unproved larger upper slide',lambda z:z.update(middle_row_inner_vertical=['-1/8','3/4'])),
                 ('wrong row midpoint',lambda z:z['row_midpoints'].__setitem__(0,'0')),
                 ('changed endpoint coefficient',lambda z:z['adjusted_linear_coefficients'].__setitem__(0,'0')),
                 ('omitted signed layer',lambda z:z['layer_table'].pop()),
                 ('invented reserve',lambda z:z['layer_table'][0].update(reserve='1')),
                 ('wrong quadratic cost',lambda z:z['quadratic_losses'].__setitem__(0,'0')),
                 ('inflated conclusion',lambda z:z.update(variation_coefficient='1/128'))]
        for name,change in changes:
            bad=copy.deepcopy(cert);change(bad)
            try:check(bad)
            except ValueError:negative.append(name)
            else:raise ValueError('accepted corruption: '+name)
    result.update(result='PASS',arithmetic='Python Fraction only',negative_controls_rejected=negative,
                  certificate_sha256=hashlib.sha256(raw).hexdigest(),
                  verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  base_certificate_sha256=hashlib.sha256((HERE/'sharp_neighborhood_certificate.json').read_bytes()).hexdigest(),
                  global_A2_closed=False,scope='widened local sharp terminal; no complete global caller',
                  separate_human_review_performed=False,lean_or_ci_run=False)
    (HERE/'wide_slide_verification_report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
