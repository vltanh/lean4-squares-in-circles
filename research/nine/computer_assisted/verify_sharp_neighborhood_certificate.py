#!/usr/bin/env python3
"""Separate exact algebra check of the sharp-neighborhood hand proof.

Only Python's standard library is used. Two physical polynomial identities,
all fourteen homogeneous layer directions, exact physical controls and mutation
controls are checked. The accompanying source proves the universal implication.
This is not a separate human review, global extraction, or Lean verification.
"""
from fractions import Fraction as R
from pathlib import Path
from itertools import product,combinations
import argparse,copy,hashlib,json

def need(ok,msg):
    if not ok:raise ValueError(msg)
def C(v):
    v=R(v);return {():v} if v else {}
def V(n):return {(n,):R(1)}
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,R(0))+c
    return {m:c for m,c in d.items() if c}
def scale(v,p):return {m:R(v)*c for m,c in p.items() if v*c}
def sub(p,q):return add(p,scale(-1,q))
def mul(p,q):
    d={}
    for m,c in p.items():
        for n,a in q.items():
            t=tuple(sorted(m+n));d[t]=d.get(t,R(0))+c*a
    return {t:a for t,a in d.items() if a}
def sq(p):return mul(p,p)
BASE=[(R(-3,2),R(1,16)),(R(-1,2),R(1,16)),(R(1,2),R(1,16)),(R(3,2),R(1,16)),
      (R(-1),R(-15,16)),(R(0),R(-15,16)),(R(1),R(-15,16))]
SIGNS={0:(-1,1),3:(1,1),4:(-1,-1),6:(1,-1)}

def check(z):
    need(z['schema']=='n9_sharp_neighborhood_v3' and z['global_A2_closed'] is False,'semantics')
    q,e,b=R(z['target_q']),R(z['position_tolerance']),R(z['tilt_bound']);h=e
    need((q,e,b)==(R(1105,256),R(1,8),R(1,64)),'geometric constants')
    weights={int(i):R(w) for i,w in z['anchor_weights'].items()}
    need(set(weights)=={0,3,4,6} and sum(weights.values())==1 and min(weights.values())>0,'weights')
    wm,wb=map(R,z['horizontal_weights']);k=R(z['vertical_weight'])
    x=[V('x'+str(i)) for i in range(7)];y=[V('y'+str(i)) for i in range(7)]
    a=[V('a'+str(i)) for i in range(7)];t=[V('b'+str(i)) for i in range(7)]
    actual={};squares={};angular={};unit={}
    for i,w in weights.items():
        s,v=SIGNS[i];cx,cy=BASE[i]
        X=add(x[i],scale(R(s,2),a[i]),scale(R(-v,2),t[i]));Y=add(y[i],scale(R(s,2),t[i]),scale(R(v,2),a[i]))
        actual=add(actual,scale(w,add(sq(X),sq(Y))))
        squares=add(squares,scale(w,add(sq(sub(x[i],C(cx))),sq(sub(y[i],C(cy))))))
        L=add(scale(s,x[i]),scale(v,y[i]));J=add(scale(-v,x[i]),scale(s,y[i]))
        angular=add(angular,scale(w,add(mul(sub(a[i],C(1)),L),mul(t[i],J))))
        unit=add(unit,scale(w/2,add(sq(a[i]),sq(t[i]),C(-1))))
    spans=add(scale(wm,add(x[3],scale(-1,x[0]),C(-3))),scale(wb,add(x[6],scale(-1,x[4]),C(-2))),
              scale(k,add(y[0],scale(-1,y[4]),y[3],scale(-1,y[6]),C(-2))))
    need(not add(actual,C(-q),scale(-1,spans),scale(-1,squares),scale(-1,angular),scale(-1,unit)),'corner identity')
    deriv={i:weights[i]*(-SIGNS[i][1]*BASE[i][0]+SIGNS[i][0]*BASE[i][1]) for i in weights}
    need(deriv=={0:R(529,1024),3:R(-529,1024),4:R(-9,1024),6:R(9,1024)},'tilt coefficients')
    A=deriv[0]-k/4;B=deriv[6]+k/4
    need((A,B)==(R(851,2048),R(225,2048)),'vertical combination')
    dx={i:V('dx'+str(i)) for i in weights};dy={i:V('dy'+str(i)) for i in weights}
    aa={i:(C(1) if i==0 else V('aa'+str(i))) for i in weights};tt={i:(C(0) if i==0 else V('tt'+str(i))) for i in weights}
    left,right=V('ownerL'),V('ownerR');offset={}
    for i,w in weights.items():
        s,v=SIGNS[i]
        term=add(mul(sub(aa[i],C(1)),add(scale(s,dx[i]),scale(v,dy[i]))),mul(tt[i],add(scale(-v,dx[i]),scale(s,dy[i]))))
        offset=add(offset,scale(w,term))
    offset=add(offset,scale(-wm,mul(tt[3],dy[3])),scale(wb,sub(mul(tt[4],dy[4]),mul(tt[6],dy[6]))),
               scale(k,add(mul(left,sub(dx[0],dx[4])),mul(right,sub(dx[3],dx[6])))))
    w=weights[3];v=weights[4]
    expected=add(scale(k,mul(left,dx[0])),
        mul(add(scale(w,add(aa[3],C(-1),scale(-1,tt[3]))),scale(k,right)),dx[3]),
        mul(scale(w,add(aa[3],C(-1),scale(-3,tt[3]))),dy[3]),
        mul(add(scale(v,add(C(1),scale(-1,aa[4]),tt[4])),scale(-k,left)),dx[4]),
        mul(scale(v,add(C(1),scale(-1,aa[4]),scale(2,tt[4]))),dy[4]),
        mul(add(scale(v,add(aa[6],C(-1),tt[6])),scale(-k,right)),dx[6]),
        mul(scale(v,add(C(1),scale(-1,aa[6]),scale(-2,tt[6]))),dy[6]))
    need(not sub(offset,expected),'offset identity')
    c=(1-4*b)/2;need(c==R(z['pair_variation_coefficient']),'relative variation bound')
    hw=b*(1+2*e)+2*h;hs=(1-b)*(1-2*e)-2*b*h
    vw=R(1,2)+2*e+b*(1+2*h);vs=(1-b)*(1-2*h)-b*(R(1,2)+2*e)
    need(hw<1 and vw<1 and hs>0 and vs>0,'axis/sign cover')
    need(0<b<=R(1,4) and b/(1-b)<=2*b,'frame Lipschitz')
    need(1-b-2*b*b>=1-2*b and b*(1+4*b*b)<=2*b,'relative-frame inequality')
    P=w*(1+b)+k;H=v*(1+b)+k
    losses=[(2*P*P+w*w*(3+b)**2)/(2*w)+k*k/v+w*R(25,16),
            k*k/(2*w)+(H*H+v*v*(2+b)**2)/(2*v)+v*R(31,16),
            k*k/w+(2*H*H+v*v*(2+b)**2)/(2*v)+v*R(31,16)]
    need(losses==list(map(R,z['quadratic_loss_coefficients'])),'quadratic losses')
    lam=R(z['claimed_variation_coefficient']);need(lam==R(1,256),'conclusion coefficient')
    need(wm*(c-h)>lam and wb*(c-h)>lam,'chain variation minimization')
    rows=[]
    for sign in (1,-1):
        for mask in range(1,8):
            X,Y,Z=[sign*int(mask>>i&1) for i in range(3)]
            val=(wm*(c-h)-lam)*abs(X)-A*X+(wb*(c-h)-lam)*abs(Z-Y)+B*(Z-Y)+(k*(c-R(1,4))-lam)*(abs(Y)+abs(X-Z))-b*sum(C*abs(x) for C,x in zip(losses,(X,Y,Z)))
            need(val>0,'nonpositive layer');rows.append({'pattern':[X,Y,Z],'reserve':str(val)})
    need(z['layer_table']==rows,'incomplete/corrupted layer cover')
    minimum=min(R(row['reserve']) for row in rows);need(minimum==R(z['minimum_layer_reserve']),'layer minimum')
    need(R(z['retained_anchor_square_fraction'])==R(1,2),'completed square factor')
    need(1+(R(1,16)+h+R(1,2))**2<q and R(1,4)+(R(15,16)+h+R(1,2))**2<q,'equality containment')
    return dict(polynomial_residual_monomials=[0,0],layer_rows_checked=14,minimum_layer_reserve=str(minimum),
                wrong_axis_upper_bounds=list(map(str,(hw,vw))),correct_axis_positive_lower_bounds=list(map(str,(hs,vs))),
                quadratic_loss_coefficients=list(map(str,losses)))

def controls():
    q=R(1105,256);h=R(1,8);beta=R(1,64);weights={0:R(23,64),3:R(23,64),4:R(9,64),6:R(9,64)}
    def packing(ps):
        corners=[]
        for x,y,a,b in ps:
            need(a*a+b*b==1,'frame control')
            corners += [(x+(s*a-t*b)/2)**2+(y+(s*b+t*a)/2)**2 for s,t in product((-1,1),repeat=2)]
        for p,z in combinations(ps,2):
            x,y,a,b=p;X,Y,A,B=z
            need(2*max(abs((X-x)*u+(Y-y)*v) for u,v in ((a,b),(-b,a),(A,B),(-B,A)))>=1+abs(a*A+b*B)+abs(a*B-b*A),'overlap control')
        return max(corners)
    eq=0
    for s1,s2 in product((R(0),h/2,h),repeat=2):
        for t in (-h,R(0),min(s1,s2)):
            cc=BASE[:]
            for i,z in ((1,s1),(2,s2),(5,t)):cc[i]=(cc[i][0],cc[i][1]+z)
            need(packing([(x,y,R(1),R(0)) for x,y in cc])==q,'equality control');eq+=1
    tilted=0
    for t in (R(1,2048),R(1,512),R(1,128)):
        a=(1-t*t)/(1+t*t);b=2*t/(1+t*t);d=(a+b-1)/2;cc=BASE[:]
        cc[0]=(cc[0][0]-d,cc[0][1]);cc[1]=(cc[1][0],cc[1][1]+d)
        for i in (2,3):cc[i]=(cc[i][0]+d,cc[i][1])
        ps=[(x,y,a if i==1 else R(1),b if i==1 else R(0)) for i,(x,y) in enumerate(cc)]
        radius=packing(ps);D=sum(weights[i]*((cc[i][0]-BASE[i][0])**2+(cc[i][1]-BASE[i][1])**2) for i in weights)
        need(b<=beta and radius-q>=2*b/256+D/2,'quantitative tilted control');tilted+=1
    return {'exact_equality_controls':eq,'genuinely_tilted_controls':tilted}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--negative-controls',action='store_true');args=ap.parse_args()
    p=Path(__file__).resolve().parent;raw=(p/'sharp_neighborhood_certificate.json').read_bytes();z=json.loads(raw)
    report=check(z);report.update(controls());neg=[]
    if args.negative_controls:
        edits=[('changed target',lambda z:z.update(target_q='1106/256')),('changed weight',lambda z:z['anchor_weights'].update({'0':'24/64'})),
          ('changed span',lambda z:z.update(horizontal_weights=['24/16','27/64'])),('inflated bound',lambda z:z.update(claimed_variation_coefficient='1/8')),
          ('missing layer',lambda z:z['layer_table'].pop()),('false layer',lambda z:z['layer_table'][0].update(reserve='1')),
          ('lost square factor',lambda z:z.update(retained_anchor_square_fraction='1')),('unsupported A2 flag',lambda z:z.update(global_A2_closed=True))]
        for name,edit in edits:
            bad=copy.deepcopy(z);edit(bad)
            try:check(bad)
            except ValueError:neg.append(name)
            else:raise ValueError('mutation accepted '+name)
    report.update(result='PASS',arithmetic='Python Fraction; sparse polynomial expansion',negative_controls_rejected=neg,
      certificate_sha256=hashlib.sha256(raw).hexdigest(),verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      global_A2_closed=False,scope='conditional sharp neighborhood; global caller not proved',separate_human_review_performed=False,lean_or_ci_run=False)
    (p/'sharp_neighborhood_verification_report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
