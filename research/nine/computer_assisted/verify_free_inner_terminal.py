#!/usr/bin/env python3
"""Independent exact algebra for the free-inner-height terminal.

Standard library only. Reconstructs the two physical polynomial identities,
constant majorants, three scalar reserves, and the equivalent 30-layer check.
It does NOT verify global mask coverage or claim a nine-square UNSAT result.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path

# Sparse multivariate polynomials; a monomial is a sorted tuple of names.
def const(x):return {():F(x)} if x else {}
def var(x):return {(x,):F(1)}
def add(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,F(0))+c
    return {m:c for m,c in out.items() if c}
def scale(a,p):return {m:F(a)*c for m,c in p.items() if a*c}
def mul(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():
            z=tuple(sorted(m+n));out[z]=out.get(z,F(0))+a*b
    return {m:c for m,c in out.items() if c}
def sub(p,q):return add(p,scale(-1,q))
def sq(p):return mul(p,p)

Q=F(1105,256);rho=F(91,60)
w=F(23,64);v=F(9,64);k=F(207,512);WM=4*w;WB=3*v
A=F(851,2048);beta0=F(7,250);tau0=F(501,1000)
PARAMETERS=[(F(1,64),F(3,5)),(F(1,32),F(2,3)),(F(1,18),F(3,4))]
EXPECTED=[
 [F(1318757539,8388608000),F(122602873,1677721600),F(47504353,1677721600)],
 [F(139153883,1048576000),F(9387937,209715200),F(5105737,209715200)],
 [F(3950801,41472000),F(461,8294400),F(68111,8294400)],
]

def physical_identities():
    data=[('0',-F(3,2),F(1,16),-1,1,w),
          ('3', F(3,2),F(1,16), 1,1,w),
          ('L',-F(1),-F(15,16),-1,-1,v),
          ('R', F(1),-F(15,16), 1,-1,v)]
    X={};Y={};dx={};z={};a={};t={};orient={};baseorient={};corners={}
    units={};displacements={}
    for name,x0,y0,s,sg,wt in data:
        dx[name]=var('x'+name);z[name]=var('z'+name)
        a[name]=var('a'+name);t[name]=var('t'+name)
        X[name]=add(const(x0),dx[name]);Y[name]=add(const(y0),z[name])
        cx=add(X[name],scale(F(s,2),a[name]),scale(-F(sg,2),t[name]))
        cy=add(Y[name],scale(F(s,2),t[name]),scale(F(sg,2),a[name]))
        corners[name]=scale(wt,add(sq(cx),sq(cy)))
        L=add(scale(s,X[name]),scale(sg,Y[name]))
        J=add(scale(-sg,X[name]),scale(s,Y[name]))
        orient[name]=scale(wt,add(mul(sub(a[name],const(1)),L),mul(t[name],J)))
        baseorient[name]=scale(wt,add(scale(s*x0+sg*y0,sub(a[name],const(1))),scale(-sg*x0+s*y0,t[name])))
        units[name]=scale(wt/2,sub(add(sq(a[name]),sq(t[name])),const(1)))
        displacements[name]=scale(wt,add(sq(dx[name]),sq(z[name])))
    spanM=sub(sub(X['3'],X['0']),const(3));spanB=sub(sub(X['R'],X['L']),const(2))
    vertical=sub(add(sub(Y['0'],Y['L']),sub(Y['3'],Y['R'])),const(2))
    lhs=sub(add(*corners.values()),const(Q))
    rhs=add(scale(WM,spanM),scale(WB,spanB),scale(k,vertical),*displacements.values(),*orient.values())
    residual=sub(sub(lhs,rhs),add(*units.values()))
    assert residual=={},residual
    ell=var('ell');rr=var('r')
    grouped={
      '0':(add(scale(w,sub(sub(const(1),a['0']),t['0'])),scale(k,ell)),scale(w,sub(sub(a['0'],const(1)),t['0']))),
      '3':(add(scale(w,sub(sub(a['3'],const(1)),t['3'])),scale(k,rr)),scale(w,add(sub(a['3'],const(1)),t['3']))),
      'L':(sub(scale(v,add(sub(const(1),a['L']),t['L'])),scale(k,ell)),scale(v,add(sub(const(1),a['L']),scale(2,t['L'])))),
      'R':(sub(scale(v,add(sub(a['R'],const(1)),t['R'])),scale(k,rr)),scale(v,sub(sub(const(1),a['R']),scale(2,t['R'])))),
    }
    products=add(scale(WB,sub(mul(t['L'],z['L']),mul(t['R'],z['R']))),
                 scale(k,add(mul(ell,sub(dx['0'],dx['L'])),mul(rr,sub(dx['3'],dx['R'])))))
    total=add(sub(add(*orient.values()),add(*baseorient.values())),products)
    target=add(*(add(mul(grouped[name][0],dx[name]),mul(grouped[name][1],z[name])) for name in grouped))
    assert sub(total,target)=={}
    # Corruption controls: an incorrect physical coefficient must be detected.
    assert sub(total,add(target,scale(F(1,1000),mul(t['L'],z['L']))))!={}
    assert sub(sub(lhs,add(rhs,const(F(1,1000)))),add(*units.values()))!={}

def scalar_check():
    bmax=F(1,18)
    assert beta0-bmax/(2-bmax*bmax)==F(29,161750)>0
    assert tau0-1/(2-bmax*bmax)==F(147,647000)>0
    P=w*(1+beta0)+k;H=v*(1+beta0)+k
    CM=(2*P*P+w*w*(1+beta0)**2)/(4*w)+k*k/(2*v)+F(25,16)*w*tau0
    CB=(2*H*H+v*v*(2+beta0)**2)/(4*v)+k*k/(2*w)+F(31,16)*v*tau0
    assert CM==F(229167423,128000000)
    assert CB==F(202189959,128000000)
    assert F(9,5)-CM==F(1232577,128000000)>0
    assert F(79,50)-CB==F(50041,128000000)>0
    assert rho*rho+rho+F(1,2)-Q==F(31,57600)>0
    cmin=(1-bmax-3*bmax*bmax-4*bmax**3)/2
    margins={
      'horizontal_wrong_axis':1-(bmax*F(89,60)+rho-F(3,5)),
      'horizontal_correct_sign':(1-bmax*bmax)*F(11,30)-bmax*(rho-F(3,5)),
      'vertical_wrong_axis':1-(F(3,4)+bmax*(rho+F(1,8))),
      'vertical_correct_sign':(1-bmax*bmax)*F(7,20)-bmax*F(3,4),
      'row_variation':cmin-(rho-F(3,5))/2,
      'shoulder_height':F(7,8)-F(3,4)*bmax-F(4,5),
      'uniform_endpoint_reserve':F(243,500)*WM-F(1,10)-A-k/4,
      'uniform_shoulder_reserve':k*(cmin-F(1,4))-F(79,50)*bmax,
    }
    expected=[F(1,1080),F(1529,4860),F(343,2160),F(1991,6480),F(13,1458),F(1,30),F(10499,128000),F(461,8294400)]
    assert list(margins.values())==expected
    assert all(x>0 for x in margins.values())
    rows=[]
    for (b,floor),expected in zip(PARAMETERS,EXPECTED):
      c=(1-b-3*b*b-4*b**3)/2;half=(rho-floor)/2;mid=F(15,16)-(rho+floor)/2
      alpha=F(243,500)*WM-F(9,5)*b
      beta=WB*(c-half);gamma=k*(c-F(1,4));B=F(225,2048)+WB*mid
      p=alpha-A-gamma;q=gamma-F(79,50)*b;r=q+beta-B
      assert [p,q,r]==expected and min(p,q,r)>0
      assert B>0 and beta>0
      phi=F(11,24)+F(51023,10800)*b+F(47,16)*b*b+F(47,12)*b**3
      assert r==WB*(floor-phi)
      def expression(t):
          x,y,l,rr=t
          return alpha*(abs(x)+abs(y))+beta*abs(rr-l)+gamma*(abs(x-l)+abs(y-rr))+A*(x-y)+B*(rr-l)-F(79,50)*b*(abs(l)+abs(rr))
      # Redundant exact full signed-layer replay, not a substitute for the hand reduction.
      vals=[]
      for mask in range(1,16):
        for sign in (-1,1):
          t=[F(sign*((mask>>i)&1)) for i in range(4)]
          val=expression(t);lower=p*(abs(t[0])+abs(t[1]))+min(q,r)*(abs(t[2])+abs(t[3]))
          assert val>=lower>0
          vals.append(val)
      rows.append({'tilt_bound':str(b),'center_floor':str(floor),'endpoint_reserve':str(p),'shoulder_reserve':str(q),'difference_reserve':str(r),'minimum_signed_layer':str(min(vals))})
    return {'geometry_margins':{k:str(v) for k,v in margins.items()},'parameter_rows':rows}

def main():
    physical_identities();report=scalar_check()
    report.update({'status':'PASS','polynomial_identities':2,'signed_layers':90,'corruptions_rejected':2,'full_masks_closed':0,'global_coverage_proved':False,'independent_human_or_kernel_review':False})
    path=Path(__file__).with_name('free_inner_terminal_verification.json');path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
