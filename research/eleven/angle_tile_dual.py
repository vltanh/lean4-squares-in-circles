"""Exact rational weak dual certificates for grouped orientation rectangles.

These helper routines do not perform discovery optimization. Each supplied
certificate is independently validated before its lower bound is returned.
"""
from fractions import Fraction as F
from check_angle_neighborhood import D2,R,frame,dot,norm2,add,scale,abs_upper

BOUNDARY=[0,2,3,5,6,7,9,10]
SIGNS=[(-1,-1),(-1,1),(1,-1),(1,1)]
NAMES=['A','Z','C','D','E','F','G','I','K']

def verify_weights(data):
    lam=[[F(x) for x in row] for row in data['lambda']]
    par=[F(x) for x in data['parameters']]
    assert len(lam)==8 and all(len(row)==4 for row in lam)
    assert len(par)==9
    assert all(x>=0 for row in lam for x in row) and all(x>=0 for x in par)
    assert sum(x for row in lam for x in row)==1
    A,Z,C,D,E,Fv,G,Iv,K=par
    # Every unloaded force vanishes identically for all angles, including
    # endpoint/equal-angle cases. These are sufficient identities, not a
    # claim to enumerate all possible zero-force identities at endpoints.
    zero_force=[A==0 and D==C,C==E==0,Z==E==0,Fv==A==0,Fv==G==0,Z==0 and G==Iv,Iv==Z==K==0,D==K==0]
    for row,condition in zip(lam,zero_force):
        assert sum(row)>0 or condition
    return lam,par

def lower_dual(ta,tb,lam,par,delta_sign=1):
    """The function D in q>=D, with signed lower support for delta.

On 0<=ta,tb<=1, frames lie in the closed first quadrant, cd>=0,
so every edge weight below is nonnegative. Signed support <= physical
support permits boxes straddling ta=tb without omitting the tie.
"""
    assert delta_sign in [-1,1]
    ua,va=frame(ta);ub,vb=frame(tb)
    ca,sa=ua;cb,sb=ub
    cd=ca*cb+sa*sb;sd=ca*sb-sa*cb
    A,Z,C,D,E,Fv,G,Iv,K=[D2(x) for x in par]
    B=Z*cd;H=Z*cb;J=Z*sa
    ka=(1+ca+sa)/2;kb=(1+cb+sb)/2;kd=(1+cd+delta_sign*sd)/2
    total=D2(F(1,2))+3*A+B*(1+ka)+C+D*kb+E+Fv+G*ka+H+(Iv+J)*kd+K
    forces=[(D-C,A),(C,E),(B,-E),(Fv,-A),(-Fv+G*sa,-G*ca),
            add(scale(-H,ua),scale(G-Iv,va)),
            add(add(scale(Iv,va),scale(J,vb)),scale(-K,ub)),
            (-D+K*cb,K*sb)]
    zero=ta*0;one=zero+1
    frames=[((one,zero),(zero,one))]*5+[(ua,va),(ub,vb),(ub,vb)]
    for row,force,(u,v) in zip(lam,forces,frames):
        L=sum(row)
        if L==0:continue
        vx=sum(w*e for w,(e,f) in zip(row,SIGNS))/2
        vy=sum(w*f for w,(e,f) in zip(row,SIGNS))/2
        V=add(scale(vx,u),scale(vy,v))
        total=total-norm2(add(force,scale(-2,V)))/(4*L)
    return total

def tile_lower_bound(bounds,data):
    """Taylor lower bound on a rational closed rectangle.

Uses exact value and gradient intervals at its rational midpoint and an
outward Hessian bound on the full rectangle. Shared edges are included.
"""
    xa,xb,ya,yb=map(F,bounds)
    assert 0<=xa<=xb<=1 and 0<=ya<=yb<=1
    lam,par=verify_weights(data)
    sign=data.get('delta_sign',1)
    center=[(xa+xb)/2,(ya+yb)/2];half=[(xb-xa)/2,(yb-ya)/2]
    mid=lower_dual(D2(center[0],[1,0]),D2(center[1],[0,1]),lam,par,sign)
    region=lower_dual(D2(R(xa,xb),[1,0]),D2(R(ya,yb),[0,1]),lam,par,sign)
    first=sum(abs_upper(g)*r for g,r in zip(mid.g,half))
    second=sum(abs_upper(region.h[i][j])*half[i]*half[j] for i in range(2) for j in range(2))/2
    return mid.v.lo-first-second
