#!/usr/bin/env python3
"""Exact full-domain opposite-return side-N both-unique exclusion.

The original parameters are (s,b,H,d). The complete loaded-endpoint cone
supplies the strict obtuse-axis and moment-sector predicates. Actual loaded
square positions follow from the full physical-circle identity. No new
support mean, force, mask, or point realization is selected. The two physical
radial endpoint alternatives are proved separately.

The shared engine checks outward integer interval arithmetic and every
closed binary split. No unresolved cell is accepted as a proof leaf.
"""
from __future__ import annotations
from fractions import Fraction
import n9_physical_two_side_certificate as engine
from n9_physical_two_side_certificate import I, D, ceildiv

engine.KIND='physical_two_opposite_return_side_bridge_unique_endpoints'
engine.ROOT=(engine.ROOT[0],(D//68,ceildiv(2*D,5)),engine.ROOT[2],engine.ROOT[3])
engine.NAMES=('s','b','H','d')
HALF=I.q(1,2)
QUARTER=I.q(1,4)


def clip(x,lo,hi):
    low=max(x.lo,lo);high=min(x.hi,hi)
    if low>high:raise ArithmeticError('empty necessary interval')
    return I(low,high)


def div(x,y):
    if y.lo<=0:raise ArithmeticError('positive divisor not bounded away from zero')
    return x*I(D*D//y.hi,ceildiv(D*D,y.lo))


def misses(x,z=0):return x.lo>z or x.hi<z


def classify(box):
    try:
        s,b,H,d=[I(*v) for v in box]
        a=(1-b.sq()).sqrt();c=(1-s.sq()).sqrt()
        if c.hi<=I.q(3,4).lo:return 'c_domain'
        D0=1-a+H*s;N0=1-H*c+b;t=H-HALF
        u=a*c-b*s;y=a*s+b*c;e=u-y
        if e.hi<=0:return 'q_positive'
        if (5*e-18*b).lo>=0:return 'return_ratio'
        for name,z in [('x',1-D0),('l',1-N0)]:
            if z.hi<=0 or z.lo>=D:return name+'_domain'
        eq=b*t*N0-(d*s+HALF*c)*e*D0
        if misses(eq):return 'full_torque'
        # The full physical mask/cone join proves tau=bvec.cvec<0 for
        # this entire both-unique alternative. All canceled scales are >0.
        tau_numerator=N0*(s*b+e)-c*b*D0
        if tau_numerator.lo>=0:return 'endpoint_axes_not_obtuse'
        R2=(d+1).sq()+QUARTER
        if R2.lo>I.q(1105,256).hi or R2.hi<I.q(79,40).sq().lo:return 'radius'
        rw=(D0.sq()+N0.sq()).sqrt()
        Kx=d-c+s*N0;Ky=HALF+s+c*N0
        Lx=d-u-y;Ly=HALF-H+y-u
        X=-c*D0+s*N0;Y=s*D0+c*N0;J=Kx*X+Ky*Y
        if (J-d*rw).lo>0:return 'B_support'
        if ((Kx.sq()+Ky.sq()+1-R2)*rw+2*J).lo>0:return 'B_point'
        # The unchanged C direction is normalized without dividing by q.
        CX=b+s*e;CY=c*e;rc=(b.sq()+e.sq()+2*b*s*e).sqrt()
        LC=Lx*CX+Ly*CY
        if ((Lx.sq()+Ly.sq()+1-R2)*rc-2*LC).lo>0:return 'C_point'
        bx=clip(div(X,rw),-D,D);by=clip(div(Y,rw),0,D)
        cx=clip(div(CX,rc),0,D);cy=clip(div(CY,rc),0,D)
        Kb=Kx*bx+Ky*by;Kw=Kx*by-Ky*bx
        Lc=Lx*cx+Ly*cy;Lw=-Lx*cy+Ly*cx
        beta=Kb+HALF;eta=Lc-HALF
        radB=R2-(beta.abs()+HALF).sq()
        radC=R2-(eta.abs()+HALF).sq()
        if radB.hi<D//4:return 'B_no_contained_unit'
        if radC.hi<D//4:return 'C_no_contained_unit'
        TB=I(max(D//4,radB.lo),radB.hi).sqrt()-HALF
        TC=I(max(D//4,radC.lo),radC.hi).sqrt()-HALF
        tau=clip(bx*cx+by*cy,-D,D)
        sigma=clip(by*cx-bx*cy,0,D)
        # Full positive endpoint forces in the proven strict support sector
        # force precisely these physical signs and the unique own corners.
        if beta.hi<=0 or eta.lo>=0 or TB.hi<=0 or TC.hi<=0:return 'unique_circle_frame'
        shiftB=TB-Kw;shiftC=-TC-Lw
        if shiftB.lo>D//2 or shiftB.hi<-D//2 or shiftC.lo>D//2 or shiftC.hi<-D//2:return 'original_port_outside_side'
        Tb=beta-HALF;Tw=TB-HALF
        Uc=eta+HALF;Uw=-TC+HALF
        nb=Tb-Uc*tau-Uw*sigma
        nw=Tw-Uc*sigma+Uw*tau
        nc=Tb*tau+Tw*sigma-Uc
        nz=Tb*sigma-Tw*tau-Uw
        if min(nb.hi,nw.hi,nc.hi,nz.hi)<=0:return 'strict_endpoint_support_sector'
        if (nw-nb).hi<=0 or (nz-nc).hi<=0:return 'strict_endpoint_moment_sector'
        return None
    except ArithmeticError:
        # An inconclusive/zero normalization never closes a cell.
        return None


def choose(box):
    widths=[Fraction(p[1]-p[0],engine.ROOT[k][1]-engine.ROOT[k][0]) for k,p in enumerate(box)]
    return max(range(4),key=lambda k:widths[k]*(1 if k<3 else Fraction(1,3)))


engine.classify=classify
engine.choose=choose

if __name__=='__main__':engine.main()
