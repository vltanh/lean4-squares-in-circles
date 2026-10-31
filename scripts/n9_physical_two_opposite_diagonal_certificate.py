#!/usr/bin/env python3
"""Exact full-domain diagonal-N exclusion in the opposite-D-vertex row.

Uses the dyadic interval operations and binary-cover replay of the companion
side-return checker, with an explicitly different domain and classification.
The associated hand theorem proves every geometry-to-interval implication.
"""
from __future__ import annotations
import n9_physical_two_side_certificate as engine
from n9_physical_two_side_certificate import I, D

engine.KIND='physical_two_opposite_return_diagonal_bridge'
engine.ROOT=(engine.ROOT[0],(0,engine.ceildiv(2*D,5)),engine.ROOT[2],engine.ROOT[3])

def classify(box):
    s,b,H,d=[I(*v) for v in box]
    a=(1-b.sq()).sqrt();c=(1-s.sq()).sqrt()
    D0=1-a+H*s;N0=1-H*c+b;t=H-I.q(1,2)
    u=a*c-b*s;y=a*s+b*c;e=u-y
    if e.hi<=0:return 'q_positive'
    if (5*e-18*b).lo>=0:return 'return_ratio'
    eq=b*t*N0-(d*s+I.q(1,2)*c)*e*D0
    if eq.lo>0 or eq.hi<0:return 'full_torque'
    orthogonal=N0*(s*b+e)-c*b*D0
    if orthogonal.lo>0 or orthogonal.hi<0:return 'endpoint_axes_not_orthogonal'
    W0=D0.sq()+N0.sq();rootW=W0.sqrt()
    Kx=d-c+s*N0;Ky=I.q(1,2)+s+c*N0
    X=-c*D0+s*N0;Y=s*D0+c*N0;J=Kx*X+Ky*Y
    if (J-d*rootW).lo>0:return 'B_support'
    radius=(d+1).sq()+I.q(1,4)
    if ((Kx.sq()+Ky.sq()+1-radius)*rootW+2*J).lo>0:return 'B_point'
    # On the proven perpendicular endpoint-axis locus, these are the two
    # components of K-L multiplied by sqrt(W0), with no division.
    Pb=(D0-b)*D0+(1+a)*N0
    Pc=-(D0-b)*N0+(1+a)*D0
    if (Pb-rootW).lo>0 and (Pc-rootW).lo>0 and rootW.lo>0:
        return 'both_support_projections_gt_one'
    return None

engine.classify=classify

if __name__=='__main__':engine.main()
