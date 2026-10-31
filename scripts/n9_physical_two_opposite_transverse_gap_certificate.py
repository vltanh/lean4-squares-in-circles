#!/usr/bin/env python3
"""Whole opposite-return transverse gaps, with exact finite replay.

The geometric soundness and complete endpoint-mask join are proved in
PHYSICAL_TWO_OPPOSITE_RETURN_COMPLETE_LOADED_ENDPOINT_CONE_2026_10_30.md.
This uses only the unchanged full hub torque, inherited return-ratio window,
and the actual owned B square.  No equation on B or C is shortened.
"""
from __future__ import annotations
import n9_physical_two_side_certificate as engine
from n9_physical_two_side_certificate import I, D

engine.KIND = 'physical_two_opposite_return_full_transverse_gap'
engine.ROOT = (engine.ROOT[0], (0, engine.ceildiv(2*D, 5)),
               engine.ROOT[2], engine.ROOT[3])


def classify(box):
    s, b, H, d = [I(*v) for v in box]
    a = (1-b.sq()).sqrt()
    c = (1-s.sq()).sqrt()
    D0 = 1-a+H*s
    N0 = 1-H*c+b
    t = H-I.q(1, 2)
    u = a*c-b*s
    y = a*s+b*c
    e = u-y
    if e.hi <= 0:
        return 'q_positive'
    if (5*e-18*b).lo >= 0:
        return 'return_ratio'
    eq = b*t*N0-(d*s+I.q(1, 2)*c)*e*D0
    if eq.lo > 0 or eq.hi < 0:
        return 'full_torque'
    WB = (D0.sq()+N0.sq()).sqrt()
    C1 = b*c
    C2 = s*b+e
    WC = (C1.sq()+C2.sq()).sqrt()
    den = D0*C2+N0*C1
    Pb = (D0-b)*D0+(1+a)*N0
    Pc = -(D0-b)*C1+(1+a)*C2
    if (WB.lo > 0 and WC.lo > 0 and
            (Pb*WC-den).lo > 0 and (Pc*WB-den).lo > 0):
        return 'both_transverse_gaps'
    Kx = d-c+s*N0
    Ky = I.q(1, 2)+s+c*N0
    X = -c*D0+s*N0
    Y = s*D0+c*N0
    J = Kx*X+Ky*Y
    if (J-d*WB).lo > 0:
        return 'B_support'
    R2 = (d+1).sq()+I.q(1, 4)
    if ((Kx.sq()+Ky.sq()+1-R2)*WB+2*J).lo > 0:
        return 'B_point'
    return None


engine.classify = classify

if __name__ == '__main__':
    engine.main()
