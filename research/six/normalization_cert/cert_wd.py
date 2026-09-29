"""Supplied six-coordinate W/D ordering certificate.

Assume both squares satisfy the central-box conditions and their assigned
open pins, and use the L1 chart bounds. Search for phi_W>=phi_D while retaining
all four undirected SAT axes for the pair. Pair disjointness is essential.
"""
from ia import *
from bnb import bnb
from cert_main import CBOX

qW,qD = PINS['W'],PINS['D']


def square_ok(S):
    if pos(S.contain_gap()): return 'contain'
    if all(neg(m) for m in S.separators(CBOX,CBOX).values()): return 'disjoint-C'
    return None


def pair_sep_margins(S,T):
    dx,dy = T.P1-S.P1,T.P2-S.P2
    out = []
    for vx,vy in ((S.c,S.s),(-S.s,S.c),(T.c,T.s),(-T.s,T.c)):
        distance = abs(vx*dx+vy*dy)
        hs = (abs(vx*S.c+vy*S.s)+abs(-vx*S.s+vy*S.c))/2
        ht = (abs(vx*T.c+vy*T.s)+abs(-vx*T.s+vy*T.c))/2
        out.append(distance-hs-ht)
    return out


def ev(box):
    pW,aW,bW,pD,aD,bD = (iv(*x) for x in box)
    if pW<pD: return 'order-ok'
    S,T = SqBox(pW,aW,bW),SqBox(pD,aD,bD)
    if S.pin_margin(*qW)<=0: return 'W-pin-out'
    if T.pin_margin(*qD)<=0: return 'D-pin-out'
    r = square_ok(S)
    if r: return 'W-'+r
    r = square_ok(T)
    if r: return 'D-'+r
    if all(neg(m) for m in pair_sep_margins(S,T)): return 'pair-overlap'
    return None


def root_box():
    return [
        (math.pi-2/3-1e-9,math.pi+5/8+1e-9),(0.884,1.116),(-0.469,0.469),
        (5*math.pi/4-15/14-1e-9,5*math.pi/4+15/14+1e-9),(0.884,1.116),(-0.469,0.469),
    ]


if __name__ == '__main__':
    import sys
    st,un,n = bnb(root_box(),ev,[1,2,1,1,2,1],max_boxes=30_000_000,name='W/D order')
    print('CERTIFIED' if not un else 'FAILED',un[:3])
    sys.exit(0 if not un else 1)
