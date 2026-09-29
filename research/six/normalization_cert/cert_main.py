"""Supplied single-square certificate predicates after Proposition A.

The central coordinates range over the whole box [0,c0]^2. No pin, window,
axial label, or reduced separator is assumed in the L1/L2 initial state.
"""
from ia import *
from bnb import bnb

CBOX = iv(0,0).union(C0)
ALLSEP = ['OWN','SEC+','SEC-','CE','CW','CN','CS']
PIN_ANGLE = {'E':0.0,'N':1.5707963267948966,'W':2.8797932657906435,
             'D':3.9269908169872414,'S':4.974188368183839}
TWO_PI = 6.283185307179586


def root_around(center):
    return [(center-3.1416,center+3.1416),(0.5,1.2),(-1.2,1.2)]


def basic(box,cx=CBOX,cy=CBOX):
    phi,a,b = (iv(*x) for x in box)
    S = SqBox(phi,a,b)
    if pos(S.contain_gap()): return 'infeasible:contain',S,None
    if neg(S.chart_gap()): return 'infeasible:chart',S,None
    seps = S.separators(cx,cy)
    if all(neg(m) for m in seps.values()):
        return 'infeasible:disjoint',S,seps
    return None,S,seps


A_MIN = arb(177)/200
A_MAX = arb(223)/200
U_MAX = arb(117)/250


def L1_eval(box):
    reason,S,seps = basic(box)
    if reason: return reason
    ok_a = S.a>A_MIN and S.a<A_MAX
    ok_u = S.u<U_MAX
    ok_sec = neg(seps['SEC+']) and neg(seps['SEC-'])
    ok_ax = 9*S.a+11*S.u < 2*PI+7
    if ok_a and ok_u and ok_sec and ok_ax: return 'claim'
    return None


def L2_eval_factory(eps):
    E = arb(eps)
    def ev(box):
        reason,S,seps = basic(box)
        if reason: return reason
        for k,q in PINS.items():
            if pos(S.pin_margin(*q)-E): return 'pin:'+k
        return None
    return ev


WINDOWS = {
    'E':(0.0,(-5,12),(3,10)),
    'N':(1.5707963267948966,(-3,10),(5,12)),
    'W':(3.141592653589793,(-2,3),(5,8)),
    'S':(4.71238898038469,(-5,8),(2,3)),
    'D':(3.9269908169872414,(-15,14),(15,14)),
}
ALLOWED = {'E':{'OWN','CE'},'N':{'OWN','CN'},'W':{'OWN','CW'},
           'S':{'OWN','CS'},'D':{'OWN','CW','CS'}}


def arb_centre(k):
    return {'E':ZERO,'N':PI/2,'W':PI,'S':3*PI/2,'D':5*PI/4}[k]


def L3_eval_factory(k):
    q,cen = PINS[k],arb_centre(k)
    _,(ln,ld),(hn,hd) = WINDOWS[k]
    WLO,WHI = arb(ln)/ld,arb(hn)/hd
    disallowed = [s for s in ALLSEP if s not in ALLOWED[k]]
    def ev(box):
        phi,a,b = (iv(*x) for x in box)
        S = SqBox(phi,a,b)
        if pos(S.contain_gap()): return 'infeasible:contain'
        if neg(S.chart_gap()): return 'infeasible:chart'
        if S.pin_margin(*q)<=0: return 'pin-outside'
        seps = S.separators(CBOX,CBOX)
        dis_ok = all(neg(seps[s]) for s in disallowed)
        if all(neg(m) for m in seps.values()): return 'infeasible:disjoint'
        rel = phi-cen
        if dis_ok and rel>WLO and rel<WHI: return 'claim'
        return None
    return ev


def sep_window_factory(k,s,wlo,whi):
    q,cen = PINS[k],arb_centre(k)
    WLO,WHI = arb(str(wlo)),arb(str(whi))
    def ev(box):
        phi,a,b = (iv(*x) for x in box)
        S = SqBox(phi,a,b)
        if pos(S.contain_gap()): return 'infeasible:contain'
        if neg(S.chart_gap()): return 'infeasible:chart'
        if S.pin_margin(*q)<=0: return 'pin-outside'
        seps = S.separators(CBOX,CBOX)
        if neg(seps[s]): return 'sep-fails'
        rel = phi-cen
        if rel>WLO and rel<WHI: return 'claim'
        return None
    return ev


def run_all(quick=False):
    results = {}
    root = [(-3.1416,3.1416),(0.5,1.2),(-1.2,1.2)]
    for name,ev in [('L1',L1_eval),('L2',L2_eval_factory(arb(1)/100))]:
        st,un,n = bnb(root,ev,[1,1,1],name=name)
        results[name] = (not un,n)
    for k in 'ENWDS':
        st,un,n = bnb(root_around(WINDOWS[k][0]),L3_eval_factory(k),[1,1,1],name='L3-'+k)
        results['L3-'+k] = (not un,n)
    return results


if __name__ == '__main__':
    import sys
    result = run_all()
    print(result)
    sys.exit(0 if all(ok for ok,n in result.values()) else 1)
