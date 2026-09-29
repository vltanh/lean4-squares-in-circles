"""Supplied L3-prime, L6 cap-piercing, and L7 own-moving-pin predicates."""
from ia import *
from bnb import bnb
from cert_main import CBOX,sep_window_factory

PI_F = 3.141592653589793
SEP_WINDOWS = {
 ('E','OWN'):(0.0,-0.4115,0.2651),
 ('E','CE'):(0.0,-0.2041,0.2041),
 ('N','OWN'):(PI_F/2,-0.2651,0.4115),
 ('N','CN'):(PI_F/2,-0.2041,0.2041),
 ('W','OWN'):(PI_F,-0.6645,0.6190),
 ('W','CW'):(PI_F,-0.3852,0.3852),
 ('S','OWN'):(3*PI_F/2,-0.6190,0.6645),
 ('S','CS'):(3*PI_F/2,-0.3852,0.3852),
 ('D','OWN'):(5*PI_F/4,-1.0033,1.0033),
 ('D','CW'):(5*PI_F/4,-1.0687,-0.4002),
 ('D','CS'):(5*PI_F/4,0.4002,1.0687),
}


def run_sep_windows():
    out = {}
    for (k,s),(cen,l,h) in SEP_WINDOWS.items():
        root = [(cen-3.1416,cen+3.1416),(0.5,1.2),(-1.2,1.2)]
        st,un,n = bnb(root,sep_window_factory(k,s,l,h),[1,1,1],name=f'L3-prime {k}/{s}')
        out[k,s] = (not un,n)
    return out


H_LO,H_HI = 0.3871,0.6129  # a superset of [3/2-rho0,rho0-1/2]


def L6_eval_factory(eps):
    E = arb(eps)
    def ev(box):
        h,th,ap,bp = (iv(*x) for x in box)
        s,c = th.sin_cos()
        if pos((abs(ap)+HALF)**2+(abs(bp)+HALF)**2-Q0):
            return 'infeasible:contain'
        P1,w = ap*c-bp*s,(abs(c)+abs(s))/2
        if neg(P1-w-h): return 'infeasible:cap'
        Z = h+HALF
        m1,m2 = HALF-abs(Z*c-ap),HALF-abs(-Z*s-bp)
        if pos(m1-E) and pos(m2-E): return 'claim'
        return None
    return ev


def run_L6(eps=None):
    if eps is None: eps = arb(1)/30
    root = [(H_LO,H_HI),(-0.7854,0.7854),(-1.3,1.3),(-1.3,1.3)]
    st,un,n = bnb(root,L6_eval_factory(eps),[1,1,1,1],name='L6 cap piercing')
    return not un,n


def L7_eval_factory(eps):
    E,qE = arb(eps),PINS['E']
    def ev(box):
        phi,a,b,cx = (iv(*x) for x in box)
        S = SqBox(phi,a,b)
        if pos(S.contain_gap()): return 'infeasible:contain'
        if neg(S.chart_gap()): return 'infeasible:chart'
        if S.pin_margin(*qE)<=0: return 'pin-E-outside'
        seps = S.separators(cx,CBOX)
        if neg(seps['OWN']): return 'not-own'
        if pos(S.pin_margin(1+cx,ZERO)-E): return 'claim'
        return None
    return ev


def run_L7(eps=None):
    if eps is None: eps = arb(1)/20
    c0hi = math.nextafter(float(C0.upper()),math.inf)
    root = [(-3.1416,3.1416),(0.5,1.2),(-1.2,1.2),(0.0,c0hi)]
    st,un,n = bnb(root,L7_eval_factory(eps),[1,1,1,1],name='L7 own moving pin')
    return not un,n


if __name__ == '__main__':
    import sys
    results = list(run_sep_windows().values())+[run_L6(),run_L7()]
    sys.exit(0 if all(ok for ok,n in results) else 1)
