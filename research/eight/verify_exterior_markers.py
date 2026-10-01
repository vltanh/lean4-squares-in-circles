#!/usr/bin/env python3
"""Exact rational interval certificate for an exterior-marker lemma.

Run with Python 3 (standard library only). Float calculations are branching
heuristics only. Every terminal box is verified by Fraction arithmetic and
Taylor bounds. See EXTERIOR_MARKER_CERTIFICATE.md for the soundness argument.
This is an intermediate certificate, NOT a proof of full n=8 optimality.
"""
from fractions import Fraction as F
from math import sin, cos
import argparse
import time

Q = F(98, 25)
GAMMA = F(4, 5)
HALF = F(1, 2)
WEIGHTS = (1.7, 2.5, 1.7, 2.5, 1.8)


def label_bounds(al, ah, ul, uh, exact):
    if exact:
        return (min(F(11,10)*ul, F(3,5)+F(4,7)*ul-F(3,8)*ah, F(3,4)),
                min(F(11,10)*uh, F(3,5)+F(4,7)*uh-F(3,8)*al, F(3,4)))
    return (min(1.1*ul, .6+4*ul/7-3*ah/8, .75),
            min(1.1*uh, .6+4*uh/7-3*al/8, .75))


def point_trig(x):
    """Return rational lower/upper bounds for sin(x) and cos(x)."""
    if abs(x) > F(23,10):
        raise AssertionError('Trigonometric domain exceeded')
    xx = x*x
    term = F(1)
    cv = F(1)
    for k in range(1,9):
        term = -term*xx/F((2*k-1)*(2*k))
        cv += term
    cl = cv-term*xx/F(17*18)
    term = x
    sv = x
    for k in range(1,9):
        term = -term*xx/F((2*k)*(2*k+1))
        sv += term
    snext = sv-term*xx/F(18*19)
    sl, su = (snext, sv) if x >= 0 else (sv, snext)
    return sl, su, cl, cv


def trig_bounds(lo, hi, exact):
    if exact:
        sl, su, cl, cu = point_trig(lo)
        tl, tu, dl, du = point_trig(hi)
        sl, su = min(sl,tl), max(su,tu)
        cl, cu = min(cl,dl), max(cu,du)
        # pi/2 lies in (3/2,8/5); possible extrema are included conservatively.
        if lo <= F(-3,2) and hi >= F(-8,5):
            sl = F(-1)
        if lo <= F(8,5) and hi >= F(3,2):
            su = F(1)
        if lo <= 0 <= hi:
            cu = F(1)
        return sl, su, cl, cu
    sl, su = min(sin(lo),sin(hi)), max(sin(lo),sin(hi))
    cl, cu = min(cos(lo),cos(hi)), max(cos(lo),cos(hi))
    if lo <= -1.5 and hi >= -1.6:
        sl = -1.
    if lo <= 1.6 and hi >= 1.5:
        su = 1.
    if lo <= 0 <= hi:
        cu = 1.
    return sl, su, cl, cu


def min_term(al, ah, xl, xh, exact):
    """Minimize alpha*x+|x|/2 on a rectangle by its corners and x=0."""
    h = HALF if exact else .5
    out = min(al*xl+h*abs(xl), al*xh+h*abs(xh),
              ah*xl+h*abs(xl), ah*xh+h*abs(xh))
    return min(out,0) if xl <= 0 <= xh else out


def margins(lo, hi, sg, tg, exact):
    a, u, A, v, g = lo
    ah, uh, Ah, vh, gh = hi
    l0, l1 = label_bounds(a,ah,u,uh,exact)
    r0, r1 = label_bounds(A,Ah,v,vh,exact)
    d0, d1 = (g+l0, gh+l1) if sg > 0 else (g-l1, gh-l0)
    d0, d1 = (d0-r1, d1-r0) if tg > 0 else (d0+r0, d1+r1)
    sn, sx, cn, cx = trig_bounds(d0,d1,exact)
    tv0, tv1 = (v,vh) if tg > 0 else (-vh,-v)
    su0, su1 = (u,uh) if sg > 0 else (-uh,-u)
    h = HALF if exact else .5
    return (
        a+h+min_term(-Ah,-A,cn,cx,exact)+min_term(tv0,tv1,sn,sx,exact),
        h+su0+min_term(-Ah,-A,sn,sx,exact)+min_term(-tv1,-tv0,cn,cx,exact),
        h-ah+min_term(A,Ah,cn,cx,exact)+min_term(-tv1,-tv0,sn,sx,exact),
        h-su1+min_term(A,Ah,sn,sx,exact)+min_term(tv0,tv1,cn,cx,exact))


def impossible(lo, hi):
    a, u, A, v, g = lo
    return (u > hi[0] or v > hi[2]
            or (a+HALF)**2+(u+HALF)**2 > Q
            or (A+HALF)**2+(v+HALF)**2 > Q)


def verify_case(sg, tg, max_nodes):
    stack = [((HALF,F(0),HALF,F(0),F(0)),
              (F(3,2),F(1),F(3,2),F(1),GAMMA), 0)]
    seen = empty = positive = max_depth = 0
    minimum = None
    start = time.monotonic()
    while stack:
        lo, hi, depth = stack.pop()
        seen += 1
        max_depth = max(max_depth,depth)
        if seen > max_nodes:
            raise RuntimeError('Node budget exhausted: NO certificate')
        if impossible(lo,hi):
            empty += 1
            continue
        fl, fh = tuple(map(float,lo)), tuple(map(float,hi))
        # Even an incorrect float heuristic cannot create an accepted leaf.
        if min(margins(fl,fh,sg,tg,False)) > 0:
            mm = min(margins(lo,hi,sg,tg,True))
            if mm > 0:
                positive += 1
                minimum = mm if minimum is None else min(minimum,mm)
                continue
        if depth > 150:
            raise RuntimeError('Depth budget exhausted: NO certificate')
        j = max(range(5),key=lambda j:float(hi[j]-lo[j])*WEIGHTS[j])
        mid = (lo[j]+hi[j])/2
        h = list(hi)
        h[j] = mid
        l = list(lo)
        l[j] = mid
        stack.append((lo,tuple(h),depth+1))
        stack.append((tuple(l),hi,depth+1))
    assert seen == 2*(empty+positive)-1
    result = {'signs':[sg,tg], 'nodes':seen, 'empty_leaves':empty,
              'positive_leaves':positive, 'max_depth':max_depth,
              'minimum_leaf_margin':str(minimum)}
    print(result,flush=True)
    print('elapsed_seconds',round(time.monotonic()-start,3),flush=True)
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--signs',nargs=2,type=int,choices=(-1,1))
    ap.add_argument('--max-nodes',type=int,default=2000000)
    args = ap.parse_args()
    cases = ([tuple(args.signs)] if args.signs
             else [(1,1),(1,-1),(-1,1),(-1,-1)])
    for sg,tg in cases:
        verify_case(sg,tg,args.max_nodes)
    if args.signs is None:
        print('All four sign cases verified by exact rational terminal checks.')
        print('At q<=98/25, exterior states with marker gap <=4/5 cannot be disjoint.')
        print('This yields at most seven exterior squares, NOT n=8 optimality.')
