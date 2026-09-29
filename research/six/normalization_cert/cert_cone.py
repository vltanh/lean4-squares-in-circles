"""Supplied Lemma A predicates: prove the strong central box before sectors.

The geometric target is c0 < cx < 1/2, 0 <= cy <= cx. Case A1 has
cy<=c0 and forbids (-0.99,1.22); case A2 has cy>=c0 and forbids
(-0.54,1.56). Both arc widths exceed 2*pi/3, contradicting N7.

IMPORTANT: the computational boxes include cx=c0 for enclosure purposes,
but the predicate drops CE and OWN using hand lemmas valid for cx>c0 only.
The certificate does NOT assert the forbidden arc on the face cx=c0.
"""
from ia import *
from bnb import bnb

TWO_PI = 2*PI
ROOT = [(-3.1416-0.001,3.1416+0.001),(0.5,1.2),(-1.2,1.2)]


def cone_eval_factory(cxbox,cybox,am,ap):
    AM,AP = arb(am),arb(ap)
    def ev(box):
        phi,a,b = (iv(*x) for x in box)
        S = SqBox(phi,a,b)
        if pos(S.contain_gap()): return 'infeasible:contain'
        if neg(S.chart_gap()): return 'infeasible:chart'
        if neg(a-HALF): return 'infeasible:interior'
        seps = S.separators(cxbox,cybox)
        if phi>=-PI/4 and phi<=PI/4:
            # Conditional hand inputs: cap depth (e) and OWN-E exclusion (f).
            # cx>c0; cy<=cx+1/10. A2 staircase excess is <0.049<1/10.
            seps = {k:v for k,v in seps.items() if k not in ('OWN','CE')}
        if all(neg(m) for m in seps.values()): return 'infeasible:disjoint'
        lab = label(a,S.u)
        if b>0: m = phi+lab
        elif b<0: m = phi-lab
        else: m = phi+iv(-1,1)*lab
        for k in (-1,0,1):
            mk = m+k*TWO_PI
            if not (mk<=-AM or mk>=AP): return None
        return 'marker-outside-arc'
    return ev


def run_A1():
    cx,cy = C0.union(arb(1)/2),iv(0,0).union(C0)
    st,un,n = bnb(ROOT,cone_eval_factory(cx,cy,0.99,1.22),[1,1,1],name='Lemma A, A1')
    return not un,n


def run_A2(ngrid=8,am=0.54,ap=1.56):
    if ngrid<4:
        raise ValueError('staircase boxes must have diagonal excess below 1/10')
    low = math.nextafter(float(C0.lower()),-math.inf)
    edges = [low+(0.5-low)*i/ngrid for i in range(ngrid+1)]
    edges[-1] = 0.5
    if max(edges[i+1]-edges[i] for i in range(ngrid))>=0.1:
        raise ValueError('hand OWN-E extension does not cover this staircase')
    ok,total = True,0
    for i in range(ngrid):
        for j in range(i+1):
            ev = cone_eval_factory(iv(edges[i],edges[i+1]),iv(edges[j],edges[j+1]),am,ap)
            st,un,n = bnb(ROOT,ev,[1,1,1],verbose=False)
            ok &= not un
            total += n
            print(f'A2[{i},{j}] '+('CERTIFIED' if not un else 'FAILED')+f' ({n} boxes)',flush=True)
    return ok,total


if __name__ == '__main__':
    import sys
    ok1,n1 = run_A1()
    ok2,n2 = run_A2()
    print('A1',ok1,n1,'A2',ok2,n2)
    sys.exit(0 if ok1 and ok2 else 1)
