"""Short fixed rational tables for the central-depth hand argument.

No adaptive subdivision or floating-point geometry occurs here. The script
expands the displayed polynomials and checks the fixed rows printed in the
companion note. All integer lower bounds use denominator 10^6.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def add(*args):
    return [sum(p[k] if k < len(p) else 0 for p in args)
            for k in range(max(map(len, args)))]


def mul(a, b):
    return [sum(a[j] * b[k-j]
                for j in range(max(0, k-len(b)+1), min(k+1, len(a))))
            for k in range(len(a)+len(b)-1)]


def sc(k, a):
    return [k*x for x in a]


def bernstein(p, lo, hi):
    n = len(p)-1
    power = [sum(p[j] * comb(j, k) * lo**(j-k) * (hi-lo)**k
                 for j in range(k, n+1)) for k in range(n+1)]
    return [sum(power[j] * F(comb(k, j), comb(n, j))
                for j in range(k+1)) for k in range(n+1)]


Q = F(9789, 2500)
z, c, s = [F(1), F(0), F(1)], [F(1), F(0), -F(1)], [F(0), F(2)]
states = [
    dict(name='segment', amin=F(1,2), Cminus=F(11,12),
         Cplus=F(11,12), D=F(7,20),
         p_intervals=[(F(0),F(1,4)),(F(1,4),F(1,2)),(F(1,2),F(1))],
         v_intervals=[(F(0),F(3,14)),(F(3,14),F(3,7))]),
    dict(name='A', amin=F(5007,10000), lam=F(10007,10000), angle=F(3741,10000),
         cm=F(9308368,10**7), cp=F(9308369,10**7), sp=F(365435,10**6),
         p_intervals=[(F(0),F(1,4)),(F(1,4),F(3,8)),(F(3,8),F(7,16)),
                      (F(7,16),F(1,2)),(F(1,2),F(1))],
         v_intervals=[(F(0),F(3,14)),(F(3,14),F(9,28)),(F(9,28),F(3,7))]),
    dict(name='B', amin=F(107,200), lam=F(41,40), angle=F(19,50),
         cm=F(9286,10000), cp=F(9287,10000), sp=F(371,1000),
         p_intervals=[(F(0),F(1,2)),(F(1,2),F(1))],
         v_intervals=[(F(0),F(3,14)),(F(3,14),F(15,56)),
                      (F(15,56),F(9,28)),(F(9,28),F(3,7))]),
    dict(name='strong_exterior', amin=F(5,9), lam=F(103,100), angle=F(19,50),
         cm=F(9286,10000), cp=F(9287,10000), sp=F(371,1000),
         p_intervals=[(F(0),F(1,2)),(F(1,2),F(1))],
         v_intervals=[(F(0),F(3,14)),(F(3,14),F(3,7))]),
]

results = []
for state in states:
    if 'angle' in state:
        t = state['angle']
        cos_low = 1-t*t/2+t**4/24-t**6/720
        cos_high = cos_low+t**8/40320
        sin_high = t-t**3/6+t**5/120-t**7/5040+t**9/362880
        assert cos_low > state['cm']
        assert cos_high < state['cp']
        assert sin_high < state['sp']
        state['Cminus'] = state['lam'] * state['cm']
        state['Cplus'] = state['lam'] * state['cp']
        state['D'] = state['lam'] * state['sp']
    assert F(1,2) - state['D'] > 0
    H = add(sc(F(1,2), z), sc(state['Cminus'],c), sc(-state['D'],s))
    P = add(mul(mul(H,H),z), mul(mul(H,c),add(c,s)),
            sc(F(1,2)-Q, mul(mul(c,c),z)))
    V = add(sc(F(1,2),mul(c,z)), sc(state['amin'],mul(s,z)),
            sc(-state['Cplus'],mul(s,c)), sc(-state['D'],mul(c,c)))
    result = {'name':state['name'],
              'parameters':{k:str(v) for k,v in state.items()
                            if k not in ['name','p_intervals','v_intervals']},
              'P_coefficients':[str(x) for x in P],
              'V_coefficients':[str(x) for x in V], 'rows':[]}
    for name, poly, intervals in [('P', P, state['p_intervals']),
                                  ('V', V, state['v_intervals'])]:
        for lo, hi in intervals:
            coeff = bernstein(poly, lo, hi)
            lower = [int((10**6*x.numerator)//x.denominator) for x in coeff]
            assert min(lower) > 0
            row = {'polynomial':name, 'interval':[str(lo),str(hi)],
                   'lower_numerators_denominator_1000000':lower,
                   'exact_coefficients':[str(x) for x in coeff]}
            result['rows'].append(row)
            print(state['name'], name, str(lo), str(hi), lower, flush=True)
    results.append(result)

assert F(11,12)**2 + F(7,20)**2 < 1
path = Path(__file__).with_name('central_band_polynomial_tables.json')
with path.open('w') as out:
    json.dump({'status':'PASS', 'Q':str(Q), 'states':results}, out, indent=2)
    out.write('\n')
    out.flush()
