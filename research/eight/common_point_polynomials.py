"""Exact short arithmetic for the hand common-point lemma.

This computes two polynomial expansions and four Bernstein coefficient rows.
It performs no subdivision search, floating-point geometry, or interval tree.
The complete inequalities and coefficient table are printed for hand checking.
"""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path


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


lam, cm, cp, sp, q = F(103,100), F(9305,10000), F(9306,10000), F(3663,10000), F(9789,2500)
z, c, ss = [F(1),F(0),F(1)], [F(1),F(0),-F(1)], [F(0),F(2)]
h = add(sc(F(1,2),z), sc(lam*cm,c), sc(-lam*sp,ss))
p = add(mul(mul(h,h),z), mul(mul(h,c),add(c,ss)), sc(F(1,2)-q,mul(mul(c,c),z)))
v = add([F(1,2),0,0,0,-F(1,2)], sc(F(10,9),mul([0,F(1)],z)), sc(-lam*cp,mul(ss,c)), sc(-lam*sp,mul(c,c)))

expected_p = [169789312225,-38723747740,-109557354141,-3833660000000,6742414645859,854071747740,-3663870687775]
expected_v = [1104399,-7253324,6791202,27253324,-7895601]
assert p == [F(x,10**12) for x in expected_p]
assert v == [F(x,9*10**6) for x in expected_v]

# Alternating Taylor series on 3/8 give the three rational trig bounds.
t = F(3,8)
cos_low = 1-t*t/2+t**4/24-t**6/720
cos_high = cos_low+t**8/40320
sin_high = t-t**3/6+t**5/120
assert cos_low > cm and cos_high < cp and sin_high < sp

rows = []
for name, poly, intervals in [
    ('P', p, [(F(0),F(1,2)),(F(1,2),F(1))]),
    ('V', v, [(F(0),F(3,14)),(F(3,14),F(3,7))]),
]:
    for lo, hi in intervals:
        b = bernstein(poly, lo, hi)
        assert min(b) > 0
        lower = [(100000*x.numerator)//x.denominator for x in b]
        assert min(lower) > 0
        row = {'polynomial':name, 'interval':[str(lo),str(hi)],
               'degree':len(poly)-1,
               'bernstein_lower_numerators_denominator_100000':lower,
               'exact_coefficients':[str(x) for x in b]}
        rows.append(row)
        print(name, str(lo), str(hi), lower, flush=True)

result = {'status':'PASS', 'p_numerators_denominator_10pow12':expected_p,
          'v_numerators_denominator_9000000':expected_v, 'rows':rows}
path = Path(__file__).with_name('common_point_polynomial_table.json')
with path.open('w') as out:
    json.dump(result, out, indent=2)
    out.write('\n')
    out.flush()
