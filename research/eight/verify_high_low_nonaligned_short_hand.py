"""Replay the three printed rational rows of the H/L hand proof.

This is an optional arithmetic check, not a numerical optimization or
subdivision certificate. All polynomials and comparison constants are
explicit in HIGH_LOW_NONALIGNED_SHORT_HAND_PROOF.md.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json


def add(*polys):
    out = [sum(p[j] if j < len(p) else 0 for p in polys)
           for j in range(max(map(len, polys)))]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def scale(a, p):
    return [a * v for v in p]


def mul(p, q):
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def square(p):
    return mul(p, p)


def compose(coefficients, p):
    out = [F(0)]
    for a in reversed(coefficients):
        out = add(mul(out, p), [a])
    return out


def bernstein(p):
    n = len(p) - 1
    return [sum(p[j] * F(comb(i, j), comb(n, j))
                for j in range(i + 1)) for i in range(n + 1)]


mu, q, k, v, beta = map(F, ['.403875', '1.089065', '.569472', '.390886', '.18'])
Q, e = F(9789, 2500), F(1, 10**11)
R_hi, c_lo, a0_lo = map(F, ['1.978788', '.899214', '1.414575'])
assert R_hi**2 > Q
assert (c_lo + F(1, 2))**2 < Q / 2
assert (a0_lo + F(1, 2))**2 < Q - F(1, 4)
assert F(3, 10)**10 / factorial(10) < e
assert F(3, 10)**11 / factorial(11) < e

# The single substitution x = .08 + .22 y has already been applied.
x = [F(2, 25), F(11, 50)]
w = add(x, [-F(19, 100)])
l = add([F('.990906')], scale(-F(7, 25), x))
S = compose([F(0), F(1), F(0), -F(1, 6), F(0), F(1, 120),
             F(0), -F(1, 5040), F(0), F(1, 362880)], x)
C = compose([F(1), F(0), -F(1, 2), F(0), F(1, 24),
             F(0), -F(1, 720), F(0), F(1, 40320)], x)
P1_coeff = list(map(F, ['.7895001401', '-.1939323304', '.0258329638',
                       '.0063465589', '.0011353387']))
P2_coeff = list(map(F, ['.6048369308', '.9594403346', '-.2050884018',
                       '-.0610720222', '.0449392223']))
P1, P2 = compose(P1_coeff, w), compose(P2_coeff, w)
U1, U2 = add(P1, [F(1, 10**7)]), add(P2, [F(1, 10**6)])
for coeff, delta, lower in [(P1_coeff, F(1, 10**7), F('.76')),
                             (P2_coeff, F(1, 10**6), F('.49'))]:
    triangle_lower = coeff[0] + delta - sum(abs(coeff[j]) * F(11, 100)**j
                                           for j in range(1, 5))
    assert triangle_lower > lower
X1 = add([k*k], square(add(l, [-v])))
X2 = add([mu*mu + q*q], square(l),
         scale(2, mul(l, add(scale(mu, S), scale(-q, C)))))
V = add(x, scale(-beta / 2, C),
        mul(add(l, [-beta / 2]), add(S, [-e])), l,
        [F('3.14159') / 4 + (k-v)*c_lo + mu*a0_lo
         + (k-v+mu+q+beta) / 2 - F('.8833')],
        scale(-R_hi, add(U1, U2)))

rows = []
expected = {
    'U1_squared_minus_X1': [16, 16, 16, 15, 15, 15, 15, 15, 15],
    'U2_squared_minus_X2_minus_3e': [85, 135, 111, 90, 96, 122, 147, 150, 126, 104, 157],
    'V': [4188, 2453, 1181, 382, 63, 225, 863, 1969, 3531, 5530, 7944],
}
for name, poly, denominator in [
    ('U1_squared_minus_X1', add(square(U1), scale(-1, X1)), 10**8),
    ('U2_squared_minus_X2_minus_3e', add(square(U2), scale(-1, X2), [-3*e]), 10**8),
    ('V', V, 10**7),
]:
    coefficients = bernstein(poly)
    numerators = [int((b * denominator).numerator // (b * denominator).denominator)
                  for b in coefficients]
    assert min(numerators) > 0
    assert numerators == expected[name]
    rows.append({'name': name, 'degree': len(poly) - 1,
                 'lower_denominator': denominator, 'lower_numerators': numerators,
                 'exact_coefficients': list(map(str, coefficients))})
    print(name, 'degree', len(poly) - 1, 'denominator', denominator,
          'positive lower numerators', numerators)

assert sum(len(r['lower_numerators']) for r in rows) == 31
Path(__file__).with_name('high_low_nonaligned_short_hand_arithmetic.json').write_text(
    json.dumps({'status': 'PASS', 'fixed_intervals': 1, 'positive_coefficients': 31,
                'rows': rows}, indent=2) + '\n')
print('PASS: three polynomial rows, 31 positive coefficients, exact rational arithmetic.')
