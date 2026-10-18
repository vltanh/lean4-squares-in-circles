"""Exact replay of the finite comparisons printed in the jump-two hand proof."""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json


def sin_partial(x, m):
    return sum(((-1)**j * x**(2*j+1) / factorial(2*j+1)
                for j in range(m+1)), F(0))


def cos_partial(x, m):
    return sum(((-1)**j * x**(2*j) / factorial(2*j)
                for j in range(m+1)), F(0))


Q, p, q, lam = F(9789, 2500), F(13, 200), F(203, 200), F(3, 4)
Rhi, chi, pi_lo = F(1979, 1000), F(9, 10), F(6283, 2000)
assert Rhi**2 > Q
assert (chi+F(1, 2))**2 > Q/2
assert p+lam-q == -F(1, 5)
assert q-lam > 0
assert p*p+q*q != lam*lam
assert F(13, 5) < 5*F(157, 50)/6
assert 1-F(7, 10)**2/2 > F(3, 4)

# The pi lower bound used here is independently reproduced from Machin's
# identity pi=16 atan(1/5)-4 atan(1/239), using an odd lower partial sum
# for the first arctangent and an even upper partial sum for the second.
def atan_partial(x, m):
    return sum(((-1)**j*x**(2*j+1)/F(2*j+1)
                for j in range(m+1)), F(0))


pi_machin_lower = 16*atan_partial(F(1, 5), 5)-4*atan_partial(F(1, 239), 2)
assert pi_machin_lower > pi_lo > F(157, 50)

# These signs are justified by the decreasing alternating tails.
x = F(7, 10)
assert sin_partial(x, 3) > F(644, 1000)
assert cos_partial(x, 3) > F(764, 1000)
assert cos_partial(x, 4) < F(765, 1000)
x = F(13, 5)
assert sin_partial(x, 5) > F(515, 1000)
assert cos_partial(x, 7) > -F(857, 1000)
assert cos_partial(x, 6) < -F(856, 1000)

uniform_N_squared_upper = p*p+q*q+lam*lam-2*lam*(-p+q/2)
assert uniform_N_squared_upper == F(2333, 2500) < 1
curvature_upper = -lam*F(3, 4)+F(2, 4)
assert curvature_upper == -F(1, 16)

rows = []
for name, angle_lo, sin_lo, cos_lo, cos_hi, Nhi, expected_square, expected_F in [
    ('pi_minus_seven_tenths', pi_lo-F(7, 10), F(644, 1000),
     -F(765, 1000), -F(764, 1000), F(832, 1000),
     F(276419, 400000), F(203993, 250000)),
    ('thirteen_fifths', F(13, 5), F(515, 1000),
     -F(857, 1000), -F(856, 1000), F(947, 1000),
     F(44821, 50000), F(815887, 1000000)),
]:
    N_squared_upper = p*p+q*q+lam*lam-2*lam*(p*cos_lo+q*sin_lo)
    assert N_squared_upper == expected_square < Nhi*Nhi
    F_lower = angle_lo+F(219, 200)-F(183, 100)*chi-lam*cos_hi-Rhi*Nhi
    assert F_lower == expected_F > F(163, 200)
    rows.append({'endpoint': name, 'N_squared_upper': str(N_squared_upper),
                 'N_upper': str(Nhi), 'F_lower': str(F_lower),
                 'strict_reserve': str(F_lower-F(163, 200))})
    print(name, 'N_squared_upper', N_squared_upper, 'F_lower', F_lower,
          'strict reserve', F_lower-F(163, 200))

large_angle_lower = F(13, 5)-2*(-F(9, 100)+(p+q)*chi)
assert large_angle_lower == F(209, 250) > F(163, 200)
out = {'status': 'PASS', 'scope': 'OO negative-positive source-negative-primary jump-two branch',
       'multiplier': str(lam), 'uniform_N_squared_upper': str(uniform_N_squared_upper),
       'strict_curvature_upper': str(curvature_upper), 'endpoint_rows': rows,
       'large_angle_lower': str(large_angle_lower),
       'subdivision_intervals': 0, 'numerical_roots': 0}
Path(__file__).with_name('jump_two_outer_opposite_hand_arithmetic.json').write_text(
    json.dumps(out, indent=2)+'\n')
print('PASS: exact rational endpoint rows and global concavity constants.')
