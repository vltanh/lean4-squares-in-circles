"""Exact arithmetic printed in the transverse-segment central-core proof.

This is a transcription aid for a fixed hand calculation.  There is no
search, interval subdivision, floating-point operation, or geometry oracle.
"""

from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path


def sin_upper(x):
    return sum((-1)**j * x**(2*j+1) / factorial(2*j+1)
               for j in range(5))


def cos_lower(x):
    return sum((-1)**j * x**(2*j) / factorial(2*j)
               for j in range(6))


L, c, A = F(11, 12), F(7, 20), F(19, 20)
r2 = L*L+c*c
d0, dlo, dhi = F(1, 12), F(1379, 10000), F(69, 500)


def quartic(d):
    return (d**4+6*L*L*d*d-8*L*L*d+4*L*L
            -3*L**4-4*L*L*c*c)


checks = {}


def positive(name, value):
    assert value > 0, (name, value)
    checks[name] = str(value)


positive('tiny_core_radius_buffer', F(98, 25)-(F(9789, 2500)+F(4, 1000)+F(1, 10**6)))
positive('inverse_sqrt_two_exceeds_seven_tenths', F(1, 2)-F(7, 10)**2)
assert r2 == F(1733, 1800)
positive('segment_endpoint_inside_unit_disk', 1-r2)
positive('low_d_derivative_comparison', L**4-4*r2*c*c)
positive('quartic_strictly_decreases', -(4*c**3+12*L*L*c-8*L*L))
positive('quartic_at_lower_bracket', quartic(dlo))
positive('negative_quartic_at_upper_bracket', -quartic(dhi))
x = dlo/L
positive('twice_atan_lower', 2*(x-x**3/3)-F(149, 500))
positive('low_d_atan_lower', 2*(F(1, 11)-F(1, 11)**3/3)-F(9, 50))
positive('phi_lower', c/L-(c/L)**3/3-F(9, 25))

for name, angle, height, reserve in [
    ('mixed_endpoint', F(1437, 1000), F(431, 500), F(1, 5000)),
    ('symmetric_endpoint', F(899, 1000), F(1, 2), F(1, 3000)),
    ('high_mid_endpoint', F(123, 100), F(3, 4), F(3, 1000)),
]:
    # Alternation gives L sin(angle)-c cos(angle) <= this rational value.
    upper = L*sin_upper(angle)-c*cos_lower(angle)
    positive(name, height-upper)
    positive(name+'_displayed_reserve', height-upper-reserve)

k2 = r2-A*A
assert k2 == F(217, 3600)
assert A*A-L*L == F(14, 225)
assert A*A+d0*d0-L*L == F(249, 3600)
positive('k_exceeds_d0', k2-d0*d0)
positive('k_below_one_quarter', F(1, 16)-k2)
positive('sqrt249_below16', F(256)-249)
positive('high_mid_derivative', A+F(5, 16)*L-F(5, 4)*r2)
positive('high_mid_comparison_decreases', F(16, 25)-(r2-F(9, 16)))
t = F(9, 25)
positive('high_corner_at_nine_twenty_fifths',
         A*(1-t*t/2)+d0*(t-t**3/6)-L)
positive('high_zero_angle_exceeds_one_quarter', 1-F(1, 4)**2/2-L/A)
positive('high_mid_width', F(9, 25)+F(5, 24)+F(123, 100)-F(899, 500))

# Machin's identity and alternating arctangent bounds give pi > 157/50.
positive('pi_lower', 16*(F(1, 5)-F(1, 5)**3/3)-4*F(1, 239)-F(157, 50))
positive('small_d_width', F(157, 100)+F(9, 50)-F(347, 200))
positive('high_small_d_width', F(157, 100)+F(1, 4)-F(899, 500))
positive('symmetric_exceeds_global_width', 2*F(899, 1000)-F(347, 200))
positive('low_band_contradiction', F(347, 200)+12*F(19, 50)-F(44, 7))
positive('high_band_contradiction', F(899, 500)+12*F(3741, 10000)-F(44, 7))

result = {'status': 'PASS', 'fixed_rational_checks': len(checks),
          'positive_reserves': checks}
Path(__file__).with_name('hand_core_scalar_arithmetic.json').write_text(
    json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'fixed_rational_checks': len(checks)}))
