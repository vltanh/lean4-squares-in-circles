"""Exact rational checks for the three complete strict-M bottom-gap rows.

These verify algebraic radical enclosures and positive trigonometric
comparison reserves. The source supplies the angle ranges and the
complete physical/radius partition. No floating-point arithmetic is used.
"""
from fractions import Fraction as Q

QMAX = Q(1105, 256)

assert Q(3, 4)-Q(173, 200)**2 == Q(71, 40000)
assert Q(47, 30)**2+Q(273, 200)**2-QMAX == Q(1819, 1440000)
assert Q(53, 60)**2-(1-Q(47, 100)**2) == Q(53, 45000)
assert (Q(47, 100)*Q(83, 60)/(Q(53, 60)-Q(47, 100))
        -Q(47, 30)) == Q(47, 7440)
assert Q(11, 15)**2+Q(197, 100)**2-QMAX == Q(147271, 1440000)
assert Q(65, 64)-Q(201, 200)**2 == Q(7, 1250)

rows = [
    dict(c=Q(149, 200), angle=Q(299, 10000),
         cos2=Q(49, 81), sin2_factor=Q(8, 81), radical=Q(65),
         root_upper=Q(133412893, 200000000),
         root_lower=Q(2015564437, 250000000),
         radius_upper=Q(14589, 10000), epsilon_max=Q(1, 597),
         sine_reserve=Q(2021939071199, 10125000000000000)),
    dict(c=Q(3, 4), angle=Q(3, 50),
         cos2=Q(49, 81), sin2_factor=Q(8, 81), radical=Q(65),
         root_upper=Q(165359457, 250000000),
         root_lower=Q(2015564437, 250000000),
         radius_upper=Q(731, 500), epsilon_max=Q(1, 200),
         sine_reserve=Q(23117663, 3000000000)),
    dict(c=Q(19, 25), angle=Q(7, 50),
         cos2=Q(11543, 18225), sin2_factor=Q(244, 18225),
         radical=Q(3341), root_upper=Q(649923073, 1000000000),
         root_lower=Q(28900692033, 500000000),
         radius_upper=Q(147, 100), epsilon_max=None,
         sine_reserve=Q(542034971370377, 94921875000000000))
]

for index, row in enumerate(rows):
    c = row['c']
    assert Q(1, 2) < c < 1
    assert 4*c*c-1 > 0 and 4*c*c*c-3*c < 0
    upper, lower = row['root_upper'], row['root_lower']
    assert upper > 0 and upper*upper > 1-c*c
    assert lower > 0 and lower*lower < row['radical']
    emax = row['epsilon_max']
    radius_sq = QMAX if emax is None else (2+emax)**2+Q(1, 4)
    rmax = row['radius_upper']
    radius_reserve = rmax*rmax-radius_sq/2
    z = (rmax-1)*Q(8, 9)
    cosine_reserve = c*c-4*z*z*(1-z*z)
    assert radius_reserve > 0 and cosine_reserve > 0
    sine_upper = (row['cos2']*(4*c*c-1)*upper
                  + row['sin2_factor']*(4*c*c*c-3*c)*lower)
    angle = row['angle']
    gap = angle-angle**3/6-sine_upper
    assert gap == row['sine_reserve'] and gap > 0
    print('row', index, 'radius reserve', radius_reserve,
          'cosine reserve', cosine_reserve, 'sine reserve', gap)

phi_rows = [
    (Q(3, 200), Q(299, 10000), Q(391, 4000000)),
    (Q(1, 25), Q(3, 50), Q(1871, 93750)),
    (Q(7, 99), Q(7, 50), Q(171521, 145544850))
]
for base, angle, reserve in phi_rows:
    assert 2*(base-base**3/3)-angle == reserve and reserve > 0
assert Q(1, 597) > Q(1, 25)**2
assert Q(1, 200) > Q(7, 99)**2
assert Q(118, 135)**2-Q(3, 4) == Q(1021, 72900)
assert Q(131, 100)-Q(81, 64) == Q(71, 1600)
print('PASS: all three complete gap comparisons have strict rational reserves')
