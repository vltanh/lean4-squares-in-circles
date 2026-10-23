"""Exact rational verification; no numerical optimizer or external packages."""
import json
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

if not __debug__:
    raise SystemExit('Run without -O: this checker uses assertions.')

path = Path(__file__).with_name('AXIS_ALIGNED_COUNTEREXAMPLE.json')
data = json.loads(path.read_text())
d = data['denominator']
centres = [tuple(Fraction(v, d) for v in row) for row in data['centres_numerators']]
q = Fraction(data['q_upper'])
assert len(centres) == 11
assert q == Fraction(491, 100) and q < 5
corners = [(x + Fraction(a, 2))**2 + (y + Fraction(b, 2))**2
           for x, y in centres for a, b in product((-1, 1), repeat=2)]
assert len(corners) == 44 and max(corners) < q
separations = [max(abs(centres[j][k] - centres[i][k]) for k in (0, 1))
               for i, j in combinations(range(11), 2)]
assert len(separations) == 55 and min(separations) >= 1
assert max(corners) == Fraction(data['maximum_corner_norm_squared'])
assert min(separations) - 1 == Fraction(data['minimum_separator_slack'])
print('PASS: all 44 corners and 55 separations checked with rational arithmetic.')
print('q =', q, '< 5; maximum corner squared norm =', max(corners))
print('Minimum separation slack =', min(separations) - 1)
