"""Independent exact audit of the fixed central-band polynomial tables.

Polynomial identities are checked by degree and exact evaluations at n+1
distinct points.  Bernstein identities are checked by expanding their basis
directly; the original table generator's conversion formula is not reused.
"""

from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
NOTE = BASE/'CENTRAL_BAND_COMMON_POINT_LEMMAS.md'
WORD_NOTE = BASE/'SEVEN_QUARTER_WORDS.md'
DATA = BASE/'central_band_polynomial_tables.json'
Q = F(9789, 2500)
data = json.loads(DATA.read_text())
assert data['Q'] == str(Q)

expected = {
    'segment': (F(1,2), F(11,12), F(11,12), F(7,20)),
    'A': (F(5007,10000), F(10007,10000)*F(9308368,10**7),
          F(10007,10000)*F(9308369,10**7),
          F(10007,10000)*F(365435,10**6)),
    'B': (F(107,200), F(41,40)*F(9286,10000),
          F(41,40)*F(9287,10000), F(41,40)*F(371,1000)),
    'strong_exterior': (F(5,9), F(103,100)*F(9286,10000),
                       F(103,100)*F(9287,10000),
                       F(103,100)*F(371,1000)),
}


def evaluate(coefficients, x):
    out = F(0)
    for coefficient in reversed(coefficients):
        out = out*x+coefficient
    return out


printed = []
pattern = r'^\| (Segment|A|B) \| \(([PV])\) \| \(\[([^\]]+)\]\) \| ([\d, ]+) \|$'
def normalize_math_delimiters(text):
    return text.replace('\\(', '(').replace('\\)', ')')


for case, polynomial, interval, numbers in re.findall(
        pattern, normalize_math_delimiters(NOTE.read_text()), re.M):
    printed.append((case.lower() if case == 'Segment' else case,
                    polynomial, [F(x.strip()) for x in interval.split(',')],
                    [int(x.strip()) for x in numbers.split(',')]))
assert len(printed) == 19
word_pattern = r'^\| \(([PV])\) \| \(\[([^\]]+)\]\) \| ([\d, ]+) \|$'
word_rows = re.findall(word_pattern,
                       normalize_math_delimiters(WORD_NOTE.read_text()), re.M)
assert len(word_rows) == 4
for polynomial, interval, numbers in word_rows:
    printed.append(('strong_exterior', polynomial,
                    [F(x.strip()) for x in interval.split(',')],
                    [int(x.strip()) for x in numbers.split(',')]))

rows = []
for state in data['states']:
    name = state['name']
    if name not in expected:
        continue
    p = state['parameters']
    amin, cm, cp, sp = expected[name]
    assert tuple(F(p[k]) for k in ['amin','Cminus','Cplus','D']) == expected[name]
    assert sp < F(1,2)
    polynomials = {k: [F(x) for x in state[k+'_coefficients']] for k in ['P','V']}
    assert len(polynomials['P']) == 7 and len(polynomials['V']) == 5
    for k, poly in polynomials.items():
        for u in map(F, range(len(poly))):
            z, c, s = 1+u*u, 1-u*u, 2*u
            H = z/2+cm*c-sp*s
            structural = (H*H*z+H*c*(c+s)+(F(1,2)-Q)*c*c*z
                          if k == 'P' else z*c/2+amin*s*z-cp*s*c-sp*c*c)
            assert evaluate(poly,u) == structural
    for polynomial in ['P','V']:
        selected = [row for row in state['rows'] if row['polynomial'] == polynomial]
        assert F(selected[0]['interval'][0]) == 0
        assert F(selected[-1]['interval'][1]) == (1 if polynomial == 'P' else F(3,7))
        for a,b in zip(selected, selected[1:]):
            assert F(a['interval'][1]) == F(b['interval'][0])
    for row in state['rows']:
        polynomial = row['polynomial']
        lo, hi = map(F,row['interval'])
        poly = polynomials[polynomial]
        n = len(poly)-1
        bs = [F(x) for x in row['exact_coefficients']]
        lows = row['lower_numerators_denominator_1000000']
        assert len(bs) == len(lows) == n+1 and lo < hi
        assert all(b >= F(low,10**6) > 0 for b,low in zip(bs,lows))
        for j in range(n+1):
            v = F(j,n)
            basis_value = sum(bs[k]*comb(n,k)*v**k*(1-v)**(n-k)
                              for k in range(n+1))
            assert basis_value == evaluate(poly,lo+(hi-lo)*v)
        rows.append((name, polynomial, [lo,hi], lows))
assert rows == printed

for h,cm,cp,sp in [
    (F(3741,10000),F(9308368,10**7),F(9308369,10**7),F(365435,10**6)),
    (F(19,50),F(9286,10000),F(9287,10000),F(371,1000)),
]:
    cl = sum((-1)**j*h**(2*j)/factorial(2*j) for j in range(4))
    cu = cl+h**8/factorial(8)
    su = sum((-1)**j*h**(2*j+1)/factorial(2*j+1) for j in range(5))
    assert cm < cl and cu < cp and su < sp

report = {'status':'PASS', 'fixed_rows_independently_checked':len(rows),
          'central_band_rows':19, 'strong_exterior_rows':4,
          'positive_Bernstein_coefficients':sum(len(row[3]) for row in rows),
          'note_sha256':hashlib.sha256(NOTE.read_bytes()).hexdigest(),
          'word_note_sha256':hashlib.sha256(WORD_NOTE.read_bytes()).hexdigest(),
          'data_sha256':hashlib.sha256(DATA.read_bytes()).hexdigest(),
          'method':'Exact polynomial identity evaluation; direct Bernstein basis evaluation; note/table transcription match.'}
Path(__file__).with_name('central_band_tables_independent_audit.json').write_text(
    json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
