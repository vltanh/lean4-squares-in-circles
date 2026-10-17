"""Exact rational checks for the quarter-one opposite-sign hand lemma.

Only the proposed scalar bounds printed in the accompanying note are
checked. There is no search, fitted optimizer, or subdivision certificate.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json

Q, p, q, lam = F(9789, 2500), F(13, 200), F(203, 200), F(39, 40)
R_hi, pi_lo = F(1979, 1000), F(314159, 100000)
assert R_hi**2 > Q
assert F('1.915')**2 > Q - F(1, 4)
assert F('1.399')**2 < Q / 2 < F('1.4')**2
assert F('1.399') > F(4, 3)

N0a, N0b = F('1.47121'), F('.06671')
assert N0a**2 > (1+p)**2 + q*q
assert N0b**2 > p*p + (q-1)**2
F0 = pi_lo/2 + F('2.26') - R_hi*(N0a+N0b)
assert F0 > F(787, 1000)

# The negative-angle obstruction and the local quarter-turn comparison.
z = F(2, 5)
barrier = F('1.399')*(z-z**3/6) + (1-z*z/2)/2
assert barrier > F('.915')
assert F('1.399')*(1-F(7,10)**2/2)-F(7,20) > 0
assert F(4,3)*(1-F(1,5)-F(2,75)) == F(232,225) > 1
assert 1-F('.915')-F(7,10)*F(1,10) == F(3,200) > 0

N1_hi = F('1.45322')
assert N1_hi**2 > (p+lam)**2 + q*q

def sine_lower(x):
    return sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(4))

def sine_upper(x):
    return sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(3))

def cosine_lower(x):
    return sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(4))

rows = []
for x, sl, sh, cl, Nh in [
    (F(1,10), F(9983,100000), F(999,10000), F(199,200), F(337,2000)),
    (F(7,10), F(3221,5000), F(16106,25000), F(19121,25000), F(1859,2500)),
]:
    assert sl < sine_lower(x)
    assert sh > sine_upper(x)
    assert cl <= cosine_lower(x)
    X2_hi = p*p+q*q+lam*lam+2*lam*(p*sh-q*cl)
    assert X2_hi < Nh*Nh
    assert (q-lam*cl)/sl < F(11,20)
    value = pi_lo/2+x+F(63,50)+lam+lam*sl-R_hi*(N1_hi+Nh)
    assert value > F(7863,10000) > F(157,200)
    rows.append({'x':str(x), 'sin_lower':str(sl), 'sin_upper':str(sh),
                 'cos_lower':str(cl), 'N2_upper':str(Nh),
                 'F_lower':str(value)})

assert F(99,1000) < F(9983,100000)
assert lam + F(65,99) < F(33,20)
assert F(11,20)**2 + F(33,20)**2 < F(7,4)**2
assert lam > F(7,8)

result = {'status':'PASS','quarter_value_lower':str(F0),
          'negative_angle_barrier':str(barrier),'endpoint_rows':rows}
Path(__file__).with_name('quarter_one_outer_opposite_hand_arithmetic.json').write_text(
    json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
