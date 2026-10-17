"""Exact rational arithmetic for the two-row hand argument; no search."""
from fractions import Fraction as F
from math import factorial

Q = F(9789, 2500)
p, q, lam = F(13, 200), F(203, 200), F(1939, 2000)
gamma = F(391, 400)


def sin_poly(x, last):
    return sum((-1)**j * x**(2*j+1) / factorial(2*j+1)
               for j in range(last+1))


def cos_poly(x, last):
    return sum((-1)**j * x**(2*j) / factorial(2*j)
               for j in range(last+1))


assert lam == q - F(7, 10)*p
assert F(1979, 1000)**2 > Q
assert F(7, 5)**2 > Q/2
assert F(48, 25)**2 > Q-F(1, 4)
assert F(2, 5)+F(23, 250)-F(199, 400) == -F(11, 2000)
assert F(1, 2)+F(1, 2)*F(19121, 25000)-F(23, 25)*F(16106, 25000) == F(362149, 1250000)
assert F(362149, 1250000) > F(7, 25)
P = lambda b: F(17, 4)-F(9, 5)*b+F(149, 100)*b*b
assert P(F(7, 25)) == F(603565, 156250) < Q
assert P(F(9, 10)) == F(38369, 10000) < Q
assert F(1939, 2000)+F(65, 99) < F(33, 20)
assert F(1210, 400) < F(49, 16)
assert lam > F(7, 8)

rows = [
    (F(1, 10), F(9983, 100000), F(999, 10000), F(199, 200),
     F(17, 100), F(196521037, 200000000)),
    (F(7, 10), F(3221, 5000), F(16106, 25000), F(19121, 25000),
     F(371, 500), F(9783839, 10000000)),
]
for x, sl, su, cl, n, f in rows:
    assert sin_poly(x, 3) > sl
    assert sin_poly(x, 2) < su
    assert cos_poly(x, 3) >= cl
    assert q-lam*cl < F(11, 20)*sl
    n2_upper = p*p+q*q+lam*lam+2*lam*(p*su-q*cl)
    assert n*n > n2_upper
    lower = x+F(4489, 4000)+lam*sl-F(1979, 1000)*n
    assert lower == f > gamma
    print(dict(x=str(x), norm_square_slack=str(n*n-n2_upper),
               cost_lower=str(lower), cost_reserve=str(lower-gamma)))
print("PASS: all fixed rational comparisons in the two-row hand proof")
