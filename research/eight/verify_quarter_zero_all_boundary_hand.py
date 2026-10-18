"""Check the displayed rational arithmetic in the full zero-quarter hand row."""
from fractions import Fraction as F
from math import factorial

Q = F(9789, 2500)
p, q, h = F(13, 200), F(203, 200), F(291, 250)
gamma = F(391, 400)
a_lo, a_hi, d_lo, d_hi = F(141, 100), F(283, 200), F(89, 100), F(9, 10)
checks = []


def record(name, value, target, relation=">"):
    assert value > target if relation == ">" else value < target, (name, value, target)
    checks.append((name, str(value), relation, str(target)))


def sin_poly(x, last):
    return sum((-1)**j*x**(2*j+1)/factorial(2*j+1) for j in range(last+1))


def cos_poly(x, last):
    return sum((-1)**j*x**(2*j)/factorial(2*j) for j in range(last+1))


assert (a_lo+F(1, 2))**2 < Q-F(1, 4) < (a_hi+F(1, 2))**2
assert (d_lo+F(1, 2))**2 < Q/2 < (d_hi+F(1, 2))**2
assert F(100, 383) > F(3, 13)
assert -F(9, 100)+(p+F(3, 200))*d_lo > -F(19, 1000)
assert -F(9, 100)+p*a_hi < F(1, 500)
assert -F(9, 100)+p*a_lo > 0
assert F(57, 40)**2 > 2
assert F(2, 5)*F(57, 40)-F(1, 2) == F(7, 100)
assert F(1979, 1000)**2 > Q

trig = {
    F(1, 10): (F(9983, 100000), F(999, 10000), F(199, 200)),
    F(1, 4): (None, F(1, 4), F(31, 32)),
    F(2, 5): (F(389, 1000), F(2, 5), F(23, 25)),
    F(1, 2): (F(47, 100), F(1, 2), F(7, 8)),
    F(7, 10): (F(3221, 5000), F(16106, 25000), F(19121, 25000)),
}
for x, (sl, su, cl) in trig.items():
    if sl is not None:
        assert sin_poly(x, 3) > sl
    assert sin_poly(x, 2) < su
    assert cos_poly(x, 3) >= cl

s7, u7, c7 = trig[F(7, 10)]
record("secondary impossible", F(14, 25)+F(7, 12)*F(13, 20), 1, "<")
record("CC +- positive derivative", 1-F(291, 500)*F(13, 20)-F(97, 1000), 0)
record("CC +- negative endpoint", -F(7, 10)+F(291, 500)*(1+c7)+F(6111, 5000)*s7, F(11, 10))

H1 = lambda x, su, cl: x+F(49017, 100000)+F(1, 2)*cl-F(183, 200)*su
assert H1(F(1, 4), F(1, 4), F(31, 32)) == F(199159, 200000)
assert H1(F(7, 10), u7, c7) == F(9831104, 10000000)
record("CO -- right derivative", 1-F(1, 2)*s7-F(183, 200)*c7, 0, "<")
record("CO -- cost", F(9831104, 10000000), gamma)

lam = F(21, 20)
assert (q-lam)/trig[F(1, 10)][0] > -F(2, 5)
assert (q-lam*c7)/s7 < F(2, 5)
assert lam+p/F(99, 1000) < F(7, 4)
assert F(2, 5)**2+F(7, 4)**2 < F(9, 5)**2
for x, n, lower in [
    (F(1, 10), F(173, 1000), F(2034909, 2000000)),
    (F(7, 10), F(193, 250), F(501811, 500000)),
]:
    sl, su, cl = trig[x]
    n2 = p*p+q*q+lam*lam+2*lam*(p*su-q*cl)
    record("CO ++ norm "+str(x), n*n, n2)
    f = x+F(231, 200)+lam*sl-F(1979, 1000)*n
    assert f == lower
    record("CO ++ cost "+str(x), f, gamma)

lam = q
H2 = lambda x, su, cl: x+F(10183, 20000)+F(203, 400)*cl-F(37149, 40000)*su
record("CO +- positive axial right derivative", 1-F(203, 400)*s7-F(37149, 40000)*c7, 0, "<")
record("CO +- positive axial 0", H2(0, 0, 1), 1)
record("CO +- positive axial .7", H2(F(7, 10), u7, c7), F(9989, 10000))
assert lam-F(9, 100)+p*d_lo == F(19657, 20000)
for lam in [q, F(39, 40)]:
    record("negative axial difference "+str(lam),
           -1-lam*F(7, 40)+lam*(a_lo+F(1, 2))*F(551, 600), 0)
    record("negative diagonal difference "+str(lam),
           -1+lam*(d_lo+F(1, 2))*F(551, 600), 0)

record("OC ++ corner impossible", F(9, 10)+F(7, 12)*F(13, 20)-F(1, 2)*F(19, 25), 1, "<")
record("OC ++ phi>.4", F(1, 2)+F(1, 2)*F(23, 25)-F(1, 12)*F(2, 5), F(9, 10))
oc_same = F(2, 5)+F(23, 25)-F(1, 12)*F(2, 5)-F(101, 1000)
assert oc_same == F(17785, 15000)
record("OC ++ cost", oc_same, gamma)
record("OC +- negative phi<.5", F(23, 50)-F(21, 20)*F(47, 100), 0, "<")
oc_minus_0 = F(2077, 5000)+F(291, 500)
oc_minus_5 = F(2077, 5000)+F(291, 500)*F(7, 8)+F(6111, 5000)*F(47, 100)-F(1, 2)
assert oc_minus_0 == F(4987, 5000)
assert oc_minus_5 == F(499542, 500000)
record("OC +- negative cost0", oc_minus_0, gamma)
record("OC +- negative cost.5", oc_minus_5, gamma)
record("OC +- positive derivative", 1-F(203, 400)*F(13, 20)-F(203, 2400), 0)

record("OO -- B lower", F(1, 2)+F(1, 2)*c7-F(183, 200)*u7, F(7, 25))
assert F(11, 50)**2+F(183, 200)**2 < 1
record("OO -- cost", F(979, 1000), gamma)
record("OO +- source endpoint", F(21, 200)*d_lo, p*a_hi)
P = lambda x: 1-F(35685, 40000)-F(39, 160)*x+F(35685, 240000)*x*x-F(35685, 4800000)*x**4
record("OO +- P decreasing", -F(39, 160)+2*F(35685, 240000)*F(7, 10), 0, "<")
record("OO +- P endpoint", P(F(7, 10)), 0)
assert F(39, 40)-F(9, 50)+2*p*a_lo == F(9783, 10000)
record("OO +- cost", F(9783, 10000), gamma)

record("primary source core impossible", F(7, 12)-F(11, 20)*F(19, 25)+F(9, 10)*F(13, 20), 1, "<")
record("primary target+ phi>=0 impossible", F(283, 200)-F(11, 20)*F(19, 25), 1, "<")
record("primary target+ phi<0 impossible", F(283, 200)-F(11, 20)*F(999, 1000)+F(9, 10)*F(1, 30), 1, "<")
assert F(19, 25)-F(11, 14) > -F(1, 30)
record("primary OO B>b", -F(2, 5)+F(7, 5)*c7-F(2, 5)*u7, 0)
record("primary OO endpoint", F(7, 10)-F(421, 1000)+F(7, 5)*c7-F(2, 5)*u7, F(109, 100))
record("primary OC phi>.4", F(183, 200)-F(21, 20)*F(23, 25)+F(3, 50)*F(2, 5), 0, "<")
lam = F(12, 5)
record("primary OC corner w", lam*F(13, 20)-h, F(2, 5), "<")
record("primary OC corner loss", F(2, 5)**2/(24*F(49, 10)), F(1, 500), "<")
record("primary OC source radical square", Q*((p+lam)**2+q*q), F(132, 25)**2, "<")
cost4 = F(2, 5)+F(303, 100)-F(132, 25)+F(13, 5)*F(23, 25)+F(6, 5)*F(389, 1000)-F(1, 500)
cost7 = F(7, 10)+F(303, 100)-F(132, 25)+F(13, 5)*F(478, 625)+F(291, 500)-F(1, 500)
assert cost4 == F(2517, 2500)
assert cost7 == F(63655, 62500)
record("primary OC cost.4", cost4, gamma)
record("primary OC cost.7", cost7, gamma)

print("PASS:", len(checks), "displayed strict rational comparisons")
for row in checks:
    print(*row)
