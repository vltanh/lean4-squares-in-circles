#!/usr/bin/env python3
"""Exact whole-rectangle arithmetic for the far-radial ABC pressure proof.

Standard library only. Reconstructs the three formula-defined integer
polynomials, all 2256 rational Bernstein coefficients, their normalized
row lower bounds, and every coefficient of the full inverse identities.
No sampled pose or floating-point sign is used.

Run with --write-certificate-dir DIR to save all exact coefficient data.
"""
from argparse import ArgumentParser
from fractions import Fraction
from functools import reduce
from math import comb, gcd, lcm
from pathlib import Path
import json


class Poly:
    """Integer polynomial in (lambda,z)."""
    def __init__(self, value=0):
        self.terms = ({e: c for e, c in value.items() if c}
                      if isinstance(value, dict) else
                      ({(0, 0): value} if value else {}))

    def __add__(self, other):
        other = as_poly(other)
        result = self.terms.copy()
        for e, c in other.terms.items():
            result[e] = result.get(e, 0) + c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + -as_poly(other)

    def __rsub__(self, other):
        return as_poly(other) + -self

    def __mul__(self, other):
        other = as_poly(other)
        result = {}
        for (i, j), a in self.terms.items():
            for (k, ell), b in other.terms.items():
                e = (i + k, j + ell)
                result[e] = result.get(e, 0) + a * b
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result, value = Poly(1), self
        while exponent:
            if exponent & 1:
                result *= value
            value *= value
            exponent //= 2
        return result

    def evaluate(self, lam, z):
        return sum(c * lam**i * z**j
                   for (i, j), c in self.terms.items())

    def divide_z_exact(self, divisor):
        """Exact division by one integer polynomial in z."""
        degree = len(divisor) - 1
        result = {}
        for i in {e[0] for e in self.terms}:
            remainder = {j: c for (ii, j), c in self.terms.items() if ii == i}
            while remainder and max(remainder) >= degree:
                top = max(remainder)
                coefficient = remainder[top]
                assert coefficient % divisor[-1] == 0
                coefficient //= divisor[-1]
                shift = top - degree
                result[i, shift] = coefficient
                for j, c in enumerate(divisor):
                    e = shift + j
                    remainder[e] = remainder.get(e, 0) - coefficient * c
                    if not remainder[e]:
                        del remainder[e]
            assert not remainder
        return Poly(result)


def as_poly(value):
    return value if isinstance(value, Poly) else Poly(value)


LAM = Poly({(1, 0): 1})
ZVAR = Poly({(0, 1): 1})
U = 1 + ZVAR**2


def geometry(d0, m):
    """All numerators are integers; M=m/(d0*U^2)."""
    z = ZVAR
    znum = m + 2*d0*z*U
    hnum = m*(1-z*z) - d0*z*U**2
    betanum = d0*U**3 + (d0//2)*(1-z*z)*U**2 + 2*z*m
    qnum = (m*m + 4*d0*z*m*U
            + ((5*d0*d0//4)*U + d0*d0*(1-z*z))*U**3)
    anum = hnum*U**2*znum**2 + z*betanum**2*(znum+m)
    aden = d0*U**5*znum**2
    bnum = qnum*U**6*znum**4 - anum**2
    return dict(d0=d0, m=m, Z=znum, H=hnum, beta=betanum,
                q=qnum, A=anum, D=aden, B=bnum)


def packet_definitions():
    z = ZVAR
    m = (49588*U**2 - 77280*z*U + 77280*z*z
         + LAM*(5957*U**2 + 7200*z*z))
    g = geometry(38640, m)
    A, D, B = g['A'], g['D'], g['B']
    first = (16*A-9*D)*B + 3*D*(A-D)*(9*D-14*A)
    second = 4*(67*D-28*A)*B - 27*D**2*(7*A-D)
    rho_num = (6*g['beta']*m*first
               + (g['H']-g['d0']*U**3)*g['Z']*second)

    m = (539*U**2 - 840*z*U + 840*z*z
         + LAM*(21*U**2 + 150*z*z))
    g = geometry(420, m)
    A, D, B = g['A'], g['D'], g['B']
    xnum = A-D
    ln = g['beta']*m
    hn = (g['H']-g['d0']*U**3)*g['Z']
    wn = (1-z*z)*ln - 2*z*hn
    vn = (1-z*z)*hn + 2*z*ln
    dgeom = ln**2 + hn**2
    qa = g['q']*U*g['Z']**2 - g['d0']*A
    n1_num = U*(ln*qa*vn + g['d0']*hn*xnum*wn) - (1-z*z)*dgeom**2
    n0_num = ln*qa*xnum*wn + g['d0']*hn*vn*B
    chord_num = 42*U*D*n0_num + n1_num*(16*B+27*D**2)
    return [
        ('RHO', rho_num, 0, 64, (11, 64)),
        ('KJ_COEFFICIENT', -n1_num, 2, 1, (8, 38)),
        ('KJ_CHORD', -chord_num, 2, 16, (14, 74)),
    ]


def certify(name, raw, u_power, expected_gcd, expected_degrees):
    primitive = raw
    for _ in range(u_power):
        primitive = primitive.divide_z_exact([1, 0, 1])
    common = reduce(gcd, (abs(c) for c in primitive.terms.values()))
    assert common == expected_gcd
    primitive = Poly({e: c//common for e, c in primitive.terms.items()})
    degrees = tuple(max(e[k] for e in primitive.terms) for k in range(2))
    assert degrees == expected_degrees
    n, m = degrees
    dl = lcm(*(comb(n, r) for r in range(n+1)))
    dz = lcm(*(comb(m, s) for s in range(m+1)))
    scale = dl*dz*91**m
    prepared = {
        (r, s): c*31**s*91**(m-s)
                * (dl//comb(n, r))*(dz//comb(m, s))
        for (r, s), c in primitive.terms.items()
    }
    rows = [
        [sum(c*comb(i, r)*comb(j, s)
             for (r, s), c in prepared.items() if r <= i and s <= j)
         for j in range(m+1)]
        for i in range(n+1)
    ]
    assert all(c > 0 for row in rows for c in row)

    # Reconstruct the complete ordinary-power polynomial from its
    # Bernstein form. No evaluation grid is used for this identity.
    lambda_inverse = [
        [sum(rows[i][j]*comb(n, i)*comb(n-i, r-i)*(-1)**(r-i)
             for i in range(r+1)) for j in range(m+1)]
        for r in range(n+1)
    ]
    for r in range(n+1):
        for s in range(m+1):
            actual = sum(lambda_inverse[r][j]*comb(m, j)*comb(m-j, s-j)
                         * (-1)**(s-j) for j in range(s+1))
            expected = (primitive.terms.get((r, s), 0)*31**s*91**(m-s)*dl*dz)
            assert actual == expected, (name, r, s)

    # Positive whole-packet reserves after normalization by G(0,0).
    floors = [min(100*c//rows[0][0] for c in row) for row in rows]
    assert all(10*c > 9*rows[0][0] for row in rows for c in row)
    expected_floors = {
        'RHO': [92,99,106,113,121,129,137,145,153,162,169,130],
        'KJ_COEFFICIENT': [97,98,100,102,104,105,107,109,110],
        'KJ_CHORD': [92,94,95,96,97,99,100,101,102,103,104,106,107,108,109],
    }
    assert floors == expected_floors[name]
    print(name, 'PASS', degrees, (n+1)*(m+1),
          'positive coefficients and complete inverse identity;', floors)
    return dict(packet=name, degrees=degrees, removed_U_power=u_power,
                common=str(common), scale=str(scale),
                normalized_row_floor_100=floors,
                coefficients=[[str(c) for c in row] for row in rows],
                power=[[i,j,str(c)] for (i,j),c in sorted(primitive.terms.items())])


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate-dir', type=Path)
    options = parser.parse_args()
    records = [certify(*packet) for packet in packet_definitions()]
    assert sum((r['degrees'][0]+1)*(r['degrees'][1]+1) for r in records) == 2256
    if options.write_certificate_dir:
        options.write_certificate_dir.mkdir(parents=True, exist_ok=True)
        for record in records:
            filename = 'ABC_UPPER_LEFT_FAR_RADIAL_' + record['packet'] + '_CERTIFICATE.json'
            (options.write_certificate_dir/filename).write_text(
                json.dumps(record, indent=2)+'\n', encoding='utf-8')
    print('PASS: 2256 exact coefficients, all normalized above 9/10, and all inverse identities.')


if __name__ == '__main__':
    main()
