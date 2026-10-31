#!/usr/bin/env python3
"""Independent exact review reconstruction; does not import the author checker.

Polynomials are lists in w of integer polynomials in z. Bernstein conversion
uses homogeneous degree elevation of original physical-interval monomials,
rather than an affine power expansion. Every actual coefficient is checked.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib
import json
import re


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def ua(a, b):
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def um(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def clean(a):
    a = [trim(x) for x in a]
    while len(a) > 1 and a[-1] == [0]:
        a.pop()
    return a


def plus(*args):
    c = [[0] for _ in range(max(map(len, args)))]
    for a in args:
        for i, x in enumerate(a):
            c[i] = ua(c[i], x)
    return clean(c)


def times(*args):
    c = [[1]]
    for a in args:
        d = [[0] for _ in range(len(c) + len(a) - 1)]
        for i, x in enumerate(c):
            for j, y in enumerate(a):
                d[i+j] = ua(d[i+j], um(x, y))
        c = clean(d)
    return c


def coeff(k, p):
    return clean([[k*x for x in a] for a in p])


def square(p):
    return times(p, p)


def make(row):
    A, B, D = [[1, 0, -1]], [[0, 2]], [[1, 0, 1]]
    M, L = plus(A, B), plus(A, coeff(-1, B))
    w = [[0], [1]]
    n, k = (B, A) if row == 'lower' else ([[1, -1]], [[1, 1]])
    K = times(M, k)
    N = plus(times(L, k), times(w, plus(times(n, M), coeff(-1, times(L, k)))))
    H = plus(times(B, K), times(A, N))
    T = plus(times(D, K), coeff(-1, H))
    Delta = plus(times(M, N), coeff(-1, times(L, K)))
    KN = plus(K, coeff(-1, N))
    J = plus(times(A, KN, D, K), times(T, Delta))
    V = plus(times(D, square(K)), coeff(-1, times(N, H)))
    K2, N2, V2 = square(K), square(N), square(V)
    W = plus(coeff(2, K2), coeff(-1, N2))
    # Clear the two terms of L separately, then subtract 21/10.
    first = coeff(10, times(W, KN, plus(J, times(square(A), plus(K2, N2))), V, V2))
    second = coeff(5, times(W, KN, D, K2, J, plus(coeff(2, V2), coeff(-1, times(square(T), K2)))))
    third = coeff(-42, times(K, K2, J, V, V2))
    return plus(first, second, third)


def elevate_monomial(k, degree, left, right):
    # z^k has degree-k Bernstein coefficients left^(k-j)*right^j.
    # Degree elevation uses only the binomial convolution below.
    return [sum((Q(comb(k, j)*comb(degree-k, i-j), comb(degree, i))
                 * left**(k-j) * right**j
                 for j in range(max(0, i-degree+k), min(k, i)+1)), Q(0))
            for i in range(degree+1)]


def run():
    base = Path(__file__).resolve().parents[1]
    source = base / 'THREE_SPOKE_EQUAL_ROOF_SEPARATION_SCALAR.md'
    rows = re.findall(r'^\| (\d+) \| (\d+) \| (\d+|Not in upper degree) \|$', source.read_text(), re.M)
    expected = {'lower': [int(a) for _, a, _ in rows],
                'upper': [int(b) for _, _, b in rows if b.isdigit()]}
    answer = {}
    for row, left, right in [('lower', Q(19,100), Q(27,100)),
                              ('upper', Q(1,4), Q(5,12))]:
        polynomial = make(row)
        n = max(len(x)-1 for x in polynomial)
        m = len(polynomial)-1
        z_basis = [elevate_monomial(k, n, left, right) for k in range(n+1)]
        w_basis = [elevate_monomial(l, m, Q(0), Q(1)) for l in range(m+1)]
        # First combine in z. This is not an affine power-coefficient transform.
        z_rows = [[sum((Q(polynomial[l][k])*z_basis[k][i]
                       for k in range(len(polynomial[l]))), Q(0))
                   for l in range(m+1)] for i in range(n+1)]
        beta = [[sum((z_rows[i][l]*w_basis[l][j] for l in range(m+1)), Q(0))
                 for j in range(m+1)] for i in range(n+1)]
        assert all(x > 0 for line in beta for x in line)
        floor = [int(10*min(line)//1) for line in beta]
        assert floor == expected[row], (row, floor, expected[row])
        degrees = (54,11) if row == 'lower' else (43,11)
        terms = sum(x != 0 for line in polynomial for x in line)
        assert (n,m) == degrees
        assert terms == (647 if row == 'lower' else 434)
        least = min(x for line in beta for x in line)
        payload = ';'.join(str(x) for line in beta for x in line).encode()
        answer[row] = {'degree':[n,m], 'monomials':terms,
                       'positive_coefficients':(n+1)*(m+1),
                       'minimum_coefficient':str(least),
                       'minimum_floor_tenths':min(floor),
                       'all_row_floors':floor,
                       'coefficient_sha256':hashlib.sha256(payload).hexdigest()}
    z = Q(19,100)
    scalar_checks = {
        'lower_rectangle_start':(1-z*z-2*z)/(1-z*z+2*z)-2*z/(1-z*z),
        'lower_rectangle_end':3-Q(173,100)**2,
        'upper_rectangle_start':Q(7,4)**2-3,
        'upper_rectangle_end':Q(17,12)**2-2,
        'geometric_radius_reserve':Q(21,10)-Q(25,12),
        'strict_radius_cap':Q(25,12)**2-Q(1105,256),
    }
    assert all(x>0 for x in scalar_checks.values())
    answer['exact_reserves']={k:str(v) for k,v in scalar_checks.items()}
    print(json.dumps(answer,indent=2))


if __name__ == '__main__':
    run()
