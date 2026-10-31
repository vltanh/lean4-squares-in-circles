"""Independent exact review of the house TDB owned-return scalar proof.

This does not import or execute the author's arithmetic implementation.
It uses sparse rational polynomials and homogeneous degree elevation to
rebuild both identities and all thirty Bernstein lower bounds.
"""

from fractions import Fraction as Q
from math import comb


def plus(*terms):
    out = {}
    for term in terms:
        for exponent, coefficient in term.items():
            out[exponent] = out.get(exponent, Q(0)) + coefficient
    return {i: a for i, a in out.items() if a}


def times(left, right):
    out = {}
    for i, a in left.items():
        for j, b in right.items():
            out[i + j] = out.get(i + j, Q(0)) + a * b
    return {i: a for i, a in out.items() if a}


def scaled(poly, factor):
    return {i: Q(factor) * a for i, a in poly.items() if factor * a}


def power(poly, exponent):
    out = {0: Q(1)}
    base = poly
    while exponent:
        if exponent & 1:
            out = times(out, base)
        base = times(base, base)
        exponent //= 2
    return out


def elevated_coefficients(poly):
    degree = max(poly)
    # Homogenize each p_i (5u/12)^i by (u+v)^(degree-i).
    # The coefficient of u^j v^(degree-j), divided by binom(degree,j),
    # is the Bernstein coefficient on the closed interval [0,5/12].
    homogeneous = [Q(0) for _ in range(degree + 1)]
    for i, a in poly.items():
        for j in range(i, degree + 1):
            homogeneous[j] += a * Q(5, 12) ** i * comb(degree - i, j - i)
    return [a / comb(degree, j) for j, a in enumerate(homogeneous)]


def main():
    a = {0: Q(1), 2: Q(1)}
    b = {0: Q(1), 2: Q(-1)}
    t = {1: Q(2)}
    k = plus(b, scaled(t, -1))
    ell = plus(power(a, 2), times(b, t))
    y0 = plus(scaled(a, Q(1, 3)), b, t)
    y1 = plus(scaled(a, Q(21, 50)), b, t)
    p0 = plus(
        scaled(times(power(ell, 2), power(a, 2)), 4),
        scaled(times(power(y0, 2), plus(power(ell, 2), power(b, 4))), -1),
    )
    d1 = plus(times(k, ell), scaled(power(a, 3), Q(13, 150)))
    p1 = plus(
        times(power(d1, 2), plus(scaled(power(a, 2), 4), scaled(power(y1, 2), -1))),
        scaled(times(times(power(b, 4), power(k, 2)), power(y1, 2)), -1),
    )
    expected0 = [4, -16, 64, 144, 292, 160, 560, -256,
                 508, -336, 208, -80, 28]
    expected1 = [18333171, -243089800, 1083164568, -852829400,
                 -1017825612, -4046689800, 7165087176, -8708591000,
                 22765217970, -6563911000, 13817385576, -219529800,
                 -387768012, 1236410600, -534697032, 163670200,
                 152982771]
    lower0 = [4443, 3826, 3395, 3205, 3326, 3855, 4914,
              6666, 9323, 13161, 18547, 25954, 36006]
    lower1 = [3258, 2132, 1285, 698, 346, 204, 236, 402,
              654, 937, 1191, 1357, 1381, 1227, 900, 472, 136]
    for poly, scale, expected, lower in (
        (p0, 9, expected0, lower0),
        (p1, 56250000, expected1, lower1),
    ):
        assert max(poly) + 1 == len(expected) == len(lower)
        assert [scale * poly.get(i, Q(0)) for i in range(len(expected))] == expected
        beta = elevated_coefficients(poly)
        margins = [10000 * value - floor for value, floor in zip(beta, lower)]
        assert all(value > 0 for value in beta)
        assert all(value > 0 for value in margins)
        print(f"degree {max(poly)}: {len(beta)} coefficients; "
              f"minimum={min(beta)}; minimum printed-floor reserve={min(margins)}")
    reserves = {
        "half-angle upper bound": Q(17, 12) ** 2 - 2,
        "circle-height upper bound": Q(143, 100) ** 2 - 2,
        "low-radius d bound": Q(15, 4) - Q(29, 15) ** 2,
        "actual left-port height": Q(12, 35) - Q(1, 15) ** 2 - Q(29, 50) ** 2,
        "acute-chord vertical gap": Q(137, 150) ** 2 - Q(3, 4),
        "final diameter excess": Q(43, 30) ** 2 - 2,
    }
    for name, value in reserves.items():
        assert value > 0
        print(f"{name}: {value}")
    print("PASS: independent sparse identities, all 30 homogeneous coefficients, six geometry reserves")


if __name__ == "__main__":
    main()
