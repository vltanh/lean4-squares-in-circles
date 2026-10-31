"""Exact arithmetic for OWNED_SOUTH_BOUNDARY_CHANNEL_HEIGHT_BOUND.md.

This checks two displayed univariate polynomial identities and all 30
Bernstein coefficients on the single rational interval [0,5/12].
There are no sampled poses, floating-point operations, or subdivisions.
"""

from fractions import Fraction as F
from math import comb


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b):
    out = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += x
    return trim(out)


def scale(a, k):
    return [k * x for x in a]


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def power(a, n):
    out = [F(1)]
    for _ in range(n):
        out = mul(out, a)
    return out


def bernstein(p):
    n = len(p) - 1
    return [
        sum(
            (p[i] * F(5, 12) ** i * F(comb(j, i), comb(n, i))
             for i in range(j + 1)),
            F(0),
        )
        for j in range(n + 1)
    ]


def main():
    a = [F(1), F(0), F(1)]
    b = [F(1), F(0), F(-1)]
    t = [F(0), F(2)]
    k = sub(b, t)
    ell = add(power(a, 2), mul(b, t))

    y0 = add(scale(a, F(1, 3)), add(b, t))
    p0 = sub(
        scale(mul(power(ell, 2), power(a, 2)), 4),
        mul(power(y0, 2), add(power(ell, 2), power(b, 4))),
    )
    ints0 = [4, -16, 64, 144, 292, 160, 560, -256,
             508, -336, 208, -80, 28]
    assert p0 == [F(x, 9) for x in ints0]

    y1 = add(scale(a, F(21, 50)), add(b, t))
    d1 = add(mul(k, ell), scale(power(a, 3), F(13, 150)))
    p1 = sub(
        mul(power(d1, 2), sub(scale(power(a, 2), 4), power(y1, 2))),
        mul(mul(power(b, 4), power(k, 2)), power(y1, 2)),
    )
    ints1 = [18333171, -243089800, 1083164568, -852829400,
             -1017825612, -4046689800, 7165087176, -8708591000,
             22765217970, -6563911000, 13817385576, -219529800,
             -387768012, 1236410600, -534697032, 163670200,
             152982771]
    assert p1 == [F(x, 56250000) for x in ints1]

    lower0 = [4443, 3826, 3395, 3205, 3326, 3855, 4914,
              6666, 9323, 13161, 18547, 25954, 36006]
    lower1 = [3258, 2132, 1285, 698, 346, 204, 236, 402,
              654, 937, 1191, 1357, 1381, 1227, 900, 472, 136]
    for p, lower, degree in [(p0, lower0, 12), (p1, lower1, 16)]:
        assert len(p) == degree + 1 == len(lower)
        beta = bernstein(p)
        assert all(10000 * x > lo > 0 for x, lo in zip(beta, lower))
        print(f"degree {degree}: {len(beta)} positive coefficients; minimum {min(beta)}")
    print("PASS: both exact identities and all 30 whole-interval coefficients")


if __name__ == "__main__":
    main()
