"""Independent expansion and squared-support check; no discovery imports."""
from fractions import Fraction as F

PREFIX = 'physical_corner_disk_'


def verify_literal(literal):
    coefficients, rhs, name = literal
    assert name.startswith(PREFIX)
    fields = name[len(PREFIX):].split('_')
    assert len(fields) == 6
    original, epsilon, tau = map(int, fields[:3])
    a, b, upper = map(F, fields[3:])
    assert 0 <= original < 9 and epsilon in (-1, 1) and tau in (-1, 1)
    assert a or b
    assert F(rhs) == upper and upper >= 0
    assert 256 * upper * upper >= 1105 * (a * a + b * b)
    # Expand a times the corner's x coordinate and b times its y coordinate.
    answer = {}
    for weight, terms in ((a, ((2 * original, F(1)),
                               (18 + original, F(epsilon, 2)),
                               (27 + original, F(-tau, 2)))),
                           (b, ((2 * original + 1, F(1)),
                               (27 + original, F(epsilon, 2)),
                               (18 + original, F(tau, 2))))):
        for index, value in terms:
            answer[index] = answer.get(index, F(0)) + weight * value
    expected = tuple((index, value) for index, value in sorted(answer.items()) if value)
    assert tuple(coefficients) == expected
    return literal
