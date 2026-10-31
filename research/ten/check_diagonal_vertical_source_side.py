#!/usr/bin/env python3
"""Exact rational table for ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md."""

from fractions import Fraction as Q
from pathlib import Path


class Interval:
    def __init__(self, lower, upper=None):
        self.lower = Q(lower)
        self.upper = Q(lower if upper is None else upper)
        assert self.lower <= self.upper

    @staticmethod
    def cast(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.cast(other)
        return Interval(self.lower + other.lower, self.upper + other.upper)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.upper, -self.lower)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        products = [a * b for a in (self.lower, self.upper)
                    for b in (other.lower, other.upper)]
        return Interval(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        assert other.lower > 0
        return self * Interval(1 / other.upper, 1 / other.lower)

    def __rtruediv__(self, other):
        return self.cast(other) / self


EXPECTED = [
    (178, 66), (162, 46), (148, 30), (135, 18),
    (125, 10), (115, 6), (108, 6), (101, 9),
    (96, 15), (92, 24), (89, 36), (87, 50),
    (85, 67), (85, 85), (84, 106), (85, 128),
]


def evaluate(j, height):
    t = Interval(Q(1, 5) + Q(13 * j, 960),
                 Q(1, 5) + Q(13 * (j + 1), 960))
    d = Interval(Q(140, 99), Q(99, 70))
    K = 2 + d
    H = Interval(height)
    r = 2 * t / (1 + t * t)
    s = (1 - t * t) / (1 + t * t)
    delta = 1 - s
    u = K / 2 - delta * (2 * H - delta) / (2 * K)
    v = K - u
    B = H - delta
    F = (d - r) * H * (v * s - B * r) - u * (
        delta * (v * s - B * r) + B * (s - r))
    return F


def main():
    assert Q(1, 5) + Q(13 * 16, 960) == Q(5, 12)
    assert 140**2 < 2 * 99**2
    assert 99**2 > 2 * 70**2
    note = Path(__file__).with_name(
        "ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md").read_text()
    minimum = None
    for j, expected in enumerate(EXPECTED):
        actual = []
        for height in (Q(1), Q(3, 2)):
            value = evaluate(j, height)
            rounded = (1000 * value.lower).__floor__()
            assert value.lower >= Q(rounded, 1000) > 0
            actual.append(rounded)
            minimum = value.lower if minimum is None else min(minimum, value.lower)
        assert tuple(actual) == expected, (j, actual, expected)
        assert f"| {j} | {expected[0]} | {expected[1]} |" in note
    assert minimum > Q(6, 1000)
    print("PASS: all 32 exact interval bounds; full 16-interval coverage; "
          "printed table matches; every lower endpoint exceeds 6/1000.")


if __name__ == "__main__":
    main()
