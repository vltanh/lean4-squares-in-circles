#!/usr/bin/env python3
"""Whole-caller isometries and extra-label permutation; no row installation.

The input has the common 54 original-variable columns.  These maps act on
physical assignments, not on proof records or inherited search intervals.
"""
from fractions import Fraction as F


def relabel(original, swap_extras=False):
    assert type(original) is int and 0 <= original < 9
    assert type(swap_extras) is bool
    return 15-original if swap_extras and original in (7, 8) else original


def variable_map(reflect=False, swap_extras=False):
    """For each new column return (old column, sign), an involution."""
    assert type(reflect) is bool and type(swap_extras) is bool
    result = [None]*54
    vertical = -1 if reflect else 1
    for i in range(9):
        j = relabel(i, swap_extras)
        result[2*i], result[2*i+1] = (2*j, 1), (2*j+1, vertical)
        result[18+i] = (18+j, 1)
        result[27+i] = (27+j, vertical)
        result[36+i] = (36+j, 1)
        result[45+i] = (45+j, 1)
    return tuple(result)


def transform(values, reflect=False, swap_extras=False):
    assert len(values) == 54
    return tuple(sign*F(values[column]) for column, sign in variable_map(reflect, swap_extras))


def map_corner(original, epsilon, tau, reflect=False, swap_extras=False):
    assert epsilon in (-1, 1) and tau in (-1, 1)
    return relabel(original, swap_extras), epsilon, -tau if reflect else tau


def pair_image(pair, swap_extras=False):
    assert len(pair) == 2 and all(type(i) is int for i in pair) and 0 <= pair[0] < pair[1] < 9
    left, right = (relabel(i, swap_extras) for i in pair)
    return (min(left, right), max(left, right)), 1 if left < right else -1


def map_owned_choice(pair, choice, reflect=False, swap_extras=False):
    """Return new sorted pair, owned choice, and relative-sine sign change."""
    assert len(choice) == 3 and all(type(i) is int for i in choice)
    owner, axis, sign = choice
    assert owner in pair and axis in (0, 1) and sign in (-1, 1)
    image, order = pair_image(pair, swap_extras)
    normal_sign = -1 if reflect and axis == 1 else 1
    new_choice = (relabel(owner, swap_extras), axis, sign*order*normal_sign)
    sine_sign = order*(-1 if reflect else 1)
    return image, new_choice, sine_sign


def map_proxy_choice(pair, choice, reflect=False, swap_extras=False):
    assert len(choice) == 2 and all(type(i) is int for i in choice)
    axis, sign = choice
    assert axis in (0, 1) and sign in (-1, 1)
    image, order = pair_image(pair, swap_extras)
    vertical_sign = -1 if reflect and axis == 1 else 1
    return image, (axis, sign*order*vertical_sign)


def normalize_physical_assignment(values):
    """Choose one of four equivalent assignments with beta_D>=0, x_H<=x_I."""
    assert len(values) == 54
    values = tuple(map(F, values))
    for i in range(9):
        a, b, z, g = (values[base+i] for base in (18, 27, 36, 45))
        assert a*a+b*b == 1 and a >= abs(b) and a > 0
        assert z == abs(b) and g == 1/(2*(a+z))
    reflect = values[30] < 0
    swap_extras = values[14] > values[16]
    normalized = transform(values, reflect, swap_extras)
    assert normalized[30] >= 0 and normalized[14] <= normalized[16]
    return normalized, dict(reflect=reflect, swap_extras=swap_extras)
