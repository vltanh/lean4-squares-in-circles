"""Discovery rows: signed center displacement above a chord of relative support.

Untrusted until the separate independent decoder and original physical
attachment have checked every weighted literal. No cell is closed here.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt
from owner_free_relative_support_snapshot import signed_product_lower_planes

PREFIX = 'physical_relative_support_chord_'
UPPER = F(121, 100)

def sqrt_lower(q, bits=30):
    q = F(q)
    assert q >= 0
    denominator = 1 << bits
    return F(isqrt(q.numerator * denominator * denominator // q.denominator), denominator)

def ratio_box(transverse):
    lower, upper = map(F, transverse)
    assert lower <= upper
    return min(lower, lower / UPPER), max(upper, upper / UPPER)

def row(scalar, differences, family, i, j, axis, sign, epsilon, zl, zu, al, au, code):
    assert family in ('signed', 'folded') and 0 <= i < j < 9
    assert axis in (0, 1) and sign in (-1, 1) and epsilon in (-1, 1)
    zl, zu, al, au = map(F, (zl, zu, al, au))
    lower, upper = differences[i, j][axis]
    assert lower >= 0 if sign == 1 else upper <= 0
    actual_l, actual_u = ratio_box(differences[i, j][1-axis])
    assert -1 <= zl <= actual_l <= actual_u <= zu <= 1
    assert al >= 0 and au >= 0 and al*al + zl*zl <= 1 and au*au + zu*zu <= 1
    if zl == zu:
        assert zl == 0 and al == au == 1
        slope, intercept = F(0), F(1)
    else:
        slope = (au-al)/(zu-zl)
        intercept = al-slope*zl
    assert intercept >= 0
    code = tuple(code)
    assert len(code) == 4 and all(bit in (0, 1) for bit in code)
    offset = 27 if family == 'signed' else 36
    terms = ((18+i, 18+j, 1), (offset+i, offset+j, 1),
             (18+i, offset+j, epsilon), (offset+i, 18+j, -epsilon))
    coefficients = {2*i+axis: F(sign), 2*j+axis: F(-sign),
                    2*i+1-axis: -slope, 2*j+1-axis: slope}
    constant = F(1)
    for (x, y, sg), bit in zip(terms, code):
        entries, shift = signed_product_lower_planes(x, y, scalar[x-18], scalar[y-18], sg)[bit]
        constant += shift
        for k, value in entries:
            coefficients[k] = coefficients.get(k, F(0)) + intercept*value/2
    label = PREFIX + '_'.join(map(str, (family, i, j, axis, sign, epsilon, zl, zu, al, au)))
    label += '_' + ''.join(map(str, code))
    return tuple((k, v) for k, v in sorted(coefficients.items()) if v), -intercept*constant/2, label

def generate(scalar, differences):
    result = []
    for (i, j), box in sorted(differences.items()):
        for axis in (0, 1):
            lower, upper = box[axis]
            sign = 1 if lower >= 0 else -1 if upper <= 0 else None
            zl, zu = ratio_box(box[1-axis])
            if sign is None or not -1 <= zl <= zu <= 1:
                continue
            if zl == zu and zl != 0:
                continue
            al, au = sqrt_lower(1-zl*zl), sqrt_lower(1-zu*zu)
            for family, epsilon, code in product(('signed', 'folded'), (-1, 1), product((0, 1), repeat=4)):
                result.append(row(scalar, differences, family, i, j, axis, sign, epsilon, zl, zu, al, au, code))
    return result
